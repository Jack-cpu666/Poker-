import asyncio
import json
import logging
import os
import random
import time
import uuid
from typing import Dict, List, Optional, Set, Any, Union
from enum import Enum
from dataclasses import dataclass, asdict, field
from collections import defaultdict
from contextlib import asynccontextmanager
from datetime import datetime, timedelta
import traceback
import hashlib
import secrets

# FastAPI and WebSocket imports
import uvicorn
from fastapi import FastAPI, WebSocket, WebSocketDisconnect, HTTPException, Request, status, Depends
from fastapi.responses import HTMLResponse, FileResponse, JSONResponse
from fastapi.middleware.cors import CORSMiddleware
from fastapi.staticfiles import StaticFiles
from fastapi.security import HTTPBearer, HTTPAuthorizationCredentials
from pydantic import BaseModel, ValidationError, Field as PydanticField

# Enhanced logging configuration with rotation
import logging.handlers

LOG_FORMAT = '%(asctime)s - %(name)s - %(levelname)s - %(funcName)s:%(lineno)d - %(message)s'
logging.basicConfig(
    level=logging.INFO,
    format=LOG_FORMAT,
    handlers=[
        logging.StreamHandler(),
        logging.handlers.RotatingFileHandler(
            'royal_blackjack.log', 
            maxBytes=10*1024*1024,  # 10MB
            backupCount=5,
            encoding='utf-8'
        )
    ]
)

# Set up logger
logger = logging.getLogger(__name__)

# Suppress noisy logs
logging.getLogger('uvicorn.access').setLevel(logging.WARNING)
logging.getLogger('uvicorn.error').setLevel(logging.INFO)

# Production Configuration Constants
class GameConfig:
    """Game configuration and constants"""
    STARTING_MONEY = 1000
    MIN_BET = 10
    MAX_BET = 500
    MAX_PLAYERS_PER_ROOM = 6
    RATE_LIMIT_MESSAGES_PER_SECOND = 5
    RATE_LIMIT_ACTIONS_PER_SECOND = 3
    MAX_CHAT_MESSAGES = 50
    MAX_ROOMS = 1000  # Increased for production
    SESSION_TIMEOUT = 7200  # 2 hours, used for how long a disconnected player might be remembered
    DEALER_HIT_THRESHOLD = 16 # Dealer hits until 17 or more. Standard rule is often dealer hits soft 17.
    ROOM_CLEANUP_INTERVAL = 300  # 5 minutes
    INACTIVE_ROOM_TIMEOUT = 3600  # 1 hour (room is considered inactive if no activity)
    HEARTBEAT_INTERVAL = 30 # Not explicitly used in current loop, but good for WebSocket health
    MAX_MESSAGE_LENGTH = 200
    BLACKJACK_PAYOUT = 1.5  # 3:2 payout
    AUTO_RESET_DELAY = 10  # seconds
    MAX_RECONNECT_ATTEMPTS = 5 # Client-side concern mostly
    RECONNECT_WINDOW = 300  # 5 minutes (how long a player might be able to reconnect with a token)

# Security Configuration
class SecurityConfig:
    """Security and validation settings"""
    MAX_NAME_LENGTH = 25
    MAX_ROOM_NAME_LENGTH = 50
    BANNED_WORDS = [ # Example list, expand as needed
        'cheat', 'hack', 'bot', 'script', 'exploit', 'bug',
        'admin', 'moderator', 'casino', 'scam', 'fraud',
        # Add offensive terms here
    ]
    IP_RATE_LIMIT = 100  # requests per minute from a single IP
    SUSPICIOUS_ACTIVITY_THRESHOLD = 50 # Number of rate limit hits before IP is considered suspicious
    AUTO_BAN_THRESHOLD = 10 # Number of player warnings before auto-ban

# Game State Enums
class GamePhase(Enum):
    """Current phase of the game"""
    WAITING = "waiting"
    DEALING = "dealing"
    PLAYER_TURNS = "player_turns"
    DEALER_TURN = "dealer_turn"
    PAYOUT = "payout"
    GAME_OVER = "game_over"

class PlayerAction(Enum):
    """Available player actions"""
    HIT = "hit"
    STAND = "stand"
    DOUBLE_DOWN = "double_down"
    SPLIT = "split"
    SURRENDER = "surrender"
    PLACE_BET = "place_bet"

class PlayerStatus(Enum):
    """Player status in current hand"""
    ACTIVE = "active" # Actively playing or betting
    STANDING = "standing" # Player chose to stand
    BUST = "bust" # Player's hand > 21
    BLACKJACK = "blackjack" # Player got a natural blackjack
    SITTING_OUT = "sitting_out" # Player chose to sit out (not implemented yet)
    ELIMINATED = "eliminated" # Player out of money or banned
    DISCONNECTED = "disconnected" # Player's WebSocket connection lost

class HandResult(Enum):
    """Result of a completed hand"""
    WIN = "win"
    LOSE = "lose"
    PUSH = "push"
    BLACKJACK = "blackjack" # Player won with a natural blackjack
    BUST = "bust" # Player busted (implicitly a loss)
    SURRENDER = "surrender" # Player surrendered

# Enhanced Data Classes
@dataclass
class Card:
    """Represents a playing card with enhanced features"""
    suit: str  # hearts, diamonds, clubs, spades
    rank: str  # A, 2-10, J, Q, K
    id: str = field(default_factory=lambda: str(uuid.uuid4()))
    dealt_at: datetime = field(default_factory=datetime.now)

    def __str__(self):
        return f"{self.rank}{self.suit[0].upper()}"

    def get_blackjack_value(self, current_total: int = 0) -> int: # current_total not used here, logic is self-contained
        """Return the blackjack value of this card"""
        if self.rank in ['J', 'Q', 'K']:
            return 10
        elif self.rank == 'A':
            # Ace value logic is typically handled at the Hand level based on current total
            return 11 # Default to 11, Hand.get_value adjusts
        else:
            try:
                return int(self.rank)
            except ValueError:
                logger.error(f"Invalid card rank: {self.rank}")
                return 0

    def to_dict(self) -> Dict[str, Any]:
        """Convert card to dictionary"""
        return {
            "suit": self.suit,
            "rank": self.rank,
            "id": self.id
        }

@dataclass
class Hand:
    """Represents a hand of cards with comprehensive tracking"""
    cards: List[Card] = field(default_factory=list)
    bet_amount: int = 0
    is_split: bool = False
    is_doubled: bool = False
    is_surrendered: bool = False
    result: Optional[HandResult] = None
    payout: int = 0
    insurance_bet: int = 0 # Insurance not fully implemented in actions
    created_at: datetime = field(default_factory=datetime.now)

    def get_value(self) -> int:
        """Calculate the best possible value of this hand"""
        if not self.cards:
            return 0
            
        total = 0
        aces = 0
        
        for card in self.cards:
            if card.rank == 'A':
                aces += 1
                total += 11
            elif card.rank in ['J', 'Q', 'K']:
                total += 10
            else:
                try:
                    total += int(card.rank)
                except ValueError: # Should not happen if Card.rank is validated
                    logger.warning(f"Invalid card rank in hand: {card.rank}")
                    continue
        
        # Convert aces from 11 to 1 if needed
        while total > 21 and aces > 0:
            total -= 10
            aces -= 1
            
        return total

    def is_bust(self) -> bool:
        """Check if hand is busted (over 21)"""
        return self.get_value() > 21

    def is_blackjack(self) -> bool:
        """Check if hand is a blackjack (21 with 2 cards)"""
        return len(self.cards) == 2 and self.get_value() == 21

    def can_split(self) -> bool:
        """Check if hand can be split"""
        # Standard rule: Only on first two cards of equal rank
        return (len(self.cards) == 2 and 
                self.cards[0].get_blackjack_value() == self.cards[1].get_blackjack_value() and
                not self.is_split) # Can't re-split a split hand usually, depends on house rules

    def can_double_down(self) -> bool:
        """Check if hand can be doubled down"""
        # Standard rule: Only on first two cards
        return len(self.cards) == 2 # is_split check might be needed if house rules restrict doubling after split

    def can_surrender(self) -> bool:
        """Check if hand can be surrendered"""
        # Standard rule: Only on first two cards, before any other action
        return len(self.cards) == 2 and not self.is_split and not self.is_doubled

    def to_dict(self) -> Dict[str, Any]:
        """Convert hand to dictionary for JSON serialization"""
        return {
            "cards": [card.to_dict() for card in self.cards],
            "value": self.get_value(),
            "bet_amount": self.bet_amount,
            "is_bust": self.is_bust(),
            "is_blackjack": self.is_blackjack(),
            "is_doubled": self.is_doubled,
            "is_surrendered": self.is_surrendered,
            "is_split": self.is_split,
            "result": self.result.value if self.result else None,
            "payout": self.payout,
            "insurance_bet": self.insurance_bet
        }

@dataclass
class PlayerStats:
    """Comprehensive player statistics"""
    total_hands_played: int = 0
    total_hands_won: int = 0
    total_blackjacks: int = 0
    total_busts: int = 0
    total_surrenders: int = 0
    total_splits: int = 0
    total_doubles: int = 0
    total_winnings: int = 0 # Net winnings (can be negative)
    total_wagered: int = 0
    session_start: datetime = field(default_factory=datetime.now)
    best_streak: int = 0 # Longest winning streak
    current_streak: int = 0

    def get_win_rate(self) -> float:
        """Calculate win rate percentage"""
        if self.total_hands_played == 0:
            return 0.0
        return (self.total_hands_won / self.total_hands_played) * 100

    def get_roi(self) -> float:
        """Calculate return on investment"""
        if self.total_wagered == 0:
            return 0.0
        # ROI = (Net Winnings / Total Wagered) * 100
        return (self.total_winnings / self.total_wagered) * 100 if self.total_wagered > 0 else 0.0

    def to_dict(self) -> Dict[str, Any]:
        """Convert stats to dictionary"""
        return {
            "total_hands_played": self.total_hands_played,
            "total_hands_won": self.total_hands_won,
            "total_blackjacks": self.total_blackjacks,
            "total_busts": self.total_busts,
            "total_surrenders": self.total_surrenders,
            "total_splits": self.total_splits,
            "total_doubles": self.total_doubles,
            "total_winnings": self.total_winnings,
            "total_wagered": self.total_wagered,
            "win_rate": round(self.get_win_rate(), 2),
            "roi": round(self.get_roi(), 2),
            "best_streak": self.best_streak,
            "current_streak": self.current_streak,
            "session_duration": str(datetime.now() - self.session_start).split('.')[0] # Readable duration
        }

@dataclass
class Player:
    """Enhanced player representation with comprehensive features"""
    id: str
    name: str
    money: int = GameConfig.STARTING_MONEY
    hands: List[Hand] = field(default_factory=lambda: [Hand()])
    current_hand_index: int = 0
    status: PlayerStatus = PlayerStatus.ACTIVE
    avatar: str = "royal_avatar" # Default avatar, could be dynamic
    color: str = "#ffffff" # Player color for UI distinction
    connection_id: Optional[str] = None # Current WebSocket ID, maps to game.connections key
    is_ai: bool = False # For future AI players
    session_id: str = field(default_factory=lambda: str(uuid.uuid4())) # Unique session ID
    stats: PlayerStats = field(default_factory=PlayerStats)
    last_activity: datetime = field(default_factory=datetime.now)
    join_time: datetime = field(default_factory=datetime.now)
    ip_address: Optional[str] = None
    user_agent: Optional[str] = None # Could be captured from request headers
    is_vip: bool = False # For premium features
    warnings: int = 0 # For moderation
    is_banned: bool = False
    ban_reason: Optional[str] = None
    reconnect_token: Optional[str] = None # For secure reconnection

    def __post_init__(self):
        """Initialize player after creation"""
        if not self.hands: # Ensure player always starts with one hand
            self.hands = [Hand()]

    def get_current_hand(self) -> Hand:
        """Get the hand currently being played"""
        if 0 <= self.current_hand_index < len(self.hands):
            return self.hands[self.current_hand_index]
        # Fallback, should not happen if logic is correct
        logger.warning(f"Player {self.id} current_hand_index {self.current_hand_index} out of bounds for hands {len(self.hands)}")
        if not self.hands: self.hands.append(Hand()) # Ensure there's always a hand
        return self.hands[0]

    def can_act(self) -> bool:
        """Check if player can take an action on their current hand"""
        if self.status not in [PlayerStatus.ACTIVE]: # Only active players can act
            return False
            
        current_hand = self.get_current_hand()
        return (not current_hand.is_bust() and 
                not current_hand.is_surrendered and
                not current_hand.is_blackjack() and # Blackjack hand doesn't act further
                current_hand.get_value() < 21) # Can't hit on 21

    def reset_for_new_hand(self):
        """Reset player for a new hand of blackjack"""
        self.hands = [Hand()] # New empty hand
        self.current_hand_index = 0
        # Preserve status like SITTING_OUT, ELIMINATED, DISCONNECTED
        if self.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED, PlayerStatus.DISCONNECTED]:
            self.status = PlayerStatus.ACTIVE

    def update_activity(self):
        """Update last activity timestamp"""
        self.last_activity = datetime.now()

    def generate_reconnect_token(self) -> str:
        """Generate secure reconnect token"""
        self.reconnect_token = secrets.token_urlsafe(32)
        return self.reconnect_token

    def validate_reconnect_token(self, token: str) -> bool:
        """Validate reconnect token against stored token and time window"""
        return (self.reconnect_token is not None and
                self.reconnect_token == token and 
                (datetime.now() - self.last_activity).total_seconds() < GameConfig.RECONNECT_WINDOW)

    def add_warning(self, reason: str):
        """Add warning to player and log it"""
        self.warnings += 1
        game.stats['total_warnings_issued'] = game.stats.get('total_warnings_issued', 0) + 1
        logger.warning(f"Player {self.name} ({self.id}) warned: {reason}. Total warnings: {self.warnings}")
        
        if self.warnings >= SecurityConfig.AUTO_BAN_THRESHOLD:
            self.ban(f"Auto-banned due to reaching {self.warnings} warnings.")

    def ban(self, reason: str):
        """Ban player from the game/server"""
        self.is_banned = True
        self.ban_reason = reason
        self.status = PlayerStatus.ELIMINATED # Effectively removes them from play
        game.stats['total_bans_issued'] = game.stats.get('total_bans_issued', 0) + 1
        logger.error(f"Player {self.name} ({self.id}) BANNED: {reason}")

    def to_dict(self, current_player_id_in_room: Optional[str] = None, include_sensitive: bool = False) -> Dict[str, Any]:
        """Convert player to dictionary for JSON serialization"""
        hands_data = [hand.to_dict() for hand in self.hands]
        
        base_data = {
            "id": self.id,
            "name": self.name,
            "money": self.money,
            "hands": hands_data,
            "current_hand_index": self.current_hand_index,
            "status": self.status.value,
            "avatar": self.avatar,
            "color": self.color,
            "is_current_player": current_player_id_in_room == self.id, # Is it this player's turn in the room?
            "is_ai": self.is_ai,
            "is_vip": self.is_vip,
            "session_duration": str(datetime.now() - self.join_time).split('.')[0],
            "stats": self.stats.to_dict()
        }

        if include_sensitive: # For admin views or specific trusted contexts
            base_data.update({
                "ip_address": self.ip_address,
                "warnings": self.warnings,
                "is_banned": self.is_banned,
                "ban_reason": self.ban_reason,
                "last_activity": self.last_activity.isoformat()
            })

        return base_data

@dataclass
class Room:
    """Enhanced room representation with advanced features"""
    code: str
    name: str
    players: Dict[str, Player] # Maps player_id to Player object
    spectators: Set[str] # Set of player_ids who are spectating
    deck: List[Card]
    dealer_hand: Hand
    current_player_id: Optional[str] = None # player_id of the player whose turn it is
    phase: GamePhase = GamePhase.WAITING
    chat_messages: List[Dict] = field(default_factory=list)
    hand_number: int = 0 # Increments each new hand played
    created_at: datetime = field(default_factory=datetime.now)
    last_activity: datetime = field(default_factory=datetime.now)
    owner_id: Optional[str] = None # player_id of the room creator/owner
    min_bet: int = GameConfig.MIN_BET
    max_bet: int = GameConfig.MAX_BET
    _player_turn_order: List[str] = field(default_factory=list) # Ordered list of player_ids for turns
    _current_player_turn_index: int = 0
    is_public: bool = True
    max_players: int = GameConfig.MAX_PLAYERS_PER_ROOM
    password: Optional[str] = None # Hashed password if private
    is_premium: bool = False # For special room features
    tournament_mode: bool = False # For tournament style play
    buy_in: int = 0 # For tournament buy-in
    prize_pool: int = 0 # For tournament prize pool

    def __post_init__(self):
        """Initialize room after creation"""
        if not self.deck: # Ensure deck is initialized
            self.deck = self.create_deck()
        if not hasattr(self, 'dealer_hand') or not self.dealer_hand:
            self.dealer_hand = Hand()

    def create_deck(self, num_decks: int = 6) -> List[Card]:
        """Create and shuffle multiple decks for professional play"""
        suits = ["hearts", "diamonds", "clubs", "spades"]
        ranks = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]
        deck = []
        
        for _ in range(num_decks):
            for suit in suits:
                for rank in ranks:
                    deck.append(Card(suit, rank))
        
        # Enhanced shuffling algorithm
        for _ in range(random.randint(3,7)):  # More realistic shuffling
            random.shuffle(deck)
        
        logger.info(f"Created {num_decks}-deck shoe with {len(deck)} cards for room {self.code}")
        return deck

    def shuffle_deck(self):
        """Reshuffle the deck"""
        self.deck = self.create_deck()
        logger.info(f"Reshuffled deck for room {self.code}")

    def deal_card(self) -> Optional[Card]:
        """Deal a card from the deck with cut card simulation"""
        # Reshuffle when deck is low (simulate cut card approx 75% penetration for 6 decks)
        # 6 decks = 312 cards. 25% remaining = 78 cards.
        if len(self.deck) < (312 * 0.25): 
            logger.info(f"Cut card reached in room {self.code} (deck size: {len(self.deck)}), reshuffling.")
            self.shuffle_deck()
        
        if self.deck:
            card = self.deck.pop()
            # logger.debug(f"Dealt card {card} in room {self.code}. Deck size: {len(self.deck)}")
            return card
        else: # Should ideally not happen due to reshuffle logic
            logger.error(f"Deck empty in room {self.code}! Attempting emergency reshuffle.")
            self.shuffle_deck()
            if self.deck: return self.deck.pop()
            logger.critical(f"CRITICAL: Deck still empty after emergency reshuffle in room {self.code}")
            return None

    def get_active_players_for_new_hand(self) -> List[Player]:
        """Get list of players eligible to participate in a new hand (have bets, not sitting out etc.)"""
        eligible = [p for p in self.players.values() 
                   if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED, PlayerStatus.DISCONNECTED] 
                   and p.money >= self.min_bet # Must have at least min_bet
                   and not p.is_ai # Exclude AI for now
                   and not p.is_banned
                   and any(h.bet_amount > 0 for h in p.hands) # Must have placed a bet for this hand
                   ]
        
        # logger.debug(f"Room {self.code} has {len(eligible)} active players for new hand")
        return eligible


    def advance_to_next_player(self):
        """Move to the next player's turn or next hand for current player."""
        current_player = self.players.get(self.current_player_id)
        
        if not current_player:
            # This case means something went wrong or all players are done.
            # Transition to dealer's turn if no current player is set and turn order exhausted.
            if self._current_player_turn_index >= len(self._player_turn_order) -1 :
                 self.current_player_id = None
                 self.phase = GamePhase.DEALER_TURN
                 logger.info(f"No current player, or turn order exhausted in room {self.code}. Moving to dealer turn.")
            return

        # Check if current player has more hands to play (due to splits)
        if (current_player.status == PlayerStatus.ACTIVE and
            current_player.current_hand_index < len(current_player.hands) - 1):
            current_player.current_hand_index += 1
            # If the new current hand is Blackjack or already busted (e.g. split Aces get one card), advance again
            if not current_player.can_act():
                self.advance_to_next_player() # Recursive call to check next hand or player
            else:
                logger.info(f"Player {current_player.name} moving to hand {current_player.current_hand_index + 1} in room {self.code}")
            return

        # Current player finished all their hands, or their single hand. Move to next player in order.
        # Reset current player's hand index for next round (though they are done for this round)
        current_player.current_hand_index = 0 

        self._current_player_turn_index += 1
        if self._current_player_turn_index < len(self._player_turn_order):
            next_player_id = self._player_turn_order[self._current_player_turn_index]
            next_player = self.players.get(next_player_id)
            
            if next_player and next_player.status == PlayerStatus.ACTIVE: # Player is still active (not blackjack, bust, surrender)
                self.current_player_id = next_player_id
                logger.info(f"Advanced to next player: {next_player.name} in room {self.code}")
                # If this next player immediately cannot act (e.g. they got blackjack), advance again.
                if not next_player.can_act():
                    self.advance_to_next_player()
            else: # Next player in order is not active (e.g. blackjack), try next one
                self.advance_to_next_player()
        else:
            # All players in the turn order have completed their turns
            self.current_player_id = None
            self.phase = GamePhase.DEALER_TURN
            logger.info(f"All players completed turns. Moving to dealer turn in room {self.code}")


    def update_activity(self):
        """Update last activity timestamp for the room"""
        self.last_activity = datetime.now()

    def is_inactive(self) -> bool:
        """Check if room has been inactive too long"""
        return (datetime.now() - self.last_activity).total_seconds() > GameConfig.INACTIVE_ROOM_TIMEOUT

    def get_player_count(self) -> int:
        """Get count of human players currently in the room (not disconnected)"""
        return len([p for p in self.players.values() 
                    if not p.is_ai and not p.is_banned and p.status != PlayerStatus.DISCONNECTED])

    def add_chat_message(self, player_id: str, message: str) -> bool:
        """Add chat message with enhanced moderation and formatting"""
        player = self.players.get(player_id)
        if not player:
            logger.warning(f"Chat message from unknown player_id {player_id} in room {self.code}")
            return False

        if player.is_banned:
            logger.warning(f"Banned player {player.name} attempted to chat in room {self.code}")
            return False

        # Simple content moderation
        message_lower = message.lower()
        for banned_word in SecurityConfig.BANNED_WORDS:
            if banned_word in message_lower:
                player.add_warning(f"Used inappropriate language in chat: '{banned_word}'")
                # Optionally, don't add the message or replace word
                # For now, we'll let it through but warn.
                # return False # If we want to block the message
                message = message.replace(banned_word, "*" * len(banned_word)) # Censor

        chat_msg = {
            "player_id": player_id,
            "player_name": player.name,
            "player_color": player.color,
            "message": message, # Potentially censored message
            "timestamp": time.time(),
            "formatted_time": datetime.now().strftime("%H:%M:%S"),
            "is_vip": player.is_vip
        }

        self.chat_messages.append(chat_msg)
        
        # Keep only recent messages
        if len(self.chat_messages) > GameConfig.MAX_CHAT_MESSAGES:
            self.chat_messages = self.chat_messages[-GameConfig.MAX_CHAT_MESSAGES:]

        self.update_activity()
        return True

    def to_dict(self, include_sensitive: bool = False) -> Dict[str, Any]:
        """Convert room to dictionary for listings or admin views"""
        base_data = {
            "code": self.code,
            "name": self.name,
            "phase": self.phase.value,
            "players": self.get_player_count(), # Active, non-disconnected human players
            "max_players": self.max_players,
            "hand_number": self.hand_number,
            "created_at": self.created_at.isoformat(),
            "is_public": self.is_public,
            "has_password": bool(self.password),
            "is_premium": self.is_premium,
            "tournament_mode": self.tournament_mode,
            "min_bet": self.min_bet,
            "max_bet": self.max_bet
        }

        if include_sensitive: # For admin panel or detailed stats
            base_data.update({
                "owner_id": self.owner_id,
                "spectators_count": len(self.spectators),
                "last_activity": self.last_activity.isoformat(),
                "deck_size": len(self.deck),
                "total_chat_messages": len(self.chat_messages),
                # Could add list of player IDs, etc.
            })

        return base_data

# Enhanced Game Logic Class
class RoyalBlackjackGame:
    """Main game engine for Royal Blackjack 3D with enterprise features"""
    
    def __init__(self):
        self.rooms: Dict[str, Room] = {}
        self.connections: Dict[str, WebSocket] = {} # Maps connection_id (player_id) to WebSocket object
        self.player_rooms: Dict[str, str] = {} # Maps player_id to room_code
        
        # Rate limiting dictionaries
        self.rate_limits: Dict[str, List[float]] = defaultdict(list) # For chat messages
        self.action_rate_limits: Dict[str, List[float]] = defaultdict(list) # For game actions
        self.ip_rate_limits: Dict[str, List[float]] = defaultdict(list) # For connections/requests from IP
        
        self.banned_ips: Set[str] = set()
        self.running = True # Controls the main game loop
        self.maintenance_mode = False # For server maintenance
        
        # Enhanced server statistics
        self.stats = {
            'total_rooms_created': 0,
            'total_players_joined_server': 0, # Count of unique players joining server
            'total_hands_played_server': 0, # Sum of hands from all rooms
            'total_money_wagered_server': 0,
            'total_money_won_by_players_server': 0, # Net winnings by players
            'server_start_time': datetime.now(),
            'peak_concurrent_players': 0,
            'peak_concurrent_rooms': 0,
            'total_chat_messages_server': 0,
            'total_bans_issued': 0,
            'total_warnings_issued': 0,
            'uptime': 0 # Calculated in get_server_stats
        }
        
        # Security tracking
        self.security_events: List[Dict] = []
        self.suspicious_ips: Dict[str, int] = defaultdict(int) # Count of suspicious activities by IP
        
        logger.info("🎰 Royal Blackjack 3D Game Engine initialized with enterprise features")

    def generate_room_code(self) -> str:
        """Generate a unique 6-character room code"""
        attempts = 0
        while attempts < 10000: # Increased attempts for larger scale
            code = ''.join(random.choices('ABCDEFGHJKLMNPQRSTUVWXYZ23456789', k=6))
            if code not in self.rooms:
                return code
            attempts += 1
        
        # Fallback if somehow all simple codes are taken (highly unlikely)
        timestamp_suffix = str(int(time.time()*100))[-4:] # more unique suffix
        fallback_code = f"RB{timestamp_suffix}"
        logger.warning(f"High attempts for room code generation, using fallback: {fallback_code}")
        return fallback_code


    def log_security_event(self, event_type: str, details: Dict[str, Any]):
        """Log security events for monitoring and potential action"""
        event = {
            'timestamp': datetime.now().isoformat(),
            'type': event_type,
            'details': details
        }
        self.security_events.append(event)
        
        # Keep only recent N security events to manage memory
        if len(self.security_events) > 2000: # Increased limit
            self.security_events = self.security_events[-2000:]
        
        logger.warning(f"SECURITY EVENT: {event_type} - {details}")


    def check_ip_rate_limit(self, ip_address: str) -> bool:
        """Check IP-based rate limiting for connections/requests"""
        if ip_address in self.banned_ips:
            logger.warning(f"Blocked request from BANNED IP: {ip_address}")
            return False
            
        current_time = time.time()
        # Clean old timestamps (older than 1 minute)
        self.ip_rate_limits[ip_address] = [
            t for t in self.ip_rate_limits[ip_address] 
            if current_time - t <= 60.0  # 1 minute window
        ]
        
        if len(self.ip_rate_limits[ip_address]) >= SecurityConfig.IP_RATE_LIMIT:
            self.suspicious_ips[ip_address] += 1
            self.log_security_event('ip_rate_limit_exceeded', {'ip': ip_address, 'count': len(self.ip_rate_limits[ip_address])})
            
            # Consider temporary IP ban if suspicious activity threshold is met
            if self.suspicious_ips[ip_address] >= SecurityConfig.SUSPICIOUS_ACTIVITY_THRESHOLD:
                self.banned_ips.add(ip_address) # This is a permanent ban in current logic, could be temp
                self.log_security_event('ip_auto_banned', {'ip': ip_address, 'reason': 'excessive_rate_limit_violations'})
                # Reset suspicious count after ban
                del self.suspicious_ips[ip_address] 
            
            return False
        
        self.ip_rate_limits[ip_address].append(current_time)
        return True

    def create_room(self, creator_player_id: str, room_name: Optional[str] = None, password: Optional[str] = None) -> Optional[str]:
        """Create a new game room with enhanced features"""
        if len(self.rooms) >= GameConfig.MAX_ROOMS:
            logger.warning(f"Maximum number of rooms ({GameConfig.MAX_ROOMS}) reached. Cannot create new room.")
            return None
        
        room_code = self.generate_room_code()
        # Sanitize room name
        default_room_name = f"Royal Table {room_code}"
        final_room_name = default_room_name
        if room_name and room_name.strip():
            final_room_name = room_name.strip()[:SecurityConfig.MAX_ROOM_NAME_LENGTH]
            # Basic check for banned words in room name
            for banned_word in SecurityConfig.BANNED_WORDS:
                if banned_word in final_room_name.lower():
                    final_room_name = default_room_name # Revert to default if banned word
                    logger.warning(f"Banned word in room name '{room_name}', reverted to default for room {room_code}")
                    break
        
        # Hashing password if provided (important for security, though not fully utilized without DB)
        hashed_password = hashlib.sha256(password.encode()).hexdigest() if password else None

        room = Room(
            code=room_code, 
            name=final_room_name, 
            players={}, 
            spectators=set(),
            deck=[], # Initialized in __post_init__
            dealer_hand=Hand(), # Initialized in __post_init__
            owner_id=creator_player_id,
            password=hashed_password, # Store hashed password
            is_public=not bool(hashed_password) # Public if no password
        )
        
        self.rooms[room_code] = room
        self.stats['total_rooms_created'] += 1
        
        # Update peak rooms
        if len(self.rooms) > self.stats['peak_concurrent_rooms']:
            self.stats['peak_concurrent_rooms'] = len(self.rooms)
        
        logger.info(f"Room '{room_code}' ('{final_room_name}') created by player {creator_player_id}")
        return room_code

    def join_room(self, room_code: str, player_id: str, player_name: str, 
                  password_attempt: Optional[str] = None, ip_address: Optional[str] = None) -> bool:
        """Join a player to a room with enhanced validation and re-join logic"""
        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"Attempt to join non-existent room '{room_code}' by player {player_id}")
            return False

        # Check password if room is private
        if room.password:
            if not password_attempt:
                logger.warning(f"Password required for room '{room_code}', none provided by player {player_id}")
                return False
            hashed_password_attempt = hashlib.sha256(password_attempt.encode()).hexdigest()
            if room.password != hashed_password_attempt:
                logger.warning(f"Invalid password for room '{room_code}' by player {player_id}")
                # Log failed attempt for security
                self.log_security_event('failed_room_join_password', {'room': room_code, 'player': player_id, 'ip': ip_address})
                return False
        
        # Validate and clean player name
        if not player_name or not player_name.strip():
            logger.warning(f"Invalid player name (empty) for player {player_id}")
            return False # Or assign a default guest name

        cleaned_player_name = player_name.strip()[:SecurityConfig.MAX_NAME_LENGTH]
        name_lower = cleaned_player_name.lower()
        for banned_word in SecurityConfig.BANNED_WORDS:
            if banned_word in name_lower:
                logger.warning(f"Banned word in player name: '{cleaned_player_name}', join rejected for player {player_id}")
                # Optionally assign a generic name or reject
                return False

        # Handle rejoining player or new player
        if player_id in room.players:  
            # Player is rejoining (was previously in this room)
            rejoining_player = room.players[player_id]
            if rejoining_player.is_banned:
                logger.warning(f"BANNED player {player_id} ('{rejoining_player.name}') attempted to rejoin room {room_code}")
                return False
                
            rejoining_player.connection_id = player_id # Update connection_id to current WebSocket
            rejoining_player.name = cleaned_player_name # Allow name update on rejoin
            rejoining_player.status = PlayerStatus.ACTIVE # Mark as active again
            rejoining_player.update_activity()
            rejoining_player.ip_address = ip_address # Update IP
            # Clear reconnect token as they have reconnected
            rejoining_player.reconnect_token = None 
            logger.info(f"Player {cleaned_player_name} ({player_id}) RE-JOINED room {room_code}")
        else:  
            # New player joining this room
            if room.get_player_count() >= room.max_players:
                logger.warning(f"Room {room_code} is full ({room.max_players} players). Cannot add {cleaned_player_name}")
                return False

            colors = ['#FF6B6B', '#4ECDC4', '#45B7D1', '#96CEB4', '#FFEAA7', '#DDA0DD', 
                      '#98D8C8', '#F7DC6F', '#FF7675', '#74B9FF', '#00B894', '#FDCB6E']
            color = colors[len(room.players) % len(colors)] # Assign a color
            
            player = Player(
                id=player_id, 
                name=cleaned_player_name, 
                color=color,
                connection_id=player_id, # WebSocket ID
                ip_address=ip_address,
                # user_agent can be captured from websocket.headers if needed
            )
            
            room.players[player_id] = player
            self.stats['total_players_joined_server'] += 1
            
            # Update peak concurrent players globally
            current_total_players = sum(r.get_player_count() for r in self.rooms.values())
            if current_total_players > self.stats['peak_concurrent_players']:
                self.stats['peak_concurrent_players'] = current_total_players
            
            logger.info(f"Player {cleaned_player_name} ({player_id}) joined room {room_code}")

        self.player_rooms[player_id] = room_code
        room.update_activity()
        return True

    def leave_room(self, player_id: str, force_remove: bool = False):
        """Handle player leaving a room or disconnecting."""
        room_code = self.player_rooms.pop(player_id, None)
        if not room_code or room_code not in self.rooms:
            if room_code: logger.warning(f"Player {player_id} tried to leave room {room_code}, but room no longer exists.")
            return

        room = self.rooms[room_code]
        player_left_name = "Unknown Player"

        if player_id in room.players:
            player_obj = room.players[player_id]
            player_left_name = player_obj.name
            
            if force_remove or player_obj.is_banned: # Immediate removal
                del room.players[player_id]
                logger.info(f"Player {player_left_name} ({player_id}) forcibly removed from room {room_code}")
            else: # Mark as disconnected, allow potential rejoin
                player_obj.status = PlayerStatus.DISCONNECTED
                player_obj.connection_id = None # Clear active connection
                player_obj.generate_reconnect_token() # For secure rejoin if implemented
                player_obj.update_activity() # Update last activity to start SESSION_TIMEOUT
                logger.info(f"Player {player_left_name} ({player_id}) marked as disconnected from room {room_code}. Token: {player_obj.reconnect_token[:8]}...")
        
        room.spectators.discard(player_id) # Also remove from spectators if they were one

        # If the leaving player was the current turn, advance turn
        if room.current_player_id == player_id and room.phase == GamePhase.PLAYER_TURNS:
            logger.info(f"Current player {player_left_name} left/disconnected. Advancing turn in room {room_code}.")
            room.advance_to_next_player()
            # If advance_to_next_player leads to dealer_turn, it will call _play_dealer_hand
            if room.phase == GamePhase.DEALER_TURN and room.current_player_id is None:
                 # This can happen if all players disconnect or finish turns quickly
                self._play_dealer_hand(room)


        # Room ownership transfer if owner leaves
        if room.owner_id == player_id:
            active_players_in_room = [pid for pid, p in room.players.items() if p.status != PlayerStatus.DISCONNECTED and not p.is_ai]
            if active_players_in_room:
                # Transfer to the longest-staying active player (or first in list as fallback)
                # Sorting by join_time to find the "oldest" active player
                active_players_in_room.sort(key=lambda pid: room.players[pid].join_time)
                new_owner_id = active_players_in_room[0]
                room.owner_id = new_owner_id
                logger.info(f"Room {room_code} ownership transferred from {player_left_name} to {room.players[new_owner_id].name}")
            else:
                room.owner_id = None # No one to transfer to
                logger.info(f"Room {room_code} owner {player_left_name} left. No active players to transfer ownership.")

        # Check if room is now empty and should be cleaned up sooner
        # (Actual deletion handled by cleanup_inactive_rooms based on last_activity)
        if not room.get_player_count() and not room.spectators:
            logger.info(f"Room {room_code} is now empty after {player_left_name} left. It will be cleaned up if inactive.")
        
        room.update_activity()


    def start_game(self, room_code: str, initiator_id: str) -> bool:
        """Start a new game round in the room."""
        room = self.rooms.get(room_code)
        if not room:
            logger.error(f"Cannot start game: room {room_code} not found.")
            return False

        if room.owner_id != initiator_id:
            logger.warning(f"Non-owner {initiator_id} attempted to start game in room {room_code}.")
            return False

        if room.phase not in [GamePhase.WAITING, GamePhase.GAME_OVER]:
            logger.warning(f"Cannot start game: room {room_code} is already in phase {room.phase.value}.")
            return False

        # Players eligible for this hand are those who have placed a bet and are active
        players_for_new_hand = room.get_active_players_for_new_hand()
        if not players_for_new_hand:
            logger.warning(f"Cannot start game in room {room_code}: No players have placed bets or are eligible.")
            return False

        logger.info(f"Starting game in room {room_code} with {len(players_for_new_hand)} players. Initiated by {initiator_id}.")
        
        room.phase = GamePhase.DEALING
        room.hand_number += 1
        self.stats['total_hands_played_server'] += 1
        room.shuffle_deck() # Fresh shuffle for new game round
        room.dealer_hand = Hand() # Reset dealer's hand

        # Prepare players for the new hand
        for player in room.players.values():
            if player in players_for_new_hand: # Only affects players participating in this hand
                player.stats.total_hands_played += 1
                # Bet amount is already set from WAITING phase.
                # Money was deducted when bet was placed.
                self.stats['total_money_wagered_server'] += player.get_current_hand().bet_amount
                # Reset hand cards, keep bet
                current_bet = player.get_current_hand().bet_amount
                player.reset_for_new_hand() # This creates a new Hand()
                player.get_current_hand().bet_amount = current_bet # Restore bet to new hand
            elif player.status == PlayerStatus.ACTIVE : # Player was active but didn't bet
                 player.reset_for_new_hand() # Reset their hand, bet will be 0

        # Set up turn order for *this specific hand* based on who bet
        room._player_turn_order = [p.id for p in players_for_new_hand]
        # Optionally shuffle turn order each round for fairness, or keep fixed seating order
        # random.shuffle(room._player_turn_order) 
        room._current_player_turn_index = -1 # Will be incremented by advance_to_next_player
        
        room.update_activity()
        # Cards will be dealt by game_loop when it sees DEALING phase
        return True


    def deal_initial_cards(self, room_code: str):
        """Deal initial two cards to each participating player and the dealer."""
        room = self.rooms.get(room_code)
        if not room or room.phase != GamePhase.DEALING:
            return

        active_players_in_hand = [room.players[pid] for pid in room._player_turn_order if pid in room.players]
        
        # Deal two rounds of cards
        for _ in range(2):
            # Players first
            for player in active_players_in_hand:
                if len(player.get_current_hand().cards) < 2:
                    card = room.deal_card()
                    if card:
                        player.get_current_hand().cards.append(card)
            # Then dealer
            if len(room.dealer_hand.cards) < 2:
                card = room.deal_card()
                if card:
                    room.dealer_hand.cards.append(card)

        # Check for player blackjacks and update status
        for player in active_players_in_hand:
            if player.get_current_hand().is_blackjack():
                player.status = PlayerStatus.BLACKJACK
                player.stats.total_blackjacks += 1
                logger.info(f"Player {player.name} has Blackjack in room {room_code}!")
        
        # Determine first player to act
        room.phase = GamePhase.PLAYER_TURNS
        room._current_player_turn_index = -1 # Reset before advancing
        self.set_next_acting_player(room) # Find the first player who needs to act

        room.update_activity()
        logger.info(f"Initial cards dealt in room {room_code}. Dealer up-card: {room.dealer_hand.cards[0] if room.dealer_hand.cards else 'N/A'}")

    def set_next_acting_player(self, room:Room):
        """ Sets the current_player_id to the next player who needs to act. """
        for i in range(len(room._player_turn_order)):
            player_id_to_check = room._player_turn_order[i]
            player_to_check = room.players.get(player_id_to_check)
            if player_to_check and player_to_check.can_act():
                room.current_player_id = player_id_to_check
                room._current_player_turn_index = i
                return
        
        # If no player can act (e.g. all blackjacks, or all busted already which shouldn't happen here)
        room.current_player_id = None
        room.phase = GamePhase.DEALER_TURN
        logger.info(f"No players can act in room {room.code}. Moving to dealer turn.")


    def player_action(self, room_code: str, player_id: str, action_enum: PlayerAction, amount: int = 0) -> bool:
        """Process a player action with comprehensive validation and state updates."""
        room = self.rooms.get(room_code)
        if not room:
            logger.error(f"Room {room_code} not found for player action by {player_id}")
            return False

        player = room.players.get(player_id)
        if not player:
            logger.error(f"Player {player_id} not found in room {room_code} for action")
            return False

        if player.is_banned:
            logger.warning(f"BANNED player {player.id} ('{player.name}') attempted action {action_enum.value}")
            return False
        
        if room.phase != GamePhase.PLAYER_TURNS and action_enum != PlayerAction.PLACE_BET:
            logger.warning(f"Player {player.name} action {action_enum.value} attempted outside of PLAYER_TURNS or WAITING (for bet). Phase: {room.phase.value}")
            return False
        
        if action_enum != PlayerAction.PLACE_BET and room.current_player_id != player_id :
            logger.warning(f"Player {player.name} action {action_enum.value} attempted, but not their turn. Current turn: {room.current_player_id}")
            return False


        logger.info(f"Processing action: Player '{player.name}' ({player_id}), Action: {action_enum.value}, Amount: ${amount}, Room: {room_code}")

        success = False
        try:
            if action_enum == PlayerAction.PLACE_BET:
                success = self._process_place_bet(room, player, amount)
            elif action_enum == PlayerAction.HIT:
                success = self._process_hit(room, player)
            elif action_enum == PlayerAction.STAND:
                success = self._process_stand(room, player)
            elif action_enum == PlayerAction.DOUBLE_DOWN:
                success = self._process_double_down(room, player)
            elif action_enum == PlayerAction.SPLIT:
                success = self._process_split(room, player)
            elif action_enum == PlayerAction.SURRENDER:
                success = self._process_surrender(room, player)
            
            if success:
                player.update_activity()
                room.update_activity()
                # Specific action stats updated within process methods
                # After an action, check if the game should move to the next player or phase
                if action_enum != PlayerAction.PLACE_BET and room.phase == GamePhase.PLAYER_TURNS:
                    if not player.can_act() or action_enum in [PlayerAction.STAND, PlayerAction.DOUBLE_DOWN, PlayerAction.SURRENDER]:
                        # If player busted, stood, doubled (gets one card then stands), or surrendered, or hand is 21.
                        room.advance_to_next_player()
                    
                    # If after advancing, it's dealer's turn, play dealer hand
                    if room.phase == GamePhase.DEALER_TURN and room.current_player_id is None:
                        self._play_dealer_hand(room)

            return success
            
        except Exception as e:
            logger.exception(f"Error processing player action {action_enum.value} for player {player.id} in room {room.code}: {e}")
            return False


    def _process_place_bet(self, room: Room, player: Player, amount: int) -> bool:
        """Process a bet placement with validation."""
        if room.phase != GamePhase.WAITING:
            logger.warning(f"Player {player.name} cannot place bet: room {room.code} not in WAITING phase (is {room.phase.value})")
            return False
        
        if not (room.min_bet <= amount <= room.max_bet):
            logger.warning(f"Player {player.name} invalid bet amount ${amount}. Min: ${room.min_bet}, Max: ${room.max_bet}")
            return False
        if amount > player.money:
            logger.warning(f"Player {player.name} insufficient funds for bet ${amount}. Has: ${player.money}")
            return False

        # Assuming player has one hand at betting stage
        player.hands[0].bet_amount = amount
        # Money is typically deducted when game starts/cards dealt, not at bet placement UI.
        # However, to ensure player has funds, good to check.
        # Actual deduction will happen when hand is confirmed for play.
        
        logger.info(f"Player {player.name} ({player.id}) placed provisional bet of ${amount} in room {room.code}")
        return True


    def _process_hit(self, room: Room, player: Player) -> bool:
        """Process a hit action for the player's current hand."""
        if not player.can_act(): 
            logger.warning(f"Player {player.name} cannot HIT. Not active or cannot act.")
            return False

        current_hand = player.get_current_hand()
        card = room.deal_card()
        if not card: return False # Error logged in deal_card

        current_hand.cards.append(card)
        logger.info(f"Player {player.name} HITS on hand {player.current_hand_index+1}, receives {card}. New hand value: {current_hand.get_value()}")

        if current_hand.is_bust():
            current_hand.result = HandResult.BUST # Mark hand result
            player.stats.total_busts += 1
            logger.info(f"Player {player.name} BUSTS on hand {player.current_hand_index+1} with {current_hand.get_value()}")
            # Status of player (overall) only changes if all hands are bust/done.
            # The can_act() check and advance_to_next_player will handle moving on.
        elif current_hand.get_value() == 21:
            logger.info(f"Player {player.name} hits to 21 on hand {player.current_hand_index+1}.")
            # Player automatically stands on 21.
        
        return True


    def _process_stand(self, room: Room, player: Player) -> bool:
        """Process a stand action for the player's current hand."""
        if not player.can_act():  # Might be slightly redundant due to outer checks, but good for safety
            logger.warning(f"Player {player.name} cannot STAND. Not active or cannot act.")
            return False
        
        # Current hand is marked as "done" implicitly by moving to next hand/player
        # Player's overall status (e.g. PlayerStatus.STANDING) is set if this is their last hand.
        logger.info(f"Player {player.name} STANDS on hand {player.current_hand_index+1} with {player.get_current_hand().get_value()}")
        return True


    def _process_double_down(self, room: Room, player: Player) -> bool:
        """Process a double down action."""
        current_hand = player.get_current_hand()
        if not current_hand.can_double_down():
            logger.warning(f"Player {player.name} cannot DOUBLE DOWN on current hand.")
            return False
        if player.money < current_hand.bet_amount:
            logger.warning(f"Player {player.name} insufficient funds to DOUBLE DOWN. Needs ${current_hand.bet_amount}, has ${player.money}")
            return False

        # Deduct additional bet
        player.money -= current_hand.bet_amount
        player.stats.total_wagered += current_hand.bet_amount # Add to total wagered for this hand
        self.stats['total_money_wagered_server'] += current_hand.bet_amount
        current_hand.bet_amount *= 2
        current_hand.is_doubled = True
        player.stats.total_doubles += 1
        
        card = room.deal_card()
        if not card: return False

        current_hand.cards.append(card)
        logger.info(f"Player {player.name} DOUBLES DOWN on hand {player.current_hand_index+1}. New bet ${current_hand.bet_amount}. Receives {card}. Final value: {current_hand.get_value()}")

        if current_hand.is_bust():
            current_hand.result = HandResult.BUST
            player.stats.total_busts += 1
            logger.info(f"Player {player.name} BUSTS after double down.")
        
        return True


    def _process_split(self, room: Room, player: Player) -> bool:
        """Process a split action."""
        current_hand_idx = player.current_hand_index
        original_hand = player.hands[current_hand_idx]

        if not original_hand.can_split():
            logger.warning(f"Player {player.name} cannot SPLIT current hand.")
            return False
        if player.money < original_hand.bet_amount:
            logger.warning(f"Player {player.name} insufficient funds to SPLIT. Needs ${original_hand.bet_amount}, has ${player.money}")
            return False
        if len(player.hands) >= 4: # Common limit for max number of hands after splits
            logger.warning(f"Player {player.name} cannot SPLIT further, already has {len(player.hands)} hands.")
            return False

        # Deduct money for the new hand's bet
        player.money -= original_hand.bet_amount
        player.stats.total_wagered += original_hand.bet_amount # Add to total wagered for new hand
        self.stats['total_money_wagered_server'] += original_hand.bet_amount

        # Create the new hand
        card_to_move = original_hand.cards.pop() # Take one card from original hand
        new_hand = Hand(cards=[card_to_move], bet_amount=original_hand.bet_amount, is_split=True)
        
        original_hand.is_split = True # Mark original hand as having been split

        # Insert the new hand immediately after the current one for play order
        player.hands.insert(current_hand_idx + 1, new_hand)
        player.stats.total_splits += 1

        # Deal one card to each of the split hands
        card1 = room.deal_card()
        if card1: original_hand.cards.append(card1)
        
        card2 = room.deal_card()
        if card2: new_hand.cards.append(card2)

        logger.info(f"Player {player.name} SPLITS hand {current_hand_idx+1}. Original: {original_hand.cards}, New: {new_hand.cards}")
        
        # Player continues playing the first split hand (original_hand).
        # The advance_to_next_player logic will handle moving to the second split hand.
        # Check if the first split hand is now a blackjack (e.g. split Aces if house rule allows play after split Aces)
        if original_hand.is_blackjack(): # Or just 21 if it's not a natural
            logger.info(f"Player {player.name}'s first split hand is 21/Blackjack.")
        
        return True


    def _process_surrender(self, room: Room, player: Player) -> bool:
        """Process a surrender action."""
        current_hand = player.get_current_hand()
        if not current_hand.can_surrender():
            logger.warning(f"Player {player.name} cannot SURRENDER current hand.")
            return False

        current_hand.is_surrendered = True
        current_hand.result = HandResult.SURRENDER
        refund_amount = current_hand.bet_amount // 2
        # Payout logic will handle refund: hand.payout = refund_amount; player.money += hand.payout
        player.stats.total_surrenders += 1
        
        logger.info(f"Player {player.name} SURRENDERS hand {player.current_hand_index+1}. Bet was ${current_hand.bet_amount}, will be refunded ${refund_amount}.")
        return True


    def _advance_player_turn_unused(self, room: Room): # This was an older unused method name
        """Helper to advance turn, now integrated into Room.advance_to_next_player and player_action"""
        pass


    def _play_dealer_hand(self, room: Room):
        """Play the dealer's hand according to standard casino rules."""
        logger.info(f"Dealer playing hand in room {room.code}. Dealer initial: {room.dealer_hand.cards}")
        
        # Standard rule: Dealer hits until 17 or more. Many casinos hit soft 17.
        # This implementation: Dealer stands on all 17s (hard or soft).
        # To hit soft 17: if dealer_value == 17 and any(c.rank == 'A' for c in room.dealer_hand.cards) and dealer_value_without_ace_as_11 < 7
        is_soft_17 = lambda hand: hand.get_value() == 17 and any(c.rank == 'A' and c.get_blackjack_value() == 11 for c in hand.cards)

        while room.dealer_hand.get_value() < 17 or (room.dealer_hand.get_value() == 17 and GameConfig.DEALER_HIT_THRESHOLD == 16 and is_soft_17(room.dealer_hand)): # Hits soft 17 if config says hit on 16 (meaning hit soft 17)
            # If DEALER_HIT_THRESHOLD is 17, dealer stands on all 17s.
            # If DEALER_HIT_THRESHOLD is 16, dealer hits soft 17.
            if room.dealer_hand.get_value() > GameConfig.DEALER_HIT_THRESHOLD : # Standard: stand on 17+
                break # Dealer stands

            logger.info(f"Dealer hits on {room.dealer_hand.get_value()}")
            card = room.deal_card()
            if card:
                room.dealer_hand.cards.append(card)
                logger.info(f"Dealer receives {card}. New dealer total: {room.dealer_hand.get_value()}")
            else: # Should not happen
                logger.error(f"Dealer ran out of cards to hit in room {room.code}!")
                break 
            
            if room.dealer_hand.is_bust():
                logger.info(f"Dealer BUSTS with {room.dealer_hand.get_value()}")
                break
        
        logger.info(f"Dealer stands with {room.dealer_hand.get_value()} in room {room.code}")
        room.phase = GamePhase.PAYOUT
        self._calculate_payouts(room)


    def _calculate_payouts(self, room: Room):
        """Calculate and distribute payouts based on hand results."""
        logger.info(f"Calculating payouts for room {room.code}. Dealer has: {room.dealer_hand.get_value()}")
        dealer_final_value = room.dealer_hand.get_value()
        dealer_is_bust = room.dealer_hand.is_bust()
        dealer_has_blackjack = room.dealer_hand.is_blackjack()

        for player in room.players.values():
            if player.status == PlayerStatus.DISCONNECTED or player.is_ai: # Skip disconnected or AI for now
                continue

            player_net_win_for_round = 0
            player_total_bet_for_round = 0

            for hand_idx, hand in enumerate(player.hands):
                if hand.bet_amount == 0: # Skip hands that had no bet (e.g. if player didn't bet but was in room)
                    continue
                
                player_total_bet_for_round += hand.bet_amount

                if hand.is_surrendered: # Already marked, payout is half bet
                    hand.result = HandResult.SURRENDER # Ensure it's set
                    hand.payout = hand.bet_amount // 2
                elif hand.is_bust():
                    hand.result = HandResult.BUST # Already marked
                    hand.payout = 0
                elif hand.is_blackjack(): # Player has natural blackjack
                    if dealer_has_blackjack:
                        hand.result = HandResult.PUSH
                        hand.payout = hand.bet_amount # Bet returned
                    else:
                        hand.result = HandResult.BLACKJACK # Player wins 3:2
                        hand.payout = int(hand.bet_amount * (1 + GameConfig.BLACKJACK_PAYOUT))
                elif dealer_is_bust:
                    hand.result = HandResult.WIN
                    hand.payout = hand.bet_amount * 2 # Player wins even money
                elif hand.get_value() > dealer_final_value:
                    hand.result = HandResult.WIN
                    hand.payout = hand.bet_amount * 2
                elif hand.get_value() == dealer_final_value:
                    if dealer_has_blackjack: # Player has 21 (not natural) vs dealer natural
                        hand.result = HandResult.LOSE
                        hand.payout = 0
                    else: # Regular push
                        hand.result = HandResult.PUSH
                        hand.payout = hand.bet_amount
                else: # Player hand value < dealer hand value (and dealer not bust)
                    hand.result = HandResult.LOSE
                    hand.payout = 0
                
                player.money += hand.payout # Add winnings/returned bet to player's money
                player_net_win_for_round += (hand.payout - hand.bet_amount)
                logger.info(f"Player {player.name}, Hand {hand_idx+1}: Bet ${hand.bet_amount}, Result {hand.result.value if hand.result else 'N/A'}, Payout ${hand.payout}. New Balance: ${player.money}")

            # Update player stats for the round
            if player_total_bet_for_round > 0: # Only if they actually played
                if player_net_win_for_round > 0:
                    player.stats.total_hands_won += 1 # Simplistic: count round as won if net positive
                    player.stats.current_streak += 1
                    if player.stats.current_streak > player.stats.best_streak:
                        player.stats.best_streak = player.stats.current_streak
                elif player_net_win_for_round < 0 :
                    player.stats.current_streak = 0
                
                player.stats.total_winnings += player_net_win_for_round
                self.stats['total_money_won_by_players_server'] += player_net_win_for_round

        room.phase = GamePhase.GAME_OVER
        room.update_activity()
        
        asyncio.create_task(self._prepare_next_hand(room.code))


    async def _prepare_next_hand(self, room_code: str, delay: int = GameConfig.AUTO_RESET_DELAY):
        """Prepare room for the next hand after a delay."""
        await asyncio.sleep(delay)
        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"Room {room_code} not found for preparing next hand (might have been cleaned up).")
            return

        # Only reset if still in GAME_OVER, otherwise another action might have occurred
        if room.phase != GamePhase.GAME_OVER:
            logger.info(f"Room {room_code} not in GAME_OVER phase ({room.phase.value}), next hand prep skipped.")
            return

        # Check for active players to continue
        active_human_players = [p for p in room.players.values() if p.status != PlayerStatus.DISCONNECTED and not p.is_ai and p.money >= room.min_bet]
        if not active_human_players:
            logger.info(f"No active players with sufficient funds in room {room_code}. Remaining in GAME_OVER.")
            # Room will eventually be cleaned up if all leave or stay inactive
            return

        room.phase = GamePhase.WAITING
        for player in room.players.values():
            if player.status != PlayerStatus.DISCONNECTED : # Reset for all non-disconnected players
                 player.reset_for_new_hand()
                 if player.money < room.min_bet and player.status != PlayerStatus.ELIMINATED:
                     player.status = PlayerStatus.ELIMINATED # Mark as eliminated if out of funds
                     logger.info(f"Player {player.name} in room {room_code} eliminated (out of funds).")
        
        room.dealer_hand = Hand()
        room.current_player_id = None
        room._player_turn_order = []
        room._current_player_turn_index = 0 # Reset for new turn order setup
        
        logger.info(f"Room {room_code} reset to WAITING phase for next hand.")
        # Game state will be broadcast by the main loop


    def get_game_state(self, room_code: str, for_player_id: str) -> Dict[str, Any]:
        """Get current game state for a specific player (or spectator)."""
        room = self.rooms.get(room_code)
        if not room:
            return {"error": "Room not found"}

        requesting_player_obj = room.players.get(for_player_id)
        is_player_in_room = requesting_player_obj is not None
        is_spectator = for_player_id in room.spectators

        players_data = {}
        for p_id, p_obj in room.players.items():
            # Only include players not marked as fully disconnected for long, or not banned
            if p_obj.status != PlayerStatus.DISCONNECTED or (datetime.now() - p_obj.last_activity).total_seconds() < GameConfig.SESSION_TIMEOUT:
                 if not p_obj.is_banned:
                    players_data[p_id] = p_obj.to_dict(room.current_player_id)

        # Dealer hand: hide hole card if game is in player turns
        dealer_cards_view = []
        dealer_value_view = None

        if room.dealer_hand.cards:
            if room.phase in [GamePhase.DEALING, GamePhase.PLAYER_TURNS] and len(room.dealer_hand.cards) == 2:
                dealer_cards_view.append(room.dealer_hand.cards[0].to_dict()) # Show first card
                dealer_cards_view.append({"suit": "back", "rank": "back", "id": "hidden_dealer_card"}) # Hide second
                dealer_value_view = room.dealer_hand.cards[0].get_blackjack_value() # Value of up-card
            else: # Dealer turn, payout, game over - show all cards
                dealer_cards_view = [card.to_dict() for card in room.dealer_hand.cards]
                dealer_value_view = room.dealer_hand.get_value()
        
        dealer_hand_data = {
            "cards": dealer_cards_view,
            "value": dealer_value_view,
            "is_blackjack": room.dealer_hand.is_blackjack() if room.phase not in [GamePhase.DEALING, GamePhase.PLAYER_TURNS] else None
        }

        game_state = {
            "room_code": room.code,
            "room_name": room.name,
            "phase": room.phase.value,
            "current_player_id": room.current_player_id,
            "players": players_data,
            "dealer_hand": dealer_hand_data,
            "chat_messages": room.chat_messages[-GameConfig.MAX_CHAT_MESSAGES:], # Send recent messages
            "is_player_in_game": is_player_in_room and requesting_player_obj.status != PlayerStatus.DISCONNECTED,
            "is_spectator": is_spectator,
            "spectator_count": len(room.spectators),
            "hand_number": room.hand_number,
            "min_bet": room.min_bet,
            "max_bet": room.max_bet,
            "can_act": (is_player_in_room and 
                       room.current_player_id == for_player_id and 
                       room.phase == GamePhase.PLAYER_TURNS and
                       requesting_player_obj.can_act()),
            "available_actions": self.get_available_actions(room, for_player_id) if is_player_in_room else [],
            "owner_id": room.owner_id,
            "is_premium": room.is_premium,
            "tournament_mode": room.tournament_mode,
            "deck_remaining_estimate": len(room.deck) // 52 if is_player_in_room else None # Approx decks left
        }
        return game_state


    def get_available_actions(self, room: Room, player_id: str) -> List[Dict[str, Any]]:
        """Get available actions for a player, considering game phase and player state."""
        player = room.players.get(player_id)
        if not player: return []

        actions = []
        
        if room.phase == GamePhase.WAITING:
            # Check if player has already placed a bet for this upcoming hand.
            # Assuming new hand means hands[0] is the one for betting.
            if player.hands and player.hands[0].bet_amount == 0 and player.money >= room.min_bet:
                actions.append({
                    "action": PlayerAction.PLACE_BET.value,
                    "label": "Place Bet",
                    "min_amount": room.min_bet,
                    "max_amount": min(room.max_bet, player.money),
                    "description": f"Place a bet between ${room.min_bet} and ${min(room.max_bet, player.money)}"
                })
        elif room.phase == GamePhase.PLAYER_TURNS and room.current_player_id == player_id and player.can_act():
            current_hand = player.get_current_hand()
            
            actions.append({"action": PlayerAction.HIT.value, "label": "Hit", "description": "Take another card"})
            actions.append({"action": PlayerAction.STAND.value, "label": "Stand", "description": "Keep current hand"})
            
            if current_hand.can_double_down() and player.money >= current_hand.bet_amount:
                actions.append({
                    "action": PlayerAction.DOUBLE_DOWN.value, "label": "Double Down",
                    "description": f"Double bet to ${current_hand.bet_amount * 2}, take one more card.",
                    "cost": current_hand.bet_amount
                })
            
            if current_hand.can_split() and player.money >= current_hand.bet_amount and len(player.hands) < 4:
                 actions.append({
                    "action": PlayerAction.SPLIT.value, "label": "Split",
                    "description": f"Split pair into two hands. Cost: ${current_hand.bet_amount}.",
                    "cost": current_hand.bet_amount
                })
            
            if current_hand.can_surrender(): # Typically only available as first action on two cards
                actions.append({
                    "action": PlayerAction.SURRENDER.value, "label": "Surrender",
                    "description": f"Forfeit half your bet (${current_hand.bet_amount // 2} loss)."
                })
        return actions


    def check_rate_limit(self, client_id: str, limit_type: str = "message") -> bool:
        """Enhanced rate limiting for messages and actions."""
        limit_config = {
            "message": (self.rate_limits, GameConfig.RATE_LIMIT_MESSAGES_PER_SECOND),
            "action": (self.action_rate_limits, GameConfig.RATE_LIMIT_ACTIONS_PER_SECOND)
        }
        if limit_type not in limit_config:
            logger.error(f"Unknown rate limit type: {limit_type}")
            return False # Default to deny for unknown types

        limit_dict, max_per_second = limit_config[limit_type]
        current_time = time.time()
        
        # Clean old entries (older than 1 second)
        limit_dict[client_id] = [t for t in limit_dict[client_id] if current_time - t <= 1.0]

        if len(limit_dict[client_id]) < max_per_second:
            limit_dict[client_id].append(current_time)
            return True
        else:
            logger.warning(f"Rate limit exceeded for client {client_id} (type: {limit_type}). Count: {len(limit_dict[client_id])}")
            # Log security event for excessive rate limiting
            self.log_security_event(f'{limit_type}_rate_limit_exceeded', {'client_id': client_id, 'count': len(limit_dict[client_id])})
            player = next((p for room in self.rooms.values() for p_id, p in room.players.items() if p_id == client_id), None)
            if player: player.add_warning(f"Exceeded {limit_type} rate limit.")
            return False


    def cleanup_inactive_rooms(self):
        """Enhanced cleanup of inactive rooms and disconnected players within rooms."""
        current_time = datetime.now()
        rooms_to_delete_codes = []
        
        for room_code, room in list(self.rooms.items()): # Iterate over a copy for safe deletion
            # 1. Clean up long-disconnected players from this room
            disconnected_player_ids_to_remove = []
            for player_id, player in room.players.items():
                if player.status == PlayerStatus.DISCONNECTED:
                    # Check if player's session timeout has expired
                    if (current_time - player.last_activity).total_seconds() > GameConfig.SESSION_TIMEOUT:
                        disconnected_player_ids_to_remove.append(player_id)
            
            for player_id in disconnected_player_ids_to_remove:
                if player_id in room.players: # Ensure player still exists before deleting
                    logger.info(f"Removing long-disconnected player {room.players[player_id].name} ({player_id}) from room {room_code} due to session timeout.")
                    del room.players[player_id]
                    # Player room mapping should also be cleared if they are fully removed.
                    if player_id in self.player_rooms and self.player_rooms[player_id] == room_code:
                        del self.player_rooms[player_id]


            # 2. Check if the room itself is inactive and empty (or only contains long-disconnected players)
            # A room is considered for deletion if it's past INACTIVE_ROOM_TIMEOUT AND truly empty.
            active_players_in_room = room.get_player_count() # Counts non-disconnected humans
            
            if active_players_in_room == 0 and not room.spectators:
                if room.is_inactive(): # Inactive for INACTIVE_ROOM_TIMEOUT
                    rooms_to_delete_codes.append(room_code)
                    logger.info(f"Room {room_code} marked for deletion: empty and inactive for over {GameConfig.INACTIVE_ROOM_TIMEOUT}s.")
            else:
                # If room has players or spectators, just update its activity to prevent premature cleanup
                # if no game actions are happening but players are present.
                # This is implicitly handled by game actions updating room.last_activity.
                # If players are just sitting, room.last_activity won't update, which is correct.
                pass
        
        # Delete marked rooms
        for room_code_to_delete in rooms_to_delete_codes:
            if room_code_to_delete in self.rooms:
                del self.rooms[room_code_to_delete]
                logger.info(f"Successfully deleted inactive room: {room_code_to_delete}")
            # Associated player_rooms entries are cleared when players leave or are removed.

    def get_server_stats(self) -> Dict[str, Any]:
        """Get comprehensive server statistics for monitoring."""
        current_time = datetime.now()
        uptime_seconds = (current_time - self.stats['server_start_time']).total_seconds()
        
        active_human_players_total = sum(room.get_player_count() for room in self.rooms.values())
        
        # A room is "active" if it has players and isn't stale
        active_game_rooms = len([rc for rc, r in self.rooms.items() if r.get_player_count() > 0 and not r.is_inactive()])

        return {
            "status": "maintenance" if self.maintenance_mode else "healthy",
            "server_version": "1.0.0 Production",
            "current_time_utc": current_time.isoformat(),
            "active_rooms_count": active_game_rooms,
            "total_rooms_count": len(self.rooms),
            "active_players_count": active_human_players_total,
            "total_websocket_connections": len(self.connections),
            "uptime_seconds": int(uptime_seconds),
            "uptime_formatted": str(timedelta(seconds=int(uptime_seconds))),
            "memory_usage_estimate_mb": round((len(self.rooms) * 0.1 + active_human_players_total * 0.02 + len(self.connections) * 0.01),2), # Very rough estimate
            "security_info": {
                "banned_ip_count": len(self.banned_ips),
                "logged_security_event_count": len(self.security_events),
                "suspicious_ip_activity_count": len(self.suspicious_ips),
                "total_warnings_issued_server": self.stats.get('total_warnings_issued', 0),
                "total_bans_issued_server": self.stats.get('total_bans_issued', 0)
            },
            "global_game_stats": self.stats # Contains totals like rooms_created, hands_played etc.
        }

    def get_room_list(self) -> List[Dict[str, Any]]:
        """Get list of public rooms, filterable and sortable in future."""
        public_rooms_data = []
        for room_code, room in self.rooms.items():
            # Only list rooms that are public, not password protected, and have active players or are new
            if room.is_public and not room.password:
                # Consider a room "listable" if it has players or was very recently created
                is_recent = (datetime.now() - room.created_at).total_seconds() < 600 # e.g. 10 mins
                if room.get_player_count() > 0 or is_recent:
                    public_rooms_data.append({
                        "code": room.code,
                        "name": room.name,
                        "players": room.get_player_count(),
                        "max_players": room.max_players,
                        "phase": room.phase.value, # Could show WAITING, GAME_OVER
                        "created": room.created_at.strftime("%Y-%m-%d %H:%M:%S UTC"),
                        "min_bet": room.min_bet,
                        "max_bet": room.max_bet,
                        "is_premium": room.is_premium,
                        "tournament_mode": room.tournament_mode
                    })
        
        # Sort by number of players (desc) then creation time (desc)
        public_rooms_data.sort(key=lambda x: (x["players"], x["created"]), reverse=True)
        return public_rooms_data[:100]  # Limit to N rooms in the list

# Global game instance
game = RoyalBlackjackGame()

# Enhanced Pydantic Models (mostly unchanged from provided, good as is)
class WSMessage(BaseModel):
    action: str = PydanticField(min_length=1, max_length=50)
    payload: dict = PydanticField(default_factory=dict)

class CreateRoomPayload(BaseModel):
    player_name: str = PydanticField(min_length=1, max_length=SecurityConfig.MAX_NAME_LENGTH)
    room_name: Optional[str] = PydanticField(default=None, max_length=SecurityConfig.MAX_ROOM_NAME_LENGTH)
    password: Optional[str] = PydanticField(default=None, min_length=4, max_length=20) # Added min_length for password
    is_premium: bool = PydanticField(default=False)

class JoinRoomPayload(BaseModel):
    room_code: str = PydanticField(min_length=6, max_length=10) # Max length adjusted for potential fallback codes
    player_name: str = PydanticField(min_length=1, max_length=SecurityConfig.MAX_NAME_LENGTH)
    password: Optional[str] = PydanticField(default=None, max_length=20)

class PlayerActionPayload(BaseModel):
    action_type: str = PydanticField(min_length=1, max_length=20) # e.g. "hit", "stand"
    amount: Optional[int] = PydanticField(default=0, ge=0, le=GameConfig.MAX_BET*2) # Max bet * 2 for double down

class ChatMessagePayload(BaseModel):
    message: str = PydanticField(min_length=1, max_length=GameConfig.MAX_MESSAGE_LENGTH)

# Enhanced Game Loop
async def game_loop():
    """Main game loop with enhanced features, error handling, and timing."""
    logger.info("🎰 Royal Blackjack 3D Game Loop started")
    loop_iteration_count = 0
    last_periodic_cleanup_time = time.monotonic()
    
    while game.running:
        loop_start_time = time.monotonic()
        try:
            loop_iteration_count += 1
            
            # Update server uptime (can also be done in get_server_stats)
            game.stats['uptime'] = (datetime.now() - game.stats['server_start_time']).total_seconds()
            
            # Periodic cleanup task (e.g., every 5 minutes)
            if loop_start_time - last_periodic_cleanup_time > GameConfig.ROOM_CLEANUP_INTERVAL:
                game.cleanup_inactive_rooms()
                last_periodic_cleanup_time = loop_start_time
                logger.debug(f"Periodic cleanup executed. Active rooms: {len(game.rooms)}")
            
            # Process rooms in DEALING phase (if cards not dealt yet)
            # This ensures that if start_game is called, deal_initial_cards follows promptly.
            for room_code, room in list(game.rooms.items()): # Iterate copy for safety
                if room.phase == GamePhase.DEALING:
                     # Check if initial cards haven't been dealt yet.
                     # This could be based on a flag or checking if players/dealer have cards.
                     # Assuming deal_initial_cards is idempotent or checks internally.
                    if not any(p.hands and p.hands[0].cards for p_id, p in room.players.items() if p_id in room._player_turn_order) \
                       and not room.dealer_hand.cards :
                        game.deal_initial_cards(room_code)


            # Broadcast game states (e.g., every 200ms for 5 FPS updates, or as needed)
            # The frequency can be adjusted based on performance and desired responsiveness.
            # Current logic is every 10 loops (1 second if loop is 100ms)
            if loop_iteration_count % 5 == 0:  # Broadcast more frequently, e.g., 2 FPS if loop is 100ms
                await broadcast_game_states()

            # Control loop frequency
            loop_duration = time.monotonic() - loop_start_time
            sleep_time = max(0, 0.1 - loop_duration) # Target 10 FPS for the game logic loop itself
            await asyncio.sleep(sleep_time)

        except Exception as e:
            logger.exception(f"CRITICAL ERROR in game_loop iteration {loop_iteration_count}: {e}")
            await asyncio.sleep(1.0) # Pause briefly after a critical error before retrying

    logger.info("🎰 Royal Blackjack 3D Game Loop gracefully stopped.")


async def broadcast_game_states():
    """Efficiently broadcast game states to all relevant connected clients."""
    all_broadcast_tasks = []
    
    for room_code, room in list(game.rooms.items()): # Iterate over a copy
        # Collect all connection_ids (player_ids) that should receive updates for this room
        # These are active players in the room and spectators of this room.
        
        # Using player.connection_id which should be the same as player.id if they are connected
        client_ids_in_room_or_spectating = set()
        for p_id, player_obj in room.players.items():
            if player_obj.connection_id and player_obj.status != PlayerStatus.DISCONNECTED: # Ensure they have an active ws link
                client_ids_in_room_or_spectating.add(player_obj.connection_id)
        client_ids_in_room_or_spectating.update(s_id for s_id in room.spectators if s_id in game.connections)


        for client_id in list(client_ids_in_room_or_spectating): # Iterate copy
            websocket_connection = game.connections.get(client_id)
            if websocket_connection:
                try:
                    # Generate game state specifically for this client_id (player or spectator)
                    game_state_for_client = game.get_game_state(room_code, client_id)
                    if "error" not in game_state_for_client: # Ensure state generation was successful
                        all_broadcast_tasks.append(
                            websocket_connection.send_json({"type": "game_state", "data": game_state_for_client})
                        )
                except WebSocketDisconnect: # Should be caught by main handler, but good practice
                    logger.warning(f"WebSocketDisconnect during broadcast prep for client {client_id} in room {room_code}.")
                    # Clean up this specific connection if it failed here
                    if client_id in game.connections: del game.connections[client_id]
                    game.leave_room(client_id) # Mark as disconnected in game logic
                except Exception as e:
                    logger.error(f"Error preparing/sending game_state for client {client_id} in room {room_code}: {e}")
                    # Consider removing problematic connection or player
            else:
                # If client_id is in room's players/spectators list but not in game.connections, they've disconnected.
                # The main WebSocket disconnect handler should catch this, but good to ensure cleanup.
                logger.debug(f"Client {client_id} listed in room {room_code} but no active WebSocket. Cleanup might be pending.")
                game.leave_room(client_id) # Ensure they are marked as disconnected

    # Execute all broadcasts concurrently
    if all_broadcast_tasks:
        results = await asyncio.gather(*all_broadcast_tasks, return_exceptions=True)
        
        failed_broadcast_count = sum(1 for result in results if isinstance(result, Exception))
        if failed_broadcast_count > 0:
            logger.warning(f"Broadcasting: {failed_broadcast_count} out of {len(all_broadcast_tasks)} sends failed.")
            for i, result in enumerate(results):
                if isinstance(result, Exception):
                    logger.debug(f"Broadcast failure detail: {result} for task {i}")

# Enhanced WebSocket Message Handler (mostly unchanged, already quite good)
async def handle_websocket_message(websocket: WebSocket, player_id: str, message: WSMessage, ip_address: Optional[str] = None):
    """Handle incoming WebSocket messages with enhanced security and validation."""
    action = message.action
    payload = message.payload
    
    if game.maintenance_mode and action not in ['ping', 'get_server_stats']: # Allow ping/stats in maintenance
        await websocket.send_json({"type": "error", "message": "🔧 Server is currently under maintenance. Please try again later."})
        return

    # IP rate limit check for all actions from this IP
    if ip_address and not game.check_ip_rate_limit(ip_address):
        await websocket.send_json({"type": "error", "message": "⚠️ Too many requests from your network. Please slow down."})
        # Optionally, could close connection here if IP is repeatedly abusive
        # await websocket.close(code=status.WS_1008_POLICY_VIOLATION)
        return
    
    try:
        if action == "create_room":
            create_payload = CreateRoomPayload(**payload) # Validation happens here
            room_code = game.create_room(player_id, create_payload.room_name, create_payload.password)
            if not room_code:
                await websocket.send_json({"type": "error", "message": "🏛️ Server is at full capacity or room name invalid. Please try again."})
                return
            # Automatically join the creator to their new room
            if game.join_room(room_code, player_id, create_payload.player_name, create_payload.password, ip_address):
                await websocket.send_json({"type": "room_created", "data": {"room_code": room_code}})
            else: # Should not happen if create_room succeeded and join is immediate
                await websocket.send_json({"type": "error", "message": "❌ Critical error: Failed to join the room you just created."})

        elif action == "join_room":
            join_payload = JoinRoomPayload(**payload)
            if game.join_room(join_payload.room_code.upper(), player_id, join_payload.player_name, join_payload.password, ip_address):
                await websocket.send_json({"type": "room_joined", "data": {"room_code": join_payload.room_code.upper()}})
            else:
                await websocket.send_json({"type": "error", "message": "❌ Failed to join room. It might be full, non-existent, or password incorrect."})
        
        elif action == "spectate_room":
            room_code_to_spectate = payload.get("room_code", "").upper()
            if not room_code_to_spectate or len(room_code_to_spectate) < 6 : # Basic validation
                 await websocket.send_json({"type": "error", "message": "❌ Invalid room code for spectating."})
                 return
            
            room_to_spectate = game.rooms.get(room_code_to_spectate)
            if room_to_spectate:
                # Ensure player is not already IN the room as a player
                if player_id in room_to_spectate.players:
                    await websocket.send_json({"type": "error", "message": "❌ You are already a player in this room. Cannot spectate."})
                    return

                room_to_spectate.spectators.add(player_id)
                game.player_rooms[player_id] = room_code_to_spectate # Associate spectator with room for broadcasts
                await websocket.send_json({"type": "spectating", "data": {"room_code": room_code_to_spectate}})
                logger.info(f"Client {player_id} now spectating room {room_code_to_spectate}")
            else:
                await websocket.send_json({"type": "error", "message": "🏛️ Room not found for spectating."})

        elif action == "leave_room":
            # This is an explicit leave action from client, not a disconnect
            current_room_code = game.player_rooms.get(player_id)
            game.leave_room(player_id, force_remove=True) # Explicit leave = full removal
            await websocket.send_json({"type": "room_left", "data":{"room_code": current_room_code}})
            logger.info(f"Client {player_id} explicitly left room {current_room_code}")


        elif action == "start_game":
            room_code_to_start = game.player_rooms.get(player_id)
            if not room_code_to_start:
                await websocket.send_json({"type": "error", "message": "❌ You are not in a room to start a game."})
                return
            if game.start_game(room_code_to_start, player_id): # start_game has owner check
                # Game state will be broadcast by game loop showing DEALING phase
                logger.info(f"Game successfully initiated in room {room_code_to_start} by owner {player_id}")
                # No immediate state needed, game_loop will handle deal_initial_cards and broadcast
            else:
                await websocket.send_json({"type": "error", "message": "❌ Cannot start game. (Not owner, no bets, wrong phase, etc.)"})

        elif action == "player_action":
            if not game.check_rate_limit(player_id, "action"):
                await websocket.send_json({"type": "error", "message": "⚠️ Action rate limit exceeded. Slow down."})
                return
            
            action_payload = PlayerActionPayload(**payload) # Validation
            room_code_for_action = game.player_rooms.get(player_id)
            if not room_code_for_action:
                await websocket.send_json({"type": "error", "message": "❌ You are not in a room to perform an action."})
                return

            try:
                blackjack_action_enum = PlayerAction(action_payload.action_type.lower()) # Ensure lowercase match
                if not game.player_action(room_code_for_action, player_id, blackjack_action_enum, action_payload.amount):
                    # player_action logs specifics, send generic error to client
                    await websocket.send_json({"type": "error", "message": "❌ Action invalid or not your turn."})
            except ValueError: # Invalid action_type string
                await websocket.send_json({"type": "error", "message": f"❌ Unknown action type: '{action_payload.action_type}'."})

        elif action == "send_chat_message":
            if not game.check_rate_limit(player_id, "message"):
                await websocket.send_json({"type": "error", "message": "⚠️ Chat message rate limit exceeded."})
                return
            
            chat_payload = ChatMessagePayload(**payload) # Validation
            room_code_for_chat = game.player_rooms.get(player_id)
            if not room_code_for_chat:
                await websocket.send_json({"type": "error", "message": "❌ Must be in a room to send chat messages."})
                return

            room_for_chat = game.rooms.get(room_code_for_chat)
            if room_for_chat and room_for_chat.add_chat_message(player_id, chat_payload.message):
                game.stats['total_chat_messages_server'] += 1
                # Successful chat message, state update will broadcast it.
            else: # add_chat_message returned False (e.g. banned word detected and blocked)
                await websocket.send_json({"type": "error", "message": "❌ Message could not be sent (e.g. contains restricted content)."})


        elif action == "get_room_list":
            available_rooms = game.get_room_list()
            await websocket.send_json({"type": "room_list", "data": {"rooms": available_rooms}})

        elif action == "ping":
            await websocket.send_json({"type": "pong", "data": {"client_payload": payload, "server_time_utc": datetime.utcnow().isoformat()}})

        elif action == "get_server_stats": # Allow this even in maintenance
            server_stats = game.get_server_stats()
            await websocket.send_json({"type": "server_stats", "data": server_stats})

        else:
            logger.warning(f"Unknown action '{action}' received from player {player_id}")
            await websocket.send_json({"type": "error", "message": f"❌ Unknown action: {action}"})

    except ValidationError as e: # Pydantic validation error for payload
        logger.warning(f"Payload validation error for action '{message.action}' from {player_id}: {e.errors()}")
        await websocket.send_json({"type": "error", "message": f"❌ Invalid data for '{message.action}': {e.errors()[0]['msg']}"})
    except WebSocketDisconnect:
        raise # Re-raise to be handled by the main WebSocket endpoint's finally block
    except Exception as e:
        logger.exception(f"Unhandled error processing message for action '{message.action}' from {player_id}: {e}")
        try:
            await websocket.send_json({"type": "error", "message": "🔧 A server error occurred. Please try again or contact support."})
        except Exception: # Connection might be dead
            pass

# Enhanced FastAPI Application Setup (lifespan mostly unchanged)
@asynccontextmanager
async def lifespan(app_instance: FastAPI):
    logger.info("🚀 Starting Royal Blackjack 3D Production Server...")
    game_task = asyncio.create_task(game_loop())
    try:
        yield
    finally:
        logger.info("🛑 Shutting down Royal Blackjack 3D server...")
        game.running = False
        disconnect_tasks = [
            conn.send_json({"type": "server_shutdown", "message": "🔧 Server is shutting down. Thanks for playing!"})
            for conn in list(game.connections.values()) # Iterate copy
            if conn.client_state == WebSocketState.CONNECTED # Check if still connected
        ]
        if disconnect_tasks:
            await asyncio.gather(*disconnect_tasks, return_exceptions=True) # Notify clients
        
        # Close all WebSocket connections gracefully
        close_tasks = [conn.close(code=status.WS_1001_GOING_AWAY) for conn in list(game.connections.values())]
        if close_tasks:
            await asyncio.gather(*close_tasks, return_exceptions=True)

        try:
            await asyncio.wait_for(game_task, timeout=10.0) # Wait for game loop
        except asyncio.TimeoutError:
            logger.warning("Game loop did not shut down gracefully in 10s, cancelling task.")
            game_task.cancel()
            try: await game_task
            except asyncio.CancelledError: logger.info("Game loop task successfully cancelled.")
        logger.info("🎰 Royal Blackjack 3D server shutdown complete.")

# FastAPI app instance
app = FastAPI(
    title="Royal Blackjack 3D - Premium Casino Platform",
    description="Professional 3D Multiplayer Blackjack Casino Experience - Production Ready",
    version="1.0.0",
    lifespan=lifespan,
    docs_url="/api/docs" if os.getenv("ENVIRONMENT", "production") == "development" else None,
    redoc_url="/api/redoc" if os.getenv("ENVIRONMENT", "production") == "development" else None
)

# CORS Middleware
app.add_middleware(
    CORSMiddleware,
    allow_origins=os.getenv("ALLOWED_ORIGINS", "*").split(","), # Be specific in production
    allow_credentials=True,
    allow_methods=["*"], # Or specific methods: ["GET", "POST"]
    allow_headers=["*"], # Or specific headers
)

# Static files (if your HTML/JS/CSS are served by FastAPI)
static_dir = os.path.join(os.path.dirname(__file__), "static_frontend") # Example path
if os.path.exists(static_dir) and os.path.isdir(static_dir) :
    app.mount("/static", StaticFiles(directory=static_dir), name="static")
    logger.info(f"Serving static files from {static_dir}")
else:
    logger.warning(f"Static directory '{static_dir}' not found. Static files will not be served by FastAPI.")


# Production HTTP Routes (mostly unchanged)
@app.get("/", response_class=HTMLResponse)
async def get_root_html():
    # This should serve your main index.html for the game
    # For development, you might use FileResponse. For production, this might be handled by Nginx/CDN.
    index_html_path = os.path.join(os.path.dirname(__file__), "index.html")
    if os.path.exists(index_html_path):
        return FileResponse(index_html_path)
    return HTMLResponse(content="<h1>Royal Blackjack 3D Server</h1><p>Frontend not found at expected location.</p>", status_code=404)

@app.get("/api/health")
async def health_check_endpoint():
    stats = game.get_server_stats() # Use the method that calculates uptime etc.
    return {
        "status": stats["status"],
        "timestamp_utc": datetime.utcnow().isoformat(),
        "version": stats["server_version"],
        "uptime_formatted": stats["uptime_formatted"],
        "active_rooms": stats["active_rooms_count"],
        "active_players": stats["active_players_count"]
    }

@app.get("/api/stats/detailed") # More detailed, potentially admin-only
async def get_server_detailed_stats():
    # Add authentication for admin endpoints in production
    # Example: if not is_admin(request): raise HTTPException(status_code=403)
    return game.get_server_stats() # Returns the full stats dictionary

@app.get("/api/rooms/list")
async def get_public_rooms_api():
    return {"rooms": game.get_room_list()}

# Admin endpoint example (needs auth in production)
@app.post("/api/admin/maintenance_mode")
async def set_maintenance_mode_api(enable: bool):
    # Implement proper authentication/authorization for admin actions
    game.maintenance_mode = enable
    action = "enabled" if enable else "disabled"
    logger.critical(f"ADMIN ACTION: Maintenance mode has been {action}.")
    return {"status": "success", "maintenance_mode": game.maintenance_mode}

# WebSocket State (FastAPI 0.100.0+)
from fastapi.websockets import WebSocketState

# Enhanced WebSocket Endpoint
@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    player_id = str(uuid.uuid4()) # Unique ID for this connection session
    client_ip = websocket.client.host if websocket.client else "unknown_ip"
    
    logger.info(f"🔌 New WebSocket connection attempt: {player_id} from IP: {client_ip}")
    
    if client_ip != "unknown_ip" and not game.check_ip_rate_limit(client_ip):
        logger.warning(f"Connection from IP {client_ip} (player_id tentative {player_id}) rejected due to IP rate limit.")
        # No await websocket.accept() means it won't fully connect.
        # Client might see this as a failed connection.
        return 
    
    await websocket.accept()
    game.connections[player_id] = websocket
    logger.info(f"🔌 WebSocket connection ACCEPTED: {player_id} from IP: {client_ip}. Total connections: {len(game.connections)}")
    
    try:
        welcome_msg_data = {
            "player_id": player_id, # This is the session/connection ID client should use
            "message": "🎰 Welcome to the Royal Blackjack 3D Experience!",
            "server_version": game.get_server_stats()["server_version"],
            "timestamp_utc": datetime.utcnow().isoformat(),
        }
        await websocket.send_json({"type": "connected", "data": welcome_msg_data})

        while True:
            if websocket.client_state != WebSocketState.CONNECTED:
                logger.warning(f"WebSocket state for {player_id} is {websocket.client_state}, breaking loop.")
                break
            try:
                raw_data = await websocket.receive_text()
                message_json = json.loads(raw_data)
                ws_message_obj = WSMessage(**message_json) # Pydantic validation
                await handle_websocket_message(websocket, player_id, ws_message_obj, client_ip)
            except WebSocketDisconnect as e: # Explicitly handle this common case
                logger.info(f"WebSocket gracefully disconnected for {player_id} (Code: {e.code}, Reason: '{e.reason}').")
                break # Exit loop on graceful disconnect
            except json.JSONDecodeError:
                logger.warning(f"Invalid JSON received from {player_id} (IP: {client_ip}).")
                await websocket.send_json({"type": "error", "message": "❌ Invalid JSON format."})
            except ValidationError as e: # Pydantic validation failed for WSMessage
                logger.warning(f"WSMessage validation error from {player_id} (IP: {client_ip}): {e.errors()}")
                await websocket.send_json({"type": "error", "message": f"❌ Invalid message structure: {e.errors()[0]['msg']}"})
            except Exception as e: # Catch other unexpected errors in message handling
                logger.exception(f"Unexpected error processing message from {player_id} (IP: {client_ip}): {e}")
                # Avoid sending detailed error back to client in production
                await websocket.send_json({"type": "error", "message": "🔧 Server encountered an issue processing your request."})

    except WebSocketDisconnect as e: # Catch disconnect if it happens outside the loop (e.g. during accept or initial send)
         logger.info(f"WebSocket (outer) disconnected for {player_id} (Code: {e.code}, Reason: '{e.reason}').")
    except Exception as e: # Catchall for other errors during ws lifecycle
        logger.exception(f"Unhandled WebSocket error for connection {player_id} (IP: {client_ip}): {e}")
    finally:
        logger.info(f"🧹 Cleaning up WebSocket connection for {player_id} (IP: {client_ip}).")
        if player_id in game.connections:
            del game.connections[player_id]
        
        # Perform game logic cleanup for the player (e.g., mark as disconnected in room)
        # The force_remove=False (default) is important here for unexpected disconnects,
        # allowing the player to potentially rejoin their session.
        # If it was an explicit "leave_room" action, force_remove=True would have been used there.
        room_code_player_was_in = game.player_rooms.get(player_id)
        game.leave_room(player_id, force_remove=False) 
        logger.info(f"Player {player_id} processed by game.leave_room. Total connections now: {len(game.connections)}")

        # Broadcast updated game state to the room the player left, so others see the change.
        if room_code_player_was_in and room_code_player_was_in in game.rooms:
            room_obj = game.rooms[room_code_player_was_in]
            clients_to_notify_in_room = set()
            for p_obj_id, p_obj_instance in room_obj.players.items():
                if p_obj_instance.connection_id and p_obj_instance.status != PlayerStatus.DISCONNECTED:
                    clients_to_notify_in_room.add(p_obj_instance.connection_id)
            clients_to_notify_in_room.update(s_id for s_id in room_obj.spectators if s_id in game.connections)

            disconnect_broadcast_tasks = []
            for client_id_to_notify in list(clients_to_notify_in_room):
                ws_conn_to_notify = game.connections.get(client_id_to_notify)
                if ws_conn_to_notify and ws_conn_to_notify.client_state == WebSocketState.CONNECTED:
                    try:
                        state_for_notification = game.get_game_state(room_code_player_was_in, client_id_to_notify)
                        if "error" not in state_for_notification:
                            disconnect_broadcast_tasks.append(
                                ws_conn_to_notify.send_json({"type": "game_state", "data": state_for_notification})
                            )
                    except Exception as broadcast_err:
                        logger.error(f"Error preparing/sending disconnect notification to {client_id_to_notify}: {broadcast_err}")
            
            if disconnect_broadcast_tasks:
                await asyncio.gather(*disconnect_broadcast_tasks, return_exceptions=True)
                logger.debug(f"Sent disconnect state updates to {len(disconnect_broadcast_tasks)} clients for room {room_code_player_was_in}")

# Main entry point for Uvicorn (if running script directly)
if __name__ == "__main__":
    # Get host and port from environment variables or use defaults
    host = os.getenv("HOST", "0.0.0.0")
    port = int(os.getenv("PORT", "8000"))
    log_level = os.getenv("LOG_LEVEL", "info").lower()

    logger.info(f"Starting server on {host}:{port} with log level {log_level}")
    
    # For production, use a proper ASGI server like Uvicorn with Gunicorn workers
    # uvicorn.run("your_module_name:app", host="0.0.0.0", port=8000, workers=4)
    uvicorn.run(app, host=host, port=port, log_level=log_level)
