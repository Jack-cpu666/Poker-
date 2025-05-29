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
    SESSION_TIMEOUT = 7200  # 2 hours
    DEALER_HIT_THRESHOLD = 16 # Standard rule is dealer hits on 16 or less, stands on 17. Some casinos hit soft 17.
    ROOM_CLEANUP_INTERVAL = 300  # 5 minutes
    INACTIVE_ROOM_TIMEOUT = 3600  # 1 hour
    HEARTBEAT_INTERVAL = 30
    MAX_MESSAGE_LENGTH = 200
    BLACKJACK_PAYOUT = 1.5  # 3:2 payout
    AUTO_RESET_DELAY = 10  # seconds
    MAX_RECONNECT_ATTEMPTS = 5
    RECONNECT_WINDOW = 300  # 5 minutes

# Security Configuration
class SecurityConfig:
    """Security and validation settings"""
    MAX_NAME_LENGTH = 25
    MAX_ROOM_NAME_LENGTH = 50
    BANNED_WORDS = [
        'cheat', 'hack', 'bot', 'script', 'exploit', 'bug',
        'admin', 'moderator', 'casino', 'scam', 'fraud'
        # Add more common offensive terms as needed
    ]
    IP_RATE_LIMIT = 100  # requests per minute
    SUSPICIOUS_ACTIVITY_THRESHOLD = 50 # Number of rate limit hits before IP is flagged
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
    ACTIVE = "active"
    STANDING = "standing"
    BUST = "bust"
    BLACKJACK = "blackjack"
    SITTING_OUT = "sitting_out" # Player chose to sit out
    ELIMINATED = "eliminated"   # Player has no money or is banned
    DISCONNECTED = "disconnected" # Player's connection dropped

class HandResult(Enum):
    """Result of a completed hand"""
    WIN = "win"
    LOSE = "lose"
    PUSH = "push"
    BLACKJACK = "blackjack" # Player blackjack win
    BUST = "bust"
    SURRENDER = "surrender"

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

    def get_blackjack_value(self, current_total: int = 0) -> int:
        """Return the blackjack value of this card"""
        if self.rank in ['J', 'Q', 'K']:
            return 10
        elif self.rank == 'A':
            # Ace is 11 unless it would bust the hand, then it's 1
            # This logic is better handled at the Hand level get_value
            return 11 # Hand.get_value will adjust if needed
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
    insurance_bet: int = 0 # Future feature
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
                except ValueError:
                    logger.warning(f"Invalid card rank during hand value calculation: {card.rank}")
                    continue

        # Convert aces from 11 to 1 if needed to avoid bust
        while total > 21 and aces > 0:
            total -= 10
            aces -= 1

        return total

    def is_bust(self) -> bool:
        """Check if hand is busted (over 21)"""
        return self.get_value() > 21

    def is_blackjack(self) -> bool:
        """Check if hand is a natural blackjack (21 with 2 cards)"""
        return len(self.cards) == 2 and self.get_value() == 21

    def can_split(self) -> bool:
        """Check if hand can be split"""
        return (len(self.cards) == 2 and
                self.cards[0].rank == self.cards[1].rank and
                not self.is_split) # Can't re-split a split hand easily with this model yet

    def can_double_down(self) -> bool:
        """Check if hand can be doubled down (typically on first two cards)"""
        return len(self.cards) == 2 and not self.is_split # Some rules allow double after split

    def can_surrender(self) -> bool:
        """Check if hand can be surrendered (typically on first two cards, before other actions)"""
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
    total_winnings: int = 0 # Net winnings (payouts - bets)
    total_wagered: int = 0
    session_start: datetime = field(default_factory=datetime.now)
    best_streak: int = 0
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
        return ((self.total_winnings) / self.total_wagered) * 100 # total_winnings is already net

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
            "session_duration": str(datetime.now() - self.session_start).split('.')[0] # Human-readable
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
    avatar: str = "royal_avatar" # Placeholder, could be dynamic
    color: str = "#ffffff" # Default color
    connection_id: Optional[str] = None # To map WebSocket connection if different from player_id
    is_ai: bool = False
    session_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    stats: PlayerStats = field(default_factory=PlayerStats)
    last_activity: datetime = field(default_factory=datetime.now)
    join_time: datetime = field(default_factory=datetime.now)
    ip_address: Optional[str] = None
    user_agent: Optional[str] = None # Could be captured from request headers
    is_vip: bool = False
    warnings: int = 0
    is_banned: bool = False
    ban_reason: Optional[str] = None
    reconnect_token: Optional[str] = None

    def __post_init__(self):
        """Initialize player after creation"""
        if not self.hands: # Ensure there's always at least one hand
            self.hands = [Hand()]

    def get_current_hand(self) -> Hand:
        """Get the hand currently being played"""
        if 0 <= self.current_hand_index < len(self.hands):
            return self.hands[self.current_hand_index]
        return self.hands[0] if self.hands else Hand() # Fallback, though should not happen

    def can_act(self) -> bool:
        """Check if player can take an action on their current hand"""
        if self.status not in [PlayerStatus.ACTIVE]:
            return False

        current_hand = self.get_current_hand()
        return (not current_hand.is_bust() and
                not current_hand.is_surrendered and
                not current_hand.is_blackjack() and # Blackjack hands don't take more actions
                current_hand.get_value() < 21)

    def reset_for_new_hand(self):
        """Reset player for a new hand"""
        self.hands = [Hand()]
        self.current_hand_index = 0
        if self.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED, PlayerStatus.DISCONNECTED]:
            if self.money < GameConfig.MIN_BET: # Check if player has enough money for min_bet
                self.status = PlayerStatus.ELIMINATED
                logger.info(f"Player {self.name} eliminated due to insufficient funds.")
            else:
                self.status = PlayerStatus.ACTIVE

    def update_activity(self):
        """Update last activity timestamp"""
        self.last_activity = datetime.now()

    def generate_reconnect_token(self) -> str:
        """Generate secure reconnect token"""
        self.reconnect_token = secrets.token_urlsafe(32)
        return self.reconnect_token

    def validate_reconnect_token(self, token: str) -> bool:
        """Validate reconnect token"""
        return (self.reconnect_token is not None and
                self.reconnect_token == token and
                (datetime.now() - self.last_activity).total_seconds() < GameConfig.RECONNECT_WINDOW)

    def add_warning(self, reason: str):
        """Add warning to player"""
        self.warnings += 1
        logger.warning(f"Player {self.name} ({self.id}) warned: {reason}. Total warnings: {self.warnings}")
        game.stats['total_warnings_issued'] = game.stats.get('total_warnings_issued',0) + 1

        if self.warnings >= SecurityConfig.AUTO_BAN_THRESHOLD:
            self.ban(f"Auto-banned after {self.warnings} warnings.")

    def ban(self, reason: str):
        """Ban player"""
        self.is_banned = True
        self.ban_reason = reason
        self.status = PlayerStatus.ELIMINATED # Banned players are eliminated
        logger.error(f"Player {self.name} ({self.id}) banned: {reason}")
        game.stats['total_bans_issued'] = game.stats.get('total_bans_issued',0) + 1


    def to_dict(self, current_player_id: Optional[str] = None, include_sensitive: bool = False) -> Dict[str, Any]:
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
            "is_current_player": current_player_id == self.id,
            "is_ai": self.is_ai,
            "is_vip": self.is_vip,
            "session_duration": str(datetime.now() - self.join_time).split('.')[0],
            "stats": self.stats.to_dict()
        }

        if include_sensitive: # For admin views or internal use
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
    players: Dict[str, Player]
    spectators: Set[str] # Set of player_ids
    deck: List[Card]
    dealer_hand: Hand
    current_player_id: Optional[str] = None
    phase: GamePhase = GamePhase.WAITING
    chat_messages: List[Dict] = field(default_factory=list)
    hand_number: int = 0
    created_at: datetime = field(default_factory=datetime.now)
    last_activity: datetime = field(default_factory=datetime.now)
    owner_id: Optional[str] = None
    min_bet: int = GameConfig.MIN_BET
    max_bet: int = GameConfig.MAX_BET
    _player_turn_order: List[str] = field(default_factory=list) # List of player_ids
    _current_player_turn_index: int = 0
    is_public: bool = True
    max_players: int = GameConfig.MAX_PLAYERS_PER_ROOM
    password: Optional[str] = None # Hashed password if implemented
    is_premium: bool = False # Example for different room types
    tournament_mode: bool = False # Example for game modes
    buy_in: int = 0
    prize_pool: int = 0

    def __post_init__(self):
        """Initialize room after creation"""
        if not self.deck:
            self.deck = self.create_deck()
        if not hasattr(self, 'dealer_hand') or not self.dealer_hand: # Ensure dealer_hand exists
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

        # Enhanced shuffling algorithm (e.g., Fisher-Yates style, random.shuffle is good)
        for _ in range(3):  # Triple shuffle for better randomization
            random.shuffle(deck)

        logger.info(f"Created {num_decks}-deck shoe with {len(deck)} cards for room {self.code}")
        return deck

    def shuffle_deck(self):
        """Reshuffle the deck"""
        self.deck = self.create_deck()
        logger.info(f"Reshuffled deck for room {self.code}")

    def deal_card(self) -> Optional[Card]:
        """Deal a card from the deck with cut card simulation"""
        # Reshuffle when deck is low (e.g., simulate cut card at ~75% penetration for 6 decks)
        # 6 decks = 312 cards. 25% remaining is 78 cards.
        if len(self.deck) < 78:
            logger.info(f"Cut card reached in room {self.code} (deck size: {len(self.deck)}), reshuffling.")
            self.shuffle_deck()

        if self.deck:
            card = self.deck.pop()
            logger.debug(f"Dealt card {card} in room {self.code}. Deck size: {len(self.deck)}")
            return card
        else:
            # This should ideally not happen if reshuffle logic is correct
            logger.error(f"No cards available in room {self.code}, attempting emergency reshuffle.")
            self.shuffle_deck()
            if self.deck: # Try again after emergency reshuffle
                 card = self.deck.pop()
                 logger.debug(f"Dealt card {card} after emergency reshuffle in room {self.code}.")
                 return card
            logger.critical(f"Deck empty even after emergency reshuffle in room {self.code}!")
            return None


    def get_active_players(self) -> List[Player]:
        """Get list of active players with money to play and not disconnected/banned"""
        active = [p for p in self.players.values()
                 if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED, PlayerStatus.DISCONNECTED]
                 and p.money >= self.min_bet # Must have enough for min bet
                 and not p.is_ai # Exclude AI if any
                 and not p.is_banned]

        logger.debug(f"Room {self.code} has {len(active)} active players for current/next hand.")
        return active

    def advance_to_next_player(self):
        """Move to the next player's turn or next hand within a split"""
        current_player = self.players.get(self.current_player_id)

        # Check if current player has more hands (from a split) to play
        if (current_player and
            current_player.current_hand_index < len(current_player.hands) - 1 and
            current_player.status == PlayerStatus.ACTIVE): # Only if still active on current hand
            
            current_player.current_hand_index += 1
            logger.info(f"Player {current_player.name} ({self.current_player_id}) moving to hand {current_player.current_hand_index + 1}/{len(current_player.hands)} in room {self.code}")
            # Player continues their turn with the new hand.
            # Check if this new hand is already a blackjack (e.g. split Aces)
            new_current_hand = current_player.get_current_hand()
            if new_current_hand.is_blackjack(): # Or if value is 21
                 logger.info(f"Player {current_player.name}'s new hand {current_player.current_hand_index + 1} is 21/Blackjack. Advancing again.")
                 self.advance_to_next_player() # Recurse to advance past this auto-completed hand
            return

        # Reset current player's hand index if they finished all their hands
        if current_player:
            current_player.current_hand_index = 0 # Reset for next game round

        # Find next active player in turn order
        self._current_player_turn_index += 1
        while self._current_player_turn_index < len(self._player_turn_order):
            next_player_id = self._player_turn_order[self._current_player_turn_index]
            next_player = self.players.get(next_player_id)

            if (next_player and
                next_player.status == PlayerStatus.ACTIVE and # Still in an active state for taking turns
                next_player.can_act()): # Check if their first hand can act
                self.current_player_id = next_player_id
                logger.info(f"Advanced to next player {next_player.name} ({next_player_id}) in room {self.code}")
                return

            self._current_player_turn_index += 1 # Move to next in order

        # All players have acted, move to dealer turn
        self.current_player_id = None
        self.phase = GamePhase.DEALER_TURN
        logger.info(f"All players completed turns, moving to dealer turn in room {self.code}")


    def update_activity(self):
        """Update last activity timestamp for the room"""
        self.last_activity = datetime.now()

    def is_inactive(self) -> bool:
        """Check if room has been inactive too long"""
        return (datetime.now() - self.last_activity).total_seconds() > GameConfig.INACTIVE_ROOM_TIMEOUT

    def get_player_count(self) -> int:
        """Get count of human players not disconnected or eliminated"""
        return len([p for p in self.players.values()
                    if not p.is_ai and not p.is_banned and
                    p.status not in [PlayerStatus.DISCONNECTED, PlayerStatus.ELIMINATED]])

    def add_chat_message(self, player_id: str, message: str) -> bool:
        """Add chat message with enhanced moderation"""
        player = self.players.get(player_id)
        if not player:
            logger.warning(f"Chat message from unknown player {player_id} in room {self.code}")
            return False

        # Sanitize message (basic example, consider more robust HTML/script sanitization)
        message = message.strip()
        if not message: return False # Empty message

        # Content moderation (simple keyword check)
        message_lower = message.lower()
        for banned_word in SecurityConfig.BANNED_WORDS:
            if banned_word in message_lower:
                player.add_warning(f"Used inappropriate language in chat: '{banned_word}'")
                # Optionally, don't add the message or replace banned words
                # For now, we'll let it through but warn the player
                # return False # If you want to block the message

        chat_msg = {
            "player_id": player_id,
            "player_name": player.name,
            "player_color": player.color, # For frontend styling
            "message": message, # Store the original (or sanitized) message
            "timestamp": time.time(), # Epoch timestamp
            "formatted_time": datetime.now().strftime("%H:%M:%S"), # User-friendly time
            "is_vip": player.is_vip # Example of conditional styling
        }

        self.chat_messages.append(chat_msg)

        # Keep only recent messages (e.g., last MAX_CHAT_MESSAGES)
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
            "players": self.get_player_count(),
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
                "spectators": len(self.spectators),
                "last_activity": self.last_activity.isoformat(),
                "deck_size": len(self.deck),
                "total_messages": len(self.chat_messages)
            })

        return base_data

# Enhanced Game Logic Class
class RoyalBlackjackGame:
    """Main game engine for Royal Blackjack 3D with enterprise features"""

    def __init__(self):
        self.rooms: Dict[str, Room] = {}
        self.connections: Dict[str, WebSocket] = {} # player_id -> WebSocket
        self.player_rooms: Dict[str, str] = {} # player_id -> room_code
        self.rate_limits: Dict[str, List[float]] = defaultdict(list) # For chat messages
        self.action_rate_limits: Dict[str, List[float]] = defaultdict(list) # For game actions
        self.ip_rate_limits: Dict[str, List[float]] = defaultdict(list) # For connections/requests per IP
        self.banned_ips: Set[str] = set()
        self.running = True # Controls the game loop
        self.maintenance_mode = False

        # Enhanced server statistics
        self.stats = {
            'total_rooms_created': 0,
            'total_players_connected': 0, # Unique players that connected
            'total_hands_played_server_wide': 0,
            'total_money_wagered_server_wide': 0,
            'total_money_won_by_players_server_wide': 0, # Payouts to players
            'server_start_time': datetime.now(),
            'peak_concurrent_players': 0,
            'peak_concurrent_rooms': 0,
            'total_chat_messages': 0,
            'total_bans_issued': 0,
            'total_warnings_issued': 0,
            'uptime': 0 # In seconds, updated by game loop
        }

        # Security tracking
        self.security_events: List[Dict] = [] # Store recent security events
        self.suspicious_ips: Dict[str, int] = defaultdict(int) # IP -> count of suspicious activities

        logger.info("🎰 Royal Blackjack 3D Game Engine initialized with enterprise features")

    def generate_room_code(self) -> str:
        """Generate a unique 6-character room code"""
        attempts = 0
        while attempts < 1000:  # Increased attempts for production robustness
            code = ''.join(random.choices('ABCDEFGHJKLMNPQRSTUVWXYZ23456789', k=6))
            if code not in self.rooms:
                return code
            attempts += 1

        # Fallback if 1000 attempts fail (highly unlikely with 30^6 combinations)
        timestamp_suffix = str(int(time.time()))[-4:]
        random_prefix = ''.join(random.choices('ABCDEFGHJKLMNPQRSTUVWXYZ', k=2))
        fallback_code = f"{random_prefix}{timestamp_suffix}"
        if fallback_code not in self.rooms:
            return fallback_code
        
        # Extremely unlikely scenario: use UUID's prefix if still clashing
        return str(uuid.uuid4())[:6].upper()


    def log_security_event(self, event_type: str, details: Dict[str, Any]):
        """Log security events for monitoring and potential automated actions"""
        event = {
            'timestamp': datetime.now().isoformat(),
            'type': event_type,
            'details': details
        }
        self.security_events.append(event)

        # Keep only recent security events (e.g., last 1000)
        if len(self.security_events) > 1000:
            self.security_events = self.security_events[-1000:]

        logger.warning(f"Security Event Logged: {event_type} - Details: {details}")

    def check_ip_rate_limit(self, ip_address: str) -> bool:
        """Check IP-based rate limiting for connections or sensitive actions"""
        if ip_address in self.banned_ips:
            logger.warning(f"Request from banned IP {ip_address} blocked.")
            return False

        current_time = time.time()
        # Clean old timestamps (older than 1 minute)
        self.ip_rate_limits[ip_address] = [
            t for t in self.ip_rate_limits[ip_address]
            if current_time - t <= 60.0  # 1 minute window
        ]

        if len(self.ip_rate_limits[ip_address]) >= SecurityConfig.IP_RATE_LIMIT:
            self.suspicious_ips[ip_address] += 1
            logger.warning(f"IP Rate limit exceeded for {ip_address}. Suspicion count: {self.suspicious_ips[ip_address]}")

            if self.suspicious_ips[ip_address] >= SecurityConfig.SUSPICIOUS_ACTIVITY_THRESHOLD:
                self.banned_ips.add(ip_address)
                self.log_security_event('ip_banned', {'ip': ip_address, 'reason': 'Excessive rate limit violations'})
                logger.error(f"IP {ip_address} auto-banned due to suspicious activity.")
                return False # Now banned

            return False # Rate limited for now

        self.ip_rate_limits[ip_address].append(current_time)
        return True

    def create_room(self, creator_player_id: str, room_name: Optional[str] = None, password: Optional[str] = None) -> Optional[str]:
        """Create a new game room with enhanced features"""
        if len(self.rooms) >= GameConfig.MAX_ROOMS:
            logger.warning(f"Maximum number of rooms ({GameConfig.MAX_ROOMS}) reached. Cannot create new room for {creator_player_id}.")
            return None

        room_code = self.generate_room_code()
        # Sanitize room_name
        room_name = (room_name or f"Royal Table {room_code}").strip()[:SecurityConfig.MAX_ROOM_NAME_LENGTH]


        # Create the room with enhanced settings
        room = Room(
            code=room_code,
            name=room_name,
            players={},
            spectators=set(),
            deck=[], # Will be initialized in __post_init__
            dealer_hand=Hand(),
            owner_id=creator_player_id,
            password=hashlib.sha256(password.encode()).hexdigest() if password else None, # Store hashed password
            is_public=password is None # Public if no password
        )

        self.rooms[room_code] = room
        self.stats['total_rooms_created'] += 1

        # Update peak rooms
        if len(self.rooms) > self.stats['peak_concurrent_rooms']:
            self.stats['peak_concurrent_rooms'] = len(self.rooms)

        logger.info(f"Room '{room_name}' ({room_code}) created by player {creator_player_id}. Public: {room.is_public}.")
        return room_code

    def join_room(self, room_code: str, player_id: str, player_name: str,
                  password: Optional[str] = None, ip_address: Optional[str] = None) -> bool:
        """Join a player to a room with enhanced validation"""
        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"Attempt to join non-existent room {room_code} by player {player_id}")
            return False

        # Check room capacity (for non-AI, non-banned players)
        if room.get_player_count() >= room.max_players and player_id not in room.players:
            logger.warning(f"Room {room_code} is full ({room.max_players} players). Cannot join {player_id}.")
            return False

        # Check password if required
        if room.password:
            if not password or hashlib.sha256(password.encode()).hexdigest() != room.password:
                logger.warning(f"Invalid password for room {room_code} by player {player_id}")
                self.log_security_event('failed_join_password', {'player_id': player_id, 'room_code': room_code, 'ip': ip_address})
                return False

        # Validate and clean player name
        player_name = player_name.strip()
        if not player_name or len(player_name) > SecurityConfig.MAX_NAME_LENGTH:
            logger.warning(f"Invalid player name '{player_name}' for player {player_id}. Length: {len(player_name)}.")
            return False

        # Check for banned words in name
        name_lower = player_name.lower()
        for banned_word in SecurityConfig.BANNED_WORDS:
            if banned_word in name_lower:
                logger.warning(f"Player name '{player_name}' for player {player_id} contains banned word: '{banned_word}'.")
                # Potentially log a security event or warn the player
                return False # Reject join

        # Handle rejoining player or new player
        if player_id in room.players:
            rejoining_player = room.players[player_id]
            if rejoining_player.is_banned:
                logger.warning(f"Banned player {player_id} ({rejoining_player.name}) attempted to rejoin room {room_code}")
                return False

            rejoining_player.connection_id = player_id # Update connection_id if it's the same as player_id
            rejoining_player.name = player_name # Allow name update on rejoin
            rejoining_player.status = PlayerStatus.ACTIVE # Mark as active again
            rejoining_player.last_activity = datetime.now()
            rejoining_player.ip_address = ip_address # Update IP
            logger.info(f"Player {player_name} ({player_id}) re-joined room {room_code}")
        else:
            # New player joining
            # Generate unique color for player (simple assignment for now)
            colors = [
                '#FF6B6B', '#4ECDC4', '#45B7D1', '#96CEB4',
                '#FFEAA7', '#DDA0DD', '#98D8C8', '#F7DC6F',
                '#FF7675', '#74B9FF', '#00B894', '#FDCB6E',
                '#A29BFE', '#FD79A8', '#E17055', '#00CEC9'
            ]
            color_index = len(room.players) % len(colors)
            color = colors[color_index]

            player = Player(
                id=player_id,
                name=player_name,
                money=GameConfig.STARTING_MONEY, # Or carry over if implementing persistence
                avatar=f"royal_avatar_{random.randint(1, 12)}", # Example avatar
                color=color,
                connection_id=player_id,
                ip_address=ip_address
            )

            room.players[player_id] = player
            self.stats['total_players_connected'] += 1 # Increment for unique player connections

            # Update peak concurrent players (server-wide)
            current_total_players = sum(r.get_player_count() for r in self.rooms.values())
            if current_total_players > self.stats['peak_concurrent_players']:
                self.stats['peak_concurrent_players'] = current_total_players

            logger.info(f"Player {player_name} ({player_id}) joined room {room_code} with IP {ip_address}")

        self.player_rooms[player_id] = room_code # Map player to this room
        room.update_activity()
        return True

    def leave_room(self, player_id: str, force_remove: bool = False):
        """Remove a player from their room or mark as disconnected."""
        room_code = self.player_rooms.get(player_id) # Use get to avoid KeyError if player not in a room
        if not room_code:
            logger.debug(f"Player {player_id} not mapped to any room, cannot leave.")
            return

        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"Room {room_code} not found for player {player_id} to leave.")
            if player_id in self.player_rooms: del self.player_rooms[player_id] # Clean up mapping
            return

        player_obj = room.players.get(player_id)

        if player_obj:
            logger.info(f"Player {player_obj.name} ({player_id}) leaving/disconnecting from room {room_code}. Force remove: {force_remove}")
            if force_remove or player_obj.is_banned: # Fully remove if forced or banned
                del room.players[player_id]
                if player_id in self.player_rooms: del self.player_rooms[player_id]
                logger.info(f"Player {player_id} forcibly removed from room {room_code}.")
            else:
                # Mark as disconnected for potential reconnection
                player_obj.status = PlayerStatus.DISCONNECTED
                player_obj.last_activity = datetime.now()
                player_obj.generate_reconnect_token() # For secure reconnection attempts
                logger.info(f"Player {player_obj.name} ({player_id}) marked as disconnected in room {room_code}.")
        
        # Remove from spectators if they were one
        if player_id in room.spectators:
            room.spectators.discard(player_id)
            if player_id in self.player_rooms and not player_obj : del self.player_rooms[player_id] # If only spectator
            logger.info(f"Spectator {player_id} removed from room {room_code}.")


        # Handle game state if the disconnected player was the current player
        if room.current_player_id == player_id and room.phase == GamePhase.PLAYER_TURNS:
            logger.info(f"Current player {player_id} left/disconnected; advancing turn in room {room_code}.")
            room.advance_to_next_player()
            # This might trigger dealer's turn if they were the last player

        # Room ownership and cleanup logic
        remaining_players = [p for p in room.players.values()
                             if not p.is_ai and p.status != PlayerStatus.DISCONNECTED and not p.is_banned]

        if not remaining_players and not room.spectators:
            # Room is effectively empty of active humans
            logger.info(f"Room {room_code} is now empty of active human players and spectators. Will be cleaned up if inactive.")
            # The cleanup_inactive_rooms job will handle deletion based on inactivity.
        elif room.owner_id == player_id and remaining_players:
            # Transfer ownership if owner left
            new_owner = next((p.id for p in remaining_players), None) # Find first remaining active player
            if new_owner:
                room.owner_id = new_owner
                logger.info(f"Room {room_code} ownership transferred from {player_id} to {new_owner}.")
            else: # Should not happen if remaining_players is true, but as a safe guard
                room.owner_id = None 
                logger.warning(f"Room {room_code} owner {player_id} left, no suitable new owner found. Owner set to None.")


        room.update_activity()


    def start_game(self, room_code: str, initiator_id: str) -> bool:
        """Start a new game in the room with validation"""
        room = self.rooms.get(room_code)
        if not room:
            logger.error(f"Cannot start game: room {room_code} not found by initiator {initiator_id}")
            return False

        # Verify initiator is room owner
        if room.owner_id != initiator_id:
            logger.warning(f"Non-owner {initiator_id} attempted to start game in room {room_code}. Owner is {room.owner_id}.")
            return False

        if room.phase not in [GamePhase.WAITING, GamePhase.GAME_OVER]:
            logger.warning(f"Game already in progress or not in a startable phase in room {room_code}. Current phase: {room.phase.value}")
            return False
        
        # Filter for players who are active and eligible to play
        eligible_players_for_new_hand = [p for p in room.players.values() 
                                         if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED, PlayerStatus.DISCONNECTED]
                                         and p.money >= room.min_bet 
                                         and not p.is_ai and not p.is_banned]


        # Check if any eligible players have placed bets
        players_with_bets = [p for p in eligible_players_for_new_hand if p.hands[0].bet_amount > 0]
        if not players_with_bets: # No one has bet
            logger.warning(f"Cannot start game in room {room_code}: No bets placed by eligible players.")
            return False
        
        if len(players_with_bets) == 0: #This check is redundant due to above
            logger.warning(f"Cannot start game in room {room_code}: No players with bets.")
            return False

        logger.info(f"Starting premium blackjack game in room {room_code} with {len(players_with_bets)} betting players, initiated by {initiator_id}.")

        # Initialize game state for new hand
        room.phase = GamePhase.DEALING
        room.hand_number += 1
        room.shuffle_deck()
        room.dealer_hand = Hand() # Fresh dealer hand
        self.stats['total_hands_played_server_wide'] += 1

        # Reset players for new hand and update statistics
        # Only players_with_bets will participate in this hand.
        room._player_turn_order = []
        for player in players_with_bets:
            player.stats.total_hands_played += 1
            # The bet was already placed and money deducted, so just ensure hand is reset
            current_bet = player.hands[0].bet_amount
            player.reset_for_new_hand() # This creates a new Hand object
            player.hands[0].bet_amount = current_bet # Re-apply the bet to the new hand
            
            # No need to update total_wagered here, it was done at bet placement.
            room._player_turn_order.append(player.id)


        # Shuffle turn order for fairness
        random.shuffle(room._player_turn_order)
        room._current_player_turn_index = -1 # Will be advanced to 0 by advance_to_next_player or set in deal
        room.current_player_id = room._player_turn_order[0] if room._player_turn_order else None

        room.update_activity()
        return True

    def deal_initial_cards(self, room_code: str):
        """Deal initial two cards to each participating player and dealer"""
        room = self.rooms.get(room_code)
        if not room or room.phase != GamePhase.DEALING:
            logger.warning(f"Cannot deal initial cards in room {room_code}. Phase: {room.phase.value if room else 'N/A'}")
            return

        participating_players = [room.players[pid] for pid in room._player_turn_order if pid in room.players]

        # Deal 2 cards to each player and dealer (standard blackjack dealing sequence)
        for card_round in range(2):
            # Deal to players first in this round
            for player in participating_players:
                if player.hands and len(player.hands[0].cards) < 2: # Ensure they get up to 2 cards
                    card = room.deal_card()
                    if card:
                        card.dealt_at = datetime.now() # Track when card was dealt
                        player.hands[0].cards.append(card)
                    else: # Should not happen with proper deck management
                        logger.error(f"Deck ran out while dealing to player {player.name} in room {room_code}")
                        # Handle error - perhaps invalidate hand or room
                        return


            # Deal to dealer in this round
            if len(room.dealer_hand.cards) < 2:
                card = room.deal_card()
                if card:
                    card.dealt_at = datetime.now()
                    room.dealer_hand.cards.append(card)
                else:
                    logger.error(f"Deck ran out while dealing to dealer in room {room_code}")
                    return

        # Check for player blackjacks and update status
        blackjack_player_names = []
        for player in participating_players:
            if player.hands[0].is_blackjack():
                player.status = PlayerStatus.BLACKJACK
                player.stats.total_blackjacks += 1
                blackjack_player_names.append(player.name)
                logger.info(f"Player {player.name} has Blackjack! in room {room_code}")

        # Transition to player turns or dealer turn if all have blackjack
        if all(p.status == PlayerStatus.BLACKJACK for p in participating_players):
            logger.info(f"All participating players have Blackjack in room {room_code}. Proceeding to dealer's turn.")
            room.phase = GamePhase.DEALER_TURN
            # Dealer turn will be processed by game loop or direct call
            self._play_dealer_hand(room) # Process immediately if all BJs
        else:
            room.phase = GamePhase.PLAYER_TURNS
            room._current_player_turn_index = -1 # Reset index for advance_to_next_player
            room.advance_to_next_player() # Find the first player who needs to act

        room.update_activity()
        if blackjack_player_names:
            logger.info(f"Initial cards dealt in room {room_code}. Player Blackjacks: {', '.join(blackjack_player_names) if blackjack_player_names else 'None'}.")
        else:
            logger.info(f"Initial cards dealt in room {room_code}. No player blackjacks.")

    def player_action(self, room_code: str, player_id: str, action: PlayerAction, amount: int = 0) -> bool:
        """Process a player action with comprehensive validation"""
        room = self.rooms.get(room_code)
        if not room:
            logger.error(f"Room {room_code} not found for player action from {player_id}")
            return False

        player = room.players.get(player_id)
        if not player:
            logger.error(f"Player {player_id} not found in room {room_code} for action {action.value}")
            return False

        if player.is_banned:
            logger.warning(f"Banned player {player_id} attempted action {action.value} in room {room_code}")
            return False

        logger.info(f"Processing action for player {player.name} ({player_id}): {action.value}, Amount: {amount}, in room {room_code} (Phase: {room.phase.value})")

        try:
            success = False
            if action == PlayerAction.PLACE_BET:
                success = self._process_place_bet(room, player, amount)
            elif room.phase == GamePhase.PLAYER_TURNS and room.current_player_id == player_id:
                if action == PlayerAction.HIT:
                    success = self._process_hit(room, player)
                elif action == PlayerAction.STAND:
                    success = self._process_stand(room, player)
                elif action == PlayerAction.DOUBLE_DOWN:
                    success = self._process_double_down(room, player)
                elif action == PlayerAction.SPLIT:
                    success = self._process_split(room, player)
                elif action == PlayerAction.SURRENDER:
                    success = self._process_surrender(room, player)
                else:
                    logger.warning(f"Unknown or out-of-phase action {action.value} by {player.name}")
            else:
                logger.warning(f"Action {action.value} by {player.name} rejected. Phase: {room.phase.value}, Current Player: {room.current_player_id}, Action Player: {player_id}")


            if success:
                player.update_activity()
                room.update_activity()

                # Update action-specific statistics
                if action == PlayerAction.DOUBLE_DOWN: player.stats.total_doubles += 1
                elif action == PlayerAction.SPLIT: player.stats.total_splits += 1
                elif action == PlayerAction.SURRENDER: player.stats.total_surrenders += 1
                # Hit/Stand/Bet are implicitly tracked by hands_played/wagered

            return success

        except Exception as e:
            logger.error(f"Critical error processing player action {action.value} for {player_id} in room {room_code}: {e}")
            logger.error(traceback.format_exc())
            return False

    def _process_place_bet(self, room: Room, player: Player, amount: int) -> bool:
        """Process a bet placement with validation"""
        if room.phase not in [GamePhase.WAITING, GamePhase.GAME_OVER]: # Allow bets if game just ended too
            logger.warning(f"Cannot place bet: room {room.code} not in WAITING or GAME_OVER phase. Current: {room.phase.value}")
            return False
        
        if not (room.min_bet <= amount <= room.max_bet):
            logger.warning(f"Invalid bet amount ${amount} for player {player.name}. Allowed: ${room.min_bet}-${room.max_bet}.")
            return False
        
        if amount > player.money:
            logger.warning(f"Player {player.name} has insufficient funds (${player.money}) for bet ${amount}.")
            return False

        # Assuming player has one hand at betting stage
        player.hands[0].bet_amount = amount
        player.money -= amount # Deduct bet from player's money
        
        # Update statistics related to wagering
        player.stats.total_wagered += amount
        self.stats['total_money_wagered_server_wide'] += amount
        
        logger.info(f"Player {player.name} placed bet of ${amount}. Remaining money: ${player.money}.")
        return True

    def _process_hit(self, room: Room, player: Player) -> bool:
        """Process a hit action"""
        current_hand = player.get_current_hand()
        if not player.can_act() or current_hand.get_value() >= 21: # Redundant check, but safe
            logger.warning(f"Player {player.name} cannot Hit. Hand value: {current_hand.get_value()}, Status: {player.status.value}")
            return False

        card = room.deal_card()
        if not card:
            logger.error(f"Deck empty, cannot deal card for Hit to player {player.name}")
            return False # Should not happen

        card.dealt_at = datetime.now()
        current_hand.cards.append(card)
        logger.info(f"Player {player.name} Hits, receives {card}. New hand value: {current_hand.get_value()}")

        if current_hand.is_bust():
            # Player busts on this hand
            # If it's not a split hand, player status might change overall.
            # For now, just log the hand bust. Payout will handle result.
            logger.info(f"Player {player.name}'s hand busted with {current_hand.get_value()}")
            self._advance_player_turn(room) # Move to next hand or player
        elif current_hand.get_value() == 21:
            logger.info(f"Player {player.name}'s hand reached 21.")
            self._advance_player_turn(room) # Auto-stand on 21

        return True

    def _process_stand(self, room: Room, player: Player) -> bool:
        """Process a stand action"""
        if not player.can_act(): # Check if it's valid to stand
            logger.warning(f"Player {player.name} cannot Stand in current state.")
            return False

        # No change to player status here, just advance turn for this hand
        logger.info(f"Player {player.name} Stands with hand value {player.get_current_hand().get_value()}")
        self._advance_player_turn(room)
        return True

    def _process_double_down(self, room: Room, player: Player) -> bool:
        """Process a double down action"""
        current_hand = player.get_current_hand()
        if not current_hand.can_double_down():
            logger.warning(f"Player {player.name} cannot Double Down on current hand.")
            return False
        
        additional_bet = current_hand.bet_amount
        if player.money < additional_bet:
            logger.warning(f"Player {player.name} has insufficient funds (${player.money}) to Double Down (needs ${additional_bet}).")
            return False

        # Double the bet
        player.money -= additional_bet
        current_hand.bet_amount += additional_bet
        current_hand.is_doubled = True
        
        player.stats.total_wagered += additional_bet # Track additional wager
        self.stats['total_money_wagered_server_wide'] += additional_bet

        # Deal exactly one more card
        card = room.deal_card()
        if card:
            card.dealt_at = datetime.now()
            current_hand.cards.append(card)
            logger.info(f"Player {player.name} Doubled Down. Bet is now ${current_hand.bet_amount}. Received {card}. New hand value: {current_hand.get_value()}")
        else:
            logger.error(f"Deck empty, cannot deal card for Double Down to {player.name}")
            # This is a server error, bet should ideally be reverted or game paused.
            # For now, proceed, but this needs robust handling if it occurs.
            
        if current_hand.is_bust():
            logger.info(f"Player {player.name}'s hand busted after Double Down with {current_hand.get_value()}")
        
        self._advance_player_turn(room) # Turn ends after double down
        return True

    def _process_split(self, room: Room, player: Player) -> bool:
        """Process a split action"""
        current_hand_index = player.current_hand_index
        original_hand = player.hands[current_hand_index]

        if not original_hand.can_split():
            logger.warning(f"Player {player.name} cannot Split current hand.")
            return False
        
        # Check max splits (e.g., up to 4 hands total)
        if len(player.hands) >= 4:
            logger.warning(f"Player {player.name} reached maximum number of splits (4 hands).")
            return False
        
        bet_for_new_hand = original_hand.bet_amount
        if player.money < bet_for_new_hand:
            logger.warning(f"Player {player.name} has insufficient funds (${player.money}) to Split (needs ${bet_for_new_hand}).")
            return False

        # Perform the split
        player.money -= bet_for_new_hand # Cost for the new hand's bet
        
        second_card_of_original_hand = original_hand.cards.pop() # Take one card for the new hand
        original_hand.is_split = True # Mark original hand as having been part of a split

        new_hand = Hand(cards=[second_card_of_original_hand], bet_amount=bet_for_new_hand, is_split=True)
        
        # Insert the new hand immediately after the current one in player's list of hands
        player.hands.insert(current_hand_index + 1, new_hand)
        
        player.stats.total_wagered += bet_for_new_hand # Track additional wager
        self.stats['total_money_wagered_server_wide'] += bet_for_new_hand

        logger.info(f"Player {player.name} Split their hand. Now has {len(player.hands)} hands.")

        # Deal one new card to each of the split hands (original and new)
        for hand_to_deal_to in [original_hand, new_hand]:
            card = room.deal_card()
            if card:
                card.dealt_at = datetime.now()
                hand_to_deal_to.cards.append(card)
                logger.info(f"Dealt {card} to one of {player.name}'s split hands. Value: {hand_to_deal_to.get_value()}")
            else:
                logger.error(f"Deck empty, cannot deal to split hand for {player.name}")
                # Critical error, may need to invalidate this split action or pause game
        
        # Player continues turn on the first of the split hands (original_hand)
        # Check if this hand is now blackjack/21 (e.g. split Aces)
        if original_hand.is_blackjack() or original_hand.get_value() == 21:
             logger.info(f"Player {player.name}'s first split hand is 21/Blackjack. Advancing.")
             self._advance_player_turn(room) # This will move to the next hand (the newly split one)
                                            # or next player if that also resolves immediately.
        return True

    def _process_surrender(self, room: Room, player: Player) -> bool:
        """Process a surrender action"""
        current_hand = player.get_current_hand()
        if not current_hand.can_surrender():
            logger.warning(f"Player {player.name} cannot Surrender current hand.")
            return False

        current_hand.is_surrendered = True
        refund_amount = current_hand.bet_amount // 2 # Half of the bet is returned
        player.money += refund_amount
        
        # Surrender counts as a loss for win rate, but bet is partially recovered
        # The net loss is bet_amount / 2. total_winnings will reflect this in payout.
        
        logger.info(f"Player {player.name} Surrendered. Bet was ${current_hand.bet_amount}, refunded ${refund_amount}. Remaining money: ${player.money}")
        self._advance_player_turn(room) # Turn ends for this hand
        return True

    def _advance_player_turn(self, room: Room):
        """Advance to next player or next hand of current player (after split)"""
        # This calls the room's method, which handles the logic
        room.advance_to_next_player()

        if room.phase == GamePhase.DEALER_TURN:
            # If advancing turn caused all players to finish, play dealer's hand
            self._play_dealer_hand(room)

    def _play_dealer_hand(self, room: Room):
        """Play the dealer's hand according to standard casino rules"""
        if room.phase != GamePhase.DEALER_TURN:
            logger.error(f"Attempted to play dealer hand in room {room.code} during incorrect phase: {room.phase.value}")
            return

        logger.info(f"Dealer playing hand in room {room.code}. Initial dealer cards: {[str(c) for c in room.dealer_hand.cards]}")

        # Check if all remaining players busted. If so, dealer doesn't need to play.
        # "Remaining players" are those who didn't get Blackjack and didn't surrender.
        active_player_hands_in_play = []
        for p_obj in room.players.values():
            if p_obj.id in room._player_turn_order : # Only consider players who were part of this hand
                for hand_obj in p_obj.hands:
                    if hand_obj.bet_amount > 0 and not hand_obj.is_surrendered and p_obj.status != PlayerStatus.BLACKJACK:
                        active_player_hands_in_play.append(hand_obj)
        
        if not any(not hand.is_bust() for hand in active_player_hands_in_play) and active_player_hands_in_play:
            logger.info(f"All remaining active players busted in room {room.code}. Dealer does not draw.")
        else:
            # Dealer plays by standard rules: hit until 17 or more.
            # GameConfig.DEALER_HIT_THRESHOLD (e.g., 16 means hit on 16 or less, stand on 17+)
            # Soft 17 rule: Does dealer hit or stand on Soft 17 (Ace + 6)? Assume stand on all 17s for now.
            # If dealer must hit soft 17:
            # while room.dealer_hand.get_value() < 17 or \
            #       (room.dealer_hand.get_value() == 17 and any(c.rank == 'A' for c in room.dealer_hand.cards) and
            #        sum(c.get_blackjack_value() for c in room.dealer_hand.cards if c.rank != 'A') + \
            #        sum(1 for c in room.dealer_hand.cards if c.rank == 'A') < 17): # complex soft 17 check
            
            while room.dealer_hand.get_value() <= GameConfig.DEALER_HIT_THRESHOLD: # Hits on 16 or less
                card = room.deal_card()
                if card:
                    card.dealt_at = datetime.now()
                    room.dealer_hand.cards.append(card)
                    new_value = room.dealer_hand.get_value()
                    logger.info(f"Dealer Hits in room {room.code}, receives {card}. New dealer total: {new_value}")
                    if new_value > 21: # Dealer busts
                        break
                else:
                    logger.error(f"Deck empty, dealer cannot Hit in room {room.code}")
                    break # Critical error

        dealer_final_value = room.dealer_hand.get_value()
        if dealer_final_value > 21:
            logger.info(f"Dealer busts in room {room.code} with {dealer_final_value}.")
        else:
            logger.info(f"Dealer stands in room {room.code} with {dealer_final_value}.")

        room.phase = GamePhase.PAYOUT
        self._calculate_payouts(room)


    def _calculate_payouts(self, room: Room):
        """Calculate and distribute payouts with comprehensive statistics"""
        if room.phase != GamePhase.PAYOUT:
            logger.error(f"Attempted to calculate payouts in room {room.code} during incorrect phase: {room.phase.value}")
            return

        logger.info(f"Calculating payouts for room {room.code}. Hand #{room.hand_number}")
        dealer_value = room.dealer_hand.get_value()
        dealer_is_bust = room.dealer_hand.is_bust()
        dealer_has_blackjack = room.dealer_hand.is_blackjack() # Natural blackjack for dealer

        server_total_payout_this_hand = 0

        for player_id in room._player_turn_order: # Iterate in turn order for consistency
            player = room.players.get(player_id)
            if not player or not player.hands:
                continue # Player might have disconnected completely

            player_total_net_winnings_this_hand = 0
            player_won_at_least_one_hand = False

            for hand in player.hands:
                if hand.bet_amount == 0: # Skip hands with no bet (e.g. if player sat out after betting phase)
                    continue

                if hand.is_surrendered:
                    hand.result = HandResult.SURRENDER
                    hand.payout = hand.bet_amount // 2 # Player gets half bet back
                    player.money += hand.payout
                    player_total_net_winnings_this_hand += (hand.payout - hand.bet_amount)
                    # For stats, surrender is often counted as a loss, but bet is partially recovered.
                    # total_winnings stat should reflect the net change.
                    continue

                hand_value = hand.get_value()

                if hand.is_bust():
                    hand.result = HandResult.BUST
                    hand.payout = 0 # Player loses bet
                    player_total_net_winnings_this_hand -= hand.bet_amount
                elif hand.is_blackjack(): # Player has natural blackjack
                    if dealer_has_blackjack:
                        hand.result = HandResult.PUSH # Blackjack vs Blackjack is usually a push
                        hand.payout = hand.bet_amount # Bet returned
                        player.money += hand.payout
                        # Net is 0 for this hand
                    else:
                        hand.result = HandResult.BLACKJACK # Player Blackjack wins 3:2
                        hand.payout = int(hand.bet_amount * (1 + GameConfig.BLACKJACK_PAYOUT))
                        player.money += hand.payout
                        player_total_net_winnings_this_hand += (hand.payout - hand.bet_amount)
                        player_won_at_least_one_hand = True
                elif dealer_is_bust:
                    hand.result = HandResult.WIN # Player wins if dealer busts (and player didn't)
                    hand.payout = hand.bet_amount * 2 # Pays 1:1
                    player.money += hand.payout
                    player_total_net_winnings_this_hand += (hand.payout - hand.bet_amount)
                    player_won_at_least_one_hand = True
                elif hand_value > dealer_value:
                    hand.result = HandResult.WIN # Player's hand beats dealer's
                    hand.payout = hand.bet_amount * 2
                    player.money += hand.payout
                    player_total_net_winnings_this_hand += (hand.payout - hand.bet_amount)
                    player_won_at_least_one_hand = True
                elif hand_value == dealer_value:
                    if dealer_has_blackjack: # Dealer BJ beats player's non-BJ 21
                        hand.result = HandResult.LOSE
                        hand.payout = 0
                        player_total_net_winnings_this_hand -= hand.bet_amount
                    else: # Non-BJ Push
                        hand.result = HandResult.PUSH
                        hand.payout = hand.bet_amount # Bet returned
                        player.money += hand.payout
                        # Net is 0
                else: # hand_value < dealer_value (and dealer didn't bust)
                    hand.result = HandResult.LOSE
                    hand.payout = 0
                    player_total_net_winnings_this_hand -= hand.bet_amount
                
                logger.info(f"  Player {player.name}, Hand ({[str(c) for c in hand.cards]} Val:{hand_value}): Result={hand.result.value if hand.result else 'N/A'}, Bet=${hand.bet_amount}, Payout=${hand.payout}")


            # Update player's overall statistics
            player.stats.total_winnings += player_total_net_winnings_this_hand
            server_total_payout_this_hand += (player_total_net_winnings_this_hand + sum(h.bet_amount for h in player.hands if h.bet_amount >0)) # Add back bets to get gross player win


            if player_won_at_least_one_hand:
                player.stats.total_hands_won += 1 # Count if any hand won (excluding pushes for win rate)
                player.stats.current_streak += 1
                if player.stats.current_streak > player.stats.best_streak:
                    player.stats.best_streak = player.stats.current_streak
            elif player_total_net_winnings_this_hand < 0 : # If player lost money overall this round
                player.stats.current_streak = 0
            # If only pushes, streak remains unchanged.

            logger.info(f"Player {player.name} total net for hand #{room.hand_number}: ${player_total_net_winnings_this_hand}. New balance: ${player.money}")

        # Update server-wide statistics
        # total_money_won_by_players_server_wide should be the gross amount paid out to players
        self.stats['total_money_won_by_players_server_wide'] += server_total_payout_this_hand

        room.phase = GamePhase.GAME_OVER
        room.update_activity()
        logger.info(f"Payouts complete for room {room.code}. Server paid out ${server_total_payout_this_hand} this hand.")

        # Schedule automatic reset for the next hand
        asyncio.create_task(self._prepare_next_hand(room.code))

    async def _prepare_next_hand(self, room_code: str, delay: int = GameConfig.AUTO_RESET_DELAY):
        """Prepare room for next hand after a delay."""
        logger.info(f"Scheduling next hand preparation for room {room_code} in {delay} seconds.")
        await asyncio.sleep(delay)

        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"Room {room_code} not found during next hand preparation. Might have been closed.")
            return

        # Check if room should proceed (e.g., still has active players wanting to play)
        active_players_for_next_hand = [p for p in room.players.values()
                                         if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED, PlayerStatus.DISCONNECTED]
                                         and p.money >= room.min_bet
                                         and not p.is_banned]

        if not active_players_for_next_hand:
            logger.info(f"No active players eligible for next hand in room {room_code}. Room remains in GAME_OVER/WAITING.")
            room.phase = GamePhase.WAITING # Or keep GAME_OVER until owner starts
            # Broadcast state so UI reflects this
            await broadcast_game_states() # Consider a targeted broadcast
            return

        # Reset room state for the next hand
        room.phase = GamePhase.WAITING
        for player in room.players.values():
            # Only reset players who are part of the room and not permanently out
            if player.status not in [PlayerStatus.ELIMINATED, PlayerStatus.SITTING_OUT]:
                 player.reset_for_new_hand() # This also checks if they have enough money for min_bet

        room.dealer_hand = Hand() # Clear dealer's hand
        room.current_player_id = None
        room._player_turn_order = []
        room._current_player_turn_index = -1 # Will be set correctly when game starts

        logger.info(f"Room {room_code} reset and now in WAITING phase for next hand.")
        # Game state will be broadcast by the main loop.

    def get_game_state(self, room_code: str, for_player_id: str) -> Dict[str, Any]:
        """Get current game state for a specific player with comprehensive data"""
        room = self.rooms.get(room_code)
        if not room:
            return {"error": "Room not found"}

        player_in_room_object = room.players.get(for_player_id)
        is_player_in_game_list = player_in_room_object is not None and not player_in_room_object.is_ai
        is_spectator = for_player_id in room.spectators

        # Build players data, obscuring sensitive info for other players
        players_data = {}
        for p_id, p_obj in room.players.items():
            if p_obj.status != PlayerStatus.DISCONNECTED or p_id == for_player_id: # Show self even if disconnected (for reconnect)
                # For other players, you might want to limit data, e.g. not show exact money unless configured
                players_data[p_id] = p_obj.to_dict(current_player_id=room.current_player_id)

        # Dealer hand visibility logic (hole card)
        dealer_cards_for_client = []
        dealer_visible_value = None
        if room.dealer_hand.cards:
            if room.phase in [GamePhase.DEALING, GamePhase.PLAYER_TURNS] and len(room.dealer_hand.cards) == 2:
                # Show first card, hide second (hole card)
                dealer_cards_for_client.append(room.dealer_hand.cards[0].to_dict())
                dealer_cards_for_client.append({"suit": "back", "rank": "back", "id": "hidden_dealer_card"})
                dealer_visible_value = room.dealer_hand.cards[0].get_blackjack_value()
            else: # Show all dealer cards (e.g., dealer turn, payout, game over)
                dealer_cards_for_client = [card.to_dict() for card in room.dealer_hand.cards]
                dealer_visible_value = room.dealer_hand.get_value()
        
        dealer_hand_data = {
            "cards": dealer_cards_for_client,
            "value": dealer_visible_value,
            "is_blackjack": room.dealer_hand.is_blackjack() if room.phase not in [GamePhase.DEALING, GamePhase.PLAYER_TURNS] else None
        }


        game_state = {
            "room_code": room.code,
            "room_name": room.name,
            "phase": room.phase.value,
            "current_player_id": room.current_player_id,
            "players": players_data,
            "dealer_hand": dealer_hand_data,
            "chat_messages": room.chat_messages[-30:],  # Send last 30 chat messages
            "is_player_in_game": is_player_in_game_list, # If they are in the room.players list
            "is_spectator": is_spectator,
            "spectator_count": len(room.spectators),
            "hand_number": room.hand_number,
            "min_bet": room.min_bet,
            "max_bet": room.max_bet,
            "can_act": (is_player_in_game_list and
                       room.current_player_id == for_player_id and
                       room.phase == GamePhase.PLAYER_TURNS and
                       player_in_room_object.can_act()), # Check if it's their turn and they can act
            "available_actions": self.get_available_actions(room, for_player_id) if is_player_in_game_list else [],
            "owner_id": room.owner_id,
            "is_premium": room.is_premium,
            "tournament_mode": room.tournament_mode,
            # "deck_remaining_percentage": round((len(room.deck) / (6*52)) * 100, 1) if is_player_in_game_list else None # Example stat
        }
        return game_state

    def get_available_actions(self, room: Room, player_id: str) -> List[Dict[str, Any]]:
        """Get available actions for a player with detailed information for UI"""
        player = room.players.get(player_id)
        # Ensure it's this player's turn and they are in a state to act.
        if not player or room.current_player_id != player_id or room.phase != GamePhase.PLAYER_TURNS or not player.can_act():
            return []

        actions = []
        current_hand = player.get_current_hand()

        # Basic actions (Hit, Stand) are usually always available if can_act is true
        actions.append({
            "action": PlayerAction.HIT.value,
            "label": "Hit",
            "description": "Take another card."
        })
        actions.append({
            "action": PlayerAction.STAND.value,
            "label": "Stand",
            "description": "Keep current hand and end your turn for this hand."
        })

        # Double Down
        if current_hand.can_double_down() and player.money >= current_hand.bet_amount:
            actions.append({
                "action": PlayerAction.DOUBLE_DOWN.value,
                "label": "Double",
                "description": f"Double your bet to ${current_hand.bet_amount * 2} and receive one more card.",
                "cost": current_hand.bet_amount # The additional amount needed
            })

        # Split
        if current_hand.can_split() and player.money >= current_hand.bet_amount and len(player.hands) < 4 : # Max 3 splits (4 hands)
            actions.append({
                "action": PlayerAction.SPLIT.value,
                "label": "Split",
                "description": f"Split your pair into two separate hands. Requires an additional bet of ${current_hand.bet_amount}.",
                "cost": current_hand.bet_amount
            })

        # Surrender (if applicable by rules, e.g., only on first two cards)
        if current_hand.can_surrender(): # This implies it's the first two cards
            actions.append({
                "action": PlayerAction.SURRENDER.value,
                "label": "Surrender",
                "description": f"Forfeit half your bet (${current_hand.bet_amount // 2}) and end your hand."
            })
        
        # Note: Insurance is not implemented here, but would be another conditional action.

        return actions

    def check_rate_limit(self, client_id: str, limit_type: str = "message") -> bool:
        """Enhanced rate limiting with different types (message, action)"""
        limit_dict = self.rate_limits
        max_per_second = GameConfig.RATE_LIMIT_MESSAGES_PER_SECOND
        
        if limit_type == "action":
            limit_dict = self.action_rate_limits
            max_per_second = GameConfig.RATE_LIMIT_ACTIONS_PER_SECOND
        
        current_time = time.time()
        # Clean old timestamps (older than 1 second)
        limit_dict[client_id] = [t for t in limit_dict[client_id] if current_time - t <= 1.0]

        if len(limit_dict[client_id]) < max_per_second:
            limit_dict[client_id].append(current_time)
            return True
        else:
            logger.warning(f"Rate limit exceeded for {client_id} (type: {limit_type}). Count: {len(limit_dict[client_id])}")
            # Potentially log security event if persistent
            return False

    def cleanup_inactive_rooms(self):
        """Enhanced cleanup: removes inactive rooms and fully disconnected players after timeout."""
        current_time = datetime.now()
        rooms_to_delete = []

        for room_code, room in list(self.rooms.items()): # Iterate over a copy for safe deletion
            players_to_fully_remove = []
            for player_id, player in list(room.players.items()): # Iterate player copy
                if player.status == PlayerStatus.DISCONNECTED:
                    # Check if disconnected player's session timeout has been reached
                    if (current_time - player.last_activity).total_seconds() > GameConfig.SESSION_TIMEOUT:
                        players_to_fully_remove.append(player_id)
            
            for player_id in players_to_fully_remove:
                logger.info(f"Session timeout for disconnected player {player_id} in room {room_code}. Fully removing.")
                del room.players[player_id] # Remove from room's player list
                if player_id in self.player_rooms:
                    del self.player_rooms[player_id] # Remove from global player-room mapping
            
            # Check if room itself should be deleted (no active human players AND inactive for timeout)
            active_human_players_in_room = [p for p in room.players.values() 
                                            if not p.is_ai and p.status != PlayerStatus.DISCONNECTED and not p.is_banned]
            
            if not active_human_players_in_room and not room.spectators and room.is_inactive():
                rooms_to_delete.append(room_code)
        
        for room_code in rooms_to_delete:
            if room_code in self.rooms:
                del self.rooms[room_code]
                logger.info(f"Deleted inactive room {room_code} due to inactivity and no players/spectators.")


    def get_server_stats(self) -> Dict[str, Any]:
        """Get comprehensive server statistics for monitoring"""
        current_time = datetime.now()
        uptime_seconds = (current_time - self.stats['server_start_time']).total_seconds()

        active_players_count = sum(room.get_player_count() for room in self.rooms.values())
        
        # Estimate memory (very rough)
        player_mem_kb = 0.5 
        room_mem_kb = 2.0 
        estimated_mem_mb = (len(self.rooms) * room_mem_kb + active_players_count * player_mem_kb) / 1024


        return {
            "status": "maintenance" if self.maintenance_mode else "healthy",
            "version": "1.0.0 Production",
            "active_rooms": len([r for r in self.rooms.values() if r.get_player_count() > 0 or r.spectators]),
            "total_rooms_ever_created": self.stats['total_rooms_created'],
            "current_rooms_in_memory": len(self.rooms),
            "active_players": active_players_count,
            "peak_concurrent_players": self.stats['peak_concurrent_players'],
            "total_connections_ever": self.stats['total_players_connected'], # total unique player IDs that connected
            "current_websocket_connections": len(self.connections),
            "uptime_seconds": int(uptime_seconds),
            "uptime_human": str(timedelta(seconds=int(uptime_seconds))),
            "estimated_memory_usage_mb": round(estimated_mem_mb, 2),
            "total_hands_played_server_wide": self.stats['total_hands_played_server_wide'],
            "total_money_wagered_server_wide": self.stats['total_money_wagered_server_wide'],
            "total_money_won_by_players_server_wide": self.stats['total_money_won_by_players_server_wide'],
            "total_chat_messages": self.stats['total_chat_messages'],
            "security": {
                "banned_ips_count": len(self.banned_ips),
                "recent_security_events_count": len(self.security_events),
                "total_warnings_issued": self.stats['total_warnings_issued'],
                "total_bans_issued": self.stats['total_bans_issued']
            }
        }

    def get_room_list(self) -> List[Dict[str, Any]]:
        """Get list of public rooms with relevant details for a lobby"""
        public_rooms_data = []
        for room_code, room in self.rooms.items():
            # Define criteria for a room to be listed (e.g., public, not password protected, has space)
            if (room.is_public and
                not room.password and
                room.get_player_count() < room.max_players): # Only list rooms with space

                public_rooms_data.append({
                    "code": room_code,
                    "name": room.name,
                    "players": room.get_player_count(),
                    "max_players": room.max_players,
                    "phase": room.phase.value, # Could be 'WAITING', 'PLAYER_TURNS' etc.
                    "created": room.created_at.strftime("%Y-%m-%d %H:%M:%S"), # More precise timestamp
                    "min_bet": room.min_bet,
                    "max_bet": room.max_bet,
                    "is_premium": room.is_premium,
                    "tournament_mode": room.tournament_mode
                })

        # Sort rooms, e.g., by most recently active or most players, newest first
        public_rooms_data.sort(key=lambda x: x["created"], reverse=True)
        return public_rooms_data[:50]  # Limit to a manageable number for the lobby display

# Global game instance
game = RoyalBlackjackGame()

# Enhanced Pydantic Models for WebSocket Payloads
class WSMessage(BaseModel):
    """WebSocket message structure with validation"""
    action: str = PydanticField(..., min_length=1, max_length=50) # Action is required
    payload: dict = PydanticField(default_factory=dict)

class CreateRoomPayload(BaseModel):
    """Create room request payload validation"""
    player_name: str = PydanticField(..., min_length=1, max_length=SecurityConfig.MAX_NAME_LENGTH)
    room_name: Optional[str] = PydanticField(None, max_length=SecurityConfig.MAX_ROOM_NAME_LENGTH)
    password: Optional[str] = PydanticField(None, min_length=4, max_length=20) # Example password constraints
    is_premium: bool = False # Default to standard room

class JoinRoomPayload(BaseModel):
    """Join room request payload validation"""
    room_code: str = PydanticField(..., min_length=6, max_length=10) # Allow for longer generated codes
    player_name: str = PydanticField(..., min_length=1, max_length=SecurityConfig.MAX_NAME_LENGTH)
    password: Optional[str] = PydanticField(None, max_length=20)
    reconnect_token: Optional[str] = None # For rejoining disconnected sessions

class PlayerActionPayload(BaseModel):
    """Player action request payload validation"""
    action_type: str = PydanticField(..., min_length=1, max_length=20) # e.g., "hit", "stand"
    amount: Optional[int] = PydanticField(None, ge=0) # For 'place_bet', amount can be up to MAX_BET

class ChatMessagePayload(BaseModel):
    """Chat message payload validation"""
    message: str = PydanticField(..., min_length=1, max_length=GameConfig.MAX_MESSAGE_LENGTH)

# Enhanced Game Loop
async def game_loop():
    """Main game loop with enhanced features, error handling, and adaptive timing."""
    logger.info("🎰 Royal Blackjack 3D Game Loop started with adaptive timing.")
    loop_count = 0
    last_cleanup_time = time.monotonic()
    last_stats_broadcast_time = time.monotonic()

    TARGET_FPS = 10  # Target ticks per second for general updates
    TARGET_INTERVAL = 1.0 / TARGET_FPS

    while game.running:
        loop_start_time = time.monotonic()
        try:
            loop_count += 1

            # Update server uptime stat
            game.stats['uptime'] = (datetime.now() - game.stats['server_start_time']).total_seconds()

            # Periodic cleanup task
            if loop_start_time - last_cleanup_time > GameConfig.ROOM_CLEANUP_INTERVAL:
                game.cleanup_inactive_rooms()
                last_cleanup_time = loop_start_time
                logger.debug(f"Periodic cleanup executed. Active rooms: {len(game.rooms)}")

            # Process rooms in DEALING phase (if initial cards not yet dealt)
            # This ensures new games progress quickly after start_game is called.
            dealing_rooms_to_process = [r for r in game.rooms.values()
                                        if r.phase == GamePhase.DEALING and not r.dealer_hand.cards] # Not yet dealt
            for room in dealing_rooms_to_process:
                if room.phase == GamePhase.DEALING: # Double check phase before dealing
                     game.deal_initial_cards(room.code)


            # Broadcast game states (can be done less frequently if needed)
            # For real-time feel, this should be fairly frequent.
            await broadcast_game_states()


            # Adaptive sleep to maintain target FPS
            loop_duration = time.monotonic() - loop_start_time
            sleep_duration = TARGET_INTERVAL - loop_duration
            if sleep_duration > 0:
                await asyncio.sleep(sleep_duration)
            elif sleep_duration < - (TARGET_INTERVAL * 2) : # If loop is taking significantly longer
                logger.warning(f"Game loop overrun: Took {loop_duration:.4f}s, Target: {TARGET_INTERVAL:.4f}s. System might be overloaded.")


        except Exception as e:
            logger.exception(f"Critical error in game_loop (iteration {loop_count}): {e}")
            await asyncio.sleep(1.0) # Sleep briefly after an error to prevent rapid error loops

    logger.info("🎰 Royal Blackjack 3D Game Loop has gracefully stopped.")


async def broadcast_game_states():
    """Efficiently broadcast game states to all connected clients in their respective rooms."""
    broadcast_tasks = []

    for room_code, room in list(game.rooms.items()): # Iterate copy for safety if rooms change
        # Collect all unique, connected user_ids associated with this room (players and spectators)
        user_ids_in_room = set()
        for p_id, player_obj in room.players.items():
            # Only consider players who are actually connected or are the current client being processed
            if player_obj.connection_id and player_obj.connection_id in game.connections:
                user_ids_in_room.add(player_obj.connection_id)
        
        for spec_id in room.spectators:
            if spec_id in game.connections:
                 user_ids_in_room.add(spec_id)


        # Prepare and queue broadcasts for each user in this room
        for user_id in list(user_ids_in_room): # Iterate copy
            ws_conn = game.connections.get(user_id)
            if ws_conn:
                try:
                    # Generate state specific to this user (e.g., for hiding other players' sensitive data)
                    game_state_for_user = game.get_game_state(room_code, user_id)
                    if "error" not in game_state_for_user: # Ensure state generation was successful
                        broadcast_tasks.append(
                            ws_conn.send_json({"type": "game_state", "data": game_state_for_user})
                        )
                except WebSocketDisconnect: # Connection might have just closed
                    logger.info(f"WebSocket already disconnected for user {user_id} during broadcast prep. Cleanup will handle.")
                    # No need to remove from game.connections here, finally block in endpoint handles it.
                except Exception as e:
                    logger.error(f"Error preparing/sending game_state for user {user_id} in room {room_code}: {e}")
                    # Potentially mark connection for closure if send fails repeatedly
            # If ws_conn is None here, it means connection is already cleaned up.
    
    # Execute all broadcasts concurrently
    if broadcast_tasks:
        results = await asyncio.gather(*broadcast_tasks, return_exceptions=True)
        
        # Log any failed broadcasts (exceptions are caught by asyncio.gather)
        failed_count = sum(1 for result in results if isinstance(result, Exception))
        if failed_count > 0:
            logger.warning(f"Broadcast failed for {failed_count} out of {len(broadcast_tasks)} attempts. Exceptions: {[r for r in results if isinstance(r,Exception)]}")
            # Individual connection issues are often handled by WebSocketDisconnect in their own loops.

# Enhanced WebSocket Message Handler
async def handle_websocket_message(websocket: WebSocket, player_id: str, message: WSMessage, ip_address: Optional[str] = None):
    """Handle incoming WebSocket messages with enhanced security and validation"""
    action = message.action
    payload = message.payload

    # Check if server is in maintenance mode (allow critical ops like 'ping')
    if game.maintenance_mode and action not in ['ping', 'get_server_stats']: # Allow stats for admin
        await websocket.send_json({
            "type": "error",
            "message": "🔧 Server is currently under maintenance. Please try again later."
        })
        return

    # IP-based rate limiting for all actions (can be too broad, use with care)
    # if ip_address and not game.check_ip_rate_limit(ip_address):
    #     await websocket.send_json({"type": "error", "message": "⚠️ Too many requests. Please slow down."})
    #     game.log_security_event('ip_rate_limit_ws', {'player_id': player_id, 'ip': ip_address, 'action': action})
    #     return # Don't process further if IP is rate-limited

    try:
        # Validate payload based on action type
        validated_payload = None
        if action == "create_room": validated_payload = CreateRoomPayload(**payload)
        elif action == "join_room": validated_payload = JoinRoomPayload(**payload)
        elif action == "player_action": validated_payload = PlayerActionPayload(**payload)
        elif action == "send_chat_message": validated_payload = ChatMessagePayload(**payload)
        # For other actions, payload is used directly or not at all.

        # Core action handling logic
        if action == "create_room":
            room_code = game.create_room(
                player_id,
                validated_payload.room_name,
                validated_payload.password
            )
            if not room_code:
                await websocket.send_json({"type": "error", "message": "🏛️ Could not create room (server full or error)."})
                return

            if game.join_room(room_code, player_id, validated_payload.player_name, validated_payload.password, ip_address):
                await websocket.send_json({"type": "room_created", "data": {"room_code": room_code, "player_name": validated_payload.player_name}})
            else:
                await websocket.send_json({"type": "error", "message": "❌ Failed to join the created room."})

        elif action == "join_room":
            # Handle reconnection attempt
            room = game.rooms.get(validated_payload.room_code)
            player_to_reconnect = None
            if room and validated_payload.reconnect_token:
                player_to_reconnect = next((p for p_id, p in room.players.items() 
                                            if p.validate_reconnect_token(validated_payload.reconnect_token)), None)
            
            if player_to_reconnect:
                player_to_reconnect.connection_id = player_id # New WebSocket connection_id for this player
                player_to_reconnect.status = PlayerStatus.ACTIVE
                player_to_reconnect.last_activity = datetime.now()
                player_to_reconnect.ip_address = ip_address
                game.player_rooms[player_id] = validated_payload.room_code
                game.connections[player_id] = websocket # Update connection mapping
                # Remove old connection_id if it was different and still in game.connections
                if player_to_reconnect.id != player_id and player_to_reconnect.id in game.connections:
                    del game.connections[player_to_reconnect.id]

                logger.info(f"Player {player_to_reconnect.name} ({player_to_reconnect.id}) reconnected to room {validated_payload.room_code} with new conn_id {player_id}.")
                await websocket.send_json({"type": "room_joined", "data": {"room_code": validated_payload.room_code, "player_name": player_to_reconnect.name}})

            elif game.join_room(validated_payload.room_code, player_id, validated_payload.player_name, validated_payload.password, ip_address):
                await websocket.send_json({"type": "room_joined", "data": {"room_code": validated_payload.room_code, "player_name": validated_payload.player_name}})
            else:
                await websocket.send_json({"type": "error", "message": "❌ Failed to join room (not found, full, wrong password, or other issue)."})

        elif action == "spectate_room":
            room_code = payload.get("room_code", "").upper() # Spectate doesn't need strict payload validation
            if not room_code or not (6 <= len(room_code) <= 10) : # Basic check
                await websocket.send_json({"type": "error", "message": "❌ Invalid room code format for spectating."})
                return

            room = game.rooms.get(room_code)
            if room:
                room.spectators.add(player_id)
                game.player_rooms[player_id] = room_code # Spectators are also mapped to rooms
                await websocket.send_json({"type": "spectating", "data": {"room_code": room_code}})
            else:
                await websocket.send_json({"type": "error", "message": "🏛️ Room not found for spectating."})

        elif action == "leave_room":
            game.leave_room(player_id, force_remove=True) # Explicit leave is a full removal
            await websocket.send_json({"type": "room_left", "message": "You have left the room."})

        elif action == "start_game":
            room_code = game.player_rooms.get(player_id)
            if not room_code:
                await websocket.send_json({"type": "error", "message": "❌ Not in a room to start a game."})
                return

            if not game.start_game(room_code, player_id): # player_id is the initiator
                await websocket.send_json({"type": "error", "message": "❌ Cannot start game (e.g., not owner, no bets, wrong phase)."})
            # Success is handled by game state broadcast automatically

        elif action == "player_action":
            if not game.check_rate_limit(player_id, "action"): # Per-player action rate limit
                await websocket.send_json({"type": "error", "message": "⚠️ Action rate limit exceeded. Slow down."})
                return

            room_code = game.player_rooms.get(player_id)
            if not room_code:
                await websocket.send_json({"type": "error", "message": "❌ Not in a room to perform an action."})
                return

            try:
                blackjack_action_enum_val = PlayerAction(validated_payload.action_type)
                action_amount = validated_payload.amount if validated_payload.amount is not None else 0
                
                if not game.player_action(room_code, player_id, blackjack_action_enum_val, action_amount):
                    await websocket.send_json({"type": "error", "message": "❌ Invalid action, not your turn, or action not allowed."})
                # Success leads to game state update via broadcast
            except ValueError: # If action_type is not a valid PlayerAction enum
                await websocket.send_json({"type": "error", "message": f"❌ Unknown action type: {validated_payload.action_type}"})

        elif action == "send_chat_message":
            if not game.check_rate_limit(player_id, "message"): # Per-player chat rate limit
                await websocket.send_json({"type": "error", "message": "💬 Chat rate limit exceeded. Please wait."})
                return

            room_code = game.player_rooms.get(player_id)
            if not room_code:
                await websocket.send_json({"type": "error", "message": "❌ Must be in a room to send chat messages."})
                return

            room = game.rooms.get(room_code)
            if room and room.add_chat_message(player_id, validated_payload.message):
                game.stats['total_chat_messages'] += 1
                # Chat update will be part of game_state broadcast
            else:
                await websocket.send_json({"type": "error", "message": "❌ Message rejected (e.g., inappropriate content, server error)."})

        elif action == "get_room_list":
            rooms_list = game.get_room_list()
            await websocket.send_json({"type": "room_list", "data": {"rooms": rooms_list}})

        elif action == "ping":
            await websocket.send_json({
                "type": "pong",
                "data": { "client_timestamp": payload.get("timestamp"), "server_timestamp": time.time()}
            })
        
        elif action == "get_server_stats": # Could be admin-only
            stats_data = game.get_server_stats()
            await websocket.send_json({"type": "server_stats", "data": stats_data})


        else:
            await websocket.send_json({"type": "error", "message": f"❌ Unknown action received: {action}"})

    except ValidationError as e: # Catches Pydantic validation errors for payloads
        logger.warning(f"Payload validation error for player {player_id}, action {action}: {e.errors()}")
        await websocket.send_json({"type": "error", "message": f"❌ Invalid data for action '{action}': {e.errors()[0]['msg']}"})
    except WebSocketDisconnect:
        raise # Re-raise to be handled by the main WebSocket endpoint's finally block
    except Exception as e:
        logger.exception(f"Unexpected error handling message from {player_id} (Action: {action}): {e}")
        try:
            await websocket.send_json({"type": "error", "message": "🔧 A server error occurred. Please try again."})
        except Exception: # If sending error also fails, connection is likely dead
            pass


# Enhanced FastAPI Application Setup
@asynccontextmanager
async def lifespan(app_instance: FastAPI):
    """Application lifespan handler for startup and shutdown events."""
    logger.info("🚀 Starting Royal Blackjack 3D Production Server...")

    # Start the main game loop as a background task
    game_task = asyncio.create_task(game_loop())

    try:
        yield # Application runs here
    finally:
        # Graceful shutdown sequence
        logger.info("🛑 Initiating graceful shutdown of Royal Blackjack 3D server...")
        game.running = False # Signal game loop to stop

        # Notify all connected clients about the shutdown
        shutdown_message = {
            "type": "server_shutdown",
            "message": "🔧 The server is shutting down for maintenance. Thanks for playing Royal Blackjack 3D!"
        }
        disconnect_tasks = []
        for ws_conn in list(game.connections.values()): # Iterate copy
            try:
                disconnect_tasks.append(ws_conn.send_json(shutdown_message))
            except Exception: pass # Ignore errors if connection already closed

        if disconnect_tasks:
            await asyncio.gather(*disconnect_tasks, return_exceptions=True)
            logger.info(f"Sent shutdown notification to {len(disconnect_tasks)} clients.")

        # Wait for the game loop to finish its current iteration and stop
        try:
            await asyncio.wait_for(game_task, timeout=10.0) # Wait up to 10 seconds
            logger.info("Game loop shut down gracefully.")
        except asyncio.TimeoutError:
            logger.warning("Game loop did not shut down within timeout. Forcing cancellation.")
            game_task.cancel()
            try:
                await game_task
            except asyncio.CancelledError:
                logger.info("Game loop task was cancelled.")
        except Exception as e:
            logger.error(f"Error during game_task await: {e}")


        # Close all remaining WebSocket connections
        close_tasks = [ws_conn.close(code=1001, reason="Server shutting down")
                       for ws_conn in list(game.connections.values())] # Iterate copy
        if close_tasks:
            await asyncio.gather(*close_tasks, return_exceptions=True)
            logger.info(f"Closed {len(close_tasks)} remaining WebSocket connections.")

        logger.info("🎰 Royal Blackjack 3D server shutdown sequence complete.")


# Create FastAPI application instance
app = FastAPI(
    title="Royal Blackjack 3D - Premium Casino Platform",
    description="Professional 3D Multiplayer Blackjack Casino Experience - Production Ready",
    version="1.0.0", # Update version as appropriate
    lifespan=lifespan,
    docs_url="/api/docs" if os.getenv("ENVIRONMENT", "development") == "development" else None, # Dev only
    redoc_url="/api/redoc" if os.getenv("ENVIRONMENT", "development") == "development" else None # Dev only
)

# Enhanced CORS middleware for production
# Configure ALLOWED_ORIGINS via environment variable for flexibility
allowed_origins_str = os.getenv("ALLOWED_ORIGINS", "http://localhost:8000,http://127.0.0.1:8000")
# For Render.com, this might be your frontend's .onrender.com domain, or "*" for open access.
# Example: "https://myblackjackgame.onrender.com,http://localhost:3000"
origins = [origin.strip() for origin in allowed_origins_str.split(",") if origin.strip()]
if not origins: origins = ["*"] # Fallback if misconfigured

app.add_middleware(
    CORSMiddleware,
    allow_origins=origins,
    allow_credentials=True,
    allow_methods=["GET", "POST", "OPTIONS"], # Adjust as needed for REST API
    allow_headers=["*"], # Or specify headers like "Content-Type", "Authorization"
)

# Serve static files (e.g., HTML, CSS, JS for the game client)
# Assumes your 'index.html' and other static assets are in a 'static' subdirectory.
# If index.html is at the root, adjust the root path handler.
static_dir = "static"
if os.path.exists(static_dir) and os.path.isdir(static_dir):
    app.mount(f"/{static_dir}", StaticFiles(directory=static_dir, html=True), name="static_assets")
    logger.info(f"Serving static files from '{static_dir}' directory.")


# Production HTTP Routes
@app.get("/", response_class=HTMLResponse)
async def get_root_or_game_page():
    """
    Serve the main game interface (index.html).
    Assumes 'index.html' is at the root or in the 'static' folder if StaticFiles is configured with html=True.
    """
    # Path to your main HTML file
    # If you put index.html in 'static' and mounted StaticFiles with html=True at "/",
    # FastAPI might serve it automatically. Otherwise, explicitly:
    html_file_path = "index.html" # Assuming index.html is at the project root
    
    # If you prefer index.html inside 'static' folder that is served at root:
    # Create a 'static' folder, put index.html there.
    # Then mount StaticFiles at root: app.mount("/", StaticFiles(directory="static", html=True), name="root_static")
    # This route then might not be needed or could be a fallback.

    if os.path.exists(html_file_path):
        return FileResponse(html_file_path)
    else:
        # Fallback HTML if 'index.html' is not found
        logger.warning(f"Main HTML file '{html_file_path}' not found. Serving fallback page.")
        # (The detailed fallback HTML from your original code can be inserted here)
        return HTMLResponse(
            content="""
            <!DOCTYPE html><html><head><title>Royal Blackjack 3D</title></head>
            <body><h1>Royal Blackjack 3D Server</h1><p>Game server is running. Frontend HTML file not found.</p></body></html>
            """, status_code=404
        )


@app.get("/health", tags=["Server Health"])
async def health_check_endpoint():
    """Enhanced health check, returns key server metrics."""
    server_stats = game.get_server_stats()
    health_status = {
        "status": server_stats.get("status", "unknown"),
        "timestamp": datetime.now().isoformat(),
        "version": server_stats.get("version", "unknown"),
        "uptime_human": server_stats.get("uptime_human", "unknown"),
        "active_rooms": server_stats.get("active_rooms", 0),
        "active_players": server_stats.get("active_players", 0),
        "current_websocket_connections": server_stats.get("current_websocket_connections",0)
    }
    return JSONResponse(content=health_status)

@app.get("/api/stats", tags=["Server Stats"])
async def get_detailed_server_stats():
    """REST endpoint to get comprehensive server statistics (potentially admin-only)."""
    # Add authentication/authorization for admin endpoints in production
    return JSONResponse(content=game.get_server_stats())


@app.get("/api/rooms", tags=["Game Rooms"])
async def get_public_game_rooms_list():
    """REST endpoint to fetch a list of public, joinable game rooms."""
    public_rooms = game.get_room_list()
    return JSONResponse(content={"rooms": public_rooms, "count": len(public_rooms)})

# (Example admin endpoint - secure this properly in production)
@app.post("/api/admin/maintenance", tags=["Admin"])
async def toggle_server_maintenance_mode(enable: bool, request: Request):
    # Implement proper admin authentication here (e.g., API key, OAuth)
    # For now, allow from localhost for dev, or require a simple header
    # admin_secret = os.getenv("ADMIN_SECRET", "supersecret")
    # if request.headers.get("X-Admin-Secret") != admin_secret:
    #    raise HTTPException(status_code=403, detail="Not authorized")
    
    game.maintenance_mode = enable
    status_message = "enabled" if enable else "disabled"
    logger.info(f"ADMIN ACTION: Maintenance mode has been {status_message}.")
    return JSONResponse(content={"maintenance_mode": game.maintenance_mode, "message": f"Server maintenance mode is now {status_message}."})

# Enhanced WebSocket Endpoint
@app.websocket("/ws")
async def websocket_game_endpoint(websocket: WebSocket):
    """Main WebSocket endpoint for game communication."""
    # Generate a unique ID for this connection session, can be different from player game ID.
    connection_id = str(uuid.uuid4())
    client_host = websocket.client.host if websocket.client else "unknown_host"
    client_port = websocket.client.port if websocket.client else 0
    client_ip = client_host # For simplicity, often the same or proxy IP

    logger.info(f"🔌 New WebSocket connection attempt from {client_ip}:{client_port} (Conn ID: {connection_id})")

    # IP-based connection rate limiting (before accepting)
    if not game.check_ip_rate_limit(client_ip): # Use a specific limit for new connections if desired
        logger.warning(f"Connection rejected for IP {client_ip} due to rate limiting. Conn ID: {connection_id}")
        # await websocket.close(code=status.WS_1008_POLICY_VIOLATION, reason="Rate limit exceeded")
        # Closing before accept might not be standard, better to accept then send error and close.
        await websocket.accept()
        await websocket.send_json({"type": "error", "message": "Connection rate limit exceeded."})
        await websocket.close(code=status.WS_1008_POLICY_VIOLATION)
        return

    await websocket.accept()
    game.connections[connection_id] = websocket # Register active connection
    
    # Send welcome/connected message
    welcome_message_data = {
        "connection_id": connection_id, # This is the WebSocket session ID
        # player_id will be part of create/join room payload from client
        "message": "🎰 Welcome to the Royal Blackjack 3D Experience!",
        "server_version": app.version,
        "timestamp": time.time()
    }
    await websocket.send_json({"type": "connected", "data": welcome_message_data})
    logger.info(f"WebSocket connection accepted for {client_ip}:{client_port} (Conn ID: {connection_id})")

    try:
        while True:
            data = await websocket.receive_text()
            try:
                message_data = json.loads(data)
                ws_message_obj = WSMessage(**message_data) # Validate structure
                # Pass connection_id as player_id for now, actions like join_room will establish game player_id
                await handle_websocket_message(websocket, connection_id, ws_message_obj, client_ip)
            except json.JSONDecodeError:
                logger.warning(f"Invalid JSON received from {connection_id}: {data[:100]}...") # Log snippet
                await websocket.send_json({"type": "error", "message": "❌ Invalid JSON format."})
            except ValidationError as e: # Pydantic validation error for WSMessage
                logger.warning(f"WSMessage validation error from {connection_id}: {e.errors()}")
                await websocket.send_json({"type": "error", "message": f"❌ Invalid message structure: {e.errors()[0]['msg']}"})
            # Specific payload validation errors are handled inside handle_websocket_message

    except WebSocketDisconnect as e:
        logger.info(f"WebSocket disconnected for {connection_id} (Code: {e.code}, Reason: '{e.reason}').")
    except Exception as e:
        logger.exception(f"Unexpected error in WebSocket handler for {connection_id}: {e}")
        try: # Attempt to inform client before closing if connection is still viable
            await websocket.send_json({"type": "error", "message": "🔧 A critical server error occurred with your connection."})
        except Exception: pass
    finally:
        # Comprehensive cleanup when WebSocket connection closes
        logger.info(f"Cleaning up connection {connection_id}...")
        if connection_id in game.connections:
            del game.connections[connection_id]

        # Player needs to be marked as disconnected in their room, not fully removed immediately
        # This allows for reconnection. `leave_room` with `force_remove=False` handles this.
        game.leave_room(connection_id, force_remove=False) # Pass connection_id which acts as player_id until game join
        
        logger.info(f"🔌 Connection closed and cleaned up for: {connection_id}")


# Main execution block for running the server
if __name__ == "__main__":
    port = int(os.getenv("PORT", 8000)) # Render.com sets the PORT environment variable
    host = os.getenv("HOST", "0.0.0.0") # Listen on all interfaces for Render.com

    # Uvicorn server configuration
    # For production on Render, reload should be False.
    # Workers can be configured based on Render plan's CPU cores (e.g., using WEB_CONCURRENCY env var)
    reload_flag = os.getenv("ENVIRONMENT", "development") == "development"
    
    # Number of workers. Gunicorn is often used in front of Uvicorn in production for worker management.
    # For a simple Uvicorn setup, you can specify workers. Render might manage this via Gunicorn.
    # If using gunicorn as entrypoint: gunicorn -w 4 -k uvicorn.workers.UvicornWorker app:app
    # For direct uvicorn:
    workers_count = int(os.getenv("WEB_CONCURRENCY", 1)) # Default to 1 if not set

    logger.info(f"Starting Uvicorn server on {host}:{port} with {workers_count} worker(s). Reload: {reload_flag}")
    
    uvicorn.run(
        "app:app",  # Points to the 'app' instance in this 'app.py' file
        host=host,
        port=port,
        reload=reload_flag, # Enable auto-reload for local development
        log_level="info",   # Uvicorn's own logging level
        workers=workers_count if not reload_flag else 1 # Multiple workers don't work well with reload
    )
