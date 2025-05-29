#!/usr/bin/env python3
"""
Royal Blackjack 3D - Complete Production Server
A full-featured multiplayer blackjack game with 3D interface
"""

import asyncio
import json
import logging
import os
import random
import time
import uuid
from typing import Dict, List, Optional, Set, Any
from enum import Enum
from dataclasses import dataclass, asdict, field
from collections import defaultdict
from contextlib import asynccontextmanager
from datetime import datetime, timedelta
import traceback

# FastAPI and WebSocket imports
import uvicorn
from fastapi import FastAPI, WebSocket, WebSocketDisconnect, HTTPException, Request, status
from fastapi.responses import HTMLResponse, FileResponse, JSONResponse
from fastapi.middleware.cors import CORSMiddleware
from fastapi.staticfiles import StaticFiles
from pydantic import BaseModel, ValidationError, Field as PydanticField

# Enhanced logging configuration
LOG_FORMAT = '%(asctime)s - %(name)s - %(levelname)s - %(message)s - [%(filename)s:%(lineno)d]'
logging.basicConfig(
    level=logging.INFO,
    format=LOG_FORMAT,
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler('blackjack_server.log', mode='a', encoding='utf-8')
    ]
)

# Set up logger
logger = logging.getLogger(__name__)

# Suppress noisy logs
logging.getLogger('uvicorn.access').setLevel(logging.WARNING)
logging.getLogger('uvicorn.error').setLevel(logging.INFO)

# Game Configuration Constants
STARTING_MONEY = 1000
MIN_BET = 10
MAX_BET = 500
MAX_PLAYERS_PER_ROOM = 6
RATE_LIMIT_MESSAGES_PER_SECOND = 5
RATE_LIMIT_ACTIONS_PER_SECOND = 3
MAX_CHAT_MESSAGES = 50
MAX_ROOMS = 100
SESSION_TIMEOUT = 3600  # 1 hour
DEALER_HIT_THRESHOLD = 16  # Dealer hits on 16, stands on 17
ROOM_CLEANUP_INTERVAL = 300  # 5 minutes
INACTIVE_ROOM_TIMEOUT = 1800  # 30 minutes
HEARTBEAT_INTERVAL = 30  # 30 seconds
MAX_MESSAGE_LENGTH = 200
BLACKJACK_PAYOUT = 1.5  # 3:2 payout ratio
AUTO_RESET_DELAY = 8  # seconds to wait before resetting game

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
    SITTING_OUT = "sitting_out"
    ELIMINATED = "eliminated"

class HandResult(Enum):
    """Result of a completed hand"""
    WIN = "win"
    LOSE = "lose" 
    PUSH = "push"
    BLACKJACK = "blackjack"
    BUST = "bust"
    SURRENDER = "surrender"

# Data Classes
@dataclass
class Card:
    """Represents a playing card"""
    suit: str  # hearts, diamonds, clubs, spades
    rank: str  # A, 2-10, J, Q, K
    id: str = field(default_factory=lambda: str(uuid.uuid4()))

    def __str__(self):
        return f"{self.rank}{self.suit[0].upper()}"

    def get_blackjack_value(self, current_total: int = 0) -> int:
        """Return the blackjack value of this card"""
        if self.rank in ['J', 'Q', 'K']:
            return 10
        elif self.rank == 'A':
            # Ace is 11 unless it would bust, then it's 1
            return 11 if current_total + 11 <= 21 else 1
        else:
            try:
                return int(self.rank)
            except ValueError:
                logger.error(f"Invalid card rank: {self.rank}")
                return 0

@dataclass
class Hand:
    """Represents a hand of cards"""
    cards: List[Card] = field(default_factory=list)
    bet_amount: int = 0
    is_split: bool = False
    is_doubled: bool = False
    is_surrendered: bool = False
    result: Optional[HandResult] = None
    payout: int = 0

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
                    logger.warning(f"Invalid card rank: {card.rank}")
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
        return len(self.cards) == 2 and self.cards[0].rank == self.cards[1].rank

    def can_double_down(self) -> bool:
        """Check if hand can be doubled down"""
        return len(self.cards) == 2 and not self.is_split

    def to_dict(self) -> Dict[str, Any]:
        """Convert hand to dictionary for JSON serialization"""
        return {
            "cards": [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in self.cards],
            "value": self.get_value(),
            "bet_amount": self.bet_amount,
            "is_bust": self.is_bust(),
            "is_blackjack": self.is_blackjack(),
            "is_doubled": self.is_doubled,
            "is_surrendered": self.is_surrendered,
            "result": self.result.value if self.result else None,
            "payout": self.payout
        }

@dataclass
class Player:
    """Represents a player in the game"""
    id: str
    name: str
    money: int = STARTING_MONEY
    hands: List[Hand] = field(default_factory=lambda: [Hand()])
    current_hand_index: int = 0
    status: PlayerStatus = PlayerStatus.ACTIVE
    avatar: str = "default"
    color: str = "#ffffff"
    connection_id: Optional[str] = None
    is_ai: bool = False
    session_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    total_hands_played: int = 0
    total_hands_won: int = 0
    total_winnings: int = 0
    last_activity: datetime = field(default_factory=datetime.now)
    join_time: datetime = field(default_factory=datetime.now)

    def get_current_hand(self) -> Hand:
        """Get the hand currently being played"""
        if 0 <= self.current_hand_index < len(self.hands):
            return self.hands[self.current_hand_index]
        return self.hands[0] if self.hands else Hand()

    def can_act(self) -> bool:
        """Check if player can take an action"""
        if self.status != PlayerStatus.ACTIVE:
            return False
            
        current_hand = self.get_current_hand()
        return (not current_hand.is_bust() and 
                not current_hand.is_surrendered and
                current_hand.get_value() < 21)

    def reset_for_new_hand(self):
        """Reset player for a new hand"""
        self.hands = [Hand()]
        self.current_hand_index = 0
        if self.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED]:
            self.status = PlayerStatus.ACTIVE

    def update_activity(self):
        """Update last activity timestamp"""
        self.last_activity = datetime.now()

    def to_dict(self, current_player_id: Optional[str] = None) -> Dict[str, Any]:
        """Convert player to dictionary for JSON serialization"""
        hands_data = [hand.to_dict() for hand in self.hands]
        
        return {
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
            "stats": {
                "total_hands_played": self.total_hands_played,
                "total_hands_won": self.total_hands_won,
                "total_winnings": self.total_winnings,
                "win_rate": round((self.total_hands_won / max(self.total_hands_played, 1)) * 100, 1)
            }
        }

@dataclass
class Room:
    """Represents a game room"""
    code: str
    name: str
    players: Dict[str, Player]
    spectators: Set[str]
    deck: List[Card]
    dealer_hand: Hand
    current_player_id: Optional[str] = None
    phase: GamePhase = GamePhase.WAITING
    chat_messages: List[Dict] = field(default_factory=list)
    hand_number: int = 0
    created_at: datetime = field(default_factory=datetime.now)
    last_activity: datetime = field(default_factory=datetime.now)
    owner_id: Optional[str] = None
    min_bet: int = MIN_BET
    max_bet: int = MAX_BET
    _player_turn_order: List[str] = field(default_factory=list)
    _current_player_turn_index: int = 0
    is_public: bool = True
    max_players: int = MAX_PLAYERS_PER_ROOM

    def __post_init__(self):
        """Initialize room after creation"""
        if not self.deck:
            self.deck = self.create_deck()
        if not hasattr(self, 'dealer_hand') or not self.dealer_hand:
            self.dealer_hand = Hand()

    def create_deck(self, num_decks: int = 1) -> List[Card]:
        """Create and shuffle deck(s)"""
        suits = ["hearts", "diamonds", "clubs", "spades"]
        ranks = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]
        deck = []
        
        for _ in range(num_decks):
            for suit in suits:
                for rank in ranks:
                    deck.append(Card(suit, rank))
        
        random.shuffle(deck)
        logger.debug(f"Created and shuffled deck with {len(deck)} cards for room {self.code}")
        return deck

    def shuffle_deck(self):
        """Shuffle the deck"""
        self.deck = self.create_deck()
        logger.info(f"Reshuffled deck for room {self.code}")

    def deal_card(self) -> Optional[Card]:
        """Deal a card from the deck"""
        if len(self.deck) < 15:  # Reshuffle if deck is low
            logger.info(f"Deck running low in room {self.code}, reshuffling")
            self.shuffle_deck()
        
        if self.deck:
            card = self.deck.pop()
            logger.debug(f"Dealt card {card} in room {self.code}")
            return card
        else:
            logger.error(f"No cards available in room {self.code}")
            return None

    def get_active_players(self) -> List[Player]:
        """Get list of active players with money to play"""
        active = [p for p in self.players.values() 
                 if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED] 
                 and p.money >= self.min_bet
                 and not p.is_ai]
        logger.debug(f"Room {self.code} has {len(active)} active players")
        return active

    def advance_to_next_player(self):
        """Move to the next player's turn"""
        if self._current_player_turn_index < len(self._player_turn_order) - 1:
            self._current_player_turn_index += 1
            self.current_player_id = self._player_turn_order[self._current_player_turn_index]
            logger.info(f"Advanced to next player {self.current_player_id} in room {self.code}")
        else:
            # All players have acted, move to dealer turn
            self.current_player_id = None
            self.phase = GamePhase.DEALER_TURN
            logger.info(f"All players acted, moving to dealer turn in room {self.code}")

    def update_activity(self):
        """Update last activity timestamp"""
        self.last_activity = datetime.now()

    def is_inactive(self) -> bool:
        """Check if room has been inactive too long"""
        return (datetime.now() - self.last_activity).total_seconds() > INACTIVE_ROOM_TIMEOUT

    def get_player_count(self) -> int:
        """Get count of human players"""
        return len([p for p in self.players.values() if not p.is_ai])

# Main Game Logic Class
class RoyalBlackjackGame:
    """Main game engine for Royal Blackjack 3D"""
    
    def __init__(self):
        self.rooms: Dict[str, Room] = {}
        self.connections: Dict[str, WebSocket] = {}
        self.player_rooms: Dict[str, str] = {}
        self.rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.action_rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.running = True
        
        # Server statistics
        self.stats = {
            'total_rooms_created': 0,
            'total_players_connected': 0,
            'total_hands_played': 0,
            'server_start_time': datetime.now(),
            'peak_concurrent_players': 0,
            'total_money_wagered': 0
        }
        
        logger.info("Royal Blackjack 3D Game Engine initialized")

    def generate_room_code(self) -> str:
        """Generate a unique 6-character room code"""
        attempts = 0
        while attempts < 100:  # Prevent infinite loop
            code = ''.join(random.choices('ABCDEFGHJKLMNPQRSTUVWXYZ23456789', k=6))
            if code not in self.rooms:
                return code
            attempts += 1
        
        # Fallback with timestamp if all random codes taken
        timestamp = str(int(time.time()))[-4:]
        return f"R{timestamp}X"

    def create_room(self, creator_player_id: str, room_name: Optional[str] = None) -> Optional[str]:
        """Create a new game room"""
        if len(self.rooms) >= MAX_ROOMS:
            logger.warning(f"Maximum number of rooms ({MAX_ROOMS}) reached")
            return None
        
        room_code = self.generate_room_code()
        room_name = room_name or f"Blackjack {room_code}"
        
        # Create the room
        room = Room(
            code=room_code, 
            name=room_name, 
            players={}, 
            spectators=set(),
            deck=[], 
            dealer_hand=Hand(),
            owner_id=creator_player_id
        )
        
        self.rooms[room_code] = room
        self.stats['total_rooms_created'] += 1
        
        logger.info(f"Room {room_code} ({room_name}) created by player {creator_player_id}")
        return room_code

    def join_room(self, room_code: str, player_id: str, player_name: str) -> bool:
        """Join a player to a room"""
        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"Attempt to join non-existent room {room_code} by {player_id}")
            return False

        # Check room capacity
        if room.get_player_count() >= room.max_players:
            logger.warning(f"Room {room_code} is full ({room.max_players} players)")
            return False

        # Validate and clean player name
        if not player_name or len(player_name.strip()) == 0:
            logger.warning(f"Invalid player name for {player_id}")
            return False

        player_name = player_name.strip()[:20]  # Limit name length

        if player_id in room.players:  
            # Rejoining player
            rejoining_player = room.players[player_id]
            rejoining_player.connection_id = player_id
            rejoining_player.name = player_name
            rejoining_player.update_activity()
            logger.info(f"Player {player_name} ({player_id}) re-joined room {room_code}")
        else:  
            # New player
            # Generate unique color for player
            colors = [
                '#FF6B6B', '#4ECDC4', '#45B7D1', '#96CEB4', 
                '#FFEAA7', '#DDA0DD', '#98D8C8', '#F7DC6F',
                '#FF7675', '#74B9FF', '#00B894', '#FDCB6E'
            ]
            color_index = len(room.players) % len(colors)
            color = colors[color_index]
            
            player = Player(
                id=player_id, 
                name=player_name, 
                money=STARTING_MONEY,
                avatar=f"avatar_{random.randint(1, 10)}", 
                color=color,
                connection_id=player_id
            )
            room.players[player_id] = player
            self.stats['total_players_connected'] += 1
            
            # Update peak concurrent players
            total_players = sum(len(r.players) for r in self.rooms.values())
            if total_players > self.stats['peak_concurrent_players']:
                self.stats['peak_concurrent_players'] = total_players
            
            logger.info(f"Player {player_name} ({player_id}) joined room {room_code}")

        self.player_rooms[player_id] = room_code
        room.update_activity()
        return True

    def leave_room(self, player_id: str, force: bool = False):
        """Remove a player from their room"""
        logger.info(f"Player {player_id} attempting to leave room. Force: {force}")
        room_code = self.player_rooms.pop(player_id, None)
        if not room_code:
            return

        room = self.rooms.get(room_code)
        if not room:
            return

        # Remove from players or spectators
        if player_id in room.players:
            player_obj = room.players[player_id]
            logger.info(f"Player {player_obj.name} ({player_id}) leaving room {room_code}")
            del room.players[player_id]

        room.spectators.discard(player_id)

        # Handle game state if player was the current player
        if room.current_player_id == player_id and room.phase == GamePhase.PLAYER_TURNS:
            room.advance_to_next_player()

        # Close room if empty or transfer ownership
        remaining_players = [p for p in room.players.values() if not p.is_ai]
        if not remaining_players and not room.spectators:
            logger.info(f"Room {room_code} is empty. Closing room.")
            if room_code in self.rooms:
                del self.rooms[room_code]
        elif room.owner_id == player_id and remaining_players:
            # Transfer ownership to next player
            new_owner = next((pid for pid, p_obj in room.players.items() if not p_obj.is_ai), None)
            if new_owner:
                room.owner_id = new_owner
                logger.info(f"Room {room_code} ownership transferred to {new_owner}")

        room.update_activity()

    def start_game(self, room_code: str) -> bool:
        """Start a new game in the room"""
        room = self.rooms.get(room_code)
        if not room:
            logger.error(f"Cannot start game: room {room_code} not found")
            return False

        active_players = room.get_active_players()
        if len(active_players) < 1:
            logger.warning(f"Cannot start game in room {room_code}: No active players")
            return False

        if room.phase not in [GamePhase.WAITING, GamePhase.GAME_OVER]:
            logger.warning(f"Game already in progress in room {room_code}")
            return False

        # Check if all active players have placed bets
        players_with_bets = [p for p in active_players if p.hands[0].bet_amount > 0]
        if len(players_with_bets) == 0:
            logger.warning(f"Cannot start game in room {room_code}: No bets placed")
            return False

        logger.info(f"Starting blackjack game in room {room_code} with {len(players_with_bets)} players")
        
        # Initialize game state
        room.phase = GamePhase.DEALING
        room.hand_number += 1
        room.shuffle_deck()
        room.dealer_hand = Hand()
        self.stats['total_hands_played'] += 1

        # Reset players for new hand
        for player in room.players.values():
            player.total_hands_played += 1
            player.reset_for_new_hand()
            
            # Restore bet for players who had placed bets
            original_player = next((p for p in players_with_bets if p.id == player.id), None)
            if original_player:
                player.hands[0].bet_amount = original_player.hands[0].bet_amount
                self.stats['total_money_wagered'] += player.hands[0].bet_amount

        # Set up turn order (randomized for fairness)
        room._player_turn_order = [p.id for p in players_with_bets]
        random.shuffle(room._player_turn_order)
        room._current_player_turn_index = 0
        room.current_player_id = room._player_turn_order[0] if room._player_turn_order else None

        room.update_activity()
        return True

    def deal_initial_cards(self, room_code: str):
        """Deal initial two cards to each player and dealer"""
        room = self.rooms.get(room_code)
        if not room or room.phase != GamePhase.DEALING:
            return

        active_players = [room.players[pid] for pid in room._player_turn_order]
        
        # Deal 2 cards to each player and dealer
        for card_round in range(2):
            # Deal to players first
            for player in active_players:
                if player.hands and len(player.hands[0].cards) < 2:
                    card = room.deal_card()
                    if card:
                        player.hands[0].cards.append(card)
            
            # Deal to dealer
            if len(room.dealer_hand.cards) < 2:
                card = room.deal_card()
                if card:
                    room.dealer_hand.cards.append(card)

        # Check for blackjacks
        blackjack_players = []
        for player in active_players:
            if player.hands[0].is_blackjack():
                player.status = PlayerStatus.BLACKJACK
                blackjack_players.append(player.name)
                logger.info(f"Player {player.name} got blackjack in room {room_code}")

        # Move to appropriate phase
        if all(p.status == PlayerStatus.BLACKJACK for p in active_players):
            # All players have blackjack, go straight to dealer
            room.phase = GamePhase.DEALER_TURN
        else:
            room.phase = GamePhase.PLAYER_TURNS
            # Skip blackjack players in turn order
            while (room.current_player_id and 
                   room.players[room.current_player_id].status == PlayerStatus.BLACKJACK):
                room.advance_to_next_player()
                if room.phase == GamePhase.DEALER_TURN:
                    break

        room.update_activity()
        logger.info(f"Initial cards dealt in room {room_code}. Blackjacks: {blackjack_players}")

    def player_action(self, room_code: str, player_id: str, action: PlayerAction, amount: int = 0) -> bool:
        """Process a player action"""
        room = self.rooms.get(room_code)
        if not room:
            logger.error(f"Room {room_code} not found for player action")
            return False

        player = room.players.get(player_id)
        if not player:
            logger.error(f"Player {player_id} not found in room {room_code}")
            return False

        logger.info(f"Processing action: {player.name} - {action.value} - Amount: {amount} in room {room_code}")

        try:
            success = False
            if action == PlayerAction.PLACE_BET:
                success = self._process_place_bet(room, player, amount)
            elif action == PlayerAction.HIT:
                success = self._process_hit(room, player)
            elif action == PlayerAction.STAND:
                success = self._process_stand(room, player)
            elif action == PlayerAction.DOUBLE_DOWN:
                success = self._process_double_down(room, player)
            elif action == PlayerAction.SPLIT:
                success = self._process_split(room, player)
            elif action == PlayerAction.SURRENDER:
                success = self._process_surrender(room, player)
            
            if success:
                player.update_activity()
                room.update_activity()
            
            return success
            
        except Exception as e:
            logger.error(f"Error processing player action: {e}")
            logger.error(traceback.format_exc())
            return False

    def _process_place_bet(self, room: Room, player: Player, amount: int) -> bool:
        """Process a bet placement"""
        if room.phase != GamePhase.WAITING:
            logger.warning(f"Cannot place bet: room {room.code} not in waiting phase")
            return False
        
        if amount < room.min_bet or amount > room.max_bet or amount > player.money:
            logger.warning(f"Invalid bet amount {amount} for player {player.name}")
            return False

        player.money -= amount
        player.hands[0].bet_amount = amount
        
        logger.info(f"Player {player.name} placed bet of ${amount}")
        return True

    def _process_hit(self, room: Room, player: Player) -> bool:
        """Process a hit action"""
        if room.phase != GamePhase.PLAYER_TURNS or room.current_player_id != player.id:
            return False

        current_hand = player.get_current_hand()
        card = room.deal_card()
        if not card:
            logger.error(f"No card available for hit action")
            return False

        current_hand.cards.append(card)
        logger.info(f"Player {player.name} hit and received {card}")

        if current_hand.is_bust():
            player.status = PlayerStatus.BUST
            logger.info(f"Player {player.name} busted with {current_hand.get_value()}")
            self._advance_player_turn(room)
        elif current_hand.get_value() == 21:
            logger.info(f"Player {player.name} reached 21")
            self._advance_player_turn(room)

        return True

    def _process_stand(self, room: Room, player: Player) -> bool:
        """Process a stand action"""
        if room.phase != GamePhase.PLAYER_TURNS or room.current_player_id != player.id:
            return False

        player.status = PlayerStatus.STANDING
        logger.info(f"Player {player.name} stands with {player.get_current_hand().get_value()}")
        self._advance_player_turn(room)
        return True

    def _process_double_down(self, room: Room, player: Player) -> bool:
        """Process a double down action"""
        if room.phase != GamePhase.PLAYER_TURNS or room.current_player_id != player.id:
            return False

        current_hand = player.get_current_hand()
        if not current_hand.can_double_down() or player.money < current_hand.bet_amount:
            logger.warning(f"Player {player.name} cannot double down")
            return False

        # Double the bet
        additional_bet = current_hand.bet_amount
        player.money -= additional_bet
        current_hand.bet_amount += additional_bet
        current_hand.is_doubled = True

        # Deal exactly one card
        card = room.deal_card()
        if card:
            current_hand.cards.append(card)
            logger.info(f"Player {player.name} doubled down and received {card}")

        if current_hand.is_bust():
            player.status = PlayerStatus.BUST
            logger.info(f"Player {player.name} busted after double down")

        self._advance_player_turn(room)
        return True

    def _process_split(self, room: Room, player: Player) -> bool:
        """Process a split action"""
        if room.phase != GamePhase.PLAYER_TURNS or room.current_player_id != player.id:
            return False

        current_hand = player.get_current_hand()
        if not current_hand.can_split() or player.money < current_hand.bet_amount:
            logger.warning(f"Player {player.name} cannot split")
            return False

        # Create new hand with second card
        second_card = current_hand.cards.pop()
        new_hand = Hand(cards=[second_card], bet_amount=current_hand.bet_amount, is_split=True)
        current_hand.is_split = True
        player.hands.append(new_hand)
        player.money -= current_hand.bet_amount

        # Deal new cards to both hands
        for hand in player.hands:
            if len(hand.cards) == 1:  # Only add card to split hands
                card = room.deal_card()
                if card:
                    hand.cards.append(card)

        logger.info(f"Player {player.name} split their hand")
        return True

    def _process_surrender(self, room: Room, player: Player) -> bool:
        """Process a surrender action"""
        if room.phase != GamePhase.PLAYER_TURNS or room.current_player_id != player.id:
            return False

        current_hand = player.get_current_hand()
        if len(current_hand.cards) != 2:
            return False

        current_hand.is_surrendered = True
        # Return half the bet
        refund = current_hand.bet_amount // 2
        player.money += refund
        
        logger.info(f"Player {player.name} surrendered, refunded ${refund}")
        self._advance_player_turn(room)
        return True

    def _advance_player_turn(self, room: Room):
        """Advance to next player or hand"""
        # Check if current player has more hands to play
        current_player = room.players.get(room.current_player_id)
        if current_player and current_player.current_hand_index < len(current_player.hands) - 1:
            current_player.current_hand_index += 1
            logger.info(f"Player {current_player.name} moving to hand {current_player.current_hand_index + 1}")
            return

        # Reset hand index for next player
        if current_player:
            current_player.current_hand_index = 0

        # Move to next player
        room.advance_to_next_player()
        
        if room.phase == GamePhase.DEALER_TURN:
            self._play_dealer_hand(room)

    def _play_dealer_hand(self, room: Room):
        """Play the dealer's hand according to rules"""
        logger.info(f"Dealer playing hand in room {room.code}")
        
        # Dealer plays by standard rules: hit on 16, stand on 17+
        while room.dealer_hand.get_value() <= DEALER_HIT_THRESHOLD:
            card = room.deal_card()
            if card:
                room.dealer_hand.cards.append(card)
                dealer_value = room.dealer_hand.get_value()
                logger.info(f"Dealer hit and received {card}, total: {dealer_value}")
            else:
                logger.error("No card available for dealer")
                break

        dealer_final = room.dealer_hand.get_value()
        if dealer_final > 21:
            logger.info(f"Dealer busted with {dealer_final}")
        else:
            logger.info(f"Dealer stands with {dealer_final}")

        room.phase = GamePhase.PAYOUT
        self._calculate_payouts(room)

    def _calculate_payouts(self, room: Room):
        """Calculate and distribute payouts"""
        logger.info(f"Calculating payouts for room {room.code}")
        dealer_value = room.dealer_hand.get_value()
        dealer_bust = room.dealer_hand.is_bust()
        dealer_blackjack = room.dealer_hand.is_blackjack()

        for player in room.players.values():
            if not player.hands or not any(h.bet_amount > 0 for h in player.hands):
                continue
                
            player_won_any = False
            total_payout = 0
            
            for hand in player.hands:
                if hand.bet_amount == 0:
                    continue
                    
                if hand.is_surrendered:
                    hand.result = HandResult.SURRENDER
                    hand.payout = 0  # Already handled in surrender
                    continue

                hand_value = hand.get_value()
                
                if hand.is_bust():
                    hand.result = HandResult.BUST
                    hand.payout = 0
                elif hand.is_blackjack() and not dealer_blackjack:
                    hand.result = HandResult.BLACKJACK
                    hand.payout = int(hand.bet_amount * (1 + BLACKJACK_PAYOUT))
                    player.money += hand.payout
                    total_payout += hand.payout
                    player_won_any = True
                elif dealer_bust or hand_value > dealer_value:
                    hand.result = HandResult.WIN
                    hand.payout = hand.bet_amount * 2
                    player.money += hand.payout
                    total_payout += hand.payout
                    player_won_any = True
                elif hand_value == dealer_value:
                    hand.result = HandResult.PUSH
                    hand.payout = hand.bet_amount  # Return original bet
                    player.money += hand.payout
                    total_payout += hand.bet_amount
                else:
                    hand.result = HandResult.LOSE
                    hand.payout = 0

            # Update player statistics
            if player_won_any:
                player.total_hands_won += 1
            
            net_result = total_payout - sum(h.bet_amount for h in player.hands if h.bet_amount > 0)
            player.total_winnings += net_result
            
            logger.info(f"Player {player.name}: Net result ${net_result}, Total winnings: ${player.total_winnings}")

        room.phase = GamePhase.GAME_OVER
        room.update_activity()
        
        # Schedule automatic reset
        asyncio.create_task(self._prepare_next_hand(room.code))

    async def _prepare_next_hand(self, room_code: str, delay: int = AUTO_RESET_DELAY):
        """Prepare room for next hand after delay"""
        await asyncio.sleep(delay)
        room = self.rooms.get(room_code)
        if not room:
            return

        # Check if room still has active players
        active_players = room.get_active_players()
        if not active_players:
            logger.info(f"No active players left in room {room_code}")
            return

        # Reset for next hand
        room.phase = GamePhase.WAITING
        for player in room.players.values():
            player.reset_for_new_hand()
        room.dealer_hand = Hand()
        room.current_player_id = None
        room._player_turn_order = []
        room._current_player_turn_index = 0
        
        logger.info(f"Room {room_code} prepared for next hand")

    def get_game_state(self, room_code: str, for_player_id: str) -> Dict[str, Any]:
        """Get current game state for a player"""
        room = self.rooms.get(room_code)
        if not room:
            return {"error": "Room not found"}

        is_player = for_player_id in room.players and not room.players[for_player_id].is_ai
        is_spectator = for_player_id in room.spectators

        # Build players data
        players_data = {}
        for p_id, p_obj in room.players.items():
            players_data[p_id] = p_obj.to_dict(room.current_player_id)

        # Dealer hand - hide hole card until dealer turn
        dealer_cards = []
        for i, card in enumerate(room.dealer_hand.cards):
            if (i == 1 and 
                room.phase in [GamePhase.DEALING, GamePhase.PLAYER_TURNS] and 
                len(room.dealer_hand.cards) > 1):
                # Hide hole card
                dealer_cards.append({"suit": "back", "rank": "back", "id": "hidden"})
            else:
                dealer_cards.append({"suit": card.suit, "rank": card.rank, "id": card.id})

        # Calculate visible dealer value
        visible_dealer_value = None
        if room.phase in [GamePhase.DEALER_TURN, GamePhase.PAYOUT, GamePhase.GAME_OVER]:
            visible_dealer_value = room.dealer_hand.get_value()
        elif len(dealer_cards) > 0 and dealer_cards[0]["suit"] != "back":
            # Show value of up card only during player turns
            up_card = room.dealer_hand.cards[0]
            visible_dealer_value = up_card.get_blackjack_value()

        game_state = {
            "room_code": room.code,
            "room_name": room.name,
            "phase": room.phase.value,
            "current_player_id": room.current_player_id,
            "players": players_data,
            "dealer_hand": {
                "cards": dealer_cards,
                "value": visible_dealer_value
            },
            "chat_messages": room.chat_messages[-20:],  # Last 20 messages
            "is_player_in_game": is_player,
            "is_spectator": is_spectator,
            "spectator_count": len(room.spectators),
            "hand_number": room.hand_number,
            "min_bet": room.min_bet,
            "max_bet": room.max_bet,
            "can_act": (is_player and 
                       room.current_player_id == for_player_id and 
                       room.phase == GamePhase.PLAYER_TURNS and
                       room.players[for_player_id].can_act()),
            "available_actions": self.get_available_actions(room, for_player_id) if is_player else [],
            "owner_id": room.owner_id
        }
        return game_state

    def get_available_actions(self, room: Room, player_id: str) -> List[Dict[str, Any]]:
        """Get available actions for a player"""
        player = room.players.get(player_id)
        if not player or not player.can_act() or room.current_player_id != player_id:
            return []

        actions = []
        current_hand = player.get_current_hand()

        if room.phase == GamePhase.WAITING and current_hand.bet_amount == 0:
            actions.append({
                "action": PlayerAction.PLACE_BET.value,
                "label": "Place Bet",
                "min_amount": room.min_bet,
                "max_amount": min(room.max_bet, player.money)
            })
        elif room.phase == GamePhase.PLAYER_TURNS:
            actions.append({"action": PlayerAction.HIT.value, "label": "Hit"})
            actions.append({"action": PlayerAction.STAND.value, "label": "Stand"})
            
            if current_hand.can_double_down() and player.money >= current_hand.bet_amount:
                actions.append({"action": PlayerAction.DOUBLE_DOWN.value, "label": "Double Down"})
            
            if (current_hand.can_split() and 
                player.money >= current_hand.bet_amount and 
                len(player.hands) < 4):  # Limit splits
                actions.append({"action": PlayerAction.SPLIT.value, "label": "Split"})
            
            if len(current_hand.cards) == 2 and not current_hand.is_split:
                actions.append({"action": PlayerAction.SURRENDER.value, "label": "Surrender"})

        return actions

    def add_chat_message(self, room_code: str, player_id: str, message_text: str) -> bool:
        """Add a chat message to a room"""
        room = self.rooms.get(room_code)
        if not room:
            return False

        player = room.players.get(player_id)
        player_name = player.name if player else f"Spectator_{player_id[:4]}"
        player_color = player.color if player else "#cccccc"

        cleaned_message = message_text.strip()
        if not cleaned_message or len(cleaned_message) > MAX_MESSAGE_LENGTH:
            return False

        # Basic content filtering
        banned_words = ['cheat', 'hack', 'bot', 'script']  # Expand as needed
        if any(word in cleaned_message.lower() for word in banned_words):
            logger.warning(f"Blocked message from {player_name}: inappropriate content")
            return False

        chat_msg = {
            "player_id": player_id,
            "player_name": player_name,
            "player_color": player_color,
            "message": cleaned_message,
            "timestamp": time.time(),
            "formatted_time": datetime.now().strftime("%H:%M:%S")
        }
        
        room.chat_messages.append(chat_msg)
        if len(room.chat_messages) > MAX_CHAT_MESSAGES:
            room.chat_messages = room.chat_messages[-MAX_CHAT_MESSAGES:]
        
        logger.debug(f"Chat in {room_code} by {player_name}: {cleaned_message}")
        room.update_activity()
        return True

    def check_rate_limit(self, client_id: str, limit_type: str = "message") -> bool:
        """Check if client is within rate limits"""
        limit_dict = self.rate_limits if limit_type == "message" else self.action_rate_limits
        max_per_second = RATE_LIMIT_MESSAGES_PER_SECOND if limit_type == "message" else RATE_LIMIT_ACTIONS_PER_SECOND

        current_time = time.time()
        # Clean old entries
        limit_dict[client_id] = [t for t in limit_dict[client_id] if current_time - t <= 1.0]

        if len(limit_dict[client_id]) < max_per_second:
            limit_dict[client_id].append(current_time)
            return True
        else:
            logger.warning(f"Rate limit exceeded for {client_id} (type: {limit_type})")
            return False

    def cleanup_inactive_rooms(self):
        """Remove inactive rooms and disconnected players"""
        current_time = datetime.now()
        rooms_to_delete = []
        
        for room_code, room in self.rooms.items():
            if room.is_inactive():
                logger.info(f"Marking inactive room {room_code} for deletion")
                rooms_to_delete.append(room_code)
                continue
                
            # Clean up disconnected players
            disconnected_players = []
            for player_id, player in room.players.items():
                if (current_time - player.last_activity).total_seconds() > SESSION_TIMEOUT:
                    disconnected_players.append(player_id)
            
            for player_id in disconnected_players:
                logger.info(f"Removing inactive player {player_id} from room {room_code}")
                self.leave_room(player_id, force=True)
        
        for room_code in rooms_to_delete:
            if room_code in self.rooms:
                del self.rooms[room_code]
                logger.info(f"Deleted inactive room {room_code}")

    def get_server_stats(self) -> Dict[str, Any]:
        """Get server statistics"""
        active_players = sum(len([p for p in room.players.values() if not p.is_ai]) 
                           for room in self.rooms.values())
        
        uptime = (datetime.now() - self.stats['server_start_time']).total_seconds()
        
        return {
            "status": "healthy",
            "active_rooms": len(self.rooms),
            "active_players": active_players,
            "total_connections": len(self.connections),
            "uptime_seconds": uptime,
            "uptime_hours": round(uptime / 3600, 2),
            **self.stats
        }

# Global game instance
game = RoyalBlackjackGame()

# Pydantic Models for Request Validation
class WSMessage(BaseModel):
    """WebSocket message structure"""
    action: str
    payload: dict = PydanticField(default_factory=dict)

class CreateRoomPayload(BaseModel):
    """Create room request payload"""
    player_name: str = PydanticField(min_length=1, max_length=20)
    room_name: Optional[str] = PydanticField(default=None, max_length=30)

class JoinRoomPayload(BaseModel):
    """Join room request payload"""
    room_code: str = PydanticField(min_length=6, max_length=6)
    player_name: str = PydanticField(min_length=1, max_length=20)

class PlayerActionPayload(BaseModel):
    """Player action request payload"""
    action_type: str
    amount: Optional[int] = 0

class ChatMessagePayload(BaseModel):
    """Chat message payload"""
    message: str = PydanticField(min_length=1, max_length=MAX_MESSAGE_LENGTH)

# Game Loop - Handles game state updates and broadcasting
async def game_loop():
    """Main game loop for processing game states and broadcasting updates"""
    logger.info("🎮 Game loop started")
    loop_count = 0
    
    while game.running:
        try:
            loop_count += 1
            
            # Periodic cleanup every 300 loops (~30 seconds at 10fps)
            if loop_count % 300 == 0:
                game.cleanup_inactive_rooms()
                logger.debug(f"Cleanup completed. Active rooms: {len(game.rooms)}")
            
            # Handle rooms in dealing phase that need initial cards
            dealing_rooms = [r for r in game.rooms.values() if r.phase == GamePhase.DEALING and not r.dealer_hand.cards]
            for room in dealing_rooms:
                game.deal_initial_cards(room.code)

            # Broadcast game state to all connected clients
            broadcast_tasks = []
            for room_code, room in list(game.rooms.items()):
                # Get all users in room (players + spectators)
                user_ids_in_room = set()
                for p_id, player_obj in room.players.items():
                    if not player_obj.is_ai and player_obj.connection_id:
                        user_ids_in_room.add(player_obj.connection_id)
                user_ids_in_room.update(room.spectators)

                # Prepare broadcasts for each user
                valid_connections = []
                for user_id in list(user_ids_in_room):
                    ws_conn = game.connections.get(user_id)
                    if ws_conn:
                        try:
                            game_state = game.get_game_state(room_code, user_id)
                            if "error" not in game_state:
                                valid_connections.append((user_id, ws_conn, game_state))
                        except Exception as e:
                            logger.error(f"Error preparing game_state for user {user_id}: {e}")
                            # Clean up failed connection
                            if user_id in game.connections:
                                del game.connections[user_id]
                            game.leave_room(user_id, force=True)
                    else:
                        # Connection lost, clean up
                        game.leave_room(user_id, force=True)

                # Queue broadcasts
                for user_id, ws_conn, game_state in valid_connections:
                    try:
                        broadcast_tasks.append(
                            ws_conn.send_json({"type": "game_state", "data": game_state})
                        )
                    except Exception as e:
                        logger.error(f"Error queueing broadcast for {user_id}: {e}")

            # Execute all broadcasts concurrently
            if broadcast_tasks:
                results = await asyncio.gather(*broadcast_tasks, return_exceptions=True)
                
                # Log any broadcast failures
                failed_count = sum(1 for result in results if isinstance(result, Exception))
                if failed_count > 0:
                    logger.warning(f"Failed to broadcast to {failed_count}/{len(broadcast_tasks)} connections")

            # Run at 10 FPS for good responsiveness without overwhelming the system
            await asyncio.sleep(0.1)

        except Exception as e:
            logger.exception(f"Critical error in game_loop: {e}")
            await asyncio.sleep(1.0)  # Longer delay on error

    logger.info("🎮 Game loop stopped")

# WebSocket Message Handler
async def handle_websocket_message(websocket: WebSocket, player_id: str, message: WSMessage):
    """Handle incoming WebSocket messages"""
    action = message.action
    payload = message.payload
    
    try:
        if action == "create_room":
            try:
                create_payload = CreateRoomPayload(**payload)
            except ValidationError as e:
                await websocket.send_json({"type": "error", "message": f"Invalid data: {e.errors()[0]['msg']}"})
                return

            room_code = game.create_room(player_id, create_payload.room_name)
            if not room_code:
                await websocket.send_json({"type": "error", "message": "Failed to create room (server full)"})
                return

            if game.join_room(room_code, player_id, create_payload.player_name):
                await websocket.send_json({"type": "room_created", "data": {"room_code": room_code}})
            else:
                await websocket.send_json({"type": "error", "message": "Failed to join created room"})

        elif action == "join_room":
            try:
                join_payload = JoinRoomPayload(**payload)
            except ValidationError as e:
                await websocket.send_json({"type": "error", "message": f"Invalid data: {e.errors()[0]['msg']}"})
                return

            if game.join_room(join_payload.room_code, player_id, join_payload.player_name):
                await websocket.send_json({"type": "room_joined", "data": {"room_code": join_payload.room_code}})
            else:
                await websocket.send_json({"type": "error", "message": "Failed to join room (not found or full)"})

        elif action == "spectate_room":
            room_code = payload.get("room_code", "").upper()
            if not room_code or len(room_code) != 6:
                await websocket.send_json({"type": "error", "message": "Invalid room code"})
                return
            
            room = game.rooms.get(room_code)
            if room:
                room.spectators.add(player_id)
                game.player_rooms[player_id] = room_code
                await websocket.send_json({"type": "spectating", "data": {"room_code": room_code}})
            else:
                await websocket.send_json({"type": "error", "message": "Room not found"})

        elif action == "leave_room":
            game.leave_room(player_id)
            await websocket.send_json({"type": "room_left"})

        elif action == "start_game":
            room_code = game.player_rooms.get(player_id)
            if not room_code:
                await websocket.send_json({"type": "error", "message": "Not in a room"})
                return
            
            room = game.rooms.get(room_code)
            if room and room.owner_id == player_id:
                if game.start_game(room_code):
                    logger.info(f"Game started in room {room_code} by {player_id}")
                else:
                    await websocket.send_json({"type": "error", "message": "Cannot start game (no bets placed or game in progress)"})
            else:
                await websocket.send_json({"type": "error", "message": "Only room owner can start game"})

        elif action == "player_action":
            if not game.check_rate_limit(player_id, "action"):
                await websocket.send_json({"type": "error", "message": "Action rate limit exceeded"})
                return
            
            try:
                action_payload = PlayerActionPayload(**payload)
            except ValidationError as e:
                await websocket.send_json({"type": "error", "message": f"Invalid action data: {e.errors()[0]['msg']}"})
                return
            
            room_code = game.player_rooms.get(player_id)
            if not room_code:
                await websocket.send_json({"type": "error", "message": "Not in a room"})
                return

            try:
                blackjack_action = PlayerAction(action_payload.action_type)
                if not game.player_action(room_code, player_id, blackjack_action, action_payload.amount or 0):
                    await websocket.send_json({"type": "error", "message": "Invalid action or not your turn"})
            except ValueError:
                await websocket.send_json({"type": "error", "message": f"Unknown action: {action_payload.action_type}"})

        elif action == "send_chat_message":
            if not game.check_rate_limit(player_id, "message"):
                await websocket.send_json({"type": "error", "message": "Chat rate limit exceeded"})
                return
            
            try:
                chat_payload = ChatMessagePayload(**payload)
            except ValidationError as e:
                await websocket.send_json({"type": "error", "message": f"Invalid message: {e.errors()[0]['msg']}"})
                return
            
            room_code = game.player_rooms.get(player_id)
            if not room_code:
                await websocket.send_json({"type": "error", "message": "Must be in a room to chat"})
                return

            if not game.add_chat_message(room_code, player_id, chat_payload.message):
                await websocket.send_json({"type": "error", "message": "Message rejected"})

        elif action == "get_room_list":
            public_rooms = []
            for r_code, r_obj in game.rooms.items():
                if r_obj.is_public and r_obj.phase in [GamePhase.WAITING, GamePhase.GAME_OVER]:
                    human_players = r_obj.get_player_count()
                    public_rooms.append({
                        "code": r_code,
                        "name": r_obj.name,
                        "players": human_players,
                        "max_players": r_obj.max_players,
                        "phase": r_obj.phase.value,
                        "created": r_obj.created_at.strftime("%H:%M")
                    })
            
            # Sort by creation time (newest first)
            public_rooms.sort(key=lambda x: x["created"], reverse=True)
            await websocket.send_json({"type": "room_list", "data": {"rooms": public_rooms[:20]}})

        elif action == "ping":
            # Handle heartbeat/ping
            await websocket.send_json({"type": "pong", "data": {"timestamp": time.time()}})

        else:
            await websocket.send_json({"type": "error", "message": f"Unknown action: {action}"})

    except WebSocketDisconnect:
        raise  # Re-raise to be handled by the WebSocket endpoint
    except Exception as e:
        logger.exception(f"Error handling message from {player_id}: {e}")
        try:
            await websocket.send_json({"type": "error", "message": "Server error occurred"})
        except Exception:
            pass  # Connection might be closed

# FastAPI Application Setup
@asynccontextmanager
async def lifespan(app_instance: FastAPI):
    """Application lifespan handler"""
    logger.info("🚀 Starting Royal Blackjack 3D server...")
    
    # Start the game loop
    game_task = asyncio.create_task(game_loop())
    
    try:
        yield
    finally:
        # Shutdown sequence
        logger.info("🛑 Shutting down Royal Blackjack 3D server...")
        game.running = False
        
        # Wait for game loop to finish gracefully
        try:
            await asyncio.wait_for(game_task, timeout=5.0)
        except asyncio.TimeoutError:
            logger.warning("Game loop did not shut down gracefully, forcing termination")
            game_task.cancel()
            try:
                await game_task
            except asyncio.CancelledError:
                pass

# Create FastAPI application
app = FastAPI(
    title="Royal Blackjack 3D",
    description="Professional 3D Multiplayer Blackjack Casino Experience",
    version="1.0.0",
    lifespan=lifespan
)

# Add CORS middleware for cross-origin requests
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],  # In production, specify actual origins
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# Serve static files if directory exists
if os.path.exists("static"):
    app.mount("/static", StaticFiles(directory="static"), name="static")

# HTTP Routes
@app.get("/", response_class=HTMLResponse)
async def get_root():
    """Serve the main game interface"""
    if os.path.exists("index.html"):
        return FileResponse("index.html")
    else:
        return HTMLResponse(
            content="""
            <!DOCTYPE html>
            <html>
                <head>
                    <title>Royal Blackjack 3D</title>
                    <style>
                        body { 
                            background: linear-gradient(135deg, #0a2a1f, #051a11); 
                            color: #fff; 
                            font-family: Arial, sans-serif; 
                            text-align: center; 
                            padding: 50px;
                            margin: 0;
                            min-height: 100vh;
                            display: flex;
                            flex-direction: column;
                            justify-content: center;
                        }
                        h1 { color: #ffd700; font-size: 3rem; margin-bottom: 20px; }
                        p { font-size: 1.2rem; margin: 10px 0; }
                        .status { color: #4ecdc4; }
                        .instruction { background: rgba(255,255,255,0.1); padding: 20px; border-radius: 10px; margin: 20px 0; }
                    </style>
                </head>
                <body>
                    <h1>🃏 Royal Blackjack 3D 🃏</h1>
                    <p class="status">✅ Server is running successfully!</p>
                    <div class="instruction">
                        <h3>Setup Instructions:</h3>
                        <p>1. Save your HTML file as <strong>'index.html'</strong> in the same directory as this server</p>
                        <p>2. Refresh this page once the file is in place</p>
                        <p>3. Enjoy your professional blackjack experience!</p>
                    </div>
                    <p><strong>WebSocket URL:</strong> ws://localhost:8000/ws</p>
                </body>
            </html>
            """,
            status_code=200  # Server is working, just missing the HTML file
        )

@app.get("/health")
async def health_check():
    """Health check endpoint for monitoring"""
    stats = game.get_server_stats()
    return stats

@app.get("/stats")
async def get_detailed_stats():
    """Get detailed server statistics"""
    stats = game.get_server_stats()
    
    # Add room details
    room_details = []
    for room_code, room in game.rooms.items():
        room_details.append({
            "code": room_code,
            "name": room.name,
            "phase": room.phase.value,
            "players": room.get_player_count(),
            "spectators": len(room.spectators),
            "hand_number": room.hand_number,
            "created": room.created_at.isoformat(),
            "last_activity": room.last_activity.isoformat(),
            "is_public": room.is_public,
            "owner_id": room.owner_id[:8] + "..." if room.owner_id else None
        })
    
    return {
        **stats,
        "rooms": room_details,
        "connection_count": len(game.connections)
    }

@app.get("/api/rooms")
async def get_public_rooms():
    """Get list of public rooms (REST endpoint)"""
    public_rooms = []
    for r_code, r_obj in game.rooms.items():
        if r_obj.is_public:
            public_rooms.append({
                "code": r_code,
                "name": r_obj.name,
                "players": r_obj.get_player_count(),
                "max_players": r_obj.max_players,
                "phase": r_obj.phase.value,
                "created": r_obj.created_at.isoformat()
            })
    
    return {"rooms": public_rooms}

# WebSocket Endpoint
@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    """Main WebSocket endpoint for game communication"""
    player_id = str(uuid.uuid4())
    client_ip = websocket.client.host if websocket.client else "unknown"
    logger.info(f"🔌 New WebSocket connection: {player_id} from {client_ip}")
    
    try:
        await websocket.accept()
        game.connections[player_id] = websocket
        
        # Send welcome message with connection info
        await websocket.send_json({
            "type": "connected",
            "data": {
                "player_id": player_id,
                "message": "Welcome to Royal Blackjack 3D!",
                "server_version": "1.0.0",
                "timestamp": time.time()
            }
        })

        # Main message handling loop
        while True:
            try:
                # Receive message from client
                data = await websocket.receive_text()
                message_data = json.loads(data)
                
                if not isinstance(message_data, dict) or "action" not in message_data:
                    raise ValueError("Invalid message format")
                
                ws_message = WSMessage(**message_data)
                await handle_websocket_message(websocket, player_id, ws_message)
                
            except json.JSONDecodeError:
                await websocket.send_json({"type": "error", "message": "Invalid JSON format"})
            except ValidationError as e:
                await websocket.send_json({
                    "type": "error", 
                    "message": f"Invalid message format: {e.errors()[0]['msg']}"
                })
            except ValueError as e:
                await websocket.send_json({"type": "error", "message": str(e)})

    except WebSocketDisconnect:
        logger.info(f"🔌 WebSocket {player_id} disconnected normally")
    except Exception as e:
        logger.exception(f"🔌 WebSocket error for {player_id}: {e}")
    finally:
        # Cleanup on disconnect
        if player_id in game.connections:
            del game.connections[player_id]
        game.leave_room(player_id, force=True)
        logger.info(f"🔌 Cleaned up connection for {player_id}")

# Development/Production Server Entry Point
if __name__ == "__main__":
    # Configuration from environment variables
    port = int(os.environ.get("PORT", 8000))
    host = os.environ.get("HOST", "0.0.0.0")
    debug = os.environ.get("DEBUG", "false").lower() == "true"
    
    # Log startup information
    logger.info("=" * 60)
    logger.info("🎰 ROYAL BLACKJACK 3D SERVER")
    logger.info("=" * 60)
    logger.info(f"🚀 Starting server on {host}:{port}")
    logger.info(f"🎯 Debug mode: {debug}")
    logger.info(f"📁 Working directory: {os.getcwd()}")
    logger.info(f"🎮 Max rooms: {MAX_ROOMS}")
    logger.info(f"👥 Max players per room: {MAX_PLAYERS_PER_ROOM}")
    logger.info(f"💰 Starting money: ${STARTING_MONEY}")
    logger.info("=" * 60)
    
    # Run the server
    try:
        uvicorn.run(
            "app:app" if __name__ == "__main__" else app,
            host=host,
            port=port,
            reload=debug,
            log_level="info" if not debug else "debug",
            access_log=True,
            ws_ping_interval=20,
            ws_ping_timeout=10
        )
    except KeyboardInterrupt:
        logger.info("🛑 Server stopped by user")
    except Exception as e:
        logger.exception(f"💥 Server startup failed: {e}")
        exit(1)
