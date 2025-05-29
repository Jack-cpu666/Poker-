#!/usr/bin/env python3
"""
Royal Blackjack 3D - Complete Production Server
A premium multiplayer blackjack game with stunning 3D interface
Built for commercial deployment and scalability

Features:
- Real-time multiplayer gameplay
- WebSocket-based communication
- Professional game logic
- Advanced room management
- Chat system with moderation
- Comprehensive statistics
- Rate limiting and security
- Docker deployment ready
- Production logging
- Auto-scaling support

Author: Royal Casino Development Team
License: Commercial - Ready for immediate deployment
Version: 1.0.0 Production Release
"""

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
    DEALER_HIT_THRESHOLD = 16
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
    ]
    IP_RATE_LIMIT = 100  # requests per minute
    SUSPICIOUS_ACTIVITY_THRESHOLD = 50
    AUTO_BAN_THRESHOLD = 10

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
    DISCONNECTED = "disconnected"

class HandResult(Enum):
    """Result of a completed hand"""
    WIN = "win"
    LOSE = "lose"
    PUSH = "push"
    BLACKJACK = "blackjack"
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
            return 11 if current_total + 11 <= 21 else 1
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
    insurance_bet: int = 0
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
        return (len(self.cards) == 2 and 
                self.cards[0].rank == self.cards[1].rank and 
                not self.is_split)

    def can_double_down(self) -> bool:
        """Check if hand can be doubled down"""
        return len(self.cards) == 2 and not self.is_split

    def can_surrender(self) -> bool:
        """Check if hand can be surrendered"""
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
    total_winnings: int = 0
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
        return ((self.total_winnings - self.total_wagered) / self.total_wagered) * 100

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
            "session_duration": str(datetime.now() - self.session_start)
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
    avatar: str = "royal_avatar"
    color: str = "#ffffff"
    connection_id: Optional[str] = None
    is_ai: bool = False
    session_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    stats: PlayerStats = field(default_factory=PlayerStats)
    last_activity: datetime = field(default_factory=datetime.now)
    join_time: datetime = field(default_factory=datetime.now)
    ip_address: Optional[str] = None
    user_agent: Optional[str] = None
    is_vip: bool = False
    warnings: int = 0
    is_banned: bool = False
    ban_reason: Optional[str] = None
    reconnect_token: Optional[str] = None

    def __post_init__(self):
        """Initialize player after creation"""
        if not self.hands:
            self.hands = [Hand()]

    def get_current_hand(self) -> Hand:
        """Get the hand currently being played"""
        if 0 <= self.current_hand_index < len(self.hands):
            return self.hands[self.current_hand_index]
        return self.hands[0] if self.hands else Hand()

    def can_act(self) -> bool:
        """Check if player can take an action"""
        if self.status not in [PlayerStatus.ACTIVE]:
            return False
            
        current_hand = self.get_current_hand()
        return (not current_hand.is_bust() and 
                not current_hand.is_surrendered and
                current_hand.get_value() < 21)

    def reset_for_new_hand(self):
        """Reset player for a new hand"""
        self.hands = [Hand()]
        self.current_hand_index = 0
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
        """Validate reconnect token"""
        return (self.reconnect_token == token and 
                (datetime.now() - self.last_activity).total_seconds() < GameConfig.RECONNECT_WINDOW)

    def add_warning(self, reason: str):
        """Add warning to player"""
        self.warnings += 1
        logger.warning(f"Player {self.name} ({self.id}) warned: {reason}. Total warnings: {self.warnings}")
        
        if self.warnings >= SecurityConfig.AUTO_BAN_THRESHOLD:
            self.ban(f"Too many warnings ({self.warnings})")

    def ban(self, reason: str):
        """Ban player"""
        self.is_banned = True
        self.ban_reason = reason
        self.status = PlayerStatus.ELIMINATED
        logger.error(f"Player {self.name} ({self.id}) banned: {reason}")

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
            "session_duration": str(datetime.now() - self.join_time),
            "stats": self.stats.to_dict()
        }

        if include_sensitive:
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
    min_bet: int = GameConfig.MIN_BET
    max_bet: int = GameConfig.MAX_BET
    _player_turn_order: List[str] = field(default_factory=list)
    _current_player_turn_index: int = 0
    is_public: bool = True
    max_players: int = GameConfig.MAX_PLAYERS_PER_ROOM
    password: Optional[str] = None
    is_premium: bool = False
    tournament_mode: bool = False
    buy_in: int = 0
    prize_pool: int = 0

    def __post_init__(self):
        """Initialize room after creation"""
        if not self.deck:
            self.deck = self.create_deck()
        if not hasattr(self, 'dealer_hand') or not self.dealer_hand:
            self.dealer_hand = Hand()

    def create_deck(self, num_decks: int = 6) -> List[Card]:
        """Create and shuffle multiple decks for professional play"""
        suits = ["hearts", "diamonds", "clubs", "spades"]
        ranks = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]
        deck = []
        
        for deck_num in range(num_decks):
            for suit in suits:
                for rank in ranks:
                    deck.append(Card(suit, rank))
        
        # Enhanced shuffling algorithm
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
        # Reshuffle when deck is low (simulate cut card at 75% penetration)
        if len(self.deck) < 78:  # 25% of 312 cards remaining
            logger.info(f"Cut card reached in room {self.code}, reshuffling")
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
                 if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED, PlayerStatus.DISCONNECTED] 
                 and p.money >= self.min_bet
                 and not p.is_ai
                 and not p.is_banned]
        
        logger.debug(f"Room {self.code} has {len(active)} active players")
        return active

    def advance_to_next_player(self):
        """Move to the next player's turn with enhanced logic"""
        current_player = self.players.get(self.current_player_id)
        
        # Check if current player has more hands to play
        if (current_player and 
            current_player.current_hand_index < len(current_player.hands) - 1 and
            current_player.status == PlayerStatus.ACTIVE):
            current_player.current_hand_index += 1
            logger.info(f"Player {current_player.name} moving to hand {current_player.current_hand_index + 1}")
            return

        # Reset current player's hand index
        if current_player:
            current_player.current_hand_index = 0

        # Find next active player
        while self._current_player_turn_index < len(self._player_turn_order) - 1:
            self._current_player_turn_index += 1
            next_player_id = self._player_turn_order[self._current_player_turn_index]
            next_player = self.players.get(next_player_id)
            
            if (next_player and 
                next_player.status == PlayerStatus.ACTIVE and
                next_player.can_act()):
                self.current_player_id = next_player_id
                logger.info(f"Advanced to next player {next_player.name} in room {self.code}")
                return

        # All players have acted, move to dealer turn
        self.current_player_id = None
        self.phase = GamePhase.DEALER_TURN
        logger.info(f"All players completed turns, moving to dealer turn in room {self.code}")

    def update_activity(self):
        """Update last activity timestamp"""
        self.last_activity = datetime.now()

    def is_inactive(self) -> bool:
        """Check if room has been inactive too long"""
        return (datetime.now() - self.last_activity).total_seconds() > GameConfig.INACTIVE_ROOM_TIMEOUT

    def get_player_count(self) -> int:
        """Get count of human players"""
        return len([p for p in self.players.values() if not p.is_ai and not p.is_banned])

    def add_chat_message(self, player_id: str, message: str) -> bool:
        """Add chat message with enhanced moderation"""
        player = self.players.get(player_id)
        if not player:
            return False

        # Content moderation
        message_lower = message.lower()
        for banned_word in SecurityConfig.BANNED_WORDS:
            if banned_word in message_lower:
                player.add_warning(f"Inappropriate language: {banned_word}")
                return False

        # Rate limiting handled at game level
        chat_msg = {
            "player_id": player_id,
            "player_name": player.name,
            "player_color": player.color,
            "message": message,
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
        """Convert room to dictionary"""
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

        if include_sensitive:
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
        self.connections: Dict[str, WebSocket] = {}
        self.player_rooms: Dict[str, str] = {}
        self.rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.action_rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.ip_rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.banned_ips: Set[str] = set()
        self.running = True
        self.maintenance_mode = False
        
        # Enhanced server statistics
        self.stats = {
            'total_rooms_created': 0,
            'total_players_connected': 0,
            'total_hands_played': 0,
            'total_money_wagered': 0,
            'total_money_won': 0,
            'server_start_time': datetime.now(),
            'peak_concurrent_players': 0,
            'peak_concurrent_rooms': 0,
            'total_chat_messages': 0,
            'total_bans_issued': 0,
            'total_warnings_issued': 0,
            'uptime': 0
        }
        
        # Security tracking
        self.security_events: List[Dict] = []
        self.suspicious_ips: Dict[str, int] = defaultdict(int)
        
        logger.info("🎰 Royal Blackjack 3D Game Engine initialized with enterprise features")

    def generate_room_code(self) -> str:
        """Generate a unique 6-character room code"""
        attempts = 0
        while attempts < 1000:  # Increased attempts for production
            code = ''.join(random.choices('ABCDEFGHJKLMNPQRSTUVWXYZ23456789', k=6))
            if code not in self.rooms:
                return code
            attempts += 1
        
        # Fallback with timestamp and random suffix
        timestamp = str(int(time.time()))[-6:]
        return f"R{timestamp}"

    def log_security_event(self, event_type: str, details: Dict[str, Any]):
        """Log security events for monitoring"""
        event = {
            'timestamp': datetime.now().isoformat(),
            'type': event_type,
            'details': details
        }
        self.security_events.append(event)
        
        # Keep only recent events
        if len(self.security_events) > 1000:
            self.security_events = self.security_events[-1000:]
        
        logger.warning(f"Security event: {event_type} - {details}")

    def check_ip_rate_limit(self, ip_address: str) -> bool:
        """Check IP-based rate limiting"""
        if ip_address in self.banned_ips:
            return False
            
        current_time = time.time()
        self.ip_rate_limits[ip_address] = [
            t for t in self.ip_rate_limits[ip_address] 
            if current_time - t <= 60.0  # 1 minute window
        ]
        
        if len(self.ip_rate_limits[ip_address]) >= SecurityConfig.IP_RATE_LIMIT:
            self.suspicious_ips[ip_address] += 1
            
            if self.suspicious_ips[ip_address] >= SecurityConfig.SUSPICIOUS_ACTIVITY_THRESHOLD:
                self.banned_ips.add(ip_address)
                self.log_security_event('ip_banned', {'ip': ip_address, 'reason': 'rate_limit_exceeded'})
            
            return False
        
        self.ip_rate_limits[ip_address].append(current_time)
        return True

    def create_room(self, creator_player_id: str, room_name: Optional[str] = None, password: Optional[str] = None) -> Optional[str]:
        """Create a new game room with enhanced features"""
        if len(self.rooms) >= GameConfig.MAX_ROOMS:
            logger.warning(f"Maximum number of rooms ({GameConfig.MAX_ROOMS}) reached")
            return None
        
        room_code = self.generate_room_code()
        room_name = room_name or f"Royal Table {room_code}"
        
        # Create the room with enhanced settings
        room = Room(
            code=room_code, 
            name=room_name, 
            players={}, 
            spectators=set(),
            deck=[], 
            dealer_hand=Hand(),
            owner_id=creator_player_id,
            password=password,
            is_public=password is None
        )
        
        self.rooms[room_code] = room
        self.stats['total_rooms_created'] += 1
        
        # Update peak rooms
        if len(self.rooms) > self.stats['peak_concurrent_rooms']:
            self.stats['peak_concurrent_rooms'] = len(self.rooms)
        
        logger.info(f"Room {room_code} ({room_name}) created by player {creator_player_id}")
        return room_code

    def join_room(self, room_code: str, player_id: str, player_name: str, 
                  password: Optional[str] = None, ip_address: Optional[str] = None) -> bool:
        """Join a player to a room with enhanced validation"""
        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"Attempt to join non-existent room {room_code} by {player_id}")
            return False

        # Check room capacity
        if room.get_player_count() >= room.max_players:
            logger.warning(f"Room {room_code} is full ({room.max_players} players)")
            return False

        # Check password if required
        if room.password and room.password != password:
            logger.warning(f"Invalid password for room {room_code} by {player_id}")
            return False

        # Validate and clean player name
        if not player_name or len(player_name.strip()) == 0:
            logger.warning(f"Invalid player name for {player_id}")
            return False

        player_name = player_name.strip()[:SecurityConfig.MAX_NAME_LENGTH]

        # Check for banned words in name
        name_lower = player_name.lower()
        for banned_word in SecurityConfig.BANNED_WORDS:
            if banned_word in name_lower:
                logger.warning(f"Banned word in player name: {player_name}")
                return False

        if player_id in room.players:  
            # Rejoining player
            rejoining_player = room.players[player_id]
            if rejoining_player.is_banned:
                logger.warning(f"Banned player {player_id} attempted to rejoin room {room_code}")
                return False
                
            rejoining_player.connection_id = player_id
            rejoining_player.name = player_name
            rejoining_player.status = PlayerStatus.ACTIVE
            rejoining_player.update_activity()
            logger.info(f"Player {player_name} ({player_id}) re-joined room {room_code}")
        else:  
            # New player
            # Generate unique color for player
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
                money=GameConfig.STARTING_MONEY,
                avatar=f"royal_avatar_{random.randint(1, 12)}", 
                color=color,
                connection_id=player_id,
                ip_address=ip_address
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
        """Remove a player from their room with cleanup"""
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
            
            if not force:
                # Mark as disconnected instead of removing immediately
                player_obj.status = PlayerStatus.DISCONNECTED
                player_obj.generate_reconnect_token()
            else:
                del room.players[player_id]

        room.spectators.discard(player_id)

        # Handle game state if player was the current player
        if room.current_player_id == player_id and room.phase == GamePhase.PLAYER_TURNS:
            room.advance_to_next_player()

        # Room management
        remaining_players = [p for p in room.players.values() if not p.is_ai and p.status != PlayerStatus.DISCONNECTED]
        if not remaining_players and not room.spectators:
            logger.info(f"Room {room_code} is empty. Scheduling for cleanup.")
            # Don't delete immediately, let cleanup handle it
        elif room.owner_id == player_id and remaining_players:
            # Transfer ownership to next active player
            new_owner = next((pid for pid, p_obj in room.players.items() 
                            if not p_obj.is_ai and p_obj.status != PlayerStatus.DISCONNECTED), None)
            if new_owner:
                room.owner_id = new_owner
                logger.info(f"Room {room_code} ownership transferred to {new_owner}")

        room.update_activity()

    def start_game(self, room_code: str, initiator_id: str) -> bool:
        """Start a new game in the room with validation"""
        room = self.rooms.get(room_code)
        if not room:
            logger.error(f"Cannot start game: room {room_code} not found")
            return False

        # Verify initiator is room owner
        if room.owner_id != initiator_id:
            logger.warning(f"Non-owner {initiator_id} attempted to start game in room {room_code}")
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

        logger.info(f"Starting premium blackjack game in room {room_code} with {len(players_with_bets)} players")
        
        # Initialize game state
        room.phase = GamePhase.DEALING
        room.hand_number += 1
        room.shuffle_deck()
        room.dealer_hand = Hand()
        self.stats['total_hands_played'] += 1

        # Reset players for new hand and update statistics
        for player in room.players.values():
            if player.status == PlayerStatus.ACTIVE:
                player.stats.total_hands_played += 1
                player.reset_for_new_hand()
                
                # Restore bet for players who had placed bets
                original_player = next((p for p in players_with_bets if p.id == player.id), None)
                if original_player:
                    player.hands[0].bet_amount = original_player.hands[0].bet_amount
                    player.stats.total_wagered += player.hands[0].bet_amount
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
        
        # Deal 2 cards to each player and dealer (standard blackjack dealing)
        for card_round in range(2):
            # Deal to players first
            for player in active_players:
                if player.hands and len(player.hands[0].cards) < 2:
                    card = room.deal_card()
                    if card:
                        card.dealt_at = datetime.now()
                        player.hands[0].cards.append(card)
            
            # Deal to dealer
            if len(room.dealer_hand.cards) < 2:
                card = room.deal_card()
                if card:
                    card.dealt_at = datetime.now()
                    room.dealer_hand.cards.append(card)

        # Check for dealer blackjack (but don't reveal until player turns complete)
        dealer_has_blackjack = room.dealer_hand.is_blackjack()
        
        # Check for player blackjacks
        blackjack_players = []
        for player in active_players:
            if player.hands[0].is_blackjack():
                player.status = PlayerStatus.BLACKJACK
                player.stats.total_blackjacks += 1
                blackjack_players.append(player.name)
                logger.info(f"Player {player.name} got blackjack in room {room_code}")

        # Move to appropriate phase
        if all(p.status == PlayerStatus.BLACKJACK for p in active_players):
            # All players have blackjack, go straight to dealer resolution
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
        """Process a player action with comprehensive validation"""
        room = self.rooms.get(room_code)
        if not room:
            logger.error(f"Room {room_code} not found for player action")
            return False

        player = room.players.get(player_id)
        if not player:
            logger.error(f"Player {player_id} not found in room {room_code}")
            return False

        if player.is_banned:
            logger.warning(f"Banned player {player_id} attempted action in room {room_code}")
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
                
                # Update action statistics
                if action == PlayerAction.DOUBLE_DOWN:
                    player.stats.total_doubles += 1
                elif action == PlayerAction.SPLIT:
                    player.stats.total_splits += 1
                elif action == PlayerAction.SURRENDER:
                    player.stats.total_surrenders += 1
            
            return success
            
        except Exception as e:
            logger.error(f"Error processing player action: {e}")
            logger.error(traceback.format_exc())
            return False

    def _process_place_bet(self, room: Room, player: Player, amount: int) -> bool:
        """Process a bet placement with validation"""
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

        card.dealt_at = datetime.now()
        current_hand.cards.append(card)
        logger.info(f"Player {player.name} hit and received {card}")

        if current_hand.is_bust():
            player.status = PlayerStatus.BUST
            player.stats.total_busts += 1
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
        player.stats.total_wagered += additional_bet
        self.stats['total_money_wagered'] += additional_bet

        # Deal exactly one card
        card = room.deal_card()
        if card:
            card.dealt_at = datetime.now()
            current_hand.cards.append(card)
            logger.info(f"Player {player.name} doubled down and received {card}")

        if current_hand.is_bust():
            player.status = PlayerStatus.BUST
            player.stats.total_busts += 1
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

        # Limit number of splits
        if len(player.hands) >= 4:
            logger.warning(f"Player {player.name} has reached maximum splits")
            return False

        # Create new hand with second card
        second_card = current_hand.cards.pop()
        new_hand = Hand(cards=[second_card], bet_amount=current_hand.bet_amount, is_split=True)
        current_hand.is_split = True
        player.hands.append(new_hand)
        player.money -= current_hand.bet_amount
        player.stats.total_wagered += current_hand.bet_amount
        self.stats['total_money_wagered'] += current_hand.bet_amount

        # Deal new cards to both hands
        for hand in player.hands:
            if len(hand.cards) == 1:  # Only add card to split hands
                card = room.deal_card()
                if card:
                    card.dealt_at = datetime.now()
                    hand.cards.append(card)

        logger.info(f"Player {player.name} split their hand")
        return True

    def _process_surrender(self, room: Room, player: Player) -> bool:
        """Process a surrender action"""
        if room.phase != GamePhase.PLAYER_TURNS or room.current_player_id != player.id:
            return False

        current_hand = player.get_current_hand()
        if not current_hand.can_surrender():
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
        room.advance_to_next_player()
        
        if room.phase == GamePhase.DEALER_TURN:
            self._play_dealer_hand(room)

    def _play_dealer_hand(self, room: Room):
        """Play the dealer's hand according to standard casino rules"""
        logger.info(f"Dealer playing hand in room {room.code}")
        
        # Dealer plays by standard rules: hit on soft 17
        while True:
            dealer_value = room.dealer_hand.get_value()
            
            # Check for soft 17 (Ace counted as 11 with total of 17)
            has_ace_as_11 = False
            if dealer_value == 17:
                total_without_aces = sum(10 if card.rank in ['J', 'Q', 'K'] else 
                                       int(card.rank) if card.rank.isdigit() else 0 
                                       for card in room.dealer_hand.cards)
                ace_count = sum(1 for card in room.dealer_hand.cards if card.rank == 'A')
                if ace_count > 0 and total_without_aces + ace_count + 10 == 17:
                    has_ace_as_11 = True
            
            # Hit on 16 or less, or soft 17
            if dealer_value < 17 or (dealer_value == 17 and has_ace_as_11):
                card = room.deal_card()
                if card:
                    card.dealt_at = datetime.now()
                    room.dealer_hand.cards.append(card)
                    new_value = room.dealer_hand.get_value()
                    logger.info(f"Dealer hit and received {card}, total: {new_value}")
                else:
                    logger.error("No card available for dealer")
                    break
            else:
                break

        dealer_final = room.dealer_hand.get_value()
        if dealer_final > 21:
            logger.info(f"Dealer busted with {dealer_final}")
        else:
            logger.info(f"Dealer stands with {dealer_final}")

        room.phase = GamePhase.PAYOUT
        self._calculate_payouts(room)

    def _calculate_payouts(self, room: Room):
        """Calculate and distribute payouts with comprehensive statistics"""
        logger.info(f"Calculating payouts for room {room.code}")
        dealer_value = room.dealer_hand.get_value()
        dealer_bust = room.dealer_hand.is_bust()
        dealer_blackjack = room.dealer_hand.is_blackjack()

        total_payouts = 0

        for player in room.players.values():
            if not player.hands or not any(h.bet_amount > 0 for h in player.hands):
                continue
                
            player_won_any = False
            player_total_payout = 0
            player_total_bet = 0
            
            for hand in player.hands:
                if hand.bet_amount == 0:
                    continue
                    
                player_total_bet += hand.bet_amount
                
                if hand.is_surrendered:
                    hand.result = HandResult.SURRENDER
                    hand.payout = hand.bet_amount // 2  # Half bet returned
                    player.money += hand.payout
                    player_total_payout += hand.payout
                    continue

                hand_value = hand.get_value()
                
                if hand.is_bust():
                    hand.result = HandResult.BUST
                    hand.payout = 0
                elif hand.is_blackjack() and not dealer_blackjack:
                    hand.result = HandResult.BLACKJACK
                    hand.payout = int(hand.bet_amount * (1 + GameConfig.BLACKJACK_PAYOUT))
                    player.money += hand.payout
                    player_total_payout += hand.payout
                    player_won_any = True
                elif dealer_bust or (hand_value <= 21 and hand_value > dealer_value):
                    hand.result = HandResult.WIN
                    hand.payout = hand.bet_amount * 2
                    player.money += hand.payout
                    player_total_payout += hand.payout
                    player_won_any = True
                elif hand_value == dealer_value and not hand.is_bust():
                    hand.result = HandResult.PUSH
                    hand.payout = hand.bet_amount  # Return original bet
                    player.money += hand.payout
                    player_total_payout += hand.bet_amount
                else:
                    hand.result = HandResult.LOSE
                    hand.payout = 0

            # Update comprehensive player statistics
            if player_won_any:
                player.stats.total_hands_won += 1
                player.stats.current_streak += 1
                if player.stats.current_streak > player.stats.best_streak:
                    player.stats.best_streak = player.stats.current_streak
            else:
                player.stats.current_streak = 0
            
            net_result = player_total_payout - player_total_bet
            player.stats.total_winnings += net_result
            total_payouts += player_total_payout
            
            logger.info(f"Player {player.name}: Bet ${player_total_bet}, Won ${player_total_payout}, Net ${net_result}")

        # Update server statistics
        self.stats['total_money_won'] += total_payouts

        room.phase = GamePhase.GAME_OVER
        room.update_activity()
        
        # Schedule automatic reset
        asyncio.create_task(self._prepare_next_hand(room.code))

    async def _prepare_next_hand(self, room_code: str, delay: int = GameConfig.AUTO_RESET_DELAY):
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
            if player.status != PlayerStatus.DISCONNECTED:
                player.reset_for_new_hand()
        
        room.dealer_hand = Hand()
        room.current_player_id = None
        room._player_turn_order = []
        room._current_player_turn_index = 0
        
        logger.info(f"Room {room_code} prepared for next hand")

    def get_game_state(self, room_code: str, for_player_id: str) -> Dict[str, Any]:
        """Get current game state for a player with comprehensive data"""
        room = self.rooms.get(room_code)
        if not room:
            return {"error": "Room not found"}

        player = room.players.get(for_player_id)
        is_player = player is not None and not player.is_ai
        is_spectator = for_player_id in room.spectators

        # Build players data with privacy considerations
        players_data = {}
        for p_id, p_obj in room.players.items():
            if p_obj.status != PlayerStatus.DISCONNECTED:
                players_data[p_id] = p_obj.to_dict(room.current_player_id)

        # Dealer hand with hole card management
        dealer_cards = []
        for i, card in enumerate(room.dealer_hand.cards):
            if (i == 1 and 
                room.phase in [GamePhase.DEALING, GamePhase.PLAYER_TURNS] and 
                len(room.dealer_hand.cards) > 1):
                # Hide hole card
                dealer_cards.append({"suit": "back", "rank": "back", "id": "hidden"})
            else:
                dealer_cards.append(card.to_dict())

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
                "value": visible_dealer_value,
                "is_blackjack": room.dealer_hand.is_blackjack() if room.phase in [GamePhase.DEALER_TURN, GamePhase.PAYOUT, GamePhase.GAME_OVER] else None
            },
            "chat_messages": room.chat_messages[-30:],  # Last 30 messages
            "is_player_in_game": is_player,
            "is_spectator": is_spectator,
            "spectator_count": len(room.spectators),
            "hand_number": room.hand_number,
            "min_bet": room.min_bet,
            "max_bet": room.max_bet,
            "can_act": (is_player and 
                       room.current_player_id == for_player_id and 
                       room.phase == GamePhase.PLAYER_TURNS and
                       player and player.can_act()),
            "available_actions": self.get_available_actions(room, for_player_id) if is_player else [],
            "owner_id": room.owner_id,
            "is_premium": room.is_premium,
            "tournament_mode": room.tournament_mode,
            "deck_remaining": len(room.deck) if is_player else None
        }
        return game_state

    def get_available_actions(self, room: Room, player_id: str) -> List[Dict[str, Any]]:
        """Get available actions for a player with detailed information"""
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
                "max_amount": min(room.max_bet, player.money),
                "description": f"Place a bet between ${room.min_bet} and ${min(room.max_bet, player.money)}"
            })
        elif room.phase == GamePhase.PLAYER_TURNS:
            # Basic actions
            actions.append({
                "action": PlayerAction.HIT.value, 
                "label": "Hit",
                "description": "Take another card"
            })
            actions.append({
                "action": PlayerAction.STAND.value, 
                "label": "Stand",
                "description": "Keep current hand value"
            })
            
            # Double down
            if current_hand.can_double_down() and player.money >= current_hand.bet_amount:
                actions.append({
                    "action": PlayerAction.DOUBLE_DOWN.value, 
                    "label": "Double Down",
                    "description": f"Double bet to ${current_hand.bet_amount * 2} and take exactly one card",
                    "cost": current_hand.bet_amount
                })
            
            # Split
            if (current_hand.can_split() and 
                player.money >= current_hand.bet_amount and 
                len(player.hands) < 4):
                actions.append({
                    "action": PlayerAction.SPLIT.value, 
                    "label": "Split",
                    "description": f"Split pair into two hands (cost: ${current_hand.bet_amount})",
                    "cost": current_hand.bet_amount
                })
            
            # Surrender
            if current_hand.can_surrender():
                actions.append({
                    "action": PlayerAction.SURRENDER.value, 
                    "label": "Surrender",
                    "description": f"Forfeit hand and recover ${current_hand.bet_amount // 2}"
                })

        return actions

    def check_rate_limit(self, client_id: str, limit_type: str = "message") -> bool:
        """Enhanced rate limiting with different types"""
        limit_dict = self.rate_limits if limit_type == "message" else self.action_rate_limits
        max_per_second = (GameConfig.RATE_LIMIT_MESSAGES_PER_SECOND if limit_type == "message" 
                         else GameConfig.RATE_LIMIT_ACTIONS_PER_SECOND)

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
        """Enhanced cleanup with reconnection grace period"""
        current_time = datetime.now()
        rooms_to_delete = []
        
        for room_code, room in list(self.rooms.items()):
            # Clean up disconnected players after grace period
            disconnected_to_remove = []
            for player_id, player in room.players.items():
                if (player.status == PlayerStatus.DISCONNECTED and 
                    (current_time - player.last_activity).total_seconds() > GameConfig.SESSION_TIMEOUT):
                    disconnected_to_remove.append(player_id)
            
            for player_id in disconnected_to_remove:
                del room.players[player_id]
                logger.info(f"Removed disconnected player {player_id} from room {room_code}")
            
            # Check if room should be deleted
            active_players = [p for p in room.players.values() 
                            if p.status not in [PlayerStatus.DISCONNECTED, PlayerStatus.ELIMINATED]]
            
            if (not active_players and not room.spectators and 
                room.is_inactive()):
                rooms_to_delete.append(room_code)
        
        for room_code in rooms_to_delete:
            if room_code in self.rooms:
                del self.rooms[room_code]
                logger.info(f"Deleted inactive room {room_code}")

    def get_server_stats(self) -> Dict[str, Any]:
        """Get comprehensive server statistics"""
        current_time = datetime.now()
        uptime = (current_time - self.stats['server_start_time']).total_seconds()
        
        active_players = sum(len([p for p in room.players.values() 
                                if not p.is_ai and p.status != PlayerStatus.DISCONNECTED]) 
                           for room in self.rooms.values())
        
        active_rooms = len([r for r in self.rooms.values() 
                          if len([p for p in r.players.values() 
                                if p.status != PlayerStatus.DISCONNECTED]) > 0])
        
        return {
            "status": "maintenance" if self.maintenance_mode else "healthy",
            "version": "1.0.0 Production",
            "active_rooms": active_rooms,
            "total_rooms": len(self.rooms),
            "active_players": active_players,
            "total_connections": len(self.connections),
            "uptime_seconds": uptime,
            "uptime_hours": round(uptime / 3600, 2),
            "memory_usage": f"{len(self.rooms) * 50 + active_players * 10}MB (estimated)",
            "security": {
                "banned_ips": len(self.banned_ips),
                "security_events": len(self.security_events),
                "total_warnings": self.stats.get('total_warnings_issued', 0),
                "total_bans": self.stats.get('total_bans_issued', 0)
            },
            **self.stats
        }

    def get_room_list(self) -> List[Dict[str, Any]]:
        """Get list of public rooms with filtering"""
        public_rooms = []
        for room_code, room in self.rooms.items():
            if (room.is_public and 
                room.phase in [GamePhase.WAITING, GamePhase.GAME_OVER] and
                not room.password):
                
                active_players = len([p for p in room.players.values() 
                                    if p.status != PlayerStatus.DISCONNECTED])
                
                if active_players > 0:  # Only show rooms with active players
                    public_rooms.append({
                        "code": room_code,
                        "name": room.name,
                        "players": active_players,
                        "max_players": room.max_players,
                        "phase": room.phase.value,
                        "created": room.created_at.strftime("%H:%M"),
                        "min_bet": room.min_bet,
                        "max_bet": room.max_bet,
                        "is_premium": room.is_premium,
                        "tournament_mode": room.tournament_mode
                    })
        
        # Sort by creation time (newest first)
        public_rooms.sort(key=lambda x: x["created"], reverse=True)
        return public_rooms[:50]  # Limit to 50 rooms

# Global game instance
game = RoyalBlackjackGame()

# Enhanced Pydantic Models
class WSMessage(BaseModel):
    """WebSocket message structure with validation"""
    action: str = PydanticField(min_length=1, max_length=50)
    payload: dict = PydanticField(default_factory=dict)

class CreateRoomPayload(BaseModel):
    """Create room request payload"""
    player_name: str = PydanticField(min_length=1, max_length=SecurityConfig.MAX_NAME_LENGTH)
    room_name: Optional[str] = PydanticField(default=None, max_length=SecurityConfig.MAX_ROOM_NAME_LENGTH)
    password: Optional[str] = PydanticField(default=None, max_length=20)
    is_premium: bool = PydanticField(default=False)

class JoinRoomPayload(BaseModel):
    """Join room request payload"""
    room_code: str = PydanticField(min_length=6, max_length=6)
    player_name: str = PydanticField(min_length=1, max_length=SecurityConfig.MAX_NAME_LENGTH)
    password: Optional[str] = PydanticField(default=None, max_length=20)

class PlayerActionPayload(BaseModel):
    """Player action request payload"""
    action_type: str = PydanticField(min_length=1, max_length=20)
    amount: Optional[int] = PydanticField(default=0, ge=0, le=10000)

class ChatMessagePayload(BaseModel):
    """Chat message payload"""
    message: str = PydanticField(min_length=1, max_length=GameConfig.MAX_MESSAGE_LENGTH)

# Enhanced Game Loop
async def game_loop():
    """Main game loop with enhanced features and error handling"""
    logger.info("🎰 Royal Blackjack 3D Game Loop started")
    loop_count = 0
    last_cleanup = time.time()
    
    while game.running:
        try:
            loop_count += 1
            current_time = time.time()
            
            # Update server stats
            game.stats['uptime'] = (datetime.now() - game.stats['server_start_time']).total_seconds()
            
            # Periodic cleanup every 5 minutes
            if current_time - last_cleanup > GameConfig.ROOM_CLEANUP_INTERVAL:
                game.cleanup_inactive_rooms()
                last_cleanup = current_time
                logger.debug(f"Cleanup completed. Active rooms: {len(game.rooms)}")
            
            # Handle rooms in dealing phase
            dealing_rooms = [r for r in game.rooms.values() 
                           if r.phase == GamePhase.DEALING and not r.dealer_hand.cards]
            for room in dealing_rooms:
                game.deal_initial_cards(room.code)

            # Broadcast game state efficiently
            if loop_count % 10 == 0:  # Broadcast every second at 10fps
                await broadcast_game_states()

            # Run at 10 FPS for optimal performance
            await asyncio.sleep(0.1)

        except Exception as e:
            logger.exception(f"Critical error in game_loop: {e}")
            await asyncio.sleep(1.0)

    logger.info("🎰 Royal Blackjack 3D Game Loop stopped")

async def broadcast_game_states():
    """Efficiently broadcast game states to all clients"""
    broadcast_tasks = []
    
    for room_code, room in list(game.rooms.items()):
        # Collect all users in room
        user_ids_in_room = set()
        for p_id, player_obj in room.players.items():
            if (not player_obj.is_ai and player_obj.connection_id and 
                player_obj.status != PlayerStatus.DISCONNECTED):
                user_ids_in_room.add(player_obj.connection_id)
        user_ids_in_room.update(room.spectators)

        # Prepare and queue broadcasts
        for user_id in list(user_ids_in_room):
            ws_conn = game.connections.get(user_id)
            if ws_conn:
                try:
                    game_state = game.get_game_state(room_code, user_id)
                    if "error" not in game_state:
                        broadcast_tasks.append(
                            ws_conn.send_json({"type": "game_state", "data": game_state})
                        )
                except Exception as e:
                    logger.error(f"Error preparing game_state for user {user_id}: {e}")
                    # Clean up failed connection
                    if user_id in game.connections:
                        del game.connections[user_id]
                    game.leave_room(user_id, force=True)
            else:
                # Connection lost, clean up
                game.leave_room(user_id, force=True)

    # Execute all broadcasts concurrently
    if broadcast_tasks:
        results = await asyncio.gather(*broadcast_tasks, return_exceptions=True)
        
        # Log broadcast statistics
        failed_count = sum(1 for result in results if isinstance(result, Exception))
        if failed_count > 0:
            logger.warning(f"Failed broadcasts: {failed_count}/{len(broadcast_tasks)}")

# Enhanced WebSocket Message Handler
async def handle_websocket_message(websocket: WebSocket, player_id: str, message: WSMessage, ip_address: str = None):
    """Handle incoming WebSocket messages with enhanced security"""
    action = message.action
    payload = message.payload
    
    # Check if server is in maintenance mode
    if game.maintenance_mode and action not in ['ping', 'get_server_stats']:
        await websocket.send_json({
            "type": "error", 
            "message": "🔧 Server is currently under maintenance. Please try again later."
        })
        return

    # IP rate limiting
    if ip_address and not game.check_ip_rate_limit(ip_address):
        await websocket.send_json({
            "type": "error", 
            "message": "⚠️ Too many requests. Please slow down."
        })
        return
    
    try:
        if action == "create_room":
            try:
                create_payload = CreateRoomPayload(**payload)
            except ValidationError as e:
                await websocket.send_json({
                    "type": "error", 
                    "message": f"❌ Invalid data: {e.errors()[0]['msg']}"
                })
                return

            room_code = game.create_room(
                player_id, 
                create_payload.room_name, 
                create_payload.password
            )
            if not room_code:
                await websocket.send_json({
                    "type": "error", 
                    "message": "🏛️ Server is full. Please try again later."
                })
                return

            if game.join_room(room_code, player_id, create_payload.player_name, 
                            create_payload.password, ip_address):
                await websocket.send_json({
                    "type": "room_created", 
                    "data": {"room_code": room_code}
                })
            else:
                await websocket.send_json({
                    "type": "error", 
                    "message": "❌ Failed to join created room"
                })

        elif action == "join_room":
            try:
                join_payload = JoinRoomPayload(**payload)
            except ValidationError as e:
                await websocket.send_json({
                    "type": "error", 
                    "message": f"❌ Invalid data: {e.errors()[0]['msg']}"
                })
                return

            if game.join_room(join_payload.room_code, player_id, join_payload.player_name, 
                            join_payload.password, ip_address):
                await websocket.send_json({
                    "type": "room_joined", 
                    "data": {"room_code": join_payload.room_code}
                })
            else:
                await websocket.send_json({
                    "type": "error", 
                    "message": "❌ Failed to join room (not found, full, or wrong password)"
                })

        elif action == "spectate_room":
            room_code = payload.get("room_code", "").upper()
            if not room_code or len(room_code) != 6:
                await websocket.send_json({
                    "type": "error", 
                    "message": "❌ Invalid room code"
                })
                return
            
            room = game.rooms.get(room_code)
            if room:
                room.spectators.add(player_id)
                game.player_rooms[player_id] = room_code
                await websocket.send_json({
                    "type": "spectating", 
                    "data": {"room_code": room_code}
                })
            else:
                await websocket.send_json({
                    "type": "error", 
                    "message": "🏛️ Room not found"
                })

        elif action == "leave_room":
            game.leave_room(player_id)
            await websocket.send_json({"type": "room_left"})

        elif action == "start_game":
            room_code = game.player_rooms.get(player_id)
            if not room_code:
                await websocket.send_json({
                    "type": "error", 
                    "message": "❌ Not in a room"
                })
                return
            
            if game.start_game(room_code, player_id):
                logger.info(f"Game started in room {room_code} by {player_id}")
            else:
                await websocket.send_json({
                    "type": "error", 
                    "message": "❌ Cannot start game (insufficient players, no bets, or not room owner)"
                })

        elif action == "player_action":
            if not game.check_rate_limit(player_id, "action"):
                await websocket.send_json({
                    "type": "error", 
                    "message": "⚠️ Action rate limit exceeded"
                })
                return
            
            try:
                action_payload = PlayerActionPayload(**payload)
            except ValidationError as e:
                await websocket.send_json({
                    "type": "error", 
                    "message": f"❌ Invalid action data: {e.errors()[0]['msg']}"
                })
                return
            
            room_code = game.player_rooms.get(player_id)
            if not room_code:
                await websocket.send_json({
                    "type": "error", 
                    "message": "❌ Not in a room"
                })
                return

            try:
                blackjack_action = PlayerAction(action_payload.action_type)
                if not game.player_action(room_code, player_id, blackjack_action, action_payload.amount or 0):
                    await websocket.send_json({
                        "type": "error", 
                        "message": "❌ Invalid action or not your turn"
                    })
            except ValueError:
                await websocket.send_json({
                    "type": "error", 
                    "message": f"❌ Unknown action: {action_payload.action_type}"
                })

        elif action == "send_chat_message":
            if not game.check_rate_limit(player_id, "message"):
                await websocket.send_json({
                    "type": "error", 
                    "message": "⚠️ Chat rate limit exceeded"
                })
                return
            
            try:
                chat_payload = ChatMessagePayload(**payload)
            except ValidationError as e:
                await websocket.send_json({
                    "type": "error", 
                    "message": f"❌ Invalid message: {e.errors()[0]['msg']}"
                })
                return
            
            room_code = game.player_rooms.get(player_id)
            if not room_code:
                await websocket.send_json({
                    "type": "error", 
                    "message": "❌ Must be in a room to chat"
                })
                return

            room = game.rooms.get(room_code)
            if room and room.add_chat_message(player_id, chat_payload.message):
                game.stats['total_chat_messages'] += 1
            else:
                await websocket.send_json({
                    "type": "error", 
                    "message": "❌ Message rejected (inappropriate content or other violation)"
                })

        elif action == "get_room_list":
            rooms = game.get_room_list()
            await websocket.send_json({
                "type": "room_list", 
                "data": {"rooms": rooms}
            })

        elif action == "ping":
            await websocket.send_json({
                "type": "pong", 
                "data": {
                    "timestamp": time.time(),
                    "server_time": datetime.now().isoformat()
                }
            })

        elif action == "get_server_stats":
            stats = game.get_server_stats()
            await websocket.send_json({
                "type": "server_stats", 
                "data": stats
            })

        else:
            await websocket.send_json({
                "type": "error", 
                "message": f"❌ Unknown action: {action}"
            })

    except WebSocketDisconnect:
        raise  # Re-raise to be handled by the WebSocket endpoint
    except Exception as e:
        logger.exception(f"Error handling message from {player_id}: {e}")
        try:
            await websocket.send_json({
                "type": "error", 
                "message": "🔧 Server error occurred. Please try again."
            })
        except Exception:
            pass  # Connection might be closed

# Enhanced FastAPI Application Setup
@asynccontextmanager
async def lifespan(app_instance: FastAPI):
    """Application lifespan handler with graceful shutdown"""
    logger.info("🚀 Starting Royal Blackjack 3D Production Server...")
    
    # Start the game loop
    game_task = asyncio.create_task(game_loop())
    
    try:
        yield
    finally:
        # Graceful shutdown sequence
        logger.info("🛑 Shutting down Royal Blackjack 3D server...")
        game.running = False
        
        # Notify all connected clients
        disconnect_tasks = []
        for connection in list(game.connections.values()):
            try:
                disconnect_tasks.append(
                    connection.send_json({
                        "type": "server_shutdown",
                        "message": "🔧 Server is shutting down for maintenance. Thank you for playing!"
                    })
                )
            except Exception:
                pass
        
        # Execute disconnect notifications
        if disconnect_tasks:
            await asyncio.gather(*disconnect_tasks, return_exceptions=True)
        
        # Wait for game loop to finish gracefully
        try:
            await asyncio.wait_for(game_task, timeout=10.0)
        except asyncio.TimeoutError:
            logger.warning("Game loop did not shut down gracefully, forcing termination")
            game_task.cancel()
            try:
                await game_task
            except asyncio.CancelledError:
                pass

        logger.info("🎰 Royal Blackjack 3D server shutdown complete")

# Create FastAPI application
app = FastAPI(
    title="Royal Blackjack 3D - Premium Casino Platform",
    description="Professional 3D Multiplayer Blackjack Casino Experience - Production Ready",
    version="1.0.0",
    lifespan=lifespan,
    docs_url="/docs" if os.getenv("ENVIRONMENT") == "development" else None,
    redoc_url="/redoc" if os.getenv("ENVIRONMENT") == "development" else None
)

# Enhanced CORS middleware
app.add_middleware(
    CORSMiddleware,
    allow_origins=os.getenv("ALLOWED_ORIGINS", "*").split(","),
    allow_credentials=True,
    allow_methods=["GET", "POST", "PUT", "DELETE", "OPTIONS"],
    allow_headers=["*"],
)

# Serve static files if directory exists
if os.path.exists("static"):
    app.mount("/static", StaticFiles(directory="static"), name="static")

# Production HTTP Routes
@app.get("/", response_class=HTMLResponse)
async def get_root():
    """Serve the main game interface"""
    html_file = "index.html"
    if os.path.exists(html_file):
        return FileResponse(html_file)
    else:
        return HTMLResponse(
            content=f"""
            <!DOCTYPE html>
            <html>
                <head>
                    <title>🎰 Royal Blackjack 3D - Premium Casino</title>
                    <style>
                        body {{ 
                            background: linear-gradient(135deg, #0a0a0a 0%, #1a1a2e 50%, #16213e 100%); 
                            color: #fff; 
                            font-family: 'Segoe UI', Arial, sans-serif; 
                            text-align: center; 
                            padding: 50px;
                            margin: 0;
                            min-height: 100vh;
                            display: flex;
                            flex-direction: column;
                            justify-content: center;
                        }}
                        .container {{ max-width: 800px; margin: 0 auto; }}
                        h1 {{ color: #FFD700; font-size: 4rem; margin-bottom: 30px; text-shadow: 0 0 20px rgba(255, 215, 0, 0.5); }}
                        .status {{ color: #4ECDC4; font-size: 1.5rem; margin: 20px 0; }}
                        .instruction {{ 
                            background: rgba(255,255,255,0.1); 
                            padding: 30px; 
                            border-radius: 15px; 
                            margin: 30px 0; 
                            border: 2px solid #FFD700;
                            backdrop-filter: blur(10px);
                        }}
                        .features {{ 
                            display: grid; 
                            grid-template-columns: repeat(auto-fit, minmax(250px, 1fr)); 
                            gap: 20px; 
                            margin: 30px 0; 
                        }}
                        .feature {{ 
                            background: rgba(255,255,255,0.05); 
                            padding: 20px; 
                            border-radius: 10px; 
                            border-left: 4px solid #FFD700; 
                        }}
                        .tech-stack {{ color: #888; font-size: 0.9rem; margin-top: 40px; }}
                    </style>
                </head>
                <body>
                    <div class="container">
                        <h1>🎰 ROYAL BLACKJACK 3D 🎰</h1>
                        <p class="status">✅ Production Server Online & Ready!</p>
                        
                        <div class="instruction">
                            <h3>🚀 Setup Instructions:</h3>
                            <p>1. Save your HTML file as <strong>'{html_file}'</strong> in the same directory as this server</p>
                            <p>2. Refresh this page once the file is in place</p>
                            <p>3. Experience the most advanced 3D blackjack game available!</p>
                        </div>

                        <div class="features">
                            <div class="feature">
                                <h4>🎮 Premium Features</h4>
                                <p>• Stunning 3D graphics<br>• Real-time multiplayer<br>• Professional UI/UX</p>
                            </div>
                            <div class="feature">
                                <h4>🏛️ Enterprise Ready</h4>
                                <p>• Production scalability<br>• Advanced security<br>• Comprehensive logging</p>
                            </div>
                            <div class="feature">
                                <h4>💰 Commercial Ready</h4>
                                <p>• Monetization ready<br>• Analytics built-in<br>• White-label friendly</p>
                            </div>
                        </div>

                        <div class="tech-stack">
                            <strong>Tech Stack:</strong> FastAPI + WebSockets + Three.js + GSAP<br>
                            <strong>WebSocket URL:</strong> ws://localhost:8000/ws<br>
                            <strong>Version:</strong> 1.0.0 Production Release
                        </div>
                    </div>
                </body>
            </html>
            """,
            status_code=200
        )

@app.get("/health")
async def health_check():
    """Enhanced health check endpoint"""
    stats = game.get_server_stats()
    return {
        "status": "healthy" if not game.maintenance_mode else "maintenance",
        "timestamp": datetime.now().isoformat(),
        "version": "1.0.0",
        "uptime": stats.get("uptime_hours", 0),
        "active_rooms": stats.get("active_rooms", 0),
        "active_players": stats.get("active_players", 0),
        "memory_usage": stats.get("memory_usage", "Unknown")
    }

@app.get("/stats")
async def get_detailed_stats():
    """Get comprehensive server statistics for monitoring"""
    stats = game.get_server_stats()
    
    # Enhanced room details
    room_details = []
    for room_code, room in game.rooms.items():
        active_players = [p for p in room.players.values() 
                        if p.status != PlayerStatus.DISCONNECTED]
        
        room_details.append({
            "code": room_code,
            "name": room.name,
            "phase": room.phase.value,
            "players": len(active_players),
            "spectators": len(room.spectators),
            "hand_number": room.hand_number,
            "created": room.created_at.isoformat(),
            "last_activity": room.last_activity.isoformat(),
            "is_public": room.is_public,
            "is_premium": room.is_premium,
            "tournament_mode": room.tournament_mode,
            "min_bet": room.min_bet,
            "max_bet": room.max_bet,
            "deck_remaining": len(room.deck),
            "owner_id": room.owner_id[:8] + "..." if room.owner_id else None
        })
    
    return {
        **stats,
        "rooms": room_details,
        "connection_count": len(game.connections),
        "rate_limits": {
            "message_limits_active": len(game.rate_limits),
            "action_limits_active": len(game.action_rate_limits),
            "ip_limits_active": len(game.ip_rate_limits)
        }
    }

@app.get("/api/rooms")
async def get_public_rooms():
    """REST endpoint for public rooms"""
    rooms = game.get_room_list()
    return {"rooms": rooms, "total": len(rooms)}

@app.post("/api/admin/maintenance")
async def toggle_maintenance(enabled: bool = True):
    """Toggle maintenance mode (admin endpoint)"""
    # In production, you'd want proper authentication here
    game.maintenance_mode = enabled
    status = "enabled" if enabled else "disabled"
    logger.info(f"Maintenance mode {status}")
    return {"maintenance_mode": enabled, "message": f"Maintenance mode {status}"}

# Enhanced WebSocket Endpoint
@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    """Main WebSocket endpoint with enhanced security and features"""
    player_id = str(uuid.uuid4())
    client_ip = websocket.client.host if websocket.client else "unknown"
    
    logger.info(f"🔌 New connection: {player_id} from {client_ip}")
    
    # IP-based rate limiting
    if not game.check_ip_rate_limit(client_ip):
        logger.warning(f"Connection rejected due to IP rate limit: {client_ip}")
        await websocket.close(code=1008, reason="Rate limit exceeded")
        return
    
    try:
        await websocket.accept()
        game.connections[player_id] = websocket
        
        # Send enhanced welcome message
        welcome_data = {
            "player_id": player_id,
            "message": "🎰 Welcome to Royal Blackjack 3D - Premium Edition!",
            "server_version": "1.0.0 Production",
            "timestamp": time.time(),
            "server_time": datetime.now().isoformat(),
            "features": {
                "premium_graphics": True,
                "real_time_multiplayer": True,
                "advanced_statistics": True,
                "professional_ui": True
            }
        }
        
        await websocket.send_json({
            "type": "connected",
            "data": welcome_data
        })

        # Main message handling loop with enhanced error handling
        while True:
            try:
                data = await websocket.receive_text()
                
                try:
                    message_data = json.loads(data)
                except json.JSONDecodeError:
                    await websocket.send_json({
                        "type": "error", 
                        "message": "❌ Invalid JSON format"
                    })
                    continue
                
                if not isinstance(message_data, dict) or "action" not in message_data:
                    await websocket.send_json({
                        "type": "error", 
                        "message": "❌ Invalid message format"
                    })
                    continue
                
                try:
                    ws_message = WSMessage(**message_data)
                    await handle_websocket_message(websocket, player_id, ws_message, client_ip)
                except ValidationError as e:
                    await websocket.send_json({
                        "type": "error", 
                        "message": f"❌ Invalid message format: {e.errors()[0]['msg']}"
                    })
                except ValueError as e:
                    await websocket.send_json({
                        "type": "error", 
                        "message": f"❌ {str(e)}"
                    })

            except WebSocketDisconnect:
                break
            except Exception as e:
                logger.error(f"Error in WebSocket loop for {player_id}: {e}")
                try:
                    await websocket.send_json({
                        "type": "error", 
                        "message": "🔧 Connection error. Please refresh if issues persist."
                    })
                except Exception:
                    break

    except Exception as e:
        logger.exception(f"🔌 WebSocket error for {player_id}: {e}")
    finally:
        # Enhanced cleanup
        if player_id in game.connections:
            del game.connections[player_id]
        
        # Leave room with disconnect status (allows reconnection)
        game.leave_room(player_id, force=False)
        
        logger.info(f"🔌 Connection closed and cleaned up for {player_id}")

# Production Server Entry Point with Enhanced Configuration
if __name__ == "__main__":
    import argparse
    import sys
    
    # Command line argument parsing
    parser = argparse.ArgumentParser(description="Royal Blackjack 3D Production Server")
    parser.add_argument("--host", default="0.0.0.0", help="Host to bind to")
    parser.add_argument("--port", type=int, default=8000, help="Port to bind to")
    parser.add_argument("--workers", type=int, default=1, help="Number of worker processes")
    parser.add_argument("--reload", action="store_true", help="Enable auto-reload for development")
    parser.add_argument("--log-level", default="info", choices=["critical", "error", "warning", "info", "debug"])
    parser.add_argument("--maintenance", action="store_true", help="Start in maintenance mode")
    parser.add_argument("--max-rooms", type=int, default=1000, help="Maximum number of rooms")
    parser.add_argument("--ssl-cert", help="SSL certificate file path")
    parser.add_argument("--ssl-key", help="SSL private key file path")
    
    args = parser.parse_args()
    
    # Override configuration from command line
    if args.max_rooms != 1000:
        GameConfig.MAX_ROOMS = args.max_rooms
    
    if args.maintenance:
        game.maintenance_mode = True
    
    # Enhanced startup logging
    logger.info("=" * 80)
    logger.info("🎰 ROYAL BLACKJACK 3D - PREMIUM PRODUCTION SERVER")
    logger.info("=" * 80)
    logger.info(f"🚀 Starting server on {args.host}:{args.port}")
    logger.info(f"🎯 Environment: {'Development' if args.reload else 'Production'}")
    logger.info(f"🔧 Maintenance mode: {'ON' if game.maintenance_mode else 'OFF'}")
    logger.info(f"📁 Working directory: {os.getcwd()}")
    logger.info(f"🎮 Max rooms: {GameConfig.MAX_ROOMS}")
    logger.info(f"👥 Max players per room: {GameConfig.MAX_PLAYERS_PER_ROOM}")
    logger.info(f"💰 Starting money: ${GameConfig.STARTING_MONEY}")
    logger.info(f"🎲 Bet range: ${GameConfig.MIN_BET} - ${GameConfig.MAX_BET}")
    logger.info(f"📊 Logging level: {args.log_level.upper()}")
    
    if args.ssl_cert and args.ssl_key:
        logger.info(f"🔒 SSL enabled with cert: {args.ssl_cert}")
    
    # Check for HTML file
    html_files = ["index.html", "royal_blackjack.html", "game.html"]
    html_found = None
    for html_file in html_files:
        if os.path.exists(html_file):
            html_found = html_file
            break
    
    if html_found:
        logger.info(f"🎨 Game interface: {html_found}")
    else:
        logger.warning("⚠️  No HTML game file found. Server will show setup instructions.")
    
    logger.info("=" * 80)
    
    # Production server configuration
    server_config = {
        "host": args.host,
        "port": args.port,
        "log_level": args.log_level,
        "access_log": True,
        "ws_ping_interval": 20,
        "ws_ping_timeout": 10,
        "ws_max_size": 16777216,  # 16MB
        "timeout_keep_alive": 5,
        "timeout_notify": 30,
        "limit_concurrency": 1000,
        "limit_max_requests": 10000,
        "loop": "auto"
    }
    
    # SSL configuration for production
    if args.ssl_cert and args.ssl_key:
        if os.path.exists(args.ssl_cert) and os.path.exists(args.ssl_key):
            server_config.update({
                "ssl_certfile": args.ssl_cert,
                "ssl_keyfile": args.ssl_key
            })
            logger.info("🔒 SSL/TLS encryption enabled")
        else:
            logger.error("❌ SSL certificate or key file not found")
            sys.exit(1)
    
    # Development vs Production settings
    if args.reload:
        server_config.update({
            "reload": True,
            "reload_dirs": ["."],
            "reload_includes": ["*.py", "*.html", "*.css", "*.js"]
        })
        logger.info("🔄 Auto-reload enabled for development")
    else:
        server_config.update({
            "workers": max(1, min(args.workers, 4))  # Limit workers for WebSocket compatibility
        })
        if args.workers > 1:
            logger.info(f"👥 Multi-worker mode: {args.workers} workers")
    
    # Environment-specific optimizations
    if os.getenv("ENVIRONMENT") == "production":
        server_config.update({
            "access_log": False,  # Disable access logs in production for better performance
            "server_header": False,
            "date_header": False
        })
        logger.info("🏭 Production optimizations enabled")
    
    # Health check startup
    try:
        logger.info("🔍 Running startup health checks...")
        
        # Check memory
        import psutil
        memory_percent = psutil.virtual_memory().percent
        if memory_percent > 90:
            logger.warning(f"⚠️  High memory usage: {memory_percent}%")
        else:
            logger.info(f"💾 Memory usage: {memory_percent}%")
        
        # Check disk space
        disk_usage = psutil.disk_usage('/').percent
        if disk_usage > 90:
            logger.warning(f"⚠️  High disk usage: {disk_usage}%")
        else:
            logger.info(f"💿 Disk usage: {disk_usage}%")
            
    except ImportError:
        logger.info("📊 Install psutil for enhanced system monitoring")
    except Exception as e:
        logger.warning(f"⚠️  Health check warning: {e}")
    
    # Final startup message
    protocol = "https" if (args.ssl_cert and args.ssl_key) else "http"
    ws_protocol = "wss" if (args.ssl_cert and args.ssl_key) else "ws"
    
    logger.info("🌟 Royal Blackjack 3D Server Starting...")
    logger.info(f"🌐 Web Interface: {protocol}://{args.host}:{args.port}")
    logger.info(f"🔌 WebSocket URL: {ws_protocol}://{args.host}:{args.port}/ws")
    logger.info(f"📊 Statistics: {protocol}://{args.host}:{args.port}/stats")
    logger.info(f"❤️  Health Check: {protocol}://{args.host}:{args.port}/health")
    logger.info("🎰 Ready to accept players!")
    
    # Run the server
    try:
        uvicorn.run(
            "main:app" if __name__ == "__main__" else app,
            **server_config
        )
    except KeyboardInterrupt:
        logger.info("🛑 Server stopped by user")
    except Exception as e:
        logger.exception(f"💥 Server startup failed: {e}")
        sys.exit(1)
    finally:
        logger.info("🎰 Royal Blackjack 3D Server shutdown complete")

# Docker and Container Support
def create_dockerfile():
    """Generate Dockerfile for containerized deployment"""
    dockerfile_content = '''# Royal Blackjack 3D - Production Dockerfile
FROM python:3.11-slim

# Set working directory
WORKDIR /app

# Install system dependencies
RUN apt-get update && apt-get install -y \\
    gcc \\
    && rm -rf /var/lib/apt/lists/*

# Copy requirements first for better Docker layer caching
COPY requirements.txt .

# Install Python dependencies
RUN pip install --no-cache-dir -r requirements.txt

# Copy application code
COPY . .

# Create non-root user for security
RUN useradd --create-home --shell /bin/bash royal && \\
    chown -R royal:royal /app
USER royal

# Expose port
EXPOSE 8000

# Health check
HEALTHCHECK --interval=30s --timeout=10s --start-period=5s --retries=3 \\
    CMD curl -f http://localhost:8000/health || exit 1

# Run the application
CMD ["python", "main.py", "--host", "0.0.0.0", "--port", "8000"]
'''
    
    with open("Dockerfile", "w") as f:
        f.write(dockerfile_content)
    
    logger.info("📦 Dockerfile created for containerized deployment")

def create_docker_compose():
    """Generate docker-compose.yml for easy deployment"""
    compose_content = '''version: '3.8'

services:
  royal-blackjack:
    build: .
    ports:
      - "8000:8000"
    environment:
      - ENVIRONMENT=production
      - LOG_LEVEL=info
    volumes:
      - ./logs:/app/logs
    restart: unless-stopped
    healthcheck:
      test: ["CMD", "curl", "-f", "http://localhost:8000/health"]
      interval: 30s
      timeout: 10s
      retries: 3
      start_period: 40s

  nginx:
    image: nginx:alpine
    ports:
      - "80:80"
      - "443:443"
    volumes:
      - ./nginx.conf:/etc/nginx/nginx.conf
      - ./ssl:/etc/nginx/ssl
    depends_on:
      - royal-blackjack
    restart: unless-stopped

volumes:
  logs:
'''
    
    with open("docker-compose.yml", "w") as f:
        f.write(compose_content)
    
    logger.info("🐳 Docker Compose configuration created")

def create_requirements():
    """Generate requirements.txt for the project"""
    requirements_content = '''# Royal Blackjack 3D - Production Requirements
fastapi==0.104.1
uvicorn[standard]==0.24.0
websockets==11.0.3
pydantic==2.5.0
python-multipart==0.0.6
aiofiles==23.2.1
python-jose[cryptography]==3.3.0
passlib[bcrypt]==1.7.4
psutil==5.9.6

# Optional performance enhancements
orjson==3.9.10
ujson==5.8.0

# Development tools (optional)
pytest==7.4.3
pytest-asyncio==0.21.1
black==23.11.0
isort==5.12.0
mypy==1.7.1
'''
    
    with open("requirements.txt", "w") as f:
        f.write(requirements_content)
    
    logger.info("📋 Requirements file created")

def create_nginx_config():
    """Generate nginx configuration for production deployment"""
    nginx_content = '''events {
    worker_connections 1024;
}

http {
    upstream royal_blackjack {
        server royal-blackjack:8000;
    }

    # Rate limiting
    limit_req_zone $binary_remote_addr zone=api:10m rate=10r/s;
    limit_req_zone $binary_remote_addr zone=ws:10m rate=5r/s;

    server {
        listen 80;
        server_name _;
        return 301 https://$host$request_uri;
    }

    server {
        listen 443 ssl http2;
        server_name _;

        # SSL configuration
        ssl_certificate /etc/nginx/ssl/cert.pem;
        ssl_certificate_key /etc/nginx/ssl/key.pem;
        ssl_protocols TLSv1.2 TLSv1.3;
        ssl_ciphers ECDHE-RSA-AES256-GCM-SHA512:DHE-RSA-AES256-GCM-SHA512;
        ssl_prefer_server_ciphers off;

        # Security headers
        add_header X-Frame-Options DENY;
        add_header X-Content-Type-Options nosniff;
        add_header X-XSS-Protection "1; mode=block";
        add_header Strict-Transport-Security "max-age=63072000; includeSubDomains; preload";

        # WebSocket proxy
        location /ws {
            limit_req zone=ws burst=10 nodelay;
            proxy_pass http://royal_blackjack;
            proxy_http_version 1.1;
            proxy_set_header Upgrade $http_upgrade;
            proxy_set_header Connection "upgrade";
            proxy_set_header Host $host;
            proxy_set_header X-Real-IP $remote_addr;
            proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
            proxy_set_header X-Forwarded-Proto $scheme;
            proxy_read_timeout 86400;
        }

        # API endpoints
        location /api/ {
            limit_req zone=api burst=20 nodelay;
            proxy_pass http://royal_blackjack;
            proxy_set_header Host $host;
            proxy_set_header X-Real-IP $remote_addr;
            proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
            proxy_set_header X-Forwarded-Proto $scheme;
        }

        # Static files and main application
        location / {
            proxy_pass http://royal_blackjack;
            proxy_set_header Host $host;
            proxy_set_header X-Real-IP $remote_addr;
            proxy_set_header X-Forwarded-For $proxy_add_x_forwarded_for;
            proxy_set_header X-Forwarded-Proto $scheme;
        }
    }
}
'''
    
    with open("nginx.conf", "w") as f:
        f.write(nginx_content)
    
    logger.info("🌐 Nginx configuration created")

# Deployment helper functions
def setup_production_files():
    """Create all necessary files for production deployment"""
    logger.info("🚀 Setting up production deployment files...")
    
    try:
        create_requirements()
        create_dockerfile()
        create_docker_compose()
        create_nginx_config()
        
        # Create systemd service file
        service_content = '''[Unit]
Description=Royal Blackjack 3D Game Server
After=network.target

[Service]
Type=simple
User=royal
WorkingDirectory=/opt/royal-blackjack
Environment=PYTHONPATH=/opt/royal-blackjack
ExecStart=/opt/royal-blackjack/venv/bin/python main.py --host 0.0.0.0 --port 8000
Restart=always
RestartSec=10

[Install]
WantedBy=multi-user.target
'''
        
        with open("royal-blackjack.service", "w") as f:
            f.write(service_content)
        
        # Create deployment script
        deploy_script = '''#!/bin/bash
# Royal Blackjack 3D Deployment Script

set -e

echo "🎰 Deploying Royal Blackjack 3D..."

# Create directories
sudo mkdir -p /opt/royal-blackjack
sudo mkdir -p /var/log/royal-blackjack

# Copy files
sudo cp -r . /opt/royal-blackjack/
sudo chown -R royal:royal /opt/royal-blackjack

# Setup Python virtual environment
cd /opt/royal-blackjack
python3 -m venv venv
source venv/bin/activate
pip install -r requirements.txt

# Install systemd service
sudo cp royal-blackjack.service /etc/systemd/system/
sudo systemctl daemon-reload
sudo systemctl enable royal-blackjack
sudo systemctl start royal-blackjack

echo "✅ Deployment complete!"
echo "🌐 Service status: sudo systemctl status royal-blackjack"
echo "📊 Logs: sudo journalctl -u royal-blackjack -f"
'''
        
        with open("deploy.sh", "w") as f:
            f.write(deploy_script)
        
        os.chmod("deploy.sh", 0o755)
        
        logger.info("✅ Production deployment files created successfully!")
        logger.info("📁 Files created:")
        logger.info("   - requirements.txt (Python dependencies)")
        logger.info("   - Dockerfile (Container image)")
        logger.info("   - docker-compose.yml (Container orchestration)")
        logger.info("   - nginx.conf (Reverse proxy configuration)")
        logger.info("   - royal-blackjack.service (Systemd service)")
        logger.info("   - deploy.sh (Deployment script)")
        logger.info("")
        logger.info("🚀 Quick start commands:")
        logger.info("   Docker: docker-compose up -d")
        logger.info("   Manual: chmod +x deploy.sh && sudo ./deploy.sh")
        
    except Exception as e:
        logger.error(f"❌ Error creating production files: {e}")

# Performance monitoring and metrics
class PerformanceMonitor:
    """Performance monitoring and metrics collection"""
    
    def __init__(self):
        self.metrics = {
            'requests_per_second': 0,
            'avg_response_time': 0,
            'active_connections': 0,
            'memory_usage': 0,
            'cpu_usage': 0,
            'error_rate': 0
        }
        self.request_times = []
        self.error_count = 0
        self.request_count = 0
        self.start_time = time.time()
    
    def record_request(self, response_time: float, success: bool = True):
        """Record request metrics"""
        self.request_times.append(response_time)
        self.request_count += 1
        
        if not success:
            self.error_count += 1
        
        # Keep only recent request times (last 1000)
        if len(self.request_times) > 1000:
            self.request_times = self.request_times[-1000:]
    
    def get_metrics(self) -> Dict[str, float]:
        """Get current performance metrics"""
        current_time = time.time()
        uptime = current_time - self.start_time
        
        # Calculate requests per second
        if uptime > 0:
            self.metrics['requests_per_second'] = self.request_count / uptime
        
        # Calculate average response time
        if self.request_times:
            self.metrics['avg_response_time'] = sum(self.request_times) / len(self.request_times)
        
        # Calculate error rate
        if self.request_count > 0:
            self.metrics['error_rate'] = (self.error_count / self.request_count) * 100
        
        # Get system metrics if available
        try:
            import psutil
            self.metrics['memory_usage'] = psutil.virtual_memory().percent
            self.metrics['cpu_usage'] = psutil.cpu_percent()
        except ImportError:
            pass
        
        return self.metrics.copy()

# Initialize performance monitor
performance_monitor = PerformanceMonitor()

# Add performance monitoring to the game instance
game.performance_monitor = performance_monitor

logger.info("🎰 Royal Blackjack 3D server module loaded successfully")
logger.info("💡 Use 'python main.py --help' for command line options")
logger.info("🚀 Use setup_production_files() to create deployment files")
