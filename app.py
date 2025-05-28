import asyncio
import json
import logging
import os
import random
import time
import uuid
import hashlib
import hmac
from typing import Dict, List, Optional, Set, Tuple, Union
from enum import Enum, IntEnum
from dataclasses import dataclass, asdict, field
from collections import defaultdict, Counter
from contextlib import asynccontextmanager
from datetime import datetime, timedelta
import math

import uvicorn
from fastapi import FastAPI, WebSocket, WebSocketDisconnect, HTTPException, Request
from fastapi.responses import HTMLResponse
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel, ValidationError, Field

# Configure advanced logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler('poker_game.log') if os.environ.get('LOG_FILE') else logging.NullHandler()
    ]
)
logger = logging.getLogger(__name__)

# Advanced Game Constants
STARTING_MONEY = 1000
TOURNAMENT_STARTING_MONEY = 10000
SMALL_BLIND = 25
BIG_BLIND = 50
ANTE = 5
MAX_PLAYERS_PER_ROOM = 10
MIN_PLAYERS_TO_START = 2
GAME_UPDATE_RATE = 60  # 60 FPS for smooth animations
RATE_LIMIT_MESSAGES_PER_SECOND = 15
RATE_LIMIT_ACTIONS_PER_SECOND = 5
MAX_CHAT_MESSAGES = 100
HAND_EVALUATION_CACHE_SIZE = 10000
AUTO_FOLD_TIMEOUT = 30  # seconds
TOURNAMENT_BLIND_INCREASE_INTERVAL = 600  # 10 minutes
MAX_ROOMS = 1000
SESSION_TIMEOUT = 3600  # 1 hour

class GameMode(Enum):
    CASH_GAME = "cash_game"
    TOURNAMENT = "tournament"
    SIT_AND_GO = "sit_and_go"

class GamePhase(Enum):
    WAITING = "waiting"
    PRE_FLOP = "pre_flop"
    FLOP = "flop"
    TURN = "turn"
    RIVER = "river"
    SHOWDOWN = "showdown"
    GAME_OVER = "game_over"
    TOURNAMENT_BREAK = "tournament_break"

class PlayerAction(Enum):
    FOLD = "fold"
    CHECK = "check"
    CALL = "call"
    RAISE = "raise"
    ALL_IN = "all_in"
    SIT_OUT = "sit_out"
    SIT_IN = "sit_in"

class PlayerStatus(Enum):
    ACTIVE = "active"
    FOLDED = "folded"
    ALL_IN = "all_in"
    SITTING_OUT = "sitting_out"
    ELIMINATED = "eliminated"

class HandRank(IntEnum):
    HIGH_CARD = 1
    PAIR = 2
    TWO_PAIR = 3
    THREE_OF_A_KIND = 4
    STRAIGHT = 5
    FLUSH = 6
    FULL_HOUSE = 7
    FOUR_OF_A_KIND = 8
    STRAIGHT_FLUSH = 9
    ROYAL_FLUSH = 10

class RoomType(Enum):
    PUBLIC = "public"
    PRIVATE = "private"
    TOURNAMENT = "tournament"

@dataclass
class Card:
    suit: str  # hearts, diamonds, clubs, spades
    rank: str  # 2-10, J, Q, K, A
    id: str = field(default_factory=lambda: str(uuid.uuid4()))
    
    def __str__(self):
        return f"{self.rank}{self.suit[0].upper()}"
    
    def value(self) -> int:
        if self.rank == 'A':
            return 14
        elif self.rank == 'K':
            return 13
        elif self.rank == 'Q':
            return 12
        elif self.rank == 'J':
            return 11
        else:
            return int(self.rank)
    
    def suit_value(self) -> int:
        return ['clubs', 'diamonds', 'hearts', 'spades'].index(self.suit)

@dataclass
class HandEvaluation:
    rank: HandRank
    value: int
    cards: List[Card]
    description: str
    kickers: List[int] = field(default_factory=list)

@dataclass
class SidePot:
    amount: int
    eligible_players: Set[str]
    winner: Optional[str] = None

@dataclass
class PlayerStats:
    hands_played: int = 0
    hands_won: int = 0
    total_winnings: int = 0
    biggest_pot: int = 0
    vpip: float = 0.0  # Voluntarily Put In Pot
    pfr: float = 0.0   # Pre-Flop Raise
    aggression_factor: float = 0.0
    showdown_percentage: float = 0.0

@dataclass
class Player:
    id: str
    name: str
    money: int = STARTING_MONEY
    current_bet: int = 0
    total_bet_this_hand: int = 0
    cards: List[Card] = field(default_factory=list)
    status: PlayerStatus = PlayerStatus.ACTIVE
    position: int = 0
    last_action: Optional[PlayerAction] = None
    last_action_time: float = 0
    avatar: str = "default"
    color: str = "#ffffff"
    is_dealer: bool = False
    is_small_blind: bool = False
    is_big_blind: bool = False
    time_bank: int = 30  # seconds
    connection_id: Optional[str] = None
    stats: PlayerStats = field(default_factory=PlayerStats)
    session_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    tournament_rank: int = 0
    
    def can_act(self) -> bool:
        return self.status == PlayerStatus.ACTIVE and self.money > 0
    
    def is_all_in(self) -> bool:
        return self.status == PlayerStatus.ALL_IN or self.money == 0
    
    def reset_for_new_hand(self):
        self.cards = []
        self.current_bet = 0
        self.total_bet_this_hand = 0
        self.last_action = None
        self.last_action_time = 0
        if self.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED]:
            self.status = PlayerStatus.ACTIVE
        self.is_dealer = False
        self.is_small_blind = False
        self.is_big_blind = False

@dataclass
class GameSettings:
    small_blind: int = SMALL_BLIND
    big_blind: int = BIG_BLIND
    ante: int = 0
    max_players: int = MAX_PLAYERS_PER_ROOM
    min_players: int = MIN_PLAYERS_TO_START
    auto_fold_timeout: int = AUTO_FOLD_TIMEOUT
    time_bank: int = 30
    game_mode: GameMode = GameMode.CASH_GAME
    tournament_structure: Dict = field(default_factory=dict)
    buy_in: int = 0
    password: Optional[str] = None

@dataclass
class Room:
    code: str
    name: str
    players: Dict[str, Player]
    spectators: Set[str]
    deck: List[Card]
    community_cards: List[Card]
    current_player_index: int = 0
    dealer_index: int = 0
    phase: GamePhase = GamePhase.WAITING
    pot: int = 0
    side_pots: List[SidePot] = field(default_factory=list)
    current_bet: int = 0
    min_raise: int = BIG_BLIND
    chat_messages: List[Dict] = field(default_factory=list)
    last_action_time: float = 0
    hand_number: int = 0
    settings: GameSettings = field(default_factory=GameSettings)
    room_type: RoomType = RoomType.PUBLIC
    created_at: datetime = field(default_factory=datetime.now)
    last_activity: datetime = field(default_factory=datetime.now)
    owner_id: Optional[str] = None
    hand_history: List[Dict] = field(default_factory=list)
    tournament_level: int = 1
    tournament_next_level: datetime = field(default_factory=lambda: datetime.now() + timedelta(minutes=10))
    paused: bool = False
    pause_reason: str = ""
    
    def __post_init__(self):
        if not self.deck:
            self.deck = self.create_deck()

    def create_deck(self) -> List[Card]:
        suits = ["hearts", "diamonds", "clubs", "spades"]
        ranks = ["2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K", "A"]
        deck = [Card(suit, rank) for suit in suits for rank in ranks]
        random.shuffle(deck)
        return deck

    def shuffle_deck(self):
        self.deck = self.create_deck()

    def deal_cards(self, count: int = 2):
        active_players = [p for p in self.players.values() if p.status == PlayerStatus.ACTIVE]
        for _ in range(count):
            for player in active_players:
                if self.deck:
                    player.cards.append(self.deck.pop())

    def deal_community_cards(self, count: int):
        for _ in range(count):
            if self.deck:
                self.community_cards.append(self.deck.pop())

    def get_active_players(self) -> List[Player]:
        return [p for p in self.players.values() if p.status not in [PlayerStatus.FOLDED, PlayerStatus.ELIMINATED, PlayerStatus.SITTING_OUT]]

    def get_players_in_hand(self) -> List[Player]:
        return [p for p in self.players.values() if p.status in [PlayerStatus.ACTIVE, PlayerStatus.ALL_IN]]

    def calculate_side_pots(self):
        self.side_pots = []
        players_in_hand = self.get_players_in_hand()
        
        if len(players_in_hand) <= 1:
            return
        
        # Group players by their total bet amount
        bet_groups = defaultdict(list)
        for player in players_in_hand:
            bet_groups[player.total_bet_this_hand].append(player)
        
        # Create side pots
        sorted_bets = sorted(bet_groups.keys())
        prev_bet = 0
        
        for bet_amount in sorted_bets:
            if bet_amount > prev_bet:
                pot_size = (bet_amount - prev_bet) * len([p for p in players_in_hand if p.total_bet_this_hand >= bet_amount])
                eligible_players = {p.id for p in players_in_hand if p.total_bet_this_hand >= bet_amount}
                
                if pot_size > 0:
                    self.side_pots.append(SidePot(pot_size, eligible_players))
                
                prev_bet = bet_amount

    def update_activity(self):
        self.last_activity = datetime.now()

class AdvancedPokerGame:
    def __init__(self):
        self.rooms: Dict[str, Room] = {}
        self.connections: Dict[str, WebSocket] = {}
        self.player_rooms: Dict[str, str] = {}
        self.player_sessions: Dict[str, str] = {}  # player_id -> session_id
        self.rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.action_rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.hand_evaluation_cache: Dict[str, HandEvaluation] = {}
        self.running = True
        self.global_stats = {
            'total_hands': 0,
            'total_players': 0,
            'active_rooms': 0,
            'biggest_pot': 0
        }

    def generate_room_code(self) -> str:
        return ''.join(random.choices('ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789', k=8))

    def create_room(self, player_id: str, room_settings: GameSettings, room_name: str = None) -> str:
        if len(self.rooms) >= MAX_ROOMS:
            raise Exception("Maximum number of rooms reached")
            
        room_code = self.generate_room_code()
        while room_code in self.rooms:
            room_code = self.generate_room_code()
        
        room_name = room_name or f"Room {room_code}"
        
        self.rooms[room_code] = Room(
            code=room_code,
            name=room_name,
            players={},
            spectators=set(),
            deck=[],
            community_cards=[],
            settings=room_settings,
            owner_id=player_id,
            room_type=RoomType.PRIVATE if room_settings.password else RoomType.PUBLIC
        )
        
        logger.info(f"Room {room_code} created by player {player_id}")
        return room_code

    def join_room(self, room_code: str, player_id: str, player_name: str, password: str = None) -> bool:
        if room_code not in self.rooms:
            return False
        
        room = self.rooms[room_code]
        
        # Check password if required
        if room.settings.password and room.settings.password != password:
            return False
        
        if len(room.players) >= room.settings.max_players:
            return False
        
        # Check if rejoining
        if player_id in room.players:
            room.players[player_id].connection_id = player_id
            room.update_activity()
            return True
        
        # Create new player
        player = Player(
            id=player_id,
            name=player_name,
            position=len(room.players),
            money=room.settings.buy_in if room.settings.buy_in > 0 else (TOURNAMENT_STARTING_MONEY if room.settings.game_mode == GameMode.TOURNAMENT else STARTING_MONEY),
            avatar=f"avatar_{random.randint(1, 10)}",
            color=f"#{random.randint(0, 0xFFFFFF):06x}",
            connection_id=player_id
        )
        
        room.players[player_id] = player
        self.player_rooms[player_id] = room_code
        room.update_activity()
        
        logger.info(f"Player {player_name} joined room {room_code}")
        return True

    def leave_room(self, player_id: str, force: bool = False):
        if player_id not in self.player_rooms:
            return
        
        room_code = self.player_rooms[player_id]
        room = self.rooms[room_code]
        
        if player_id in room.players:
            player = room.players[player_id]
            
            # In tournament, mark as eliminated instead of removing
            if room.settings.game_mode == GameMode.TOURNAMENT and not force:
                player.status = PlayerStatus.ELIMINATED
                player.connection_id = None
            else:
                del room.players[player_id]
        
        if player_id in room.spectators:
            room.spectators.remove(player_id)
        
        if player_id in self.player_rooms:
            del self.player_rooms[player_id]
        
        # Clean up empty rooms or transfer ownership
        if not room.players and not room.spectators:
            del self.rooms[room_code]
            logger.info(f"Room {room_code} deleted (empty)")
        elif room.owner_id == player_id and room.players:
            # Transfer ownership to another player
            room.owner_id = next(iter(room.players.keys()))

    def spectate_room(self, room_code: str, player_id: str, password: str = None) -> bool:
        if room_code not in self.rooms:
            return False
        
        room = self.rooms[room_code]
        
        # Check password if required
        if room.settings.password and room.settings.password != password:
            return False
        
        room.spectators.add(player_id)
        self.player_rooms[player_id] = room_code
        room.update_activity()
        return True

    def start_game(self, room_code: str, force_start: bool = False):
        room = self.rooms[room_code]
        active_players = room.get_active_players()
        
        if len(active_players) < room.settings.min_players and not force_start:
            return False
        
        room.phase = GamePhase.PRE_FLOP
        room.hand_number += 1
        room.shuffle_deck()
        room.community_cards = []
        room.pot = 0
        room.side_pots = []
        room.current_bet = room.settings.big_blind
        room.min_raise = room.settings.big_blind
        
        # Reset all players for new hand
        for player in room.players.values():
            player.reset_for_new_hand()
        
        # Set positions
        self.set_player_positions(room)
        
        # Post blinds and ante
        self.post_blinds_and_ante(room)
        
        # Deal cards
        room.deal_cards(2)
        
        # Set first player to act
        room.current_player_index = self.get_first_player_to_act(room)
        room.last_action_time = time.time()
        
        # Update stats
        self.global_stats['total_hands'] += 1
        
        logger.info(f"Game started in room {room_code}, hand #{room.hand_number}")
        return True

    def set_player_positions(self, room: Room):
        active_players = room.get_active_players()
        if len(active_players) < 2:
            return
        
        # Rotate dealer position
        room.dealer_index = (room.dealer_index + 1) % len(active_players)
        
        # Set dealer, small blind, and big blind
        dealer_player = active_players[room.dealer_index]
        dealer_player.is_dealer = True
        
        if len(active_players) == 2:
            # Heads up: dealer is small blind
            dealer_player.is_small_blind = True
            big_blind_idx = (room.dealer_index + 1) % len(active_players)
            active_players[big_blind_idx].is_big_blind = True
        else:
            # Multi-way: small blind is next to dealer
            small_blind_idx = (room.dealer_index + 1) % len(active_players)
            big_blind_idx = (room.dealer_index + 2) % len(active_players)
            active_players[small_blind_idx].is_small_blind = True
            active_players[big_blind_idx].is_big_blind = True

    def post_blinds_and_ante(self, room: Room):
        active_players = room.get_active_players()
        
        # Post ante
        if room.settings.ante > 0:
            for player in active_players:
                ante_amount = min(room.settings.ante, player.money)
                player.money -= ante_amount
                player.current_bet += ante_amount
                player.total_bet_this_hand += ante_amount
                room.pot += ante_amount
        
        # Post blinds
        for player in active_players:
            if player.is_small_blind:
                blind_amount = min(room.settings.small_blind, player.money)
                player.money -= blind_amount
                player.current_bet += blind_amount
                player.total_bet_this_hand += blind_amount
                room.pot += blind_amount
                if player.money == 0:
                    player.status = PlayerStatus.ALL_IN
            elif player.is_big_blind:
                blind_amount = min(room.settings.big_blind, player.money)
                player.money -= blind_amount
                player.current_bet += blind_amount
                player.total_bet_this_hand += blind_amount
                room.pot += blind_amount
                if player.money == 0:
                    player.status = PlayerStatus.ALL_IN

    def get_first_player_to_act(self, room: Room) -> int:
        active_players = room.get_active_players()
        if len(active_players) < 3:
            return 0
        
        # First player after big blind
        for i, player in enumerate(active_players):
            if player.is_big_blind:
                return (i + 1) % len(active_players)
        return 0

    def player_action(self, room_code: str, player_id: str, action: PlayerAction, amount: int = 0) -> bool:
        room = self.rooms[room_code]
        
        if player_id not in room.players:
            return False
        
        player = room.players[player_id]
        active_players = room.get_active_players()
        
        if not player.can_act() or active_players[room.current_player_index].id != player_id:
            return False
        
        # Process action
        success = self.process_player_action(room, player, action, amount)
        
        if success:
            player.last_action = action
            player.last_action_time = time.time()
            room.last_action_time = time.time()
            
            # Update stats
            player.stats.hands_played += 1
            
            # Move to next player or advance game
            self.advance_game(room_code)
        
        return success

    def process_player_action(self, room: Room, player: Player, action: PlayerAction, amount: int) -> bool:
        if action == PlayerAction.FOLD:
            player.status = PlayerStatus.FOLDED
            return True
            
        elif action == PlayerAction.CHECK:
            if room.current_bet > player.current_bet:
                return False  # Can't check if there's a bet to call
            return True
            
        elif action == PlayerAction.CALL:
            call_amount = min(room.current_bet - player.current_bet, player.money)
            if call_amount <= 0:
                return False
            
            player.money -= call_amount
            player.current_bet += call_amount
            player.total_bet_this_hand += call_amount
            room.pot += call_amount
            
            if player.money == 0:
                player.status = PlayerStatus.ALL_IN
            return True
            
        elif action == PlayerAction.RAISE:
            total_bet = room.current_bet + max(amount, room.min_raise)
            bet_amount = min(total_bet - player.current_bet, player.money)
            
            if bet_amount <= 0 or total_bet < room.current_bet + room.min_raise:
                return False
            
            player.money -= bet_amount
            player.current_bet += bet_amount
            player.total_bet_this_hand += bet_amount
            room.pot += bet_amount
            room.current_bet = player.current_bet
            room.min_raise = max(room.min_raise, bet_amount)
            
            if player.money == 0:
                player.status = PlayerStatus.ALL_IN
            return True
            
        elif action == PlayerAction.ALL_IN:
            if player.money <= 0:
                return False
            
            bet_amount = player.money
            player.current_bet += bet_amount
            player.total_bet_this_hand += bet_amount
            room.pot += bet_amount
            player.money = 0
            player.status = PlayerStatus.ALL_IN
            
            if player.current_bet > room.current_bet:
                room.current_bet = player.current_bet
                room.min_raise = max(room.min_raise, bet_amount)
            
            return True
            
        elif action == PlayerAction.SIT_OUT:
            player.status = PlayerStatus.SITTING_OUT
            return True
            
        elif action == PlayerAction.SIT_IN:
            if player.status == PlayerStatus.SITTING_OUT:
                player.status = PlayerStatus.ACTIVE
                return True
            return False
        
        return False

    def advance_game(self, room_code: str):
        room = self.rooms[room_code]
        active_players = room.get_players_in_hand()
        
        # Check if hand is over
        if len(active_players) <= 1:
            self.end_hand(room_code)
            return
        
        # Move to next player
        self.move_to_next_player(room)
        
        # Check if betting round is complete
        if self.is_betting_round_complete(room):
            self.advance_phase(room_code)

    def move_to_next_player(self, room: Room):
        active_players = room.get_active_players()
        if not active_players:
            return
        
        start_index = room.current_player_index
        attempts = 0
        
        while attempts < len(active_players):
            room.current_player_index = (room.current_player_index + 1) % len(active_players)
            current_player = active_players[room.current_player_index]
            
            if current_player.can_act():
                break
                
            attempts += 1
        
        # Set action timer
        room.last_action_time = time.time()

    def is_betting_round_complete(self, room: Room) -> bool:
        active_players = [p for p in room.players.values() if p.status == PlayerStatus.ACTIVE]
        
        if len(active_players) <= 1:
            return True
        
        # Check if all active players have acted and matched the current bet
        for player in active_players:
            if player.last_action is None:
                return False
            if player.current_bet < room.current_bet and player.money > 0:
                return False
        
        return True

    def advance_phase(self, room_code: str):
        room = self.rooms[room_code]
        
        # Reset betting for next round
        for player in room.players.values():
            player.current_bet = 0
            player.last_action = None
        
        room.current_bet = 0
        room.min_raise = room.settings.big_blind
        
        # Advance to next phase
        if room.phase == GamePhase.PRE_FLOP:
            room.phase = GamePhase.FLOP
            room.deal_community_cards(3)
        elif room.phase == GamePhase.FLOP:
            room.phase = GamePhase.TURN
            room.deal_community_cards(1)
        elif room.phase == GamePhase.TURN:
            room.phase = GamePhase.RIVER
            room.deal_community_cards(1)
        elif room.phase == GamePhase.RIVER:
            room.phase = GamePhase.SHOWDOWN
            self.end_hand(room_code)
            return
        
        # Set first player to act (first active player after dealer)
        active_players = room.get_active_players()
        if active_players:
            for i, player in enumerate(active_players):
                if not player.is_dealer:
                    room.current_player_index = i
                    break
            else:
                room.current_player_index = 0
        
        room.last_action_time = time.time()

    def end_hand(self, room_code: str):
        room = self.rooms[room_code]
        players_in_hand = room.get_players_in_hand()
        
        # Calculate side pots
        room.calculate_side_pots()
        
        # Evaluate hands and determine winners
        winners = self.determine_winners(room)
        
        # Distribute winnings
        self.distribute_winnings(room, winners)
        
        # Save hand history
        self.save_hand_history(room)
        
        # Update tournament if applicable
        if room.settings.game_mode == GameMode.TOURNAMENT:
            self.update_tournament(room)
        
        # Check if game should continue
        active_players = [p for p in room.players.values() if p.money > 0 and p.status != PlayerStatus.ELIMINATED]
        
        if len(active_players) <= 1 and room.settings.game_mode == GameMode.TOURNAMENT:
            room.phase = GamePhase.GAME_OVER
            self.end_tournament(room)
        else:
            room.phase = GamePhase.WAITING
            
            # Auto-start next hand if enough players
            if len(active_players) >= room.settings.min_players:
                asyncio.create_task(self.auto_start_next_hand(room_code))

    def determine_winners(self, room: Room) -> Dict[str, HandEvaluation]:
        players_in_hand = room.get_players_in_hand()
        winners = {}
        
        for player in players_in_hand:
            if player.status != PlayerStatus.FOLDED:
                hand_eval = self.evaluate_hand(player.cards + room.community_cards)
                winners[player.id] = hand_eval
        
        return winners

    def evaluate_hand(self, cards: List[Card]) -> HandEvaluation:
        # Create cache key
        card_key = ''.join(sorted([f"{c.suit[0]}{c.rank}" for c in cards]))
        
        if card_key in self.hand_evaluation_cache:
            return self.hand_evaluation_cache[card_key]
        
        # Evaluate hand (full poker hand evaluation)
        hand_eval = self.full_hand_evaluation(cards)
        
        # Cache result
        if len(self.hand_evaluation_cache) < HAND_EVALUATION_CACHE_SIZE:
            self.hand_evaluation_cache[card_key] = hand_eval
        
        return hand_eval

    def full_hand_evaluation(self, cards: List[Card]) -> HandEvaluation:
        # Get all possible 5-card combinations
        from itertools import combinations
        
        best_hand = None
        best_rank = HandRank.HIGH_CARD
        best_value = 0
        best_cards = []
        
        for combo in combinations(cards, 5):
            hand_rank, hand_value, hand_cards = self.evaluate_5_card_hand(list(combo))
            
            if hand_rank > best_rank or (hand_rank == best_rank and hand_value > best_value):
                best_rank = hand_rank
                best_value = hand_value
                best_cards = hand_cards
                best_hand = combo
        
        return HandEvaluation(
            rank=best_rank,
            value=best_value,
            cards=list(best_hand) if best_hand else [],
            description=self.get_hand_description(best_rank, best_cards)
        )

    def evaluate_5_card_hand(self, cards: List[Card]) -> Tuple[HandRank, int, List[int]]:
        # Sort cards by value (descending)
        cards.sort(key=lambda x: x.value(), reverse=True)
        values = [c.value() for c in cards]
        suits = [c.suit for c in cards]
        
        # Check for flush
        is_flush = len(set(suits)) == 1
        
        # Check for straight
        is_straight = False
        if values == [14, 5, 4, 3, 2]:  # A-5 straight (wheel)
            is_straight = True
            values = [5, 4, 3, 2, 1]  # Treat ace as 1
        elif values[0] - values[4] == 4 and len(set(values)) == 5:
            is_straight = True
        
        # Count occurrences
        value_counts = Counter(values)
        counts = sorted(value_counts.values(), reverse=True)
        
        # Determine hand rank
        if is_straight and is_flush:
            if values[0] == 14:  # Royal flush
                return HandRank.ROYAL_FLUSH, values[0], values
            else:  # Straight flush
                return HandRank.STRAIGHT_FLUSH, values[0], values
        elif counts == [4, 1]:  # Four of a kind
            four_kind = [v for v, c in value_counts.items() if c == 4][0]
            kicker = [v for v, c in value_counts.items() if c == 1][0]
            return HandRank.FOUR_OF_A_KIND, four_kind * 1000 + kicker, [four_kind, kicker]
        elif counts == [3, 2]:  # Full house
            three_kind = [v for v, c in value_counts.items() if c == 3][0]
            pair = [v for v, c in value_counts.items() if c == 2][0]
            return HandRank.FULL_HOUSE, three_kind * 100 + pair, [three_kind, pair]
        elif is_flush:  # Flush
            return HandRank.FLUSH, sum(v * (10 ** i) for i, v in enumerate(reversed(values))), values
        elif is_straight:  # Straight
            return HandRank.STRAIGHT, values[0], values
        elif counts == [3, 1, 1]:  # Three of a kind
            three_kind = [v for v, c in value_counts.items() if c == 3][0]
            kickers = sorted([v for v, c in value_counts.items() if c == 1], reverse=True)
            return HandRank.THREE_OF_A_KIND, three_kind * 10000 + kickers[0] * 100 + kickers[1], [three_kind] + kickers
        elif counts == [2, 2, 1]:  # Two pair
            pairs = sorted([v for v, c in value_counts.items() if c == 2], reverse=True)
            kicker = [v for v, c in value_counts.items() if c == 1][0]
            return HandRank.TWO_PAIR, pairs[0] * 10000 + pairs[1] * 100 + kicker, pairs + [kicker]
        elif counts == [2, 1, 1, 1]:  # One pair
            pair = [v for v, c in value_counts.items() if c == 2][0]
            kickers = sorted([v for v, c in value_counts.items() if c == 1], reverse=True)
            return HandRank.PAIR, pair * 1000000 + sum(k * (100 ** i) for i, k in enumerate(reversed(kickers))), [pair] + kickers
        else:  # High card
            return HandRank.HIGH_CARD, sum(v * (10 ** i) for i, v in enumerate(reversed(values))), values

    def get_hand_description(self, rank: HandRank, cards: List[int]) -> str:
        card_names = {14: 'A', 13: 'K', 12: 'Q', 11: 'J'}
        
        def card_name(value):
            return card_names.get(value, str(value))
        
        if rank == HandRank.ROYAL_FLUSH:
            return "Royal Flush"
        elif rank == HandRank.STRAIGHT_FLUSH:
            return f"Straight Flush, {card_name(cards[0])} high"
        elif rank == HandRank.FOUR_OF_A_KIND:
            return f"Four of a Kind, {card_name(cards[0])}s"
        elif rank == HandRank.FULL_HOUSE:
            return f"Full House, {card_name(cards[0])}s over {card_name(cards[1])}s"
        elif rank == HandRank.FLUSH:
            return f"Flush, {card_name(cards[0])} high"
        elif rank == HandRank.STRAIGHT:
            return f"Straight, {card_name(cards[0])} high"
        elif rank == HandRank.THREE_OF_A_KIND:
            return f"Three of a Kind, {card_name(cards[0])}s"
        elif rank == HandRank.TWO_PAIR:
            return f"Two Pair, {card_name(cards[0])}s and {card_name(cards[1])}s"
        elif rank == HandRank.PAIR:
            return f"Pair of {card_name(cards[0])}s"
        else:
            return f"High Card, {card_name(cards[0])}"

    def distribute_winnings(self, room: Room, winners: Dict[str, HandEvaluation]):
        if not winners:
            return
        
        # Handle side pots first
        if room.side_pots:
            for side_pot in room.side_pots:
                eligible_winners = {pid: hand for pid, hand in winners.items() if pid in side_pot.eligible_players}
                if eligible_winners:
                    best_hand = max(eligible_winners.values(), key=lambda h: (h.rank, h.value))
                    pot_winners = [pid for pid, hand in eligible_winners.items() if hand.rank == best_hand.rank and hand.value == best_hand.value]
                    
                    winnings_per_player = side_pot.amount // len(pot_winners)
                    remainder = side_pot.amount % len(pot_winners)
                    
                    for i, winner_id in enumerate(pot_winners):
                        amount = winnings_per_player + (1 if i < remainder else 0)
                        room.players[winner_id].money += amount
                        room.players[winner_id].stats.total_winnings += amount
        else:
            # Main pot
            if room.pot > 0:
                best_hand = max(winners.values(), key=lambda h: (h.rank, h.value))
                pot_winners = [pid for pid, hand in winners.items() if hand.rank == best_hand.rank and hand.value == best_hand.value]
                
                winnings_per_player = room.pot // len(pot_winners)
                remainder = room.pot % len(pot_winners)
                
                for i, winner_id in enumerate(pot_winners):
                    amount = winnings_per_player + (1 if i < remainder else 0)
                    room.players[winner_id].money += amount
                    room.players[winner_id].stats.total_winnings += amount
                    room.players[winner_id].stats.hands_won += 1
                    
                    if amount > room.players[winner_id].stats.biggest_pot:
                        room.players[winner_id].stats.biggest_pot = amount
                    
                    if amount > self.global_stats['biggest_pot']:
                        self.global_stats['biggest_pot'] = amount

    def save_hand_history(self, room: Room):
        hand_data = {
            'hand_number': room.hand_number,
            'timestamp': datetime.now().isoformat(),
            'players': {pid: {
                'name': p.name,
                'position': p.position,
                'cards': [{'suit': c.suit, 'rank': c.rank} for c in p.cards] if p.cards else [],
                'actions': [],  # Would need to track actions during hand
                'final_money': p.money
            } for pid, p in room.players.items()},
            'community_cards': [{'suit': c.suit, 'rank': c.rank} for c in room.community_cards],
            'pot': room.pot,
            'winner': None  # Would need to track winner
        }
        
        room.hand_history.append(hand_data)
        
        # Keep only last 50 hands
        if len(room.hand_history) > 50:
            room.hand_history = room.hand_history[-50:]

    def update_tournament(self, room: Room):
        if room.settings.game_mode != GameMode.TOURNAMENT:
            return
        
        # Check if blinds should increase
        if datetime.now() >= room.tournament_next_level:
            room.tournament_level += 1
            room.settings.small_blind = int(room.settings.small_blind * 1.5)
            room.settings.big_blind = int(room.settings.big_blind * 1.5)
            room.tournament_next_level = datetime.now() + timedelta(seconds=TOURNAMENT_BLIND_INCREASE_INTERVAL)
            
            # Add break every 5 levels
            if room.tournament_level % 5 == 0:
                room.phase = GamePhase.TOURNAMENT_BREAK
                room.paused = True
                room.pause_reason = "Tournament break - 5 minutes"
                asyncio.create_task(self.resume_tournament_after_break(room.code))

    async def resume_tournament_after_break(self, room_code: str):
        await asyncio.sleep(300)  # 5 minute break
        if room_code in self.rooms:
            room = self.rooms[room_code]
            room.paused = False
            room.pause_reason = ""
            room.phase = GamePhase.WAITING

    def end_tournament(self, room: Room):
        # Rank players by money
        remaining_players = [p for p in room.players.values() if p.money > 0]
        eliminated_players = [p for p in room.players.values() if p.money <= 0]
        
        # Set final rankings
        for i, player in enumerate(sorted(remaining_players, key=lambda p: p.money, reverse=True)):
            player.tournament_rank = i + 1
        
        for i, player in enumerate(eliminated_players):
            player.tournament_rank = len(remaining_players) + i + 1

    async def auto_start_next_hand(self, room_code: str):
        await asyncio.sleep(5)  # 5 second delay
        if room_code in self.rooms:
            room = self.rooms[room_code]
            if room.phase == GamePhase.WAITING:
                self.start_game(room_code)

    def add_chat_message(self, room_code: str, player_id: str, message: str):
        if room_code not in self.rooms:
            return
        
        room = self.rooms[room_code]
        player_name = "Spectator"
        player_color = "#ffffff"
        
        if player_id in room.players:
            player = room.players[player_id]
            player_name = player.name
            player_color = player.color
        
        chat_msg = {
            "id": str(uuid.uuid4()),
            "player_id": player_id,
            "player_name": player_name,
            "player_color": player_color,
            "message": message,
            "timestamp": time.time(),
            "formatted_time": datetime.now().strftime("%H:%M:%S")
        }
        
        room.chat_messages.append(chat_msg)
        
        # Keep only last MAX_CHAT_MESSAGES
        if len(room.chat_messages) > MAX_CHAT_MESSAGES:
            room.chat_messages = room.chat_messages[-MAX_CHAT_MESSAGES:]
        
        room.update_activity()

    def check_rate_limit(self, player_id: str, limit_type: str = "message") -> bool:
        now = time.time()
        rate_limit_dict = self.rate_limits if limit_type == "message" else self.action_rate_limits
        max_per_second = RATE_LIMIT_MESSAGES_PER_SECOND if limit_type == "message" else RATE_LIMIT_ACTIONS_PER_SECOND
        
        rate_limit_dict[player_id] = [t for t in rate_limit_dict[player_id] if now - t < 1.0]
        
        if len(rate_limit_dict[player_id]) >= max_per_second:
            return False
        
        rate_limit_dict[player_id].append(now)
        return True

    def cleanup_inactive_rooms(self):
        current_time = datetime.now()
        rooms_to_delete = []
        
        for room_code, room in self.rooms.items():
            if current_time - room.last_activity > timedelta(seconds=SESSION_TIMEOUT):
                rooms_to_delete.append(room_code)
        
        for room_code in rooms_to_delete:
            logger.info(f"Cleaning up inactive room {room_code}")
            del self.rooms[room_code]

    def get_game_state(self, room_code: str, player_id: str) -> dict:
        if room_code not in self.rooms:
            return {}
        
        room = self.rooms[room_code]
        is_player = player_id in room.players
        is_spectator = player_id in room.spectators
        
        # Get current player
        active_players = room.get_active_players()
        current_player = None
        if active_players and 0 <= room.current_player_index < len(active_players):
            current_player = active_players[room.current_player_index]
        
        # Convert players to dict format
        players_data = {}
        for pid, player in room.players.items():
            player_data = {
                "id": player.id,
                "name": player.name,
                "money": player.money,
                "current_bet": player.current_bet,
                "total_bet_this_hand": player.total_bet_this_hand,
                "status": player.status.value,
                "position": player.position,
                "last_action": player.last_action.value if player.last_action else None,
                "avatar": player.avatar,
                "color": player.color,
                "is_dealer": player.is_dealer,
                "is_small_blind": player.is_small_blind,
                "is_big_blind": player.is_big_blind,
                "time_bank": player.time_bank,
                "is_current_player": current_player and current_player.id == pid,
                "tournament_rank": player.tournament_rank,
                "stats": {
                    "hands_played": player.stats.hands_played,
                    "hands_won": player.stats.hands_won,
                    "total_winnings": player.stats.total_winnings,
                    "biggest_pot": player.stats.biggest_pot
                }
            }
            
            # Only show cards to the player themselves, spectators in showdown, or all players in showdown
            show_cards = (pid == player_id or 
                         (is_spectator and room.phase == GamePhase.SHOWDOWN) or 
                         room.phase == GamePhase.SHOWDOWN)
            
            if show_cards and player.cards:
                player_data["cards"] = [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in player.cards]
            else:
                player_data["cards"] = [{"suit": "back", "rank": "back", "id": f"back_{i}"} for i in range(len(player.cards))]
            
            players_data[pid] = player_data
        
        # Game state
        game_state = {
            "room_code": room.code,
            "room_name": room.name,
            "phase": room.phase.value,
            "pot": room.pot,
            "current_bet": room.current_bet,
            "min_raise": room.min_raise,
            "current_player_index": room.current_player_index,
            "dealer_index": room.dealer_index,
            "players": players_data,
            "community_cards": [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in room.community_cards],
            "chat_messages": room.chat_messages[-20:],  # Last 20 messages
            "is_player": is_player,
            "is_spectator": is_spectator,
            "spectator_count": len(room.spectators),
            "hand_number": room.hand_number,
            "settings": {
                "small_blind": room.settings.small_blind,
                "big_blind": room.settings.big_blind,
                "ante": room.settings.ante,
                "max_players": room.settings.max_players,
                "game_mode": room.settings.game_mode.value,
                "auto_fold_timeout": room.settings.auto_fold_timeout
            },
            "tournament_info": {
                "level": room.tournament_level,
                "next_level_time": room.tournament_next_level.isoformat() if room.settings.game_mode == GameMode.TOURNAMENT else None
            } if room.settings.game_mode == GameMode.TOURNAMENT else None,
            "side_pots": [{"amount": sp.amount, "eligible_players": len(sp.eligible_players)} for sp in room.side_pots],
            "paused": room.paused,
            "pause_reason": room.pause_reason,
            "time_left": max(0, room.settings.auto_fold_timeout - (time.time() - room.last_action_time)) if current_player else 0,
            "can_act": is_player and current_player and current_player.id == player_id and room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER],
            "available_actions": self.get_available_actions(room, player_id) if is_player else []
        }
        
        return game_state

    def get_available_actions(self, room: Room, player_id: str) -> List[Dict]:
        if player_id not in room.players:
            return []
        
        player = room.players[player_id]
        if not player.can_act():
            return []
        
        actions = []
        
        # Fold (always available)
        actions.append({"action": "fold", "label": "Fold"})
        
        # Check/Call
        if room.current_bet == player.current_bet:
            actions.append({"action": "check", "label": "Check"})
        else:
            call_amount = min(room.current_bet - player.current_bet, player.money)
            if call_amount > 0:
                actions.append({"action": "call", "label": f"Call ${call_amount}", "amount": call_amount})
        
        # Raise (if player has enough money)
        if player.money > room.current_bet - player.current_bet:
            min_raise_amount = room.min_raise
            max_raise_amount = player.money - (room.current_bet - player.current_bet)
            actions.append({
                "action": "raise", 
                "label": "Raise", 
                "min_amount": min_raise_amount,
                "max_amount": max_raise_amount
            })
        
        # All-in (if player has money)
        if player.money > 0:
            actions.append({"action": "all_in", "label": f"All-In ${player.money}", "amount": player.money})
        
        return actions

    def get_room_list(self) -> List[Dict]:
        rooms = []
        for room_code, room in self.rooms.items():
            if room.room_type == RoomType.PUBLIC:
                rooms.append({
                    "code": room_code,
                    "name": room.name,
                    "players": len(room.players),
                    "max_players": room.settings.max_players,
                    "spectators": len(room.spectators),
                    "phase": room.phase.value,
                    "game_mode": room.settings.game_mode.value,
                    "small_blind": room.settings.small_blind,
                    "big_blind": room.settings.big_blind,
                    "created_at": room.created_at.isoformat(),
                    "has_password": bool(room.settings.password)
                })
        return rooms

# Global game instance
game = AdvancedPokerGame()

# WebSocket message models
class WSMessage(BaseModel):
    action: str
    payload: dict = Field(default_factory=dict)

class CreateRoomRequest(BaseModel):
    player_name: str = "Anonymous"
    room_name: str = ""
    game_mode: str = "cash_game"
    small_blind: int = SMALL_BLIND
    big_blind: int = BIG_BLIND
    max_players: int = MAX_PLAYERS_PER_ROOM
    buy_in: int = 0
    password: str = ""

class JoinRoomRequest(BaseModel):
    room_code: str
    player_name: str = "Anonymous"
    password: str = ""

# FastAPI app with lifespan
@asynccontextmanager
async def lifespan(app: FastAPI):
    # Startup
    logger.info("Starting advanced poker game server...")
    
    # Start background tasks
    game_task = asyncio.create_task(game_loop())
    cleanup_task = asyncio.create_task(cleanup_loop())
    
    yield
    
    # Shutdown
    logger.info("Shutting down poker game server...")
    game.running = False
    
    # Cancel tasks
    game_task.cancel()
    cleanup_task.cancel()
    
    try:
        await game_task
        await cleanup_task
    except asyncio.CancelledError:
        pass

app = FastAPI(
    title="Advanced 3D Multiplayer Poker",
    description="Professional casino-quality poker game with 3D graphics",
    version="2.0.0",
    lifespan=lifespan
)

# Add CORS middleware
app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

async def game_loop():
    """Advanced game loop with 60 FPS updates and auto-fold handling"""
    while game.running:
        try:
            current_time = time.time()
            
            # Check for auto-fold timeouts
            for room_code, room in list(game.rooms.items()):
                if room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER] and not room.paused:
                    active_players = room.get_active_players()
                    if active_players and 0 <= room.current_player_index < len(active_players):
                        current_player = active_players[room.current_player_index]
                        
                        # Auto-fold if timeout exceeded
                        if current_time - room.last_action_time > room.settings.auto_fold_timeout:
                            logger.info(f"Auto-folding player {current_player.name} in room {room_code}")
                            game.player_action(room_code, current_player.id, PlayerAction.FOLD)
            
            # Broadcast game state to all connected clients
            for room_code, room in list(game.rooms.items()):
                if room.players or room.spectators:
                    # Get all connected users in this room
                    room_users = set()
                    for player_id in room.players.keys():
                        if player_id in game.connections:
                            room_users.add(player_id)
                    for spectator_id in room.spectators:
                        if spectator_id in game.connections:
                            room_users.add(spectator_id)
                    
                    # Broadcast to each user
                    for user_id in list(room_users):
                        if user_id in game.connections:
                            try:
                                game_state = game.get_game_state(room_code, user_id)
                                await game.connections[user_id].send_json({
                                    "type": "game_state",
                                    "data": game_state
                                })
                            except Exception as e:
                                logger.error(f"Error broadcasting to {user_id}: {e}")
                                # Remove broken connection
                                if user_id in game.connections:
                                    del game.connections[user_id]
                                game.leave_room(user_id)
            
            await asyncio.sleep(1.0 / GAME_UPDATE_RATE)  # 60 FPS
        except Exception as e:
            logger.error(f"Error in game loop: {e}")
            await asyncio.sleep(1.0)

async def cleanup_loop():
    """Background task to clean up inactive rooms and connections"""
    while game.running:
        try:
            game.cleanup_inactive_rooms()
            await asyncio.sleep(300)  # Run every 5 minutes
        except Exception as e:
            logger.error(f"Error in cleanup loop: {e}")
            await asyncio.sleep(60)

@app.get("/", response_class=HTMLResponse)
async def get_poker_game():
    return HTMLResponse(content=ADVANCED_HTML_TEMPLATE)

@app.get("/api/rooms")
async def get_rooms():
    return {"rooms": game.get_room_list()}

@app.get("/api/stats")
async def get_stats():
    return {
        "global_stats": game.global_stats,
        "active_rooms": len(game.rooms),
        "connected_players": len(game.connections)
    }

@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    await websocket.accept()
    player_id = str(uuid.uuid4())
    game.connections[player_id] = websocket
    
    try:
        # Send welcome message
        await websocket.send_json({
            "type": "connected",
            "data": {
                "player_id": player_id,
                "server_info": {
                    "version": "2.0.0",
                    "features": ["tournaments", "side_pots", "advanced_graphics", "hand_history"]
                }
            }
        })
        
        while True:
            data = await websocket.receive_text()
            
            # Rate limiting
            if not game.check_rate_limit(player_id, "message"):
                await websocket.send_json({"type": "error", "message": "Rate limit exceeded"})
                continue
            
            try:
                message = WSMessage.model_validate_json(data)
                await handle_websocket_message(websocket, player_id, message)
            except ValidationError as e:
                await websocket.send_json({"type": "error", "message": f"Invalid message format: {e}"})
            except Exception as e:
                logger.error(f"Error handling message: {e}")
                await websocket.send_json({"type": "error", "message": "Internal server error"})
                
    except WebSocketDisconnect:
        logger.info(f"Player {player_id} disconnected")
    except Exception as e:
        logger.error(f"WebSocket error: {e}")
    finally:
        # Cleanup
        if player_id in game.connections:
            del game.connections[player_id]
        game.leave_room(player_id)

async def handle_websocket_message(websocket: WebSocket, player_id: str, message: WSMessage):
    action = message.action
    payload = message.payload
    
    try:
        if action == "create_room":
            # Parse create room request
            room_settings = GameSettings(
                small_blind=payload.get("small_blind", SMALL_BLIND),
                big_blind=payload.get("big_blind", BIG_BLIND),
                max_players=min(payload.get("max_players", MAX_PLAYERS_PER_ROOM), MAX_PLAYERS_PER_ROOM),
                game_mode=GameMode(payload.get("game_mode", "cash_game")),
                buy_in=payload.get("buy_in", 0),
                password=payload.get("password") if payload.get("password") else None
            )
            
            room_code = game.create_room(player_id, room_settings, payload.get("room_name", ""))
            player_name = payload.get("player_name", f"Player_{player_id[:8]}")
            
            if game.join_room(room_code, player_id, player_name):
                await websocket.send_json({
                    "type": "room_created",
                    "data": {"room_code": room_code, "room_name": game.rooms[room_code].name}
                })
            else:
                await websocket.send_json({"type": "error", "message": "Failed to join created room"})
        
        elif action == "join_room":
            room_code = payload.get("room_code", "").upper()
            player_name = payload.get("player_name", f"Player_{player_id[:8]}")
            password = payload.get("password", "")
            
            if game.join_room(room_code, player_id, player_name, password):
                await websocket.send_json({
                    "type": "room_joined",
                    "data": {"room_code": room_code}
                })
            else:
                await websocket.send_json({
                    "type": "error",
                    "message": "Failed to join room. Check room code and password."
                })
        
        elif action == "leave_room":
            game.leave_room(player_id)
            await websocket.send_json({"type": "room_left"})
        
        elif action == "spectate":
            room_code = payload.get("room_code", "").upper()
            password = payload.get("password", "")
            
            if game.spectate_room(room_code, player_id, password):
                await websocket.send_json({
                    "type": "spectating",
                    "data": {"room_code": room_code}
                })
            else:
                await websocket.send_json({
                    "type": "error",
                    "message": "Failed to spectate room"
                })
        
        elif action == "start_game":
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]
                if game.start_game(room_code):
                    await websocket.send_json({"type": "game_started"})
                else:
                    await websocket.send_json({"type": "error", "message": "Cannot start game"})
        
        elif action == "player_action":
            if not game.check_rate_limit(player_id, "action"):
                await websocket.send_json({"type": "error", "message": "Action rate limit exceeded"})
                return
                
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]
                action_type = payload.get("action_type")
                amount = payload.get("amount", 0)
                
                try:
                    poker_action = PlayerAction(action_type)
                    if game.player_action(room_code, player_id, poker_action, amount):
                        await websocket.send_json({"type": "action_accepted"})
                    else:
                        await websocket.send_json({"type": "error", "message": "Invalid action"})
                except ValueError:
                    await websocket.send_json({
                        "type": "error",
                        "message": "Invalid action type"
                    })
        
        elif action == "send_chat":
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]
                message_text = payload.get("message", "")
                if message_text.strip() and len(message_text) <= 200:
                    game.add_chat_message(room_code, player_id, message_text.strip())
        
        elif action == "get_room_list":
            rooms = game.get_room_list()
            await websocket.send_json({
                "type": "room_list",
                "data": {"rooms": rooms}
            })
        
        elif action == "get_hand_history":
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]
                room = game.rooms[room_code]
                await websocket.send_json({
                    "type": "hand_history",
                    "data": {"history": room.hand_history[-10:]}  # Last 10 hands
                })
        
        elif action == "pause_game":
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]
                room = game.rooms[room_code]
                if room.owner_id == player_id:
                    room.paused = not room.paused
                    room.pause_reason = "Paused by room owner" if room.paused else ""
                    await websocket.send_json({"type": "game_paused" if room.paused else "game_resumed"})
        
        elif action == "kick_player":
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]
                room = game.rooms[room_code]
                target_player_id = payload.get("target_player_id")
                
                if room.owner_id == player_id and target_player_id in room.players:
                    game.leave_room(target_player_id, force=True)
                    await websocket.send_json({"type": "player_kicked"})
        
        else:
            await websocket.send_json({"type": "error", "message": "Unknown action"})
            
    except Exception as e:
        logger.error(f"Error in handle_websocket_message: {e}")
        await websocket.send_json({"type": "error", "message": "Server error processing request"})

# Advanced HTML Template with stunning 3D graphics and animations
ADVANCED_HTML_TEMPLATE = """
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>🎰 Royal Poker 3D - Professional Casino Experience</title>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js"></script>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/gsap/3.12.2/gsap.min.js"></script>
    <link href="https://fonts.googleapis.com/css2?family=Orbitron:wght@400;700;900&family=Roboto:wght@300;400;500;700&display=swap" rel="stylesheet">
    <style>
        :root {
            --primary-gold: #ffd700;
            --secondary-gold: #ffed4e;
            --dark-green: #0a2a1f;
            --light-green: #1a5d3a;
            --casino-red: #dc143c;
            --casino-blue: #191970;
            --text-light: #ffffff;
            --text-dark: #333333;
            --shadow: rgba(0, 0, 0, 0.3);
        }

        * {
            margin: 0;
            padding: 0;
            box-sizing: border-box;
        }

        body {
            font-family: 'Roboto', sans-serif;
            background: radial-gradient(ellipse at center, #0a2a1f 0%, #051a11 100%);
            color: var(--text-light);
            overflow: hidden;
            user-select: none;
        }

        #gameContainer {
            position: relative;
            width: 100vw;
            height: 100vh;
        }

        #canvas {
            display: block;
            cursor: grab;
        }

        #canvas:active {
            cursor: grabbing;
        }

        /* Loading Screen */
        #loadingScreen {
            position: fixed;
            top: 0;
            left: 0;
            width: 100%;
            height: 100%;
            background: linear-gradient(135deg, #0a2a1f, #051a11);
            display: flex;
            flex-direction: column;
            justify-content: center;
            align-items: center;
            z-index: 10000;
            transition: opacity 1s ease-out;
        }

        .loading-logo {
            font-family: 'Orbitron', monospace;
            font-size: 4rem;
            font-weight: 900;
            color: var(--primary-gold);
            text-shadow: 0 0 30px rgba(255, 215, 0, 0.8);
            margin-bottom: 30px;
            animation: pulse 2s infinite;
        }

        .loading-spinner {
            width: 80px;
            height: 80px;
            border: 4px solid rgba(255, 215, 0, 0.3);
            border-top: 4px solid var(--primary-gold);
            border-radius: 50%;
            animation: spin 1s linear infinite;
            margin-bottom: 20px;
        }

        .loading-text {
            font-size: 1.2rem;
            color: var(--text-light);
            opacity: 0.8;
        }

        @keyframes pulse {
            0%, 100% { transform: scale(1); }
            50% { transform: scale(1.05); }
        }

        @keyframes spin {
            0% { transform: rotate(0deg); }
            100% { transform: rotate(360deg); }
        }

        /* UI Overlay */
        .ui-overlay {
            position: absolute;
            top: 0;
            left: 0;
            width: 100%;
            height: 100%;
            pointer-events: none;
            z-index: 100;
        }

        .ui-panel {
            position: absolute;
            background: linear-gradient(135deg, rgba(0, 0, 0, 0.9), rgba(26, 93, 58, 0.8));
            border-radius: 15px;
            padding: 20px;
            color: var(--text-light);
            pointer-events: auto;
            border: 2px solid var(--primary-gold);
            box-shadow: 0 10px 30px var(--shadow);
            backdrop-filter: blur(10px);
            transition: all 0.3s ease;
        }

        .ui-panel:hover {
            transform: translateY(-2px);
            box-shadow: 0 15px 40px var(--shadow);
        }

        /* Main Menu */
        .menu-panel {
            top: 50%;
            left: 50%;
            transform: translate(-50%, -50%);
            text-align: center;
            min-width: 400px;
            max-width: 90vw;
        }

        .menu-title {
            font-family: 'Orbitron', monospace;
            font-size: 3rem;
            font-weight: 900;
            color: var(--primary-gold);
            text-shadow: 0 0 20px rgba(255, 215, 0, 0.8);
            margin-bottom: 30px;
            animation: glow 2s ease-in-out infinite alternate;
        }

        @keyframes glow {
            from { text-shadow: 0 0 20px rgba(255, 215, 0, 0.8); }
            to { text-shadow: 0 0 30px rgba(255, 215, 0, 1), 0 0 40px rgba(255, 215, 0, 0.8); }
        }

        .menu-section {
            margin-bottom: 25px;
            padding: 20px;
            background: rgba(255, 255, 255, 0.05);
            border-radius: 10px;
            border: 1px solid rgba(255, 215, 0, 0.3);
        }

        .menu-section h3 {
            color: var(--secondary-gold);
            margin-bottom: 15px;
            font-size: 1.2rem;
        }

        /* Game HUD */
        .game-hud {
            top: 20px;
            left: 20px;
            max-width: 350px;
        }

        .hud-item {
            display: flex;
            justify-content: space-between;
            align-items: center;
            margin-bottom: 10px;
            padding: 8px 12px;
            background: rgba(255, 255, 255, 0.1);
            border-radius: 8px;
            border-left: 4px solid var(--primary-gold);
        }

        .hud-label {
            font-weight: 500;
            color: var(--secondary-gold);
        }

        .hud-value {
            font-weight: 700;
            color: var(--text-light);
        }

        /* Pot Display */
        .pot-display {
            position: absolute;
            top: 15%;
            left: 50%;
            transform: translateX(-50%);
            background: radial-gradient(circle, rgba(255, 215, 0, 0.9), rgba(255, 237, 78, 0.7));
            color: var(--text-dark);
            padding: 25px;
            border-radius: 50%;
            border: 4px solid var(--primary-gold);
            font-family: 'Orbitron', monospace;
            font-size: 1.8rem;
            font-weight: 900;
            text-align: center;
            min-width: 150px;
            min-height: 150px;
            display: flex;
            flex-direction: column;
            justify-content: center;
            align-items: center;
            box-shadow: 0 0 40px rgba(255, 215, 0, 0.6);
            animation: potGlow 3s ease-in-out infinite;
        }

        @keyframes potGlow {
            0%, 100% { box-shadow: 0 0 40px rgba(255, 215, 0, 0.6); }
            50% { box-shadow: 0 0 60px rgba(255, 215, 0, 0.9); }
        }

        /* Action Buttons */
        .actions-panel {
            bottom: 30px;
            left: 50%;
            transform: translateX(-50%);
            display: flex;
            gap: 15px;
            flex-wrap: wrap;
            justify-content: center;
            max-width: 90vw;
        }

        .action-button {
            background: linear-gradient(135deg, var(--primary-gold), var(--secondary-gold));
            border: none;
            border-radius: 12px;
            padding: 15px 25px;
            color: var(--text-dark);
            font-weight: 700;
            font-size: 1rem;
            cursor: pointer;
            transition: all 0.3s ease;
            box-shadow: 0 5px 15px rgba(255, 215, 0, 0.3);
            position: relative;
            overflow: hidden;
        }

        .action-button:hover {
            transform: translateY(-3px);
            box-shadow: 0 8px 25px rgba(255, 215, 0, 0.5);
        }

        .action-button:active {
            transform: translateY(-1px);
        }

        .action-button:disabled {
            background: linear-gradient(135deg, #666, #888);
            cursor: not-allowed;
            transform: none;
            opacity: 0.5;
        }

        .action-button.fold {
            background: linear-gradient(135deg, var(--casino-red), #ff6b6b);
        }

        .action-button.call {
            background: linear-gradient(135deg, #28a745, #20c997);
        }

        .action-button.raise {
            background: linear-gradient(135deg, var(--casino-blue), #6c5ce7);
        }

        .action-button.all-in {
            background: linear-gradient(135deg, #ff4757, #ff3742);
            animation: allInPulse 1s infinite;
        }

        @keyframes allInPulse {
            0%, 100% { box-shadow: 0 5px 15px rgba(255, 71, 87, 0.3); }
            50% { box-shadow: 0 5px 25px rgba(255, 71, 87, 0.6); }
        }

        /* Raise Controls */
        .raise-controls {
            display: flex;
            align-items: center;
            gap: 10px;
            background: rgba(255, 255, 255, 0.1);
            padding: 10px;
            border-radius: 8px;
        }

        .raise-slider {
            flex: 1;
            -webkit-appearance: none;
            appearance: none;
            height: 8px;
            background: rgba(255, 255, 255, 0.3);
            border-radius: 4px;
            outline: none;
        }

        .raise-slider::-webkit-slider-thumb {
            -webkit-appearance: none;
            appearance: none;
            width: 20px;
            height: 20px;
            background: var(--primary-gold);
            border-radius: 50%;
            cursor: pointer;
        }

        /* Chat Panel */
        .chat-panel {
            top: 20px;
            right: 20px;
            width: 320px;
            height: 400px;
            display: flex;
            flex-direction: column;
        }

        .chat-header {
            display: flex;
            justify-content: space-between;
            align-items: center;
            margin-bottom: 15px;
            padding-bottom: 10px;
            border-bottom: 2px solid var(--primary-gold);
        }

        .chat-title {
            font-family: 'Orbitron', monospace;
            font-weight: 700;
            color: var(--primary-gold);
        }

        .chat-toggle {
            background: none;
            border: 2px solid var(--primary-gold);
            color: var(--primary-gold);
            border-radius: 6px;
            padding: 5px 10px;
            cursor: pointer;
            transition: all 0.3s ease;
        }

        .chat-toggle:hover {
            background: var(--primary-gold);
            color: var(--text-dark);
        }

        #chatMessages {
            flex: 1;
            overflow-y: auto;
            background: rgba(255, 255, 255, 0.05);
            border-radius: 8px;
            padding: 15px;
            margin-bottom: 15px;
            border: 1px solid rgba(255, 215, 0, 0.2);
        }

        .chat-message {
            margin-bottom: 10px;
            padding: 8px 12px;
            border-radius: 8px;
            background: rgba(255, 255, 255, 0.1);
            border-left: 3px solid;
            animation: slideInChat 0.3s ease-out;
        }

        @keyframes slideInChat {
            from { opacity: 0; transform: translateX(20px); }
            to { opacity: 1; transform: translateX(0); }
        }

        .chat-player-name {
            font-weight: 700;
            margin-right: 8px;
        }

        .chat-timestamp {
            font-size: 0.8rem;
            opacity: 0.6;
            float: right;
        }

        .chat-input-container {
            display: flex;
            gap: 10px;
        }

        /* Player Info Cards */
        .player-cards {
            position: absolute;
            bottom: 100px;
            left: 50%;
            transform: translateX(-50%);
            display: flex;
            gap: 20px;
            flex-wrap: wrap;
            justify-content: center;
            max-width: 90vw;
        }

        .player-card {
            background: linear-gradient(135deg, rgba(26, 93, 58, 0.9), rgba(10, 42, 31, 0.9));
            border: 2px solid var(--primary-gold);
            border-radius: 15px;
            padding: 15px;
            text-align: center;
            min-width: 150px;
            position: relative;
            transition: all 0.3s ease;
            backdrop-filter: blur(10px);
        }

        .player-card.current-player {
            border-color: var(--casino-red);
            box-shadow: 0 0 30px rgba(220, 20, 60, 0.6);
            animation: currentPlayerGlow 2s ease-in-out infinite;
        }

        @keyframes currentPlayerGlow {
            0%, 100% { box-shadow: 0 0 30px rgba(220, 20, 60, 0.6); }
            50% { box-shadow: 0 0 40px rgba(220, 20, 60, 0.9); }
        }

        .player-card.folded {
            opacity: 0.4;
            filter: grayscale(80%);
        }

        .player-card.all-in {
            border-color: var(--casino-red);
            animation: allInGlow 1s ease-in-out infinite;
        }

        @keyframes allInGlow {
            0%, 100% { box-shadow: 0 0 20px rgba(255, 71, 87, 0.4); }
            50% { box-shadow: 0 0 30px rgba(255, 71, 87, 0.7); }
        }

        .player-avatar {
            width: 50px;
            height: 50px;
            border-radius: 50%;
            background: var(--primary-gold);
            margin: 0 auto 10px;
            display: flex;
            align-items: center;
            justify-content: center;
            font-size: 1.5rem;
            font-weight: 700;
            color: var(--text-dark);
        }

        .player-name {
            font-weight: 700;
            color: var(--text-light);
            margin-bottom: 5px;
        }

        .player-money {
            color: var(--primary-gold);
            font-weight: 700;
            font-family: 'Orbitron', monospace;
        }

        .player-action {
            position: absolute;
            top: -10px;
            right: -10px;
            background: var(--casino-red);
            color: var(--text-light);
            padding: 4px 8px;
            border-radius: 12px;
            font-size: 0.8rem;
            font-weight: 700;
            animation: actionPop 0.5s ease-out;
        }

        @keyframes actionPop {
            0% { transform: scale(0); }
            80% { transform: scale(1.2); }
            100% { transform: scale(1); }
        }

        /* Input Styles */
        input {
            padding: 12px 15px;
            border: 2px solid var(--primary-gold);
            border-radius: 8px;
            background: rgba(255, 255, 255, 0.1);
            color: var(--text-light);
            font-size: 1rem;
            transition: all 0.3s ease;
            backdrop-filter: blur(10px);
        }

        input:focus {
            outline: none;
            border-color: var(--secondary-gold);
            box-shadow: 0 0 15px rgba(255, 215, 0, 0.3);
        }

        input::placeholder {
            color: rgba(255, 255, 255, 0.6);
        }

        /* Scrollbar Styles */
        ::-webkit-scrollbar {
            width: 8px;
        }

        ::-webkit-scrollbar-track {
            background: rgba(255, 255, 255, 0.1);
            border-radius: 4px;
        }

        ::-webkit-scrollbar-thumb {
            background: var(--primary-gold);
            border-radius: 4px;
        }

        ::-webkit-scrollbar-thumb:hover {
            background: var(--secondary-gold);
        }

        /* Responsive Design */
        @media (max-width: 768px) {
            .menu-panel {
                min-width: 300px;
                padding: 15px;
            }

            .menu-title {
                font-size: 2rem;
            }

            .chat-panel {
                width: 280px;
                height: 300px;
            }

            .actions-panel {
                bottom: 20px;
                gap: 10px;
            }

            .action-button {
                padding: 12px 18px;
                font-size: 0.9rem;
            }

            .player-cards {
                bottom: 80px;
                gap: 10px;
            }

            .player-card {
                min-width: 120px;
                padding: 10px;
            }
        }

        /* Utility Classes */
        .hidden {
            display: none !important;
        }

        .fade-in {
            animation: fadeIn 0.5s ease-out;
        }

        .fade-out {
            animation: fadeOut 0.5s ease-out;
        }

        @keyframes fadeIn {
            from { opacity: 0; }
            to { opacity: 1; }
        }

        @keyframes fadeOut {
            from { opacity: 1; }
            to { opacity: 0; }
        }

        .slide-up {
            animation: slideUp 0.5s ease-out;
        }

        @keyframes slideUp {
            from { transform: translateY(20px); opacity: 0; }
            to { transform: translateY(0); opacity: 1; }
        }

        /* Tournament Display */
        .tournament-info {
            position: absolute;
            top: 20px;
            left: 50%;
            transform: translateX(-50%);
            background: linear-gradient(135deg, rgba(25, 25, 112, 0.9), rgba(138, 43, 226, 0.8));
            border: 2px solid var(--primary-gold);
            border-radius: 10px;
            padding: 15px 25px;
            text-align: center;
            backdrop-filter: blur(10px);
        }

        .tournament-level {
            font-family: 'Orbitron', monospace;
            font-size: 1.2rem;
            font-weight: 700;
            color: var(--primary-gold);
            margin-bottom: 5px;
        }

        .tournament-timer {
            color: var(--text-light);
            font-size: 0.9rem;
        }

        /* Notification System */
        .notification {
            position: fixed;
            top: 20px;
            right: 20px;
            background: linear-gradient(135deg, rgba(40, 167, 69, 0.9), rgba(32, 201, 151, 0.9));
            color: var(--text-light);
            padding: 15px 20px;
            border-radius: 8px;
            border-left: 4px solid var(--primary-gold);
            box-shadow: 0 5px 15px var(--shadow);
            z-index: 9999;
            animation: slideInNotification 0.5s ease-out;
            max-width: 300px;
        }

        .notification.error {
            background: linear-gradient(135deg, rgba(220, 20, 60, 0.9), rgba(255, 107, 107, 0.9));
        }

        .notification.warning {
            background: linear-gradient(135deg, rgba(255, 193, 7, 0.9), rgba(255, 235, 59, 0.9));
            color: var(--text-dark);
        }

        @keyframes slideInNotification {
            from { transform: translateX(100%); opacity: 0; }
            to { transform: translateX(0); opacity: 1; }
        }

        /* Hand History Modal */
        .modal {
            position: fixed;
            top: 0;
            left: 0;
            width: 100%;
            height: 100%;
            background: rgba(0, 0, 0, 0.8);
            display: flex;
            justify-content: center;
            align-items: center;
            z-index: 9999;
        }

        .modal-content {
            background: linear-gradient(135deg, rgba(10, 42, 31, 0.95), rgba(26, 93, 58, 0.95));
            border: 2px solid var(--primary-gold);
            border-radius: 15px;
            padding: 30px;
            max-width: 80vw;
            max-height: 80vh;
            overflow-y: auto;
            backdrop-filter: blur(15px);
        }

        .modal-header {
            display: flex;
            justify-content: space-between;
            align-items: center;
            margin-bottom: 20px;
            padding-bottom: 15px;
            border-bottom: 2px solid var(--primary-gold);
        }

        .modal-title {
            font-family: 'Orbitron', monospace;
            font-size: 1.5rem;
            font-weight: 700;
            color: var(--primary-gold);
        }

        .modal-close {
            background: none;
            border: 2px solid var(--casino-red);
            color: var(--casino-red);
            border-radius: 6px;
            padding: 8px 15px;
            cursor: pointer;
            font-weight: 700;
            transition: all 0.3s ease;
        }

        .modal-close:hover {
            background: var(--casino-red);
            color: var(--text-light);
        }
    </style>
</head>
<body>
    <!-- Loading Screen -->
    <div id="loadingScreen">
        <div class="loading-logo">🎰 ROYAL POKER 3D</div>
        <div class="loading-spinner"></div>
        <div class="loading-text">Loading casino experience...</div>
    </div>

    <div id="gameContainer">
        <canvas id="canvas"></canvas>
        
        <div class="ui-overlay">
            <!-- Main Menu -->
            <div id="menuPanel" class="ui-panel menu-panel hidden">
                <h1 class="menu-title">🎰 ROYAL POKER 3D 🎰</h1>
                
                <div class="menu-section">
                    <h3>Player Setup</h3>
                    <input type="text" id="playerName" placeholder="Enter your name" value="Player" style="width: 100%; margin-bottom: 15px;">
                </div>
                
                <div class="menu-section">
                    <h3>Quick Play</h3>
                    <div style="display: flex; flex-direction: column; gap: 15px;">
                        <button class="action-button" onclick="createQuickRoom()">🎯 Create Quick Room</button>
                        <div style="display: flex; gap: 10px;">
                            <input type="text" id="roomCode" placeholder="Room Code" style="flex: 1;">
                            <button class="action-button" onclick="joinRoom()">🚪 Join Room</button>
                        </div>
                        <button class="action-button" onclick="spectateRoom()">👁️ Spectate Room</button>
                    </div>
                </div>
                
                <div class="menu-section">
                    <h3>Custom Game</h3>
                    <div style="display: grid; grid-template-columns: 1fr 1fr; gap: 10px; margin-bottom: 15px;">
                        <div>
                            <label>Game Mode:</label>
                            <select id="gameMode" style="width: 100%; padding: 8px; border-radius: 5px; background: rgba(255,255,255,0.1); color: white; border: 1px solid var(--primary-gold);">
                                <option value="cash_game">Cash Game</option>
                                <option value="tournament">Tournament</option>
                                <option value="sit_and_go">Sit & Go</option>
                            </select>
                        </div>
                        <div>
                            <label>Max Players:</label>
                            <input type="number" id="maxPlayers" min="2" max="10" value="8" style="width: 100%;">
                        </div>
                        <div>
                            <label>Small Blind:</label>
                            <input type="number" id="smallBlind" min="1" value="25" style="width: 100%;">
                        </div>
                        <div>
                            <label>Big Blind:</label>
                            <input type="number" id="bigBlind" min="2" value="50" style="width: 100%;">
                        </div>
                        <div>
                            <label>Buy-in:</label>
                            <input type="number" id="buyIn" min="0" value="1000" style="width: 100%;">
                        </div>
                        <div>
                            <label>Password (Optional):</label>
                            <input type="password" id="roomPassword" placeholder="Leave empty for public" style="width: 100%;">
                        </div>
                    </div>
                    <input type="text" id="roomName" placeholder="Room Name (Optional)" style="width: 100%; margin-bottom: 15px;">
                    <button class="action-button" onclick="createCustomRoom()">🎪 Create Custom Room</button>
                </div>
                
                <div class="menu-section">
                    <h3>Browse Rooms</h3>
                    <button class="action-button" onclick="showRoomList()">🏛️ Browse Public Rooms</button>
                </div>
                
                <div style="margin-top: 20px; font-size: 14px; color: #ccc; text-align: center;">
                    💰 Starting money: $1,000 | 🎯 Blinds: $25/$50<br>
                    🏆 Tournament mode available | 👥 Up to 10 players
                </div>
            </div>

            <!-- Room List Modal -->
            <div id="roomListModal" class="modal hidden">
                <div class="modal-content">
                    <div class="modal-header">
                        <h2 class="modal-title">🏛️ Public Rooms</h2>
                        <button class="modal-close" onclick="hideRoomList()">✕</button>
                    </div>
                    <div id="roomList" style="max-height: 400px; overflow-y: auto;">
                        <div style="text-align: center; color: #ccc; padding: 20px;">
                            Loading rooms...
                        </div>
                    </div>
                    <div style="margin-top: 20px; text-align: center;">
                        <button class="action-button" onclick="refreshRoomList()">🔄 Refresh</button>
                    </div>
                </div>
            </div>

            <!-- Game HUD -->
            <div id="gameHUD" class="ui-panel game-hud hidden">
                <div class="hud-item">
                    <span class="hud-label">🏠 Room:</span>
                    <span class="hud-value" id="currentRoom">-</span>
                </div>
                <div class="hud-item">
                    <span class="hud-label">🎮 Phase:</span>
                    <span class="hud-value" id="phaseText">Waiting</span>
                </div>
                <div class="hud-item">
                    <span class="hud-label">💰 Money:</span>
                    <span class="hud-value">$<span id="moneyAmount">1000</span></span>
                </div>
                <div class="hud-item">
                    <span class="hud-label">🎯 Current Bet:</span>
                    <span class="hud-value">$<span id="betAmount">0</span></span>
                </div>
                <div class="hud-item">
                    <span class="hud-label">🃏 Hand:</span>
                    <span class="hud-value" id="handNumber">0</span>
                </div>
                <div style="margin-top: 20px; display: flex; flex-direction: column; gap: 10px;">
                    <button class="action-button" onclick="startGame()" id="startGameBtn" style="width: 100%;">🚀 Start Game</button>
                    <button class="action-button" onclick="showHandHistory()" style="width: 100%;">📊 Hand History</button>
                    <button class="action-button" onclick="pauseGame()" id="pauseGameBtn" style="width: 100%;">⏸️ Pause Game</button>
                    <button class="action-button fold" onclick="leaveRoom()" style="width: 100%;">🚪 Leave Room</button>
                </div>
            </div>

            <!-- Tournament Info -->
            <div id="tournamentInfo" class="tournament-info hidden">
                <div class="tournament-level">🏆 Level <span id="tournamentLevel">1</span></div>
                <div class="tournament-timer">Next level in: <span id="tournamentTimer">10:00</span></div>
                <div style="margin-top: 5px; font-size: 0.8rem;">
                    Blinds: $<span id="tournamentBlinds">25/50</span>
                </div>
            </div>

            <!-- Pot Display -->
            <div id="potDisplay" class="pot-display hidden">
                <div style="font-size: 1rem; margin-bottom: 5px;">💰 POT</div>
                <div>$<span id="potAmount">0</span></div>
                <div id="sidePots" style="font-size: 0.8rem; margin-top: 5px; color: rgba(0,0,0,0.7);"></div>
            </div>

            <!-- Action Timer -->
            <div id="actionTimer" class="hidden" style="position: absolute; top: 25%; left: 50%; transform: translateX(-50%); background: rgba(220, 20, 60, 0.9); color: white; padding: 10px 20px; border-radius: 25px; font-family: 'Orbitron', monospace; font-weight: 700; font-size: 1.2rem; animation: timerPulse 1s infinite;">
                ⏰ <span id="timerSeconds">30</span>s
            </div>

            <!-- Action Buttons -->
            <div id="actionsPanel" class="actions-panel hidden">
                <button class="action-button fold" onclick="playerAction('fold')" id="foldBtn">
                    🚫 Fold
                </button>
                <button class="action-button" onclick="playerAction('check')" id="checkBtn">
                    ✅ Check
                </button>
                <button class="action-button call" onclick="playerAction('call')" id="callBtn">
                    📞 Call $<span id="callAmount">0</span>
                </button>
                <div class="raise-controls">
                    <span style="color: var(--primary-gold); font-weight: 700;">Raise:</span>
                    <input type="range" id="raiseSlider" class="raise-slider" min="50" max="1000" value="100" oninput="updateRaiseAmount()">
                    <input type="number" id="raiseAmount" min="50" value="100" style="width: 80px;" onchange="updateRaiseSlider()">
                    <button class="action-button raise" onclick="playerAction('raise')" id="raiseBtn">
                        📈 Raise
                    </button>
                </div>
                <button class="action-button all-in" onclick="playerAction('all_in')" id="allInBtn">
                    🔥 ALL IN
                </button>
            </div>

            <!-- Chat Panel -->
            <div id="chatPanel" class="chat-panel hidden">
                <div class="chat-header">
                    <h3 class="chat-title">💬 Chat</h3>
                    <button class="chat-toggle" onclick="toggleChat()" id="chatToggle">−</button>
                </div>
                <div id="chatMessages"></div>
                <div class="chat-input-container">
                    <input type="text" id="chatInput" placeholder="Type message..." style="flex: 1;" onkeypress="if(event.key==='Enter') sendChat()" maxlength="200">
                    <button class="action-button" onclick="sendChat()">Send</button>
                </div>
            </div>

            <!-- Player Cards -->
            <div id="playerCards" class="player-cards hidden"></div>

            <!-- Hand History Modal -->
            <div id="handHistoryModal" class="modal hidden">
                <div class="modal-content">
                    <div class="modal-header">
                        <h2 class="modal-title">📊 Hand History</h2>
                        <button class="modal-close" onclick="hideHandHistory()">✕</button>
                    </div>
                    <div id="handHistoryContent" style="max-height: 400px; overflow-y: auto;">
                        <div style="text-align: center; color: #ccc; padding: 20px;">
                            No hands played yet.
                        </div>
                    </div>
                </div>
            </div>
        </div>
    </div>

    <script>
        // Advanced Game State Management
        let ws = null;
        let scene, camera, renderer, controls;
        let pokerTable, tableGroup;
        let cards = [], chips = [], playerPositions = [];
        let cardMaterials = {}, chipMaterials = {};
        let gameState = null;
        let isConnected = false;
        let isPlayer = false;
        let currentRoom = null;
        let animationQueue = [];
        let soundEnabled = true;
        let cameraAnimating = false;
        
        // 3D Scene objects
        let tableCards = [];
        let playerCardObjects = {};
        let chipStacks = [];
        let dealerButton, blindButtons = [];
        let particleSystem;
        
        // UI State
        let chatCollapsed = false;
        let notificationQueue = [];
        
        // Initialize Three.js scene with advanced graphics
        function initThreeJS() {
            const canvas = document.getElementById('canvas');
            
            // Scene setup
            scene = new THREE.Scene();
            scene.fog = new THREE.Fog(0x051a11, 15, 50);
            
            // Advanced lighting setup
            setupLighting();
            
            // Camera with smooth controls
            camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, 1000);
            camera.position.set(0, 12, 15);
            camera.lookAt(0, 0, 0);
            
            // Renderer with advanced settings
            renderer = new THREE.WebGLRenderer({ 
                canvas: canvas, 
                antialias: true,
                alpha: true,
                powerPreference: "high-performance"
            });
            renderer.setSize(window.innerWidth, window.innerHeight);
            renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
            renderer.shadowMap.enabled = true;
            renderer.shadowMap.type = THREE.PCFSoftShadowMap;
            renderer.toneMapping = THREE.ACESFilmicToneMapping;
            renderer.toneMappingExposure = 1.2;
            renderer.outputEncoding = THREE.sRGBEncoding;
            
            // Create casino environment
            createCasinoEnvironment();
            createPokerTable();
            createCardMaterials();
            createChipMaterials();
            
            // Add mouse controls
            addMouseControls();
            
            // Particle system for effects
            createParticleSystem();
            
            // Start render loop
            animate();
        }

        function setupLighting() {
            // Ambient light
            const ambientLight = new THREE.AmbientLight(0x404040, 0.3);
            scene.add(ambientLight);

            // Main directional light (casino ceiling)
            const mainLight = new THREE.DirectionalLight(0xffffff, 0.8);
            mainLight.position.set(10, 20, 10);
            mainLight.castShadow = true;
            mainLight.shadow.mapSize.width = 4096;
            mainLight.shadow.mapSize.height = 4096;
            mainLight.shadow.camera.near = 0.5;
            mainLight.shadow.camera.far = 50;
            mainLight.shadow.camera.left = -20;
            mainLight.shadow.camera.right = 20;
            mainLight.shadow.camera.top = 20;
            mainLight.shadow.camera.bottom = -20;
            scene.add(mainLight);

            // Table spot lights
            const tableLight1 = new THREE.SpotLight(0xffd700, 0.8, 30, Math.PI / 4, 0.5);
            tableLight1.position.set(0, 10, 0);
            tableLight1.target.position.set(0, 0, 0);
            tableLight1.castShadow = true;
            scene.add(tableLight1);
            scene.add(tableLight1.target);

            // Rim lighting
            const rimLight1 = new THREE.DirectionalLight(0x4444ff, 0.3);
            rimLight1.position.set(-10, 5, -10);
            scene.add(rimLight1);

            const rimLight2 = new THREE.DirectionalLight(0xff4444, 0.2);
            rimLight2.position.set(10, 5, -10);
            scene.add(rimLight2);

            // Point lights for atmosphere
            for (let i = 0; i < 6; i++) {
                const angle = (i / 6) * Math.PI * 2;
                const pointLight = new THREE.PointLight(0xffd700, 0.4, 20);
                pointLight.position.set(
                    Math.cos(angle) * 12,
                    8,
                    Math.sin(angle) * 12
                );
                scene.add(pointLight);
            }
        }

        function createCasinoEnvironment() {
            // Casino floor
            const floorGeometry = new THREE.PlaneGeometry(100, 100);
            const floorMaterial = new THREE.MeshLambertMaterial({ 
                color: 0x2a0a0a,
                transparent: true,
                opacity: 0.8
            });
            const floor = new THREE.Mesh(floorGeometry, floorMaterial);
            floor.rotation.x = -Math.PI / 2;
            floor.position.y = -2;
            floor.receiveShadow = true;
            scene.add(floor);

            // Casino walls (distant)
            for (let i = 0; i < 4; i++) {
                const wallGeometry = new THREE.PlaneGeometry(100, 20);
                const wallMaterial = new THREE.MeshLambertMaterial({ 
                    color: 0x1a1a2e,
                    transparent: true,
                    opacity: 0.3
                });
                const wall = new THREE.Mesh(wallGeometry, wallMaterial);
                
                const angle = (i / 4) * Math.PI * 2;
                wall.position.set(
                    Math.cos(angle) * 50,
                    8,
                    Math.sin(angle) * 50
                );
                wall.lookAt(0, 8, 0);
                scene.add(wall);
            }

            // Ceiling with casino lights
            const ceilingGeometry = new THREE.PlaneGeometry(100, 100);
            const ceilingMaterial = new THREE.MeshLambertMaterial({ 
                color: 0x0f0f0f,
                transparent: true,
                opacity: 0.9
            });
            const ceiling = new THREE.Mesh(ceilingGeometry, ceilingMaterial);
            ceiling.rotation.x = Math.PI / 2;
            ceiling.position.y = 20;
            scene.add(ceiling);
        }

        function createPokerTable() {
            tableGroup = new THREE.Group();
            
            // Main table surface
            const tableGeometry = new THREE.CylinderGeometry(7, 7, 0.4, 64);
            const tableMaterial = new THREE.MeshPhongMaterial({ 
                color: 0x8B4513,
                shininess: 30,
                specular: 0x222222
            });
            pokerTable = new THREE.Mesh(tableGeometry, tableMaterial);
            pokerTable.position.y = -0.2;
            pokerTable.receiveShadow = true;
            pokerTable.castShadow = true;
            tableGroup.add(pokerTable);

            // Table edge/rail
            const edgeGeometry = new THREE.TorusGeometry(7, 0.3, 16, 64);
            const edgeMaterial = new THREE.MeshPhongMaterial({ 
                color: 0x654321,
                shininess: 50
            });
            const tableEdge = new THREE.Mesh(edgeGeometry, edgeMaterial);
            tableEdge.position.y = 0;
            tableEdge.castShadow = true;
            tableGroup.add(tableEdge);

            // Felt surface
            const feltGeometry = new THREE.CylinderGeometry(6.5, 6.5, 0.05, 64);
            const feltMaterial = new THREE.MeshLambertMaterial({ color: 0x0d4d2a });
            const tableFelt = new THREE.Mesh(feltGeometry, feltMaterial);
            tableFelt.position.y = 0.25;
            tableFelt.receiveShadow = true;
            tableGroup.add(tableFelt);

            // Table markings and details
            createTableMarkings();
            
            // Cup holders
            for (let i = 0; i < 10; i++) {
                const angle = (i / 10) * Math.PI * 2;
                const cupHolderGeometry = new THREE.CylinderGeometry(0.2, 0.2, 0.1, 16);
                const cupHolderMaterial = new THREE.MeshPhongMaterial({ color: 0x333333 });
                const cupHolder = new THREE.Mesh(cupHolderGeometry, cupHolderMaterial);
                cupHolder.position.set(
                    Math.cos(angle) * 6,
                    0.25,
                    Math.sin(angle) * 6
                );
                tableGroup.add(cupHolder);
            }
            
            scene.add(tableGroup);
            
            // Create player positions
            createPlayerPositions();
        }

        function createTableMarkings() {
            // Community card area outline
            const cardAreaGeometry = new THREE.RingGeometry(1.5, 1.6, 32);
            const cardAreaMaterial = new THREE.MeshBasicMaterial({ 
                color: 0xffd700,
                transparent: true,
                opacity: 0.5
            });
            const cardArea = new THREE.Mesh(cardAreaGeometry, cardAreaMaterial);
            cardArea.rotation.x = -Math.PI / 2;
            cardArea.position.y = 0.26;
            tableGroup.add(cardArea);

            // Pot area
            const potAreaGeometry = new THREE.RingGeometry(0.8, 0.9, 32);
            const potAreaMaterial = new THREE.MeshBasicMaterial({ 
                color: 0xffd700,
                transparent: true,
                opacity: 0.3
            });
            const potArea = new THREE.Mesh(potAreaGeometry, potAreaMaterial);
            potArea.rotation.x = -Math.PI / 2;
            potArea.position.set(0, 0.26, 2);
            tableGroup.add(potArea);
        }

        function createPlayerPositions() {
            playerPositions = [];
            for (let i = 0; i < 10; i++) {
                const angle = (i / 10) * Math.PI * 2;
                const position = {
                    angle: angle,
                    x: Math.cos(angle) * 5,
                    z: Math.sin(angle) * 5,
                    cardX: Math.cos(angle) * 4.2,
                    cardZ: Math.sin(angle) * 4.2,
                    chipX: Math.cos(angle) * 3.5,
                    chipZ: Math.sin(angle) * 3.5
                };
                playerPositions.push(position);
            }
        }

        function createCardMaterials() {
            cardMaterials = {};
            
            // Card back material
            cardMaterials.back = new THREE.MeshPhongMaterial({
                color: 0x2E4BC6,
                shininess: 30
            });

            // Suit colors
            const redColor = 0xDD0000;
            const blackColor = 0x000000;
            const whiteColor = 0xFFFFFF;

            // Create materials for each suit
            ['hearts', 'diamonds', 'clubs', 'spades'].forEach(suit => {
                const isRed = suit === 'hearts' || suit === 'diamonds';
                cardMaterials[suit] = new THREE.MeshPhongMaterial({
                    color: whiteColor,
                    shininess: 20
                });
            });
        }

        function createChipMaterials() {
            chipMaterials = {
                1: new THREE.MeshPhongMaterial({ color: 0xFFFFFF, shininess: 50 }),    // White
                5: new THREE.MeshPhongMaterial({ color: 0xFF0000, shininess: 50 }),    // Red  
                10: new THREE.MeshPhongMaterial({ color: 0xFFAA00, shininess: 50 }),   // Orange
                25: new THREE.MeshPhongMaterial({ color: 0x00AA00, shininess: 50 }),   // Green
                50: new THREE.MeshPhongMaterial({ color: 0x0066CC, shininess: 50 }),   // Blue
                100: new THREE.MeshPhongMaterial({ color: 0x000000, shininess: 50 }),  // Black
                500: new THREE.MeshPhongMaterial({ color: 0x800080, shininess: 50 }),  // Purple
                1000: new THREE.MeshPhongMaterial({ color: 0xFFD700, shininess: 50 }), // Gold
            };
        }

        function createCard3D(suit, rank, position, rotation = 0, faceUp = true) {
            const cardGroup = new THREE.Group();
            
            // Card geometry
            const cardGeometry = new THREE.PlaneGeometry(0.9, 1.3);
            
            // Card material
            const material = faceUp && suit !== 'back' ? cardMaterials[suit] || cardMaterials.back : cardMaterials.back;
            
            const card = new THREE.Mesh(cardGeometry, material);
            card.rotation.x = -Math.PI / 2;
            card.rotation.z = rotation;
            card.castShadow = true;
            card.receiveShadow = true;
            
            cardGroup.add(card);
            
            // Add card details if face up
            if (faceUp && suit !== 'back') {
                createCardDetails(cardGroup, suit, rank, rotation);
            }
            
            cardGroup.position.copy(position);
            
            return cardGroup;
        }

        function createCardDetails(cardGroup, suit, rank, rotation) {
            // Suit symbol
            const symbolGeometry = new THREE.PlaneGeometry(0.2, 0.2);
            const symbolMaterial = new THREE.MeshBasicMaterial({ 
                color: (suit === 'hearts' || suit === 'diamonds') ? 0xFF0000 : 0x000000,
                transparent: true,
                opacity: 0.8
            });
            
            const symbol = new THREE.Mesh(symbolGeometry, symbolMaterial);
            symbol.position.set(0, 0.01, 0.3);
            symbol.rotation.x = -Math.PI / 2;
            symbol.rotation.z = rotation;
            cardGroup.add(symbol);
            
            // Rank text (simplified)
            const rankGeometry = new THREE.PlaneGeometry(0.15, 0.15);
            const rankMaterial = new THREE.MeshBasicMaterial({ 
                color: (suit === 'hearts' || suit === 'diamonds') ? 0xFF0000 : 0x000000,
                transparent: true,
                opacity: 0.8
            });
            
            const rankMesh = new THREE.Mesh(rankGeometry, rankMaterial);
            rankMesh.position.set(0, 0.01, -0.3);
            rankMesh.rotation.x = -Math.PI / 2;
            rankMesh.rotation.z = rotation;
            cardGroup.add(rankMesh);
        }

        function createChip3D(value, position, count = 1) {
            const chipGroup = new THREE.Group();
            
            for (let i = 0; i < count; i++) {
                const chipGeometry = new THREE.CylinderGeometry(0.35, 0.35, 0.08, 16);
                const chipValue = getChipValue(value);
                const chipMaterial = chipMaterials[chipValue] || chipMaterials[1];
                
                const chip = new THREE.Mesh(chipGeometry, chipMaterial);
                chip.position.y = i * 0.09;
                chip.castShadow = true;
                chip.receiveShadow = true;
                
                // Add chip edge
                const edgeGeometry = new THREE.TorusGeometry(0.35, 0.02, 8, 16);
                const edgeMaterial = new THREE.MeshPhongMaterial({ color: 0xFFFFFF, shininess: 100 });
                const edge = new THREE.Mesh(edgeGeometry, edgeMaterial);
                edge.position.y = i * 0.09;
                
                chipGroup.add(chip);
                chipGroup.add(edge);
            }
            
            chipGroup.position.copy(position);
            return chipGroup;
        }

        function getChipValue(amount) {
            if (amount >= 1000) return 1000;
            if (amount >= 500) return 500;
            if (amount >= 100) return 100;
            if (amount >= 50) return 50;
            if (amount >= 25) return 25;
            if (amount >= 10) return 10;
            if (amount >= 5) return 5;
            return 1;
        }

        function createParticleSystem() {
            const particleCount = 100;
            const particles = new THREE.BufferGeometry();
            const particlePositions = new Float32Array(particleCount * 3);
            
            for (let i = 0; i < particleCount * 3; i += 3) {
                particlePositions[i] = (Math.random() - 0.5) * 50;     // x
                particlePositions[i + 1] = Math.random() * 30 + 5;    // y
                particlePositions[i + 2] = (Math.random() - 0.5) * 50; // z
            }
            
            particles.setAttribute('position', new THREE.BufferAttribute(particlePositions, 3));
            
            const particleMaterial = new THREE.PointsMaterial({
                color: 0xFFD700,
                size: 0.1,
                transparent: true,
                opacity: 0.3,
                blending: THREE.AdditiveBlending
            });
            
            particleSystem = new THREE.Points(particles, particleMaterial);
            scene.add(particleSystem);
        }

        function addMouseControls() {
            let mouseDown = false;
            let mouseX = 0;
            let mouseY = 0;
            let targetCameraX = 0;
            let targetCameraZ = 15;
            
            canvas.addEventListener('mousedown', (event) => {
                mouseDown = true;
                mouseX = event.clientX;
                mouseY = event.clientY;
            });
            
            canvas.addEventListener('mouseup', () => {
                mouseDown = false;
            });
            
            canvas.addEventListener('mousemove', (event) => {
                if (!cameraAnimating && mouseDown) {
                    const deltaX = event.clientX - mouseX;
                    const deltaY = event.clientY - mouseY;
                    
                    targetCameraX += deltaX * 0.01;
                    targetCameraZ += deltaY * 0.01;
                    targetCameraZ = Math.max(8, Math.min(25, targetCameraZ));
                    
                    mouseX = event.clientX;
                    mouseY = event.clientY;
                }
            });
            
            canvas.addEventListener('wheel', (event) => {
                if (!cameraAnimating) {
                    targetCameraZ += event.deltaY * 0.01;
                    targetCameraZ = Math.max(8, Math.min(25, targetCameraZ));
                }
            });
            
            // Smooth camera movement
            function updateCamera() {
                if (!cameraAnimating) {
                    const radius = targetCameraZ;
                    camera.position.x = Math.sin(targetCameraX) * radius;
                    camera.position.z = Math.cos(targetCameraX) * radius;
                    camera.position.y = 12;
                    camera.lookAt(0, 0, 0);
                }
                requestAnimationFrame(updateCamera);
            }
            updateCamera();
        }

        function animate() {
            requestAnimationFrame(animate);
            
            // Animate table rotation
            if (tableGroup) {
                tableGroup.rotation.y += 0.0005;
            }
            
            // Animate particle system
            if (particleSystem) {
                particleSystem.rotation.y += 0.001;
                const positions = particleSystem.geometry.attributes.position.array;
                for (let i = 1; i < positions.length; i += 3) {
                    positions[i] += Math.sin(Date.now() * 0.001 + i) * 0.001;
                }
                particleSystem.geometry.attributes.position.needsUpdate = true;
            }
            
            // Animate cards
            tableCards.forEach((card, index) => {
                if (card) {
                    card.rotation.y = Math.sin(Date.now() * 0.001 + index) * 0.1;
                    card.position.y = 0.3 + Math.sin(Date.now() * 0.002 + index) * 0.05;
                }
            });
            
            // Animate chips
            chipStacks.forEach((chipStack, index) => {
                if (chipStack) {
                    chipStack.rotation.y += 0.01;
                }
            });
            
            // Process animation queue
            processAnimationQueue();
            
            renderer.render(scene, camera);
        }

        function processAnimationQueue() {
            if (animationQueue.length > 0) {
                const animation = animationQueue[0];
                if (animation.update()) {
                    animationQueue.shift();
                }
            }
        }

        function animateCardDeal(targetPosition, delay = 0) {
            return new Promise((resolve) => {
                setTimeout(() => {
                    const cardGroup = createCard3D('back', '?', new THREE.Vector3(0, 5, 0));
                    scene.add(cardGroup);
                    
                    // Animate card falling and sliding to position
                    gsap.to(cardGroup.position, {
                        duration: 0.8,
                        x: targetPosition.x,
                        y: targetPosition.y,
                        z: targetPosition.z,
                        ease: "power2.out",
                        onComplete: resolve
                    });
                    
                    gsap.to(cardGroup.rotation, {
                        duration: 0.8,
                        y: Math.random() * 0.2 - 0.1,
                        ease: "power2.out"
                    });
                    
                }, delay);
            });
        }

        function animateChipStack(position, amount) {
            const chipCount = Math.min(Math.floor(amount / getChipValue(amount)), 10);
            const chipStack = createChip3D(amount, position, chipCount);
            scene.add(chipStack);
            chipStacks.push(chipStack);
            
            // Animate chips falling
            chipStack.position.y = 5;
            gsap.to(chipStack.position, {
                duration: 0.6,
                y: 0.3,
                ease: "bounce.out"
            });
        }

        function updateTableVisuals() {
            // Clear existing objects
            clearTableObjects();
            
            if (!gameState) return;
            
            // Community cards with dealing animation
            gameState.community_cards.forEach((card, index) => {
                setTimeout(() => {
                    const position = new THREE.Vector3(-2 + index * 1, 0.3, 0);
                    const cardObj = createCard3D(card.suit, card.rank, position, 0, true);
                    scene.add(cardObj);
                    tableCards.push(cardObj);
                    
                    // Card reveal animation
                    cardObj.scale.set(0, 0, 0);
                    gsap.to(cardObj.scale, {
                        duration: 0.5,
                        x: 1, y: 1, z: 1,
                        ease: "back.out(1.7)"
                    });
                    
                }, index * 200);
            });
            
            // Player cards and positions
            const players = Object.values(gameState.players);
            players.forEach((player, index) => {
                if (index < playerPositions.length) {
                    const pos = playerPositions[index];
                    
                    // Player cards
                    if (player.cards && player.cards.length > 0) {
                        player.cards.forEach((card, cardIndex) => {
                            const cardPosition = new THREE.Vector3(
                                pos.cardX + (cardIndex - 0.5) * 0.3,
                                0.3,
                                pos.cardZ
                            );
                            
                            const faceUp = card.suit !== 'back';
                            const cardObj = createCard3D(card.suit, card.rank, cardPosition, pos.angle, faceUp);
                            scene.add(cardObj);
                            
                            if (!playerCardObjects[player.id]) {
                                playerCardObjects[player.id] = [];
                            }
                            playerCardObjects[player.id].push(cardObj);
                        });
                    }
                    
                    // Player chip stacks
                    if (player.current_bet > 0) {
                        const chipPosition = new THREE.Vector3(pos.chipX, 0.3, pos.chipZ);
                        animateChipStack(chipPosition, player.current_bet);
                    }
                }
            });
            
            // Main pot chips
            if (gameState.pot > 0) {
                const potPosition = new THREE.Vector3(0, 0.3, 2);
                animateChipStack(potPosition, gameState.pot);
            }
            
            // Side pots
            if (gameState.side_pots && gameState.side_pots.length > 0) {
                gameState.side_pots.forEach((sidePot, index) => {
                    const angle = (index / gameState.side_pots.length) * Math.PI * 2;
                    const sidePotPosition = new THREE.Vector3(
                        Math.cos(angle) * 1.5,
                        0.3,
                        Math.sin(angle) * 1.5 + 2
                    );
                    animateChipStack(sidePotPosition, sidePot.amount);
                });
            }
        }

        function clearTableObjects() {
            // Remove cards
            tableCards.forEach(card => scene.remove(card));
            tableCards = [];
            
            // Remove player cards
            Object.values(playerCardObjects).forEach(cards => {
                cards.forEach(card => scene.remove(card));
            });
            playerCardObjects = {};
            
            // Remove chips
            chipStacks.forEach(chips => scene.remove(chips));
            chipStacks = [];
        }

        // WebSocket Connection Management
        function connectWebSocket() {
            const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
            const wsUrl = `${protocol}//${window.location.host}/ws`;
            
            ws = new WebSocket(wsUrl);
            
            ws.onopen = function() {
                console.log('Connected to advanced poker server');
                isConnected = true;
                hideLoadingScreen();
                showMainMenu();
                showNotification('Connected to Royal Poker 3D!', 'success');
            };
            
            ws.onmessage = function(event) {
                const message = JSON.parse(event.data);
                handleServerMessage(message);
            };
            
            ws.onclose = function() {
                console.log('Disconnected from server');
                isConnected = false;
                showLoadingScreen('Connection lost. Reconnecting...');
                showNotification('Connection lost. Reconnecting...', 'error');
                
                // Attempt to reconnect
                setTimeout(connectWebSocket, 3000);
            };
            
            ws.onerror = function(error) {
                console.error('WebSocket error:', error);
                showNotification('Connection error occurred', 'error');
            };
        }

        function sendMessage(action, payload = {}) {
            if (ws && ws.readyState === WebSocket.OPEN) {
                ws.send(JSON.stringify({ action, payload }));
            } else {
                showNotification('Not connected to server', 'error');
            }
        }

        function handleServerMessage(message) {
            console.log('Received:', message);
            
            switch (message.type) {
                case 'connected':
                    showNotification(`Welcome! Server version ${message.data.server_info.version}`, 'success');
                    break;
                    
                case 'room_created':
                case 'room_joined':
                    currentRoom = message.data.room_code;
                    isPlayer = true;
                    showGameInterface();
                    showNotification(`Joined room ${currentRoom}`, 'success');
                    animateCameraToTable();
                    break;
                    
                case 'spectating':
                    currentRoom = message.data.room_code;
                    isPlayer = false;
                    showGameInterface();
                    showNotification(`Spectating room ${currentRoom}`, 'info');
                    animateCameraToTable();
                    break;
                    
                case 'room_left':
                    showMainMenu();
                    showNotification('Left room', 'info');
                    animateCameraToMenu();
                    break;
                    
                case 'game_state':
                    gameState = message.data;
                    updateGameInterface();
                    updateTableVisuals();
                    break;
                    
                case 'game_started':
                    showNotification('Game started! Good luck!', 'success');
                    break;
                    
                case 'action_accepted':
                    // Action was successful
                    break;
                    
                case 'room_list':
                    updateRoomList(message.data.rooms);
                    break;
                    
                case 'hand_history':
                    updateHandHistory(message.data.history);
                    break;
                    
                case 'error':
                    showNotification('Error: ' + message.message, 'error');
                    break;
                    
                default:
                    console.log('Unknown message type:', message.type);
            }
        }

        // Camera Animation Functions
        function animateCameraToTable() {
            cameraAnimating = true;
            gsap.to(camera.position, {
                duration: 2,
                x: 0,
                y: 12,
                z: 15,
                ease: "power2.inOut",
                onComplete: () => {
                    cameraAnimating = false;
                    camera.lookAt(0, 0, 0);
                }
            });
        }

        function animateCameraToMenu() {
            cameraAnimating = true;
            gsap.to(camera.position, {
                duration: 2,
                x: 5,
                y: 15,
                z: 20,
                ease: "power2.inOut",
                onComplete: () => {
                    cameraAnimating = false;
                    camera.lookAt(0, 0, 0);
                }
            });
        }

        // UI Management Functions
        function hideLoadingScreen() {
            const loadingScreen = document.getElementById('loadingScreen');
            gsap.to(loadingScreen, {
                duration: 1,
                opacity: 0,
                onComplete: () => {
                    loadingScreen.style.display = 'none';
                }
            });
        }

        function showLoadingScreen(text = 'Loading casino experience...') {
            const loadingScreen = document.getElementById('loadingScreen');
            const loadingText = loadingScreen.querySelector('.loading-text');
            loadingText.textContent = text;
            loadingScreen.style.display = 'flex';
            gsap.to(loadingScreen, {
                duration: 0.5,
                opacity: 1
            });
        }

        function showMainMenu() {
            document.getElementById('menuPanel').classList.remove('hidden');
            document.getElementById('gameHUD').classList.add('hidden');
            document.getElementById('potDisplay').classList.add('hidden');
            document.getElementById('actionsPanel').classList.add('hidden');
            document.getElementById('chatPanel').classList.add('hidden');
            document.getElementById('playerCards').classList.add('hidden');
            document.getElementById('tournamentInfo').classList.add('hidden');
            document.getElementById('actionTimer').classList.add('hidden');
            
            currentRoom = null;
            gameState = null;
            isPlayer = false;
            
            clearTableObjects();
        }

        function showGameInterface() {
            document.getElementById('menuPanel').classList.add('hidden');
            document.getElementById('gameHUD').classList.remove('hidden');
            document.getElementById('chatPanel').classList.remove('hidden');
            document.getElementById('playerCards').classList.remove('hidden');
            
            if (currentRoom) {
                document.getElementById('currentRoom').textContent = currentRoom;
            }
        }

        function updateGameInterface() {
            if (!gameState) return;

            // Update HUD
            document.getElementById('phaseText').textContent = gameState.phase.replace('_', ' ').toUpperCase();
            document.getElementById('handNumber').textContent = gameState.hand_number;
            
            // Show/hide pot
            if (gameState.pot > 0) {
                document.getElementById('potDisplay').classList.remove('hidden');
                document.getElementById('potAmount').textContent = gameState.pot.toLocaleString();
                
                // Side pots display
                const sidePots = document.getElementById('sidePots');
                if (gameState.side_pots && gameState.side_pots.length > 0) {
                    sidePots.innerHTML = gameState.side_pots.map((sp, i) => 
                        `Side Pot ${i + 1}: ${sp.amount.toLocaleString()}`
                    ).join('<br>');
                } else {
                    sidePots.innerHTML = '';
                }
            } else {
                document.getElementById('potDisplay').classList.add('hidden');
            }

            // Update player money and bet info
            if (gameState.is_player && gameState.players) {
                const myPlayer = Object.values(gameState.players).find(p => 
                    p.cards && p.cards.length > 0 && p.cards[0].suit !== 'back'
                );
                
                if (myPlayer) {
                    document.getElementById('moneyAmount').textContent = myPlayer.money.toLocaleString();
                }
            }

            document.getElementById('betAmount').textContent = gameState.current_bet.toLocaleString();

            // Tournament info
            if (gameState.tournament_info) {
                document.getElementById('tournamentInfo').classList.remove('hidden');
                document.getElementById('tournamentLevel').textContent = gameState.tournament_info.level;
                document.getElementById('tournamentBlinds').textContent = 
                    `${gameState.settings.small_blind}/${gameState.settings.big_blind}`;
                
                // Update timer if available
                if (gameState.tournament_info.next_level_time) {
                    updateTournamentTimer(gameState.tournament_info.next_level_time);
                }
            } else {
                document.getElementById('tournamentInfo').classList.add('hidden');
            }

            // Show/hide action timer
            if (gameState.can_act && gameState.time_left > 0) {
                document.getElementById('actionTimer').classList.remove('hidden');
                document.getElementById('timerSeconds').textContent = Math.ceil(gameState.time_left);
            } else {
                document.getElementById('actionTimer').classList.add('hidden');
            }

            // Show/hide start game button
            const startBtn = document.getElementById('startGameBtn');
            if (gameState.phase === 'waiting' && Object.keys(gameState.players).length >= 2) {
                startBtn.style.display = 'block';
            } else {
                startBtn.style.display = 'none';
            }

            // Show/hide action buttons
            if (gameState.can_act && gameState.available_actions) {
                document.getElementById('actionsPanel').classList.remove('hidden');
                updateActionButtons();
            } else {
                document.getElementById('actionsPanel').classList.add('hidden');
            }

            // Update player cards
            updatePlayerCards();
            
            // Update chat
            updateChat();
            
            // Handle paused state
            if (gameState.paused) {
                showNotification(`Game paused: ${gameState.pause_reason}`, 'warning');
            }
        }

        function updateActionButtons() {
            if (!gameState || !gameState.available_actions) return;

            const actions = gameState.available_actions;
            
            // Update button states
            const foldBtn = document.getElementById('foldBtn');
            const checkBtn = document.getElementById('checkBtn');
            const callBtn = document.getElementById('callBtn');
            const raiseBtn = document.getElementById('raiseBtn');
            const allInBtn = document.getElementById('allInBtn');
            
            // Reset all buttons
            [foldBtn, checkBtn, callBtn, raiseBtn, allInBtn].forEach(btn => {
                btn.disabled = true;
                btn.style.display = 'none';
            });
            
            // Enable available actions
            actions.forEach(action => {
                switch (action.action) {
                    case 'fold':
                        foldBtn.disabled = false;
                        foldBtn.style.display = 'inline-block';
                        break;
                    case 'check':
                        checkBtn.disabled = false;
                        checkBtn.style.display = 'inline-block';
                        break;
                    case 'call':
                        callBtn.disabled = false;
                        callBtn.style.display = 'inline-block';
                        document.getElementById('callAmount').textContent = action.amount.toLocaleString();
                        break;
                    case 'raise':
                        raiseBtn.disabled = false;
                        raiseBtn.style.display = 'inline-block';
                        
                        // Update raise controls
                        const raiseSlider = document.getElementById('raiseSlider');
                        const raiseAmount = document.getElementById('raiseAmount');
                        raiseSlider.min = action.min_amount;
                        raiseSlider.max = action.max_amount;
                        raiseAmount.min = action.min_amount;
                        raiseAmount.max = action.max_amount;
                        raiseAmount.value = Math.max(action.min_amount, parseInt(raiseAmount.value));
                        raiseSlider.value = raiseAmount.value;
                        break;
                    case 'all_in':
                        allInBtn.disabled = false;
                        allInBtn.style.display = 'inline-block';
                        allInBtn.innerHTML = `🔥 ALL IN ${action.amount.toLocaleString()}`;
                        break;
                }
            });
        }

        function updatePlayerCards() {
            const playerCardsContainer = document.getElementById('playerCards');
            playerCardsContainer.innerHTML = '';
            
            if (!gameState || !gameState.players) return;
            
            Object.values(gameState.players).forEach(player => {
                const playerCard = document.createElement('div');
                playerCard.className = 'player-card';
                
                if (player.is_current_player) {
                    playerCard.classList.add('current-player');
                }
                if (player.status === 'folded') {
                    playerCard.classList.add('folded');
                }
                if (player.status === 'all_in') {
                    playerCard.classList.add('all-in');
                }
                
                playerCard.innerHTML = `
                    <div class="player-avatar" style="background-color: ${player.color}">
                        ${player.name.charAt(0).toUpperCase()}
                    </div>
                    <div class="player-name">${player.name}</div>
                    <div class="player-money">${player.money.toLocaleString()}</div>
                    ${player.current_bet > 0 ? `<div style="color: var(--primary-gold); font-size: 0.9rem;">Bet: ${player.current_bet.toLocaleString()}</div>` : ''}
                    ${player.last_action ? `<div class="player-action">${player.last_action.toUpperCase()}</div>` : ''}
                    ${player.is_dealer ? '<div style="position: absolute; top: -5px; left: -5px; background: gold; color: black; border-radius: 50%; width: 20px; height: 20px; display: flex; align-items: center; justify-content: center; font-size: 0.8rem; font-weight: bold;">D</div>' : ''}
                `;
                
                playerCardsContainer.appendChild(playerCard);
                
                // Animate card appearance
                gsap.from(playerCard, {
                    duration: 0.5,
                    scale: 0,
                    rotation: 360,
                    ease: "back.out(1.7)"
                });
            });
        }

        function updateChat() {
            if (!gameState || !gameState.chat_messages) return;

            const chatMessages = document.getElementById('chatMessages');
            const shouldScroll = chatMessages.scrollTop + chatMessages.clientHeight >= chatMessages.scrollHeight - 10;
            
            chatMessages.innerHTML = '';
            
            gameState.chat_messages.forEach(msg => {
                const msgDiv = document.createElement('div');
                msgDiv.className = 'chat-message';
                msgDiv.style.borderLeftColor = msg.player_color || '#ffffff';
                
                msgDiv.innerHTML = `
                    <span class="chat-player-name" style="color: ${msg.player_color || '#ffffff'}">${msg.player_name}:</span>
                    <span>${msg.message}</span>
                    <span class="chat-timestamp">${msg.formatted_time}</span>
                `;
                
                chatMessages.appendChild(msgDiv);
            });
            
            if (shouldScroll) {
                chatMessages.scrollTop = chatMessages.scrollHeight;
            }
        }

        function updateTournamentTimer(nextLevelTime) {
            const now = new Date();
            const next = new Date(nextLevelTime);
            const diff = next - now;
            
            if (diff > 0) {
                const minutes = Math.floor(diff / 60000);
                const seconds = Math.floor((diff % 60000) / 1000);
                document.getElementById('tournamentTimer').textContent = 
                    `${minutes}:${seconds.toString().padStart(2, '0')}`;
            }
        }

        // Game Action Functions
        function createQuickRoom() {
            const playerName = document.getElementById('playerName').value.trim() || 'Anonymous';
            sendMessage('create_room', { 
                player_name: playerName,
                game_mode: 'cash_game',
                small_blind: 25,
                big_blind: 50,
                max_players: 8
            });
            isPlayer = true;
        }

        function createCustomRoom() {
            const playerName = document.getElementById('playerName').value.trim() || 'Anonymous';
            const roomName = document.getElementById('roomName').value.trim();
            const gameMode = document.getElementById('gameMode').value;
            const maxPlayers = parseInt(document.getElementById('maxPlayers').value);
            const smallBlind = parseInt(document.getElementById('smallBlind').value);
            const bigBlind = parseInt(document.getElementById('bigBlind').value);
            const buyIn = parseInt(document.getElementById('buyIn').value);
            const password = document.getElementById('roomPassword').value.trim();
            
            sendMessage('create_room', { 
                player_name: playerName,
                room_name: roomName,
                game_mode: gameMode,
                max_players: maxPlayers,
                small_blind: smallBlind,
                big_blind: bigBlind,
                buy_in: buyIn,
                password: password
            });
            isPlayer = true;
        }

        function joinRoom() {
            const roomCode = document.getElementById('roomCode').value.trim().toUpperCase();
            const playerName = document.getElementById('playerName').value.trim() || 'Anonymous';
            
            if (!roomCode) {
                showNotification('Please enter a room code', 'error');
                return;
            }
            
            sendMessage('join_room', { 
                room_code: roomCode, 
                player_name: playerName 
            });
            isPlayer = true;
        }

        function spectateRoom() {
            const roomCode = document.getElementById('roomCode').value.trim().toUpperCase();
            
            if (!roomCode) {
                showNotification('Please enter a room code', 'error');
                return;
            }
            
            sendMessage('spectate', { room_code: roomCode });
            isPlayer = false;
        }

        function leaveRoom() {
            sendMessage('leave_room');
        }

        function startGame() {
            sendMessage('start_game');
        }

        function pauseGame() {
            sendMessage('pause_game');
        }

        function playerAction(action) {
            let payload = { action_type: action };
            
            if (action === 'raise') {
                const amount = parseInt(document.getElementById('raiseAmount').value) || 0;
                payload.amount = amount;
            }
            
            sendMessage('player_action', payload);
            
            // Show action feedback
            showNotification(`Action: ${action.toUpperCase()}`, 'info');
        }

        function sendChat() {
            const chatInput = document.getElementById('chatInput');
            const message = chatInput.value.trim();
            
            if (message && message.length <= 200) {
                sendMessage('send_chat', { message });
                chatInput.value = '';
            } else if (message.length > 200) {
                showNotification('Message too long (max 200 characters)', 'error');
            }
        }

        function toggleChat() {
            const chatMessages = document.getElementById('chatMessages');
            const chatToggle = document.getElementById('chatToggle');
            
            chatCollapsed = !chatCollapsed;
            
            if (chatCollapsed) {
                chatMessages.style.display = 'none';
                chatToggle.textContent = '+';
            } else {
                chatMessages.style.display = 'block';
                chatToggle.textContent = '−';
            }
        }

        function updateRaiseAmount() {
            const slider = document.getElementById('raiseSlider');
            const input = document.getElementById('raiseAmount');
            input.value = slider.value;
        }

        function updateRaiseSlider() {
            const slider = document.getElementById('raiseSlider');
            const input = document.getElementById('raiseAmount');
            slider.value = input.value;
        }

        // Room List Functions
        function showRoomList() {
            document.getElementById('roomListModal').classList.remove('hidden');
            sendMessage('get_room_list');
        }

        function hideRoomList() {
            document.getElementById('roomListModal').classList.add('hidden');
        }

        function refreshRoomList() {
            sendMessage('get_room_list');
        }

        function updateRoomList(rooms) {
            const roomList = document.getElementById('roomList');
            
            if (rooms.length === 0) {
                roomList.innerHTML = '<div style="text-align: center; color: #ccc; padding: 20px;">No public rooms available</div>';
                return;
            }
            
            roomList.innerHTML = rooms.map(room => `
                <div style="background: rgba(255,255,255,0.1); border-radius: 10px; padding: 15px; margin-bottom: 10px; border: 1px solid var(--primary-gold);">
                    <div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 10px;">
                        <strong style="color: var(--primary-gold);">${room.name}</strong>
                        <span style="background: var(--primary-gold); color: black; padding: 2px 8px; border-radius: 12px; font-size: 0.8rem;">${room.code}</span>
                    </div>
                    <div style="display: grid; grid-template-columns: 1fr 1fr; gap: 10px; font-size: 0.9rem;">
                        <div>👥 ${room.players}/${room.max_players} players</div>
                        <div>👁️ ${room.spectators} spectators</div>
                        <div>🎮 ${room.phase.replace('_', ' ')}</div>
                        <div>💰 ${room.small_blind}/${room.big_blind}</div>
                    </div>
                    <div style="margin-top: 10px; text-align: center;">
                        <button class="action-button" onclick="joinRoomByCode('${room.code}')" style="margin-right: 10px;">Join</button>
                        <button class="action-button" onclick="spectateRoomByCode('${room.code}')">Spectate</button>
                    </div>
                </div>
            `).join('');
        }

        function joinRoomByCode(roomCode) {
            document.getElementById('roomCode').value = roomCode;
            hideRoomList();
            joinRoom();
        }

        function spectateRoomByCode(roomCode) {
            document.getElementById('roomCode').value = roomCode;
            hideRoomList();
            spectateRoom();
        }

        // Hand History Functions
        function showHandHistory() {
            document.getElementById('handHistoryModal').classList.remove('hidden');
            sendMessage('get_hand_history');
        }

        function hideHandHistory() {
            document.getElementById('handHistoryModal').classList.add('hidden');
        }

        function updateHandHistory(history) {
            const content = document.getElementById('handHistoryContent');
            
            if (history.length === 0) {
                content.innerHTML = '<div style="text-align: center; color: #ccc; padding: 20px;">No hands played yet.</div>';
                return;
            }
            
            content.innerHTML = history.map(hand => `
                <div style="background: rgba(255,255,255,0.1); border-radius: 10px; padding: 15px; margin-bottom: 15px; border: 1px solid var(--primary-gold);">
                    <div style="display: flex; justify-content: space-between; margin-bottom: 10px;">
                        <strong style="color: var(--primary-gold);">Hand #${hand.hand_number}</strong>
                        <span style="color: #ccc; font-size: 0.9rem;">${new Date(hand.timestamp).toLocaleString()}</span>
                    </div>
                    <div style="margin-bottom: 10px;">
                        <strong>Community Cards:</strong> 
                        ${hand.community_cards.map(card => `${card.rank}${card.suit[0].toUpperCase()}`).join(' ')}
                    </div>
                    <div style="margin-bottom: 10px;">
                        <strong>Pot:</strong> ${hand.pot.toLocaleString()}
                    </div>
                    <div>
                        <strong>Players:</strong><br>
                        ${Object.values(hand.players).map(player => 
                            `${player.name}: ${player.final_money.toLocaleString()}`
                        ).join('<br>')}
                    </div>
                </div>
            `).join('');
        }

        // Notification System
        function showNotification(message, type = 'info') {
            const notification = document.createElement('div');
            notification.className = `notification ${type}`;
            notification.textContent = message;
            
            document.body.appendChild(notification);
            
            // Auto remove after 4 seconds
            setTimeout(() => {
                if (notification.parentNode) {
                    gsap.to(notification, {
                        duration: 0.5,
                        x: 300,
                        opacity: 0,
                        onComplete: () => {
                            if (notification.parentNode) {
                                notification.parentNode.removeChild(notification);
                            }
                        }
                    });
                }
            }, 4000);
        }

        // Handle window resize
        window.addEventListener('resize', function() {
            camera.aspect = window.innerWidth / window.innerHeight;
            camera.updateProjectionMatrix();
            renderer.setSize(window.innerWidth, window.innerHeight);
        });

        // Keyboard shortcuts
        document.addEventListener('keydown', function(event) {
            if (!gameState || !gameState.can_act) return;
            
            switch(event.key.toLowerCase()) {
                case 'f':
                    if (document.getElementById('foldBtn').style.display !== 'none') {
                        playerAction('fold');
                    }
                    break;
                case 'c':
                    if (document.getElementById('checkBtn').style.display !== 'none') {
                        playerAction('check');
                    } else if (document.getElementById('callBtn').style.display !== 'none') {
                        playerAction('call');
                    }
                    break;
                case 'r':
                    if (document.getElementById('raiseBtn').style.display !== 'none') {
                        playerAction('raise');
                    }
                    break;
                case 'a':
                    if (document.getElementById('allInBtn').style.display !== 'none') {
                        playerAction('all_in');
                    }
                    break;
                case 'enter':
                    if (document.activeElement.id === 'chatInput') {
                        sendChat();
                    }
                    break;
            }
        });

        // Initialize everything when page loads
        window.addEventListener('load', function() {
            initThreeJS();
            connectWebSocket();
            
            // Show loading screen initially
            showLoadingScreen();
        });

        // Add CSS animations for timer
        const style = document.createElement('style');
        style.textContent = `
            @keyframes timerPulse {
                0%, 100% { transform: translateX(-50%) scale(1); }
                50% { transform: translateX(-50%) scale(1.1); }
            }
        `;
        document.head.appendChild(style);
    </script>
</body>
</html>
"""

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run(app, host="0.0.0.0", port=port)
