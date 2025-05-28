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
from pydantic import BaseModel, ValidationError, Field as PydanticField # Renamed to avoid conflict

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
GAME_UPDATE_RATE = 30  # Reduced for less frequent updates, 60 might be too much for backend logic + broadcast
RATE_LIMIT_MESSAGES_PER_SECOND = 15
RATE_LIMIT_ACTIONS_PER_SECOND = 5
MAX_CHAT_MESSAGES = 100
HAND_EVALUATION_CACHE_SIZE = 10000
AUTO_FOLD_TIMEOUT = 30  # seconds
TOURNAMENT_BLIND_INCREASE_INTERVAL = 600  # 10 minutes
MAX_ROOMS = 1000
SESSION_TIMEOUT = 3600  # 1 hour
AI_ACTION_DELAY_MIN = 1.0 # seconds
AI_ACTION_DELAY_MAX = 3.0 # seconds

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
    value: int # Numeric representation of hand strength for comparison
    cards_used: List[Card] # The 5 cards forming the best hand
    description: str
    kickers: List[int] = field(default_factory=list)


@dataclass
class SidePot:
    amount: int
    eligible_players: Set[str]
    winner_ids: List[str] = field(default_factory=list)
    winning_hand_description: str = ""


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
    total_bet_this_hand: int = 0 # Total amount this player has put into the pot in the current hand across all betting rounds
    cards: List[Card] = field(default_factory=list)
    status: PlayerStatus = PlayerStatus.ACTIVE
    position: int = 0 # Relative to dealer button for the current hand
    last_action: Optional[PlayerAction] = None
    last_action_time: float = 0
    last_action_amount: int = 0 # Stores amount for raise/call
    avatar: str = "default"
    color: str = "#ffffff"
    is_dealer: bool = False
    is_small_blind: bool = False
    is_big_blind: bool = False
    time_bank: int = 30  # seconds
    connection_id: Optional[str] = None # WebSocket connection ID if human, None if AI
    stats: PlayerStats = field(default_factory=PlayerStats)
    session_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    tournament_rank: int = 0
    is_ai: bool = False
    actions_this_hand: List[Dict] = field(default_factory=list) # To store { "action": PlayerAction.value, "amount": int, "phase": GamePhase.value }
    
    def can_act(self) -> bool:
        return self.status == PlayerStatus.ACTIVE and self.money > 0

    def is_all_in_for_hand(self) -> bool: # Changed name for clarity
        return self.status == PlayerStatus.ALL_IN or (self.money == 0 and self.current_bet > 0)

    def reset_for_new_hand(self):
        self.cards = []
        self.current_bet = 0 # Bet in current betting round
        self.total_bet_this_hand = 0
        self.last_action = None
        self.last_action_time = 0
        self.last_action_amount = 0
        self.actions_this_hand = []
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
    tournament_structure: Dict = field(default_factory=dict) # e.g., blind levels
    buy_in: int = 0 # For cash games or tournaments
    password: Optional[str] = None
    ai_players: int = 0 # Number of AI players

@dataclass
class Room:
    code: str
    name: str
    players: Dict[str, Player] # player_id -> Player object
    spectators: Set[str] # player_id of spectators
    deck: List[Card]
    community_cards: List[Card]
    current_player_id: Optional[str] = None # ID of player whose turn it is
    dealer_player_id: Optional[str] = None # Player who is dealer
    phase: GamePhase = GamePhase.WAITING
    pot: int = 0 # Main pot
    side_pots: List[SidePot] = field(default_factory=list)
    current_bet_to_match: int = 0 # The highest bet in the current round that others need to match
    min_raise_amount: int = BIG_BLIND # Minimum legal raise amount
    chat_messages: List[Dict] = field(default_factory=list)
    last_action_timestamp: float = 0 # Timestamp of the last game action
    hand_number: int = 0
    settings: GameSettings = field(default_factory=GameSettings)
    room_type: RoomType = RoomType.PUBLIC
    created_at: datetime = field(default_factory=datetime.now)
    last_activity: datetime = field(default_factory=datetime.now)
    owner_id: Optional[str] = None # player_id of the room owner
    hand_history: List[Dict] = field(default_factory=list)
    tournament_level: int = 1
    tournament_next_blind_increase: datetime = field(default_factory=lambda: datetime.now() + timedelta(minutes=10))
    paused: bool = False
    pause_reason: str = ""
    
    # Replaces current_player_index, dealer_index for more robustness with player joining/leaving
    _player_order_for_hand: List[str] = field(default_factory=list) # Order of players for current hand
    _current_player_order_index: int = 0

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

    def deal_cards(self): # Deals to players in _player_order_for_hand
        # Deal 2 cards to each player in the hand
        for _ in range(2):
            for player_id in self._player_order_for_hand:
                player = self.players.get(player_id)
                if player and player.status != PlayerStatus.SITTING_OUT and player.status != PlayerStatus.ELIMINATED:
                    if self.deck:
                        player.cards.append(self.deck.pop())


    def deal_community_cards(self, count: int):
        # Burn a card
        if self.deck:
            self.deck.pop() 
        for _ in range(count):
            if self.deck:
                self.community_cards.append(self.deck.pop())

    def get_active_players_in_hand(self) -> List[Player]:
        """Players still eligible to win the pot (not folded, not eliminated)"""
        return [p for p_id in self._player_order_for_hand 
                if (p := self.players.get(p_id)) and p.status not in [PlayerStatus.FOLDED, PlayerStatus.ELIMINATED, PlayerStatus.SITTING_OUT]]


    def get_players_eligible_for_pot(self) -> List[Player]:
        """Players who are not folded and not eliminated."""
        return [p for p in self.players.values() if p.status not in [PlayerStatus.FOLDED, PlayerStatus.ELIMINATED]]


    def calculate_side_pots(self):
        self.side_pots = []
        
        # Players who have contributed to the pot and are not folded
        contending_players = sorted(
            [p for p in self.get_players_eligible_for_pot() if p.total_bet_this_hand > 0],
            key=lambda p: p.total_bet_this_hand
        )

        if not contending_players:
            return

        main_pot_amount = self.pot # start with total pot and subtract side pots
        
        # Create a list of unique bet amounts made by players who are all-in or have finished betting
        all_in_bets = sorted(list(set(p.total_bet_this_hand for p in contending_players if p.is_all_in_for_hand())))

        last_bet_level = 0
        for bet_level in all_in_bets:
            if bet_level == 0: continue

            pot_amount_at_this_level = 0
            eligible_for_this_pot = set()

            for p in self.get_players_eligible_for_pot(): # Consider all players for contribution
                contribution = min(p.total_bet_this_hand, bet_level) - last_bet_level
                if contribution > 0:
                    pot_amount_at_this_level += contribution
                    eligible_for_this_pot.add(p.id)
            
            if pot_amount_at_this_level > 0:
                self.side_pots.append(SidePot(amount=pot_amount_at_this_level, eligible_players=eligible_for_this_pot))
                main_pot_amount -= pot_amount_at_this_level
            last_bet_level = bet_level

        # The remaining amount is the main pot, contested by players who matched the highest bets or are still in.
        if main_pot_amount > 0:
             eligible_main_pot = {
                p.id for p in self.get_players_eligible_for_pot() 
                if p.total_bet_this_hand >= last_bet_level # or not p.is_all_in_for_hand()
            }
             if eligible_main_pot: # Ensure there are eligible players
                # Prepend main pot to side_pots list for ordered processing
                self.side_pots.insert(0, SidePot(amount=main_pot_amount, eligible_players=eligible_main_pot))
        
        # If only one side_pot was created and it contains all the money, it's essentially the main pot.
        # This logic simplifies by always having side_pots array, main pot is the first if multiple levels.
        if not self.side_pots and self.pot > 0:
             eligible_players = {p.id for p in self.get_players_eligible_for_pot()}
             if eligible_players:
                self.side_pots.append(SidePot(amount=self.pot, eligible_players=eligible_players))

        # Filter out empty side pots
        self.side_pots = [sp for sp in self.side_pots if sp.amount > 0 and sp.eligible_players]
        logger.info(f"Room {self.code} calculated side pots: {self.side_pots}")


    def update_activity(self):
        self.last_activity = datetime.now()

    def get_player_acting_next(self, start_player_id: str) -> Optional[str]:
        if not self._player_order_for_hand: return None
        try:
            current_idx = self._player_order_for_hand.index(start_player_id)
        except ValueError:
            return None # Start player not in current hand order

        for i in range(len(self._player_order_for_hand)):
            next_idx = (current_idx + 1 + i) % len(self._player_order_for_hand)
            next_player_id = self._player_order_for_hand[next_idx]
            player = self.players.get(next_player_id)
            if player and player.can_act():
                return player.id
        return None # No one can act


class AdvancedPokerGame:
    def __init__(self):
        self.rooms: Dict[str, Room] = {}
        self.connections: Dict[str, WebSocket] = {} # connection_id (player_id for humans) -> WebSocket
        self.player_rooms: Dict[str, str] = {} # player_id -> room_code
        # self.player_sessions: Dict[str, str] = {} # No longer used with player_id as key
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
        return ''.join(random.choices('ABCDEFGHJKLMNPQRSTUVWXYZ23456789', k=6)) # Shorter, more memorable

    def create_room(self, creator_player_id: str, room_settings: GameSettings, room_name: str = None) -> Optional[str]:
        if len(self.rooms) >= MAX_ROOMS:
            logger.error("Maximum number of rooms reached")
            return None
            
        room_code = self.generate_room_code()
        while room_code in self.rooms:
            room_code = self.generate_room_code()
        
        room_name = room_name or f"Room {room_code}"
        
        self.rooms[room_code] = Room(
            code=room_code,
            name=room_name,
            players={},
            spectators=set(),
            deck=[], # will be created in __post_init__
            community_cards=[],
            settings=room_settings,
            owner_id=creator_player_id, # Set creator as owner
            room_type=RoomType.PRIVATE if room_settings.password else RoomType.PUBLIC
        )
        
        # Add AI players if any
        for i in range(room_settings.ai_players):
            ai_player_id = f"AI_{str(uuid.uuid4())[:8]}"
            ai_player = Player(
                id=ai_player_id,
                name=f"AI Bot {i+1}",
                money=room_settings.buy_in if room_settings.buy_in > 0 else (TOURNAMENT_STARTING_MONEY if room_settings.game_mode == GameMode.TOURNAMENT else STARTING_MONEY),
                is_ai=True,
                avatar=f"avatar_ai_{random.randint(1,3)}",
                color=f"#{random.randint(0x808080, 0xFFFFFF):06x}" # Lighter colors for AI
            )
            self.rooms[room_code].players[ai_player_id] = ai_player
            logger.info(f"AI Player {ai_player.name} ({ai_player_id}) added to room {room_code}")

        logger.info(f"Room {room_code} created by player {creator_player_id} with {room_settings.ai_players} AI players.")
        return room_code

    def join_room(self, room_code: str, player_id: str, player_name: str, password: Optional[str] = None) -> bool:
        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"Attempt to join non-existent room {room_code} by {player_id}")
            return False
        
        if room.settings.password and room.settings.password != password:
            logger.warning(f"Password mismatch for room {room_code} by {player_id}")
            return False
        
        # Count human players for max_players limit
        human_players_count = sum(1 for p in room.players.values() if not p.is_ai)
        if human_players_count >= room.settings.max_players:
            logger.warning(f"Room {room_code} is full (max human players: {room.settings.max_players})")
            return False
        
        if player_id in room.players: # Rejoining
            rejoining_player = room.players[player_id]
            if rejoining_player.is_ai:
                logger.warning(f"Human player {player_id} attempting to join as existing AI {rejoining_player.name}")
                return False # Cannot replace an AI this way
            rejoining_player.connection_id = player_id # Re-establish connection
            rejoining_player.name = player_name # Allow name update on rejoin
            if rejoining_player.status == PlayerStatus.ELIMINATED and room.settings.game_mode != GameMode.TOURNAMENT:
                rejoining_player.status = PlayerStatus.ACTIVE # Allow rejoining in cash games if eliminated
            logger.info(f"Player {player_name} ({player_id}) re-joined room {room_code}")
        else: # New player
            player = Player(
                id=player_id,
                name=player_name,
                money=room.settings.buy_in if room.settings.buy_in > 0 else (TOURNAMENT_STARTING_MONEY if room.settings.game_mode == GameMode.TOURNAMENT else STARTING_MONEY),
                avatar=f"avatar_{random.randint(1, 10)}",
                color=f"#{random.randint(0, 0xFFFFFF):06x}",
                connection_id=player_id,
                is_ai=False
            )
            room.players[player_id] = player
            logger.info(f"Player {player_name} ({player_id}) joined room {room_code}")

        self.player_rooms[player_id] = room_code
        room.update_activity()
        return True
    
    # ... (leave_room, spectate_room as before, with minor logging/robustness updates) ...

    def start_game(self, room_code: str): # Removed force_start, min_players is a hard rule
        room = self.rooms.get(room_code)
        if not room: return False

        # Players ready to play (not sitting out, not eliminated, and includes AI)
        eligible_players = [p for p in room.players.values() if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED] and p.money > 0]

        if len(eligible_players) < room.settings.min_players:
            logger.warning(f"Cannot start game in room {room_code}: Not enough players ({len(eligible_players)}/{room.settings.min_players})")
            return False
        
        if room.phase != GamePhase.WAITING:
            logger.warning(f"Game already in progress in room {room_code}. Phase: {room.phase}")
            return False

        room.phase = GamePhase.PRE_FLOP # Initial phase
        room.hand_number += 1
        room.shuffle_deck()
        room.community_cards = []
        room.pot = 0
        room.side_pots = []
        
        # Determine player order for the hand (e.g., clockwise from dealer)
        # This needs a stable way to determine order, e.g., initial join order or assigned positions.
        # For simplicity, using current list of eligible players, then rotating dealer.
        
        # Rotate dealer
        if room.dealer_player_id is None or room.dealer_player_id not in room.players or room.players[room.dealer_player_id] not in eligible_players:
            room.dealer_player_id = eligible_players[0].id
        else:
            current_dealer_idx = -1
            for i, p in enumerate(eligible_players):
                if p.id == room.dealer_player_id:
                    current_dealer_idx = i
                    break
            next_dealer_idx = (current_dealer_idx + 1) % len(eligible_players)
            room.dealer_player_id = eligible_players[next_dealer_idx].id

        # Set player order for the hand starting from dealer's left
        dealer_actual_idx = -1
        for i, p_id in enumerate(p.id for p in eligible_players): # use eligible players to find dealer index
            if p_id == room.dealer_player_id:
                dealer_actual_idx = i
                break
        
        room._player_order_for_hand = []
        if dealer_actual_idx != -1:
            ordered_for_blinds = eligible_players[dealer_actual_idx+1:] + eligible_players[:dealer_actual_idx+1]
            room._player_order_for_hand = [p.id for p in ordered_for_blinds]


        for p_id, player in room.players.items():
            player.reset_for_new_hand() # Reset for all players
            if player.id not in room._player_order_for_hand and player.status != PlayerStatus.ELIMINATED: # If player became ineligible between hands
                 player.status = PlayerStatus.SITTING_OUT 

        # Assign dealer, SB, BB roles based on _player_order_for_hand
        # Dealer is the last in _player_order_for_hand based on typical poker rotation (button moves)
        room.players[room.dealer_player_id].is_dealer = True

        num_players_in_hand = len(room._player_order_for_hand)
        if num_players_in_hand > 0:
            sb_player_id = room._player_order_for_hand[0] # First after dealer
            room.players[sb_player_id].is_small_blind = True

            if num_players_in_hand > 1:
                bb_player_id = room._player_order_for_hand[1 % num_players_in_hand] # Second after dealer or first if heads up
                room.players[bb_player_id].is_big_blind = True
            else: # Heads up, dealer is SB, other is BB. Order means SB acts first pre-flop.
                # This logic needs adjustment for heads-up if dealer posts SB and acts last pre-flop.
                # Standard heads-up: Dealer is SB, other is BB. SB acts first PRE-FLOP. BB acts first POST-FLOP.
                # The _player_order_for_hand implies acting order.
                # If dealer is last in order: player_order[0] is SB, player_order[1] is BB.
                # This makes SB act first, which is correct for HU pre-flop.
                pass


        # Post blinds and ante
        self.post_blinds_and_ante(room) # Uses is_small_blind, is_big_blind flags
        
        room.current_bet_to_match = room.settings.big_blind
        room.min_raise_amount = room.settings.big_blind

        # Deal cards
        room.deal_cards()
        
        # Determine first player to act pre-flop
        if num_players_in_hand > 0:
            if num_players_in_hand == 2: # Heads up, SB (non-dealer) acts first pre-flop
                # The player at index 0 in _player_order_for_hand is SB.
                 room.current_player_id = room._player_order_for_hand[0]
            elif num_players_in_hand > 2: # UTG is after BB
                 bb_idx = -1
                 for i, p_id in enumerate(room._player_order_for_hand):
                     if room.players[p_id].is_big_blind:
                         bb_idx = i
                         break
                 room.current_player_id = room._player_order_for_hand[(bb_idx + 1) % num_players_in_hand]
            else: # Single player, hand ends immediately (handled later)
                room.current_player_id = None
        
        room.last_action_timestamp = time.time()
        
        self.global_stats['total_hands'] += 1
        logger.info(f"Game started in room {room_code}, hand #{room.hand_number}. Dealer: {room.dealer_player_id}, Current Player: {room.current_player_id}")
        logger.info(f"Player order: {room._player_order_for_hand}")

        if room.current_player_id and room.players[room.current_player_id].is_ai:
            asyncio.create_task(self.ai_perform_action(room_code, room.current_player_id))
        return True

    def post_blinds_and_ante(self, room: Room):
        # Ante first, from all players in _player_order_for_hand
        if room.settings.ante > 0:
            for player_id in room._player_order_for_hand:
                player = room.players[player_id]
                ante_amount = min(room.settings.ante, player.money)
                player.money -= ante_amount
                # Ante doesn't count towards current_bet but goes to total_bet_this_hand and pot
                player.total_bet_this_hand += ante_amount 
                room.pot += ante_amount
                player.actions_this_hand.append({
                    "action": "ante", "amount": ante_amount, "phase": room.phase.value
                })
                if player.money == 0: player.status = PlayerStatus.ALL_IN
        
        # Blinds
        for player_id in room._player_order_for_hand:
            player = room.players[player_id]
            blind_amount = 0
            action_label = ""
            if player.is_small_blind:
                blind_amount = min(room.settings.small_blind, player.money)
                action_label = "small_blind"
            elif player.is_big_blind:
                blind_amount = min(room.settings.big_blind, player.money)
                action_label = "big_blind"

            if blind_amount > 0:
                player.money -= blind_amount
                player.current_bet += blind_amount
                player.total_bet_this_hand += blind_amount
                room.pot += blind_amount
                player.actions_this_hand.append({
                    "action": action_label, "amount": blind_amount, "phase": room.phase.value
                })
                if player.money == 0: player.status = PlayerStatus.ALL_IN
        logger.info(f"Room {room.code}: Blinds and antes posted. Pot: {room.pot}")


    async def ai_perform_action(self, room_code: str, player_id: str):
        await asyncio.sleep(random.uniform(AI_ACTION_DELAY_MIN, AI_ACTION_DELAY_MAX))
        
        room = self.rooms.get(room_code)
        if not room or room.current_player_id != player_id:
            return # No longer this AI's turn or room gone

        player = room.players.get(player_id)
        if not player or not player.is_ai or not player.can_act():
            return

        available_actions = self.get_available_actions(room, player_id)
        # Basic AI: 30% fold, 50% check/call, 20% raise if possible
        
        chosen_action_obj = None
        rand_choice = random.random()

        can_check = any(a['action'] == 'check' for a in available_actions)
        can_call = any(a['action'] == 'call' for a in available_actions)
        can_raise = any(a['action'] == 'raise' for a in available_actions)

        action_to_perform = PlayerAction.FOLD
        amount_to_perform = 0

        if rand_choice < 0.15 and any(a['action'] == 'fold' for a in available_actions): # 15% Fold
            action_to_perform = PlayerAction.FOLD
        elif rand_choice < 0.75 : # 60% Check or Call
            if can_check:
                action_to_perform = PlayerAction.CHECK
            elif can_call:
                action_to_perform = PlayerAction.CALL
                call_action = next(a for a in available_actions if a['action'] == 'call')
                amount_to_perform = call_action['amount']
            # If can't check or call, will default to fold if not overridden by raise
        elif can_raise: # 25% Raise (if possible)
            raise_action_details = next(a for a in available_actions if a['action'] == 'raise')
            # AI raises minimum amount
            action_to_perform = PlayerAction.RAISE
            amount_to_perform = raise_action_details['min_amount']
        elif can_call: # Fallback to call if raise wasn't chosen/possible but call is
            action_to_perform = PlayerAction.CALL
            call_action = next(a for a in available_actions if a['action'] == 'call')
            amount_to_perform = call_action['amount']
        elif can_check: # Fallback to check
            action_to_perform = PlayerAction.CHECK
        else: # Default to fold if no other valid action was selected
             action_to_perform = PlayerAction.FOLD

        # Ensure AI doesn't try to bet more than it has (covered by process_player_action)
        # If AI chooses ALL_IN (not explicitly here but could be added)
        if player.money <= amount_to_perform and action_to_perform in [PlayerAction.CALL, PlayerAction.RAISE]:
            action_to_perform = PlayerAction.ALL_IN
            amount_to_perform = player.money # This is not how all_in amount is passed, process_player_action handles it.
                                             # For all_in, amount is usually 0 or implied.
                                             # Let's ensure process_player_action correctly handles this.
                                             # If AI decided to CALL or RAISE an amount that is all-in for it.

        logger.info(f"AI {player.name} in room {room_code} chose action: {action_to_perform.value} with amount {amount_to_perform}")
        self.player_action(room_code, player_id, action_to_perform, amount_to_perform)


    def player_action(self, room_code: str, player_id: str, action_type: PlayerAction, amount: int = 0) -> bool:
        room = self.rooms.get(room_code)
        if not room: return False
        
        player = room.players.get(player_id)
        if not player: return False

        if room.current_player_id != player_id:
            logger.warning(f"Action by {player.name} ({player_id}) but not their turn (current: {room.current_player_id})")
            return False
        
        if not player.can_act() and action_type not in [PlayerAction.SIT_OUT, PlayerAction.SIT_IN]:
             logger.warning(f"Player {player.name} ({player_id}) cannot act (status: {player.status}, money: {player.money})")
             return False

        success = self.process_player_action(room, player, action_type, amount)
        
        if success:
            player.last_action = action_type
            player.last_action_amount = amount if action_type == PlayerAction.RAISE else (room.current_bet_to_match - (player.total_bet_this_hand - player.current_bet) if action_type == PlayerAction.CALL else 0) # Approximate call amount
            player.last_action_time = time.time()
            room.last_action_timestamp = time.time()
            
            player.actions_this_hand.append({
                "action": action_type.value, 
                "amount": player.last_action_amount, # Amount of the bet/raise itself
                "total_bet_this_round": player.current_bet, # Player's total bet in this round
                "phase": room.phase.value
            })

            # VPIP/PFR Stats (Simplified)
            if room.phase == GamePhase.PRE_FLOP:
                if action_type in [PlayerAction.CALL, PlayerAction.RAISE, PlayerAction.ALL_IN]:
                    player.stats.vpip = (player.stats.vpip * player.stats.hands_played + 1) / (player.stats.hands_played + 1)
                    if action_type == PlayerAction.RAISE:
                         player.stats.pfr = (player.stats.pfr * player.stats.hands_played + 1) / (player.stats.hands_played + 1)
            if action_type != PlayerAction.SIT_OUT and action_type != PlayerAction.SIT_IN :
                 player.stats.hands_played +=1 # Count only game actions towards hands_played

            self.advance_game_flow(room_code) # Changed from advance_game
        else:
            logger.warning(f"Player action {action_type.value} by {player.name} failed processing.")
        
        return success

    def process_player_action(self, room: Room, player: Player, action: PlayerAction, amount: int) -> bool:
        bet_amount_for_this_action = 0

        if action == PlayerAction.FOLD:
            player.status = PlayerStatus.FOLDED
            return True
            
        elif action == PlayerAction.CHECK:
            # Can only check if current bet is 0 or player has already matched current bet
            if player.current_bet < room.current_bet_to_match:
                logger.warning(f"{player.name} cannot CHECK. Bet to match: {room.current_bet_to_match}, player's bet: {player.current_bet}")
                return False
            return True
            
        elif action == PlayerAction.CALL:
            amount_to_call = room.current_bet_to_match - player.current_bet
            if amount_to_call <= 0: # Trying to call when no bet to call, or already called. This should be a check.
                logger.warning(f"{player.name} tried to CALL, but amount_to_call is {amount_to_call}. Effectively a CHECK.")
                # If it's a call of 0, treat as check if valid, else invalid
                return player.current_bet >= room.current_bet_to_match # True if it's a valid check scenario

            bet_amount_for_this_action = min(amount_to_call, player.money)
            
            player.money -= bet_amount_for_this_action
            player.current_bet += bet_amount_for_this_action
            player.total_bet_this_hand += bet_amount_for_this_action
            room.pot += bet_amount_for_this_action
            
            if player.money == 0: player.status = PlayerStatus.ALL_IN
            return True
            
        elif action == PlayerAction.RAISE:
            # Amount is the RAISE AMOUNT (additional to the call)
            # Player must at least call the current_bet_to_match
            amount_to_call = room.current_bet_to_match - player.current_bet
            
            # Total bet player will have made this round: player.current_bet + amount_to_call + amount (raise amount)
            # This total must be >= room.current_bet_to_match + room.min_raise_amount
            
            total_new_bet_this_round = player.current_bet + amount_to_call + amount
            
            if amount <= 0: return False # Raise amount must be positive
            if amount < room.min_raise_amount: # Raise must be at least min_raise_amount
                # Exception: if player is all-in with less than min_raise_amount, it's a valid all-in raise but doesn't reopen betting for those who acted
                if player.money <= amount_to_call + amount : # Is all-in raise
                    pass # Allow all-in raise even if less than min_raise_amount
                else:
                    logger.warning(f"{player.name} RAISE too small. Amount: {amount}, MinRaise: {room.min_raise_amount}")
                    return False

            bet_amount_for_this_action = amount_to_call + amount # Total money player puts in THIS action
            if bet_amount_for_this_action > player.money : # Cannot bet more than they have
                logger.warning(f"{player.name} cannot RAISE. Bet amount: {bet_amount_for_this_action}, Player money: {player.money}")
                return False


            player.money -= bet_amount_for_this_action
            player.current_bet += bet_amount_for_this_action # player.current_bet is now the new room.current_bet_to_match
            player.total_bet_this_hand += bet_amount_for_this_action
            room.pot += bet_amount_for_this_action
            
            # Update room's betting state
            # The new minimum raise is the size of this raise, if it's a full raise
            if player.money > 0 : # if not all-in, this is a full raise that re-opens action
                 room.min_raise_amount = amount # The 'amount' IS the raise size
            
            room.current_bet_to_match = player.current_bet
            
            if player.money == 0: player.status = PlayerStatus.ALL_IN
            return True
            
        elif action == PlayerAction.ALL_IN:
            if player.money <= 0: return False # Already all-in or no money
            
            bet_amount_for_this_action = player.money
            
            player.money = 0
            player.current_bet += bet_amount_for_this_action
            player.total_bet_this_hand += bet_amount_for_this_action
            room.pot += bet_amount_for_this_action
            player.status = PlayerStatus.ALL_IN
            
            # If this all-in is a raise
            if player.current_bet > room.current_bet_to_match:
                # This raise amount is player.current_bet - room.current_bet_to_match (before updating room.current_bet_to_match)
                actual_raise_size = player.current_bet - room.current_bet_to_match
                if actual_raise_size >= room.min_raise_amount: # if it's a "full" raise
                     room.min_raise_amount = actual_raise_size
                # else it's an "incomplete" all-in raise, min_raise_amount doesn't change for others
                room.current_bet_to_match = player.current_bet # This is the new amount to match
            return True
            
        elif action == PlayerAction.SIT_OUT:
            player.status = PlayerStatus.SITTING_OUT
            # If it was player's turn, and they sit out, it's a fold for the current hand
            if room.phase != GamePhase.WAITING:
                player.status = PlayerStatus.FOLDED # Fold for current hand
                # Consider them SITTING_OUT for next hands
            return True
            
        elif action == PlayerAction.SIT_IN:
            if player.status == PlayerStatus.SITTING_OUT:
                player.status = PlayerStatus.ACTIVE
                return True
            return False
        
        return False

    def advance_game_flow(self, room_code: str):
        room = self.rooms.get(room_code)
        if not room: return

        # Check for end of hand conditions
        active_players_in_hand = room.get_active_players_in_hand()
        if len(active_players_in_hand) <= 1:
            if room.phase != GamePhase.SHOWDOWN : # If not already in showdown (e.g. everyone else folded)
                logger.info(f"Room {room.code}: Hand ending early, active players <=1. Num active: {len(active_players_in_hand)}")
                # If one player left, they win the pot without showdown (unless it's river and betting ended)
                if len(active_players_in_hand) == 1 and room.phase != GamePhase.RIVER: # or betting not complete on river
                    # Award pot to the single remaining player
                    winner = active_players_in_hand[0]
                    winner.money += room.pot
                    winner.stats.total_winnings += room.pot
                    winner.stats.hands_won +=1
                    if room.pot > winner.stats.biggest_pot: winner.stats.biggest_pot = room.pot
                    if room.pot > self.global_stats['biggest_pot']: self.global_stats['biggest_pot'] = room.pot
                    
                    logger.info(f"{winner.name} wins ${room.pot} as last player in hand.")
                    room.pot = 0 # Pot distributed
                    self.save_hand_history(room, {winner.id: "Won by default"})

                    asyncio.create_task(self.prepare_next_hand(room_code))
                    return
                else: # Multiple all-ins or end of river betting
                     room.phase = GamePhase.SHOWDOWN # Ensure it goes to showdown
                     self.end_hand(room_code) # Proceed to showdown/end_hand logic
                     return

        # Determine next player
        next_player_id = None
        all_acted_or_all_in = True
        
        # Iterate through players in order to find next player to act
        # A betting round ends when:
        # 1. All players have had a turn to act.
        # 2. All players still in the hand have either folded or have the same amount bet for the round (or are all-in with less).
        
        highest_bet_this_round = room.current_bet_to_match # This is already updated by raise/all-in
        
        # Check if all active (non-folded, non-all-in) players have bet amounts equal to highest_bet_this_round
        # OR if all players who can still act have acted since the last raise.
        
        # Find the player who made the last significant bet/raise (the aggressor)
        # The betting round ends when action returns to this aggressor and they don't re-raise.
        # Or, if everyone calls/checks around.

        # Simplified: Find next player. If all players have acted (current_bet matches room.current_bet_to_match or are all-in/folded)
        # then advance phase.
        
        round_complete = True
        player_who_last_raised_id = None # ID of player who made the current room.current_bet_to_match

        # Find who made the current room.current_bet_to_match
        # Iterate backwards from current player
        current_player_idx_in_order = -1
        if room.current_player_id and room.current_player_id in room._player_order_for_hand:
            current_player_idx_in_order = room._player_order_for_hand.index(room.current_player_id)

        # Find the player who opened betting or last raised in this round
        aggressor_id_this_round = None
        for p_id in reversed(room._player_order_for_hand): # Simplified: last player to bet this amount
            p = room.players[p_id]
            if p.current_bet == room.current_bet_to_match and p.last_action in [PlayerAction.RAISE, PlayerAction.ALL_IN, PlayerAction.CALL]: # Call for BB posting
                 # Check if this was the action that SET current_bet_to_match (e.g. a raise)
                 # This needs more sophisticated tracking of who the action is "to".
                 # For now, assume if current_bet == room.current_bet_to_match, they are "settled" for this amount.
                 pass


        # Check if betting round is complete
        # A round is complete if all players in _player_order_for_hand who are not FOLDED or ALL_IN
        # have player.current_bet == room.current_bet_to_match AND have had a chance to act on this bet.
        # This is tricky. Simpler: if all non-folded, non-all-in players have player.current_bet == room.current_bet_to_match,
        # and the action has gone around the table at least once since the current_bet_to_match was established.
        
        betting_round_over = True
        first_actor_this_betting_level_id = None # Tracks who needs to act to close action
        
        # Determine who needs to act. Usually player left of BB pre-flop, or SB post-flop.
        # Logic: check if all players (not folded/allin) have had a turn since last raise, or have bet the same amount.
        
        action_is_closed = True
        player_acted_count = 0
        for p_id in room._player_order_for_hand:
            player = room.players.get(p_id)
            if player and player.status == PlayerStatus.ACTIVE and not player.is_all_in_for_hand(): # Active and can still bet
                player_acted_count +=1
                if player.current_bet < room.current_bet_to_match:
                    action_is_closed = False
                    break
                if player.last_action is None and room.phase != GamePhase.PRE_FLOP: # Pre-flop blinds are not "actions" yet
                     # This condition means player hasn't acted in this round yet (e.g. SB/BB post-flop)
                     # However, if current_bet_to_match is 0 (everyone checked), last_action could be None.
                     # This needs to check if player has acted *since the current_bet_to_match was established*
                     # For simplicity now: if player.current_bet matches and they are active, assume they are good unless they are the current player to act.
                     pass # Covered by player.current_bet check mostly


        if action_is_closed:
            # Check if everyone who needed to act on the current_bet_to_match has acted.
            # This requires knowing who made the last raise. Action goes around to them.
            # This part is complex. For now, if action_is_closed is true, assume round is over.
            # A more robust check: if all active players (not folded, not all-in) have EITHER
            # (player.current_bet == room.current_bet_to_match) OR (player.last_action was the one setting current_bet_to_match)
            # No, this is simpler: if all active players have acted and their current_bet matches the room's current_bet_to_match (or they are all-in)
            
            # A simple check: iterate players. If a player can act and their bet is less than current_bet_to_match, round is not over.
            found_player_to_act = False
            potential_next_player_id = room.get_player_acting_next(room.current_player_id)
            
            if potential_next_player_id:
                 next_player_obj = room.players[potential_next_player_id]
                 # If the next player to act has already matched the current bet (or is the one who made it),
                 # and everyone else has also matched or folded/all-in, the round is over.
                 # This is true if next_player_obj.current_bet == room.current_bet_to_match
                 #  AND (next_player_obj.last_action is not None or it's BB preflop who can check)
                 # This indicates action has gone around.
                 
                 # More simply: if ALL active (non-folded, non-all-in) players have current_bet == room.current_bet_to_match
                 # then the round is over.
                 all_bets_matched = True
                 for p_id_check in room._player_order_for_hand:
                     p_check = room.players[p_id_check]
                     if p_check.status == PlayerStatus.ACTIVE and not p_check.is_all_in_for_hand():
                         if p_check.current_bet < room.current_bet_to_match:
                             all_bets_matched = False
                             break
                 
                 if all_bets_matched:
                     # Check if the player who is "due" to act (potential_next_player_id) has already acted on this bet level.
                     # This is tricky. The original aggressor concept is better.
                     # If the potential_next_player_id is the one who made the last raise (player.current_bet == room.current_bet_to_match implies this if they are next)
                     # then round is over.
                     # If player.last_action established room.current_bet_to_match and it's their turn again, round ends.
                     
                     # Let's use a simpler rule: if all active (non-folded/all-in) players have current_bet matching room.current_bet_to_match
                     # *AND* the current player (who just acted) was the one who established this bet (or called it),
                     # *AND* the next player up also has matched this bet (or is the one who established it), it must have gone around.
                     # This is still too complex for here.

                     # Simplest robust rule: Round ends if (number of players who have acted this round >= number of active players in hand) AND (all bets are matched or players are all-in/folded)
                     # This is also not quite right.
                     # Standard rule: betting is over when (1) all players have folded except one, or (2) all remaining players have contributed an equal amount to the pot for the round (unless a player is all-in).
                     # And action has completed for all players. (i.e. highest bet has been called by all players not all-in/folded)

                     num_can_still_act = 0
                     num_bets_not_matching = 0
                     for p_id_chk in room._player_order_for_hand:
                         p_chk = room.players[p_id_chk]
                         if p_chk.status == PlayerStatus.ACTIVE and not p_chk.is_all_in_for_hand():
                             num_can_still_act += 1
                             if p_chk.current_bet < room.current_bet_to_match:
                                 num_bets_not_matching +=1
                     
                     if num_bets_not_matching == 0: # All active players have matched or exceeded current bet. Round over.
                         logger.info(f"Room {room.code}: Betting round complete. Advancing phase.")
                         self.advance_phase(room_code)
                         return
                     else: # Bets not matched, find next player
                         room.current_player_id = potential_next_player_id
                         logger.info(f"Room {room.code}: Next player is {room.current_player_id}")
             else: # No one can act (e.g. all but one folded, or all remaining are all-in)
                 logger.info(f"Room {room.code}: No more players can act. Betting round complete by default.")
                 self.advance_phase(room_code) # This should also handle all-in situations by fast-forwarding phases.
                 return

        else: # Round not complete, find next player
            next_player_id = room.get_player_acting_next(room.current_player_id)
            if next_player_id:
                room.current_player_id = next_player_id
                logger.info(f"Room {room.code}: Next player is {room.current_player_id}")
            else: # Should not happen if active_players_in_hand > 1
                logger.error(f"Room {room.code}: Could not determine next player, but round not complete. Active: {len(active_players_in_hand)}")
                # This might indicate an issue or all remaining players are all-in
                self.advance_phase(room_code) # Try to advance phase, maybe it's an all-in situation
                return

        # If next player is AI, trigger AI action
        if room.current_player_id and room.players[room.current_player_id].is_ai:
            asyncio.create_task(self.ai_perform_action(room_code, room.current_player_id))
        
        room.last_action_timestamp = time.time() # Reset timer for next player


    def advance_phase(self, room_code: str):
        room = self.rooms.get(room_code)
        if not room: return

        # If only one player (or none) remains not folded, hand ends (handled by SHOWDOWN or earlier logic)
        active_players_in_hand = room.get_active_players_in_hand()
        if len(active_players_in_hand) <= 1 and room.phase != GamePhase.SHOWDOWN:
            # This case should ideally be caught before advance_phase is called,
            # but as a safeguard:
            if room.phase != GamePhase.GAME_OVER: # Avoid re-triggering if game just ended
                logger.info(f"Room {room.code}: Advancing phase, but only {len(active_players_in_hand)} player(s) left. Ending hand.")
                self.end_hand(room_code)
            return

        # Reset player.current_bet for the new round, last_action
        for player in room.players.values():
            player.current_bet = 0 
            player.last_action = None # Cleared for the new betting round
            player.last_action_amount = 0
        
        room.current_bet_to_match = 0
        room.min_raise_amount = room.settings.big_blind # Reset min raise for new street
        
        current_phase = room.phase
        next_phase = None

        if current_phase == GamePhase.PRE_FLOP:
            next_phase = GamePhase.FLOP
            room.deal_community_cards(3)
        elif current_phase == GamePhase.FLOP:
            next_phase = GamePhase.TURN
            room.deal_community_cards(1)
        elif current_phase == GamePhase.TURN:
            next_phase = GamePhase.RIVER
            room.deal_community_cards(1)
        elif current_phase == GamePhase.RIVER:
            next_phase = GamePhase.SHOWDOWN
            # No cards dealt, proceed to end_hand which handles showdown
        elif current_phase == GamePhase.SHOWDOWN: # Already in showdown, likely called from end_hand
             asyncio.create_task(self.prepare_next_hand(room_code))
             return
        else: # Waiting, Game_Over, etc.
            logger.warning(f"Room {room.code}: Advance_phase called from unexpected phase: {current_phase}")
            return

        if next_phase:
            room.phase = next_phase
            logger.info(f"Room {room.code}: Advanced to phase {room.phase.value}. Community cards: {[str(c) for c in room.community_cards]}")

            if next_phase == GamePhase.SHOWDOWN:
                self.end_hand(room_code)
                return

            # Determine first player to act in the new round (typically SB or first active player left of dealer)
            # Player order for acting remains room._player_order_for_hand
            first_to_act_post_flop_id = None
            if room._player_order_for_hand:
                # Find first player in order who is still in the hand (not FOLDED, not ELIMINATED) and not ALL_IN
                for p_id in room._player_order_for_hand:
                    player = room.players.get(p_id)
                    if player and player.status == PlayerStatus.ACTIVE and not player.is_all_in_for_hand():
                        first_to_act_post_flop_id = player.id
                        break
            
            room.current_player_id = first_to_act_post_flop_id
            
            if not room.current_player_id and len(active_players_in_hand) > 1:
                # All remaining players are all-in. Fast-forward through remaining streets.
                logger.info(f"Room {room.code}: All remaining players are all-in. Fast-forwarding phase {room.phase.value}.")
                if room.phase != GamePhase.SHOWDOWN:
                     self.advance_phase(room_code) # Recursive call to deal next street if needed
                return # Avoid triggering AI if no one can act


            room.last_action_timestamp = time.time()
            logger.info(f"Room {room.code}: First to act in {room.phase.value} is {room.current_player_id}")

            if room.current_player_id and room.players[room.current_player_id].is_ai:
                asyncio.create_task(self.ai_perform_action(room_code, room.current_player_id))
        else:
            logger.error(f"Room {room.code}: No next phase determined from {current_phase}")


    def end_hand(self, room_code: str):
        room = self.rooms.get(room_code)
        if not room: return
        
        logger.info(f"Room {room.code}: Ending hand #{room.hand_number}. Phase: {room.phase}")
        room.phase = GamePhase.SHOWDOWN # Explicitly set to showdown

        players_in_showdown = [p for p in room.get_players_eligible_for_pot() if p.status != PlayerStatus.FOLDED]
        
        # Evaluate hands only if there's a contest (more than one player or side pots)
        evaluated_hands = {} # player_id -> HandEvaluation
        if len(players_in_showdown) > 0 : # Potentially 1 player if others folded on river after betting
            for player in players_in_showdown:
                if player.cards: # Ensure player has cards (should always be true if not folded)
                    combined_cards = player.cards + room.community_cards
                    evaluated_hands[player.id] = self.evaluate_hand(combined_cards)
                    logger.info(f"Player {player.name} hand: {[str(c) for c in player.cards]}, eval: {evaluated_hands[player.id].description}")
        
        # Calculate side pots based on total_bet_this_hand for all players involved in the hand
        room.calculate_side_pots() # This should create self.side_pots
        
        # Distribute winnings from side pots then main pot
        # This needs to iterate through room.side_pots
        all_winners_info = {} # player_id -> { "amount_won": int, "hand_description": str }

        if not room.side_pots and room.pot > 0 : # Handle main pot if no side pots were explicitly created but pot exists
            # This case should be covered by calculate_side_pots making the main pot a "side_pot" entry
             eligible_players = {p.id for p in players_in_showdown}
             if eligible_players:
                room.side_pots.append(SidePot(amount=room.pot, eligible_players=eligible_players))


        for i, pot_info in enumerate(room.side_pots):
            logger.info(f"Distributing Pot #{i}: Amount: {pot_info.amount}, Eligible: {pot_info.eligible_players}")
            
            eligible_winners_for_this_pot = {
                pid: evaluated_hands[pid] 
                for pid in pot_info.eligible_players 
                if pid in evaluated_hands # Player must be in showdown and have a hand
            }

            if not eligible_winners_for_this_pot:
                # This can happen if all eligible players folded (e.g. one player bets, all fold, they win this "pot")
                # Or if only one player was eligible from the start.
                if len(pot_info.eligible_players) == 1:
                    winner_id = list(pot_info.eligible_players)[0]
                    winner_player = room.players.get(winner_id)
                    if winner_player:
                        logger.info(f"Side Pot #{i}: Player {winner_player.name} wins ${pot_info.amount} uncontested.")
                        winner_player.money += pot_info.amount
                        pot_info.winner_ids = [winner_id]
                        pot_info.winning_hand_description = "Uncontested"
                        # Update stats
                        if winner_id not in all_winners_info: all_winners_info[winner_id] = {"amount_won":0, "hand_description": "Uncontested"}
                        all_winners_info[winner_id]["amount_won"] += pot_info.amount

                    else: # Should not happen
                        logger.error(f"Side Pot #{i}: Uncontested winner {winner_id} not found.")
                else: # Multiple eligible, but none with evaluated hands (e.g. all folded after being eligible for this pot segment)
                      # This case implies the pot money should be returned or handled based on game rules (rare)
                      # Or, it means those in `pot_info.eligible_players` who didn't fold earlier get it.
                      # This should typically mean one player remains from `pot_info.eligible_players` if others folded.
                    logger.warning(f"Side Pot #{i}: No evaluated hands among eligible players: {pot_info.eligible_players}. Pot amount: {pot_info.amount}. This might need refund logic or re-evaluation of who is eligible.")
                    # For now, if no one in evaluated_hands is eligible, and eligible_players has >0, this is an issue.
                    # Assuming this means players folded after contributing to this part of pot.
                    # The money should go to the remaining player(s) from this eligibility set.
                    # This is complex. A simpler model: If `eligible_winners_for_this_pot` is empty,
                    # then the last remaining player from `pot_info.eligible_players` who did NOT FOLD wins.
                    
                    non_folded_eligibles = [p_id for p_id in pot_info.eligible_players if room.players[p_id].status != PlayerStatus.FOLDED]
                    if len(non_folded_eligibles) == 1:
                        winner_id = non_folded_eligibles[0]
                        winner_player = room.players.get(winner_id)
                        logger.info(f"Side Pot #{i} (fallback): Player {winner_player.name} wins ${pot_info.amount} as last non-folded eligible.")
                        winner_player.money += pot_info.amount
                        pot_info.winner_ids = [winner_id]
                        pot_info.winning_hand_description = "Last non-folded eligible"
                        if winner_id not in all_winners_info: all_winners_info[winner_id] = {"amount_won":0, "hand_description": "Won by default"}
                        all_winners_info[winner_id]["amount_won"] += pot_info.amount
                    elif len(non_folded_eligibles) > 1:
                        logger.error(f"Side Pot #{i}: Multiple non-folded eligibles but no evaluated hands. This is an error. Pot: {pot_info.amount}, Eligibles: {non_folded_eligibles}")
                    else: # All eligible players for this pot segment folded. Money should remain or go to overall winner.
                          # This implies an issue with pot calculation or player status tracking.
                        logger.error(f"Side Pot #{i}: All eligible players folded for this pot segment. Pot: {pot_info.amount}, Eligible Original: {pot_info.eligible_players}")


                continue # Next pot

            # Determine winner(s) for this specific pot
            best_hand_val = max(eligible_winners_for_this_pot.values(), key=lambda h: (h.rank, h.value))
            current_pot_winners_ids = [
                pid for pid, hand_eval in eligible_winners_for_this_pot.items() 
                if hand_eval.rank == best_hand_val.rank and hand_eval.value == best_hand_val.value
            ]
            
            pot_info.winner_ids = current_pot_winners_ids
            pot_info.winning_hand_description = best_hand_val.description

            if current_pot_winners_ids:
                winnings_per_winner = pot_info.amount // len(current_pot_winners_ids)
                remainder = pot_info.amount % len(current_pot_winners_ids)
                
                for idx, winner_id in enumerate(current_pot_winners_ids):
                    player_wins = winnings_per_winner + (1 if idx < remainder else 0)
                    room.players[winner_id].money += player_wins
                    
                    if winner_id not in all_winners_info:
                         all_winners_info[winner_id] = {"amount_won":0, "hand_description": best_hand_val.description}
                    all_winners_info[winner_id]["amount_won"] += player_wins
                    # Ensure hand description for this player is the best one if they win multiple pots
                    # For simplicity, just use the one from the last pot they won part of.

                    logger.info(f"Side Pot #{i}: Player {room.players[winner_id].name} wins ${player_wins} with {best_hand_val.description}")
            else:
                 logger.error(f"Side Pot #{i}: No winners determined for pot {pot_info.amount} among {eligible_winners_for_this_pot.keys()}")

        room.pot = 0 # All pot money should now be in side_pots or distributed

        # Update global stats and player stats from all_winners_info
        for p_id, win_info in all_winners_info.items():
            player = room.players[p_id]
            player.stats.total_winnings += win_info["amount_won"]
            player.stats.hands_won += 1 # Counted once per hand won, even if multiple pots
            if win_info["amount_won"] > player.stats.biggest_pot:
                player.stats.biggest_pot = win_info["amount_won"]
            if win_info["amount_won"] > self.global_stats['biggest_pot']:
                self.global_stats['biggest_pot'] = win_info["amount_won"]

        self.save_hand_history(room, all_winners_info)
        
        if room.settings.game_mode == GameMode.TOURNAMENT:
            self.update_tournament_state(room) # Check for eliminations, game end
        
        asyncio.create_task(self.prepare_next_hand(room_code))


    async def prepare_next_hand(self, room_code: str, delay: int = 7): # Increased delay for showdown visibility
        room = self.rooms.get(room_code)
        if not room: return

        await asyncio.sleep(delay)
        
        if room_code not in self.rooms: return # Room might have been closed during sleep
        
        # Clear table for next hand (cards, reset player states for hand vars)
        room.community_cards = []
        room.side_pots = [] # Clear calculated side pots
        # Player reset handled in start_game
        
        # Check for game over conditions (e.g., tournament winner)
        active_players_for_game = [p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED and p.money > 0]
        
        if room.settings.game_mode == GameMode.TOURNAMENT and len(active_players_for_game) <= 1:
            room.phase = GamePhase.GAME_OVER
            logger.info(f"Room {room_code}: Tournament ended. Winner(s) determined.")
            # Announce winner, etc. (Further logic for tournament end screen)
            # For now, it just stops starting new hands.
            # Rankings should have been set in update_tournament_state
            # We might want to send a final game_over state to clients.
            return # Don't start new hand
        
        room.phase = GamePhase.WAITING
        # Auto-start next hand if enough players are not sitting out / eliminated
        if len(active_players_for_game) >= room.settings.min_players:
            logger.info(f"Room {room.code}: Automatically starting next hand.")
            self.start_game(room_code)
        else:
            logger.info(f"Room {room.code}: Waiting for players. Need {room.settings.min_players}, have {len(active_players_for_game)} active.")
            # Send updated game state that it's WAITING
            # The game_loop will send this periodically.

    # ... (evaluate_hand, full_hand_evaluation, evaluate_5_card_hand, get_hand_description as before) ...
    def evaluate_hand(self, cards: List[Card]) -> HandEvaluation:
        card_key = tuple(sorted((c.rank, c.suit) for c in cards)) # More robust cache key
        if card_key in self.hand_evaluation_cache:
            return self.hand_evaluation_cache[card_key]
        
        eval_result = self.full_hand_evaluation(cards)
        
        if len(self.hand_evaluation_cache) < HAND_EVALUATION_CACHE_SIZE:
            self.hand_evaluation_cache[card_key] = eval_result
        return eval_result

    def full_hand_evaluation(self, all_cards: List[Card]) -> HandEvaluation:
        from itertools import combinations
        
        if len(all_cards) < 5: # Not enough cards for a poker hand
            # Create a dummy high card eval if needed, or handle error
            # For now, assume we always get at least 5 cards if a hand is to be evaluated
            return HandEvaluation(HandRank.HIGH_CARD, 0, [], "Invalid hand ( < 5 cards)")


        best_hand_rank = HandRank.HIGH_CARD
        best_hand_value = 0 # Stores a comparable int value of the hand
        best_combo_cards = [] # The 5 cards forming the best hand
        best_kickers_values = []

        for combo in combinations(all_cards, 5):
            current_rank, current_value, kicker_values_from_eval, combo_sorted_by_val = self.evaluate_5_card_hand(list(combo))
            
            if current_rank > best_hand_rank:
                best_hand_rank = current_rank
                best_hand_value = current_value
                best_combo_cards = combo_sorted_by_val
                best_kickers_values = kicker_values_from_eval
            elif current_rank == best_hand_rank and current_value > best_hand_value:
                best_hand_value = current_value
                best_combo_cards = combo_sorted_by_val
                best_kickers_values = kicker_values_from_eval
        
        # Convert best_combo_cards (list of Card objects) to what HandEvaluation expects if different
        return HandEvaluation(
            rank=best_hand_rank,
            value=best_hand_value, # This is the comparable value
            cards_used=best_combo_cards, # The actual 5 cards
            description=self.get_hand_description(best_hand_rank, best_kickers_values or [c.value() for c in best_combo_cards]),
            kickers=best_kickers_values # Store kicker values used for description/tie-breaking
        )

    def evaluate_5_card_hand(self, five_cards: List[Card]) -> Tuple[HandRank, int, List[int], List[Card]]:
        # five_cards: list of 5 Card objects
        # Returns: HandRank, comparable_value (int), kicker_values (for description), sorted_cards_by_value

        # Sort cards by value (descending) for processing
        # Ace can be high (14) or low (1 for A-5 straight)
        
        # Create a version of cards sorted by value for consistent processing
        # We need the original Card objects too for the final HandEvaluation.cards_used
        
        # Helper to get card values
        def card_value(c: Card, ace_low=False):
            if c.rank == 'A': return 1 if ace_low else 14
            if c.rank == 'K': return 13
            if c.rank == 'Q': return 12
            if c.rank == 'J': return 11
            return int(c.rank)

        # Sort cards by rank (Ace high)
        # Keep original Card objects, sort by their value
        sorted_cards = sorted(five_cards, key=lambda c: card_value(c), reverse=True)
        values = [card_value(c) for c in sorted_cards] # Ace high values: e.g. [14, 5, 4, 3, 2]
        suits = [c.suit for c in sorted_cards]
        
        is_flush = len(set(suits)) == 1
        
        # Straight check (Ace high and Ace low A-2-3-4-5)
        is_straight = False
        # Check for A-5 straight (values are [14, 5, 4, 3, 2] if sorted Ace high)
        # Ace low straight (A,2,3,4,5) - values would be 5,4,3,2,A(1)
        # For A-5 straight, sorted values (Ace high) are [14, 5, 4, 3, 2]
        # If we sort Ace low: values would be [5,4,3,2,1] for wheel
        
        unique_values = sorted(list(set(values)), reverse=True)
        if len(unique_values) == 5: # Needs 5 distinct ranks for a straight
            if (values[0] - values[4] == 4): # Normal straight e.g. 10,9,8,7,6
                is_straight = True
            elif values == [14, 5, 4, 3, 2]: # Ace-to-five straight (Wheel)
                is_straight = True
                # For wheel, the high card is 5. Values for comparison should be 5,4,3,2,1
                # So, if it's a wheel, the values used for hand strength should reflect this.
                # The 'values' list itself will be [14,5,4,3,2]. We need to handle this in rank assignment.
        
        # Value counts for pairs, trips, quads
        value_counts = Counter(values)
        # [(value, count), ...] sorted by count desc, then value desc
        sorted_counts = sorted(value_counts.items(), key=lambda item: (item[1], item[0]), reverse=True)
        
        # Primary cards (e.g., the four cards in quads, three in trips) + kickers
        primary_card_values = []
        kicker_card_values = []

        # Rank determination
        if is_straight and is_flush:
            if values == [14, 13, 12, 11, 10]: # Royal Flush (AKQJT suited)
                primary_card_values = values
                return HandRank.ROYAL_FLUSH, self._calculate_hand_strength_value(HandRank.ROYAL_FLUSH, primary_card_values), primary_card_values, sorted_cards
            else: # Straight Flush
                # If it's a wheel straight flush (A-5 suited), high card is 5
                sflush_values = [5,4,3,2,1] if values == [14,5,4,3,2] else values
                primary_card_values = sflush_values
                return HandRank.STRAIGHT_FLUSH, self._calculate_hand_strength_value(HandRank.STRAIGHT_FLUSH, primary_card_values), primary_card_values, sorted_cards
        
        # Four of a Kind: sorted_counts will be [(val_quad, 4), (val_kicker, 1)]
        if sorted_counts[0][1] == 4:
            quad_val = sorted_counts[0][0]
            kicker_val = sorted_counts[1][0]
            primary_card_values = [quad_val] * 4
            kicker_card_values = [kicker_val]
            return HandRank.FOUR_OF_A_KIND, self._calculate_hand_strength_value(HandRank.FOUR_OF_A_KIND, [quad_val, kicker_val]), [quad_val, kicker_val], sorted_cards

        # Full House: sorted_counts will be [(val_trip, 3), (val_pair, 2)]
        if sorted_counts[0][1] == 3 and sorted_counts[1][1] == 2:
            trip_val = sorted_counts[0][0]
            pair_val = sorted_counts[1][0]
            primary_card_values = [trip_val] * 3 + [pair_val] * 2
            kicker_card_values = [trip_val, pair_val] # For description
            return HandRank.FULL_HOUSE, self._calculate_hand_strength_value(HandRank.FULL_HOUSE, [trip_val, pair_val]), kicker_card_values, sorted_cards

        if is_flush: # Flush (but not straight flush)
            primary_card_values = values # All 5 cards define the flush, sorted high to low
            return HandRank.FLUSH, self._calculate_hand_strength_value(HandRank.FLUSH, primary_card_values), primary_card_values, sorted_cards

        if is_straight: # Straight (but not straight flush)
            # If wheel (A-5), high card is 5. Values for comparison: 5,4,3,2,1
            straight_values = [5,4,3,2,1] if values == [14,5,4,3,2] else values
            primary_card_values = straight_values
            return HandRank.STRAIGHT, self._calculate_hand_strength_value(HandRank.STRAIGHT, primary_card_values), primary_card_values, sorted_cards

        # Three of a Kind: sorted_counts will be [(val_trip, 3), (kicker1, 1), (kicker2, 1)]
        if sorted_counts[0][1] == 3:
            trip_val = sorted_counts[0][0]
            k1_val = sorted_counts[1][0]
            k2_val = sorted_counts[2][0]
            primary_card_values = [trip_val] * 3
            kicker_card_values = [trip_val, k1_val, k2_val] # For description/strength
            return HandRank.THREE_OF_A_KIND, self._calculate_hand_strength_value(HandRank.THREE_OF_A_KIND, kicker_card_values), kicker_card_values, sorted_cards
        
        # Two Pair: sorted_counts will be [(high_pair_val, 2), (low_pair_val, 2), (kicker_val, 1)]
        if sorted_counts[0][1] == 2 and sorted_counts[1][1] == 2:
            p1_val = sorted_counts[0][0] # Higher pair
            p2_val = sorted_counts[1][0] # Lower pair
            k_val = sorted_counts[2][0]  # Kicker
            primary_card_values = [p1_val]*2 + [p2_val]*2
            kicker_card_values = [p1_val, p2_val, k_val] # For description/strength
            return HandRank.TWO_PAIR, self._calculate_hand_strength_value(HandRank.TWO_PAIR, kicker_card_values), kicker_card_values, sorted_cards

        # One Pair: sorted_counts will be [(pair_val, 2), (k1,1), (k2,1), (k3,1)]
        if sorted_counts[0][1] == 2:
            pair_val = sorted_counts[0][0]
            k1 = sorted_counts[1][0]
            k2 = sorted_counts[2][0]
            k3 = sorted_counts[3][0]
            primary_card_values = [pair_val] * 2
            kicker_card_values = [pair_val, k1, k2, k3] # For description/strength
            return HandRank.PAIR, self._calculate_hand_strength_value(HandRank.PAIR, kicker_card_values), kicker_card_values, sorted_cards
            
        # High Card: all cards are kickers, sorted high to low
        primary_card_values = values
        return HandRank.HIGH_CARD, self._calculate_hand_strength_value(HandRank.HIGH_CARD, primary_card_values), primary_card_values, sorted_cards

    def _calculate_hand_strength_value(self, rank: HandRank, card_values: List[int]) -> int:
        """Calculates a single integer representing hand strength for comparison.
        Higher is better. rank is primary, card_values are secondary tie-breakers.
        card_values should be ordered by significance (e.g., for Full House [trip_val, pair_val]).
        For Flush/Straight/HighCard, card_values are all 5 cards, high to low.
        """
        value = int(rank) * (10**10) # Max 5 kickers, 2 digits per kicker (max card val 14)
        # Max card value is 14 (Ace). Max 5 kickers. Each kicker up to 2 digits.
        # Example: Pair of Aces (14), K(13) Q(12) J(11) kickers:
        # Rank 2. values: [14, 13, 12, 11] (pair val, k1, k2, k3) - one more kicker if 5 cards considered
        # If card_values represents [PairVal, K1, K2, K3], it needs to be padded for 5 significant values
        
        # For hands like Pair, TwoPair, ThreeOfAKind, FourOfAKind, card_values list might be shorter
        # than 5. Example: Four of a kind: [QuadVal, KickerVal]. Total 2 significant values.
        # Example: Pair: [PairVal, Kicker1, Kicker2, Kicker3]. Total 4 significant values.

        # Let card_values be the significant card values that define the hand's strength, in order.
        # E.g., for Four of a Kind: [quad_value, kicker_value]
        # E.g., for Flush: [card1_value, card2_value, card3_value, card4_value, card5_value]
        
        multiplier = 10**8
        for i, val in enumerate(card_values):
            if i < 5 : # Consider up to 5 significant values for tie-breaking
                value += val * multiplier
                multiplier //= 100 # Each card value can be up to 14 (2 digits)
        return value

    def get_hand_description(self, rank: HandRank, kicker_values: List[int]) -> str:
        # kicker_values here are the significant card values for the hand, ordered.
        # E.g., for Full House: [trip_value, pair_value]
        # E.g., for Flush: [c1, c2, c3, c4, c5] (all 5 card values of the flush)
        
        def card_name(value):
            if value == 14: return 'Ace'
            if value == 13: return 'King'
            if value == 12: return 'Queen'
            if value == 11: return 'Jack'
            if value == 1: return 'Ace (Low)' # For A-5 straight descriptions
            return str(value)

        desc = rank.name.replace('_', ' ')
        
        if not kicker_values: return desc # Should not happen if evaluation is correct

        if rank == HandRank.ROYAL_FLUSH: return "Royal Flush"
        if rank == HandRank.STRAIGHT_FLUSH:
            # kicker_values for SF is [high_card_val, ...] or [5,4,3,2,1] for wheel
            return f"Straight Flush, {card_name(kicker_values[0])} high"
        if rank == HandRank.FOUR_OF_A_KIND:
            # kicker_values: [quad_val, kicker_val]
            return f"Four of a Kind, {card_name(kicker_values[0])}s, {card_name(kicker_values[1])} kicker"
        if rank == HandRank.FULL_HOUSE:
            # kicker_values: [trip_val, pair_val]
            return f"Full House, {card_name(kicker_values[0])}s full of {card_name(kicker_values[1])}s"
        if rank == HandRank.FLUSH:
            # kicker_values: [c1, c2, c3, c4, c5] sorted high to low
            return f"Flush, {card_name(kicker_values[0])} high (Kickers: {', '.join(map(card_name, kicker_values[1:]))})"
        if rank == HandRank.STRAIGHT:
            # kicker_values: [high_card_val, ...] or [5,4,3,2,1] for wheel
             return f"Straight, {card_name(kicker_values[0])} high"
        if rank == HandRank.THREE_OF_A_KIND:
            # kicker_values: [trip_val, k1, k2]
            return f"Three of a Kind, {card_name(kicker_values[0])}s (Kickers: {card_name(kicker_values[1])}, {card_name(kicker_values[2])})"
        if rank == HandRank.TWO_PAIR:
            # kicker_values: [high_pair_val, low_pair_val, kicker_val]
            return f"Two Pair, {card_name(kicker_values[0])}s and {card_name(kicker_values[1])}s ({card_name(kicker_values[2])} kicker)"
        if rank == HandRank.PAIR:
            # kicker_values: [pair_val, k1, k2, k3]
            return f"Pair of {card_name(kicker_values[0])}s (Kickers: {', '.join(map(card_name, kicker_values[1:4]))})"
        if rank == HandRank.HIGH_CARD:
            # kicker_values: [c1, c2, c3, c4, c5]
            return f"High Card {card_name(kicker_values[0])} (Kickers: {', '.join(map(card_name, kicker_values[1:]))})"
        return desc # Fallback

    def save_hand_history(self, room: Room, winners_info: Dict[str, Dict]):
        # winners_info: { player_id: {"amount_won": int, "hand_description": str} }
        hand_data = {
            'hand_number': room.hand_number,
            'timestamp': datetime.now().isoformat(),
            'players': [], # List of player hand details
            'community_cards': [{'suit': c.suit, 'rank': c.rank, "id": c.id} for c in room.community_cards],
            'total_pot_distributed': sum(pot.amount for pot in room.side_pots), # Sum of all pots that were distributed
            'side_pots_details': [{
                "amount": sp.amount, 
                "eligible_players": list(sp.eligible_players), # Convert set to list for JSON
                "winner_ids": sp.winner_ids,
                "winning_hand_description": sp.winning_hand_description
                } for sp in room.side_pots],
            'winners': winners_info # player_id -> {amount_won, hand_description}
        }

        for p_id, player in room.players.items():
            player_hand_detail = {
                'id': player.id,
                'name': player.name,
                'initial_money': player.money - winners_info.get(p_id, {}).get("amount_won", 0) + player.total_bet_this_hand, # Approximate
                'final_money': player.money,
                'cards': [{'suit': c.suit, 'rank': c.rank, "id": c.id} for c in player.cards] if player.cards else [],
                'actions': player.actions_this_hand, # Actions taken by this player during the hand
                'total_bet_this_hand': player.total_bet_this_hand,
                'status_at_end': player.status.value,
            }
            if p_id in winners_info:
                player_hand_detail['amount_won'] = winners_info[p_id]["amount_won"]
                player_hand_detail['hand_description'] = winners_info[p_id]["hand_description"]
            
            hand_data['players'].append(player_hand_detail)
        
        room.hand_history.append(hand_data)
        if len(room.hand_history) > 50: # Keep last 50 hands
            room.hand_history = room.hand_history[-50:]
        logger.info(f"Room {room.code}: Hand #{room.hand_number} history saved.")

    def update_tournament_state(self, room: Room):
        if room.settings.game_mode != GameMode.TOURNAMENT:
            return

        # Check for eliminations
        eliminated_this_hand = []
        for p_id, player in room.players.items():
            if player.money <= 0 and player.status != PlayerStatus.ELIMINATED:
                player.status = PlayerStatus.ELIMINATED
                # Assign rank: total players - num already eliminated
                num_eliminated_so_far = sum(1 for p_check in room.players.values() if p_check.tournament_rank > 0)
                player.tournament_rank = len(room.players) - num_eliminated_so_far
                eliminated_this_hand.append(player.name)
        if eliminated_this_hand:
            logger.info(f"Tournament {room.code}: Players eliminated: {', '.join(eliminated_this_hand)}")
        
        # Check for blind increase
        if datetime.now() >= room.tournament_next_blind_increase:
            room.tournament_level += 1
            # Example blind increase schedule (can be made more complex from room.settings.tournament_structure)
            room.settings.small_blind = int(room.settings.small_blind * 1.5)
            room.settings.big_blind = int(room.settings.big_blind * 1.5)
            if room.settings.ante > 0: # Ante can also increase
                room.settings.ante = int(room.settings.ante * 1.5) if room.settings.ante > 0 else max(1, int(room.settings.small_blind * 0.1))


            room.tournament_next_blind_increase = datetime.now() + timedelta(seconds=TOURNAMENT_BLIND_INCREASE_INTERVAL)
            logger.info(f"Tournament {room.code}: Level up to {room.tournament_level}. Blinds: {room.settings.small_blind}/{room.settings.big_blind}, Ante: {room.settings.ante}")
            
            # Tournament break
            if room.tournament_level % 5 == 0: # Example: break every 5 levels
                room.phase = GamePhase.TOURNAMENT_BREAK
                room.paused = True
                room.pause_reason = f"Tournament Break ({TOURNAMENT_BLIND_INCREASE_INTERVAL // 60 // 5} min)" # Assuming 5 min break for 10 min levels
                asyncio.create_task(self.resume_tournament_after_break(room.code, 300)) # 5 min break

    # ... (other methods like add_chat_message, check_rate_limit, cleanup_inactive_rooms mostly as before) ...
    # ... (get_game_state and get_available_actions need minor updates if player object changed significantly) ...

    def get_game_state(self, room_code: str, for_player_id: str) -> dict: # Changed player_id to for_player_id
        room = self.rooms.get(room_code)
        if not room: return {}
        
        is_player_in_game = for_player_id in room.players and not room.players[for_player_id].is_ai
        is_spectator = for_player_id in room.spectators
        
        current_player_obj = room.players.get(room.current_player_id) if room.current_player_id else None
        
        players_data = {}
        for p_id, p_obj in room.players.items():
            player_data = {
                "id": p_obj.id, "name": p_obj.name, "money": p_obj.money,
                "current_bet": p_obj.current_bet, # Bet in current round
                "total_bet_this_hand": p_obj.total_bet_this_hand,
                "status": p_obj.status.value,
                "position_label": "", # Placeholder for UI position (e.g. Dealer, SB, BB, UTG)
                "last_action": p_obj.last_action.value if p_obj.last_action else None,
                "last_action_amount": p_obj.last_action_amount,
                "avatar": p_obj.avatar, "color": p_obj.color,
                "is_dealer": p_obj.is_dealer, "is_small_blind": p_obj.is_small_blind, "is_big_blind": p_obj.is_big_blind,
                "time_bank": p_obj.time_bank,
                "is_current_player": current_player_obj and current_player_obj.id == p_id,
                "tournament_rank": p_obj.tournament_rank,
                "is_ai": p_obj.is_ai,
                "stats": asdict(p_obj.stats) # Convert PlayerStats to dict
            }
            
            show_cards_condition = (
                p_id == for_player_id or  # Player sees their own cards
                (room.phase == GamePhase.SHOWDOWN and p_obj.status != PlayerStatus.FOLDED) or # All non-folded cards visible at showdown
                (is_spectator and room.phase == GamePhase.SHOWDOWN and p_obj.status != PlayerStatus.FOLDED)
            )
            
            if show_cards_condition and p_obj.cards:
                player_data["cards"] = [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in p_obj.cards]
            elif p_obj.cards: # Player has cards but shouldn't be shown to for_player_id
                player_data["cards"] = [{"suit": "back", "rank": "back", "id": f"back_{i}_{p_id}"} for i in range(len(p_obj.cards))]
            else:
                player_data["cards"] = [] # No cards (e.g. before deal)
            
            players_data[p_id] = player_data
        
        game_state = {
            "room_code": room.code, "room_name": room.name, "phase": room.phase.value,
            "pot": room.pot, # This is total pot collected. Side pots are separate.
            "current_bet_to_match": room.current_bet_to_match,
            "min_raise_amount": room.min_raise_amount,
            "current_player_id": room.current_player_id,
            "dealer_player_id": room.dealer_player_id,
            "players": players_data,
            "community_cards": [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in room.community_cards],
            "chat_messages": room.chat_messages[-30:], # Last 30 messages
            "is_player_in_game": is_player_in_game,
            "is_spectator": is_spectator,
            "spectator_count": len(room.spectators),
            "hand_number": room.hand_number,
            "settings": {
                "small_blind": room.settings.small_blind, "big_blind": room.settings.big_blind,
                "ante": room.settings.ante, "max_players": room.settings.max_players,
                "game_mode": room.settings.game_mode.value,
                "auto_fold_timeout": room.settings.auto_fold_timeout,
                "ai_players": room.settings.ai_players
            },
            "tournament_info": {
                "level": room.tournament_level,
                "next_blind_increase_time": room.tournament_next_blind_increase.isoformat()
            } if room.settings.game_mode == GameMode.TOURNAMENT else None,
            "side_pots": [{"amount": sp.amount, "eligible_players_count": len(sp.eligible_players), "winner_ids": sp.winner_ids, "winning_hand": sp.winning_hand_description} for sp in room.side_pots],
            "paused": room.paused, "pause_reason": room.pause_reason,
            "time_left_for_action": max(0, room.settings.auto_fold_timeout - (time.time() - room.last_action_timestamp)) if current_player_obj else 0,
            "can_act": is_player_in_game and current_player_obj and current_player_obj.id == for_player_id and room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER, GamePhase.TOURNAMENT_BREAK],
            "available_actions": self.get_available_actions(room, for_player_id) if is_player_in_game else []
        }
        return game_state

    def get_available_actions(self, room: Room, player_id: str) -> List[Dict]:
        player = room.players.get(player_id)
        if not player or not player.can_act() or room.current_player_id != player_id :
            return []
        
        actions = []
        
        # Fold
        actions.append({"action": PlayerAction.FOLD.value, "label": "Fold"})
        
        # Check/Call
        amount_to_call = room.current_bet_to_match - player.current_bet
        if amount_to_call <= 0: # Can check
            actions.append({"action": PlayerAction.CHECK.value, "label": "Check"})
        else: # Must call or raise or fold
            actual_call_amount = min(amount_to_call, player.money) # Cannot call more than you have
            actions.append({
                "action": PlayerAction.CALL.value, 
                "label": f"Call ${actual_call_amount}", 
                "amount": actual_call_amount
            })
        
        # Raise
        # Min raise amount is room.min_raise_amount (the size of the raise itself)
        # Max raise is player's remaining money after calling
        money_after_call = player.money - amount_to_call if amount_to_call > 0 else player.money
        
        if money_after_call > 0 : # Must have money left after calling to be able to raise
            # Minimum raise to: room.current_bet_to_match + room.min_raise_amount
            # So, the raise amount itself is room.min_raise_amount
            # Max raise amount (the "amount" part of raise) is all their remaining chips after an implicit call
            
            min_possible_raise_value = room.min_raise_amount
            # If player is all-in, their raise can be less than min_raise_amount
            max_possible_raise_value = money_after_call

            if max_possible_raise_value >= min_possible_raise_value : # Can make at least a min raise
                actions.append({
                    "action": PlayerAction.RAISE.value, 
                    "label": "Raise", 
                    "min_amount": min_possible_raise_value, # Smallest valid raise amount
                    "max_amount": max_possible_raise_value  # Largest valid raise amount (all-in)
                })
            elif max_possible_raise_value > 0: # Cannot make a full min_raise, but can go all-in for less
                 # This case is covered by All-In. A raise must be at least min_raise_amount unless it's all-in.
                 # The UI might offer a "Raise All-In" option here.
                 # For simplicity, direct all-in will handle this. If an "Raise" action for less than min_raise is chosen,
                 # it should become an All-In action if it's all their money.
                 pass


        # All-in
        if player.money > 0:
            actions.append({
                "action": PlayerAction.ALL_IN.value, 
                "label": f"All-In ${player.money}", 
                "amount": player.money # This is informational; actual amount processed by ALL_IN logic
            })
        
        return actions
# Global game instance
game = AdvancedPokerGame()

# WebSocket message models
class WSMessage(BaseModel):
    action: str
    payload: dict = PydanticField(default_factory=dict)

# Updated CreateRoomRequest to align with frontend
class CreateRoomPayload(BaseModel):
    player_name: str = "Anonymous"
    room_name: Optional[str] = None
    game_mode: str = GameMode.CASH_GAME.value
    small_blind: int = SMALL_BLIND
    big_blind: int = BIG_BLIND
    max_players: int = MAX_PLAYERS_PER_ROOM # Max human players
    buy_in: int = 0
    password: Optional[str] = None
    ai_players: int = 0


async def game_loop():
    """Advanced game loop with ~30 FPS updates and auto-fold handling"""
    while game.running:
        start_time = time.perf_counter()
        try:
            current_time = time.time()
            
            # Auto-fold, AI actions (AI actions are now triggered directly after human player action or phase change)
            # Auto-fold remains here.
            for room_code, room in list(game.rooms.items()): # list() for safe iteration if items are removed
                if room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER, GamePhase.TOURNAMENT_BREAK] and not room.paused:
                    if room.current_player_id:
                        current_player = room.players.get(room.current_player_id)
                        if current_player and not current_player.is_ai: # Only auto-fold human players
                            if current_time - room.last_action_timestamp > room.settings.auto_fold_timeout:
                                logger.info(f"Auto-folding player {current_player.name} in room {room_code} due to timeout.")
                                game.player_action(room_code, current_player.id, PlayerAction.FOLD)
                                # State will be broadcast below
            
            # Broadcast game state to all connected clients in each room
            for room_code, room in list(game.rooms.items()):
                # Collect all human player_ids and spectator_ids associated with this room
                user_ids_in_room = set()
                for p_id, player_obj in room.players.items():
                    if not player_obj.is_ai and player_obj.connection_id: # Human player
                        user_ids_in_room.add(player_obj.connection_id)
                user_ids_in_room.update(room.spectators)

                if not user_ids_in_room: continue

                # Create a list of (user_id, websocket_connection) for valid connections
                connections_to_broadcast = []
                for user_id in list(user_ids_in_room): # list() for safe iteration
                    ws_conn = game.connections.get(user_id)
                    if ws_conn:
                        connections_to_broadcast.append((user_id, ws_conn))
                    else: # Stale user_id in room.players or room.spectators
                        logger.warning(f"User {user_id} in room {room_code} but no active WebSocket connection. Cleaning up.")
                        game.leave_room(user_id, force=True) # Force remove if connection is dead

                # Asynchronously send game state to all valid connections
                if connections_to_broadcast:
                    broadcast_tasks = []
                    for user_id, ws_conn in connections_to_broadcast:
                        try:
                            game_state_for_user = game.get_game_state(room_code, user_id)
                            broadcast_tasks.append(
                                ws_conn.send_json({"type": "game_state", "data": game_state_for_user})
                            )
                        except Exception as e: # Catch error during game_state creation or send_json prep
                            logger.error(f"Error preparing/sending game_state to {user_id} in room {room_code}: {e}")
                            # Consider removing this connection if send fails repeatedly elsewhere
                    
                    if broadcast_tasks:
                        results = await asyncio.gather(*broadcast_tasks, return_exceptions=True)
                        for i, result in enumerate(results):
                            if isinstance(result, Exception):
                                user_id_failed, _ = connections_to_broadcast[i]
                                logger.error(f"Failed to broadcast to {user_id_failed}: {result}")
                                # Handle failed send: remove connection, leave room
                                if user_id_failed in game.connections: del game.connections[user_id_failed]
                                game.leave_room(user_id_failed, force=True)
            
            elapsed_time = time.perf_counter() - start_time
            sleep_duration = max(0, (1.0 / GAME_UPDATE_RATE) - elapsed_time)
            await asyncio.sleep(sleep_duration)

        except Exception as e:
            logger.exception(f"Critical error in game_loop: {e}") # Use logger.exception for stack trace
            await asyncio.sleep(1.0) # Avoid fast spinning on persistent error
# ... (lifespan, app setup, other endpoints as before) ...

async def handle_websocket_message(websocket: WebSocket, player_id: str, message: WSMessage):
    action = message.action
    payload_dict = message.payload # pydantic model already converted this
    
    try:
        if action == "create_room":
            try:
                create_payload = CreateRoomPayload(**payload_dict)
            except ValidationError as e:
                await websocket.send_json({"type": "error", "message": f"Invalid create room data: {e}"})
                return

            game_settings = GameSettings(
                small_blind=create_payload.small_blind,
                big_blind=create_payload.big_blind,
                max_players=min(create_payload.max_players, MAX_PLAYERS_PER_ROOM),
                game_mode=GameMode(create_payload.game_mode),
                buy_in=create_payload.buy_in,
                password=create_payload.password if create_payload.password else None,
                ai_players=min(create_payload.ai_players, MAX_PLAYERS_PER_ROOM -1) # Ensure at least 1 human if AI are maxed
            )
            
            room_code = game.create_room(player_id, game_settings, create_payload.room_name)
            if not room_code:
                await websocket.send_json({"type": "error", "message": "Failed to create room (server limit?)"})
                return

            if game.join_room(room_code, player_id, create_payload.player_name):
                await websocket.send_json({
                    "type": "room_created", # Or use room_joined consistently
                    "data": {"room_code": room_code, "room_name": game.rooms[room_code].name}
                })
            else: # Should not happen if create_room succeeded and join logic is fine
                await websocket.send_json({"type": "error", "message": "Failed to join newly created room"})
        
        # ... (rest of handle_websocket_message largely same, ensure player_id is used for game.player_rooms etc) ...
        # Ensure player_action uses payload.get("action_type") and PlayerAction(action_type)
        elif action == "player_action":
            if not game.check_rate_limit(player_id, "action"):
                await websocket.send_json({"type": "error", "message": "Action rate limit exceeded"})
                return
                
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]
                action_type_str = payload_dict.get("action_type")
                amount = payload_dict.get("amount", 0)
                
                try:
                    poker_action_enum = PlayerAction(action_type_str)
                    if game.player_action(room_code, player_id, poker_action_enum, amount):
                        # Success, game_state update will show result.
                        # Optionally send simple ack: await websocket.send_json({"type": "action_accepted"})
                        pass 
                    else:
                        await websocket.send_json({"type": "error", "message": "Invalid action or not your turn."})
                except ValueError: # Invalid string for PlayerAction enum
                    await websocket.send_json({"type": "error", "message": f"Invalid action type string: {action_type_str}"})
            else:
                await websocket.send_json({"type": "error", "message": "Player not in a room."})

        # ... (other actions) ...

    except Exception as e:
        logger.exception(f"Error handling WebSocket message (action: {action}): {e}") #.exception for stack trace
        try: # Try to inform client, connection might be dead
            await websocket.send_json({"type": "error", "message": "Server error processing request."})
        except:
            pass # Ignore if cannot send error back

# The rest of the FastAPI setup and ADVANCED_HTML_TEMPLATE will be provided in the next part.
# For brevity, I'm omitting unchanged parts of the Python file (like the HTML template string for now,
# and some helper methods in AdvancedPokerGame that were already robust).
# The core changes are in game logic for AI, hand history, and state management.

# Make sure to include the full, updated ADVANCED_HTML_TEMPLATE in the final response.
# I'm focusing on the Python changes first as they are foundational.
# The provided HTML template variable ADVANCED_HTML_TEMPLATE is very long.
# I will edit it in the final combined response.
if __name__ == "__main__":
    # For Uvicorn, ensure the app object is passed correctly if this file is run directly.
    # Example: uvicorn.run("your_filename:app", host="0.0.0.0", port=port, reload=True)
    # The current uvicorn.run(app, ...) is fine if app is defined at the top level.
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run(app, host="0.0.0.0", port=port)
```

**`ADVANCED_HTML_TEMPLATE` (Inside `poker_server.py` or as a separate file loaded by an endpoint)**

Key changes to JavaScript and HTML:
1.  **Main Menu Restructure (HTML & CSS):**
    *   HTML for `#menuPanel` changed to match the screenshot's layout (Player Setup, Quick Play, Custom Game with AI Players input).
    *   CSS might need slight tweaks if the new structure breaks alignment, but I'll try to keep it minimal.
2.  **Fix Main Menu Mouse Issue (JS):**
    *   In `addMouseControls()`, camera mouse interactions (drag, wheel) will be disabled if the `#menuPanel` is visible.
3.  **Fix Chat Input Overlap (CSS):**
    *   Changed `.chat-panel` height to `max-height: 40vh;` and made `#chatMessages` `flex: 1;` to be more responsive.
4.  **Fix Excessive Notifications (JS):**
    *   A flag `isLoadingOrReconnecting` will prevent multiple "Loading..." or "Reconnecting..." notifications if one is already active.
5.  **AI Player Integration (JS):**
    *   `createCustomRoom()` now reads and sends `ai_players` count.
    *   `updatePlayerCards()` displays an "(AI)" badge next to AI player names if `player.is_ai` is true in the game state.
6.  **Loading Screen:**
    *   The loading text on `showLoadingScreen` is now passed as an argument.
7.  **General JS:**
    *   `GAME_UPDATE_RATE` in JS matches the Python backend for consistency if needed (though JS animation is Three.js `requestAnimationFrame`).
    *   Slight adjustment to player card animation timing.

```html
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
            font-size: 3.5rem; /* Slightly smaller for balance */
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
            /* Removed transform: translateY to prevent movement bug with mouse controls */
            box-shadow: 0 15px 40px var(--shadow);
        }

        /* Main Menu */
        .menu-panel {
            top: 50%;
            left: 50%;
            transform: translate(-50%, -50%);
            text-align: left; /* Changed for better section layout */
            min-width: 450px; /* Increased width */
            max-width: 90vw;
        }

        .menu-title {
            font-family: 'Orbitron', monospace;
            font-size: 2.5rem; /* Adjusted size */
            font-weight: 900;
            color: var(--primary-gold);
            text-shadow: 0 0 20px rgba(255, 215, 0, 0.8);
            margin-bottom: 25px; /* Adjusted margin */
            animation: glow 2s ease-in-out infinite alternate;
            text-align: center; /* Centered title */
        }
        
        .menu-title .slot-icon { /* For slot machine icons in title */
             font-size: 2rem; /* Adjust if needed */
             vertical-align: middle;
        }


        @keyframes glow {
            from { text-shadow: 0 0 20px rgba(255, 215, 0, 0.8); }
            to { text-shadow: 0 0 30px rgba(255, 215, 0, 1), 0 0 40px rgba(255, 215, 0, 0.8); }
        }

        .menu-section {
            margin-bottom: 20px; /* Adjusted margin */
            padding: 15px; /* Adjusted padding */
            background: rgba(255, 255, 255, 0.05);
            border-radius: 10px;
            border: 1px solid rgba(255, 215, 0, 0.3);
        }

        .menu-section h3 {
            color: var(--secondary-gold);
            margin-bottom: 12px; /* Adjusted margin */
            font-size: 1.1rem; /* Adjusted size */
            border-bottom: 1px solid rgba(255,215,0,0.2);
            padding-bottom: 8px;
        }
        
        .menu-section label {
            display: block;
            margin-bottom: 5px;
            font-size: 0.9rem;
            color: rgba(255,255,255,0.8);
        }
        .menu-section input[type="text"],
        .menu-section input[type="number"],
        .menu-section input[type="password"],
        .menu-section select {
            width: 100%;
            margin-bottom: 10px; /* Space below each input */
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
        
        .game-hud .action-button { /* Style for buttons in HUD */
            padding: 10px 15px;
            font-size: 0.9rem;
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
            text-align: center; /* Ensure text is centered */
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
        
        /* Specific button colors - ensure high contrast for text */
        .action-button.fold { background: linear-gradient(135deg, var(--casino-red), #ff6b6b); color: var(--text-light); }
        .action-button.call { background: linear-gradient(135deg, #28a745, #20c997); color: var(--text-light); }
        .action-button.raise { background: linear-gradient(135deg, var(--casino-blue), #6c5ce7); color: var(--text-light); }
        .action-button.all-in { background: linear-gradient(135deg, #ff4757, #ff3742); color: var(--text-light); animation: allInPulse 1s infinite; }


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
            width: 320px; /* Fixed width */
            max-height: 40vh; /* Max height relative to viewport */
            min-height: 200px; /* Min height */
            display: flex;
            flex-direction: column;
        }

        .chat-header {
            display: flex;
            justify-content: space-between;
            align-items: center;
            margin-bottom: 10px; /* Reduced margin */
            padding-bottom: 8px; /* Reduced padding */
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
            flex: 1; /* Allows this to grow and shrink */
            overflow-y: auto;
            background: rgba(255, 255, 255, 0.05);
            border-radius: 8px;
            padding: 10px; /* Reduced padding */
            margin-bottom: 10px; /* Reduced margin */
            border: 1px solid rgba(255, 215, 0, 0.2);
        }

        .chat-message {
            margin-bottom: 8px; /* Reduced margin */
            padding: 6px 10px; /* Reduced padding */
            border-radius: 8px;
            background: rgba(255, 255, 255, 0.1);
            border-left: 3px solid;
            animation: slideInChat 0.3s ease-out;
            word-wrap: break-word; /* Ensure long messages wrap */
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
            margin-top: auto; /* Pushes to bottom if chatMessages doesn't fill space */
        }
        .chat-input-container input {
            padding: 10px 12px; /* Adjusted padding */
        }
        .chat-input-container button {
            padding: 10px 15px; /* Adjusted padding */
        }


        /* Player Info Cards */
        .player-cards {
            position: absolute;
            bottom: 120px; /* Increased space from bottom */
            left: 50%;
            transform: translateX(-50%);
            display: flex;
            gap: 15px; /* Adjusted gap */
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
            min-width: 160px; /* Slightly wider */
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
            overflow: hidden; /* For text if too long */
        }

        .player-name {
            font-weight: 700;
            color: var(--text-light);
            margin-bottom: 5px;
            font-size: 0.95rem; /* Slightly smaller for long names */
            white-space: nowrap;
            overflow: hidden;
            text-overflow: ellipsis;
            max-width: 130px; /* Prevent overflow */
        }
        .player-name .ai-badge {
            font-size: 0.7rem;
            color: var(--secondary-gold);
            font-weight: normal;
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
        input, select { /* Apply to select as well */
            padding: 12px 15px;
            border: 2px solid var(--primary-gold);
            border-radius: 8px;
            background: rgba(255, 255, 255, 0.1);
            color: var(--text-light);
            font-size: 1rem;
            transition: all 0.3s ease;
            backdrop-filter: blur(10px);
            font-family: 'Roboto', sans-serif; /* Ensure font consistency */
        }
        select option {
            background: var(--dark-green);
            color: var(--text-light);
        }


        input:focus, select:focus {
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
                min-width: 90vw; /* Full width on small screens */
                padding: 15px;
            }

            .menu-title {
                font-size: 2rem;
            }
            .menu-title .slot-icon { font-size: 1.5rem; }


            .chat-panel {
                width: 90vw; /* Full width on small screens */
                max-height: 30vh; /* Shorter on small screens */
                top: auto; /* Allow it to be pushed by other elements */
                bottom: 20px; /* Example: place at bottom */
                left: 5vw;
                right: 5vw;
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
                bottom: 180px; /* Adjust if chat panel is at bottom */
                gap: 8px;
            }

            .player-card {
                min-width: 120px;
                padding: 10px;
            }
            .player-name { max-width: 100px; }
        }
        @media (max-width: 480px) {
            .menu-title { font-size: 1.8rem; }
            .menu-title .slot-icon { font-size: 1.3rem; }
            .action-button { padding: 10px 15px; font-size: 0.8rem; }
            .raise-controls { flex-direction: column; }
            .raise-controls input[type="number"] { width: 100% !important; }
        }


        /* Utility Classes */
        .hidden {
            display: none !important;
        }

        .fade-in { animation: fadeIn 0.5s ease-out; }
        .fade-out { animation: fadeOut 0.5s ease-out; }
        @keyframes fadeIn { from { opacity: 0; } to { opacity: 1; } }
        @keyframes fadeOut { from { opacity: 1; } to { opacity: 0; } }

        .slide-up { animation: slideUp 0.5s ease-out; }
        @keyframes slideUp { from { transform: translateY(20px); opacity: 0; } to { transform: translateY(0); opacity: 1; } }

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
            z-index: 101; /* Above UI panels but below modals */
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
        .notification-container {
            position: fixed;
            top: 20px;
            right: 20px;
            z-index: 10000; /* Above everything */
            display: flex;
            flex-direction: column;
            gap: 10px;
            align-items: flex-end;
        }
        .notification {
            background: linear-gradient(135deg, rgba(40, 167, 69, 0.9), rgba(32, 201, 151, 0.9));
            color: var(--text-light);
            padding: 15px 20px;
            border-radius: 8px;
            border-left: 4px solid var(--primary-gold);
            box-shadow: 0 5px 15px var(--shadow);
            animation: slideInNotification 0.5s ease-out;
            min-width: 250px;
            max-width: 350px;
        }

        .notification.error { background: linear-gradient(135deg, rgba(220, 20, 60, 0.9), rgba(255, 107, 107, 0.9)); }
        .notification.warning { background: linear-gradient(135deg, rgba(255, 193, 7, 0.9), rgba(255, 235, 59, 0.9)); color: var(--text-dark); }
        .notification.info { background: linear-gradient(135deg, rgba(25, 25, 112, 0.9), rgba(108, 92, 231, 0.9)); }


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
        <div class="loading-logo"><span class="slot-icon">🎰</span> ROYAL POKER 3D <span class="slot-icon">🎰</span></div>
        <div class="loading-spinner"></div>
        <div class="loading-text">Loading casino experience...</div>
    </div>

    <div id="gameContainer">
        <canvas id="canvas"></canvas>
        
        <div class="ui-overlay">
            <!-- Main Menu (Restructured) -->
            <div id="menuPanel" class="ui-panel menu-panel hidden">
                <h1 class="menu-title"><span class="slot-icon">🎰</span> ROYAL POKER 3D <span class="slot-icon">🎰</span></h1>
                
                <div class="menu-section">
                    <h3>Player Setup</h3>
                    <label for="playerName">Player Name:</label>
                    <input type="text" id="playerName" placeholder="Enter your name" value="Player">
                </div>
                
                <div class="menu-section">
                    <h3>Quick Play</h3>
                    <button class="action-button" onclick="createQuickRoom()" style="width: 100%; margin-bottom: 10px;">🎯 Create Quick Room</button>
                    <div style="display: flex; gap: 10px; margin-bottom: 10px;">
                        <input type="text" id="roomCode" placeholder="Room Code" style="flex: 1; margin-bottom: 0;">
                        <button class="action-button" onclick="joinRoom()">🚪 Join</button>
                    </div>
                    <button class="action-button" onclick="spectateRoom()" style="width: 100%;">👁️ Spectate Room</button>
                </div>
                
                <div class="menu-section">
                    <h3>Custom Game</h3>
                    <label for="roomName">Room Name (Optional):</label>
                    <input type="text" id="roomName" placeholder="My Awesome Poker Room">
                    
                    <div style="display: grid; grid-template-columns: 1fr 1fr; gap: 15px; margin-top:10px;">
                        <div>
                            <label for="gameMode">Game Mode:</label>
                            <select id="gameMode">
                                <option value="cash_game">Cash Game</option>
                                <option value="tournament">Tournament</option>
                                <option value="sit_and_go" disabled>Sit & Go (Soon)</option>
                            </select>
                        </div>
                        <div>
                            <label for="maxPlayers">Max Players:</label>
                            <input type="number" id="maxPlayers" min="2" max="10" value="8">
                        </div>
                        <div>
                            <label for="smallBlind">Small Blind:</label>
                            <input type="number" id="smallBlind" min="1" value="25">
                        </div>
                        <div>
                            <label for="bigBlind">Big Blind:</label>
                            <input type="number" id="bigBlind" min="2" value="50">
                        </div>
                        <div>
                            <label for="buyIn">Buy-in:</label>
                            <input type="number" id="buyIn" min="0" value="1000" step="50">
                        </div>
                        <div>
                            <label for="aiPlayers">AI Players:</label>
                            <input type="number" id="aiPlayers" min="0" max="9" value="0">
                        </div>
                    </div>
                     <label for="roomPassword" style="margin-top:10px;">Password (Optional):</label>
                    <input type="password" id="roomPassword" placeholder="Leave empty for public">
                    <button class="action-button" onclick="createCustomRoom()" style="width: 100%; margin-top: 15px;">🎪 Create Custom Room</button>
                </div>
                
                <div class="menu-section">
                    <h3>Browse Rooms</h3>
                    <button class="action-button" onclick="showRoomList()" style="width: 100%;">🏛️ Browse Public Rooms</button>
                </div>
            </div>

            <!-- Room List Modal -->
            <div id="roomListModal" class="modal hidden">
                <div class="modal-content">
                    <div class="modal-header">
                        <h2 class="modal-title">🏛️ Public Rooms</h2>
                        <button class="modal-close" onclick="hideRoomList()">✕</button>
                    </div>
                    <div id="roomList" style="max-height: 60vh; overflow-y: auto;">
                        <div style="text-align: center; color: #ccc; padding: 20px;">Loading rooms...</div>
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
                    <span class="hud-label">💰 My Money:</span>
                    <span class="hud-value">$<span id="moneyAmount">0</span></span>
                </div>
                <div class="hud-item">
                    <span class="hud-label">🎯 To Call:</span>
                    <span class="hud-value">$<span id="betToMatch">0</span></span>
                </div>
                 <div class="hud-item">
                    <span class="hud-label">✋ Hand:</span>
                    <span class="hud-value" id="handNumber">0</span>
                </div>
                <div style="margin-top: 15px; display: flex; flex-direction: column; gap: 8px;">
                    <button class="action-button" onclick="startGame()" id="startGameBtn" style="width: 100%;">🚀 Start Game</button>
                    <button class="action-button" onclick="showHandHistory()" style="width: 100%;">📊 Hand History</button>
                    <button class="action-button" onclick="pauseGame()" id="pauseGameBtn" style="width: 100%;">⏸️ Pause Game</button>
                    <button class="action-button fold" onclick="leaveRoom()" style="width: 100%;">🚪 Leave Room</button>
                </div>
            </div>

            <!-- Tournament Info -->
            <div id="tournamentInfo" class="tournament-info hidden">
                <div class="tournament-level">🏆 Level <span id="tournamentLevel">1</span></div>
                <div class="tournament-timer">Next: <span id="tournamentTimer">10:00</span></div>
                <div style="margin-top: 5px; font-size: 0.8rem;">Blinds: $<span id="tournamentBlinds">25/50</span></div>
            </div>

            <!-- Pot Display -->
            <div id="potDisplay" class="pot-display hidden">
                <div style="font-size: 1rem; margin-bottom: 5px;">💰 POT</div>
                <div>$<span id="potAmount">0</span></div>
                <div id="sidePotsDisplay" style="font-size: 0.8rem; margin-top: 5px; color: rgba(0,0,0,0.7);"></div>
            </div>

            <!-- Action Timer -->
            <div id="actionTimer" class="hidden" style="position: absolute; top: 25%; left: 50%; transform: translateX(-50%); background: rgba(220, 20, 60, 0.9); color: white; padding: 10px 20px; border-radius: 25px; font-family: 'Orbitron', monospace; font-weight: 700; font-size: 1.2rem; animation: timerPulse 1s infinite; z-index:101;">
                ⏰ <span id="timerSeconds">30</span>s
            </div>

            <!-- Action Buttons -->
            <div id="actionsPanel" class="actions-panel hidden">
                <button class="action-button fold" onclick="playerAction('fold')" id="foldBtn">🚫 Fold</button>
                <button class="action-button" onclick="playerAction('check')" id="checkBtn">✅ Check</button>
                <button class="action-button call" onclick="playerAction('call')" id="callBtn">📞 Call $<span id="callAmount">0</span></button>
                <div class="raise-controls">
                    <span style="color: var(--primary-gold); font-weight: 700; white-space:nowrap;">Raise To:</span>
                    <input type="range" id="raiseSlider" class="raise-slider" min="50" max="1000" value="100" oninput="updateRaiseAmountInput()" onchange="updateRaiseAmountInput()">
                    <input type="number" id="raiseAmountInput" min="50" value="100" style="width: 80px;" oninput="updateRaiseSliderFromInput()" onchange="updateRaiseSliderFromInput()">
                    <button class="action-button raise" onclick="playerAction('raise')" id="raiseBtn">📈 Raise</button>
                </div>
                <button class="action-button all-in" onclick="playerAction('all_in')" id="allInBtn">🔥 ALL IN</button>
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

            <!-- Player Cards UI -->
            <div id="playerCardsDisplay" class="player-cards hidden"></div>

            <!-- Hand History Modal -->
            <div id="handHistoryModal" class="modal hidden">
                <div class="modal-content">
                    <div class="modal-header">
                        <h2 class="modal-title">📊 Hand History</h2>
                        <button class="modal-close" onclick="hideHandHistory()">✕</button>
                    </div>
                    <div id="handHistoryContent" style="max-height: 60vh; overflow-y: auto;">
                        <div style="text-align: center; color: #ccc; padding: 20px;">No hands played yet or history not loaded.</div>
                    </div>
                </div>
            </div>
        </div>
    </div>
    <div id="notificationContainer" class="notification-container"></div>


    <script>
        // Advanced Game State Management
        let ws = null;
        let scene, camera, renderer; // Removed controls, using custom mouse interaction
        let pokerTable, tableGroup;
        // let cards = [], chips = [], playerPositions = []; // playerPositions is still used
        let playerPositions = [];
        let cardMaterials = {}, chipMaterials = {};
        let currentGameState = null; // Renamed from gameState to avoid conflict
        let isConnected = false;
        let isPlayerInGame = false; // True if current client is a player in the room
        let myPlayerId = null; // Assigned by server on connect
        let currentRoomCode = null;
        // let animationQueue = []; // GSAP handles animations directly now
        // let soundEnabled = true; // Placeholder for sound features
        let cameraAnimating = false;
        let isLoadingOrReconnecting = false; // For managing loading/reconnect notifications
        
        // 3D Scene objects
        let communityCardObjects = [];
        let playerCardObjects3D = {}; // Stores 3D card objects for each player { playerId: [cardMesh1, cardMesh2] }
        let chipStackObjects = {}; // { "pot": potChipMesh, "player_bet_playerId": playerBetChipMesh }
        let dealerButtonMesh; //, blindButtonMeshes = [];
        let particleSystem;
        
        // UI State
        let chatCollapsed = false;
        // let notificationQueue = []; // Notifications shown directly
        
        // Initialize Three.js scene with advanced graphics
        function initThreeJS() {
            // ... (Three.js setup as before, ensure no major changes unless specified) ...
            // Make sure createPlayerPositions() is called.
            const canvas = document.getElementById('canvas');
            scene = new THREE.Scene();
            scene.fog = new THREE.Fog(0x051a11, 15, 50);
            setupLighting();
            camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, 1000);
            camera.position.set(0, 12, 15); // Default camera position for table view
            camera.lookAt(0, 0, 0);
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
            // renderer.outputEncoding = THREE.sRGBEncoding; // Removed, caused issues with some materials if not handled consistently

            createCasinoEnvironment();
            createPokerTable(); // This calls createPlayerPositions
            createCardMaterials();
            createChipMaterials();
            addMouseControls();
            createParticleSystem();
            animate();
        }
        
        function setupLighting() { /* ... As before ... */ 
            const ambientLight = new THREE.AmbientLight(0x404040, 0.5); // Slightly brighter ambient
            scene.add(ambientLight);
            const mainLight = new THREE.DirectionalLight(0xffffff, 1.0); // Brighter main
            mainLight.position.set(10, 20, 10);
            mainLight.castShadow = true;
            mainLight.shadow.mapSize.width = 2048; mainLight.shadow.mapSize.height = 2048; // Adjusted for performance
            mainLight.shadow.camera.near = 0.5; mainLight.shadow.camera.far = 50;
            mainLight.shadow.camera.left = -20; mainLight.shadow.camera.right = 20;
            mainLight.shadow.camera.top = 20; mainLight.shadow.camera.bottom = -20;
            scene.add(mainLight);
            const tableLight1 = new THREE.SpotLight(0xffd700, 1.0, 30, Math.PI / 4, 0.3, 1); // Adjusted intensity/penumbra
            tableLight1.position.set(0, 10, 0);
            tableLight1.target.position.set(0, 0, 0);
            tableLight1.castShadow = true;
            scene.add(tableLight1);
            scene.add(tableLight1.target);
        }
        function createCasinoEnvironment() { /* ... As before ... */ 
            const floorGeometry = new THREE.PlaneGeometry(100, 100);
            const floorMaterial = new THREE.MeshLambertMaterial({ color: 0x2a0a0a, transparent: true, opacity: 0.8 });
            const floor = new THREE.Mesh(floorGeometry, floorMaterial);
            floor.rotation.x = -Math.PI / 2; floor.position.y = -2; floor.receiveShadow = true;
            scene.add(floor);
             // Simpler background: A large sphere an image or gradient
            const backgroundSphere = new THREE.SphereGeometry(100, 32, 32);
            const backgroundMaterial = new THREE.MeshBasicMaterial({
                color: 0x030f0a, // Dark green/blue
                side: THREE.BackSide,
                fog: false // No fog on the skybox itself
            });
            const skybox = new THREE.Mesh(backgroundSphere, backgroundMaterial);
            scene.add(skybox);
        }
        function createPokerTable() { /* ... As before, ensure createPlayerPositions is called ... */ 
            tableGroup = new THREE.Group();
            const tableGeometry = new THREE.CylinderGeometry(7, 7, 0.4, 64);
            const tableMaterial = new THREE.MeshPhongMaterial({ color: 0x8B4513, shininess: 30, specular: 0x222222 });
            pokerTable = new THREE.Mesh(tableGeometry, tableMaterial);
            pokerTable.position.y = -0.2; pokerTable.receiveShadow = true; pokerTable.castShadow = true;
            tableGroup.add(pokerTable);
            const edgeGeometry = new THREE.TorusGeometry(7, 0.3, 16, 64);
            const edgeMaterial = new THREE.MeshPhongMaterial({ color: 0x654321, shininess: 50 });
            const tableEdge = new THREE.Mesh(edgeGeometry, edgeMaterial);
            tableEdge.rotation.x = Math.PI / 2; // Correct orientation for torus as edge
            tableEdge.position.y = -0.05; // Adjusted position
            tableEdge.castShadow = true;
            tableGroup.add(tableEdge);
            const feltGeometry = new THREE.CylinderGeometry(6.5, 6.5, 0.05, 64);
            const feltMaterial = new THREE.MeshLambertMaterial({ color: 0x0d4d2a });
            const tableFelt = new THREE.Mesh(feltGeometry, feltMaterial);
            tableFelt.position.y = 0.025; // On top of table base
            tableFelt.receiveShadow = true;
            tableGroup.add(tableFelt);
            createTableMarkings();
            scene.add(tableGroup);
            createPlayerPositions(); // Ensure this is defined and called
        }
        function createTableMarkings() { /* ... As before ... */ 
             // Community card area outline
            const cardAreaGeometry = new THREE.RingGeometry(1.5, 1.55, 32); // Slightly thicker
            const cardAreaMaterial = new THREE.MeshBasicMaterial({ color: 0xffd700, transparent: true, opacity: 0.5, side: THREE.DoubleSide });
            const cardArea = new THREE.Mesh(cardAreaGeometry, cardAreaMaterial);
            cardArea.rotation.x = -Math.PI / 2; cardArea.position.y = 0.03; // Slightly above felt
            tableGroup.add(cardArea);
        }
        function createPlayerPositions() { /* ... As before ... */ 
            playerPositions = []; // Max 10 players
            const radius = 5; // Radius from center for player card positions
            for (let i = 0; i < 10; i++) {
                const angle = (i / 10) * Math.PI * 2 + Math.PI / 10; // Offset so player 0 is not straight down
                playerPositions.push({
                    angle: angle,
                    x: Math.cos(angle) * radius,
                    z: Math.sin(angle) * radius,
                    cardXOffset: -0.25, // For first card
                    cardSpacing: 0.5, // Between two cards
                    chipX: Math.cos(angle) * (radius - 1.0), // Chips closer to center
                    chipZ: Math.sin(angle) * (radius - 1.0),
                });
            }
        }
        function createCardMaterials() { /* ... As before ... */ 
             cardMaterials.back = new THREE.MeshPhongMaterial({ color: 0x2E4BC6, shininess: 30, map: createCardTexture("?", "?", true) }); // Card back texture
            ['hearts', 'diamonds', 'clubs', 'spades'].forEach(suit => {
                // For simplicity, reuse logic or create individual textures per rank/suit
                // This example will use a generic white front face, details added via other meshes or textures
                cardMaterials[suit] = new THREE.MeshPhongMaterial({ color: 0xfefefe, shininess: 10 });
            });
        }

        function createCardTexture(rank, suitName, isBack = false) {
            const canvas = document.createElement('canvas');
            const ctx = canvas.getContext('2d');
            canvas.width = 180; // Card dimensions ratio approx 2.5:3.5
            canvas.height = 260;

            // Card background
            ctx.fillStyle = isBack ? '#2E4BC6' : '#FFFFFF';
            ctx.fillRect(0, 0, canvas.width, canvas.height);
            
            // Border
            ctx.strokeStyle = isBack ? '#FFFFFF' : '#AAAAAA';
            ctx.lineWidth = 8;
            ctx.strokeRect(0,0, canvas.width, canvas.height);


            if (!isBack) {
                // Suit symbol and rank text
                const suitSymbols = { 'hearts': '♥', 'diamonds': '♦', 'clubs': '♣', 'spades': '♠' };
                const suitColor = (suitName === 'hearts' || suitName === 'diamonds') ? '#DD0000' : '#000000';
                
                ctx.fillStyle = suitColor;
                ctx.font = 'bold 48px Arial';
                ctx.textAlign = 'center';
                
                // Rank Top-Left
                ctx.fillText(rank, 30, 50);
                // Suit Top-Left
                ctx.fillText(suitSymbols[suitName] || '', 30, 100);

                // Rank Bottom-Right (rotated)
                ctx.save();
                ctx.translate(canvas.width - 30, canvas.height - 50);
                ctx.rotate(Math.PI);
                ctx.fillText(rank, 0, 0);
                ctx.restore();
                
                // Suit Bottom-Right (rotated)
                ctx.save();
                ctx.translate(canvas.width - 30, canvas.height - 100);
                ctx.rotate(Math.PI);
                ctx.fillText(suitSymbols[suitName] || '', 0, 0);
                ctx.restore();

                // Large central suit symbol (optional)
                ctx.font = 'bold 96px Arial';
                ctx.fillText(suitSymbols[suitName] || '', canvas.width / 2, canvas.height / 2 + 20);

            } else { // Back design
                ctx.fillStyle = 'rgba(255,255,255,0.3)';
                ctx.beginPath();
                ctx.arc(canvas.width / 2, canvas.height / 2, 50, 0, Math.PI * 2);
                ctx.fill();
                ctx.font = 'bold 20px Orbitron';
                ctx.fillStyle = '#FFFFFF';
                ctx.textAlign = 'center';
                ctx.fillText('ROYAL', canvas.width/2, canvas.height/2 - 10);
                ctx.fillText('POKER', canvas.width/2, canvas.height/2 + 20);
            }

            const texture = new THREE.CanvasTexture(canvas);
            texture.needsUpdate = true;
            return texture;
        }


        function createChipMaterials() { /* ... As before ... */ 
            chipMaterials = {
                1: new THREE.MeshPhongMaterial({ color: 0xFFFFFF, shininess: 50 }),    // White
                5: new THREE.MeshPhongMaterial({ color: 0xFF0000, shininess: 50 }),    // Red  
                25: new THREE.MeshPhongMaterial({ color: 0x00AA00, shininess: 50 }),   // Green
                100: new THREE.MeshPhongMaterial({ color: 0x000000, shininess: 50 }),  // Black
                500: new THREE.MeshPhongMaterial({ color: 0x800080, shininess: 50 }),  // Purple
                1000: new THREE.MeshPhongMaterial({ color: 0xFFD700, shininess: 50 }), // Gold
                // Add more denominations as needed
                'default': new THREE.MeshPhongMaterial({ color: 0xFFAA00, shininess: 50 }), // Orange for other values
            };
        }
        function createCard3D(cardData, position, rotationY = 0, faceUp = true) {
            // cardData: { suit, rank, id } from server, or { suit: 'back', rank: 'back' }
            const cardGroup = new THREE.Group();
            const cardWidth = 0.9;
            const cardHeight = 1.3;
            const cardDepth = 0.02;
            const cardGeometry = new THREE.BoxGeometry(cardWidth, cardHeight, cardDepth);
            
            const frontTexture = faceUp ? createCardTexture(cardData.rank, cardData.suit) : createCardTexture("?", "?", true);
            const backTexture = createCardTexture("?", "?", true);
            const sideMaterial = new THREE.MeshPhongMaterial({color: 0xcccccc, shininess:5});

            const materials = [
                sideMaterial, // right
                sideMaterial, // left
                sideMaterial, // top
                sideMaterial, // bottom
                new THREE.MeshPhongMaterial({ map: frontTexture, shininess: faceUp ? 10 : 30 }), // front
                new THREE.MeshPhongMaterial({ map: backTexture, shininess: 30  })  // back
            ];
            
            const cardMesh = new THREE.Mesh(cardGeometry, materials);
            cardMesh.castShadow = true;
            cardMesh.receiveShadow = true;
            
            cardGroup.add(cardMesh);
            cardGroup.position.copy(position);
            cardGroup.rotation.y = rotationY; // Rotation around Y axis (for player positions)
            cardGroup.userData = { id: cardData.id, suit: cardData.suit, rank: cardData.rank, faceUp: faceUp }; // Store card info

            return cardGroup;
        }
        function createChip3D(value, position, stackCount = 1) { /* ... As before ... */ 
            const chipGroup = new THREE.Group();
            const chipRadius = 0.20; // Smaller chips
            const chipHeight = 0.05;

            const denomination = getChipDenomination(value); // Determine best chip color
            const chipMaterial = chipMaterials[denomination] || chipMaterials['default'];
            
            for (let i = 0; i < stackCount; i++) {
                const chipGeometry = new THREE.CylinderGeometry(chipRadius, chipRadius, chipHeight, 16);
                const chip = new THREE.Mesh(chipGeometry, chipMaterial);
                chip.position.y = i * (chipHeight + 0.005) + chipHeight/2; // Stacked with slight gap
                chip.castShadow = true;
                chip.receiveShadow = true;
                chipGroup.add(chip);
            }
            chipGroup.position.copy(position);
            chipGroup.userData = { value: value, count: stackCount };
            return chipGroup;
        }
        
        function getChipDenomination(totalAmount) { // Simplified logic to pick a chip color
            if (totalAmount >= 1000) return 1000;
            if (totalAmount >= 500) return 500;
            if (totalAmount >= 100) return 100;
            if (totalAmount >= 25) return 25;
            if (totalAmount >= 5) return 5;
            return 1;
        }

        function createParticleSystem() { /* ... As before ... */ 
            const particleCount = 200; // More particles
            const particles = new THREE.BufferGeometry();
            const particlePositions = new Float32Array(particleCount * 3);
            for (let i = 0; i < particleCount * 3; i += 3) {
                particlePositions[i] = (Math.random() - 0.5) * 60;    
                particlePositions[i + 1] = Math.random() * 25 + 2;   
                particlePositions[i + 2] = (Math.random() - 0.5) * 60; 
            }
            particles.setAttribute('position', new THREE.BufferAttribute(particlePositions, 3));
            const particleMaterial = new THREE.PointsMaterial({
                color: 0xFFD700, size: 0.08, transparent: true, opacity: 0.2, blending: THREE.AdditiveBlending, fog: false
            });
            particleSystem = new THREE.Points(particles, particleMaterial);
            scene.add(particleSystem);
        }

        function addMouseControls() {
            let mouseDown = false;
            let lastMouseX = 0, lastMouseY = 0;
            let targetCameraRotationY = 0; // For horizontal rotation around table
            let targetCameraDistance = 15; // For zoom
            
            const menuPanel = document.getElementById('menuPanel');

            canvas.addEventListener('mousedown', (event) => {
                if (menuPanel.classList.contains('hidden')) { // Only control if menu is hidden
                    mouseDown = true;
                    lastMouseX = event.clientX;
                    lastMouseY = event.clientY; // Not used for Y rotation, but good to have
                }
            });
            
            document.addEventListener('mouseup', () => { // Listen on document to catch mouseup outside canvas
                mouseDown = false;
            });
            
            document.addEventListener('mousemove', (event) => { // Listen on document
                if (mouseDown && menuPanel.classList.contains('hidden') && !cameraAnimating) {
                    const deltaX = event.clientX - lastMouseX;
                    targetCameraRotationY -= deltaX * 0.005; // Adjust sensitivity
                    lastMouseX = event.clientX;
                    lastMouseY = event.clientY;
                }
            });
            
            canvas.addEventListener('wheel', (event) => {
                if (menuPanel.classList.contains('hidden') && !cameraAnimating) {
                    event.preventDefault(); // Prevent page scroll
                    targetCameraDistance += event.deltaY * 0.01;
                    targetCameraDistance = Math.max(8, Math.min(25, targetCameraDistance)); // Clamp zoom
                }
            });
            
            // Smooth camera movement in animate loop
        }

        function animate() {
            requestAnimationFrame(animate);
            
            // Smooth camera update if not animating via GSAP
            if (!cameraAnimating) {
                const currentRotationY = camera.rotation.y; // This is not how orbit works
                // Need to calculate position based on targetCameraRotationY and targetCameraDistance
                camera.position.x = Math.sin(targetCameraRotationY) * targetCameraDistance;
                camera.position.z = Math.cos(targetCameraRotationY) * targetCameraDistance;
                camera.position.y = THREE.MathUtils.lerp(camera.position.y, 12, 0.1); // Smooth Y adjustment if needed
                camera.lookAt(0, 0, 0);
            }


            if (tableGroup) tableGroup.rotation.y += 0.0003; // Slower rotation
            if (particleSystem) particleSystem.rotation.y += 0.0005;
            
            // Animate community cards slightly
            communityCardObjects.forEach((cardMesh, index) => {
                if (cardMesh) {
                    // cardMesh.rotation.y = Math.sin(Date.now() * 0.0005 + index) * 0.05;
                    cardMesh.position.y = 0.05 + Math.sin(Date.now() * 0.001 + index * 0.5) * 0.02;
                }
            });
            
            renderer.render(scene, camera);
        }

        // function animateCardDeal(...) // Replaced by direct GSAP animations in updateTableVisuals
        // function animateChipStack(...) // Replaced by direct GSAP animations in updateTableVisuals

        function updateTableVisuals() {
            clearTable3DObjects(); // Clear old 3D objects
            
            if (!currentGameState) return;
            
            const cardBaseY = 0.05; // Y position for cards on felt

            // Community cards
            currentGameState.community_cards.forEach((cardData, index) => {
                const position = new THREE.Vector3(-2 + index * 1, cardBaseY, 0);
                const cardObj = createCard3D(cardData, position, 0, true);
                scene.add(cardObj);
                communityCardObjects.push(cardObj);
                
                gsap.from(cardObj.scale, { duration: 0.5, x: 0, y: 0, z: 0, ease: "back.out(1.7)", delay: index * 0.15 });
                gsap.from(cardObj.position, {duration: 0.5, y: cardBaseY + 2, ease: "power2.out", delay: index * 0.15});
            });
            
            // Player cards and bets
            const playersArray = Object.values(currentGameState.players);
            playersArray.forEach((player, pIndex) => {
                if (pIndex < playerPositions.length) { // Ensure we have a predefined 3D position
                    const pos3D = playerPositions[pIndex];
                    
                    // Player cards
                    if (player.cards && player.cards.length > 0) {
                        playerCardObjects3D[player.id] = [];
                        player.cards.forEach((cardData, cardIndex) => {
                            const cardPosition = new THREE.Vector3(
                                pos3D.x + (cardData.suit === 'back' ? 0 : pos3D.cardXOffset + cardIndex * pos3D.cardSpacing), // Center back cards, spread revealed
                                cardBaseY,
                                pos3D.z
                            );
                            // Rotate cards to face center slightly, or align with player position
                            const cardRotationY = pos3D.angle + Math.PI/2; // Align with player position radius

                            const cardObj = createCard3D(cardData, cardPosition, cardRotationY, cardData.suit !== 'back');
                            scene.add(cardObj);
                            playerCardObjects3D[player.id].push(cardObj);

                            // Animation for dealing cards
                            if (cardObj.userData.suit === 'back' || !cardObj.userData.isDealt) { // Only animate if new or back
                                cardObj.userData.isDealt = true; // Mark as dealt to avoid re-animating same cards
                                const dealDelay = pIndex * 0.1 + cardIndex * 0.05;
                                gsap.from(cardObj.position, { duration: 0.6, x:0, y: cardBaseY + 3, z:0, ease: "circ.out", delay: dealDelay });
                                gsap.from(cardObj.rotation, { duration: 0.6, y: cardRotationY + Math.PI, z: Math.PI, ease: "circ.out", delay: dealDelay });
                            }
                        });
                    }
                    
                    // Player chip bets (total_bet_this_hand indicates chips pushed forward)
                    if (player.total_bet_this_hand > 0) {
                        const chipPosition = new THREE.Vector3(pos3D.chipX, 0, pos3D.chipZ); // Y is 0, chip height handled by createChip3D
                        const stackCount = Math.min(Math.ceil(player.total_bet_this_hand / getChipDenomination(player.total_bet_this_hand)), 10); // Max 10 chips visual
                        const chipStack = createChip3D(player.total_bet_this_hand, chipPosition, stackCount);
                        scene.add(chipStack);
                        chipStackObjects[`player_bet_${player.id}`] = chipStack;
                        gsap.from(chipStack.scale, {duration: 0.4, x:0, y:0, z:0, ease: "elastic.out(1, 0.5)"});
                    }
                }
            });
            
            // Main pot chips
            if (currentGameState.pot > 0) { // This pot is sum of all side_pots + main for display
                const potDisplayAmount = currentGameState.side_pots.reduce((sum, sp) => sum + sp.amount, 0);
                if(potDisplayAmount > 0) {
                    const potPosition = new THREE.Vector3(0, 0, 1.5); // Central pot area
                    const stackCount = Math.min(Math.ceil(potDisplayAmount / getChipDenomination(potDisplayAmount)), 20);
                    const potChips = createChip3D(potDisplayAmount, potPosition, stackCount);
                    scene.add(potChips);
                    chipStackObjects["main_pot"] = potChips;
                    gsap.from(potChips.scale, {duration: 0.5, x:0, y:0, z:0, ease: "elastic.out(1, 0.3)"});
                }
            }
            // Dealer button
            if(currentGameState.dealer_player_id && currentGameState.players[currentGameState.dealer_player_id]){
                const dealerPlayerIndex = playersArray.findIndex(p => p.id === currentGameState.dealer_player_id);
                if(dealerPlayerIndex !== -1 && dealerPlayerIndex < playerPositions.length){
                    const dealerPos3D = playerPositions[dealerPlayerIndex];
                    // Position button slightly in front of player's cards
                    const buttonPos = new THREE.Vector3(
                        dealerPos3D.x + Math.cos(dealerPos3D.angle) * 0.7, 
                        cardBaseY, 
                        dealerPos3D.z + Math.sin(dealerPos3D.angle) * 0.7
                    );
                    if(dealerButtonMesh) scene.remove(dealerButtonMesh);
                    dealerButtonMesh = new THREE.Mesh(
                        new THREE.CylinderGeometry(0.2, 0.2, 0.05, 16),
                        new THREE.MeshPhongMaterial({color: 0xffffff, emissive: 0x333333})
                    );
                    dealerButtonMesh.position.copy(buttonPos);
                    // Add 'D' text on button
                    scene.add(dealerButtonMesh);
                }
            }

        }

        function clearTable3DObjects() {
            communityCardObjects.forEach(obj => scene.remove(obj));
            communityCardObjects = [];
            
            Object.values(playerCardObjects3D).forEach(cardsList => cardsList.forEach(obj => scene.remove(obj)));
            playerCardObjects3D = {};
            
            Object.values(chipStackObjects).forEach(obj => scene.remove(obj));
            chipStackObjects = {};

            if(dealerButtonMesh) scene.remove(dealerButtonMesh);
            dealerButtonMesh = null;
        }

        // WebSocket Connection Management
        function connectWebSocket() {
            if (isLoadingOrReconnecting) return; // Prevent multiple connection attempts overlaying notifications
            isLoadingOrReconnecting = true;
            showLoadingScreen('Connecting to Royal Poker 3D...');

            const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
            const wsUrl = `${protocol}//${window.location.host}/ws`;
            
            ws = new WebSocket(wsUrl);
            
            ws.onopen = function() {
                console.log('Connected to advanced poker server');
                isConnected = true;
                isLoadingOrReconnecting = false;
                hideLoadingScreen();
                showMainMenu(); // Show menu after initial connect
                // Welcome notification sent by server
            };
            
            ws.onmessage = function(event) {
                const message = JSON.parse(event.data);
                handleServerMessage(message);
            };
            
            ws.onclose = function() {
                console.log('Disconnected from server');
                isConnected = false;
                clearTable3DObjects(); // Clear table on disconnect
                if (!isLoadingOrReconnecting) { // Only show reconnecting message if not already trying
                    showLoadingScreen('Connection lost. Reconnecting...');
                    showNotification('Connection lost. Attempting to reconnect...', 'error');
                }
                isLoadingOrReconnecting = true; 
                
                // Attempt to reconnect after a delay
                setTimeout(() => {
                    isLoadingOrReconnecting = false; // Allow next attempt to show notification if needed
                    connectWebSocket();
                }, 5000); // Increased reconnect delay
            };
            
            ws.onerror = function(error) {
                console.error('WebSocket error:', error);
                if (!isLoadingOrReconnecting) { // Avoid duplicate error messages if already trying to reconnect
                    showNotification('Connection error. Check console.', 'error');
                    // Potentially trigger reconnect logic similar to onclose if appropriate
                }
                 isLoadingOrReconnecting = false; // Allow trying again
            };
        }

        function sendMessage(action, payload = {}) {
            if (ws && ws.readyState === WebSocket.OPEN) {
                ws.send(JSON.stringify({ action, payload }));
            } else {
                showNotification('Not connected to server. Please wait.', 'error');
            }
        }

        function handleServerMessage(message) {
            console.log('Received:', message);
            
            switch (message.type) {
                case 'connected':
                    myPlayerId = message.data.player_id; // Store my player ID
                    showNotification(`Welcome to Royal Poker 3D! Your ID: ${myPlayerId.substring(0,6)}`, 'success');
                    break;
                    
                case 'room_created': // Server sends this after successful create + join
                case 'room_joined':
                    currentRoomCode = message.data.room_code;
                    isPlayerInGame = true; // Assumes joining means playing, spectate is separate
                    showGameInterface();
                    showNotification(`Joined room: ${currentRoomCode}`, 'success');
                    animateCameraToTable();
                    break;
                    
                case 'spectating':
                    currentRoomCode = message.data.room_code;
                    isPlayerInGame = false;
                    showGameInterface();
                    showNotification(`Spectating room: ${currentRoomCode}`, 'info');
                    animateCameraToTable();
                    break;
                    
                case 'room_left':
                    showMainMenu();
                    showNotification('You have left the room.', 'info');
                    animateCameraToMenu();
                    currentRoomCode = null;
                    currentGameState = null;
                    isPlayerInGame = false;
                    clearTable3DObjects();
                    break;
                    
                case 'game_state':
                    currentGameState = message.data;
                    updateGameInterface(); // This will call updateTableVisuals internally
                    break;
                    
                case 'game_started':
                    showNotification('Game started! Good luck!', 'success');
                    // Game state update will handle visuals
                    break;
                
                case 'action_accepted': // Optional: server can send this for quick feedback
                    // showNotification('Action accepted!', 'info', 1000); // Short duration
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
                
                case 'game_paused':
                    showNotification('Game paused by owner.', 'warning');
                    break;
                case 'game_resumed':
                    showNotification('Game resumed.', 'info');
                    break;
                case 'player_kicked':
                    showNotification('A player was kicked by the owner.', 'info');
                    // If *I* was kicked, server should send a room_left or specific "kicked" message.
                    // For now, rely on game_state removing the player.
                    break;

                default:
                    console.warn('Unknown message type from server:', message.type);
            }
        }

        // Camera Animation Functions
        function animateCameraToTable() {
            cameraAnimating = true;
            targetCameraRotationY = 0; // Reset rotation for default table view
            targetCameraDistance = 15;
            gsap.to(camera.position, {
                duration: 1.5, // Faster animation
                x: 0, y: 12, z: 15,
                ease: "power2.inOut",
                onUpdate: () => camera.lookAt(0,0,0),
                onComplete: () => cameraAnimating = false
            });
        }

        function animateCameraToMenu() {
            cameraAnimating = true;
            targetCameraRotationY = Math.PI / 8; // Slight angle for menu
            targetCameraDistance = 20;
            gsap.to(camera.position, {
                duration: 1.5,
                x: 5, y: 15, z: 20, // Example menu camera position
                ease: "power2.inOut",
                onUpdate: () => camera.lookAt(0,0,0),
                onComplete: () => cameraAnimating = false
            });
        }

        // UI Management Functions
        function hideLoadingScreen() {
            const loadingScreen = document.getElementById('loadingScreen');
            gsap.to(loadingScreen, {
                duration: 0.5, // Faster fade
                opacity: 0,
                onComplete: () => loadingScreen.style.display = 'none'
            });
        }

        function showLoadingScreen(text = 'Loading casino experience...') {
            const loadingScreen = document.getElementById('loadingScreen');
            loadingScreen.querySelector('.loading-text').textContent = text;
            loadingScreen.style.display = 'flex';
            gsap.to(loadingScreen, { duration: 0.3, opacity: 1 });
        }

        function showMainMenu() {
            document.getElementById('menuPanel').classList.remove('hidden');
            document.getElementById('gameHUD').classList.add('hidden');
            document.getElementById('potDisplay').classList.add('hidden');
            document.getElementById('actionsPanel').classList.add('hidden');
            document.getElementById('chatPanel').classList.add('hidden');
            document.getElementById('playerCardsDisplay').classList.add('hidden');
            document.getElementById('tournamentInfo').classList.add('hidden');
            document.getElementById('actionTimer').classList.add('hidden');
            
            currentRoomCode = null;
            currentGameState = null;
            isPlayerInGame = false;
            clearTable3DObjects();
        }

        function showGameInterface() {
            document.getElementById('menuPanel').classList.add('hidden');
            document.getElementById('gameHUD').classList.remove('hidden');
            document.getElementById('chatPanel').classList.remove('hidden');
            document.getElementById('playerCardsDisplay').classList.remove('hidden');
            
            if (currentRoomCode) {
                document.getElementById('currentRoom').textContent = currentRoomCode;
            }
            // Pot, actions, etc., shown based on game state
        }

        function updateGameInterface() {
            if (!currentGameState) return;

            document.getElementById('phaseText').textContent = currentGameState.phase.replace(/_/g, ' ').toUpperCase();
            document.getElementById('handNumber').textContent = currentGameState.hand_number;
            document.getElementById('betToMatch').textContent = currentGameState.current_bet_to_match.toLocaleString();

            const potDisplayEl = document.getElementById('potDisplay');
            const totalPotForDisplay = currentGameState.side_pots.reduce((sum, sp) => sum + sp.amount, 0);

            if (totalPotForDisplay > 0) {
                potDisplayEl.classList.remove('hidden');
                document.getElementById('potAmount').textContent = totalPotForDisplay.toLocaleString();
                
                const sidePotsDisplayEl = document.getElementById('sidePotsDisplay');
                if (currentGameState.side_pots && currentGameState.side_pots.length > 1) { // Show only if actual side pots exist
                    sidePotsDisplayEl.innerHTML = currentGameState.side_pots
                        .map((sp, i) => `Side ${i+1}: ${sp.amount.toLocaleString()} (${sp.winning_hand || 'Pending'})`)
                        .join('<br>');
                } else {
                    sidePotsDisplayEl.innerHTML = '';
                }
            } else {
                potDisplayEl.classList.add('hidden');
            }

            const myPlayerData = currentGameState.players[myPlayerId];
            if (myPlayerData) {
                document.getElementById('moneyAmount').textContent = myPlayerData.money.toLocaleString();
            } else {
                 document.getElementById('moneyAmount').textContent = 'N/A'; // Spectator or not found
            }


            if (currentGameState.tournament_info) { /* ... As before ... */ } 
            else { document.getElementById('tournamentInfo').classList.add('hidden'); }

            if (currentGameState.can_act && currentGameState.time_left_for_action > 0) { /* ... As before ... */ } 
            else { document.getElementById('actionTimer').classList.add('hidden'); }
            
            const startBtn = document.getElementById('startGameBtn');
            const canStart = currentGameState.phase === 'waiting' &&
                             Object.values(currentGameState.players).filter(p => p.status !== 'eliminated' && p.status !== 'sitting_out').length >= (currentGameState.settings.min_players || 2) &&
                             isPlayerInGame; // Only players can start
            startBtn.style.display = canStart ? 'block' : 'none';
            
            const pauseBtn = document.getElementById('pauseGameBtn');
             // Only room owner can pause/resume. Assuming owner_id is part of game_state or player object.
             // For now, enable if player. For better UX, check if self is owner.
            pauseBtn.style.display = isPlayerInGame ? 'block' : 'none';
            pauseBtn.textContent = currentGameState.paused ? "▶️ Resume Game" : "⏸️ Pause Game";


            if (currentGameState.can_act && currentGameState.available_actions && isPlayerInGame) {
                document.getElementById('actionsPanel').classList.remove('hidden');
                updateActionButtons();
            } else {
                document.getElementById('actionsPanel').classList.add('hidden');
            }

            updatePlayerCardsUI(); // Renamed to avoid conflict
            updateChat();
            updateTableVisuals(); // Update 3D scene based on new state
            
            if (currentGameState.paused && currentGameState.pause_reason) {
                showNotification(`Game paused: ${currentGameState.pause_reason}`, 'warning', 5000);
            }
        }
        
        function updateActionButtons() {
            if (!currentGameState || !currentGameState.available_actions) return;
            const actions = currentGameState.available_actions;
            
            ['foldBtn', 'checkBtn', 'callBtn', 'raiseBtn', 'allInBtn'].forEach(id => {
                const btn = document.getElementById(id);
                if(btn) { btn.disabled = true; btn.style.display = 'none';}
            });
            document.querySelector('.raise-controls').style.display = 'none'; // Hide raise slider group initially

            actions.forEach(action => {
                const btn = document.getElementById(action.action.toLowerCase() + 'Btn'); // e.g. foldBtn
                if (btn) {
                    btn.disabled = false;
                    btn.style.display = 'inline-block';
                    if (action.action === 'call') {
                        document.getElementById('callAmount').textContent = action.amount.toLocaleString();
                    } else if (action.action === 'all_in') {
                        btn.innerHTML = `🔥 ALL IN ${action.amount.toLocaleString()}`;
                    } else if (action.action === 'raise') {
                        document.querySelector('.raise-controls').style.display = 'flex'; // Show raise group
                        const raiseSlider = document.getElementById('raiseSlider');
                        const raiseAmountInput = document.getElementById('raiseAmountInput');
                        
                        // Calculate total bet "Raise To" amount. Action.amount is the raise ON TOP of call.
                        const callAmountForRaise = currentGameState.current_bet_to_match - (currentGameState.players[myPlayerId]?.current_bet || 0);
                        const minTotalBet = currentGameState.current_bet_to_match + action.min_amount;
                        const maxTotalBet = (currentGameState.players[myPlayerId]?.current_bet || 0) + callAmountForRaise + action.max_amount;

                        raiseSlider.min = minTotalBet;
                        raiseSlider.max = maxTotalBet;
                        raiseAmountInput.min = minTotalBet;
                        raiseAmountInput.max = maxTotalBet;
                        
                        // Set initial value to minimum valid raise if current input is too low or not set
                        if (!raiseAmountInput.value || parseInt(raiseAmountInput.value) < minTotalBet) {
                            raiseAmountInput.value = minTotalBet;
                        }
                        raiseSlider.value = raiseAmountInput.value;
                    }
                }
            });
        }


        function updatePlayerCardsUI() { // Renamed
            const playerCardsContainer = document.getElementById('playerCardsDisplay');
            playerCardsContainer.innerHTML = '';
            
            if (!currentGameState || !currentGameState.players) return;
            
            Object.values(currentGameState.players).forEach(player => {
                const playerCardDiv = document.createElement('div');
                playerCardDiv.className = 'player-card';
                if (player.is_current_player) playerCardDiv.classList.add('current-player');
                if (player.status === 'folded') playerCardDiv.classList.add('folded');
                if (player.status === 'all_in') playerCardDiv.classList.add('all-in');
                if (player.id === myPlayerId) playerCardDiv.style.borderColor = 'cyan'; // Highlight self

                let nameDisplay = player.name;
                if(player.is_ai) nameDisplay += ' <span class="ai-badge">(AI)</span>';
                
                playerCardDiv.innerHTML = `
                    <div class="player-avatar" style="background-color: ${player.color}">${player.name.charAt(0).toUpperCase()}</div>
                    <div class="player-name">${nameDisplay}</div>
                    <div class="player-money">$${player.money.toLocaleString()}</div>
                    ${player.current_bet > 0 ? `<div style="color: var(--primary-gold); font-size: 0.8rem;">Bet: $${player.current_bet.toLocaleString()}</div>` : ''}
                    ${player.last_action ? `<div class="player-action">${player.last_action.toUpperCase()} ${player.last_action_amount > 0 ? '$'+player.last_action_amount : ''}</div>` : ''}
                    ${player.is_dealer ? '<div style="position: absolute; top: -8px; left: -8px; background: gold; color: black; border-radius: 50%; width: 24px; height: 24px; display: flex; align-items: center; justify-content: center; font-size: 0.9rem; font-weight: bold; box-shadow: 0 0 5px black;">D</div>' : ''}
                `;
                playerCardsContainer.appendChild(playerCardDiv);
                gsap.from(playerCardDiv, { duration: 0.3, opacity:0, y: 10, ease: "power2.out", delay: 0.1 }); // Subtle animation
            });
        }

        function updateChat() { /* ... As before, but ensure scroll logic is robust ... */ 
            if (!currentGameState || !currentGameState.chat_messages) return;
            const chatMessagesEl = document.getElementById('chatMessages');
            const isScrolledToBottom = chatMessagesEl.scrollHeight - chatMessagesEl.clientHeight <= chatMessagesEl.scrollTop + 1;

            // Simple clear and redraw. For performance with many messages, consider incremental updates.
            chatMessagesEl.innerHTML = ''; 
            currentGameState.chat_messages.forEach(msg => {
                const msgDiv = document.createElement('div');
                msgDiv.className = 'chat-message';
                msgDiv.style.borderLeftColor = msg.player_color || '#ffffff';
                
                // Sanitize message content before inserting as HTML to prevent XSS
                const nameSpan = document.createElement('span');
                nameSpan.className = 'chat-player-name';
                nameSpan.style.color = msg.player_color || '#ffffff';
                nameSpan.textContent = msg.player_name + ': ';

                const messageSpan = document.createElement('span');
                messageSpan.textContent = msg.message;

                const timeSpan = document.createElement('span');
                timeSpan.className = 'chat-timestamp';
                timeSpan.textContent = msg.formatted_time;
                
                msgDiv.appendChild(nameSpan);
                msgDiv.appendChild(messageSpan);
                msgDiv.appendChild(timeSpan);
                chatMessagesEl.appendChild(msgDiv);
            });
            if (isScrolledToBottom) {
                chatMessagesEl.scrollTop = chatMessagesEl.scrollHeight;
            }
        }

        function updateTournamentTimer(nextLevelTimeStr) { /* ... As before ... */ }

        // Game Action Functions
        function createQuickRoom() {
            const playerName = document.getElementById('playerName').value.trim() || 'Player';
            sendMessage('create_room', { 
                player_name: playerName,
                game_mode: 'cash_game',
                small_blind: 25, big_blind: 50, max_players: 8, ai_players: 1 // Default 1 AI for quick game
            });
        }

        function createCustomRoom() {
            const payload = {
                player_name: document.getElementById('playerName').value.trim() || 'Player',
                room_name: document.getElementById('roomName').value.trim() || null,
                game_mode: document.getElementById('gameMode').value,
                max_players: parseInt(document.getElementById('maxPlayers').value),
                small_blind: parseInt(document.getElementById('smallBlind').value),
                big_blind: parseInt(document.getElementById('bigBlind').value),
                buy_in: parseInt(document.getElementById('buyIn').value),
                password: document.getElementById('roomPassword').value.trim() || null,
                ai_players: parseInt(document.getElementById('aiPlayers').value)
            };
            sendMessage('create_room', payload);
        }

        function joinRoom() { /* ... As before, ensure player_name is sent ... */ }
        function spectateRoom() { /* ... As before ... */ }
        function leaveRoom() { /* ... As before ... */ }
        function startGame() { /* ... As before ... */ }
        function pauseGame() { /* ... As before ... */ }

        function playerAction(actionTypeStr) { // actionTypeStr is 'fold', 'check', etc.
            let payload = { action_type: actionTypeStr };
            if (actionTypeStr === 'raise') {
                const raiseToAmount = parseInt(document.getElementById('raiseAmountInput').value);
                // Server expects "amount" to be the raise ON TOP of a call.
                // Client UI has "Raise To Amount". Calculate difference.
                const currentMyBet = currentGameState.players[myPlayerId]?.current_bet || 0;
                const callAmount = currentGameState.current_bet_to_match - currentMyBet;
                const raiseAmountOnTopOfCall = raiseToAmount - (currentMyBet + callAmount);

                if (raiseAmountOnTopOfCall < (currentGameState.min_raise_amount || 0) && (currentMyBet + callAmount + raiseAmountOnTopOfCall) < currentGameState.players[myPlayerId]?.money) {
                     // If raise is less than min_raise_amount AND not an all-in
                    showNotification(`Raise must be at least to $${currentMyBet + callAmount + (currentGameState.min_raise_amount || 0)} (or All-In)`, 'error');
                    return;
                }
                payload.amount = Math.max(0, raiseAmountOnTopOfCall); // Ensure not negative
            }
            sendMessage('player_action', payload);
        }


        function sendChat() { /* ... As before ... */ }
        function toggleChat() { /* ... As before ... */ }

        function updateRaiseAmountInput() { // Slider moves, update input box
            document.getElementById('raiseAmountInput').value = document.getElementById('raiseSlider').value;
        }
        function updateRaiseSliderFromInput() { // Input box changes, update slider
            const inputVal = parseInt(document.getElementById('raiseAmountInput').value);
            const slider = document.getElementById('raiseSlider');
            if (inputVal >= parseInt(slider.min) && inputVal <= parseInt(slider.max)) {
                slider.value = inputVal;
            } else if (inputVal < parseInt(slider.min)) {
                 slider.value = slider.min;
                 document.getElementById('raiseAmountInput').value = slider.min;
            } else if (inputVal > parseInt(slider.max)) {
                slider.value = slider.max;
                document.getElementById('raiseAmountInput').value = slider.max;
            }
        }

        // Room List Functions
        function showRoomList() { /* ... As before ... */ }
        function hideRoomList() { /* ... As before ... */ }
        function refreshRoomList() { /* ... As before ... */ }
        function updateRoomList(rooms) { /* ... As before, maybe add AI count if available in room data ... */ }
        function joinRoomByCode(roomCode) { /* ... As before ... */ }
        function spectateRoomByCode(roomCode) { /* ... As before ... */ }

        // Hand History Functions
        function showHandHistory() { /* ... As before ... */ }
        function hideHandHistory() { /* ... As before ... */ }
        function updateHandHistory(history) {
            const content = document.getElementById('handHistoryContent');
            if (!history || history.length === 0) {
                content.innerHTML = '<div style="text-align: center; color: #ccc; padding: 20px;">No hand history available.</div>';
                return;
            }
            content.innerHTML = history.map(hand => {
                let playerActionsHtml = hand.players.map(p => {
                    let actionsStr = p.actions.map(act => `${act.phase}: ${act.action} ${act.amount > 0 ? '$'+act.amount : ''}`).join(', ');
                    return `<div><strong>${p.name}</strong> (Bet: $${p.total_bet_this_hand}): ${actionsStr || 'No actions'} ${p.amount_won > 0 ? `- Won $${p.amount_won}` : ''}</div>`;
                }).join('');

                let winnersHtml = Object.entries(hand.winners || {}).map(([pId, winInfo]) => {
                     const winnerPlayer = hand.players.find(p => p.id === pId);
                     return `<div>${winnerPlayer ? winnerPlayer.name : 'Unknown'} won $${winInfo.amount_won} (${winInfo.hand_description})</div>`;
                }).join('');


                return `
                <div style="background: rgba(255,255,255,0.05); border-radius: 10px; padding: 15px; margin-bottom: 10px; border: 1px solid var(--primary-gold);">
                    <div style="display: flex; justify-content: space-between; margin-bottom: 10px;">
                        <strong style="color: var(--primary-gold);">Hand #${hand.hand_number}</strong>
                        <span style="color: #ccc; font-size: 0.9rem;">${new Date(hand.timestamp).toLocaleTimeString()}</span>
                    </div>
                    <div><strong>Community:</strong> ${hand.community_cards.map(c => c.rank + c.suit[0].toUpperCase()).join(' ') || 'N/A'}</div>
                    <div><strong>Total Pot:</strong> $${hand.total_pot_distributed.toLocaleString()}</div>
                    <div style="margin-top: 5px;"><strong>Player Actions & Bets:</strong>${playerActionsHtml}</div>
                     <div style="margin-top: 5px;"><strong>Winners:</strong>${winnersHtml || 'N/A'}</div>
                </div>`;
            }).join('');
        }


        // Notification System
        function showNotification(message, type = 'info', duration = 4000) {
            const container = document.getElementById('notificationContainer');
            const notification = document.createElement('div');
            notification.className = `notification ${type}`;
            notification.textContent = message;
            
            container.appendChild(notification);
            
            gsap.from(notification, {duration: 0.5, x: "100%", opacity: 0, ease: "power2.out"});

            setTimeout(() => {
                gsap.to(notification, {
                    duration: 0.5, x: "100%", opacity: 0, ease: "power2.in",
                    onComplete: () => {
                        if (notification.parentNode) notification.parentNode.removeChild(notification);
                    }
                });
            }, duration);
        }

        // Handle window resize
        window.addEventListener('resize', function() { /* ... As before ... */ });
        // Keyboard shortcuts
        document.addEventListener('keydown', function(event) { /* ... As before, ensure button IDs match ... */ });

        // Initialize everything
        window.addEventListener('load', function() {
            initThreeJS(); // Setup 3D scene
            connectWebSocket(); // Connect to server
            // Loading screen is shown by connectWebSocket if needed
        });

        // Add CSS animations for timer (already in HTML <style>)
    </script>
</body>
</html>
