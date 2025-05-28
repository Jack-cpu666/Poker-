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
from fastapi.responses import HTMLResponse, FileResponse # Added FileResponse
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
GAME_UPDATE_RATE = 30
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
    suit: str
    rank: str
    id: str = field(default_factory=lambda: str(uuid.uuid4()))
    
    def __str__(self):
        return f"{self.rank}{self.suit[0].upper()}"
    
    def value(self) -> int:
        if self.rank == 'A': return 14
        elif self.rank == 'K': return 13
        elif self.rank == 'Q': return 12
        elif self.rank == 'J': return 11
        else: return int(self.rank)
    
    def suit_value(self) -> int:
        return ['clubs', 'diamonds', 'hearts', 'spades'].index(self.suit)

@dataclass
class HandEvaluation:
    rank: HandRank
    value: int
    cards_used: List[Card]
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
    vpip: float = 0.0
    pfr: float = 0.0
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
    last_action_amount: int = 0
    avatar: str = "default"
    color: str = "#ffffff"
    is_dealer: bool = False
    is_small_blind: bool = False
    is_big_blind: bool = False
    time_bank: int = 30
    connection_id: Optional[str] = None
    stats: PlayerStats = field(default_factory=PlayerStats)
    session_id: str = field(default_factory=lambda: str(uuid.uuid4()))
    tournament_rank: int = 0
    is_ai: bool = False
    actions_this_hand: List[Dict] = field(default_factory=list)
    
    def can_act(self) -> bool:
        return self.status == PlayerStatus.ACTIVE and self.money > 0

    def is_all_in_for_hand(self) -> bool:
        return self.status == PlayerStatus.ALL_IN or (self.money == 0 and self.current_bet > 0)

    def reset_for_new_hand(self):
        self.cards = []
        self.current_bet = 0
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
    tournament_structure: Dict = field(default_factory=dict)
    buy_in: int = 0
    password: Optional[str] = None
    ai_players: int = 0

@dataclass
class Room:
    code: str
    name: str
    players: Dict[str, Player]
    spectators: Set[str]
    deck: List[Card]
    community_cards: List[Card]
    current_player_id: Optional[str] = None
    dealer_player_id: Optional[str] = None
    phase: GamePhase = GamePhase.WAITING
    pot: int = 0
    side_pots: List[SidePot] = field(default_factory=list)
    current_bet_to_match: int = 0
    min_raise_amount: int = BIG_BLIND
    chat_messages: List[Dict] = field(default_factory=list)
    last_action_timestamp: float = 0
    hand_number: int = 0
    settings: GameSettings = field(default_factory=GameSettings)
    room_type: RoomType = RoomType.PUBLIC
    created_at: datetime = field(default_factory=datetime.now)
    last_activity: datetime = field(default_factory=datetime.now)
    owner_id: Optional[str] = None
    hand_history: List[Dict] = field(default_factory=list)
    tournament_level: int = 1
    tournament_next_blind_increase: datetime = field(default_factory=lambda: datetime.now() + timedelta(minutes=10))
    paused: bool = False
    pause_reason: str = ""
    _player_order_for_hand: List[str] = field(default_factory=list)
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

    def deal_cards(self):
        for _ in range(2):
            for player_id in self._player_order_for_hand:
                player = self.players.get(player_id)
                if player and player.status != PlayerStatus.SITTING_OUT and player.status != PlayerStatus.ELIMINATED:
                    if self.deck:
                        player.cards.append(self.deck.pop())

    def deal_community_cards(self, count: int):
        if self.deck: self.deck.pop() 
        for _ in range(count):
            if self.deck:
                self.community_cards.append(self.deck.pop())

    def get_active_players_in_hand(self) -> List[Player]:
        return [p for p_id in self._player_order_for_hand 
                if (p := self.players.get(p_id)) and p.status not in [PlayerStatus.FOLDED, PlayerStatus.ELIMINATED, PlayerStatus.SITTING_OUT]]

    def get_players_eligible_for_pot(self) -> List[Player]:
        return [p for p in self.players.values() if p.status not in [PlayerStatus.FOLDED, PlayerStatus.ELIMINATED]]

    def calculate_side_pots(self):
        self.side_pots = []
        contending_players = sorted(
            [p for p in self.get_players_eligible_for_pot() if p.total_bet_this_hand > 0],
            key=lambda p: p.total_bet_this_hand
        )
        if not contending_players: return

        main_pot_amount = self.pot
        all_in_bets = sorted(list(set(p.total_bet_this_hand for p in contending_players if p.is_all_in_for_hand())))
        last_bet_level = 0
        for bet_level in all_in_bets:
            if bet_level == 0: continue
            pot_amount_at_this_level = 0
            eligible_for_this_pot = set()
            for p in self.get_players_eligible_for_pot():
                contribution = min(p.total_bet_this_hand, bet_level) - last_bet_level
                if contribution > 0:
                    pot_amount_at_this_level += contribution
                    eligible_for_this_pot.add(p.id)
            if pot_amount_at_this_level > 0:
                self.side_pots.append(SidePot(amount=pot_amount_at_this_level, eligible_players=eligible_for_this_pot))
                main_pot_amount -= pot_amount_at_this_level
            last_bet_level = bet_level
        if main_pot_amount > 0:
            eligible_main_pot = {p.id for p in self.get_players_eligible_for_pot() if p.total_bet_this_hand >= last_bet_level}
            if eligible_main_pot:
                self.side_pots.insert(0, SidePot(amount=main_pot_amount, eligible_players=eligible_main_pot))
        if not self.side_pots and self.pot > 0:
            eligible_players = {p.id for p in self.get_players_eligible_for_pot()}
            if eligible_players:
                self.side_pots.append(SidePot(amount=self.pot, eligible_players=eligible_players))
        self.side_pots = [sp for sp in self.side_pots if sp.amount > 0 and sp.eligible_players]
        logger.info(f"Room {self.code} calculated side pots: {self.side_pots}")

    def update_activity(self):
        self.last_activity = datetime.now()

    def get_player_acting_next(self, start_player_id: str) -> Optional[str]:
        if not self._player_order_for_hand: return None
        try:
            current_idx = self._player_order_for_hand.index(start_player_id)
        except ValueError:
            logger.warning(f"get_player_acting_next: start_player_id {start_player_id} not in _player_order_for_hand for room {self.code}. Trying to find first valid actor.")
            current_idx = -1 
        for i in range(len(self._player_order_for_hand)):
            next_idx = (current_idx + 1 + i) % len(self._player_order_for_hand)
            next_player_id = self._player_order_for_hand[next_idx]
            player = self.players.get(next_player_id)
            if player and player.can_act() and not player.is_all_in_for_hand():
                return player.id
        return None

class AdvancedPokerGame:
    def __init__(self):
        self.rooms: Dict[str, Room] = {}
        self.connections: Dict[str, WebSocket] = {}
        self.player_rooms: Dict[str, str] = {}
        self.rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.action_rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.hand_evaluation_cache: Dict[str, HandEvaluation] = {}
        self.running = True
        self.global_stats = {'total_hands': 0, 'total_players': 0, 'active_rooms': 0, 'biggest_pot': 0}

    def generate_room_code(self) -> str:
        return ''.join(random.choices('ABCDEFGHJKLMNPQRSTUVWXYZ23456789', k=6))

    def create_room(self, creator_player_id: str, room_settings: GameSettings, room_name: str = None) -> Optional[str]:
        if len(self.rooms) >= MAX_ROOMS:
            logger.error("Maximum number of rooms reached")
            return None
        room_code = self.generate_room_code()
        while room_code in self.rooms: room_code = self.generate_room_code()
        room_name = room_name or f"Room {room_code}"
        self.rooms[room_code] = Room(code=room_code, name=room_name, players={}, spectators=set(), deck=[], community_cards=[], settings=room_settings, owner_id=creator_player_id, room_type=RoomType.PRIVATE if room_settings.password else RoomType.PUBLIC)
        for i in range(room_settings.ai_players):
            ai_player_id = f"AI_{str(uuid.uuid4())[:8]}"
            ai_player = Player(id=ai_player_id, name=f"AI Bot {i+1}", money=room_settings.buy_in if room_settings.buy_in > 0 else (TOURNAMENT_STARTING_MONEY if room_settings.game_mode == GameMode.TOURNAMENT else STARTING_MONEY), is_ai=True, avatar=f"avatar_ai_{random.randint(1,3)}", color=f"#{random.randint(0x808080, 0xFFFFFF):06x}")
            self.rooms[room_code].players[ai_player_id] = ai_player
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
        human_players_count = sum(1 for p in room.players.values() if not p.is_ai)
        if human_players_count >= room.settings.max_players: 
            logger.warning(f"Room {room_code} is full (max human players: {room.settings.max_players})")
            return False
        
        if player_id in room.players:
            rejoining_player = room.players[player_id]
            if rejoining_player.is_ai: 
                logger.warning(f"Human player {player_id} attempting to join as existing AI {rejoining_player.name}")
                return False
            rejoining_player.connection_id = player_id
            rejoining_player.name = player_name
            if rejoining_player.status == PlayerStatus.ELIMINATED and room.settings.game_mode != GameMode.TOURNAMENT:
                rejoining_player.status = PlayerStatus.ACTIVE
                rejoining_player.money = room.settings.buy_in if room.settings.buy_in > 0 else STARTING_MONEY
            logger.info(f"Player {player_name} ({player_id}) re-joined room {room_code}")
        else:
            player = Player(id=player_id, name=player_name, money=room.settings.buy_in if room.settings.buy_in > 0 else (TOURNAMENT_STARTING_MONEY if room.settings.game_mode == GameMode.TOURNAMENT else STARTING_MONEY), avatar=f"avatar_{random.randint(1, 10)}", color=f"#{random.randint(0, 0xFFFFFF):06x}", connection_id=player_id, is_ai=False)
            room.players[player_id] = player
            logger.info(f"Player {player_name} ({player_id}) joined room {room_code}")
        self.player_rooms[player_id] = room_code
        room.update_activity()
        return True

    def leave_room(self, player_id: str, force: bool = False):
        room_code = self.player_rooms.pop(player_id, None)
        if not room_code: 
            logger.info(f"Player {player_id} tried to leave but was not in any room.")
            return
        room = self.rooms.get(room_code)
        if not room: 
            logger.warning(f"Player {player_id} was in room {room_code}, but room not found.")
            return

        player_obj = room.players.pop(player_id, None)
        if player_obj:
            logger.info(f"Player {player_obj.name} ({player_id}) left room {room_code}.")
            if room.phase not in [GamePhase.WAITING, GamePhase.GAME_OVER] and player_obj.status != PlayerStatus.FOLDED:
                 player_obj.status = PlayerStatus.FOLDED
                 if room.current_player_id == player_id:
                     self.advance_game_flow(room_code)
        room.spectators.discard(player_id)
        if not any(not p.is_ai for p in room.players.values()) and not room.spectators:
            logger.info(f"Room {room_code} is empty of humans. Closing room.")
            if room_code in self.rooms: del self.rooms[room_code]
        elif room.owner_id == player_id and any(not p.is_ai for p in room.players.values()):
            new_owner = next((pid for pid, p in room.players.items() if not p.is_ai), None)
            if new_owner: 
                room.owner_id = new_owner
                logger.info(f"Room owner {player_id} left. New owner of room {room_code} is {new_owner}.")
            else: 
                logger.info(f"Owner {player_id} left room {room_code}, no other human players.")
        room.update_activity()

    def start_game(self, room_code: str):
        room = self.rooms.get(room_code)
        if not room: return False
        eligible_players = [p for p in room.players.values() if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED] and p.money > 0]
        if len(eligible_players) < room.settings.min_players: 
            logger.warning(f"Cannot start game in room {room_code}: Not enough players ({len(eligible_players)}/{room.settings.min_players})")
            return False
        if room.phase != GamePhase.WAITING: 
            logger.warning(f"Game already in progress in room {room_code}. Phase: {room.phase}")
            return False

        room.phase = GamePhase.PRE_FLOP
        room.hand_number += 1
        room.shuffle_deck()
        room.community_cards = []
        room.pot = 0
        room.side_pots = []
        
        eligible_player_ids_for_rotation = [p.id for p in eligible_players]
        if not room.dealer_player_id or room.dealer_player_id not in eligible_player_ids_for_rotation:
            room.dealer_player_id = eligible_player_ids_for_rotation[0]
        else:
            current_dealer_idx = eligible_player_ids_for_rotation.index(room.dealer_player_id)
            next_dealer_idx = (current_dealer_idx + 1) % len(eligible_player_ids_for_rotation)
            room.dealer_player_id = eligible_player_ids_for_rotation[next_dealer_idx]

        dealer_actual_idx_in_eligible = -1
        for i, p in enumerate(eligible_players):
            if p.id == room.dealer_player_id:
                dealer_actual_idx_in_eligible = i
                break
        
        room._player_order_for_hand = []
        if dealer_actual_idx_in_eligible != -1:
            ordered_for_blinds_and_action = eligible_players[dealer_actual_idx_in_eligible+1:] + eligible_players[:dealer_actual_idx_in_eligible+1]
            room._player_order_for_hand = [p.id for p in ordered_for_blinds_and_action]

        for p_id, player in room.players.items():
            player.reset_for_new_hand()
            if player.id not in room._player_order_for_hand and player.status != PlayerStatus.ELIMINATED and player.money > 0: 
                 player.status = PlayerStatus.SITTING_OUT

        if room.dealer_player_id in room.players:
            room.players[room.dealer_player_id].is_dealer = True

        num_players_in_hand_order = len(room._player_order_for_hand)
        if num_players_in_hand_order == 2: 
            sb_player_id = room.dealer_player_id
            bb_player_id = next(p_id for p_id in room._player_order_for_hand if p_id != room.dealer_player_id)
            if sb_player_id in room.players: room.players[sb_player_id].is_small_blind = True
            if bb_player_id in room.players: room.players[bb_player_id].is_big_blind = True
            room._player_order_for_hand = [sb_player_id, bb_player_id]
        elif num_players_in_hand_order > 0 :
            sb_player_id = room._player_order_for_hand[0] 
            if sb_player_id in room.players: room.players[sb_player_id].is_small_blind = True
            bb_player_id = room._player_order_for_hand[1 % num_players_in_hand_order] 
            if bb_player_id in room.players: room.players[bb_player_id].is_big_blind = True
        
        self.post_blinds_and_ante(room)
        room.current_bet_to_match = room.settings.big_blind
        room.min_raise_amount = room.settings.big_blind
        room.deal_cards()
        
        if num_players_in_hand_order > 0:
            if num_players_in_hand_order == 2:
                 room.current_player_id = room._player_order_for_hand[0]
            elif num_players_in_hand_order > 2:
                 bb_idx = -1
                 for i, p_id in enumerate(room._player_order_for_hand):
                     if room.players[p_id].is_big_blind: bb_idx = i; break
                 room.current_player_id = room._player_order_for_hand[(bb_idx + 1) % num_players_in_hand_order]
            else: room.current_player_id = None
        
        room.last_action_timestamp = time.time()
        self.global_stats['total_hands'] += 1
        logger.info(f"Game started in room {room_code}, hand #{room.hand_number}. Dealer: {room.dealer_player_id}, Current Player: {room.current_player_id}, Order: {room._player_order_for_hand}")
        if room.current_player_id and room.players[room.current_player_id].is_ai:
            asyncio.create_task(self.ai_perform_action(room_code, room.current_player_id))
        return True

    def post_blinds_and_ante(self, room: Room):
        if room.settings.ante > 0:
            for player_id in room._player_order_for_hand:
                player = room.players[player_id]
                ante_amount = min(room.settings.ante, player.money)
                player.money -= ante_amount; player.total_bet_this_hand += ante_amount; room.pot += ante_amount
                player.actions_this_hand.append({"action": "ante", "amount": ante_amount, "phase": room.phase.value})
                if player.money == 0: player.status = PlayerStatus.ALL_IN
        
        for player_id in room._player_order_for_hand:
            player = room.players[player_id]; blind_amount = 0; action_label = ""
            if player.is_small_blind: blind_amount = min(room.settings.small_blind, player.money); action_label = "small_blind"
            elif player.is_big_blind: blind_amount = min(room.settings.big_blind, player.money); action_label = "big_blind"
            if blind_amount > 0:
                player.money -= blind_amount; player.current_bet += blind_amount; player.total_bet_this_hand += blind_amount; room.pot += blind_amount
                player.actions_this_hand.append({"action": action_label, "amount": blind_amount, "phase": room.phase.value})
                if player.money == 0: player.status = PlayerStatus.ALL_IN
        logger.info(f"Room {room.code}: Blinds/antes posted. Pot: {room.pot}")

    async def ai_perform_action(self, room_code: str, player_id: str):
        await asyncio.sleep(random.uniform(AI_ACTION_DELAY_MIN, AI_ACTION_DELAY_MAX))
        room = self.rooms.get(room_code)
        if not room or room.current_player_id != player_id: return
        player = room.players.get(player_id)
        if not player or not player.is_ai or not player.can_act(): return

        available_actions = self.get_available_actions(room, player_id)
        action_to_perform = PlayerAction.FOLD; amount_to_perform = 0
        rand_choice = random.random()
        can_check = any(a['action'] == 'check' for a in available_actions)
        can_call = any(a['action'] == 'call' for a in available_actions)
        can_raise = any(a['action'] == 'raise' for a in available_actions)

        if rand_choice < 0.15 and any(a['action'] == 'fold' for a in available_actions): action_to_perform = PlayerAction.FOLD
        elif rand_choice < 0.75 : 
            if can_check: action_to_perform = PlayerAction.CHECK
            elif can_call:
                action_to_perform = PlayerAction.CALL
                amount_to_perform = next(a for a in available_actions if a['action'] == 'call')['amount']
        elif can_raise:
            action_to_perform = PlayerAction.RAISE
            amount_to_perform = next(a for a in available_actions if a['action'] == 'raise')['min_amount']
        elif can_call:
            action_to_perform = PlayerAction.CALL
            amount_to_perform = next(a for a in available_actions if a['action'] == 'call')['amount']
        elif can_check: action_to_perform = PlayerAction.CHECK
        else: action_to_perform = PlayerAction.FOLD

        if player.money <= amount_to_perform and action_to_perform in [PlayerAction.CALL, PlayerAction.RAISE]:
            action_to_perform = PlayerAction.ALL_IN 
        
        logger.info(f"AI {player.name} in room {room_code} chose: {action_to_perform.value} with amount {amount_to_perform}")
        self.player_action(room_code, player_id, action_to_perform, amount_to_perform if action_to_perform == PlayerAction.RAISE else (amount_to_perform if action_to_perform == PlayerAction.CALL else 0) )


    def player_action(self, room_code: str, player_id: str, action_type: PlayerAction, amount: int = 0) -> bool:
        room = self.rooms.get(room_code); player = room.players.get(player_id)
        if not room or not player: return False
        if room.current_player_id != player_id: 
            logger.warning(f"Action by {player.name} ({player_id}) but not their turn (current: {room.current_player_id})")
            return False
        if not player.can_act() and action_type not in [PlayerAction.SIT_OUT, PlayerAction.SIT_IN]: 
            logger.warning(f"Player {player.name} ({player_id}) cannot act (status: {player.status}, money: {player.money})")
            return False

        success = self.process_player_action(room, player, action_type, amount)
        if success:
            player.last_action = action_type
            player.last_action_time = time.time()
            room.last_action_timestamp = time.time()
            
            action_amount_this_turn = 0
            if action_type == PlayerAction.RAISE: 
                action_amount_this_turn = amount # This 'amount' is the raise amount on top of call
            elif action_type == PlayerAction.CALL: 
                # Calculate the actual amount called this turn
                amount_needed_to_call = room.current_bet_to_match - (player.total_bet_this_hand - player.current_bet)
                action_amount_this_turn = min(amount_needed_to_call, player.money + (player.current_bet - (player.total_bet_this_hand-player.current_bet))) # Bit convoluted, simpler if amount passed for call
            elif action_type == PlayerAction.ALL_IN: 
                action_amount_this_turn = player.current_bet - (player.total_bet_this_hand - player.current_bet) # Total put in this round, less what was already in total
                # Or more simply, the amount of money they had when they went all-in (which is now 0)
                # This relies on process_player_action having updated current_bet correctly.

            player.last_action_amount = action_amount_this_turn
            
            player.actions_this_hand.append({"action": action_type.value, "amount": action_amount_this_turn, "total_bet_this_round": player.current_bet, "phase": room.phase.value})

            if room.phase == GamePhase.PRE_FLOP:
                if action_type in [PlayerAction.CALL, PlayerAction.RAISE, PlayerAction.ALL_IN]:
                    # VPIP needs one action per hand, not per betting round if already VPIP'd
                    # This is simplified. A better VPIP only counts first voluntary action.
                    player.stats.vpip = (player.stats.vpip * player.stats.hands_played + 1) / (player.stats.hands_played + 1 if player.stats.hands_played > 0 else 1)
                    if action_type == PlayerAction.RAISE:
                         player.stats.pfr = (player.stats.pfr * player.stats.hands_played + 1) / (player.stats.hands_played + 1 if player.stats.hands_played > 0 else 1)
            if action_type not in [PlayerAction.SIT_OUT, PlayerAction.SIT_IN] :
                 player.stats.hands_played +=1 # Increment only if it's a game action.
            self.advance_game_flow(room_code)
        else:
            logger.warning(f"Player action {action_type.value} by {player.name} failed processing.")
        return success

    def process_player_action(self, room: Room, player: Player, action: PlayerAction, amount: int) -> bool:
        bet_amount_for_this_action = 0 # This is the money moved from player.money in this specific action
        
        if action == PlayerAction.FOLD: 
            player.status = PlayerStatus.FOLDED
            return True
            
        if action == PlayerAction.CHECK: 
            if player.current_bet < room.current_bet_to_match:
                logger.warning(f"{player.name} cannot CHECK. Bet to match: {room.current_bet_to_match}, player's bet: {player.current_bet}")
                return False
            return True
            
        if action == PlayerAction.CALL:
            amount_to_call_this_turn = room.current_bet_to_match - player.current_bet
            if amount_to_call_this_turn <= 0: # Trying to call when no bet to call, or already called. Treat as check.
                return player.current_bet >= room.current_bet_to_match 

            bet_amount_for_this_action = min(amount_to_call_this_turn, player.money)
            
            player.money -= bet_amount_for_this_action
            player.current_bet += bet_amount_for_this_action
            player.total_bet_this_hand += bet_amount_for_this_action
            room.pot += bet_amount_for_this_action
            
            if player.money == 0: player.status = PlayerStatus.ALL_IN
            return True
            
        if action == PlayerAction.RAISE:
            # `amount` is the raise ON TOP OF a call.
            # Player must at least call the current_bet_to_match.
            amount_to_call_this_turn = room.current_bet_to_match - player.current_bet
            
            total_additional_money_this_action = amount_to_call_this_turn + amount 
            
            if amount <= 0: return False # Raise amount (on top of call) must be positive
            if total_additional_money_this_action > player.money: # Cannot bet more than they have
                logger.warning(f"{player.name} cannot RAISE. Bet amount: {total_additional_money_this_action}, Player money: {player.money}")
                return False
            
            # A raise must be at least room.min_raise_amount, unless it's an all-in raise.
            # `amount` is the raise amount itself (on top of call).
            if amount < room.min_raise_amount and (player.money > total_additional_money_this_action): # Not all-in and raise amount is too small
                logger.warning(f"{player.name} RAISE too small. Amount: {amount}, MinRaise: {room.min_raise_amount}")
                return False

            bet_amount_for_this_action = total_additional_money_this_action
            player.money -= bet_amount_for_this_action
            player.current_bet += bet_amount_for_this_action 
            player.total_bet_this_hand += bet_amount_for_this_action
            room.pot += bet_amount_for_this_action
            
            # Update room's betting state
            # If not all-in, this raise sets new min_raise_amount for others
            if player.money > 0 : 
                 room.min_raise_amount = amount # The 'amount' IS the raise size on top of call
            
            room.current_bet_to_match = player.current_bet # New target for others
            
            if player.money == 0: player.status = PlayerStatus.ALL_IN
            return True
            
        if action == PlayerAction.ALL_IN:
            if player.money <= 0: return False # Already all-in or no money
            
            bet_amount_for_this_action = player.money # They are betting all their remaining money
            
            player.money = 0
            player.current_bet += bet_amount_for_this_action
            player.total_bet_this_hand += bet_amount_for_this_action
            room.pot += bet_amount_for_this_action
            player.status = PlayerStatus.ALL_IN
            
            # If this all-in constitutes a raise
            if player.current_bet > room.current_bet_to_match:
                # This raise amount is player.current_bet - (original room.current_bet_to_match)
                # The amount they added BEYOND the previous current_bet_to_match
                actual_raise_size_this_action = player.current_bet - room.current_bet_to_match 
                if actual_raise_size_this_action >= room.min_raise_amount: # if it's a "full" raise
                     room.min_raise_amount = actual_raise_size_this_action
                room.current_bet_to_match = player.current_bet # This is the new amount to match
            return True
            
        if action == PlayerAction.SIT_OUT:
            player.status = PlayerStatus.SITTING_OUT
            if room.phase != GamePhase.WAITING: player.status = PlayerStatus.FOLDED
            return True
        if action == PlayerAction.SIT_IN:
            if player.status == PlayerStatus.SITTING_OUT: player.status = PlayerStatus.ACTIVE; return True
            return False
        return False

    def advance_game_flow(self, room_code: str):
        room = self.rooms.get(room_code);
        if not room: return

        active_players_in_hand = room.get_active_players_in_hand()
        if len(active_players_in_hand) <= 1:
            if room.phase not in [GamePhase.SHOWDOWN, GamePhase.GAME_OVER] :
                logger.info(f"Room {room.code}: Hand ending early, active players <=1. Num active: {len(active_players_in_hand)}")
                if len(active_players_in_hand) == 1 and room.phase != GamePhase.RIVER: 
                    winner = active_players_in_hand[0]
                    total_pot_won = room.pot # Assuming simple pot for now. Side pots handled in end_hand.
                    winner.money += total_pot_won
                    winner.stats.total_winnings += total_pot_won
                    winner.stats.hands_won +=1
                    if total_pot_won > winner.stats.biggest_pot: winner.stats.biggest_pot = total_pot_won
                    if total_pot_won > self.global_stats['biggest_pot']: self.global_stats['biggest_pot'] = total_pot_won
                    logger.info(f"{winner.name} wins ${total_pot_won} as last player.")
                    room.pot = 0 
                    self.save_hand_history(room, {winner.id: {"amount_won": total_pot_won, "hand_description":"Won by default"}})
                    asyncio.create_task(self.prepare_next_hand(room_code))
                    return
                else: 
                     logger.info(f"Room {room.code}: Conditions met to proceed to showdown or already there.")
                     room.phase = GamePhase.SHOWDOWN
                     self.end_hand(room_code) 
                     return
        
        all_bets_matched = True
        num_active_non_all_in = 0
        player_who_needs_to_act_found = False

        for p_id_check in room._player_order_for_hand:
            p_check = room.players.get(p_id_check)
            if p_check and p_check.status == PlayerStatus.ACTIVE and not p_check.is_all_in_for_hand():
                num_active_non_all_in += 1
                if p_check.current_bet < room.current_bet_to_match:
                    all_bets_matched = False
                    break 
                if room.phase == GamePhase.PRE_FLOP and p_check.is_big_blind and \
                   p_check.current_bet == room.settings.big_blind and \
                   room.current_bet_to_match == room.settings.big_blind and \
                   p_check.last_action is None: 
                    all_bets_matched = False 
                    break
        
        if all_bets_matched and num_active_non_all_in > 0:
            # Check if the player who is supposed to act next (if any) has already acted at this betting level.
            # This means action has completed around the table.
            # Example: P1 bets, P2 calls, P3 calls. P1's turn again. Action on P1 has completed the circle for this bet level.
            # If player whose turn it would be (e.g. room.current_player_id if it was just passed to them)
            # has current_bet == room.current_bet_to_match and has already acted this round (last_action not None)
            # OR if BB pre-flop and it's checked to them.
            
            # Simpler check: If all_bets_matched is true, AND the current_player_id is the one who
            # made the last raise (or BB in pre-flop if checked around), the round is over.
            # This is complex. Let's use: if all bets matched, and number of active players > 0, it means betting is closed for this round.
            logger.info(f"Room {room.code}: Betting round complete. All bets matched. Advancing phase.")
            self.advance_phase(room_code)
            return
        elif num_active_non_all_in == 0 and len(active_players_in_hand) > 1: # All remaining are all-in
             logger.info(f"Room {room.code}: All remaining players are all-in. Advancing phase.")
             self.advance_phase(room_code) 
             return

        # If betting not complete, find next player
        next_player_id = room.get_player_acting_next(room.current_player_id if room.current_player_id else room.dealer_player_id) # Fallback to dealer if current is None
        
        if next_player_id:
            room.current_player_id = next_player_id
            logger.info(f"Room {room.code}: Next player is {room.current_player_id}")
            if room.players[next_player_id].is_ai:
                asyncio.create_task(self.ai_perform_action(room_code, next_player_id))
        else: # No one can act, but betting wasn't closed by all_bets_matched. Could be all folded/all-in now.
            logger.info(f"Room {room.code}: No player found to act next, but all_bets_matched was false or num_active_non_all_in was 0. Advancing phase (likely showdown).")
            self.advance_phase(room_code) # This should lead to showdown or hand end.
            return
        
        room.last_action_timestamp = time.time()


    def advance_phase(self, room_code: str):
        room = self.rooms.get(room_code)
        if not room: return

        active_players_in_hand = room.get_active_players_in_hand()
        if len(active_players_in_hand) <= 1 and room.phase not in [GamePhase.SHOWDOWN, GamePhase.GAME_OVER]:
            if room.phase != GamePhase.GAME_OVER:
                logger.info(f"Room {room.code}: Advancing phase, but only {len(active_players_in_hand)} player(s) left. Ending hand.")
                self.end_hand(room_code)
            return

        for player in room.players.values():
            player.current_bet = 0 
            player.last_action = None 
            player.last_action_amount = 0
        
        room.current_bet_to_match = 0
        room.min_raise_amount = room.settings.big_blind 
        
        current_phase = room.phase
        next_phase = None

        if current_phase == GamePhase.PRE_FLOP: next_phase = GamePhase.FLOP; room.deal_community_cards(3)
        elif current_phase == GamePhase.FLOP: next_phase = GamePhase.TURN; room.deal_community_cards(1)
        elif current_phase == GamePhase.TURN: next_phase = GamePhase.RIVER; room.deal_community_cards(1)
        elif current_phase == GamePhase.RIVER: next_phase = GamePhase.SHOWDOWN
        elif current_phase == GamePhase.SHOWDOWN: 
             asyncio.create_task(self.prepare_next_hand(room_code))
             return
        else: logger.warning(f"Room {room.code}: Advance_phase called from unexpected phase: {current_phase}"); return

        if next_phase:
            room.phase = next_phase
            logger.info(f"Room {room.code}: Advanced to phase {room.phase.value}. Community: {[str(c) for c in room.community_cards]}")

            if next_phase == GamePhase.SHOWDOWN:
                self.end_hand(room_code)
                return

            # Determine first player to act post-flop (or pre-flop handled in start_game)
            # Post-flop, action starts with first active player left of dealer.
            # _player_order_for_hand is [PlayerLeftOfDealer, ..., Dealer] for 3+ players
            # For HU, _player_order_for_hand is [SB(Dealer), BB(Other)] pre-flop. Post-flop, BB(Other) is first.
            first_to_act_this_round_id = None
            if room._player_order_for_hand:
                if len(room._player_order_for_hand) == 2 and room.phase != GamePhase.PRE_FLOP: # HU Post-flop
                    # Player who is NOT the dealer (SB) acts first post-flop.
                    # _player_order_for_hand is [SB, BB]. BB (index 1) acts first.
                    bb_player_id = room._player_order_for_hand[1]
                    if room.players[bb_player_id].status == PlayerStatus.ACTIVE and not room.players[bb_player_id].is_all_in_for_hand():
                        first_to_act_this_round_id = bb_player_id
                    elif room.players[room._player_order_for_hand[0]].status == PlayerStatus.ACTIVE and not room.players[room._player_order_for_hand[0]].is_all_in_for_hand(): # If BB folded/all-in, SB acts
                        first_to_act_this_round_id = room._player_order_for_hand[0]

                else: # 3+ players or Pre-flop (pre-flop first actor already set by start_game)
                    for p_id in room._player_order_for_hand: # Iterate in defined action order
                        player = room.players.get(p_id)
                        if player and player.status == PlayerStatus.ACTIVE and not player.is_all_in_for_hand():
                            first_to_act_this_round_id = player.id
                            break
            
            room.current_player_id = first_to_act_this_round_id
            
            if not room.current_player_id and len(active_players_in_hand) > 1:
                logger.info(f"Room {room.code}: All remaining players are all-in at start of {room.phase.value}. Fast-forwarding.")
                if room.phase != GamePhase.SHOWDOWN:
                     self.advance_phase(room_code) 
                return

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
        if room.phase != GamePhase.SHOWDOWN : room.phase = GamePhase.SHOWDOWN

        players_in_showdown = [p for p in room.get_players_eligible_for_pot() if p.status != PlayerStatus.FOLDED]
        evaluated_hands = {}
        if len(players_in_showdown) > 0 :
            for player in players_in_showdown:
                if player.cards:
                    combined_cards = player.cards + room.community_cards
                    evaluated_hands[player.id] = self.evaluate_hand(combined_cards)
                    logger.info(f"Player {player.name} hand: {[str(c) for c in player.cards]}, eval: {evaluated_hands[player.id].description}")
        
        room.calculate_side_pots()
        all_winners_info = {}

        if not room.side_pots and room.pot > 0 :
             eligible_players = {p.id for p in players_in_showdown}
             if eligible_players:
                room.side_pots.append(SidePot(amount=room.pot, eligible_players=eligible_players))

        for i, pot_info in enumerate(room.side_pots):
            logger.info(f"Distributing Pot #{i}: Amount: {pot_info.amount}, Eligible: {pot_info.eligible_players}")
            eligible_winners_for_this_pot = {pid: evaluated_hands[pid] for pid in pot_info.eligible_players if pid in evaluated_hands}

            if not eligible_winners_for_this_pot:
                non_folded_eligibles = [p_id for p_id in pot_info.eligible_players if room.players[p_id].status != PlayerStatus.FOLDED]
                if len(non_folded_eligibles) == 1:
                    winner_id = non_folded_eligibles[0]; winner_player = room.players.get(winner_id)
                    logger.info(f"Side Pot #{i} (uncontested): Player {winner_player.name} wins ${pot_info.amount}.")
                    winner_player.money += pot_info.amount
                    pot_info.winner_ids = [winner_id]; pot_info.winning_hand_description = "Uncontested"
                    if winner_id not in all_winners_info: all_winners_info[winner_id] = {"amount_won":0, "hand_description": "Won by default"}
                    all_winners_info[winner_id]["amount_won"] += pot_info.amount
                elif len(non_folded_eligibles) > 1: logger.error(f"Side Pot #{i}: Multiple non-folded eligibles but no evaluated hands. Pot: {pot_info.amount}, Eligibles: {non_folded_eligibles}")
                else: logger.error(f"Side Pot #{i}: All eligible players folded. Pot: {pot_info.amount}, Eligible Original: {pot_info.eligible_players}")
                continue

            best_hand_val = max(eligible_winners_for_this_pot.values(), key=lambda h: (h.rank, h.value))
            current_pot_winners_ids = [pid for pid, hand_eval in eligible_winners_for_this_pot.items() if hand_eval.rank == best_hand_val.rank and hand_eval.value == best_hand_val.value]
            pot_info.winner_ids = current_pot_winners_ids
            pot_info.winning_hand_description = best_hand_val.description

            if current_pot_winners_ids:
                winnings_per_winner = pot_info.amount // len(current_pot_winners_ids)
                remainder = pot_info.amount % len(current_pot_winners_ids)
                for idx, winner_id in enumerate(current_pot_winners_ids):
                    player_wins = winnings_per_winner + (1 if idx < remainder else 0)
                    room.players[winner_id].money += player_wins
                    if winner_id not in all_winners_info: all_winners_info[winner_id] = {"amount_won":0, "hand_description": best_hand_val.description}
                    all_winners_info[winner_id]["amount_won"] += player_wins
                    logger.info(f"Side Pot #{i}: Player {room.players[winner_id].name} wins ${player_wins} with {best_hand_val.description}")
            else: logger.error(f"Side Pot #{i}: No winners for pot {pot_info.amount} among {eligible_winners_for_this_pot.keys()}")
        room.pot = 0

        for p_id, win_info in all_winners_info.items():
            player = room.players[p_id]
            player.stats.total_winnings += win_info["amount_won"]
            player.stats.hands_won += 1
            if win_info["amount_won"] > player.stats.biggest_pot: player.stats.biggest_pot = win_info["amount_won"]
            if win_info["amount_won"] > self.global_stats['biggest_pot']: self.global_stats['biggest_pot'] = win_info["amount_won"]

        self.save_hand_history(room, all_winners_info)
        if room.settings.game_mode == GameMode.TOURNAMENT: self.update_tournament_state(room)
        asyncio.create_task(self.prepare_next_hand(room_code))

    async def prepare_next_hand(self, room_code: str, delay: int = 7):
        room = self.rooms.get(room_code); 
        if not room: return
        await asyncio.sleep(delay)
        if room_code not in self.rooms: return
        
        room.community_cards = []; room.side_pots = []
        active_players_for_game = [p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED and p.money > 0]
        
        if room.settings.game_mode == GameMode.TOURNAMENT and len(active_players_for_game) <= 1:
            room.phase = GamePhase.GAME_OVER; logger.info(f"Room {room_code}: Tournament ended."); return
        
        room.phase = GamePhase.WAITING
        if len(active_players_for_game) >= room.settings.min_players:
            logger.info(f"Room {room.code}: Auto starting next hand.")
            self.start_game(room_code)
        else: logger.info(f"Room {room.code}: Waiting for players. Need {room.settings.min_players}, have {len(active_players_for_game)}.")

    def evaluate_hand(self, cards: List[Card]) -> HandEvaluation:
        card_key = tuple(sorted((c.rank, c.suit) for c in cards))
        if card_key in self.hand_evaluation_cache: return self.hand_evaluation_cache[card_key]
        eval_result = self.full_hand_evaluation(cards)
        if len(self.hand_evaluation_cache) < HAND_EVALUATION_CACHE_SIZE: self.hand_evaluation_cache[card_key] = eval_result
        return eval_result

    def full_hand_evaluation(self, all_cards: List[Card]) -> HandEvaluation:
        from itertools import combinations
        if len(all_cards) < 5: return HandEvaluation(HandRank.HIGH_CARD, 0, [], "Invalid hand (<5 cards)")
        best_hand_rank = HandRank.HIGH_CARD; best_hand_value = 0; best_combo_cards = []; best_kickers_values = []
        for combo in combinations(all_cards, 5):
            current_rank, current_value, kicker_values, combo_sorted = self.evaluate_5_card_hand(list(combo))
            if current_rank > best_hand_rank or (current_rank == best_hand_rank and current_value > best_hand_value):
                best_hand_rank, best_hand_value, best_combo_cards, best_kickers_values = current_rank, current_value, combo_sorted, kicker_values
        return HandEvaluation(rank=best_hand_rank, value=best_hand_value, cards_used=best_combo_cards, description=self.get_hand_description(best_hand_rank, best_kickers_values or [c.value() for c in best_combo_cards]), kickers=best_kickers_values)

    def evaluate_5_card_hand(self, five_cards: List[Card]) -> Tuple[HandRank, int, List[int], List[Card]]:
        def card_val(c: Card, ace_low=False): return 1 if c.rank == 'A' and ace_low else (14 if c.rank == 'A' else (13 if c.rank == 'K' else (12 if c.rank == 'Q' else (11 if c.rank == 'J' else int(c.rank)))))
        sorted_cards = sorted(five_cards, key=lambda c: card_val(c), reverse=True)
        values = [card_val(c) for c in sorted_cards]
        suits = [c.suit for c in sorted_cards]
        is_flush = len(set(suits)) == 1
        is_straight = False
        unique_vals_desc = sorted(list(set(values)), reverse=True)
        if len(unique_vals_desc) == 5:
            if (values[0] - values[4] == 4): is_straight = True
            elif values == [14, 5, 4, 3, 2]: is_straight = True # Wheel A-5
        
        val_counts = Counter(values)
        sorted_counts = sorted(val_counts.items(), key=lambda item: (item[1], item[0]), reverse=True)
        
        # Rank determination logic (simplified structure for brevity)
        if is_straight and is_flush:
            sflush_vals = [5,4,3,2,1] if values == [14,5,4,3,2] else values
            rank = HandRank.ROYAL_FLUSH if sflush_vals == [14,13,12,11,10] else HandRank.STRAIGHT_FLUSH
            return rank, self._calculate_hand_strength_value(rank, sflush_vals), sflush_vals, sorted_cards
        if sorted_counts[0][1] == 4: # Quads
            quad_val, kicker_val = sorted_counts[0][0], sorted_counts[1][0]
            return HandRank.FOUR_OF_A_KIND, self._calculate_hand_strength_value(HandRank.FOUR_OF_A_KIND, [quad_val, kicker_val]), [quad_val, kicker_val], sorted_cards
        if sorted_counts[0][1] == 3 and sorted_counts[1][1] == 2: # Full House
            trip_val, pair_val = sorted_counts[0][0], sorted_counts[1][0]
            return HandRank.FULL_HOUSE, self._calculate_hand_strength_value(HandRank.FULL_HOUSE, [trip_val, pair_val]), [trip_val, pair_val], sorted_cards
        if is_flush: return HandRank.FLUSH, self._calculate_hand_strength_value(HandRank.FLUSH, values), values, sorted_cards
        if is_straight:
            straight_vals = [5,4,3,2,1] if values == [14,5,4,3,2] else values
            return HandRank.STRAIGHT, self._calculate_hand_strength_value(HandRank.STRAIGHT, straight_vals), straight_vals, sorted_cards
        if sorted_counts[0][1] == 3: # Trips
            trip_val, k1, k2 = sorted_counts[0][0], sorted_counts[1][0], sorted_counts[2][0]
            return HandRank.THREE_OF_A_KIND, self._calculate_hand_strength_value(HandRank.THREE_OF_A_KIND, [trip_val, k1, k2]), [trip_val, k1, k2], sorted_cards
        if sorted_counts[0][1] == 2 and sorted_counts[1][1] == 2: # Two Pair
            p1, p2, k = sorted_counts[0][0], sorted_counts[1][0], sorted_counts[2][0]
            return HandRank.TWO_PAIR, self._calculate_hand_strength_value(HandRank.TWO_PAIR, [p1,p2,k]), [p1,p2,k], sorted_cards
        if sorted_counts[0][1] == 2: # Pair
            pair_v, k1, k2, k3 = sorted_counts[0][0], sorted_counts[1][0], sorted_counts[2][0], sorted_counts[3][0]
            return HandRank.PAIR, self._calculate_hand_strength_value(HandRank.PAIR, [pair_v,k1,k2,k3]), [pair_v,k1,k2,k3], sorted_cards
        return HandRank.HIGH_CARD, self._calculate_hand_strength_value(HandRank.HIGH_CARD, values), values, sorted_cards

    def _calculate_hand_strength_value(self, rank: HandRank, card_values: List[int]) -> int:
        value = int(rank) * (10**10); multiplier = 10**8
        for i, val in enumerate(card_values):
            if i < 5 : value += val * multiplier; multiplier //= 100
        return value

    def get_hand_description(self, rank: HandRank, kicker_values: List[int]) -> str:
        def name(v): return 'Ace' if v==14 else ('King' if v==13 else ('Queen' if v==12 else ('Jack' if v==11 else ('Ace (Low)' if v==1 else str(v)))))
        if not kicker_values: return rank.name.replace('_',' ')
        if rank == HandRank.ROYAL_FLUSH: return "Royal Flush"
        if rank == HandRank.STRAIGHT_FLUSH: return f"Straight Flush, {name(kicker_values[0])} high"
        if rank == HandRank.FOUR_OF_A_KIND: return f"Four of a Kind, {name(kicker_values[0])}s, {name(kicker_values[1])} kicker"
        if rank == HandRank.FULL_HOUSE: return f"Full House, {name(kicker_values[0])}s full of {name(kicker_values[1])}s"
        if rank == HandRank.FLUSH: return f"Flush, {name(kicker_values[0])} high ({', '.join(map(name, kicker_values[1:]))})"
        if rank == HandRank.STRAIGHT: return f"Straight, {name(kicker_values[0])} high"
        if rank == HandRank.THREE_OF_A_KIND: return f"Three of a Kind, {name(kicker_values[0])}s ({name(kicker_values[1])}, {name(kicker_values[2])})"
        if rank == HandRank.TWO_PAIR: return f"Two Pair, {name(kicker_values[0])}s and {name(kicker_values[1])}s ({name(kicker_values[2])} kicker)"
        if rank == HandRank.PAIR: return f"Pair of {name(kicker_values[0])}s ({', '.join(map(name, kicker_values[1:4]))})"
        if rank == HandRank.HIGH_CARD: return f"High Card {name(kicker_values[0])} ({', '.join(map(name, kicker_values[1:]))})"
        return rank.name.replace('_',' ')

    def save_hand_history(self, room: Room, winners_info: Dict[str, Dict]):
        hand_data = {'hand_number': room.hand_number, 'timestamp': datetime.now().isoformat(), 'players': [], 'community_cards': [{'suit': c.suit, 'rank': c.rank, "id": c.id} for c in room.community_cards], 'total_pot_distributed': sum(pot.amount for pot in room.side_pots), 'side_pots_details': [{"amount": sp.amount, "eligible_players": list(sp.eligible_players), "winner_ids": sp.winner_ids, "winning_hand_description": sp.winning_hand_description} for sp in room.side_pots], 'winners': winners_info}
        for p_id, player in room.players.items():
            p_detail = {'id': player.id, 'name': player.name, 'initial_money': player.money - winners_info.get(p_id, {}).get("amount_won", 0) + player.total_bet_this_hand, 'final_money': player.money, 'cards': [{'suit': c.suit, 'rank': c.rank, "id": c.id} for c in player.cards] if player.cards else [], 'actions': player.actions_this_hand, 'total_bet_this_hand': player.total_bet_this_hand, 'status_at_end': player.status.value}
            if p_id in winners_info: p_detail['amount_won'] = winners_info[p_id]["amount_won"]; p_detail['hand_description'] = winners_info[p_id]["hand_description"]
            hand_data['players'].append(p_detail)
        room.hand_history.append(hand_data)
        if len(room.hand_history) > 50: room.hand_history = room.hand_history[-50:]
        logger.info(f"Room {room.code}: Hand #{room.hand_number} history saved.")

    def update_tournament_state(self, room: Room):
        if room.settings.game_mode != GameMode.TOURNAMENT: return
        eliminated_this_hand = []
        for p_id, player in room.players.items():
            if player.money <= 0 and player.status != PlayerStatus.ELIMINATED:
                player.status = PlayerStatus.ELIMINATED
                num_eliminated = sum(1 for p in room.players.values() if p.tournament_rank > 0)
                player.tournament_rank = len(room.players) - num_eliminated
                eliminated_this_hand.append(player.name)
        if eliminated_this_hand: logger.info(f"Tournament {room.code}: Eliminated: {', '.join(eliminated_this_hand)}")
        
        if datetime.now() >= room.tournament_next_blind_increase:
            room.tournament_level += 1
            room.settings.small_blind = int(room.settings.small_blind * 1.5)
            room.settings.big_blind = int(room.settings.big_blind * 1.5)
            if room.settings.ante > 0: room.settings.ante = int(room.settings.ante * 1.5) if room.settings.ante > 0 else max(1, int(room.settings.small_blind * 0.1))
            room.tournament_next_blind_increase = datetime.now() + timedelta(seconds=TOURNAMENT_BLIND_INCREASE_INTERVAL)
            logger.info(f"Tournament {room.code}: Level {room.tournament_level}. Blinds: {room.settings.small_blind}/{room.settings.big_blind}, Ante: {room.settings.ante}")
            if room.tournament_level % 5 == 0:
                room.phase = GamePhase.TOURNAMENT_BREAK; room.paused = True; room.pause_reason = f"Tournament Break ({(TOURNAMENT_BLIND_INCREASE_INTERVAL // 60) // 5} min)"
                asyncio.create_task(self.resume_tournament_after_break(room.code, 300))

    async def resume_tournament_after_break(self, room_code: str, break_duration_seconds: int):
        await asyncio.sleep(break_duration_seconds)
        room = self.rooms.get(room_code)
        if room and room.paused and room.phase == GamePhase.TOURNAMENT_BREAK:
            room.paused = False
            room.pause_reason = ""
            room.phase = GamePhase.WAITING # Will trigger start_game if conditions met
            logger.info(f"Tournament {room_code}: Break ended. Resuming game.")
            # Game loop will pick up and broadcast new state, potentially start next hand

    def get_game_state(self, room_code: str, for_player_id: str) -> dict:
        room = self.rooms.get(room_code);
        if not room: return {}
        is_player_in_game = for_player_id in room.players and not room.players[for_player_id].is_ai
        is_spectator = for_player_id in room.spectators
        current_player_obj = room.players.get(room.current_player_id) if room.current_player_id else None
        players_data = {}
        for p_id, p_obj in room.players.items():
            player_data = {"id": p_obj.id, "name": p_obj.name, "money": p_obj.money, "current_bet": p_obj.current_bet, "total_bet_this_hand": p_obj.total_bet_this_hand, "status": p_obj.status.value, "last_action": p_obj.last_action.value if p_obj.last_action else None, "last_action_amount": p_obj.last_action_amount, "avatar": p_obj.avatar, "color": p_obj.color, "is_dealer": p_obj.is_dealer, "is_small_blind": p_obj.is_small_blind, "is_big_blind": p_obj.is_big_blind, "time_bank": p_obj.time_bank, "is_current_player": current_player_obj and current_player_obj.id == p_id, "tournament_rank": p_obj.tournament_rank, "is_ai": p_obj.is_ai, "stats": asdict(p_obj.stats)}
            show_cards = (p_id == for_player_id or (room.phase == GamePhase.SHOWDOWN and p_obj.status != PlayerStatus.FOLDED) or (is_spectator and room.phase == GamePhase.SHOWDOWN and p_obj.status != PlayerStatus.FOLDED))
            if show_cards and p_obj.cards: player_data["cards"] = [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in p_obj.cards]
            elif p_obj.cards: player_data["cards"] = [{"suit": "back", "rank": "back", "id": f"back_{i}_{p_id}"} for i in range(len(p_obj.cards))]
            else: player_data["cards"] = []
            players_data[p_id] = player_data
        
        game_state = {"room_code": room.code, "room_name": room.name, "phase": room.phase.value, "pot": room.pot, "current_bet_to_match": room.current_bet_to_match, "min_raise_amount": room.min_raise_amount, "current_player_id": room.current_player_id, "dealer_player_id": room.dealer_player_id, "players": players_data, "community_cards": [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in room.community_cards], "chat_messages": room.chat_messages[-30:], "is_player_in_game": is_player_in_game, "is_spectator": is_spectator, "spectator_count": len(room.spectators), "hand_number": room.hand_number, "settings": {"small_blind": room.settings.small_blind, "big_blind": room.settings.big_blind, "ante": room.settings.ante, "max_players": room.settings.max_players, "game_mode": room.settings.game_mode.value, "auto_fold_timeout": room.settings.auto_fold_timeout, "ai_players": room.settings.ai_players}, "tournament_info": {"level": room.tournament_level, "next_blind_increase_time": room.tournament_next_blind_increase.isoformat()} if room.settings.game_mode == GameMode.TOURNAMENT else None, "side_pots": [{"amount": sp.amount, "eligible_players_count": len(sp.eligible_players), "winner_ids": sp.winner_ids, "winning_hand": sp.winning_hand_description} for sp in room.side_pots], "paused": room.paused, "pause_reason": room.pause_reason, "time_left_for_action": max(0, room.settings.auto_fold_timeout - (time.time() - room.last_action_timestamp)) if current_player_obj else 0, "can_act": is_player_in_game and current_player_obj and current_player_obj.id == for_player_id and room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER, GamePhase.TOURNAMENT_BREAK], "available_actions": self.get_available_actions(room, for_player_id) if is_player_in_game else []}
        return game_state

    def get_available_actions(self, room: Room, player_id: str) -> List[Dict]:
        player = room.players.get(player_id)
        if not player or not player.can_act() or room.current_player_id != player_id : return []
        actions = [{"action": PlayerAction.FOLD.value, "label": "Fold"}]
        amount_to_call = room.current_bet_to_match - player.current_bet
        if amount_to_call <= 0: actions.append({"action": PlayerAction.CHECK.value, "label": "Check"})
        else: actions.append({"action": PlayerAction.CALL.value, "label": f"Call ${min(amount_to_call, player.money)}", "amount": min(amount_to_call, player.money)})
        
        money_after_call = player.money - (amount_to_call if amount_to_call > 0 else 0)
        if money_after_call > 0 :
            min_possible_raise_value = room.min_raise_amount # This is the raise *amount* (on top of call)
            max_possible_raise_value = money_after_call # Can raise up to all remaining chips
            if max_possible_raise_value >= min_possible_raise_value :
                actions.append({"action": PlayerAction.RAISE.value, "label": "Raise", "min_amount": min_possible_raise_value, "max_amount": max_possible_raise_value})
        if player.money > 0: actions.append({"action": PlayerAction.ALL_IN.value, "label": f"All-In ${player.money}", "amount": player.money})
        return actions

    def add_chat_message(self, room_code: str, player_id: str, message_text: str):
        room = self.rooms.get(room_code)
        if not room: return
        player = room.players.get(player_id)
        player_name = player.name if player else "Spectator"
        player_color = player.color if player else "#cccccc"
        
        chat_msg = {
            "player_id": player_id,
            "player_name": player_name,
            "player_color": player_color,
            "message": message_text[:200], # Max length
            "timestamp": time.time(),
            "formatted_time": datetime.now().strftime("%H:%M:%S")
        }
        room.chat_messages.append(chat_msg)
        if len(room.chat_messages) > MAX_CHAT_MESSAGES:
            room.chat_messages = room.chat_messages[-MAX_CHAT_MESSAGES:]
        logger.info(f"Chat in {room_code} by {player_name}: {message_text}")
        room.update_activity()

    def check_rate_limit(self, client_id: str, type: str = "message") -> bool:
        limit_dict = self.rate_limits if type == "message" else self.action_rate_limits
        max_per_second = RATE_LIMIT_MESSAGES_PER_SECOND if type == "message" else RATE_LIMIT_ACTIONS_PER_SECOND
        
        current_time = time.time()
        if client_id not in limit_dict:
            limit_dict[client_id] = [current_time]
            return True
        
        # Remove timestamps older than 1 second
        limit_dict[client_id] = [t for t in limit_dict[client_id] if current_time - t <= 1]
        
        if len(limit_dict[client_id]) < max_per_second:
            limit_dict[client_id].append(current_time)
            return True
        else:
            logger.warning(f"Rate limit exceeded for {client_id} (type: {type})")
            return False

# Global game instance
game = AdvancedPokerGame()

# WebSocket message models
class WSMessage(BaseModel):
    action: str
    payload: dict = PydanticField(default_factory=dict)

class CreateRoomPayload(BaseModel):
    player_name: str = "Anonymous"
    room_name: Optional[str] = None
    game_mode: str = GameMode.CASH_GAME.value
    small_blind: int = SMALL_BLIND
    big_blind: int = BIG_BLIND
    max_players: int = MAX_PLAYERS_PER_ROOM
    buy_in: int = 0
    password: Optional[str] = None
    ai_players: int = 0

async def game_loop():
    while game.running:
        start_time = time.perf_counter()
        try:
            current_time = time.time()
            for room_code, room in list(game.rooms.items()):
                if room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER, GamePhase.TOURNAMENT_BREAK] and not room.paused:
                    if room.current_player_id:
                        current_player = room.players.get(room.current_player_id)
                        if current_player and not current_player.is_ai:
                            if current_time - room.last_action_timestamp > room.settings.auto_fold_timeout:
                                logger.info(f"Auto-folding player {current_player.name} in room {room_code} due to timeout.")
                                game.player_action(room_code, current_player.id, PlayerAction.FOLD)
            
            for room_code, room in list(game.rooms.items()):
                user_ids_in_room = set()
                for p_id, player_obj in room.players.items():
                    if not player_obj.is_ai and player_obj.connection_id: user_ids_in_room.add(player_obj.connection_id)
                user_ids_in_room.update(room.spectators)
                if not user_ids_in_room: continue

                connections_to_broadcast = []
                for user_id in list(user_ids_in_room):
                    ws_conn = game.connections.get(user_id)
                    if ws_conn: connections_to_broadcast.append((user_id, ws_conn))
                    else: 
                        logger.warning(f"User {user_id} in room {room_code} but no WebSocket. Cleaning.")
                        game.leave_room(user_id, force=True)

                if connections_to_broadcast:
                    broadcast_tasks = []
                    for user_id, ws_conn in connections_to_broadcast:
                        try:
                            game_state_for_user = game.get_game_state(room_code, user_id)
                            broadcast_tasks.append(ws_conn.send_json({"type": "game_state", "data": game_state_for_user}))
                        except Exception as e: 
                            logger.error(f"Error preparing/sending game_state to {user_id} in {room_code}: {e}")
                    
                    if broadcast_tasks:
                        results = await asyncio.gather(*broadcast_tasks, return_exceptions=True)
                        for i, result in enumerate(results):
                            if isinstance(result, Exception):
                                user_id_failed, _ = connections_to_broadcast[i]
                                logger.error(f"Failed to broadcast to {user_id_failed}: {result}")
                                if user_id_failed in game.connections: del game.connections[user_id_failed]
                                game.leave_room(user_id_failed, force=True)
            
            elapsed_time = time.perf_counter() - start_time
            sleep_duration = max(0, (1.0 / GAME_UPDATE_RATE) - elapsed_time)
            await asyncio.sleep(sleep_duration)
        except Exception as e:
            logger.exception(f"Critical error in game_loop: {e}")
            await asyncio.sleep(1.0)

async def handle_websocket_message(websocket: WebSocket, player_id: str, message: WSMessage):
    action = message.action; payload_dict = message.payload
    try:
        if action == "create_room":
            try: create_payload = CreateRoomPayload(**payload_dict)
            except ValidationError as e: await websocket.send_json({"type": "error", "message": f"Invalid create room data: {e}"}); return
            game_settings = GameSettings(small_blind=create_payload.small_blind, big_blind=create_payload.big_blind, max_players=min(create_payload.max_players, MAX_PLAYERS_PER_ROOM), game_mode=GameMode(create_payload.game_mode), buy_in=create_payload.buy_in, password=create_payload.password if create_payload.password else None, ai_players=min(create_payload.ai_players, MAX_PLAYERS_PER_ROOM -1))
            room_code = game.create_room(player_id, game_settings, create_payload.room_name)
            if not room_code: await websocket.send_json({"type": "error", "message": "Failed to create room (server limit?)"}); return
            if game.join_room(room_code, player_id, create_payload.player_name):
                await websocket.send_json({"type": "room_created", "data": {"room_code": room_code, "room_name": game.rooms[room_code].name}})
            else: await websocket.send_json({"type": "error", "message": "Failed to join newly created room"})
        
        elif action == "join_room":
            if player_id in game.player_rooms: await websocket.send_json({"type": "error", "message": "Already in a room."}); return
            room_code = payload_dict.get("room_code")
            player_name = payload_dict.get("player_name", "Player")
            password = payload_dict.get("password")
            if game.join_room(room_code, player_id, player_name, password):
                await websocket.send_json({"type": "room_joined", "data": {"room_code": room_code}})
            else: await websocket.send_json({"type": "error", "message": "Failed to join room (invalid code, password, or full)."})

        elif action == "spectate_room":
            room_code = payload_dict.get("room_code")
            room = game.rooms.get(room_code)
            if room:
                room.spectators.add(player_id)
                game.player_rooms[player_id] = room_code # Associate spectator with room for disconnect handling
                await websocket.send_json({"type": "spectating", "data": {"room_code": room_code}})
                logger.info(f"Player {player_id} is now spectating room {room_code}")
            else: await websocket.send_json({"type": "error", "message": "Room not found."})
        
        elif action == "leave_room":
            game.leave_room(player_id)
            await websocket.send_json({"type": "room_left"}) # Client handles UI

        elif action == "start_game":
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]
                room = game.rooms.get(room_code)
                if room and room.owner_id == player_id : # Only owner can start (or add other conditions)
                    if game.start_game(room_code): pass # State update will show
                    else: await websocket.send_json({"type": "error", "message": "Cannot start game (not enough players?)."})
                else: await websocket.send_json({"type": "error", "message": "Only room owner can start game or room not found."})
        
        elif action == "player_action":
            if not game.check_rate_limit(player_id, "action"): await websocket.send_json({"type": "error", "message": "Action rate limit exceeded"}); return
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]
                action_type_str = payload_dict.get("action_type")
                amount = payload_dict.get("amount", 0)
                try:
                    poker_action_enum = PlayerAction(action_type_str)
                    if not game.player_action(room_code, player_id, poker_action_enum, amount):
                         await websocket.send_json({"type": "error", "message": "Invalid action or not your turn."})
                except ValueError: await websocket.send_json({"type": "error", "message": f"Invalid action type: {action_type_str}"})
            else: await websocket.send_json({"type": "error", "message": "Player not in a room."})

        elif action == "send_chat_message":
            if not game.check_rate_limit(player_id, "message"): await websocket.send_json({"type": "error", "message": "Chat rate limit exceeded"}); return
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]
                message_text = payload_dict.get("message")
                if message_text and 0 < len(message_text) <= 200:
                    game.add_chat_message(room_code, player_id, message_text)
                else: await websocket.send_json({"type": "error", "message": "Invalid chat message."})
        
        elif action == "get_room_list": # Request to get public rooms
            public_rooms = []
            for code, room_obj in game.rooms.items():
                if room_obj.room_type == RoomType.PUBLIC and room_obj.phase == GamePhase.WAITING: # Example filter
                    public_rooms.append({
                        "code": code,
                        "name": room_obj.name,
                        "players": len(room_obj.players),
                        "max_players": room_obj.settings.max_players,
                        "game_mode": room_obj.settings.game_mode.value,
                        "blinds": f"{room_obj.settings.small_blind}/{room_obj.settings.big_blind}"
                    })
            await websocket.send_json({"type": "room_list", "data": {"rooms": public_rooms}})

        elif action == "get_hand_history":
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]
                room = game.rooms.get(room_code)
                if room:
                    await websocket.send_json({"type": "hand_history", "data": {"history": room.hand_history[-10:]}}) # Send last 10
            
    except Exception as e:
        logger.exception(f"Error handling WebSocket message (action: {action}): {e}")
        try: await websocket.send_json({"type": "error", "message": "Server error processing request."})
        except: pass


# --- FastAPI App Setup ---
@asynccontextmanager
async def lifespan(app: FastAPI):
    # Startup
    asyncio.create_task(game_loop())
    # asyncio.create_task(game.cleanup_inactive_rooms_periodically()) # If you add a cleanup task
    logger.info("Advanced Poker Game Server Started")
    yield
    # Shutdown
    game.running = False
    logger.info("Advanced Poker Game Server Shutting Down")

app = FastAPI(lifespan=lifespan)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"], 
    allow_credentials=True,
    allow_methods=["*"], 
    allow_headers=["*"], 
)

# --- HTTP Routes ---
@app.get("/", response_class=HTMLResponse)
async def get_root():
    try:
        # Ensure 'index.html' is in the same directory as app.py,
        # or in a 'static' or 'templates' subdirectory and adjust the path.
        return FileResponse("index.html")
    except RuntimeError as e:
        logger.error(f"Error serving index.html: {e}. Make sure the file exists.")
        return HTMLResponse(content="<h1>Error: Frontend not found.</h1><p>Please ensure index.html is in the correct location.</p>", status_code=500)

@app.get("/health")
async def health_check():
    return {"status": "ok", "active_rooms": len(game.rooms), "total_players_ever": game.global_stats['total_players']}

# --- WebSocket Route ---
@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    await websocket.accept()
    player_id = str(uuid.uuid4()) # Unique ID for this connection
    game.connections[player_id] = websocket
    game.global_stats['total_players'] += 1
    logger.info(f"Player {player_id} connected.")
    
    await websocket.send_json({
        "type": "connected",
        "data": {"player_id": player_id, "message": "Welcome to the Advanced Poker Game!"}
    })

    try:
        while True:
            data = await websocket.receive_text()
            try:
                message_data = json.loads(data)
                ws_message = WSMessage(**message_data) # Validate with Pydantic model
                await handle_websocket_message(websocket, player_id, ws_message)
            except json.JSONDecodeError:
                logger.warning(f"Invalid JSON received from {player_id}: {data}")
                await websocket.send_json({"type": "error", "message": "Invalid JSON format."})
            except ValidationError as e:
                logger.warning(f"Invalid WSMessage structure from {player_id}: {e.errors()}")
                await websocket.send_json({"type": "error", "message": f"Invalid message structure: {e.errors()}"})
            except Exception as e:
                logger.exception(f"Error processing message from {player_id}: {e}")
                await websocket.send_json({"type": "error", "message": "Error processing your request."})

    except WebSocketDisconnect:
        logger.info(f"Player {player_id} disconnected.")
    except Exception as e:
        logger.exception(f"Unexpected error in WebSocket connection for {player_id}: {e}")
    finally:
        if player_id in game.connections:
            del game.connections[player_id]
        game.leave_room(player_id, force=True) # Ensure player is removed from any room
        logger.info(f"Cleaned up resources for player {player_id}.")


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    # When running directly, for Render this will be overridden by their start command.
    # For local testing:
    uvicorn.run("app:app", host="0.0.0.0", port=port, reload=True)
