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

logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s',
    handlers=[
        logging.StreamHandler(),
        logging.FileHandler('poker_game.log') if os.environ.get('LOG_FILE') else logging.NullHandler()
    ]
)
logger = logging.getLogger(__name__)

STARTING_MONEY = 1000
TOURNAMENT_STARTING_MONEY = 10000
SMALL_BLIND = 25
BIG_BLIND = 50
ANTE = 5
MAX_PLAYERS_PER_ROOM = 10
MIN_PLAYERS_TO_START = 2
GAME_UPDATE_RATE = 60
RATE_LIMIT_MESSAGES_PER_SECOND = 15
RATE_LIMIT_ACTIONS_PER_SECOND = 2
MAX_CHAT_MESSAGES = 100
HAND_EVALUATION_CACHE_SIZE = 10000
AUTO_FOLD_TIMEOUT = 30
TOURNAMENT_BLIND_INCREASE_INTERVAL = 600
MAX_ROOMS = 1000
SESSION_TIMEOUT = 3600
MAX_AI_PLAYERS = 7

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
    ai_difficulty: str = "medium"
    
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
        players_to_deal = [p for p in self.players.values() if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED]]
        for _ in range(count):
            for player in players_to_deal:
                if player.status == PlayerStatus.ACTIVE:
                    if self.deck:
                        player.cards.append(self.deck.pop())

    def deal_community_cards(self, count: int):
        for _ in range(count):
            if self.deck:
                self.community_cards.append(self.deck.pop())

    def get_active_players(self) -> List[Player]:
        return [p for p in self.players.values() if p.status not in [PlayerStatus.FOLDED, PlayerStatus.ELIMINATED, PlayerStatus.SITTING_OUT]]

    def get_seated_players(self) -> List[Player]:
        return sorted([p for p in self.players.values() if p.status != PlayerStatus.ELIMINATED], key=lambda p: p.position)

    def get_players_in_hand(self) -> List[Player]:
        return [p for p in self.players.values() if p.status in [PlayerStatus.ACTIVE, PlayerStatus.ALL_IN]]

    def calculate_side_pots(self):
        self.side_pots = []
        players_in_hand_sorted = sorted([p for p in self.get_players_in_hand() if p.total_bet_this_hand > 0], key=lambda p: p.total_bet_this_hand)
        if not players_in_hand_sorted: return
        all_bets = sorted(list(set(p.total_bet_this_hand for p in players_in_hand_sorted)))
        last_bet_level = 0
        for bet_level in all_bets:
            current_pot_amount = 0
            eligible_for_this_pot = set()
            for p in self.players.values():
                if p.total_bet_this_hand >= bet_level:
                    current_pot_amount += (bet_level - last_bet_level)
                    eligible_for_this_pot.add(p.id)
                elif p.total_bet_this_hand > last_bet_level:
                    current_pot_amount += (p.total_bet_this_hand - last_bet_level)
                    eligible_for_this_pot.add(p.id)
            if current_pot_amount > 0 and len(eligible_for_this_pot) > 1 :
                self.side_pots.append(SidePot(amount=current_pot_amount, eligible_players=eligible_for_this_pot))
            elif current_pot_amount > 0 and len(eligible_for_this_pot) == 1 and self.side_pots:
                 pass
            last_bet_level = bet_level
        if self.side_pots:
            main_pot_total = sum(sp.amount for sp in self.side_pots)
            self.pot -= main_pot_total

    def update_activity(self):
        self.last_activity = datetime.now()

class PokerAI:
    def __init__(self, player_id: str, room_code: str, game: 'AdvancedPokerGame'):
        self.player_id = player_id
        self.room_code = room_code
        self.game = game

    async def decide_action(self):
        await asyncio.sleep(random.uniform(1.5, 4.0))
        if self.room_code not in self.game.rooms: return
        room = self.game.rooms[self.room_code]
        if self.player_id not in room.players: return
        player = room.players[self.player_id]
        active_game_players = room.get_active_players()
        if not active_game_players or \
           room.current_player_index >= len(active_game_players) or \
           active_game_players[room.current_player_index].id != self.player_id or \
           not player.can_act():
            logger.info(f"AI {player.name} turn skipped or no longer valid.")
            return
        available_actions = self.game.get_available_actions(room, self.player_id)
        if not available_actions:
            logger.warning(f"AI {player.name} has no available actions.")
            if self.game.player_action(self.room_code, self.player_id, PlayerAction.FOLD, 0):
                 logger.info(f"AI {player.name} performed fallback FOLD action.")
            return
        possible_action_details = {a['action']: a for a in available_actions}
        action_to_take = None
        action_amount = 0
        if PlayerAction.CHECK.value in possible_action_details:
            action_to_take = PlayerAction.CHECK
        elif PlayerAction.CALL.value in possible_action_details:
            call_details = possible_action_details[PlayerAction.CALL.value]
            call_amount = call_details.get('amount', 0)
            if call_amount <= player.money * 0.2 or random.random() < 0.5:
                action_to_take = PlayerAction.CALL
                action_amount = call_amount
            else:
                 if PlayerAction.FOLD.value in possible_action_details:
                    action_to_take = PlayerAction.FOLD
        elif PlayerAction.FOLD.value in possible_action_details:
            action_to_take = PlayerAction.FOLD
        if action_to_take:
            logger.info(f"AI {player.name} decided action: {action_to_take.value} with amount {action_amount}")
            if not self.game.player_action(self.room_code, self.player_id, action_to_take, action_amount):
                logger.error(f"AI {player.name} failed to perform action {action_to_take.value}")
                if PlayerAction.FOLD.value in possible_action_details:
                     self.game.player_action(self.room_code, self.player_id, PlayerAction.FOLD, 0)
        else:
            logger.warning(f"AI {player.name} could not decide on an action. Defaulting to FOLD.")
            if PlayerAction.FOLD.value in possible_action_details:
                self.game.player_action(self.room_code, self.player_id, PlayerAction.FOLD, 0)

class AdvancedPokerGame:
    def __init__(self):
        self.rooms: Dict[str, Room] = {}
        self.connections: Dict[str, WebSocket] = {}
        self.player_rooms: Dict[str, str] = {}
        self.player_sessions: Dict[str, str] = {}
        self.rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.action_rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.hand_evaluation_cache: Dict[str, HandEvaluation] = {}
        self.running = True
        self.global_stats = {'total_hands': 0, 'total_players': 0, 'active_rooms': 0, 'biggest_pot': 0}

    def generate_room_code(self) -> str:
        return ''.join(random.choices('ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789', k=6))

    def create_room(self, owner_id: str, room_settings: GameSettings, room_name: str = None, num_ai_players: int = 0) -> str:
        if len(self.rooms) >= MAX_ROOMS: raise Exception("Maximum number of rooms reached")
        room_code = self.generate_room_code()
        while room_code in self.rooms: room_code = self.generate_room_code()
        room_name = room_name or f"Room {room_code}"
        new_room = Room(code=room_code, name=room_name, players={}, spectators=set(), deck=[], community_cards=[], settings=room_settings, owner_id=owner_id, room_type=RoomType.PRIVATE if room_settings.password else RoomType.PUBLIC)
        self.rooms[room_code] = new_room
        actual_num_ai = min(num_ai_players, room_settings.max_players -1, MAX_AI_PLAYERS)
        for i in range(actual_num_ai):
            ai_player_id = f"AI_{str(uuid.uuid4())[:6]}"
            ai_player_name = f"Bot {random.choice(['Ace', 'King', 'Queen', 'Jack', 'Ten'])} {i+1}"
            ai_player = Player(id=ai_player_id, name=ai_player_name, money=room_settings.buy_in if room_settings.buy_in > 0 else (TOURNAMENT_STARTING_MONEY if room_settings.game_mode == GameMode.TOURNAMENT else STARTING_MONEY), is_ai=True, avatar=f"avatar_ai_{random.randint(1,5)}", color=f"#{random.randint(0x50, 0xAA):02x}{random.randint(0x50, 0xAA):02x}{random.randint(0x50, 0xAA):02x}", position=i + 1)
            new_room.players[ai_player_id] = ai_player
        logger.info(f"Room {room_code} ('{room_name}') created by player {owner_id} with {actual_num_ai} AI players.")
        return room_code

    def join_room(self, room_code: str, player_id: str, player_name: str, password: str = None) -> bool:
        if room_code not in self.rooms: return False
        room = self.rooms[room_code]
        if room.settings.password and room.settings.password != password: return False
        if len(room.players) >= room.settings.max_players: return False
        if player_id in room.players:
            room.players[player_id].connection_id = player_id
            room.players[player_id].name = player_name
            if room.players[player_id].status == PlayerStatus.SITTING_OUT: room.players[player_id].status = PlayerStatus.ACTIVE
            logger.info(f"Player {player_name} ({player_id}) re-joined room {room_code}")
            self.player_rooms[player_id] = room_code
            room.update_activity()
            return True
        player = Player(id=player_id, name=player_name, position=len(room.players), money=room.settings.buy_in if room.settings.buy_in > 0 else (TOURNAMENT_STARTING_MONEY if room.settings.game_mode == GameMode.TOURNAMENT else STARTING_MONEY), avatar=f"avatar_{random.randint(1, 10)}", color=f"#{random.randint(0, 0xFFFFFF):06x}", connection_id=player_id)
        room.players[player_id] = player
        self.player_rooms[player_id] = room_code
        room.update_activity()
        logger.info(f"Player {player_name} ({player_id}) joined room {room_code}")
        return True

    def leave_room(self, player_id: str, force: bool = False):
        if player_id not in self.player_rooms:
            if player_id in self.connections: logger.info(f"Player {player_id} (not in room) is leaving.")
            return
        room_code = self.player_rooms[player_id]
        if room_code not in self.rooms:
            del self.player_rooms[player_id]
            return
        room = self.rooms[room_code]
        if player_id in room.players:
            player = room.players[player_id]
            if room.settings.game_mode == GameMode.TOURNAMENT and not force and player.status != PlayerStatus.ELIMINATED:
                player.status = PlayerStatus.SITTING_OUT
                player.connection_id = None
                logger.info(f"Player {player.name} ({player_id}) disconnected from tournament in room {room_code}, now sitting out.")
            else:
                del room.players[player_id]
                logger.info(f"Player {player.name} ({player_id}) left room {room_code}.")
        if player_id in room.spectators:
            room.spectators.remove(player_id)
            logger.info(f"Spectator {player_id} left room {room_code}.")
        del self.player_rooms[player_id]
        if room.owner_id == player_id and any(not p.is_ai for p in room.players.values()):
            new_owner = next((p.id for p in room.players.values() if not p.is_ai), None)
            if new_owner:
                room.owner_id = new_owner
                logger.info(f"Room {room_code} ownership transferred to {room.players[new_owner].name}.")
            elif room.players:
                 room.owner_id = next(iter(room.players.keys()))
                 logger.info(f"Room {room_code} ownership transferred to AI {room.players[room.owner_id].name}.")
        if not any(not p.is_ai for p in room.players.values()) and not room.spectators:
            logger.info(f"Room {room_code} is now empty of human players/spectators. Deleting room.")
            del self.rooms[room_code]
        elif not room.players and not room.spectators:
            logger.info(f"Room {room_code} is empty. Deleting room.")
            del self.rooms[room_code]

    def spectate_room(self, room_code: str, player_id: str, password: str = None) -> bool:
        if room_code not in self.rooms: return False
        room = self.rooms[room_code]
        if room.settings.password and room.settings.password != password: return False
        room.spectators.add(player_id)
        self.player_rooms[player_id] = room_code
        room.update_activity()
        logger.info(f"Player {player_id} started spectating room {room_code}")
        return True

    def start_game(self, room_code: str, force_start: bool = False):
        if room_code not in self.rooms: return False
        room = self.rooms[room_code]
        players_ready_to_play = [p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED]
        if len(players_ready_to_play) < room.settings.min_players and not force_start:
            logger.warning(f"Cannot start game in room {room_code}: not enough players ({len(players_ready_to_play)}/{room.settings.min_players})")
            return False
        room.phase = GamePhase.PRE_FLOP
        room.hand_number += 1
        room.shuffle_deck()
        room.community_cards = []
        room.pot = 0
        room.side_pots = []
        room.current_bet = room.settings.big_blind
        room.min_raise = room.settings.big_blind
        seated_players = sorted([p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED], key=lambda p: p.id)
        for i, player in enumerate(seated_players):
            player.position = i
            player.reset_for_new_hand()
            if player.money <= 0 and room.settings.game_mode != GameMode.TOURNAMENT :
                player.money = room.settings.buy_in if room.settings.buy_in > 0 else STARTING_MONEY
            if player.connection_id is None and not player.is_ai and player.status == PlayerStatus.ACTIVE:
                player.status = PlayerStatus.SITTING_OUT
        room.dealer_index = (room.dealer_index + 1) % len(seated_players)
        self.set_player_blinds(room, seated_players)
        self.post_blinds_and_ante(room)
        room.deal_cards(2)
        room.current_player_index = self.get_first_player_to_act_idx(room, seated_players)
        room.last_action_time = time.time()
        self.global_stats['total_hands'] += 1
        logger.info(f"Game started in room {room_code}, hand #{room.hand_number}. Dealer: {seated_players[room.dealer_index].name}. First to act: {seated_players[room.current_player_index].name if room.current_player_index != -1 else 'N/A'}")
        if room.current_player_index != -1 and seated_players[room.current_player_index].is_ai:
            asyncio.create_task(self.check_for_ai_turn(room_code))
        return True

    def set_player_blinds(self, room: Room, seated_players: List[Player]):
        num_seated = len(seated_players)
        if num_seated < 2: return
        for p in seated_players: p.is_dealer = False; p.is_small_blind = False; p.is_big_blind = False
        eligible_for_blinds = [p for p in seated_players if p.status != PlayerStatus.SITTING_OUT]
        num_eligible = len(eligible_for_blinds)
        if num_eligible < 2:
            logger.warning(f"Not enough eligible players ({num_eligible}) for blinds in room {room.code}")
            return
        dealer_player = seated_players[room.dealer_index]
        dealer_player.is_dealer = True
        sb_player = None
        current_idx = room.dealer_index
        for _ in range(num_seated):
            current_idx = (current_idx + 1) % num_seated
            if seated_players[current_idx].status != PlayerStatus.SITTING_OUT:
                sb_player = seated_players[current_idx]; break
        if sb_player:
            sb_player.is_small_blind = True
            bb_player = None
            sb_idx_in_seated = seated_players.index(sb_player)
            current_idx = sb_idx_in_seated
            for _ in range(num_seated):
                current_idx = (current_idx + 1) % num_seated
                if seated_players[current_idx].status != PlayerStatus.SITTING_OUT:
                    bb_player = seated_players[current_idx]; break
            if bb_player: bb_player.is_big_blind = True
            else: logger.error(f"Could not assign Big Blind in room {room.code}")
        else: logger.error(f"Could not assign Small Blind in room {room.code}")

    def post_blinds_and_ante(self, room: Room):
        players_for_ante = [p for p in room.players.values() if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED]]
        if room.settings.ante > 0:
            for player in players_for_ante:
                ante_amount = min(room.settings.ante, player.money)
                player.money -= ante_amount; player.total_bet_this_hand += ante_amount; room.pot += ante_amount
                if player.money == 0: player.status = PlayerStatus.ALL_IN
        sb_player = next((p for p in room.players.values() if p.is_small_blind), None)
        bb_player = next((p for p in room.players.values() if p.is_big_blind), None)
        if sb_player:
            blind_amount = min(room.settings.small_blind, sb_player.money)
            sb_player.money -= blind_amount; sb_player.current_bet += blind_amount; sb_player.total_bet_this_hand += blind_amount; room.pot += blind_amount
            if sb_player.money == 0: sb_player.status = PlayerStatus.ALL_IN
        if bb_player:
            blind_amount = min(room.settings.big_blind, bb_player.money)
            bb_player.money -= blind_amount; bb_player.current_bet += blind_amount; bb_player.total_bet_this_hand += blind_amount; room.pot += blind_amount
            if bb_player.money == 0: bb_player.status = PlayerStatus.ALL_IN
        room.current_bet = room.settings.big_blind

    def get_first_player_to_act_idx(self, room: Room, seated_players: List[Player]) -> int:
        num_seated = len(seated_players)
        if num_seated < 2: return -1 
        bb_player = next((p for p in seated_players if p.is_big_blind), None)
        if not bb_player:
            logger.warning(f"No Big Blind found to determine first actor in room {room.code}")
            start_idx = room.dealer_index
            for i in range(num_seated):
                current_player_idx = (start_idx + 1 + i) % num_seated
                if seated_players[current_player_idx].status != PlayerStatus.SITTING_OUT: return current_player_idx
            return -1
        bb_idx_in_seated = seated_players.index(bb_player)
        current_idx = bb_idx_in_seated
        for _ in range(num_seated):
            current_idx = (current_idx + 1) % num_seated
            if seated_players[current_idx].status != PlayerStatus.SITTING_OUT: return current_idx
        return -1

    async def check_for_ai_turn(self, room_code: str):
        if room_code not in self.rooms: return
        room = self.rooms[room_code]
        if room.phase in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER] or room.paused: return
        seated_players = room.get_seated_players()
        if not seated_players or not (0 <= room.current_player_index < len(seated_players)): return
        current_player_at_table = seated_players[room.current_player_index]
        current_player_obj = room.players.get(current_player_at_table.id)
        if current_player_obj and current_player_obj.is_ai and current_player_obj.can_act():
            active_players_for_turn_check = room.get_active_players()
            if active_players_for_turn_check:
                logger.info(f"AI player {current_player_obj.name}'s turn in room {room_code}")
                ai_instance = PokerAI(current_player_obj.id, room_code, self)
                asyncio.create_task(ai_instance.decide_action())

    def player_action(self, room_code: str, player_id: str, action: PlayerAction, amount: int = 0) -> bool:
        if room_code not in self.rooms: return False
        room = self.rooms[room_code]
        if player_id not in room.players: return False
        player = room.players[player_id]
        seated_players = room.get_seated_players()
        if not seated_players or not (0 <= room.current_player_index < len(seated_players)):
            logger.warning(f"Action by {player.name}: No current player or index out of bounds.")
            return False
        current_actor_at_table = seated_players[room.current_player_index]
        if current_actor_at_table.id != player_id:
            logger.warning(f"Action by {player.name} but it's {current_actor_at_table.name}'s turn.")
            return False
        if not player.can_act():
            logger.warning(f"Player {player.name} cannot act (status: {player.status}, money: {player.money}).")
            return False
        success = self.process_player_action(room, player, action, amount)
        if success:
            player.last_action = action
            player.last_action_time = time.time()
            room.last_action_time = time.time()
            if room.phase != GamePhase.WAITING: player.stats.hands_played += 1
            self.advance_game(room_code)
        return success

    def process_player_action(self, room: Room, player: Player, action: PlayerAction, amount: int) -> bool:
        amount = max(0, amount)
        if action == PlayerAction.FOLD:
            player.status = PlayerStatus.FOLDED; logger.info(f"Player {player.name} FOLDED."); return True
        elif action == PlayerAction.CHECK:
            is_bb_option = (room.phase == GamePhase.PRE_FLOP and player.is_big_blind and player.current_bet == room.settings.big_blind and room.current_bet == room.settings.big_blind)
            if player.current_bet < room.current_bet and not is_bb_option:
                logger.warning(f"Player {player.name} tried to CHECK but needs to call ${room.current_bet - player.current_bet}"); return False
            logger.info(f"Player {player.name} CHECKED."); return True
        elif action == PlayerAction.CALL:
            amount_to_call = room.current_bet - player.current_bet
            if amount_to_call <= 0 :
                if amount_to_call == 0: return self.process_player_action(room, player, PlayerAction.CHECK, 0)
                logger.warning(f"Player {player.name} tried to CALL but amount to call is ${amount_to_call}"); return False
            actual_call = min(amount_to_call, player.money)
            player.money -= actual_call; player.current_bet += actual_call; player.total_bet_this_hand += actual_call; room.pot += actual_call
            if player.money == 0: player.status = PlayerStatus.ALL_IN; logger.info(f"Player {player.name} CALLED ${actual_call} and is ALL-IN.")
            else: logger.info(f"Player {player.name} CALLED ${actual_call}.")
            return True
        elif action == PlayerAction.RAISE:
            bet_needed_to_call = room.current_bet - player.current_bet
            if player.money < (bet_needed_to_call + amount):
                actual_raise_amount_possible = player.money - bet_needed_to_call
                if actual_raise_amount_possible <=0: logger.warning(f"Player {player.name} tried to RAISE (all-in) but cannot even call."); return False
                amount_put_in = player.money
                player.current_bet += amount_put_in; player.total_bet_this_hand += amount_put_in; room.pot += amount_put_in
                player.money = 0; player.status = PlayerStatus.ALL_IN
                if actual_raise_amount_possible >= room.min_raise: room.min_raise = actual_raise_amount_possible
                room.current_bet = player.current_bet
                logger.info(f"Player {player.name} RAISED ALL-IN to ${player.current_bet} (raised by ${actual_raise_amount_possible}).")
            else:
                if amount < room.min_raise: logger.warning(f"Player {player.name} tried to RAISE by ${amount}, less than min_raise ${room.min_raise}"); return False 
                amount_put_in = bet_needed_to_call + amount
                player.money -= amount_put_in; player.current_bet += amount_put_in; player.total_bet_this_hand += amount_put_in; room.pot += amount_put_in
                room.current_bet = player.current_bet; room.min_raise = amount
                logger.info(f"Player {player.name} RAISED to ${player.current_bet} (raised by ${amount}).")
            return True
        elif action == PlayerAction.ALL_IN:
            if player.money <= 0: return False
            amount_to_all_in = player.money
            player.current_bet += amount_to_all_in; player.total_bet_this_hand += amount_to_all_in; room.pot += amount_to_all_in
            player.money = 0; player.status = PlayerStatus.ALL_IN
            if player.current_bet > room.current_bet:
                amount_raised_over_current_bet = player.current_bet - room.current_bet 
                if amount_raised_over_current_bet >= room.min_raise: room.min_raise = amount_raised_over_current_bet
                room.current_bet = player.current_bet
            logger.info(f"Player {player.name} went ALL-IN with ${amount_to_all_in}."); return True
        elif action == PlayerAction.SIT_OUT: player.status = PlayerStatus.SITTING_OUT; logger.info(f"Player {player.name} is SITTING OUT."); return True
        elif action == PlayerAction.SIT_IN:
            if player.status == PlayerStatus.SITTING_OUT: player.status = PlayerStatus.ACTIVE; logger.info(f"Player {player.name} is SITTING IN."); return True
            return False
        return False

    def advance_game(self, room_code: str):
        if room_code not in self.rooms: return
        room = self.rooms[room_code]
        players_still_in_hand = room.get_players_in_hand()
        if len(players_still_in_hand) <= 1 and room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN]:
            logger.info(f"Hand ends early in room {room_code} as only {len(players_still_in_hand)} player(s) remain.")
            self.end_hand(room_code); return
        if self.is_betting_round_complete(room):
            logger.info(f"Betting round complete for phase {room.phase.value} in room {room_code}.")
            self.advance_phase(room_code)
        else:
            self.move_to_next_player(room)
            seated_players = room.get_seated_players()
            if seated_players and 0 <= room.current_player_index < len(seated_players):
                if seated_players[room.current_player_index].is_ai:
                    asyncio.create_task(self.check_for_ai_turn(room_code))

    def move_to_next_player(self, room: Room):
        seated_players = room.get_seated_players()
        if not seated_players: return
        num_seated = len(seated_players)
        start_search_idx = room.current_player_index
        for i in range(num_seated):
            next_player_candidate_idx = (start_search_idx + 1 + i) % num_seated
            candidate_player = seated_players[next_player_candidate_idx]
            if candidate_player.status == PlayerStatus.ACTIVE and candidate_player.money > 0:
                room.current_player_index = next_player_candidate_idx
                room.last_action_time = time.time()
                logger.info(f"Next player to act in room {room.code}: {candidate_player.name} (Index {room.current_player_index})")
                return
        logger.warning(f"Could not find next active player in room {room.code}. Current index: {room.current_player_index}")

    def is_betting_round_complete(self, room: Room) -> bool:
        active_players_for_betting = [p for p in room.players.values() if p.status == PlayerStatus.ACTIVE and p.money > 0]
        if not active_players_for_betting: return True
        highest_bet_this_round = room.current_bet
        for p in room.get_players_in_hand():
            if p.status == PlayerStatus.ACTIVE and p.current_bet < highest_bet_this_round and p.money > 0: return False
        players_to_check = [p for p in room.players.values() if p.status == PlayerStatus.ACTIVE and p.money > 0]
        if not players_to_check: return True
        for p in players_to_check:
            if p.last_action is None and room.phase != GamePhase.PRE_FLOP:
                if room.phase == GamePhase.PRE_FLOP and p.is_big_blind and room.current_bet == room.settings.big_blind: pass
                else: return False
            if p.current_bet < room.current_bet: return False
        return True

    def advance_phase(self, room_code: str):
        if room_code not in self.rooms: return
        room = self.rooms[room_code]
        for player in room.players.values(): player.current_bet = 0; player.last_action = None
        room.current_bet = 0; room.min_raise = room.settings.big_blind
        if room.phase == GamePhase.PRE_FLOP:
            room.phase = GamePhase.FLOP; room.deal_community_cards(3)
            logger.info(f"Room {room.code} advanced to FLOP. Community cards: {[str(c) for c in room.community_cards]}")
        elif room.phase == GamePhase.FLOP:
            room.phase = GamePhase.TURN; room.deal_community_cards(1)
            logger.info(f"Room {room.code} advanced to TURN. Community cards: {[str(c) for c in room.community_cards]}")
        elif room.phase == GamePhase.TURN:
            room.phase = GamePhase.RIVER; room.deal_community_cards(1)
            logger.info(f"Room {room.code} advanced to RIVER. Community cards: {[str(c) for c in room.community_cards]}")
        elif room.phase == GamePhase.RIVER:
            logger.info(f"Room {room.code} betting on RIVER complete, advancing to SHOWDOWN.")
            room.phase = GamePhase.SHOWDOWN; self.end_hand(room_code); return
        seated_players = room.get_seated_players()
        if not seated_players: return
        start_idx = room.dealer_index; found_next_actor = False
        for i in range(len(seated_players)):
            candidate_idx = (start_idx + 1 + i) % len(seated_players)
            player_candidate = seated_players[candidate_idx]
            if player_candidate.status == PlayerStatus.ACTIVE and player_candidate.money > 0:
                room.current_player_index = candidate_idx; room.last_action_time = time.time()
                logger.info(f"First player to act in {room.phase.value} for room {room.code}: {player_candidate.name}")
                found_next_actor = True
                if player_candidate.is_ai: asyncio.create_task(self.check_for_ai_turn(room_code))
                break
        if not found_next_actor:
            logger.info(f"No active player found to start betting in {room.phase.value} for room {room.code}. Advancing phase again.")
            if room.phase != GamePhase.SHOWDOWN: self.advance_phase(room_code)

    def end_hand(self, room_code: str):
        if room_code not in self.rooms: return
        room = self.rooms[room_code]
        if room.phase != GamePhase.SHOWDOWN: room.phase = GamePhase.SHOWDOWN
        logger.info(f"Ending hand #{room.hand_number} in room {room.code}. Phase: {room.phase.value}")
        winners_evaluations = self.determine_winners(room)
        self.distribute_winnings(room, winners_evaluations)
        self.save_hand_history(room)
        if room.settings.game_mode == GameMode.TOURNAMENT: self.update_tournament(room)
        active_human_players = [p for p in room.players.values() if not p.is_ai and p.status != PlayerStatus.ELIMINATED and p.money > 0]
        if room.settings.game_mode == GameMode.TOURNAMENT:
            surviving_players = [p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED and p.money > 0]
            if len(surviving_players) <= 1:
                room.phase = GamePhase.GAME_OVER
                self.end_tournament(room, surviving_players[0] if surviving_players else None)
                logger.info(f"Tournament in room {room.code} ended. Winner: {surviving_players[0].name if surviving_players else 'N/A'}")
                return
        room.phase = GamePhase.WAITING
        players_for_next_hand = [p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED and (p.is_ai or p.connection_id is not None or p.status != PlayerStatus.SITTING_OUT)]
        if len(players_for_next_hand) >= room.settings.min_players:
            logger.info(f"Room {room.code} has enough players ({len(players_for_next_hand)}), scheduling next hand.")
            asyncio.create_task(self.auto_start_next_hand(room_code, delay=8))
        else:
            logger.info(f"Room {room.code} waiting for players for next hand ({len(players_for_next_hand)}/{room.settings.min_players}).")

    def determine_winners(self, room: Room) -> Dict[str, HandEvaluation]:
        players_to_evaluate = [p for p in room.players.values() if p.status != PlayerStatus.FOLDED and p.status != PlayerStatus.ELIMINATED and p.cards]
        if not players_to_evaluate:
            winner_by_default = next((p for p in room.get_players_in_hand()), None)
            if winner_by_default: return {winner_by_default.id: HandEvaluation(HandRank.HIGH_CARD, 0, [], "Default Winner", [])}
            return {}
        evaluations = {}
        for player in players_to_evaluate:
            cards_to_eval = player.cards
            if room.phase in [GamePhase.FLOP, GamePhase.TURN, GamePhase.RIVER, GamePhase.SHOWDOWN]:
                cards_to_eval = player.cards + room.community_cards
            if len(cards_to_eval) >= 5:
                hand_eval = self.evaluate_hand(cards_to_eval)
                evaluations[player.id] = hand_eval
            elif player.cards :
                player.cards.sort(key=lambda c: c.value(), reverse=True)
                hc_val = sum(c.value() * (10**(2*(1-i))) for i, c in enumerate(player.cards[:2]))
                evaluations[player.id] = HandEvaluation(rank=HandRank.HIGH_CARD, value=hc_val, cards=player.cards[:], description=f"High Card {player.cards[0].rank if player.cards else ''}", kickers=[c.value() for c in player.cards])
        return evaluations

    def evaluate_hand(self, cards: List[Card]) -> HandEvaluation:
        card_key = ''.join(sorted([f"{c.suit[0]}{c.rank}" for c in cards]))
        if card_key in self.hand_evaluation_cache: return self.hand_evaluation_cache[card_key]
        if len(cards) < 5:
            sorted_cards = sorted(cards, key=lambda c: c.value(), reverse=True)
            hc_val = sum(c.value() * (10**(2*(len(sorted_cards)-1-i))) for i, c in enumerate(sorted_cards))
            return HandEvaluation(HandRank.HIGH_CARD, hc_val, sorted_cards, "Incomplete Hand", [c.value() for c in sorted_cards])
        hand_eval = self.full_hand_evaluation(cards)
        if len(self.hand_evaluation_cache) < HAND_EVALUATION_CACHE_SIZE: self.hand_evaluation_cache[card_key] = hand_eval
        return hand_eval

    def full_hand_evaluation(self, all_cards: List[Card]) -> HandEvaluation:
        from itertools import combinations
        best_hand_eval_details = (HandRank.HIGH_CARD, 0, [])
        best_five_card_combo = []
        if len(all_cards) < 5:
            sorted_cards = sorted(all_cards, key=lambda c: c.value(), reverse=True)
            hc_val = sum(c.value() * (10**(2*(len(sorted_cards)-1-i))) for i, c in enumerate(sorted_cards))
            return HandEvaluation(HandRank.HIGH_CARD, hc_val, sorted_cards, f"High Card {sorted_cards[0].rank if sorted_cards else 'N/A'}", [c.value() for c in sorted_cards])
        for combo_cards_obj in combinations(all_cards, 5):
            current_rank, current_value, current_card_values = self.evaluate_5_card_hand(list(combo_cards_obj))
            if current_rank > best_hand_eval_details[0] or (current_rank == best_hand_eval_details[0] and current_value > best_hand_eval_details[1]):
                best_hand_eval_details = (current_rank, current_value, current_card_values)
                best_five_card_combo = list(combo_cards_obj)
        return HandEvaluation(rank=best_hand_eval_details[0], value=best_hand_eval_details[1], cards=sorted(best_five_card_combo, key=lambda c: c.value(), reverse=True), description=self.get_hand_description(best_hand_eval_details[0], best_hand_eval_details[2]), kickers=best_hand_eval_details[2])

    def evaluate_5_card_hand(self, cards: List[Card]) -> Tuple[HandRank, int, List[int]]:
        cards.sort(key=lambda x: x.value(), reverse=True)
        values = [c.value() for c in cards]; suits = [c.suit for c in cards]
        is_flush = len(set(suits)) == 1
        is_straight = False; unique_values = sorted(list(set(values)), reverse=True)
        if len(unique_values) >= 5:
            if all(unique_values[i] - unique_values[i+1] == 1 for i in range(4)):
                 if values[0] - values[4] == 4 and len(set(values))==5 : is_straight = True
        straight_values_for_ranking = values[:]
        if set(values) == {14, 2, 3, 4, 5}: is_straight = True; straight_values_for_ranking = [5,4,3,2,1]
        elif is_straight: straight_values_for_ranking = values[:]
        value_counts = Counter(values); counts = sorted(value_counts.values(), reverse=True)
        if is_straight and is_flush and values[0] == 14 and values[4] == 10 : return HandRank.ROYAL_FLUSH, values[0], straight_values_for_ranking
        if is_straight and is_flush: return HandRank.STRAIGHT_FLUSH, straight_values_for_ranking[0], straight_values_for_ranking
        if counts == [4, 1]: four_val = [v for v,c in value_counts.items() if c==4][0]; kicker_val = [v for v,c in value_counts.items() if c==1][0]; return HandRank.FOUR_OF_A_KIND, four_val*15+kicker_val, [four_val,kicker_val]
        if counts == [3, 2]: three_val = [v for v,c in value_counts.items() if c==3][0]; pair_val = [v for v,c in value_counts.items() if c==2][0]; return HandRank.FULL_HOUSE, three_val*15+pair_val, [three_val,pair_val]
        if is_flush: flush_value = sum(v*(15**(4-i)) for i,v in enumerate(values)); return HandRank.FLUSH, flush_value, values
        if is_straight: return HandRank.STRAIGHT, straight_values_for_ranking[0], straight_values_for_ranking
        if counts == [3,1,1]: three_val = [v for v,c in value_counts.items() if c==3][0]; kickers=sorted([v for v,c in value_counts.items() if c==1],reverse=True); val_comp=three_val*(15**2)+kickers[0]*15+kickers[1]; return HandRank.THREE_OF_A_KIND, val_comp, [three_val]+kickers
        if counts == [2,2,1]: pairs_vals=sorted([v for v,c in value_counts.items() if c==2],reverse=True); kicker_val=[v for v,c in value_counts.items() if c==1][0]; val_comp=pairs_vals[0]*(15**2)+pairs_vals[1]*15+kicker_val; return HandRank.TWO_PAIR, val_comp, pairs_vals+[kicker_val]
        if counts == [2,1,1,1]: pair_val=[v for v,c in value_counts.items() if c==2][0]; kickers=sorted([v for v,c in value_counts.items() if c==1],reverse=True); val_comp=pair_val*(15**3)+kickers[0]*(15**2)+kickers[1]*15+kickers[2]; return HandRank.PAIR, val_comp, [pair_val]+kickers
        hc_val = sum(v*(15**(4-i)) for i,v in enumerate(values)); return HandRank.HIGH_CARD, hc_val, values

    def get_hand_description(self, rank: HandRank, best_card_values: List[int]) -> str:
        card_names = {14:'Ace',13:'King',12:'Queen',11:'Jack',10:'Ten',9:'Nine',8:'Eight',7:'Seven',6:'Six',5:'Five',4:'Four',3:'Three',2:'Two',1:'Ace (low)'}
        def name(v): return card_names.get(v,str(v))
        if not best_card_values: return rank.name.replace('_',' ')
        if rank==HandRank.ROYAL_FLUSH: return "Royal Flush"
        if rank==HandRank.STRAIGHT_FLUSH: return f"Straight Flush, {name(best_card_values[0])} high"
        if rank==HandRank.FOUR_OF_A_KIND: return f"Four of a Kind, {name(best_card_values[0])}s"
        if rank==HandRank.FULL_HOUSE: return f"Full House, {name(best_card_values[0])}s full of {name(best_card_values[1])}s"
        if rank==HandRank.FLUSH: return f"Flush, {name(best_card_values[0])} high"
        if rank==HandRank.STRAIGHT: return f"Straight, {name(best_card_values[0])} high"
        if rank==HandRank.THREE_OF_A_KIND: return f"Three of a Kind, {name(best_card_values[0])}s"
        if rank==HandRank.TWO_PAIR: return f"Two Pair, {name(best_card_values[0])}s and {name(best_card_values[1])}s"
        if rank==HandRank.PAIR: return f"Pair of {name(best_card_values[0])}s"
        return f"High Card {name(best_card_values[0])}"

    def distribute_winnings(self, room: Room, winners_evals: Dict[str, HandEvaluation]):
        if not winners_evals:
            remaining_player_ids = [p.id for p in room.get_players_in_hand()]
            if len(remaining_player_ids) == 1:
                winner_id = remaining_player_ids[0]
                room.players[winner_id].money += room.pot; room.players[winner_id].stats.hands_won += 1
                room.players[winner_id].stats.total_winnings += room.pot
                if room.pot > room.players[winner_id].stats.biggest_pot: room.players[winner_id].stats.biggest_pot = room.pot
                logger.info(f"Player {room.players[winner_id].name} wins pot of ${room.pot} by default.")
                self.global_stats['biggest_pot'] = max(self.global_stats['biggest_pot'], room.pot); room.pot = 0
            else: logger.warning(f"No winners evaluated and not a single player remaining in hand for room {room.code}. Pot: ${room.pot}")
            return
        best_rank_val = HandRank.HIGH_CARD; best_numeric_val = 0
        for eval_data in winners_evals.values():
            if eval_data.rank > best_rank_val: best_rank_val = eval_data.rank; best_numeric_val = eval_data.value
            elif eval_data.rank == best_rank_val and eval_data.value > best_numeric_val: best_numeric_val = eval_data.value
        actual_winners_ids = [pid for pid, eval_data in winners_evals.items() if eval_data.rank == best_rank_val and eval_data.value == best_numeric_val]
        if not actual_winners_ids: logger.error(f"No winners found after evaluation in room {room.code}. This should not happen."); return
        pot_to_distribute = room.pot
        if pot_to_distribute <=0 and not room.side_pots: logger.info(f"No pot to distribute in room {room.code}."); return
        winnings_per_winner = pot_to_distribute // len(actual_winners_ids); remainder = pot_to_distribute % len(actual_winners_ids)
        winner_names_log = []
        for i, winner_id in enumerate(actual_winners_ids):
            player = room.players[winner_id]; amount_won = winnings_per_winner + (1 if i < remainder else 0)
            player.money += amount_won; player.stats.hands_won += 1; player.stats.total_winnings += amount_won
            if amount_won > player.stats.biggest_pot: player.stats.biggest_pot = amount_won
            self.global_stats['biggest_pot'] = max(self.global_stats['biggest_pot'], amount_won)
            winner_names_log.append(f"{player.name} (won ${amount_won})")
        logger.info(f"Pot of ${pot_to_distribute} distributed to: {', '.join(winner_names_log)} in room {room.code}.")
        room.pot = 0

    def save_hand_history(self, room: Room): pass

    def update_tournament(self, room: Room):
        if room.settings.game_mode != GameMode.TOURNAMENT: return
        for player in list(room.players.values()):
            if player.money <= 0 and player.status != PlayerStatus.ELIMINATED:
                player.status = PlayerStatus.ELIMINATED
                player.tournament_rank = len([p for p in room.players.values() if p.status == PlayerStatus.ELIMINATED])
                logger.info(f"Player {player.name} eliminated from tournament in room {room.code}. Rank: {player.tournament_rank}")
        if datetime.now() >= room.tournament_next_level:
            room.tournament_level += 1
            new_sb = math.ceil(room.settings.small_blind * 1.5 / 5) * 5
            new_bb = math.ceil(room.settings.big_blind * 1.5 / 5) * 5
            room.settings.small_blind = new_sb; room.settings.big_blind = new_bb
            room.tournament_next_level = datetime.now() + timedelta(seconds=TOURNAMENT_BLIND_INCREASE_INTERVAL)
            logger.info(f"Room {room.code} tournament level up: {room.tournament_level}. Blinds: {new_sb}/{new_bb}")
            if room.tournament_level % 5 == 0:
                room.phase = GamePhase.TOURNAMENT_BREAK; room.paused = True
                room.pause_reason = f"Tournament Break - Level {room.tournament_level} (5 min)"
                logger.info(f"Room {room.code} on tournament break for 5 minutes.")
                asyncio.create_task(self.resume_tournament_after_break(room.code))

    async def resume_tournament_after_break(self, room_code: str):
        await asyncio.sleep(300)
        if room_code in self.rooms:
            room = self.rooms[room_code]
            if room.paused and room.phase == GamePhase.TOURNAMENT_BREAK :
                room.paused = False; room.pause_reason = ""; room.phase = GamePhase.WAITING
                logger.info(f"Tournament break ended in room {room.code}.")
                players_for_next_hand = [p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED]
                if len(players_for_next_hand) >= room.settings.min_players:
                    asyncio.create_task(self.auto_start_next_hand(room_code, delay=2))

    def end_tournament(self, room: Room, winner: Optional[Player]):
        logger.info(f"Tournament ended in room {room.code}.")
        if winner: winner.tournament_rank = 1; logger.info(f"Winner: {winner.name}")

    async def auto_start_next_hand(self, room_code: str, delay: int = 5):
        await asyncio.sleep(delay)
        if room_code in self.rooms:
            room = self.rooms[room_code]
            if room.phase == GamePhase.WAITING and not room.paused:
                ready_players = [p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED and (p.is_ai or p.status != PlayerStatus.SITTING_OUT)]
                if len(ready_players) >= room.settings.min_players:
                    logger.info(f"Auto-starting next hand in room {room_code}.")
                    self.start_game(room_code)
                else:
                    logger.info(f"Auto-start next hand in room {room_code} aborted: not enough ready players ({len(ready_players)}/{room.settings.min_players}).")

    def add_chat_message(self, room_code: str, player_id: str, message: str):
        if room_code not in self.rooms: return
        room = self.rooms[room_code]
        player_name = "Spectator"; player_color = "#CCCCCC"
        if player_id in room.players: player = room.players[player_id]; player_name = player.name; player_color = player.color
        elif player_id == "SYSTEM": player_name = "SYSTEM"; player_color = "#FFD700"
        chat_msg = {"id":str(uuid.uuid4()),"player_id":player_id,"player_name":player_name,"player_color":player_color,"message":message,"timestamp":time.time(),"formatted_time":datetime.now().strftime("%H:%M:%S")}
        room.chat_messages.append(chat_msg)
        if len(room.chat_messages) > MAX_CHAT_MESSAGES: room.chat_messages = room.chat_messages[-MAX_CHAT_MESSAGES:]
        room.update_activity()

    def check_rate_limit(self, player_id: str, limit_type: str = "message") -> bool:
        now = time.time()
        if limit_type == "message": rate_limit_dict = self.rate_limits; max_per_second = RATE_LIMIT_MESSAGES_PER_SECOND
        elif limit_type == "action": rate_limit_dict = self.action_rate_limits; max_per_second = RATE_LIMIT_ACTIONS_PER_SECOND
        else: return True
        rate_limit_dict[player_id] = [t for t in rate_limit_dict[player_id] if now - t < 1.0]
        if len(rate_limit_dict[player_id]) >= max_per_second:
            logger.warning(f"Rate limit exceeded for player {player_id}, type {limit_type}.")
            return False
        rate_limit_dict[player_id].append(now); return True

    def cleanup_inactive_rooms(self):
        current_time = datetime.now(); rooms_to_delete = []
        for room_code, room in list(self.rooms.items()):
            is_empty_public_room = room.room_type == RoomType.PUBLIC and not room.players and not room.spectators
            long_inactivity = current_time - room.last_activity > timedelta(seconds=SESSION_TIMEOUT)
            short_inactivity_empty_public = is_empty_public_room and (current_time - room.created_at > timedelta(minutes=15))
            if long_inactivity or short_inactivity_empty_public : rooms_to_delete.append(room_code)
        for room_code in rooms_to_delete:
            logger.info(f"Cleaning up inactive/empty room {room_code}")
            if room_code in self.rooms:
                room_to_del = self.rooms[room_code]
                all_user_ids_in_room = list(room_to_del.players.keys()) + list(room_to_del.spectators)
                for user_id in all_user_ids_in_room:
                    if user_id in self.connections:
                         logger.info(f"Removing player {user_id} from player_rooms due to room cleanup.")
                         if user_id in self.player_rooms: del self.player_rooms[user_id]
                del self.rooms[room_code]

    def get_game_state(self, room_code: str, player_id: str) -> dict:
        if room_code not in self.rooms: return {"error": "Room not found"}
        room = self.rooms[room_code]; is_player_in_room = player_id in room.players; is_spectator = player_id in room.spectators
        seated_players = room.get_seated_players(); current_player_obj = None
        if seated_players and 0 <= room.current_player_index < len(seated_players):
            current_player_id_at_table = seated_players[room.current_player_index].id
            current_player_obj = room.players.get(current_player_id_at_table)
        players_data = {}
        for pid, p_obj in room.players.items():
            is_this_player_current_actor = current_player_obj and current_player_obj.id == pid
            player_data = {"id":p_obj.id,"name":p_obj.name,"money":p_obj.money,"current_bet":p_obj.current_bet,"total_bet_this_hand":p_obj.total_bet_this_hand,"status":p_obj.status.value,"position":p_obj.position,"last_action":p_obj.last_action.value if p_obj.last_action else None,"avatar":p_obj.avatar,"color":p_obj.color,"is_dealer":p_obj.is_dealer,"is_small_blind":p_obj.is_small_blind,"is_big_blind":p_obj.is_big_blind,"time_bank":p_obj.time_bank,"is_current_player":is_this_player_current_actor,"tournament_rank":p_obj.tournament_rank,"is_ai":p_obj.is_ai,"stats":asdict(p_obj.stats)}
            show_cards = False
            if pid == player_id and not p_obj.is_ai: show_cards = True
            elif room.phase == GamePhase.SHOWDOWN:
                if p_obj.status != PlayerStatus.FOLDED or p_obj.is_all_in(): show_cards = True
            if show_cards and p_obj.cards: player_data["cards"] = [{"suit":c.suit,"rank":c.rank,"id":c.id} for c in p_obj.cards]
            elif p_obj.cards: player_data["cards"] = [{"suit":"back","rank":"back","id":f"back_{i}_{pid}"} for i in range(len(p_obj.cards))]
            else: player_data["cards"] = []
            players_data[pid] = player_data
        time_left_for_action = 0
        if current_player_obj and current_player_obj.status==PlayerStatus.ACTIVE and room.phase not in [GamePhase.WAITING,GamePhase.SHOWDOWN,GamePhase.GAME_OVER] and not room.paused :
            time_left_for_action = max(0, room.settings.auto_fold_timeout - (time.time()-room.last_action_time))
            if current_player_obj.is_ai: time_left_for_action = room.settings.auto_fold_timeout
        can_this_player_act = (is_player_in_room and current_player_obj and current_player_obj.id==player_id and not room.players[player_id].is_ai and room.phase not in [GamePhase.WAITING,GamePhase.SHOWDOWN,GamePhase.GAME_OVER] and not room.paused and room.players[player_id].status==PlayerStatus.ACTIVE)
        game_state = {"room_code":room.code,"room_name":room.name,"phase":room.phase.value,"pot":room.pot,"current_bet":room.current_bet,"min_raise":room.min_raise,"current_player_id_acting":current_player_obj.id if current_player_obj else None,"dealer_index":room.dealer_index,"players":players_data,"community_cards":[{"suit":c.suit,"rank":c.rank,"id":c.id} for c in room.community_cards],"chat_messages":room.chat_messages[-30:],"is_player":is_player_in_room,"is_spectator":is_spectator,"spectator_count":len(room.spectators),"hand_number":room.hand_number,"settings":{"small_blind":room.settings.small_blind,"big_blind":room.settings.big_blind,"ante":room.settings.ante,"max_players":room.settings.max_players,"game_mode":room.settings.game_mode.value,"auto_fold_timeout":room.settings.auto_fold_timeout},"tournament_info":{"level":room.tournament_level,"next_level_time":room.tournament_next_level.isoformat() if room.settings.game_mode==GameMode.TOURNAMENT else None} if room.settings.game_mode==GameMode.TOURNAMENT else None,"side_pots":[{"amount":sp.amount,"eligible_players_count":len(sp.eligible_players)} for sp in room.side_pots],"paused":room.paused,"pause_reason":room.pause_reason,"time_left_for_action":time_left_for_action,"can_act":can_this_player_act,"available_actions":self.get_available_actions(room,player_id) if can_this_player_act else [], "owner_id": room.owner_id}
        return game_state

    def get_available_actions(self, room: Room, player_id: str) -> List[Dict]:
        if player_id not in room.players: return []
        player = room.players[player_id]
        if not player.can_act() or player.is_ai : return []
        actions = []
        actions.append({"action": PlayerAction.FOLD.value, "label": "Fold"})
        bet_to_match = room.current_bet; player_current_round_bet = player.current_bet
        if player_current_round_bet == bet_to_match : actions.append({"action":PlayerAction.CHECK.value,"label":"Check"})
        else:
            amount_to_call = bet_to_match - player_current_round_bet
            if amount_to_call > 0:
                actual_call_amount = min(amount_to_call, player.money)
                actions.append({"action":PlayerAction.CALL.value,"label":f"Call ${actual_call_amount}"+(" (All-in)" if actual_call_amount==player.money else ""),"amount":actual_call_amount})
        money_after_call = player.money - max(0, bet_to_match - player_current_round_bet)
        if money_after_call > 0 :
            min_raise_by = room.min_raise; max_raise_by = money_after_call
            if max_raise_by >= min_raise_by : actions.append({"action":PlayerAction.RAISE.value,"label":"Raise","min_amount":min_raise_by,"max_amount":max_raise_by})
        if player.money > 0:
            is_call_all_in = any(a['action']==PlayerAction.CALL.value and a['amount']==player.money for a in actions)
            if not is_call_all_in: actions.append({"action":PlayerAction.ALL_IN.value,"label":f"All-In ${player.money}","amount":player.money})
        return actions

    def get_room_list(self) -> List[Dict]:
        rooms_data = []
        for room_code, room in self.rooms.items():
            if room.room_type == RoomType.PUBLIC:
                human_players = len([p for p in room.players.values() if not p.is_ai])
                ai_players = len([p for p in room.players.values() if p.is_ai])
                rooms_data.append({"code":room_code,"name":room.name,"players":f"{human_players}H + {ai_players}AI","max_players":room.settings.max_players,"spectators":len(room.spectators),"phase":room.phase.value,"game_mode":room.settings.game_mode.value,"small_blind":room.settings.small_blind,"big_blind":room.settings.big_blind,"created_at":room.created_at.isoformat(),"has_password":bool(room.settings.password)})
        return sorted(rooms_data, key=lambda r: r['created_at'], reverse=True)

game = AdvancedPokerGame()

class WSMessage(BaseModel):
    action: str
    payload: dict = Field(default_factory=dict)

class CreateRoomRequest(BaseModel):
    player_name: str = "Anonymous"
    room_name: str = ""
    game_mode: str = GameMode.CASH_GAME.value
    small_blind: int = SMALL_BLIND
    big_blind: int = BIG_BLIND
    max_players: int = MAX_PLAYERS_PER_ROOM
    buy_in: int = 0
    password: Optional[str] = None
    num_ai_players: int = Field(default=0, ge=0, le=MAX_AI_PLAYERS)

@asynccontextmanager
async def lifespan(app: FastAPI):
    logger.info("Starting advanced poker game server...")
    game_task = asyncio.create_task(game_loop())
    cleanup_task = asyncio.create_task(cleanup_loop())
    yield
    logger.info("Shutting down poker game server...")
    game.running = False; game_task.cancel(); cleanup_task.cancel()
    try: await game_task; await cleanup_task
    except asyncio.CancelledError: logger.info("Background tasks cancelled.")

app = FastAPI(title="Advanced 3D Multiplayer Poker", description="Professional casino-quality poker game", version="2.0.2", lifespan=lifespan)
app.add_middleware(CORSMiddleware, allow_origins=["*"], allow_credentials=True, allow_methods=["*"], allow_headers=["*"])

async def game_loop():
    while game.running:
        try:
            current_time = time.time()
            for room_code, room in list(game.rooms.items()):
                if room.phase not in [GamePhase.WAITING,GamePhase.SHOWDOWN,GamePhase.GAME_OVER] and not room.paused:
                    seated_players = room.get_seated_players()
                    if seated_players and 0 <= room.current_player_index < len(seated_players):
                        current_player_at_table = seated_players[room.current_player_index]
                        current_player_obj = room.players.get(current_player_at_table.id)
                        if current_player_obj and not current_player_obj.is_ai and current_player_obj.status==PlayerStatus.ACTIVE:
                            if current_time-room.last_action_time > room.settings.auto_fold_timeout:
                                logger.info(f"Auto-folding player {current_player_obj.name} in room {room_code} due to timeout.")
                                game.player_action(room_code,current_player_obj.id,PlayerAction.FOLD)
            for room_code, room in list(game.rooms.items()):
                connected_user_ids_in_room = set()
                for pid,p in room.players.items():
                    if p.connection_id and pid in game.connections: connected_user_ids_in_room.add(pid)
                for spec_id in room.spectators:
                    if spec_id in game.connections: connected_user_ids_in_room.add(spec_id)
                for user_id in list(connected_user_ids_in_room):
                    ws_conn = game.connections.get(user_id)
                    if ws_conn:
                        try:
                            game_state_for_user = game.get_game_state(room_code,user_id)
                            await ws_conn.send_json({"type":"game_state","data":game_state_for_user})
                        except WebSocketDisconnect:
                            logger.warning(f"WebSocketDisconnect broadcasting {user_id} in {room_code}. Cleaning up.")
                            game.leave_room(user_id)
                        except Exception as e:
                            logger.error(f"Error broadcasting state to {user_id}: {e}")
                            if user_id in game.connections: del game.connections[user_id]
                            game.leave_room(user_id)
            await asyncio.sleep(1.0/GAME_UPDATE_RATE)
        except asyncio.CancelledError: logger.info("Game loop cancelled."); break
        except Exception as e: logger.exception(f"Critical error in game loop: {e}"); await asyncio.sleep(1.0)

async def cleanup_loop():
    while game.running:
        try:
            await asyncio.sleep(300)
            game.cleanup_inactive_rooms()
            logger.info("Ran cleanup task for inactive rooms.")
        except asyncio.CancelledError: logger.info("Cleanup loop cancelled."); break
        except Exception as e: logger.exception(f"Error in cleanup loop: {e}")

@app.get("/", response_class=HTMLResponse)
async def get_poker_game_html(): return HTMLResponse(content=ADVANCED_HTML_TEMPLATE)
@app.get("/api/rooms")
async def http_get_rooms(): return {"rooms": game.get_room_list()}
@app.get("/api/stats")
async def http_get_stats(): return {"global_stats":game.global_stats,"active_rooms":len(game.rooms),"connected_players":len([cid for cid,ws in game.connections.items() if game.player_rooms.get(cid)])}

@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    player_id = str(uuid.uuid4())
    await websocket.accept()
    game.connections[player_id] = websocket
    logger.info(f"Player {player_id} connected via WebSocket.")
    try:
        await websocket.send_json({"type":"connected","data":{"player_id":player_id,"server_info":{"version":"2.0.2"}}})
        while True:
            data = await websocket.receive_text()
            if not game.check_rate_limit(player_id,"message"):
                await websocket.send_json({"type":"error","message":"Message rate limit exceeded. Slow down."}); continue
            try:
                message = WSMessage.model_validate_json(data)
                await handle_websocket_message(websocket, player_id, message)
            except ValidationError as e: await websocket.send_json({"type":"error","message":f"Invalid message: {e}"})
            except Exception as e: logger.exception(f"Error processing WebSocket message from {player_id}: {e}"); await websocket.send_json({"type":"error","message":"Server error processing your request."})
    except WebSocketDisconnect: logger.info(f"Player {player_id} WebSocket disconnected.")
    except Exception as e: logger.exception(f"Unexpected error in WebSocket handler for {player_id}: {e}")
    finally:
        logger.info(f"Cleaning up for player {player_id}.")
        if player_id in game.connections: del game.connections[player_id]
        game.leave_room(player_id); logger.info(f"Player {player_id} fully cleaned up.")

async def handle_websocket_message(websocket: WebSocket, player_id: str, message: WSMessage):
    action = message.action; payload = message.payload
    current_room_code = game.player_rooms.get(player_id)
    try:
        if action == "create_room":
            player_name=payload.get("player_name",f"Player_{player_id[:6]}"); num_ai=int(payload.get("num_ai_players",0)); num_ai=max(0,min(num_ai,MAX_AI_PLAYERS))
            room_settings = GameSettings(small_blind=int(payload.get("small_blind",SMALL_BLIND)),big_blind=int(payload.get("big_blind",BIG_BLIND)),max_players=min(int(payload.get("max_players",MAX_PLAYERS_PER_ROOM)),MAX_PLAYERS_PER_ROOM),game_mode=GameMode(payload.get("game_mode","cash_game")),buy_in=int(payload.get("buy_in",0)),password=payload.get("password") if payload.get("password") else None)
            if 1+num_ai > room_settings.max_players: await websocket.send_json({"type":"error","message":f"Max players ({room_settings.max_players}) too low for you + {num_ai} AI."}); return
            new_room_code = game.create_room(player_id,room_settings,payload.get("room_name",""),num_ai_players=num_ai)
            if game.join_room(new_room_code,player_id,player_name): await websocket.send_json({"type":"room_created","data":{"room_code":new_room_code,"room_name":game.rooms[new_room_code].name}})
            else: await websocket.send_json({"type":"error","message":"Failed to join the room after creation."})
        elif action == "join_room":
            rtc=payload.get("room_code","").upper(); pntj=payload.get("player_name",f"Player_{player_id[:6]}"); ptoj=payload.get("password","")
            if game.join_room(rtc,player_id,pntj,ptoj): await websocket.send_json({"type":"room_joined","data":{"room_code":rtc}})
            else: await websocket.send_json({"type":"error","message":"Failed to join room. Invalid code, password, or room full."})
        elif action == "leave_room":
            if current_room_code: game.leave_room(player_id); await websocket.send_json({"type":"room_left","data":{"room_code":current_room_code}})
            else: await websocket.send_json({"type":"error","message":"You are not in a room."})
        elif action == "spectate":
            rtc_spec = payload.get("room_code", "").upper()
            pwd_spec = payload.get("password", "")
            if game.spectate_room(rtc_spec, player_id, pwd_spec):
                await websocket.send_json({"type": "spectating", "data": {"room_code": rtc_spec}})
            else:
                await websocket.send_json({"type": "error", "message": "Failed to spectate room"})
        elif action == "start_game":
            if current_room_code and game.rooms[current_room_code].owner_id == player_id:
                if not game.start_game(current_room_code): await websocket.send_json({"type":"error","message":"Cannot start game (e.g., not enough players)."})
            elif not current_room_code: await websocket.send_json({"type":"error","message":"Not in a room."})
            else: await websocket.send_json({"type":"error","message":"Only room owner can start game."})
        elif action == "player_action":
            if not current_room_code: await websocket.send_json({"type":"error","message":"Not in a room."}); return
            if not game.check_rate_limit(player_id,"action"): await websocket.send_json({"type":"error","message":"Action rate limit exceeded. Please wait."}); return
            action_type_str=payload.get("action_type"); action_amount=int(payload.get("amount",0))
            try:
                poker_action_enum = PlayerAction(action_type_str)
                if not game.player_action(current_room_code,player_id,poker_action_enum,action_amount):
                    game_state_now = game.get_game_state(current_room_code, player_id)
                    available_now = game_state_now.get("available_actions", [])
                    await websocket.send_json({"type":"error","message":"Invalid action or not your turn.","debug_available_actions":available_now})
            except ValueError: await websocket.send_json({"type":"error","message":"Unknown action type."})
        elif action == "send_chat":
            if not current_room_code: await websocket.send_json({"type":"error","message":"Not in a room to chat."}); return
            message_text=payload.get("message","")
            if 0 < len(message_text.strip()) <= 200: game.add_chat_message(current_room_code,player_id,message_text.strip())
            elif len(message_text.strip()) > 200: await websocket.send_json({"type":"error","message":"Chat message too long (max 200 chars)."})
        elif action == "get_room_list": await websocket.send_json({"type":"room_list","data":{"rooms":game.get_room_list()}})
        elif action == "get_hand_history":
            if current_room_code and current_room_code in game.rooms:
                room = game.rooms[current_room_code]
                await websocket.send_json({"type": "hand_history", "data": {"history": room.hand_history[-10:]}}) # Send last 10
            else: await websocket.send_json({"type":"error", "message": "Not in a room to get hand history."})
        elif action == "pause_game":
             if current_room_code and current_room_code in game.rooms:
                room = game.rooms[current_room_code]
                if room.owner_id == player_id :
                    room.paused = not room.paused
                    room.pause_reason = "Paused by room owner" if room.paused else ""
                    logger.info(f"Room {current_room_code} {'paused' if room.paused else 'resumed'} by owner {player_id}.")
                else: await websocket.send_json({"type":"error", "message": "Only room owner can pause/resume."})
             else: await websocket.send_json({"type":"error", "message": "Not in a room."})
        else: await websocket.send_json({"type":"error","message":f"Unknown action: {action}"})
    except Exception as e: logger.exception(f"Error handling WebSocket action '{action}' for player {player_id}: {e}"); await websocket.send_json({"type":"error","message":f"Server error processing action '{action}'."})

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
            --primary-gold: #ffd700; --secondary-gold: #ffed4e; --dark-green: #0a2a1f; --light-green: #1a5d3a;
            --casino-red: #dc143c; --casino-blue: #191970; --text-light: #ffffff; --text-dark: #333333; --shadow: rgba(0,0,0,0.3);
        }
        * { margin:0; padding:0; box-sizing:border-box; }
        body { font-family:'Roboto',sans-serif; background:radial-gradient(ellipse at center,#0a2a1f 0%,#051a11 100%); color:var(--text-light); overflow:hidden; user-select:none; }
        #gameContainer { position:relative; width:100vw; height:100vh; }
        #canvas { display:block; cursor:grab; } #canvas:active { cursor:grabbing; }
        #loadingScreen { position:fixed; top:0; left:0; width:100%; height:100%; background:linear-gradient(135deg,#0a2a1f,#051a11); display:flex; flex-direction:column; justify-content:center; align-items:center; z-index:10000; transition:opacity 1s ease-out; }
        .loading-logo { font-family:'Orbitron',monospace; font-size:clamp(2rem,10vw,4rem); font-weight:900; color:var(--primary-gold); text-shadow:0 0 30px rgba(255,215,0,0.8); margin-bottom:30px; animation:pulse 2s infinite; }
        .loading-spinner { width:80px; height:80px; border:4px solid rgba(255,215,0,0.3); border-top:4px solid var(--primary-gold); border-radius:50%; animation:spin 1s linear infinite; margin-bottom:20px; }
        .loading-text { font-size:1.2rem; color:var(--text-light); opacity:0.8; }
        @keyframes pulse { 0%,100% {transform:scale(1);} 50% {transform:scale(1.05);} } @keyframes spin { 0% {transform:rotate(0deg);} 100% {transform:rotate(360deg);} }
        .ui-overlay { position:absolute; top:0; left:0; width:100%; height:100%; pointer-events:none; z-index:100; }
        .ui-panel { position:absolute; background:linear-gradient(135deg,rgba(0,0,0,0.9),rgba(26,93,58,0.8)); border-radius:15px; padding:20px; color:var(--text-light); pointer-events:auto; border:2px solid var(--primary-gold); box-shadow:0 10px 30px var(--shadow); backdrop-filter:blur(10px); transition:all 0.3s ease; }
        .ui-panel:hover:not(.modal-content) { transform:translateY(-2px); box-shadow:0 15px 40px var(--shadow); } /* Added :not modal for hover */
        .menu-panel { top:50%; left:50%; transform:translate(-50%,-50%); text-align:center; min-width:320px; width:clamp(320px, 90vw, 500px); max-height:90vh; overflow-y:auto; }
        .menu-title { font-family:'Orbitron',monospace; font-size:clamp(2rem,8vw,3rem); font-weight:900; color:var(--primary-gold); text-shadow:0 0 20px rgba(255,215,0,0.8); margin-bottom:30px; animation:glow 2s ease-in-out infinite alternate; }
        @keyframes glow { from {text-shadow:0 0 20px rgba(255,215,0,0.8);} to {text-shadow:0 0 30px rgba(255,215,0,1),0 0 40px rgba(255,215,0,0.8);} }
        .menu-section { margin-bottom:20px; padding:15px; background:rgba(255,255,255,0.05); border-radius:10px; border:1px solid rgba(255,215,0,0.3); }
        .menu-section h3 { color:var(--secondary-gold); margin-bottom:10px; font-size:1.1rem; }
        .game-hud { top:15px; left:15px; max-width:300px; max-height:calc(100vh - 30px - 120px); overflow-y:auto; }
        .hud-item { display:flex; justify-content:space-between; align-items:center; margin-bottom:8px; padding:6px 10px; background:rgba(255,255,255,0.1); border-radius:8px; border-left:3px solid var(--primary-gold); font-size:0.9rem;}
        .hud-label { font-weight:500; color:var(--secondary-gold); margin-right:5px;} .hud-value { font-weight:700; color:var(--text-light); }
        .pot-display { position:absolute; top:12%; left:50%; transform:translateX(-50%); background:radial-gradient(circle,rgba(255,215,0,0.9),rgba(255,237,78,0.7)); color:var(--text-dark); padding:20px; border-radius:50%; border:3px solid var(--primary-gold); font-family:'Orbitron',monospace; font-size:1.5rem; font-weight:900; text-align:center; min-width:120px; min-height:120px; display:flex; flex-direction:column; justify-content:center; align-items:center; box-shadow:0 0 30px rgba(255,215,0,0.6); animation:potGlow 3s ease-in-out infinite; }
        @keyframes potGlow { 0%,100% {box-shadow:0 0 30px rgba(255,215,0,0.6);} 50% {box-shadow:0 0 50px rgba(255,215,0,0.9);} }
        .actions-panel { bottom:20px; left:50%; transform:translateX(-50%); display:flex; gap:10px; flex-wrap:wrap; justify-content:center; max-width:calc(100vw - 40px); padding:5px; }
        .action-button { background:linear-gradient(135deg,var(--primary-gold),var(--secondary-gold)); border:none; border-radius:10px; padding:10px 18px; color:var(--text-dark); font-weight:700; font-size:0.9rem; cursor:pointer; transition:all 0.2s ease; box-shadow:0 4px 12px rgba(255,215,0,0.25); position:relative; overflow:hidden; }
        .action-button:hover { transform:translateY(-2px); box-shadow:0 6px 20px rgba(255,215,0,0.4); } .action-button:active { transform:translateY(-1px); }
        .action-button:disabled { background:linear-gradient(135deg,#555,#777); cursor:not-allowed; transform:none; opacity:0.6; box-shadow:none; }
        .action-button.fold { background:linear-gradient(135deg,var(--casino-red),#ff6b6b); color:white; }
        .action-button.call { background:linear-gradient(135deg,#28a745,#20c997); color:white; }
        .action-button.raise { background:linear-gradient(135deg,var(--casino-blue),#6c5ce7); color:white;}
        .action-button.all-in { background:linear-gradient(135deg,#ff4757,#ff3742); animation:allInPulse 1s infinite; color:white; }
        @keyframes allInPulse { 0%,100% {box-shadow:0 5px 15px rgba(255,71,87,0.3);} 50% {box-shadow:0 5px 25px rgba(255,71,87,0.6);} }
        .raise-controls { display:flex; align-items:center; gap:8px; background:rgba(255,255,255,0.08); padding:8px; border-radius:8px; }
        .raise-slider { flex:1; -webkit-appearance:none; appearance:none; height:6px; background:rgba(255,255,255,0.25); border-radius:3px; outline:none; }
        .raise-slider::-webkit-slider-thumb { -webkit-appearance:none; appearance:none; width:18px; height:18px; background:var(--primary-gold); border-radius:50%; cursor:pointer; }
        .chat-panel { top:15px; right:15px; width:clamp(280px, 30vw, 320px); max-height:calc(100vh - 30px - 120px); display:flex; flex-direction:column; }
        .chat-header { display:flex; justify-content:space-between; align-items:center; margin-bottom:10px; padding-bottom:8px; border-bottom:2px solid var(--primary-gold); }
        .chat-title { font-family:'Orbitron',monospace; font-weight:700; color:var(--primary-gold); font-size:1.1rem;}
        .chat-toggle { background:none; border:1px solid var(--primary-gold); color:var(--primary-gold); border-radius:5px; padding:4px 8px; cursor:pointer; transition:all 0.3s ease; font-size:0.8rem; }
        .chat-toggle:hover { background:var(--primary-gold); color:var(--text-dark); }
        #chatMessages { flex:1; overflow-y:auto; background:rgba(255,255,255,0.04); border-radius:8px; padding:10px; margin-bottom:10px; border:1px solid rgba(255,215,0,0.15); min-height:50px; font-size:0.85rem; }
        .chat-message { margin-bottom:8px; padding:6px 10px; border-radius:6px; background:rgba(255,255,255,0.08); border-left:3px solid; animation:slideInChat 0.3s ease-out; word-wrap:break-word; }
        @keyframes slideInChat { from {opacity:0;transform:translateX(15px);} to {opacity:1;transform:translateX(0);} }
        .chat-player-name { font-weight:700; margin-right:5px; } .chat-timestamp { font-size:0.75rem; opacity:0.7; float:right; }
        .chat-input-container { display:flex; gap:8px; margin-top:auto; }
        .player-cards { position:absolute; bottom:80px; left:50%; transform:translateX(-50%); display:flex; gap:15px; flex-wrap:wrap; justify-content:center; max-width:calc(100vw - 30px); }
        .player-card { background:linear-gradient(135deg,rgba(26,93,58,0.85),rgba(10,42,31,0.85)); border:2px solid var(--primary-gold); border-radius:12px; padding:10px 12px; text-align:center; min-width:130px; max-width: 160px; position:relative; transition:all 0.3s ease; backdrop-filter:blur(8px); font-size:0.9rem;}
        .player-card.current-player { border-color:var(--casino-red); box-shadow:0 0 25px rgba(220,20,60,0.5); animation:currentPlayerGlow 1.5s ease-in-out infinite alternate; }
        @keyframes currentPlayerGlow { from {box-shadow:0 0 25px rgba(220,20,60,0.5);} to {box-shadow:0 0 35px rgba(220,20,60,0.8);} }
        .player-card.folded { opacity:0.5; filter:grayscale(70%); transform:scale(0.95); }
        .player-card.all-in { border-color:var(--casino-red); animation:allInGlow 1s ease-in-out infinite alternate; }
        @keyframes allInGlow { from {box-shadow:0 0 15px rgba(255,71,87,0.3);} to {box-shadow:0 0 25px rgba(255,71,87,0.6);} }
        .player-avatar { width:40px; height:40px; border-radius:50%; background:var(--primary-gold); margin:0 auto 8px; display:flex; align-items:center; justify-content:center; font-size:1.3rem; font-weight:700; color:var(--text-dark); }
        .player-name { font-weight:700; color:var(--text-light); margin-bottom:4px; white-space:nowrap; overflow:hidden; text-overflow:ellipsis; max-width:100%; }
        .player-money { color:var(--primary-gold); font-weight:700; font-family:'Orbitron',monospace; font-size:0.95rem; }
        .player-action { position:absolute; top:-8px; right:-8px; background:var(--casino-red); color:var(--text-light); padding:3px 7px; border-radius:10px; font-size:0.7rem; font-weight:700; animation:actionPop 0.4s ease-out; }
        @keyframes actionPop { 0% {transform:scale(0);} 80% {transform:scale(1.15);} 100% {transform:scale(1);} }
        input,select { padding:10px 12px; border:2px solid var(--primary-gold); border-radius:8px; background:rgba(255,255,255,0.1); color:var(--text-light); font-size:0.9rem; transition:all 0.2s ease; backdrop-filter:blur(8px); width:100%;} /* Ensure full width for grid */
        input:focus,select:focus { outline:none; border-color:var(--secondary-gold); box-shadow:0 0 12px rgba(255,215,0,0.25); }
        input::placeholder { color:rgba(255,255,255,0.5); } select option { background-color:var(--dark-green); color:var(--text-light); }
        ::-webkit-scrollbar { width:6px; } ::-webkit-scrollbar-track { background:rgba(255,255,255,0.08); border-radius:3px; }
        ::-webkit-scrollbar-thumb { background:var(--primary-gold); border-radius:3px; } ::-webkit-scrollbar-thumb:hover { background:var(--secondary-gold); }
        @media (max-width:768px) { /* Further refined responsive */
            .menu-panel { padding:15px; font-size:0.9rem;} .menu-title { font-size:clamp(1.8rem,7vw,2.5rem); } .menu-section { padding:12px; }
            .action-button { padding:9px 15px; font-size:0.85rem; }
            .game-hud { max-width:calc(50vw - 25px); padding:8px; font-size:0.85rem;}
            .hud-item { padding:5px 8px; margin-bottom:6px; } .game-hud .action-button { padding:8px 10px; font-size:0.75rem; }
            .chat-panel { width:calc(50vw - 25px); padding:8px; font-size:0.85rem;} #chatMessages {padding:8px; font-size:0.8rem;}
            .player-card { min-width:110px; padding:8px; font-size:0.85rem; } .player-avatar {width:35px; height:35px; font-size:1.1rem;}
            .pot-display {font-size:1.3rem; padding:15px; min-width:100px; min-height:100px;}
            .actions-panel {gap:8px;} input, select{font-size:0.85rem; padding: 8px 10px;}
        }
        .hidden {display:none!important;} .fade-in {animation:fadeIn 0.5s ease-out;} .fade-out {animation:fadeOut 0.5s ease-out;}
        @keyframes fadeIn {from{opacity:0;}to{opacity:1;}} @keyframes fadeOut {from{opacity:1;}to{opacity:0;}}
        .tournament-info {position:absolute;top:15px;left:50%;transform:translateX(-50%);background:linear-gradient(135deg,rgba(25,25,112,0.9),rgba(138,43,226,0.8));border:2px solid var(--primary-gold);border-radius:10px;padding:10px 20px;text-align:center;backdrop-filter:blur(8px);z-index:101;}
        .tournament-level {font-family:'Orbitron',monospace;font-size:1.1rem;font-weight:700;color:var(--primary-gold);margin-bottom:4px;}
        .tournament-timer {color:var(--text-light);font-size:0.85rem;}
        .notification {position:fixed;top:15px;right:15px;background:linear-gradient(135deg,rgba(40,167,69,0.9),rgba(32,201,151,0.9));color:var(--text-light);padding:12px 18px;border-radius:8px;border-left:4px solid var(--primary-gold);box-shadow:0 4px 12px var(--shadow);z-index:9999;animation:slideInNotification 0.4s ease-out;max-width:280px;pointer-events:auto;font-size:0.9rem;}
        .notification.error {background:linear-gradient(135deg,rgba(220,20,60,0.9),rgba(255,107,107,0.9));}
        .notification.warning {background:linear-gradient(135deg,rgba(255,193,7,0.9),rgba(255,235,59,0.9));color:var(--text-dark);}
        @keyframes slideInNotification {from{transform:translateX(100%);opacity:0;}to{transform:translateX(0);opacity:1;}}
        .modal {position:fixed;top:0;left:0;width:100%;height:100%;background:rgba(0,0,0,0.85);display:flex;justify-content:center;align-items:center;z-index:9998;pointer-events:auto;}
        .modal-content {background:linear-gradient(135deg,rgba(10,42,31,0.95),rgba(26,93,58,0.95));border:2px solid var(--primary-gold);border-radius:15px;padding:25px;max-width:calc(100vw - 40px);width:600px;max-height:85vh;overflow-y:auto;backdrop-filter:blur(12px);}
        .modal-header {display:flex;justify-content:space-between;align-items:center;margin-bottom:18px;padding-bottom:12px;border-bottom:2px solid var(--primary-gold);}
        .modal-title {font-family:'Orbitron',monospace;font-size:1.4rem;font-weight:700;color:var(--primary-gold);}
        .modal-close {background:none;border:2px solid var(--casino-red);color:var(--casino-red);border-radius:6px;padding:7px 12px;cursor:pointer;font-weight:700;transition:all 0.2s ease;font-size:0.9rem;}
        .modal-close:hover {background:var(--casino-red);color:var(--text-light);}
        #actionTimer {position:absolute;top:22%;left:50%;transform:translateX(-50%);background:rgba(220,20,60,0.85);color:white;padding:8px 18px;border-radius:20px;font-family:'Orbitron',monospace;font-weight:700;font-size:1.1rem;animation:timerPulse 1s infinite alternate;z-index:101;}
        @keyframes timerPulse {from{transform:translateX(-50%) scale(1);}to{transform:translateX(-50%) scale(1.05);}}
    </style>
</head>
<body>
    <div id="loadingScreen"><div class="loading-logo">🎰 ROYAL POKER 3D</div><div class="loading-spinner"></div><div class="loading-text">Loading casino experience...</div></div>
    <div id="gameContainer"><canvas id="canvas"></canvas><div class="ui-overlay">
        <div id="menuPanel" class="ui-panel menu-panel hidden">
            <h1 class="menu-title">🎰 ROYAL POKER 3D 🎰</h1>
            <div class="menu-section"><h3>Player Setup</h3><input type="text" id="playerName" placeholder="Enter your name" value="Player" style="width:100%;margin-bottom:10px;"></div>
            <div class="menu-section"><h3>Quick Play</h3><div style="display:flex;flex-direction:column;gap:12px;"><button class="action-button" onclick="createQuickRoom()">🎯 Create Quick Room</button><div style="display:flex;gap:8px;"><input type="text" id="roomCode" placeholder="Room Code" style="flex:1;"><button class="action-button" onclick="joinRoom()">🚪 Join</button></div><button class="action-button" onclick="spectateRoom()">👁️ Spectate</button></div></div>
            <div class="menu-section"><h3>Custom Game</h3><div style="display:grid;grid-template-columns:1fr 1fr;gap:12px 10px;margin-bottom:12px;">
                <div><label style="display:block;font-size:0.8rem;margin-bottom:3px;">Game Mode:</label><select id="gameMode" style="width:100%;"><option value="cash_game">Cash Game</option><option value="tournament">Tournament</option><option value="sit_and_go">Sit & Go</option></select></div>
                <div><label style="display:block;font-size:0.8rem;margin-bottom:3px;">Max Players:</label><input type="number" id="maxPlayers" min="2" max="10" value="8" style="width:100%;"></div>
                <div><label style="display:block;font-size:0.8rem;margin-bottom:3px;">Small Blind:</label><input type="number" id="smallBlind" min="1" value="25" step="5" style="width:100%;"></div>
                <div><label style="display:block;font-size:0.8rem;margin-bottom:3px;">Big Blind:</label><input type="number" id="bigBlind" min="2" value="50" step="5" style="width:100%;"></div>
                <div><label style="display:block;font-size:0.8rem;margin-bottom:3px;">Buy-in:</label><input type="number" id="buyIn" min="0" value="1000" step="100" style="width:100%;"></div>
                <div><label style="display:block;font-size:0.8rem;margin-bottom:3px;">AI Players:</label><input type="number" id="numAiPlayers" min="0" max="7" value="0" style="width:100%;"></div>
                <div style="grid-column:span 2;"><label style="display:block;font-size:0.8rem;margin-bottom:3px;">Password (Optional):</label><input type="password" id="roomPassword" placeholder="Leave empty for public" style="width:100%;"></div>
            </div><input type="text" id="roomName" placeholder="Room Name (Optional)" style="width:100%;margin-bottom:12px;"><button class="action-button" onclick="createCustomRoom()">🎪 Create Custom Room</button></div>
            <div class="menu-section"><h3>Browse Rooms</h3><button class="action-button" onclick="showRoomList()">🏛️ Browse Public Rooms</button></div>
            <div style="margin-top:15px;font-size:0.8rem;color:#bbb;text-align:center;">Starting: $1,000 | Blinds: $25/$50<br>Tournaments | Up to 10 players</div>
        </div>
        <div id="roomListModal" class="modal hidden"><div class="modal-content"><div class="modal-header"><h2 class="modal-title">🏛️ Public Rooms</h2><button class="modal-close" onclick="hideRoomList()">✕</button></div><div id="roomListContainer" style="max-height:60vh;overflow-y:auto;"><div id="roomList" style="text-align:center;color:#ccc;padding:20px;">Loading rooms...</div></div><div style="margin-top:15px;text-align:center;"><button class="action-button" onclick="refreshRoomList()">🔄 Refresh</button></div></div></div>
        <div id="gameHUD" class="ui-panel game-hud hidden">
            <div class="hud-item"><span class="hud-label">Room:</span><span class="hud-value" id="currentRoom">-</span></div>
            <div class="hud-item"><span class="hud-label">Phase:</span><span class="hud-value" id="phaseText">Waiting</span></div>
            <div class="hud-item"><span class="hud-label">My $:</span><span class="hud-value" id="myMoneyAmount">0</span></div>
            <div class="hud-item"><span class="hud-label">Call:</span><span class="hud-value" id="betToMatch">0</span></div>
            <div class="hud-item"><span class="hud-label">Hand:</span><span class="hud-value" id="handNumber">0</span></div>
            <div style="margin-top:15px;display:flex;flex-direction:column;gap:8px;"><button class="action-button" onclick="startGame()" id="startGameBtn" style="width:100%;">🚀 Start Game</button><button class="action-button" onclick="showHandHistory()" id="handHistoryBtn" style="width:100%;">📊 History</button><button class="action-button" onclick="pauseGame()" id="pauseGameBtn" style="width:100%;">⏸️ Pause</button><button class="action-button fold" onclick="leaveRoom()" style="width:100%;">🚪 Leave</button></div>
        </div>
        <div id="tournamentInfo" class="tournament-info hidden"><div class="tournament-level">🏆 Level <span id="tournamentLevel">1</span></div><div class="tournament-timer">Next: <span id="tournamentTimer">10:00</span></div><div style="font-size:0.8rem;">Blinds: $<span id="tournamentBlinds">25/50</span></div></div>
        <div id="potDisplay" class="pot-display hidden"><div style="font-size:0.9rem;margin-bottom:3px;">POT</div><div>$<span id="potAmount">0</span></div><div id="sidePots" style="font-size:0.7rem;margin-top:3px;color:rgba(0,0,0,0.65);"></div></div>
        <div id="actionTimer" class="hidden">⏰ <span id="timerSeconds">30</span>s</div>
        <div id="actionsPanel" class="actions-panel hidden">
            <button class="action-button fold" onclick="playerAction('fold')" id="foldBtn">🚫 Fold</button>
            <button class="action-button" onclick="playerAction('check')" id="checkBtn">✅ Check</button>
            <button class="action-button call" onclick="playerAction('call')" id="callBtn">📞 Call $<span id="callAmount">0</span></button>
            <div id="raiseControlsContainer" class="raise-controls" style="display:none;"><span style="color:var(--primary-gold);font-weight:700;font-size:0.85rem;">Raise By:</span><input type="range" id="raiseSlider" class="raise-slider" oninput="updateRaiseAmountDisplay()" onchange="updateRaiseAmountDisplay()"><input type="number" id="raiseAmountInput" style="width:70px;font-size:0.85rem;padding:6px 8px;" oninput="updateRaiseSliderFromInput()"><button class="action-button raise" onclick="playerAction('raise')" id="raiseBtn">📈 Raise</button></div>
            <button class="action-button all-in" onclick="playerAction('all_in')" id="allInBtn">🔥 ALL IN</button>
        </div>
        <div id="chatPanel" class="chat-panel hidden"><div class="chat-header"><h3 class="chat-title">💬 Chat</h3><button class="chat-toggle" onclick="toggleChat()" id="chatToggle">−</button></div><div id="chatMessages"></div><div class="chat-input-container"><input type="text" id="chatInput" placeholder="Type message..." style="flex:1;" onkeypress="if(event.key==='Enter') sendChat()" maxlength="200"><button class="action-button" onclick="sendChat()" style="padding:10px 12px;">Send</button></div></div>
        <div id="playerCards" class="player-cards hidden"></div>
        <div id="handHistoryModal" class="modal hidden"><div class="modal-content"><div class="modal-header"><h2 class="modal-title">📊 Hand History</h2><button class="modal-close" onclick="hideHandHistory()">✕</button></div><div id="handHistoryContentContainer" style="max-height:60vh;overflow-y:auto;"><div id="handHistoryContent" style="text-align:center;color:#ccc;padding:20px;">No hands played yet.</div></div></div></div>
    </div></div>
    <script>
        let ws = null, scene, camera, renderer, tableGroup;
        let playerPositions3D = [], cardMaterials = {}, chipMaterials = {};
        let gameState = null, myPlayerId = null, isConnected = false, currentRoomCode = null;
        let cameraAnimating = false, uiActive = false;
        let tableCards3D = [], playerCardObjects3D = {}, chipStacks3D = [];
        let initialConnectionNotified = false, connectionLostNotified = false, lastPauseReasonNotified = "";
        let chatCollapsed = false;

        function updateUiActiveState() {
            uiActive = !document.getElementById('menuPanel').classList.contains('hidden') || 
                       !document.getElementById('roomListModal').classList.contains('hidden') || 
                       !document.getElementById('handHistoryModal').classList.contains('hidden');
        }
        function initThreeJS() {
            const canvas=document.getElementById('canvas'); scene=new THREE.Scene(); scene.fog=new THREE.Fog(0x051a11,15,50); setupLighting(); camera=new THREE.PerspectiveCamera(75,window.innerWidth/window.innerHeight,0.1,1000); camera.position.set(0,12,15); camera.lookAt(0,0,0); renderer=new THREE.WebGLRenderer({canvas:canvas,antialias:true,alpha:true,powerPreference:"high-performance"}); renderer.setSize(window.innerWidth,window.innerHeight); renderer.setPixelRatio(Math.min(window.devicePixelRatio,2)); renderer.shadowMap.enabled=true; renderer.shadowMap.type=THREE.PCFSoftShadowMap; renderer.toneMapping=THREE.ACESFilmicToneMapping; renderer.toneMappingExposure=1.1;
            createCasinoEnvironment(); createPokerTable3D(); createCardMaterials(); createChipMaterials(); addMouseCameraControls(); animate();
        }
        function setupLighting(){const amb=new THREE.AmbientLight(0x404040,0.6);scene.add(amb);const mainL=new THREE.DirectionalLight(0xffffff,1.0);mainL.position.set(5,15,5);mainL.castShadow=true;mainL.shadow.mapSize.width=2048;mainL.shadow.mapSize.height=2048;mainL.shadow.camera.near=0.5;mainL.shadow.camera.far=50;mainL.shadow.camera.left=-15;mainL.shadow.camera.right=15;mainL.shadow.camera.top=15;mainL.shadow.camera.bottom=-15;scene.add(mainL);const spotL=new THREE.SpotLight(0xffd700,0.9,30,Math.PI/3.5,0.4,1);spotL.position.set(0,9,0);spotL.target.position.set(0,0,0);spotL.castShadow=true;scene.add(spotL);scene.add(spotL.target);}
        function createCasinoEnvironment(){const floorGeo=new THREE.PlaneGeometry(100,100);const floorMat=new THREE.MeshStandardMaterial({color:0x1a1a1a,roughness:0.85,metalness:0.15});const floor=new THREE.Mesh(floorGeo,floorMat);floor.rotation.x=-Math.PI/2;floor.position.y=-0.5;floor.receiveShadow=true;scene.add(floor);}
        function createPokerTable3D(){tableGroup=new THREE.Group();const tableGeo=new THREE.CylinderGeometry(7,7,0.4,64);const tableMat=new THREE.MeshStandardMaterial({color:0x7A3C1E,roughness:0.65,metalness:0.25});const pTable=new THREE.Mesh(tableGeo,tableMat);pTable.position.y=-0.2;pTable.receiveShadow=true;pTable.castShadow=true;tableGroup.add(pTable);const feltGeo=new THREE.CylinderGeometry(6.5,6.5,0.05,64);const feltMat=new THREE.MeshStandardMaterial({color:0x0b4d27,roughness:0.9});const tFelt=new THREE.Mesh(feltGeo,feltMat);tFelt.position.y=0.25;tFelt.receiveShadow=true;tableGroup.add(tFelt);scene.add(tableGroup);createPlayerPositions3D();}
        function createPlayerPositions3D(){playerPositions3D=[];for(let i=0;i<10;i++){const ang=(i/10)*Math.PI*2;playerPositions3D.push({angle:ang,x:Math.cos(ang)*5,z:Math.sin(ang)*5,cardX:Math.cos(ang)*4.2,cardZ:Math.sin(ang)*4.2,chipX:Math.cos(ang)*3.5,chipZ:Math.sin(ang)*3.5});}}
        function createCardMaterials(){const defMat={roughness:0.75,metalness:0.05};cardMaterials.back=new THREE.MeshStandardMaterial({color:0x2E4BC6,...defMat});['hearts','diamonds','clubs','spades'].forEach(s=>{cardMaterials[s]=new THREE.MeshStandardMaterial({color:0xffffff,...defMat});});}
        function createChipMaterials(){const defMat={roughness:0.55,metalness:0.1};chipMaterials={1:new THREE.MeshStandardMaterial({color:0xFFFFFF,...defMat}),5:new THREE.MeshStandardMaterial({color:0xFF0000,...defMat}),25:new THREE.MeshStandardMaterial({color:0x00AA00,...defMat}),100:new THREE.MeshStandardMaterial({color:0x222222,...defMat}),500:new THREE.MeshStandardMaterial({color:0x800080,...defMat}),1000:new THREE.MeshStandardMaterial({color:0xFFD700,...defMat})};}
        function createCard3DObject(s,r,pos,rotY=0,faceUp=true){const grp=new THREE.Group();const geo=new THREE.PlaneGeometry(0.85,1.25);const mat=faceUp&&s!=='back'?cardMaterials[s]||cardMaterials.back:cardMaterials.back;const mesh=new THREE.Mesh(geo,mat);mesh.rotation.x=-Math.PI/2;mesh.castShadow=true;mesh.receiveShadow=true;grp.add(mesh);grp.position.copy(pos);grp.rotation.y=rotY;return grp;}
        function createChip3DStack(val,pos,cnt=1){const grp=new THREE.Group();for(let i=0;i<cnt;i++){const geo=new THREE.CylinderGeometry(0.18,0.18,0.045,16);const key=Object.keys(chipMaterials).reverse().find(k=>val>=parseInt(k))||1;const mat=chipMaterials[key]||chipMaterials[1];const chip=new THREE.Mesh(geo,mat);chip.position.y=i*0.05;chip.castShadow=true;chip.receiveShadow=true;grp.add(chip);}grp.position.copy(pos);return grp;}
        function addMouseCameraControls(){let md=false,lmX=null,lmY=null,trX=camera.rotation.x,trY=camera.rotation.y,tZ=camera.position.z;canvas.addEventListener('mousedown',(e)=>{if(uiActive||cameraAnimating)return;md=true;lmX=e.clientX;lmY=e.clientY;});canvas.addEventListener('mouseup',()=>{md=false;});canvas.addEventListener('mouseleave',()=>{md=false;});canvas.addEventListener('mousemove',(e)=>{if(uiActive||cameraAnimating||!md)return;const dX=e.clientX-lmX;const rad=Math.sqrt(camera.position.x**2+camera.position.z**2);let ang=Math.atan2(camera.position.x,camera.position.z);ang-=dX*0.004;camera.position.x=rad*Math.sin(ang);camera.position.z=rad*Math.cos(ang);camera.lookAt(0,0,0);lmX=e.clientX;lmY=e.clientY;});canvas.addEventListener('wheel',(e)=>{if(uiActive||cameraAnimating)return;e.preventDefault();tZ+=e.deltaY*0.01;tZ=Math.max(7,Math.min(22,tZ));const mag=camera.position.length();camera.position.normalize().multiplyScalar(tZ);camera.position.y=Math.max(4,Math.min(14,camera.position.y+(tZ>mag?0.08:-0.08)*(e.deltaY>0?1:-1)));camera.lookAt(0,0,0);});}
        function animate(){requestAnimationFrame(animate);renderer.render(scene,camera);}
        function animateCameraToTable(){cameraAnimating=true;gsap.to(camera.position,{duration:1.2,x:0,y:9,z:12,ease:"power2.inOut",onUpdate:()=>camera.lookAt(0,0,0),onComplete:()=>{cameraAnimating=false;updateUiActiveState();}});}
        function animateCameraToMenu(){cameraAnimating=true;gsap.to(camera.position,{duration:1.2,x:0,y:12,z:15,ease:"power2.inOut",onUpdate:()=>camera.lookAt(0,0,0),onComplete:()=>{cameraAnimating=false;updateUiActiveState();}});}
        function updateTableVisuals3D(){clearTable3DObjects();if(!gameState||!playerPositions3D.length)return;gameState.community_cards.forEach((c,i)=>{const p=new THREE.Vector3(-1.8+i*0.9,0.3,0);const o=createCard3DObject(c.suit,c.rank,p,0,true);scene.add(o);tableCards3D.push(o);gsap.from(o.scale,{duration:0.4,x:0,y:0,z:0,ease:"back.out(1.7)",delay:i*0.08});});Object.values(gameState.players).forEach((plr)=>{const pIdx=plr.position;if(pIdx>=0&&pIdx<playerPositions3D.length){const p3d=playerPositions3D[pIdx];if(plr.cards&&plr.cards.length>0){playerCardObjects3D[plr.id]=[];plr.cards.forEach((c,ci)=>{const cOff=(ci-(plr.cards.length-1)/2)*0.45;const cPos=new THREE.Vector3(p3d.cardX+cOff*Math.cos(p3d.angle+Math.PI/2),0.3,p3d.cardZ+cOff*Math.sin(p3d.angle+Math.PI/2));const faceUp=c.suit!=='back';const o=createCard3DObject(c.suit,c.rank,cPos,p3d.angle,faceUp);scene.add(o);playerCardObjects3D[plr.id].push(o);gsap.from(o.position,{duration:0.4,y:1.8,ease:"bounce.out",delay:0.4+ci*0.08});});} if(plr.current_bet>0){const chipPos=new THREE.Vector3(p3d.chipX*0.8,0.26,p3d.chipZ*0.8);const s=createChip3DStack(plr.current_bet,chipPos,Math.min(4,Math.ceil(plr.current_bet/100)));scene.add(s);chipStacks3D.push(s);gsap.from(s.scale,{duration:0.25,x:0,y:0,z:0,ease:"elastic.out(1,0.5)",delay:0.7});}}}); if(gameState.pot>0){const potPos=new THREE.Vector3(0,0.26,1.2);const cs=createChip3DStack(gameState.pot,potPos,Math.min(8,Math.ceil(gameState.pot/200)));scene.add(cs);chipStacks3D.push(cs);gsap.from(cs.scale,{duration:0.4,x:0,y:0,z:0,ease:"elastic.out(1,0.3)",delay:0.15});}}
        function clearTable3DObjects(){tableCards3D.forEach(c=>scene.remove(c));tableCards3D=[];Object.values(playerCardObjects3D).flat().forEach(c=>scene.remove(c));playerCardObjects3D={};chipStacks3D.forEach(s=>scene.remove(s));chipStacks3D=[];}
        function connectWebSocket(){const prot=window.location.protocol==='https:'?'wss:':'ws:';const url=`${prot}//${window.location.host}/ws`;ws=new WebSocket(url);ws.onopen=()=>{isConnected=true;hideLoadingScreen();showMainMenu();if(!initialConnectionNotified){showNotification('Connected to Royal Poker 3D!','success');initialConnectionNotified=true;}connectionLostNotified=false;};ws.onmessage=(e)=>{const msg=JSON.parse(e.data);handleServerMessage(msg);};ws.onclose=()=>{isConnected=false;showLoadingScreen('Connection lost. Reconnecting...');if(!connectionLostNotified){showNotification('Connection lost. Attempting to reconnect...','error');connectionLostNotified=true;}initialConnectionNotified=false;setTimeout(connectWebSocket,3000);};ws.onerror=(err)=>{console.error('WS Error:',err);showNotification('Connection error.','error');};}
        function sendMessage(act,pld={}){if(ws&&ws.readyState===WebSocket.OPEN){ws.send(JSON.stringify({action:act,payload:pld}));}else{showNotification('Not connected.','error');}}
        function handleServerMessage(msg){console.log('Recv:',msg.type,msg.data?.room_code);switch(msg.type){case'connected':myPlayerId=msg.data.player_id;showNotification(`Welcome! Server: ${msg.data.server_info.version}`,'success');break;case'room_created':case'room_joined':currentRoomCode=msg.data.room_code;showGameInterface();showNotification(`Joined: ${msg.data.room_name||currentRoomCode}`,'success');animateCameraToTable();break;case'spectating':currentRoomCode=msg.data.room_code;showGameInterface();showNotification(`Spectating: ${currentRoomCode}`,'info');animateCameraToTable();break;case'room_left':showMainMenu();showNotification(`Left room: ${msg.data.room_code}`,'info');animateCameraToMenu();currentRoomCode=null;gameState=null;clearTable3DObjects();break;case'game_state':gameState=msg.data;updateGameInterface();updateTableVisuals3D();break;case'game_started':showNotification('Game started! GL!','success');break;case'room_list':updateRoomList(msg.data.rooms);break;case'hand_history':updateHandHistory(msg.data.history);break;case'error':showNotification(`Error: ${msg.message}`,'error');break;default:console.log('Unknown msg type:',msg.type);}}
        function hideLoadingScreen(){const el=document.getElementById('loadingScreen');gsap.to(el,{duration:0.8,opacity:0,onComplete:()=>{el.style.display='none';updateUiActiveState();}});updateUiActiveState();}
        function showLoadingScreen(txt='Loading...'){const el=document.getElementById('loadingScreen');el.querySelector('.loading-text').textContent=txt;el.style.display='flex';gsap.to(el,{duration:0.4,opacity:1});updateUiActiveState();}
        function showMainMenu(){['menuPanel'].forEach(id=>document.getElementById(id).classList.remove('hidden'));['gameHUD','potDisplay','actionsPanel','chatPanel','playerCards','tournamentInfo','actionTimer'].forEach(id=>document.getElementById(id).classList.add('hidden'));currentRoomCode=null;gameState=null;clearTable3DObjects();updateUiActiveState();}
        function showGameInterface(){['gameHUD','chatPanel','playerCards'].forEach(id=>document.getElementById(id).classList.remove('hidden'));document.getElementById('menuPanel').classList.add('hidden');if(currentRoomCode)document.getElementById('currentRoom').textContent=currentRoomCode.substring(0,8);updateUiActiveState();}
        function updateGameInterface(){if(!gameState)return;document.getElementById('phaseText').textContent=gameState.phase.replace(/_/g,' ').toUpperCase();document.getElementById('handNumber').textContent=gameState.hand_number;document.getElementById('betToMatch').textContent=gameState.current_bet.toLocaleString();const myPData=gameState.players[myPlayerId];document.getElementById('myMoneyAmount').textContent=myPData?myPData.money.toLocaleString():"N/A";const potDisp=document.getElementById('potDisplay');const potAmtEl=document.getElementById('potAmount');const sPotsEl=document.getElementById('sidePots');if(gameState.pot>0||(gameState.side_pots&&gameState.side_pots.length>0)){potDisp.classList.remove('hidden');potAmtEl.textContent=gameState.pot.toLocaleString();if(gameState.side_pots&&gameState.side_pots.length>0){sPotsEl.innerHTML=gameState.side_pots.map((sp,i)=>`Side ${i+1}: ${sp.amount.toLocaleString()} (${sp.eligible_players_count}p)`).join('<br>');}else{sPotsEl.innerHTML='';}}else{potDisp.classList.add('hidden');} const tourneyInfoEl=document.getElementById('tournamentInfo');if(gameState.tournament_info){tourneyInfoEl.classList.remove('hidden');document.getElementById('tournamentLevel').textContent=gameState.tournament_info.level;document.getElementById('tournamentBlinds').textContent=`${gameState.settings.small_blind}/${gameState.settings.big_blind}`;if(gameState.tournament_info.next_level_time)updateTournamentTimer(gameState.tournament_info.next_level_time);}else{tourneyInfoEl.classList.add('hidden');} const timerEl=document.getElementById('actionTimer');if(gameState.can_act&&gameState.time_left_for_action>0){timerEl.classList.remove('hidden');document.getElementById('timerSeconds').textContent=Math.ceil(gameState.time_left_for_action);}else{timerEl.classList.add('hidden');} const startBtn=document.getElementById('startGameBtn');startBtn.style.display=(gameState.phase==='waiting'&&Object.keys(gameState.players).length>=gameState.settings.min_players&&myPlayerId===gameState.owner_id)?'block':'none';const pauseBtn=document.getElementById('pauseGameBtn');pauseBtn.textContent=gameState.paused?'▶️ Resume':'⏸️ Pause';pauseBtn.style.display=(myPlayerId===gameState.owner_id)?'block':'none';document.getElementById('handHistoryBtn').style.display=(gameState.hand_history&&gameState.hand_history.length>0)?'block':'none';document.getElementById('actionsPanel').style.display=(gameState.can_act&&gameState.available_actions&&gameState.available_actions.length>0)?'flex':'none';if(gameState.can_act)updateActionButtons();updatePlayerCards();updateChat();if(gameState.paused&&gameState.pause_reason!==lastPauseReasonNotified){showNotification(`Paused: ${gameState.pause_reason}`,'warning');lastPauseReasonNotified=gameState.pause_reason;}else if(!gameState.paused){lastPauseReasonNotified="";}}
        function updateActionButtons(){if(!gameState||!gameState.available_actions)return;const acts=gameState.available_actions;['foldBtn','checkBtn','callBtn','raiseControlsContainer','allInBtn'].forEach(id=>{const el=document.getElementById(id);if(el){el.style.display='none';if(el.tagName==='BUTTON')el.disabled=true;}});acts.forEach(a=>{if(a.action==='fold'){const b=document.getElementById('foldBtn');b.style.display='inline-block';b.disabled=false;}if(a.action==='check'){const b=document.getElementById('checkBtn');b.style.display='inline-block';b.disabled=false;}if(a.action==='call'){const b=document.getElementById('callBtn');b.style.display='inline-block';b.disabled=false;document.getElementById('callAmount').textContent=a.amount.toLocaleString();}if(a.action==='raise'){document.getElementById('raiseControlsContainer').style.display='flex';document.getElementById('raiseBtn').disabled=false;const sl=document.getElementById('raiseSlider');const ip=document.getElementById('raiseAmountInput');sl.min=a.min_amount;sl.max=a.max_amount;ip.min=a.min_amount;ip.max=a.max_amount;ip.value=Math.max(a.min_amount,Math.min(parseInt(ip.value)||a.min_amount,a.max_amount));sl.value=ip.value;}if(a.action==='all_in'){const b=document.getElementById('allInBtn');b.style.display='inline-block';b.disabled=false;b.innerHTML=`🔥 ALL IN ${a.amount.toLocaleString()}`;}}); }
        function updateRaiseAmountDisplay(){document.getElementById('raiseAmountInput').value=document.getElementById('raiseSlider').value;}
        function updateRaiseSliderFromInput(){const input=document.getElementById('raiseAmountInput'); const slider=document.getElementById('raiseSlider'); const val=parseInt(input.value); if(!isNaN(val) && val>=parseInt(input.min) && val<=parseInt(input.max)){slider.value=val;}else if(!isNaN(val) && val<parseInt(input.min)){slider.value=input.min; input.value=input.min;} else if(!isNaN(val) && val>parseInt(input.max)){slider.value=input.max; input.value=input.max;}}
        function updatePlayerCards(){const cont=document.getElementById('playerCards');cont.innerHTML='';if(!gameState||!gameState.players)return;Object.values(gameState.players).sort((a,b)=>a.position-b.position).forEach(p=>{const d=document.createElement('div');d.className='player-card';if(p.is_current_player)d.classList.add('current-player');if(p.status==='folded')d.classList.add('folded');if(p.status==='all_in')d.classList.add('all-in');let aiI=p.is_ai?'<span style="font-size:0.75em;opacity:0.7;margin-right:2px;">🤖</span>':'';let dlrI=p.is_dealer?'<span style="position:absolute;top:-7px;left:-7px;background:gold;color:black;border-radius:50%;width:18px;height:18px;display:flex;align-items:center;justify-content:center;font-size:0.65rem;font-weight:bold;box-shadow:0 0 4px black;">D</span>':'';let bTxt='';if(p.is_small_blind)bTxt='<span style="font-size:0.65em;color:#add8e6;">SB</span>';if(p.is_big_blind)bTxt='<span style="font-size:0.65em;color:#90ee90;">BB</span>';d.innerHTML=`<div class="player-avatar" style="background-color:${p.color}">${p.name.charAt(0).toUpperCase()}</div><div class="player-name">${aiI}${p.name.substring(0,10)}${p.name.length>10?'..':''} ${bTxt}</div><div class="player-money">$${p.money.toLocaleString()}</div>${p.current_bet>0?`<div style="color:var(--primary-gold);font-size:0.8rem;">Bet: $${p.current_bet.toLocaleString()}</div>`:''}${p.last_action?`<div class="player-action">${p.last_action.toUpperCase().substring(0,5)}</div>`:''}${dlrI}`;cont.appendChild(d);gsap.from(d,{duration:0.25,scale:0.6,opacity:0,delay:p.position*0.04});});}
        function updateChat(){if(!gameState||!gameState.chat_messages)return;const el=document.getElementById('chatMessages');const scroll=el.scrollTop+el.clientHeight>=el.scrollHeight-20;el.innerHTML=gameState.chat_messages.map(m=>`<div class="chat-message" style="border-left-color:${m.player_color||'#fff'};"><strong class="chat-player-name" style="color:${m.player_color||'#fff'}">${m.player_name}:</strong> <span>${m.message}</span><span class="chat-timestamp">${m.formatted_time}</span></div>`).join('');if(scroll)el.scrollTop=el.scrollHeight;}
        function updateTournamentTimer(nextTimeStr){const n=new Date();const nxt=new Date(nextTimeStr);const d=nxt-n;if(d>0){const m=Math.floor(d/60000);const s=Math.floor((d%60000)/1000);document.getElementById('tournamentTimer').textContent=`${m}:${s.toString().padStart(2,'0')}`;}}
        function createQuickRoom(){const n=document.getElementById('playerName').value.trim()||'Player';sendMessage('create_room',{player_name:n,num_ai_players:0});}
        function createCustomRoom(){sendMessage('create_room',{player_name:document.getElementById('playerName').value.trim()||'Player',room_name:document.getElementById('roomName').value.trim(),game_mode:document.getElementById('gameMode').value,max_players:parseInt(document.getElementById('maxPlayers').value),small_blind:parseInt(document.getElementById('smallBlind').value),big_blind:parseInt(document.getElementById('bigBlind').value),buy_in:parseInt(document.getElementById('buyIn').value),password:document.getElementById('roomPassword').value.trim(),num_ai_players:parseInt(document.getElementById('numAiPlayers').value)}); }
        function joinRoom(){const c=document.getElementById('roomCode').value.trim().toUpperCase();const n=document.getElementById('playerName').value.trim()||'Player';if(!c){showNotification('Enter room code.','error');return;}sendMessage('join_room',{room_code:c,player_name:n});}
        function spectateRoom(){const c=document.getElementById('roomCode').value.trim().toUpperCase();if(!c){showNotification('Enter room code.','error');return;}sendMessage('spectate',{room_code:c});}
        function leaveRoom(){sendMessage('leave_room');} function startGame(){sendMessage('start_game');} function pauseGame(){sendMessage('pause_game');}
        function playerAction(act){let pld={action_type:act};if(act==='raise'){pld.amount=parseInt(document.getElementById('raiseAmountInput').value)||0;}sendMessage('player_action',pld);}
        function sendChat(){const i=document.getElementById('chatInput');const m=i.value.trim();if(m&&m.length<=200){sendMessage('send_chat',{message:m});i.value='';}else if(m.length>200){showNotification('Msg too long (max 200).','error');}}
        function toggleChat(){chatCollapsed=!chatCollapsed;document.getElementById('chatMessages').style.display=chatCollapsed?'none':'block';document.getElementById('chatToggle').textContent=chatCollapsed?'+':'−';}
        function showRoomList(){document.getElementById('roomListModal').classList.remove('hidden');sendMessage('get_room_list');updateUiActiveState();}
        function hideRoomList(){document.getElementById('roomListModal').classList.add('hidden');updateUiActiveState();}
        function refreshRoomList(){document.getElementById('roomList').innerHTML = '<div style="text-align:center;color:#ccc;padding:20px;">Refreshing...</div>';sendMessage('get_room_list');}
        function updateRoomList(rms){const lst=document.getElementById('roomList');if(rms.length===0){lst.innerHTML='<div style="text-align:center;color:#ccc;padding:20px;">No public rooms.</div>';return;}lst.innerHTML=rms.map(r=>`<div style="background:rgba(255,255,255,0.08);border-radius:8px;padding:12px;margin-bottom:10px;border:1px solid rgba(var(--primary-gold),0.5);"><div style="display:flex;justify-content:space-between;align-items:center;margin-bottom:8px;"><strong style="color:var(--primary-gold);">${r.name} (${r.code})</strong><span style="font-size:0.75em;">${r.game_mode.replace('_',' ')}</span></div><div style="display:grid;grid-template-columns:1fr 1fr;gap:8px;font-size:0.85rem;"><div>👥 ${r.players}/${r.max_players}</div><div>👁️ ${r.spectators}</div><div>🎲 ${r.phase.replace('_',' ')}</div><div>💰 ${r.small_blind}/${r.big_blind}</div></div><div style="margin-top:10px;text-align:center;"><button class="action-button" onclick="joinRoomByCode('${r.code}')" style="margin-right:8px;padding:8px 12px;">Join</button><button class="action-button" onclick="spectateRoomByCode('${r.code}')" style="padding:8px 12px;">Spectate</button></div></div>`).join('');}
        function joinRoomByCode(c){document.getElementById('roomCode').value=c;hideRoomList();joinRoom();}
        function spectateRoomByCode(c){document.getElementById('roomCode').value=c;hideRoomList();spectateRoom();}
        function showHandHistory(){document.getElementById('handHistoryModal').classList.remove('hidden');sendMessage('get_hand_history');updateUiActiveState();}
        function hideHandHistory(){document.getElementById('handHistoryModal').classList.add('hidden');updateUiActiveState();}
        function updateHandHistory(hist){const c=document.getElementById('handHistoryContent');if(hist.length===0){c.innerHTML='<div style="text-align:center;color:#ccc;padding:20px;">No hands recorded.</div>';return;}c.innerHTML=hist.map(h=>`<div style="background:rgba(255,255,255,0.08);border-radius:8px;padding:12px;margin-bottom:10px;border:1px solid rgba(var(--primary-gold),0.5);font-size:0.85rem;"><div style="display:flex;justify-content:space-between;margin-bottom:8px;"><strong style="color:var(--primary-gold);">Hand #${h.hand_number}</strong><span style="color:#bbb;font-size:0.8rem;">${new Date(h.timestamp).toLocaleTimeString()}</span></div><div style="margin-bottom:6px;"><strong>Cards:</strong> ${h.community_cards.map(card=>`${card.rank}${card.suit[0].toUpperCase()}`).join(' ')}</div><div style="margin-bottom:6px;"><strong>Pot:</strong> $${h.pot.toLocaleString()}</div><div><strong>Players:</strong><br>${Object.values(h.players).map(p=>`${p.name}: $${p.final_money.toLocaleString()}`).join('<br>')}</div></div>`).join('');}
        function showNotification(msg,type='info'){const n=document.createElement('div');n.className=`notification ${type}`;n.textContent=msg;document.body.appendChild(n);gsap.from(n,{duration:0.4,x:"100%",opacity:0,ease:"power2.out"});setTimeout(()=>{gsap.to(n,{duration:0.4,x:"100%",opacity:0,ease:"power2.in",onComplete:()=>{if(n.parentNode)n.parentNode.removeChild(n);}});},3500);}
        window.addEventListener('resize',()=>{if(camera&&renderer){camera.aspect=window.innerWidth/window.innerHeight;camera.updateProjectionMatrix();renderer.setSize(window.innerWidth,window.innerHeight);}});
        document.addEventListener('keydown',(e)=>{if(!gameState||!gameState.can_act)return;const focusedEl=document.activeElement;if(focusedEl.tagName==='INPUT'&&focusedEl.type==='text'||focusedEl.type==='number'||focusedEl.type==='password')return; switch(e.key.toLowerCase()){case'f':if(!document.getElementById('foldBtn').disabled)playerAction('fold');break;case'c':if(!document.getElementById('checkBtn').disabled&&document.getElementById('checkBtn').style.display!=='none')playerAction('check');else if(!document.getElementById('callBtn').disabled&&document.getElementById('callBtn').style.display!=='none')playerAction('call');break;case'r':if(!document.getElementById('raiseBtn').disabled&&document.getElementById('raiseControlsContainer').style.display!=='none')playerAction('raise');break;case'a':if(!document.getElementById('allInBtn').disabled)playerAction('all_in');break;}});
        window.addEventListener('load',()=>{initThreeJS();connectWebSocket();showLoadingScreen();updateUiActiveState();});
    </script>
</body>
</html>
"""

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run(app, host="0.0.0.0", port=port, ws_ping_interval=20, ws_ping_timeout=20)
