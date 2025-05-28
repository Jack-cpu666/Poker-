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
RATE_LIMIT_ACTIONS_PER_SECOND = 5
MAX_CHAT_MESSAGES = 100
HAND_EVALUATION_CACHE_SIZE = 10000
AUTO_FOLD_TIMEOUT = 30
TOURNAMENT_BLIND_INCREASE_INTERVAL = 600
MAX_ROOMS = 1000
SESSION_TIMEOUT = 3600
AI_ACTION_DELAY = 1.5 # Seconds for AI to "think"

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
        if self.rank == 'K': return 13
        if self.rank == 'Q': return 12
        if self.rank == 'J': return 11
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
    num_ai_players: int = 0

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
        if len(players_in_hand) <= 1: return
        bet_groups = defaultdict(list)
        for player in players_in_hand: bet_groups[player.total_bet_this_hand].append(player)
        sorted_bets = sorted(bet_groups.keys())
        prev_bet = 0
        for bet_amount in sorted_bets:
            if bet_amount > prev_bet:
                pot_size = (bet_amount - prev_bet) * len([p for p in players_in_hand if p.total_bet_this_hand >= bet_amount])
                eligible_players = {p.id for p in players_in_hand if p.total_bet_this_hand >= bet_amount}
                if pot_size > 0: self.side_pots.append(SidePot(pot_size, eligible_players))
                prev_bet = bet_amount

    def update_activity(self):
        self.last_activity = datetime.now()

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
        self.ai_pending_actions: Dict[str, asyncio.Task] = {}


    def generate_room_code(self) -> str:
        return ''.join(random.choices('ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789', k=8))

    def create_room(self, player_id: str, room_settings: GameSettings, room_name: str = None) -> str:
        if len(self.rooms) >= MAX_ROOMS: raise Exception("Maximum number of rooms reached")
        room_code = self.generate_room_code()
        while room_code in self.rooms: room_code = self.generate_room_code()
        room_name = room_name or f"Room {room_code}"
        self.rooms[room_code] = Room(
            code=room_code, name=room_name, players={}, spectators=set(), deck=[], community_cards=[],
            settings=room_settings, owner_id=player_id,
            room_type=RoomType.PRIVATE if room_settings.password else RoomType.PUBLIC
        )
        logger.info(f"Room {room_code} created by player {player_id}")
        self._add_ai_players(room_code, room_settings.num_ai_players, room_settings.buy_in)
        return room_code

    def _add_ai_players(self, room_code: str, num_ai: int, buy_in: int):
        room = self.rooms[room_code]
        for i in range(num_ai):
            if len(room.players) >= room.settings.max_players: break
            ai_id = f"AI_{str(uuid.uuid4())[:8]}"
            ai_player = Player(
                id=ai_id, name=f"AI Bot {i+1}", is_ai=True,
                position=len(room.players),
                money=buy_in if buy_in > 0 else (TOURNAMENT_STARTING_MONEY if room.settings.game_mode == GameMode.TOURNAMENT else STARTING_MONEY),
                avatar=f"avatar_ai_{random.randint(1, 5)}",
                color=f"#{random.randint(0x808080, 0xFFFFFF):06x}" # Lighter colors for AI
            )
            room.players[ai_id] = ai_player
            logger.info(f"AI Player {ai_player.name} added to room {room_code}")

    def join_room(self, room_code: str, player_id: str, player_name: str, password: str = None) -> bool:
        if room_code not in self.rooms: return False
        room = self.rooms[room_code]
        if room.settings.password and room.settings.password != password: return False
        if len(room.players) >= room.settings.max_players: return False
        if player_id in room.players:
            room.players[player_id].connection_id = player_id
            if room.players[player_id].is_ai: room.players[player_id].is_ai = False # Human taking over an AI spot? Unlikely here.
            room.update_activity()
            return True
        player = Player(
            id=player_id, name=player_name, position=len(room.players),
            money=room.settings.buy_in if room.settings.buy_in > 0 else (TOURNAMENT_STARTING_MONEY if room.settings.game_mode == GameMode.TOURNAMENT else STARTING_MONEY),
            avatar=f"avatar_{random.randint(1, 10)}", color=f"#{random.randint(0, 0xFFFFFF):06x}",
            connection_id=player_id
        )
        room.players[player_id] = player
        self.player_rooms[player_id] = room_code
        room.update_activity()
        logger.info(f"Player {player_name} joined room {room_code}")
        return True

    def leave_room(self, player_id: str, force: bool = False):
        if player_id not in self.player_rooms and not any(player_id == p.id for room in self.rooms.values() for p in room.players.values() if p.is_ai):
             return

        room_code = self.player_rooms.get(player_id)
        if not room_code: # Could be an AI player not in player_rooms
            for rc, r in self.rooms.items():
                if player_id in r.players and r.players[player_id].is_ai:
                    room_code = rc
                    break
            if not room_code: return
        
        room = self.rooms[room_code]
        
        if player_id in self.ai_pending_actions:
            self.ai_pending_actions[player_id].cancel()
            del self.ai_pending_actions[player_id]

        if player_id in room.players:
            player = room.players[player_id]
            if room.settings.game_mode == GameMode.TOURNAMENT and not force and not player.is_ai:
                player.status = PlayerStatus.ELIMINATED
                player.connection_id = None
            else:
                del room.players[player_id]
        
        if player_id in room.spectators: room.spectators.remove(player_id)
        if player_id in self.player_rooms: del self.player_rooms[player_id]
        
        if not any(not p.is_ai for p in room.players.values()) and not room.spectators: # No human players or spectators
            del self.rooms[room_code]
            logger.info(f"Room {room_code} deleted (only AI or empty)")
        elif room.owner_id == player_id and room.players:
            human_players = [pid for pid, p in room.players.items() if not p.is_ai]
            if human_players:
                room.owner_id = human_players[0]
            else: # No human players left to own, room might be AI only
                room.owner_id = None


    def spectate_room(self, room_code: str, player_id: str, password: str = None) -> bool:
        if room_code not in self.rooms: return False
        room = self.rooms[room_code]
        if room.settings.password and room.settings.password != password: return False
        room.spectators.add(player_id)
        self.player_rooms[player_id] = room_code
        room.update_activity()
        return True

    def start_game(self, room_code: str, force_start: bool = False):
        room = self.rooms[room_code]
        active_players = room.get_active_players()
        if len(active_players) < room.settings.min_players and not force_start: return False
        room.phase = GamePhase.PRE_FLOP
        room.hand_number += 1
        room.shuffle_deck()
        room.community_cards = []
        room.pot = 0
        room.side_pots = []
        room.current_bet = room.settings.big_blind
        room.min_raise = room.settings.big_blind
        for player in room.players.values(): player.reset_for_new_hand()
        self.set_player_positions(room)
        self.post_blinds_and_ante(room)
        room.deal_cards(2)
        room.current_player_index = self.get_first_player_to_act(room)
        room.last_action_time = time.time()
        self.global_stats['total_hands'] += 1
        logger.info(f"Game started in room {room_code}, hand #{room.hand_number}")
        self.check_ai_turn(room_code)
        return True

    def set_player_positions(self, room: Room):
        active_players = room.get_active_players()
        if len(active_players) < 2: return
        room.dealer_index = (room.dealer_index + 1) % len(active_players)
        dealer_player = active_players[room.dealer_index]
        dealer_player.is_dealer = True
        if len(active_players) == 2:
            dealer_player.is_small_blind = True
            big_blind_idx = (room.dealer_index + 1) % len(active_players)
            active_players[big_blind_idx].is_big_blind = True
        else:
            small_blind_idx = (room.dealer_index + 1) % len(active_players)
            big_blind_idx = (room.dealer_index + 2) % len(active_players)
            active_players[small_blind_idx].is_small_blind = True
            active_players[big_blind_idx].is_big_blind = True

    def post_blinds_and_ante(self, room: Room):
        active_players = room.get_active_players()
        if room.settings.ante > 0:
            for player in active_players:
                ante_amount = min(room.settings.ante, player.money)
                player.money -= ante_amount; player.current_bet += ante_amount
                player.total_bet_this_hand += ante_amount; room.pot += ante_amount
        for player in active_players:
            if player.is_small_blind:
                blind_amount = min(room.settings.small_blind, player.money)
                player.money -= blind_amount; player.current_bet += blind_amount
                player.total_bet_this_hand += blind_amount; room.pot += blind_amount
                if player.money == 0: player.status = PlayerStatus.ALL_IN
            elif player.is_big_blind:
                blind_amount = min(room.settings.big_blind, player.money)
                player.money -= blind_amount; player.current_bet += blind_amount
                player.total_bet_this_hand += blind_amount; room.pot += blind_amount
                if player.money == 0: player.status = PlayerStatus.ALL_IN

    def get_first_player_to_act(self, room: Room) -> int:
        active_players = room.get_active_players()
        if not active_players: return 0
        if len(active_players) < 2 : return 0 # was <3
        
        # Small blind acts first in heads-up pre-flop if they are also dealer
        if len(active_players) == 2:
            for i, player in enumerate(active_players):
                if player.is_small_blind: return i
        
        # Standard: player after big blind
        for i, player in enumerate(active_players):
            if player.is_big_blind:
                return (i + 1) % len(active_players)
        return 0


    def player_action(self, room_code: str, player_id: str, action: PlayerAction, amount: int = 0) -> bool:
        room = self.rooms[room_code]
        if player_id not in room.players: return False
        player = room.players[player_id]
        
        active_players = room.get_active_players() # get list of active players
        if not active_players : return False # no active players
        current_acting_player = active_players[room.current_player_index % len(active_players)] # use modulo for safety

        if not player.can_act() or current_acting_player.id != player_id:
             return False
        
        success = self.process_player_action(room, player, action, amount)
        if success:
            player.last_action = action
            player.last_action_time = time.time()
            room.last_action_time = time.time()
            if not player.is_ai : player.stats.hands_played += 1
            self.advance_game(room_code)
        return success

    def process_player_action(self, room: Room, player: Player, action: PlayerAction, amount: int) -> bool:
        if action == PlayerAction.FOLD:
            player.status = PlayerStatus.FOLDED
            return True
        elif action == PlayerAction.CHECK:
            if room.current_bet > player.current_bet: return False
            return True
        elif action == PlayerAction.CALL:
            call_amount = min(room.current_bet - player.current_bet, player.money)
            if call_amount < 0: return False # Can't call less than 0
            if call_amount == 0 and room.current_bet > player.current_bet: return False # effectively a check when bet is pending
            player.money -= call_amount; player.current_bet += call_amount
            player.total_bet_this_hand += call_amount; room.pot += call_amount
            if player.money == 0: player.status = PlayerStatus.ALL_IN
            return True
        elif action == PlayerAction.RAISE:
            actual_raise_amount = amount # This is the amount ON TOP of current_bet
            min_total_bet_after_raise = room.current_bet + max(actual_raise_amount, room.min_raise)
            
            # The amount player needs to add to their current bet
            additional_money_needed = min_total_bet_after_raise - player.current_bet

            if additional_money_needed <= 0 : return False # Trying to raise by 0 or negative
            if additional_money_needed > player.money : return False # Not enough money for this raise
            if min_total_bet_after_raise < room.current_bet + room.min_raise and player.money > additional_money_needed:
                return False # Raise amount too small unless it's an all-in that is less than min_raise

            player.money -= additional_money_needed
            player.current_bet += additional_money_needed
            player.total_bet_this_hand += additional_money_needed
            room.pot += additional_money_needed
            
            # Update room's current_bet and min_raise
            # The new min_raise is the difference between the new total bet and the previous total bet
            new_min_raise_increment = player.current_bet - room.current_bet
            room.current_bet = player.current_bet
            room.min_raise = max(room.min_raise, new_min_raise_increment)

            if player.money == 0: player.status = PlayerStatus.ALL_IN
            return True
        elif action == PlayerAction.ALL_IN:
            if player.money <= 0: return False
            bet_amount = player.money
            player.current_bet += bet_amount
            player.total_bet_this_hand += bet_amount
            room.pot += bet_amount
            player.money = 0
            player.status = PlayerStatus.ALL_IN
            if player.current_bet > room.current_bet:
                new_min_raise_increment = player.current_bet - room.current_bet
                room.current_bet = player.current_bet
                room.min_raise = max(room.min_raise, new_min_raise_increment)
            return True
        elif action == PlayerAction.SIT_OUT:
            player.status = PlayerStatus.SITTING_OUT; return True
        elif action == PlayerAction.SIT_IN:
            if player.status == PlayerStatus.SITTING_OUT: player.status = PlayerStatus.ACTIVE; return True
            return False
        return False

    def advance_game(self, room_code: str):
        room = self.rooms[room_code]
        players_still_in_hand = room.get_players_in_hand() # Players not folded
        
        # Count players who can still act (not folded, not all-in)
        players_who_can_act = [p for p in players_still_in_hand if p.status == PlayerStatus.ACTIVE and p.money > 0]

        if len(players_still_in_hand) <= 1:
            self.end_hand(room_code)
            return
        
        # If only one player can act or all acting players are all-in, but there are other all-in players
        if len(players_who_can_act) <= 1 and any(p.status == PlayerStatus.ALL_IN for p in players_still_in_hand):
            all_acted_or_all_in = True
            for p in players_still_in_hand:
                 if p.status == PlayerStatus.ACTIVE and p.money > 0 and p.current_bet < room.current_bet:
                    all_acted_or_all_in = False
                    break
            if all_acted_or_all_in:
                while room.phase not in [GamePhase.RIVER, GamePhase.SHOWDOWN, GamePhase.GAME_OVER]:
                    self.advance_phase(room_code, skip_betting_round_check=True)
                    if room.phase == GamePhase.SHOWDOWN: break # End hand called from advance_phase
                if room.phase != GamePhase.SHOWDOWN and room.phase != GamePhase.GAME_OVER : # Ensure end_hand if not already triggered
                    self.end_hand(room_code)
                return

        self.move_to_next_player(room)
        
        if self.is_betting_round_complete(room):
            self.advance_phase(room_code)
        else:
            self.check_ai_turn(room_code)


    def move_to_next_player(self, room: Room):
        active_players = room.get_active_players()
        if not active_players: return
        
        start_index = room.current_player_index
        for i in range(len(active_players)):
            room.current_player_index = (start_index + 1 + i) % len(active_players)
            current_player = active_players[room.current_player_index]
            if current_player.can_act():
                room.last_action_time = time.time()
                return
        
        # If no one can act (e.g. all all-in or folded), effectively round is over.
        # This case should ideally be caught by is_betting_round_complete or advance_game logic
        logger.warning(f"move_to_next_player: No player found who can act in room {room.code}")


    def is_betting_round_complete(self, room: Room) -> bool:
        acting_players = [p for p in room.players.values() if p.status == PlayerStatus.ACTIVE and p.money > 0]
        
        if not acting_players: return True # No one left to act
        if len(acting_players) == 1 and acting_players[0].current_bet >= room.current_bet: return True


        all_acted_and_bets_equal = True
        num_players_yet_to_act_this_round = 0

        highest_bet_by_active_player = 0
        for p in acting_players:
            if p.current_bet > highest_bet_by_active_player:
                highest_bet_by_active_player = p.current_bet
        
        # Room.current_bet should be the highest bet on the table by any player (active or all-in)
        # Highest_bet_by_active_player is the highest bet by someone who can still act

        for player in acting_players:
            if player.last_action is None and not (player.is_big_blind and room.phase == GamePhase.PRE_FLOP and room.current_bet == room.settings.big_blind):
                num_players_yet_to_act_this_round +=1
            
            if player.current_bet < room.current_bet: # room.current_bet reflects the highest bet
                all_acted_and_bets_equal = False # Someone needs to call/raise/fold
                break
        
        if num_players_yet_to_act_this_round > 0 : return False
        return all_acted_and_bets_equal


    def advance_phase(self, room_code: str, skip_betting_round_check: bool = False):
        room = self.rooms[room_code]
        
        if not skip_betting_round_check:
             room.calculate_side_pots() # Calculate before resetting current_bet

        for player in room.players.values():
            if player.status != PlayerStatus.ALL_IN: # All-in players keep their current_bet for side pot calcs
                player.current_bet = 0
            player.last_action = None
        
        room.current_bet = 0
        room.min_raise = room.settings.big_blind
        
        if room.phase == GamePhase.PRE_FLOP: room.phase = GamePhase.FLOP; room.deal_community_cards(3)
        elif room.phase == GamePhase.FLOP: room.phase = GamePhase.TURN; room.deal_community_cards(1)
        elif room.phase == GamePhase.TURN: room.phase = GamePhase.RIVER; room.deal_community_cards(1)
        elif room.phase == GamePhase.RIVER: room.phase = GamePhase.SHOWDOWN; self.end_hand(room_code); return
        else: # Should not happen if logic is correct
            logger.error(f"Invalid phase transition from {room.phase} in room {room_code}")
            self.end_hand(room_code) # Fallback
            return

        active_players_for_next_round = room.get_active_players()
        if not active_players_for_next_round: # All players folded or all-in
             self.advance_phase(room_code, skip_betting_round_check=True) # Force advance to showdown if needed
             return

        # Find first player to act: player after dealer button who is still active
        # Start search from player after dealer.
        dealer_player_id = None
        for p in active_players_for_next_round: # use active players for next round for dealer pos
            if p.is_dealer:
                dealer_player_id = p.id
                break
        
        start_search_idx = 0
        if dealer_player_id:
            try:
                # Find the dealer in the *original* list of active players to determine next index
                # This assumes active_players_for_next_round maintains relative order
                dealer_original_idx = [p.id for p in active_players_for_next_round].index(dealer_player_id)
                start_search_idx = (dealer_original_idx + 1) % len(active_players_for_next_round)
            except ValueError:
                start_search_idx = 0 # Fallback if dealer not found (shouldn't happen)
        
        found_next_player = False
        for i in range(len(active_players_for_next_round)):
            check_idx = (start_search_idx + i) % len(active_players_for_next_round)
            if active_players_for_next_round[check_idx].can_act():
                room.current_player_index = check_idx
                found_next_player = True
                break
        
        if not found_next_player: # e.g. only one player left who can act, or all others are all-in
            # This typically means we should go to showdown or next phase without betting
             self.advance_phase(room_code, skip_betting_round_check=True)
             return


        room.last_action_time = time.time()
        self.check_ai_turn(room_code)


    def end_hand(self, room_code: str):
        room = self.rooms[room_code]
        room.phase = GamePhase.SHOWDOWN # Ensure phase is showdown
        room.calculate_side_pots()
        winners_eval = self.determine_winners(room)
        self.distribute_winnings(room, winners_eval)
        self.save_hand_history(room, winners_eval)
        if room.settings.game_mode == GameMode.TOURNAMENT: self.update_tournament(room)
        
        active_players_overall = [p for p in room.players.values() if p.money > 0 and p.status != PlayerStatus.ELIMINATED]
        if len(active_players_overall) <= 1 and room.settings.game_mode != GameMode.CASH_GAME : # Tournament ends if 1 or 0 players left
            room.phase = GamePhase.GAME_OVER
            if room.settings.game_mode == GameMode.TOURNAMENT: self.end_tournament(room)
        else:
            room.phase = GamePhase.WAITING
            if len(active_players_overall) >= room.settings.min_players:
                asyncio.create_task(self.auto_start_next_hand(room_code))

    def determine_winners(self, room: Room) -> Dict[str, HandEvaluation]:
        players_in_hand = room.get_players_in_hand()
        winners_eval = {}
        if not players_in_hand: return winners_eval

        # If only one player left in hand (others folded), they win the pot by default
        if len(players_in_hand) == 1:
            player = players_in_hand[0]
            # Create a dummy HandEvaluation as cards might not be shown/evaluated
            # If player has cards (e.g. was never all-in pre-showdown), evaluate them for fun/history
            if player.cards and room.community_cards:
                 hand_eval = self.evaluate_hand(player.cards + room.community_cards)
            else: # No cards to evaluate (e.g. everyone folded pre-flop to this player)
                hand_eval = HandEvaluation(HandRank.HIGH_CARD, 0, [], "Winner by default (all others folded)", [])
            winners_eval[player.id] = hand_eval
            return winners_eval

        for player in players_in_hand:
            if player.status != PlayerStatus.FOLDED:
                if not player.cards: # Should not happen if player is in hand and not folded
                    logger.error(f"Player {player.id} in hand at showdown but has no cards.")
                    continue
                hand_eval = self.evaluate_hand(player.cards + room.community_cards)
                winners_eval[player.id] = hand_eval
        return winners_eval


    def evaluate_hand(self, cards: List[Card]) -> HandEvaluation:
        card_key = ''.join(sorted([f"{c.suit[0]}{c.rank}" for c in cards]))
        if card_key in self.hand_evaluation_cache: return self.hand_evaluation_cache[card_key]
        hand_eval = self.full_hand_evaluation(cards)
        if len(self.hand_evaluation_cache) < HAND_EVALUATION_CACHE_SIZE: self.hand_evaluation_cache[card_key] = hand_eval
        return hand_eval

    def full_hand_evaluation(self, cards: List[Card]) -> HandEvaluation:
        from itertools import combinations
        best_hand_combo = None; best_rank = HandRank.HIGH_CARD; best_value = 0; best_cards_values = []
        
        # Ensure we have at least 5 cards to evaluate for combinations
        if len(cards) < 5:
            # This case can happen if a player is all-in with few community cards revealed
            # We evaluate what they have.
            if not cards: return HandEvaluation(HandRank.HIGH_CARD,0,[], "No Cards", [])
            
            # Pad with dummy low cards if less than 5, but this changes hand logic
            # Instead, evaluate the best hand possible with available cards
            # For simplicity, let's just use the cards as is if < 5, standard evaluator handles 5
             return HandEvaluation(HandRank.HIGH_CARD,0,cards, "Less than 5 cards", [c.value() for c in cards])


        for combo in combinations(cards, 5):
            hand_rank, hand_value, hand_cards_values = self.evaluate_5_card_hand(list(combo))
            if hand_rank > best_rank or (hand_rank == best_rank and hand_value > best_value):
                best_rank = hand_rank; best_value = hand_value; best_cards_values = hand_cards_values; best_hand_combo = combo
        
        return HandEvaluation(
            rank=best_rank, value=best_value,
            cards=list(best_hand_combo) if best_hand_combo else [],
            description=self.get_hand_description(best_rank, best_cards_values),
            kickers=best_cards_values # The primary values of the hand
        )

    def evaluate_5_card_hand(self, cards: List[Card]) -> Tuple[HandRank, int, List[int]]:
        cards.sort(key=lambda x: x.value(), reverse=True)
        values = [c.value() for c in cards]; suits = [c.suit for c in cards]
        is_flush = len(set(suits)) == 1
        is_straight = False
        unique_values = sorted(list(set(values)), reverse=True)
        if len(unique_values) >= 5: # Check for normal straight
            for i in range(len(unique_values) - 4):
                if unique_values[i] - unique_values[i+4] == 4:
                    is_straight = True; values = unique_values[i:i+5]; break # Use the straight's values
        if not is_straight and set(values) == {14, 2, 3, 4, 5}: # Ace-low straight (wheel)
            is_straight = True; values = [5, 4, 3, 2, 14] # Keep Ace high for value, but order as 5-high

        value_counts = Counter([c.value() for c in cards]) # Use original card values for counts
        counts_sorted_values = sorted(value_counts.items(), key=lambda item: (item[1], item[0]), reverse=True)
        
        # Re-evaluate straight using sorted unique values from the 5-card hand
        hand_values_sorted = sorted([c.value() for c in cards], reverse=True)
        is_five_card_straight = False
        if len(set(hand_values_sorted)) == 5: # Must be 5 unique ranks for a straight
            if hand_values_sorted[0] - hand_values_sorted[4] == 4:
                is_five_card_straight = True
            elif hand_values_sorted == [14, 5, 4, 3, 2]: # A-5 wheel
                is_five_card_straight = True
                # For wheel, kicker comparison uses 5 as high card.
                # Value stored for wheel should be based on 5, not A.

        if is_five_card_straight and is_flush:
            if hand_values_sorted == [14, 13, 12, 11, 10]: return HandRank.ROYAL_FLUSH, hand_values_sorted[0], hand_values_sorted
            actual_straight_values = [5,4,3,2,1] if hand_values_sorted == [14,5,4,3,2] else hand_values_sorted
            return HandRank.STRAIGHT_FLUSH, actual_straight_values[0], actual_straight_values

        
        primary_ranks = [item[0] for item in counts_sorted_values]
        counts = [item[1] for item in counts_sorted_values]

        if counts[0] == 4: # Four of a kind
            # Ranks are [QuadRank, KickerRank]
            quad_rank = primary_ranks[0]
            kicker_rank = primary_ranks[1]
            # Value: QuadRank * 15 (higher than any kicker) + KickerRank
            return HandRank.FOUR_OF_A_KIND, quad_rank * 15 + kicker_rank, [quad_rank, kicker_rank]

        if counts[0] == 3 and counts[1] == 2: # Full house
            # Ranks are [ThreeOfAKindRank, PairRank]
            three_rank = primary_ranks[0]
            pair_rank = primary_ranks[1]
            # Value: ThreeRank * 15 + PairRank
            return HandRank.FULL_HOUSE, three_rank * 15 + pair_rank, [three_rank, pair_rank]

        if is_flush:
            # Ranks are the 5 card ranks in descending order
            # Value: Sum of ranks weighted (e.g., R1*15^4 + R2*15^3 + ...)
            value = sum(val * (15**(4-i)) for i, val in enumerate(hand_values_sorted))
            return HandRank.FLUSH, value, hand_values_sorted

        if is_five_card_straight:
            actual_straight_values = [5,4,3,2,1] if hand_values_sorted == [14,5,4,3,2] else hand_values_sorted
            return HandRank.STRAIGHT, actual_straight_values[0], actual_straight_values
        
        if counts[0] == 3: # Three of a kind
            # Ranks: [ThreeRank, Kicker1, Kicker2]
            three_rank = primary_ranks[0]
            kickers = sorted([primary_ranks[1], primary_ranks[2]], reverse=True)
            # Value: ThreeRank*15^2 + Kicker1*15 + Kicker2
            value = three_rank * (15**2) + kickers[0] * 15 + kickers[1]
            return HandRank.THREE_OF_A_KIND, value, [three_rank] + kickers

        if counts[0] == 2 and counts[1] == 2: # Two pair
            # Ranks: [HighPair, LowPair, Kicker]
            high_pair = primary_ranks[0]
            low_pair = primary_ranks[1]
            kicker = primary_ranks[2]
            # Value: HighPair*15^2 + LowPair*15 + Kicker
            value = high_pair * (15**2) + low_pair * 15 + kicker
            return HandRank.TWO_PAIR, value, [high_pair, low_pair, kicker]

        if counts[0] == 2: # One pair
            # Ranks: [PairRank, Kicker1, Kicker2, Kicker3]
            pair_rank = primary_ranks[0]
            kickers = sorted([primary_ranks[1], primary_ranks[2], primary_ranks[3]], reverse=True)
            # Value: PairRank*15^3 + Kicker1*15^2 + Kicker2*15 + Kicker3
            value = pair_rank * (15**3) + kickers[0] * (15**2) + kickers[1] * 15 + kickers[2]
            return HandRank.PAIR, value, [pair_rank] + kickers
        
        # High card
        # Ranks: [Kicker1, Kicker2, Kicker3, Kicker4, Kicker5]
        # Value: Kicker1*15^4 + Kicker2*15^3 + ...
        value = sum(val * (15**(4-i)) for i, val in enumerate(hand_values_sorted))
        return HandRank.HIGH_CARD, value, hand_values_sorted


    def get_hand_description(self, rank: HandRank, cards_values: List[int]) -> str:
        card_names = {14: 'A', 13: 'K', 12: 'Q', 11: 'J'}
        def name(v): return card_names.get(v, str(v))
        if not cards_values: return rank.name.replace('_', ' ')

        if rank == HandRank.ROYAL_FLUSH: return "Royal Flush"
        if rank == HandRank.STRAIGHT_FLUSH: return f"Straight Flush, {name(cards_values[0])} high"
        if rank == HandRank.FOUR_OF_A_KIND: return f"Four of a Kind, {name(cards_values[0])}s"
        if rank == HandRank.FULL_HOUSE: return f"Full House, {name(cards_values[0])}s over {name(cards_values[1])}s"
        if rank == HandRank.FLUSH: return f"Flush, {name(cards_values[0])} high"
        if rank == HandRank.STRAIGHT: return f"Straight, {name(cards_values[0])} high"
        if rank == HandRank.THREE_OF_A_KIND: return f"Three of a Kind, {name(cards_values[0])}s"
        if rank == HandRank.TWO_PAIR: return f"Two Pair, {name(cards_values[0])}s and {name(cards_values[1])}s"
        if rank == HandRank.PAIR: return f"Pair of {name(cards_values[0])}s"
        return f"High Card, {name(cards_values[0])}"

    def distribute_winnings(self, room: Room, winners_eval: Dict[str, HandEvaluation]):
        if not winners_eval and not room.pot: return

        # Handle case where everyone folded (one winner by default)
        if len(winners_eval) == 1 and room.pot > 0:
            winner_id = list(winners_eval.keys())[0]
            player = room.players[winner_id]
            player.money += room.pot
            if not player.is_ai:
                player.stats.total_winnings += room.pot
                player.stats.hands_won += 1
                if room.pot > player.stats.biggest_pot: player.stats.biggest_pot = room.pot
            if room.pot > self.global_stats['biggest_pot']: self.global_stats['biggest_pot'] = room.pot
            room.pot = 0
            return

        # Sort side pots from smallest to largest contributor cap
        # This logic is complex. True side pot calculation would map players to bets.
        # For now, a simplified approach if using room.side_pots:
        
        all_pots_to_distribute = []
        if room.side_pots:
            for sp in sorted(room.side_pots, key=lambda x: x.amount): # Process smaller side pots first
                all_pots_to_distribute.append({'amount': sp.amount, 'eligible_ids': sp.eligible_players})
        
        # Add main pot (remaining after side pots)
        # The main pot definition depends on how side_pots are calculated relative to room.pot
        # Let's assume room.pot is total, side_pots are parts of it.
        # Or, side_pots are calculated, and remaining is main. The current code for side_pots calculates contributions.
        
        # Let's re-think distribution with side_pots as defined.
        # The total pot is sum of player.total_bet_this_hand.
        # Side pots are layered.
        
        players_in_showdown = {pid: eval_ for pid, eval_ in winners_eval.items() if pid in room.players}

        if not players_in_showdown: # Everyone folded, pot should've been awarded.
             logger.warning(f"Distribute winnings called with no players in showdown for room {room.code}")
             # If pot remains, refund it or award to last active (complex)
             # For now, assume this means hand ended before showdown with a single winner
             if room.pot > 0 and len(room.get_players_in_hand()) == 1:
                 winner = room.get_players_in_hand()[0]
                 winner.money += room.pot
                 logger.info(f"Awarding remaining pot {room.pot} to last player {winner.id}")
                 room.pot = 0
             return


        # Pots (smallest to largest based on player contribution levels)
        sorted_total_bets = sorted(list(set(p.total_bet_this_hand for p in room.players.values() if p.id in players_in_showdown)))
        
        awarded_from_total_bets = 0
        last_bet_level = 0

        for bet_level in sorted_total_bets:
            # Contribution for this layer of the pot
            contribution_this_layer = bet_level - last_bet_level
            if contribution_this_layer <= 0: continue

            # Players eligible for this layer (those who bet at least this much)
            eligible_player_ids_for_layer = {
                p.id for p in room.players.values() 
                if p.id in players_in_showdown and p.total_bet_this_hand >= bet_level
            }
            if not eligible_player_ids_for_layer: continue

            pot_this_layer = contribution_this_layer * len([
                p for p in room.players.values() if p.total_bet_this_hand >= bet_level # all players who contributed to this level
            ])
            
            if pot_this_layer <=0 : continue

            # Determine winners for this layer's pot
            layer_winners_eval = {pid: players_in_showdown[pid] for pid in eligible_player_ids_for_layer if pid in players_in_showdown}
            if not layer_winners_eval: continue
            
            best_hand_rank = max(ev.rank for ev in layer_winners_eval.values())
            best_hands_this_rank = [ev for ev in layer_winners_eval.values() if ev.rank == best_hand_rank]
            best_hand_value = max(ev.value for ev in best_hands_this_rank)
            
            pot_actual_winners = [
                pid for pid, ev in layer_winners_eval.items() 
                if ev.rank == best_hand_rank and ev.value == best_hand_value
            ]

            if not pot_actual_winners: continue # Should not happen

            winnings_per_winner = pot_this_layer // len(pot_actual_winners)
            remainder = pot_this_layer % len(pot_actual_winners)

            for i, winner_id in enumerate(pot_actual_winners):
                player = room.players[winner_id]
                amount_won = winnings_per_winner + (1 if i < remainder else 0)
                player.money += amount_won
                awarded_from_total_bets += amount_won
                if not player.is_ai:
                    player.stats.total_winnings += amount_won
                    player.stats.hands_won += 1 # Simplified: count any pot win as hand won
                    if amount_won > player.stats.biggest_pot: player.stats.biggest_pot = amount_won
                if amount_won > self.global_stats['biggest_pot']: self.global_stats['biggest_pot'] = amount_won
            
            last_bet_level = bet_level

        # Verify total pot distribution
        total_pot_collected = sum(p.total_bet_this_hand for p in room.players.values())
        if awarded_from_total_bets != total_pot_collected:
             logger.warning(f"Pot distribution mismatch in room {room.code}. Collected: {total_pot_collected}, Awarded: {awarded_from_total_bets}. Pot: {room.pot}")
             # If there's a discrepancy, it might be due to rounding or logic error.
             # Distribute remaining room.pot if any, but ideally total_bet_this_hand covers everything.
             if room.pot > awarded_from_total_bets and total_pot_collected == room.pot: # If room.pot was the true total
                 # This part is tricky, means the side pot logic might not align with room.pot
                 pass


        room.pot = 0 # All bets are now distributed or part of side pots handled.
        room.side_pots = [] # Clear side pots after distribution.

    def save_hand_history(self, room: Room, winners_eval: Dict[str, HandEvaluation]):
        winner_info = []
        if winners_eval:
            best_rank = max(ev.rank for ev in winners_eval.values())
            best_hands_this_rank = [ev for ev in winners_eval.values() if ev.rank == best_rank]
            best_value = max(ev.value for ev in best_hands_this_rank)
            
            winner_ids = [pid for pid, ev in winners_eval.items() if ev.rank == best_rank and ev.value == best_value]
            if winner_ids:
                first_winner_id = winner_ids[0]
                winning_hand_desc = winners_eval[first_winner_id].description
                winner_info = [{"id": wid, "name": room.players[wid].name, "hand_desc": winning_hand_desc} for wid in winner_ids]

        hand_data = {
            'hand_number': room.hand_number, 'timestamp': datetime.now().isoformat(),
            'players': {pid: {
                'name': p.name, 'position': p.position,
                'cards': [{'suit': c.suit, 'rank': c.rank} for c in p.cards] if p.cards else [],
                'total_bet_this_hand': p.total_bet_this_hand,
                'final_money': p.money
            } for pid, p in room.players.items()},
            'community_cards': [{'suit': c.suit, 'rank': c.rank} for c in room.community_cards],
            'total_pot_collected': sum(p.total_bet_this_hand for p in room.players.values()),
            'winners': winner_info
        }
        room.hand_history.append(hand_data)
        if len(room.hand_history) > 50: room.hand_history = room.hand_history[-50:]

    def update_tournament(self, room: Room):
        if room.settings.game_mode != GameMode.TOURNAMENT: return
        if datetime.now() >= room.tournament_next_level:
            room.tournament_level += 1
            room.settings.small_blind = int(room.settings.small_blind * 1.5)
            room.settings.big_blind = int(room.settings.big_blind * 1.5)
            room.tournament_next_level = datetime.now() + timedelta(seconds=TOURNAMENT_BLIND_INCREASE_INTERVAL)
            if room.tournament_level % 5 == 0:
                room.phase = GamePhase.TOURNAMENT_BREAK; room.paused = True
                room.pause_reason = "Tournament break - 5 minutes"
                asyncio.create_task(self.resume_tournament_after_break(room.code))

    async def resume_tournament_after_break(self, room_code: str):
        await asyncio.sleep(300)
        if room_code in self.rooms:
            room = self.rooms[room_code]
            room.paused = False; room.pause_reason = ""; room.phase = GamePhase.WAITING

    def end_tournament(self, room: Room):
        # Filter out AI players for ranking display purposes if needed, or rank all.
        players_for_ranking = [p for p in room.players.values() if not p.is_ai] # Example: Rank only humans
        # If ranking all: players_for_ranking = list(room.players.values())

        # Sort players by money, then by elimination order for ties in money (e.g., 0)
        # This requires tracking elimination time or order, not currently done.
        # Simplified: sort by money.
        
        # Set final rankings for human players
        human_players = sorted([p for p in room.players.values() if not p.is_ai], key=lambda p: p.money, reverse=True)
        
        # Consider players who were eliminated earlier. Their status is ELIMINATED.
        # A proper ranking needs elimination order.
        # Simplified: rank current money state.
        
        # Assign ranks
        current_rank = 1
        for p_list in [human_players]: # Could add AI if desired
            for player in p_list:
                player.tournament_rank = current_rank
                current_rank +=1
        
        logger.info(f"Tournament ended in room {room.code}. Final rankings determined.")


    async def auto_start_next_hand(self, room_code: str):
        await asyncio.sleep(5)
        if room_code in self.rooms:
            room = self.rooms[room_code]
            active_players_overall = [p for p in room.players.values() if p.money > 0 and p.status != PlayerStatus.ELIMINATED]
            if room.phase == GamePhase.WAITING and len(active_players_overall) >= room.settings.min_players:
                self.start_game(room_code)

    def add_chat_message(self, room_code: str, player_id: str, message: str):
        if room_code not in self.rooms: return
        room = self.rooms[room_code]; player_name = "Spectator"; player_color = "#ffffff"
        if player_id in room.players:
            player = room.players[player_id]
            player_name = player.name; player_color = player.color
        chat_msg = {"id": str(uuid.uuid4()), "player_id": player_id, "player_name": player_name,
                    "player_color": player_color, "message": message, "timestamp": time.time(),
                    "formatted_time": datetime.now().strftime("%H:%M:%S")}
        room.chat_messages.append(chat_msg)
        if len(room.chat_messages) > MAX_CHAT_MESSAGES: room.chat_messages = room.chat_messages[-MAX_CHAT_MESSAGES:]
        room.update_activity()

    def check_rate_limit(self, player_id: str, limit_type: str = "message") -> bool:
        now = time.time()
        rate_limit_dict = self.rate_limits if limit_type == "message" else self.action_rate_limits
        max_per_second = RATE_LIMIT_MESSAGES_PER_SECOND if limit_type == "message" else RATE_LIMIT_ACTIONS_PER_SECOND
        rate_limit_dict[player_id] = [t for t in rate_limit_dict[player_id] if now - t < 1.0]
        if len(rate_limit_dict[player_id]) >= max_per_second: return False
        rate_limit_dict[player_id].append(now)
        return True

    def cleanup_inactive_rooms(self):
        current_time = datetime.now(); rooms_to_delete = []
        for room_code, room in self.rooms.items():
            if current_time - room.last_activity > timedelta(seconds=SESSION_TIMEOUT):
                # Check if only AI players are left or truly inactive
                human_player_active = any(not p.is_ai and p.connection_id for p in room.players.values())
                if not human_player_active and not room.spectators:
                     rooms_to_delete.append(room_code)
        for room_code in rooms_to_delete:
            logger.info(f"Cleaning up inactive room {room_code}")
            # Cancel any pending AI actions for this room
            for player_id in list(self.ai_pending_actions.keys()):
                if player_id in self.rooms[room_code].players:
                    self.ai_pending_actions[player_id].cancel()
                    del self.ai_pending_actions[player_id]
            del self.rooms[room_code]
    
    async def _ai_take_action(self, room_code: str, player_id: str):
        try:
            await asyncio.sleep(AI_ACTION_DELAY) # Simulate thinking
            if room_code not in self.rooms or player_id not in self.rooms[room_code].players:
                return # Room or player gone

            room = self.rooms[room_code]
            player = room.players[player_id]

            if not player.can_act(): return
            
            # Ensure it's still this AI's turn
            active_players = room.get_active_players()
            if not active_players or active_players[room.current_player_index % len(active_players)].id != player_id:
                return


            available_actions = self.get_available_actions(room, player_id)
            if not available_actions: return # No actions available

            chosen_action_info = None
            
            # Basic AI: Prioritize check/call, then small raise, then fold. Rarely all-in.
            can_check = any(a['action'] == 'check' for a in available_actions)
            can_call = any(a['action'] == 'call' for a in available_actions)
            can_raise = any(a['action'] == 'raise' for a in available_actions)
            can_all_in = any(a['action'] == 'all_in' for a in available_actions)

            rand_choice = random.random()

            if can_check and rand_choice < 0.6: # 60% chance to check
                chosen_action_info = next(a for a in available_actions if a['action'] == 'check')
            elif can_call and rand_choice < 0.8: # 20% chance to call (if check failed or not available)
                chosen_action_info = next(a for a in available_actions if a['action'] == 'call')
            elif can_raise and rand_choice < 0.9 and player.money > room.settings.big_blind * 2: # 10% chance to raise small
                raise_action = next(a for a in available_actions if a['action'] == 'raise')
                raise_amount = min(raise_action['min_amount'] * 2, raise_action['max_amount']) # Raise 2x min_raise or max
                if player.money >= raise_amount: # Check if player has enough for this specific raise amount
                     chosen_action_info = {'action': 'raise', 'amount': raise_amount}

            if not chosen_action_info and can_call: # Fallback to call if other choices failed
                chosen_action_info = next(a for a in available_actions if a['action'] == 'call')
            
            if not chosen_action_info and can_all_in and player.money < room.settings.big_blind * 10 and random.random() < 0.1: # Desperate All-in
                 chosen_action_info = next(a for a in available_actions if a['action'] == 'all_in')


            if not chosen_action_info: # Default to fold if nothing else, or check if possible
                if can_check: chosen_action_info = next(a for a in available_actions if a['action'] == 'check')
                else: chosen_action_info = next(a for a in available_actions if a['action'] == 'fold')


            action_type = PlayerAction(chosen_action_info['action'])
            action_amount = chosen_action_info.get('amount', 0)
            
            logger.info(f"AI {player.name} in room {room_code} performs action: {action_type.value} {action_amount if action_amount > 0 else ''}")
            self.player_action(room_code, player_id, action_type, action_amount)

        except asyncio.CancelledError:
            logger.info(f"AI action for {player_id} in {room_code} cancelled.")
        except Exception as e:
            logger.error(f"Error in AI action for {player_id} in {room_code}: {e}")
        finally:
            if player_id in self.ai_pending_actions:
                del self.ai_pending_actions[player_id]


    def check_ai_turn(self, room_code: str):
        if room_code not in self.rooms: return
        room = self.rooms[room_code]
        if room.phase in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER] or room.paused:
            return

        active_players = room.get_active_players()
        if not active_players or not (0 <= room.current_player_index < len(active_players)):
            return
            
        current_player = active_players[room.current_player_index]
        if current_player.is_ai and current_player.can_act():
            if current_player.id not in self.ai_pending_actions: # Prevent multiple tasks for same AI
                task = asyncio.create_task(self._ai_take_action(room_code, current_player.id))
                self.ai_pending_actions[current_player.id] = task


    def get_game_state(self, room_code: str, player_id: str) -> dict:
        if room_code not in self.rooms: return {}
        room = self.rooms[room_code]; is_player = player_id in room.players and not room.players[player_id].is_ai
        is_spectator = player_id in room.spectators
        active_players = room.get_active_players(); current_player_obj = None
        if active_players and 0 <= room.current_player_index < len(active_players):
            current_player_obj = active_players[room.current_player_index]
        
        players_data = {}
        for pid, p in room.players.items():
            player_data = {
                "id": p.id, "name": p.name, "money": p.money, "current_bet": p.current_bet,
                "total_bet_this_hand": p.total_bet_this_hand, "status": p.status.value,
                "position": p.position, "last_action": p.last_action.value if p.last_action else None,
                "avatar": p.avatar, "color": p.color, "is_dealer": p.is_dealer,
                "is_small_blind": p.is_small_blind, "is_big_blind": p.is_big_blind,
                "time_bank": p.time_bank, "is_current_player": current_player_obj and current_player_obj.id == pid,
                "tournament_rank": p.tournament_rank, "is_ai": p.is_ai,
                "stats": asdict(p.stats) if not p.is_ai else PlayerStats().__dict__ # Send default for AI
            }
            show_cards = (pid == player_id and not p.is_ai) or \
                         (is_spectator and room.phase == GamePhase.SHOWDOWN) or \
                         room.phase == GamePhase.SHOWDOWN or \
                         (p.is_ai and room.phase == GamePhase.SHOWDOWN) # Show AI cards at showdown
            
            if show_cards and p.cards:
                player_data["cards"] = [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in p.cards]
            elif p.cards: # Player has cards, but not shown to this requester
                player_data["cards"] = [{"suit": "back", "rank": "back", "id": f"back_{i}_{p.id}"} for i in range(len(p.cards))]
            else: # No cards (e.g. player not in hand or waiting)
                player_data["cards"] = []

            players_data[pid] = player_data
        
        game_state = {
            "room_code": room.code, "room_name": room.name, "phase": room.phase.value, "pot": room.pot,
            "current_bet": room.current_bet, "min_raise": room.min_raise,
            "current_player_id": current_player_obj.id if current_player_obj else None,
            "dealer_index": room.dealer_index, "players": players_data,
            "community_cards": [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in room.community_cards],
            "chat_messages": room.chat_messages[-20:], "is_player": is_player, "is_spectator": is_spectator,
            "spectator_count": len(room.spectators), "hand_number": room.hand_number,
            "settings": {
                "small_blind": room.settings.small_blind, "big_blind": room.settings.big_blind, "ante": room.settings.ante,
                "max_players": room.settings.max_players, "game_mode": room.settings.game_mode.value,
                "auto_fold_timeout": room.settings.auto_fold_timeout, "num_ai_players": room.settings.num_ai_players
            },
            "tournament_info": {
                "level": room.tournament_level,
                "next_level_time": room.tournament_next_level.isoformat() if room.settings.game_mode == GameMode.TOURNAMENT else None
            } if room.settings.game_mode == GameMode.TOURNAMENT else None,
            "side_pots": [{"amount": sp.amount, "eligible_players_count": len(sp.eligible_players)} for sp in room.side_pots], # Fixed key
            "paused": room.paused, "pause_reason": room.pause_reason,
            "time_left": max(0, room.settings.auto_fold_timeout - (time.time() - room.last_action_time)) if current_player_obj and not current_player_obj.is_ai else 0,
            "can_act": is_player and current_player_obj and current_player_obj.id == player_id and room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER, GamePhase.TOURNAMENT_BREAK] and not room.paused,
            "available_actions": self.get_available_actions(room, player_id) if is_player and current_player_obj and current_player_obj.id == player_id else []
        }
        return game_state

    def get_available_actions(self, room: Room, player_id: str) -> List[Dict]:
        if player_id not in room.players: return []
        player = room.players[player_id]
        if not player.can_act() or player.is_ai: return [] # AI actions decided server-side
        
        actions = [{"action": "fold", "label": "Fold"}]
        if room.current_bet == player.current_bet:
            actions.append({"action": "check", "label": "Check"})
        else:
            call_amount = min(room.current_bet - player.current_bet, player.money)
            if call_amount > 0 : actions.append({"action": "call", "label": f"Call ${call_amount}", "amount": call_amount})
            elif call_amount == 0 and player.money > 0: # Can check if current_bet already matched (e.g. BB pre-flop no raise)
                 actions.append({"action": "check", "label": "Check"})


        # Raise: must have more money than needed to just call the current bet
        money_after_call = player.money - max(0, room.current_bet - player.current_bet)
        if money_after_call > 0:
            # Min raise amount is the greater of BB or the last raise increment.
            # This is added ON TOP of the current bet to reach the new total bet.
            min_raise_increment = room.min_raise 
            # Max raise is all their remaining money AFTER calling the current bet.
            max_raise_increment = money_after_call

            if max_raise_increment >= min_raise_increment : # Can make at least a min raise
                actions.append({
                    "action": "raise", "label": "Raise",
                    "min_amount": min_raise_increment, # This is the increment
                    "max_amount": max_raise_increment  # This is the increment
                })
        
        if player.money > 0:
            actions.append({"action": "all_in", "label": f"All-In ${player.money}", "amount": player.money})
        return actions

    def get_room_list(self) -> List[Dict]:
        return [{
            "code": rc, "name": r.name, "players": len(r.players), "max_players": r.settings.max_players,
            "spectators": len(r.spectators), "phase": r.phase.value, "game_mode": r.settings.game_mode.value,
            "small_blind": r.settings.small_blind, "big_blind": r.settings.big_blind,
            "created_at": r.created_at.isoformat(), "has_password": bool(r.settings.password)
        } for rc, r in self.rooms.items() if r.room_type == RoomType.PUBLIC]

game = AdvancedPokerGame()

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
    num_ai_players: int = 0

class JoinRoomRequest(BaseModel):
    room_code: str
    player_name: str = "Anonymous"
    password: str = ""

@asynccontextmanager
async def lifespan(app: FastAPI):
    logger.info("Starting advanced poker game server...")
    game_task = asyncio.create_task(game_loop())
    cleanup_task = asyncio.create_task(cleanup_loop())
    yield
    logger.info("Shutting down poker game server...")
    game.running = False
    game_task.cancel(); cleanup_task.cancel()
    # Cancel all pending AI actions
    for task in game.ai_pending_actions.values(): task.cancel()
    game.ai_pending_actions.clear()
    try: await asyncio.gather(game_task, cleanup_task, return_exceptions=True)
    except asyncio.CancelledError: pass

app = FastAPI(title="Advanced 3D Multiplayer Poker", description="Professional casino-quality poker game", version="2.0.1", lifespan=lifespan)
app.add_middleware(CORSMiddleware, allow_origins=["*"], allow_credentials=True, allow_methods=["*"], allow_headers=["*"])

async def game_loop():
    while game.running:
        try:
            current_time = time.time()
            for room_code, room in list(game.rooms.items()):
                if room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER, GamePhase.TOURNAMENT_BREAK] and not room.paused:
                    active_players = room.get_active_players()
                    if active_players and 0 <= room.current_player_index < len(active_players):
                        current_player = active_players[room.current_player_index]
                        if not current_player.is_ai and current_time - room.last_action_time > room.settings.auto_fold_timeout:
                            logger.info(f"Auto-folding player {current_player.name} in room {room_code}")
                            game.player_action(room_code, current_player.id, PlayerAction.FOLD)
                        elif current_player.is_ai:
                            game.check_ai_turn(room_code) # Re-check if AI needs to act (e.g. if previous task failed)


            for room_code, room in list(game.rooms.items()):
                if room.players or room.spectators:
                    room_users = set()
                    for player_id, p_obj in room.players.items():
                        if not p_obj.is_ai and p_obj.connection_id and p_obj.connection_id in game.connections:
                            room_users.add(p_obj.connection_id)
                    for spectator_id in room.spectators:
                        if spectator_id in game.connections: room_users.add(spectator_id)
                    
                    for user_id in list(room_users):
                        if user_id in game.connections:
                            try:
                                game_state = game.get_game_state(room_code, user_id)
                                await game.connections[user_id].send_json({"type": "game_state", "data": game_state})
                            except Exception as e:
                                logger.error(f"Error broadcasting to {user_id}: {e}")
                                if user_id in game.connections: del game.connections[user_id]
                                game.leave_room(user_id)
            await asyncio.sleep(1.0 / GAME_UPDATE_RATE)
        except Exception as e:
            logger.error(f"Error in game loop: {e}")
            await asyncio.sleep(1.0)

async def cleanup_loop():
    while game.running:
        try:
            game.cleanup_inactive_rooms()
            await asyncio.sleep(300)
        except Exception as e:
            logger.error(f"Error in cleanup loop: {e}")
            await asyncio.sleep(60)

@app.get("/", response_class=HTMLResponse)
async def get_poker_game_html(): return HTMLResponse(content=ADVANCED_HTML_TEMPLATE)
@app.get("/api/rooms")
async def get_rooms_api(): return {"rooms": game.get_room_list()}
@app.get("/api/stats")
async def get_stats_api(): return {"global_stats": game.global_stats, "active_rooms": len(game.rooms), "connected_players": len(game.connections)}

@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    await websocket.accept()
    player_id = str(uuid.uuid4())
    game.connections[player_id] = websocket
    try:
        await websocket.send_json({
            "type": "connected", "data": {"player_id": player_id, "server_info": {"version": "2.0.1"}}
        })
        while True:
            data = await websocket.receive_text()
            if not game.check_rate_limit(player_id, "message"):
                await websocket.send_json({"type": "error", "message": "Rate limit exceeded"}); continue
            try:
                message = WSMessage.model_validate_json(data)
                await handle_websocket_message(websocket, player_id, message)
            except ValidationError as e: await websocket.send_json({"type": "error", "message": f"Invalid message format: {e}"})
            except Exception as e: logger.error(f"Error handling message: {e}"); await websocket.send_json({"type": "error", "message": "Internal server error"})
    except WebSocketDisconnect: logger.info(f"Player {player_id} disconnected")
    except Exception as e: logger.error(f"WebSocket error for {player_id}: {e}")
    finally:
        if player_id in game.connections: del game.connections[player_id]
        game.leave_room(player_id) # This will also cancel AI task if it was this player_id

async def handle_websocket_message(websocket: WebSocket, player_id: str, message: WSMessage):
    action = message.action; payload = message.payload
    try:
        if action == "create_room":
            try:
                req_data = CreateRoomRequest(**payload)
                room_settings = GameSettings(
                    small_blind=req_data.small_blind, big_blind=req_data.big_blind,
                    max_players=min(req_data.max_players, MAX_PLAYERS_PER_ROOM),
                    game_mode=GameMode(req_data.game_mode), buy_in=req_data.buy_in,
                    password=req_data.password if req_data.password else None,
                    num_ai_players=req_data.num_ai_players
                )
                room_code = game.create_room(player_id, room_settings, req_data.room_name)
                if game.join_room(room_code, player_id, req_data.player_name):
                    await websocket.send_json({"type": "room_created", "data": {"room_code": room_code, "room_name": game.rooms[room_code].name}})
                else: await websocket.send_json({"type": "error", "message": "Failed to join created room"})
            except (ValidationError, ValueError) as e:
                await websocket.send_json({"type": "error", "message": f"Invalid room creation data: {e}"})

        elif action == "join_room":
            req_data = JoinRoomRequest(**payload)
            if game.join_room(req_data.room_code.upper(), player_id, req_data.player_name, req_data.password):
                await websocket.send_json({"type": "room_joined", "data": {"room_code": req_data.room_code.upper()}})
            else: await websocket.send_json({"type": "error", "message": "Failed to join room."})
        
        elif action == "leave_room": game.leave_room(player_id); await websocket.send_json({"type": "room_left"})
        
        elif action == "spectate":
            room_code = payload.get("room_code", "").upper(); password = payload.get("password", "")
            if game.spectate_room(room_code, player_id, password):
                await websocket.send_json({"type": "spectating", "data": {"room_code": room_code}})
            else: await websocket.send_json({"type": "error", "message": "Failed to spectate room"})
        
        elif action == "start_game":
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]
                # Ensure only owner can start
                if game.rooms[room_code].owner_id == player_id:
                    if game.start_game(room_code): await websocket.send_json({"type": "game_started"})
                    else: await websocket.send_json({"type": "error", "message": "Cannot start game (e.g. not enough players)"})
                else: await websocket.send_json({"type": "error", "message": "Only room owner can start the game"})
            else: await websocket.send_json({"type": "error", "message": "Not in a room"})

        elif action == "player_action":
            if not game.check_rate_limit(player_id, "action"):
                await websocket.send_json({"type": "error", "message": "Action rate limit exceeded"}); return
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]
                action_type_str = payload.get("action_type"); amount = payload.get("amount", 0)
                try:
                    poker_action = PlayerAction(action_type_str)
                    if game.player_action(room_code, player_id, poker_action, amount): await websocket.send_json({"type": "action_accepted"})
                    else: await websocket.send_json({"type": "error", "message": "Invalid action or not your turn"})
                except ValueError: await websocket.send_json({"type": "error", "message": "Invalid action type"})
            else: await websocket.send_json({"type": "error", "message": "Not in a room to perform action"})
        
        elif action == "send_chat":
            if player_id in game.player_rooms:
                room_code = game.player_rooms[player_id]; message_text = payload.get("message", "")
                if message_text.strip() and len(message_text) <= 200: game.add_chat_message(room_code, player_id, message_text.strip())
        
        elif action == "get_room_list": await websocket.send_json({"type": "room_list", "data": {"rooms": game.get_room_list()}})
        
        elif action == "get_hand_history":
            if player_id in game.player_rooms:
                room = game.rooms[game.player_rooms[player_id]]
                await websocket.send_json({"type": "hand_history", "data": {"history": room.hand_history[-10:]}})
        
        elif action == "pause_game":
            if player_id in game.player_rooms:
                room = game.rooms[game.player_rooms[player_id]]
                if room.owner_id == player_id:
                    room.paused = not room.paused
                    room.pause_reason = "Paused by room owner" if room.paused else ""
                    await websocket.send_json({"type": "game_paused" if room.paused else "game_resumed"})
        
        elif action == "kick_player":
            if player_id in game.player_rooms:
                room = game.rooms[game.player_rooms[player_id]]; target_player_id = payload.get("target_player_id")
                if room.owner_id == player_id and target_player_id in room.players and not room.players[target_player_id].is_ai:
                    game.leave_room(target_player_id, force=True)
                    # Notify kicker and potentially kicked player (if still connected)
                    await websocket.send_json({"type": "player_kicked", "data": {"target_id": target_player_id}})
                    if target_player_id in game.connections:
                         await game.connections[target_player_id].send_json({"type": "kicked_from_room", "data":{"room_code": room.code}})
                elif room.players.get(target_player_id, Player("","",is_ai=True)).is_ai: # check if target is AI
                     await websocket.send_json({"type": "error", "message": "Cannot kick AI players."})
                else: await websocket.send_json({"type": "error", "message": "Only room owner can kick players."})


        else: await websocket.send_json({"type": "error", "message": "Unknown action"})
    except Exception as e:
        logger.error(f"Error in handle_websocket_message for action {action}: {e}")
        await websocket.send_json({"type": "error", "message": "Server error processing request"})

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
            --primary-gold: #ffd700; --secondary-gold: #ffed4e; --dark-green: #0a2a1f;
            --light-green: #1a5d3a; --casino-red: #dc143c; --casino-blue: #191970;
            --text-light: #ffffff; --text-dark: #333333; --shadow: rgba(0, 0, 0, 0.3);
        }
        * { margin: 0; padding: 0; box-sizing: border-box; }
        body { font-family: 'Roboto', sans-serif; background: radial-gradient(ellipse at center, #0a2a1f 0%, #051a11 100%); color: var(--text-light); overflow: hidden; user-select: none; }
        #gameContainer { position: relative; width: 100vw; height: 100vh; }
        #canvas { display: block; cursor: grab; }
        #canvas:active { cursor: grabbing; }
        #loadingScreen { position: fixed; top: 0; left: 0; width: 100%; height: 100%; background: linear-gradient(135deg, #0a2a1f, #051a11); display: flex; flex-direction: column; justify-content: center; align-items: center; z-index: 10000; transition: opacity 1s ease-out; }
        .loading-logo { font-family: 'Orbitron', monospace; font-size: 4rem; font-weight: 900; color: var(--primary-gold); text-shadow: 0 0 30px rgba(255, 215, 0, 0.8); margin-bottom: 30px; animation: pulse 2s infinite; }
        .loading-spinner { width: 80px; height: 80px; border: 4px solid rgba(255, 215, 0, 0.3); border-top: 4px solid var(--primary-gold); border-radius: 50%; animation: spin 1s linear infinite; margin-bottom: 20px; }
        .loading-text { font-size: 1.2rem; color: var(--text-light); opacity: 0.8; }
        @keyframes pulse { 0%, 100% { transform: scale(1); } 50% { transform: scale(1.05); } }
        @keyframes spin { 0% { transform: rotate(0deg); } 100% { transform: rotate(360deg); } }
        .ui-overlay { position: absolute; top: 0; left: 0; width: 100%; height: 100%; pointer-events: none; z-index: 100; }
        .ui-panel { position: absolute; background: linear-gradient(135deg, rgba(0, 0, 0, 0.9), rgba(26, 93, 58, 0.8)); border-radius: 15px; padding: 20px; color: var(--text-light); pointer-events: auto; border: 2px solid var(--primary-gold); box-shadow: 0 10px 30px var(--shadow); backdrop-filter: blur(10px); transition: all 0.3s ease; }
        .ui-panel:hover { transform: translateY(-2px); box-shadow: 0 15px 40px var(--shadow); }
        .menu-panel { top: 50%; left: 50%; transform: translate(-50%, -50%); text-align: center; min-width: 450px; max-width: 90vw; max-height: 90vh; overflow-y: auto;}
        .menu-title { font-family: 'Orbitron', monospace; font-size: 3rem; font-weight: 900; color: var(--primary-gold); text-shadow: 0 0 20px rgba(255, 215, 0, 0.8); margin-bottom: 30px; animation: glow 2s ease-in-out infinite alternate; }
        @keyframes glow { from { text-shadow: 0 0 20px rgba(255, 215, 0, 0.8); } to { text-shadow: 0 0 30px rgba(255, 215, 0, 1), 0 0 40px rgba(255, 215, 0, 0.8); } }
        .menu-section { margin-bottom: 25px; padding: 20px; background: rgba(255, 255, 255, 0.05); border-radius: 10px; border: 1px solid rgba(255, 215, 0, 0.3); }
        .menu-section h3 { color: var(--secondary-gold); margin-bottom: 15px; font-size: 1.2rem; }
        .menu-section label { display: block; margin-bottom: 5px; color: var(--secondary-gold); font-size: 0.9rem; text-align: left; }
        .menu-section input[type="text"], .menu-section input[type="number"], .menu-section input[type="password"], .menu-section select { width: 100%; box-sizing: border-box; margin-bottom: 10px; }
        select { padding: 12px 15px; border: 2px solid var(--primary-gold); border-radius: 8px; background: rgba(255, 255, 255, 0.1); color: var(--text-light); font-size: 1rem; transition: all 0.3s ease; backdrop-filter: blur(10px); -webkit-appearance: none; -moz-appearance: none; appearance: none; background-image: url('data:image/svg+xml;charset=US-ASCII,%3Csvg%20xmlns%3D%22http%3A//www.w3.org/2000/svg%22%20width%3D%22292.4%22%20height%3D%22292.4%22%3E%3Cpath%20fill%3D%22%23ffd700%22%20d%3D%22M287%2069.4a17.6%2017.6%200%200%200-13-5.4H18.4c-5%200-9.3%201.8-12.9%205.4A17.6%2017.6%200%200%200%200%2082.2c0%205%201.8%209.3%205.4%2012.9l128%20127.9c3.6%203.6%207.8%205.4%2012.8%205.4s9.2-1.8%2012.8-5.4L287%2095c3.5-3.5%205.4-7.8%205.4-12.8%200-5-1.9-9.2-5.5-12.8z%22/%3E%3C/svg%3E'); background-repeat: no-repeat; background-position: right 1rem center; background-size: .65em auto; }
        select option { background: var(--dark-green); color: var(--text-light); }

        .game-hud { top: 20px; left: 20px; max-width: 350px; }
        .hud-item { display: flex; justify-content: space-between; align-items: center; margin-bottom: 10px; padding: 8px 12px; background: rgba(255, 255, 255, 0.1); border-radius: 8px; border-left: 4px solid var(--primary-gold); }
        .hud-label { font-weight: 500; color: var(--secondary-gold); }
        .hud-value { font-weight: 700; color: var(--text-light); }
        .pot-display { position: absolute; top: 15%; left: 50%; transform: translateX(-50%); background: radial-gradient(circle, rgba(255, 215, 0, 0.9), rgba(255, 237, 78, 0.7)); color: var(--text-dark); padding: 25px; border-radius: 50%; border: 4px solid var(--primary-gold); font-family: 'Orbitron', monospace; font-size: 1.8rem; font-weight: 900; text-align: center; min-width: 150px; min-height: 150px; display: flex; flex-direction: column; justify-content: center; align-items: center; box-shadow: 0 0 40px rgba(255, 215, 0, 0.6); animation: potGlow 3s ease-in-out infinite; }
        @keyframes potGlow { 0%, 100% { box-shadow: 0 0 40px rgba(255, 215, 0, 0.6); } 50% { box-shadow: 0 0 60px rgba(255, 215, 0, 0.9); } }
        .actions-panel { bottom: 30px; left: 50%; transform: translateX(-50%); display: flex; gap: 15px; flex-wrap: wrap; justify-content: center; max-width: 90vw; }
        .action-button { background: linear-gradient(135deg, var(--primary-gold), var(--secondary-gold)); border: none; border-radius: 12px; padding: 15px 25px; color: var(--text-dark); font-weight: 700; font-size: 1rem; cursor: pointer; transition: all 0.3s ease; box-shadow: 0 5px 15px rgba(255, 215, 0, 0.3); position: relative; overflow: hidden; }
        .action-button:hover { transform: translateY(-3px); box-shadow: 0 8px 25px rgba(255, 215, 0, 0.5); }
        .action-button:active { transform: translateY(-1px); }
        .action-button:disabled { background: linear-gradient(135deg, #666, #888); cursor: not-allowed; transform: none; opacity: 0.5; }
        .action-button.fold { background: linear-gradient(135deg, var(--casino-red), #ff6b6b); }
        .action-button.call { background: linear-gradient(135deg, #28a745, #20c997); }
        .action-button.raise { background: linear-gradient(135deg, var(--casino-blue), #6c5ce7); }
        .action-button.all-in { background: linear-gradient(135deg, #ff4757, #ff3742); animation: allInPulse 1s infinite; }
        @keyframes allInPulse { 0%, 100% { box-shadow: 0 5px 15px rgba(255, 71, 87, 0.3); } 50% { box-shadow: 0 5px 25px rgba(255, 71, 87, 0.6); } }
        .raise-controls { display: flex; align-items: center; gap: 10px; background: rgba(255, 255, 255, 0.1); padding: 10px; border-radius: 8px; }
        .raise-slider { flex: 1; -webkit-appearance: none; appearance: none; height: 8px; background: rgba(255, 255, 255, 0.3); border-radius: 4px; outline: none; }
        .raise-slider::-webkit-slider-thumb { -webkit-appearance: none; appearance: none; width: 20px; height: 20px; background: var(--primary-gold); border-radius: 50%; cursor: pointer; }
        .chat-panel { top: 20px; right: 20px; width: 320px; height: 400px; display: flex; flex-direction: column; }
        .chat-header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 15px; padding-bottom: 10px; border-bottom: 2px solid var(--primary-gold); }
        .chat-title { font-family: 'Orbitron', monospace; font-weight: 700; color: var(--primary-gold); }
        .chat-toggle { background: none; border: 2px solid var(--primary-gold); color: var(--primary-gold); border-radius: 6px; padding: 5px 10px; cursor: pointer; transition: all 0.3s ease; }
        .chat-toggle:hover { background: var(--primary-gold); color: var(--text-dark); }
        #chatMessages { flex: 1; overflow-y: auto; background: rgba(255, 255, 255, 0.05); border-radius: 8px; padding: 15px; margin-bottom: 15px; border: 1px solid rgba(255, 215, 0, 0.2); }
        .chat-message { margin-bottom: 10px; padding: 8px 12px; border-radius: 8px; background: rgba(255, 255, 255, 0.1); border-left: 3px solid; animation: slideInChat 0.3s ease-out; }
        @keyframes slideInChat { from { opacity: 0; transform: translateX(20px); } to { opacity: 1; transform: translateX(0); } }
        .chat-player-name { font-weight: 700; margin-right: 8px; }
        .chat-timestamp { font-size: 0.8rem; opacity: 0.6; float: right; }
        .chat-input-container { display: flex; gap: 10px; margin-top: 10px; }
        .player-cards { position: absolute; bottom: 100px; left: 50%; transform: translateX(-50%); display: flex; gap: 20px; flex-wrap: wrap; justify-content: center; max-width: 90vw; }
        .player-card { background: linear-gradient(135deg, rgba(26, 93, 58, 0.9), rgba(10, 42, 31, 0.9)); border: 2px solid var(--primary-gold); border-radius: 15px; padding: 15px; text-align: center; min-width: 150px; position: relative; transition: all 0.3s ease; backdrop-filter: blur(10px); }
        .player-card.current-player { border-color: var(--casino-red); box-shadow: 0 0 30px rgba(220, 20, 60, 0.6); animation: currentPlayerGlow 2s ease-in-out infinite; }
        @keyframes currentPlayerGlow { 0%, 100% { box-shadow: 0 0 30px rgba(220, 20, 60, 0.6); } 50% { box-shadow: 0 0 40px rgba(220, 20, 60, 0.9); } }
        .player-card.folded { opacity: 0.4; filter: grayscale(80%); }
        .player-card.all-in { border-color: var(--casino-red); animation: allInGlow 1s ease-in-out infinite; }
        @keyframes allInGlow { 0%, 100% { box-shadow: 0 0 20px rgba(255, 71, 87, 0.4); } 50% { box-shadow: 0 0 30px rgba(255, 71, 87, 0.7); } }
        .player-avatar { width: 50px; height: 50px; border-radius: 50%; background: var(--primary-gold); margin: 0 auto 10px; display: flex; align-items: center; justify-content: center; font-size: 1.5rem; font-weight: 700; color: var(--text-dark); }
        .player-name { font-weight: 700; color: var(--text-light); margin-bottom: 5px; }
        .player-money { color: var(--primary-gold); font-weight: 700; font-family: 'Orbitron', monospace; }
        .player-action { position: absolute; top: -10px; right: -10px; background: var(--casino-red); color: var(--text-light); padding: 4px 8px; border-radius: 12px; font-size: 0.8rem; font-weight: 700; animation: actionPop 0.5s ease-out; }
        @keyframes actionPop { 0% { transform: scale(0); } 80% { transform: scale(1.2); } 100% { transform: scale(1); } }
        input { padding: 12px 15px; border: 2px solid var(--primary-gold); border-radius: 8px; background: rgba(255, 255, 255, 0.1); color: var(--text-light); font-size: 1rem; transition: all 0.3s ease; backdrop-filter: blur(10px); }
        input:focus { outline: none; border-color: var(--secondary-gold); box-shadow: 0 0 15px rgba(255, 215, 0, 0.3); }
        input::placeholder { color: rgba(255, 255, 255, 0.6); }
        ::-webkit-scrollbar { width: 8px; }
        ::-webkit-scrollbar-track { background: rgba(255, 255, 255, 0.1); border-radius: 4px; }
        ::-webkit-scrollbar-thumb { background: var(--primary-gold); border-radius: 4px; }
        ::-webkit-scrollbar-thumb:hover { background: var(--secondary-gold); }
        @media (max-width: 768px) {
            .menu-panel { min-width: 300px; padding: 15px; } .menu-title { font-size: 2rem; }
            .chat-panel { width: 280px; height: 300px; } .actions-panel { bottom: 20px; gap: 10px; }
            .action-button { padding: 12px 18px; font-size: 0.9rem; } .player-cards { bottom: 80px; gap: 10px; }
            .player-card { min-width: 120px; padding: 10px; }
            .menu-section .grid-2-cols { grid-template-columns: 1fr; } /* Stack custom game options on small screens */
        }
        .hidden { display: none !important; } .fade-in { animation: fadeIn 0.5s ease-out; }
        .fade-out { animation: fadeOut 0.5s ease-out; }
        @keyframes fadeIn { from { opacity: 0; } to { opacity: 1; } }
        @keyframes fadeOut { from { opacity: 1; } to { opacity: 0; } }
        .slide-up { animation: slideUp 0.5s ease-out; }
        @keyframes slideUp { from { transform: translateY(20px); opacity: 0; } to { transform: translateY(0); opacity: 1; } }
        .tournament-info { position: absolute; top: 20px; left: 50%; transform: translateX(-50%); background: linear-gradient(135deg, rgba(25, 25, 112, 0.9), rgba(138, 43, 226, 0.8)); border: 2px solid var(--primary-gold); border-radius: 10px; padding: 15px 25px; text-align: center; backdrop-filter: blur(10px); }
        .tournament-level { font-family: 'Orbitron', monospace; font-size: 1.2rem; font-weight: 700; color: var(--primary-gold); margin-bottom: 5px; }
        .tournament-timer { color: var(--text-light); font-size: 0.9rem; }
        .notification { position: fixed; top: 20px; right: 20px; background: linear-gradient(135deg, rgba(40, 167, 69, 0.9), rgba(32, 201, 151, 0.9)); color: var(--text-light); padding: 15px 20px; border-radius: 8px; border-left: 4px solid var(--primary-gold); box-shadow: 0 5px 15px var(--shadow); z-index: 9999; animation: slideInNotification 0.5s ease-out; max-width: 300px; }
        .notification.error { background: linear-gradient(135deg, rgba(220, 20, 60, 0.9), rgba(255, 107, 107, 0.9)); }
        .notification.warning { background: linear-gradient(135deg, rgba(255, 193, 7, 0.9), rgba(255, 235, 59, 0.9)); color: var(--text-dark); }
        @keyframes slideInNotification { from { transform: translateX(100%); opacity: 0; } to { transform: translateX(0); opacity: 1; } }
        .modal { position: fixed; top: 0; left: 0; width: 100%; height: 100%; background: rgba(0, 0, 0, 0.8); display: flex; justify-content: center; align-items: center; z-index: 9999; }
        .modal-content { background: linear-gradient(135deg, rgba(10, 42, 31, 0.95), rgba(26, 93, 58, 0.95)); border: 2px solid var(--primary-gold); border-radius: 15px; padding: 30px; max-width: 80vw; max-height: 80vh; overflow-y: auto; backdrop-filter: blur(15px); }
        .modal-header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 20px; padding-bottom: 15px; border-bottom: 2px solid var(--primary-gold); }
        .modal-title { font-family: 'Orbitron', monospace; font-size: 1.5rem; font-weight: 700; color: var(--primary-gold); }
        .modal-close { background: none; border: 2px solid var(--casino-red); color: var(--casino-red); border-radius: 6px; padding: 8px 15px; cursor: pointer; font-weight: 700; transition: all 0.3s ease; }
        .modal-close:hover { background: var(--casino-red); color: var(--text-light); }
    </style>
</head>
<body>
    <div id="loadingScreen"><div class="loading-logo">🎰 ROYAL POKER 3D</div><div class="loading-spinner"></div><div class="loading-text">Loading casino experience...</div></div>
    <div id="gameContainer">
        <canvas id="canvas"></canvas>
        <div class="ui-overlay">
            <div id="menuPanel" class="ui-panel menu-panel hidden">
                <h1 class="menu-title">🎰 ROYAL POKER 3D 🎰</h1>
                <div class="menu-section"><label for="playerName">Player Name:</label><input type="text" id="playerName" placeholder="Enter your name" value="Player"></div>
                <div class="menu-section"><h3>Quick Play</h3><div style="display: flex; flex-direction: column; gap: 15px;"><button class="action-button" onclick="createQuickRoom()">🎯 Create Quick Room</button><div style="display: flex; gap: 10px;"><input type="text" id="roomCode" placeholder="Room Code" style="flex: 1;"><button class="action-button" onclick="joinRoom()">🚪 Join Room</button></div><button class="action-button" onclick="spectateRoom()">👁️ Spectate Room</button></div></div>
                <div class="menu-section"><h3>Custom Game</h3><div class="grid-2-cols" style="display: grid; grid-template-columns: 1fr 1fr; gap: 15px; margin-bottom: 15px;">
                    <div><label for="gameMode">Game Mode:</label><select id="gameMode"><option value="cash_game">Cash Game</option><option value="tournament">Tournament</option><option value="sit_and_go">Sit & Go</option></select></div>
                    <div><label for="maxPlayers">Max Players:</label><input type="number" id="maxPlayers" min="2" max="10" value="8"></div>
                    <div><label for="smallBlind">Small Blind:</label><input type="number" id="smallBlind" min="1" value="25"></div>
                    <div><label for="bigBlind">Big Blind:</label><input type="number" id="bigBlind" min="2" value="50"></div>
                    <div><label for="buyIn">Buy-in:</label><input type="number" id="buyIn" min="0" value="1000"></div>
                    <div><label for="numAiPlayers">AI Players (0-8):</label><input type="number" id="numAiPlayers" min="0" max="8" value="0"></div>
                    <div style="grid-column: 1 / -1;"><label for="roomPassword">Password (Optional):</label><input type="password" id="roomPassword" placeholder="Leave empty for public"></div>
                </div><label for="roomName">Room Name (Optional):</label><input type="text" id="roomName" placeholder="Room Name (Optional)"><button class="action-button" onclick="createCustomRoom()" style="margin-top:15px;">🎪 Create Custom Room</button></div>
                <div class="menu-section"><h3>Browse Rooms</h3><button class="action-button" onclick="showRoomList()">🏛️ Browse Public Rooms</button></div>
            </div>
            <div id="roomListModal" class="modal hidden"><div class="modal-content"><div class="modal-header"><h2 class="modal-title">🏛️ Public Rooms</h2><button class="modal-close" onclick="hideRoomList()">✕</button></div><div id="roomList" style="max-height: 400px; overflow-y: auto;"><div style="text-align: center; color: #ccc; padding: 20px;">Loading rooms...</div></div><div style="margin-top: 20px; text-align: center;"><button class="action-button" onclick="refreshRoomList()">🔄 Refresh</button></div></div></div>
            <div id="gameHUD" class="ui-panel game-hud hidden"><div class="hud-item"><span class="hud-label">🏠 Room:</span><span class="hud-value" id="currentRoom">-</span></div><div class="hud-item"><span class="hud-label">🎮 Phase:</span><span class="hud-value" id="phaseText">Waiting</span></div><div class="hud-item"><span class="hud-label">💰 Money:</span><span class="hud-value">$<span id="moneyAmount">1000</span></span></div><div class="hud-item"><span class="hud-label">🎯 My Bet:</span><span class="hud-value">$<span id="playerBetAmount">0</span></span></div><div class="hud-item"><span class="hud-label">🔥 Pot:</span><span class="hud-value">$<span id="potAmountHUD">0</span></span></div><div class="hud-item"><span class="hud-label">🃏 Hand:</span><span class="hud-value" id="handNumber">0</span></div><div style="margin-top: 20px; display: flex; flex-direction: column; gap: 10px;"><button class="action-button" onclick="startGame()" id="startGameBtn" style="width: 100%;">🚀 Start Game</button><button class="action-button" onclick="showHandHistory()" style="width: 100%;">📊 Hand History</button><button class="action-button" onclick="pauseGame()" id="pauseGameBtn" style="width: 100%;">⏸️ Pause Game</button><button class="action-button fold" onclick="leaveRoom()" style="width: 100%;">🚪 Leave Room</button></div></div>
            <div id="tournamentInfo" class="tournament-info hidden"><div class="tournament-level">🏆 Level <span id="tournamentLevel">1</span></div><div class="tournament-timer">Next level in: <span id="tournamentTimer">10:00</span></div><div style="margin-top: 5px; font-size: 0.8rem;">Blinds: $<span id="tournamentBlinds">25/50</span></div></div>
            <div id="potDisplay" class="pot-display hidden"><div style="font-size: 1rem; margin-bottom: 5px;">💰 POT</div><div>$<span id="potAmount">0</span></div><div id="sidePots" style="font-size: 0.8rem; margin-top: 5px; color: rgba(0,0,0,0.7);"></div></div>
            <div id="actionTimer" class="hidden" style="position: absolute; top: 25%; left: 50%; transform: translateX(-50%); background: rgba(220, 20, 60, 0.9); color: white; padding: 10px 20px; border-radius: 25px; font-family: 'Orbitron', monospace; font-weight: 700; font-size: 1.2rem; animation: timerPulse 1s infinite;">⏰ <span id="timerSeconds">30</span>s</div>
            <div id="actionsPanel" class="actions-panel hidden"><button class="action-button fold" onclick="playerAction('fold')" id="foldBtn">🚫 Fold</button><button class="action-button" onclick="playerAction('check')" id="checkBtn">✅ Check</button><button class="action-button call" onclick="playerAction('call')" id="callBtn">📞 Call $<span id="callAmount">0</span></button><div class="raise-controls"><span style="color: var(--primary-gold); font-weight: 700;">Raise:</span><input type="range" id="raiseSlider" class="raise-slider" min="50" max="1000" value="100" oninput="updateRaiseAmountDisplay()"><input type="number" id="raiseAmountInput" min="50" value="100" style="width: 80px;" onchange="updateRaiseSliderFromInput()"><button class="action-button raise" onclick="playerAction('raise')" id="raiseBtn">📈 Raise</button></div><button class="action-button all-in" onclick="playerAction('all_in')" id="allInBtn">🔥 ALL IN</button></div>
            <div id="chatPanel" class="chat-panel hidden"><div class="chat-header"><h3 class="chat-title">💬 Chat</h3><button class="chat-toggle" onclick="toggleChat()" id="chatToggle">−</button></div><div id="chatMessages"></div><div class="chat-input-container"><input type="text" id="chatInput" placeholder="Type message..." style="flex: 1;" onkeypress="if(event.key==='Enter') sendChat()" maxlength="200"><button class="action-button" onclick="sendChat()">Send</button></div></div>
            <div id="playerCards" class="player-cards hidden"></div>
            <div id="handHistoryModal" class="modal hidden"><div class="modal-content"><div class="modal-header"><h2 class="modal-title">📊 Hand History</h2><button class="modal-close" onclick="hideHandHistory()">✕</button></div><div id="handHistoryContent" style="max-height: 400px; overflow-y: auto;"><div style="text-align: center; color: #ccc; padding: 20px;">No hands played yet.</div></div></div></div>
        </div>
    </div>
    <script>
        let ws = null, scene, camera, renderer, controls;
        let pokerTable, tableGroup; let cards = [], chips = [], playerPositions = [];
        let cardMaterials = {}, chipMaterials = {}; let gameState = null;
        let isConnected = false, isPlayer = false, currentRoom = null;
        let animationQueue = []; let soundEnabled = true, cameraAnimating = false;
        let tableCards = [], playerCardObjects = {}, chipStacks = [];
        let dealerButton, blindButtons = []; let particleSystem;
        let chatCollapsed = false, notificationQueue = [];
        let previousGameState = null;

        function initThreeJS() {
            const canvas = document.getElementById('canvas');
            scene = new THREE.Scene(); scene.fog = new THREE.Fog(0x051a11, 15, 50);
            setupLighting();
            camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, 1000);
            camera.position.set(0, 12, 15); camera.lookAt(0, 0, 0);
            renderer = new THREE.WebGLRenderer({ canvas: canvas, antialias: true, alpha: true, powerPreference: "high-performance" });
            renderer.setSize(window.innerWidth, window.innerHeight); renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
            renderer.shadowMap.enabled = true; renderer.shadowMap.type = THREE.PCFSoftShadowMap;
            renderer.toneMapping = THREE.ACESFilmicToneMapping; renderer.toneMappingExposure = 1.2;
            renderer.outputEncoding = THREE.sRGBEncoding;
            createCasinoEnvironment(); createPokerTable(); createCardMaterials(); createChipMaterials();
            addMouseControls(); createParticleSystem(); animate();
        }
        function setupLighting() {
            const ambientLight = new THREE.AmbientLight(0x404040, 0.3); scene.add(ambientLight);
            const mainLight = new THREE.DirectionalLight(0xffffff, 0.8); mainLight.position.set(10, 20, 10); mainLight.castShadow = true;
            mainLight.shadow.mapSize.width = 2048; mainLight.shadow.mapSize.height = 2048;
            mainLight.shadow.camera.near = 0.5; mainLight.shadow.camera.far = 50;
            mainLight.shadow.camera.left = -20; mainLight.shadow.camera.right = 20; mainLight.shadow.camera.top = 20; mainLight.shadow.camera.bottom = -20;
            scene.add(mainLight);
            const tableLight1 = new THREE.SpotLight(0xffd700, 0.8, 30, Math.PI / 4, 0.5); tableLight1.position.set(0, 10, 0); tableLight1.target.position.set(0, 0, 0); tableLight1.castShadow = true; scene.add(tableLight1); scene.add(tableLight1.target);
        }
        function createCasinoEnvironment() {
            const floorGeometry = new THREE.PlaneGeometry(100, 100); const floorMaterial = new THREE.MeshLambertMaterial({ color: 0x2a0a0a, transparent: true, opacity: 0.8 });
            const floor = new THREE.Mesh(floorGeometry, floorMaterial); floor.rotation.x = -Math.PI / 2; floor.position.y = -2; floor.receiveShadow = true; scene.add(floor);
        }
        function createPokerTable() {
            tableGroup = new THREE.Group();
            const tableGeometry = new THREE.CylinderGeometry(7, 7, 0.4, 64); const tableMaterial = new THREE.MeshPhongMaterial({ color: 0x8B4513, shininess: 30, specular: 0x222222 });
            pokerTable = new THREE.Mesh(tableGeometry, tableMaterial); pokerTable.position.y = -0.2; pokerTable.receiveShadow = true; pokerTable.castShadow = true; tableGroup.add(pokerTable);
            const feltGeometry = new THREE.CylinderGeometry(6.5, 6.5, 0.05, 64); const feltMaterial = new THREE.MeshLambertMaterial({ color: 0x0d4d2a });
            const tableFelt = new THREE.Mesh(feltGeometry, feltMaterial); tableFelt.position.y = 0.25; tableFelt.receiveShadow = true; tableGroup.add(tableFelt);
            scene.add(tableGroup); createPlayerPositions();
        }
        function createPlayerPositions() { playerPositions = []; for (let i = 0; i < 10; i++) { const angle = (i / 10) * Math.PI * 2; playerPositions.push({ angle: angle, x: Math.cos(angle) * 5, z: Math.sin(angle) * 5, cardX: Math.cos(angle) * 4.2, cardZ: Math.sin(angle) * 4.2, chipX: Math.cos(angle) * 3.5, chipZ: Math.sin(angle) * 3.5 }); } }
        function createCardMaterials() { cardMaterials = {}; cardMaterials.back = new THREE.MeshPhongMaterial({ color: 0x2E4BC6, shininess: 30 }); ['hearts', 'diamonds', 'clubs', 'spades'].forEach(suit => { cardMaterials[suit] = new THREE.MeshPhongMaterial({ color: 0xFFFFFF, shininess: 20 }); }); }
        function createChipMaterials() { chipMaterials = { 1: new THREE.MeshPhongMaterial({ color: 0xFFFFFF, shininess: 50 }), 5: new THREE.MeshPhongMaterial({ color: 0xFF0000, shininess: 50 }), 25: new THREE.MeshPhongMaterial({ color: 0x00AA00, shininess: 50 }), 100: new THREE.MeshPhongMaterial({ color: 0x000000, shininess: 50 }), 500: new THREE.MeshPhongMaterial({ color: 0x800080, shininess: 50 }), 1000: new THREE.MeshPhongMaterial({ color: 0xFFD700, shininess: 50 }), }; }
        function createCard3D(suit, rank, position, rotation = 0, faceUp = true) { const cardGroup = new THREE.Group(); const cardGeometry = new THREE.PlaneGeometry(0.9, 1.3); const material = faceUp && suit !== 'back' ? cardMaterials[suit] || cardMaterials.back : cardMaterials.back; const card = new THREE.Mesh(cardGeometry, material); card.rotation.x = -Math.PI / 2; card.rotation.z = rotation; card.castShadow = true; card.receiveShadow = true; cardGroup.add(card); cardGroup.position.copy(position); return cardGroup; }
        function createChip3D(value, position, count = 1) { const chipGroup = new THREE.Group(); for (let i = 0; i < count; i++) { const chipGeometry = new THREE.CylinderGeometry(0.35, 0.35, 0.08, 16); const chipValue = getChipValue(value); const chipMaterial = chipMaterials[chipValue] || chipMaterials[1]; const chip = new THREE.Mesh(chipGeometry, chipMaterial); chip.position.y = i * 0.09; chip.castShadow = true; chip.receiveShadow = true; chipGroup.add(chip); } chipGroup.position.copy(position); return chipGroup; }
        function getChipValue(amount) { if (amount >= 1000) return 1000; if (amount >= 500) return 500; if (amount >= 100) return 100; if (amount >= 25) return 25; return 5; }
        function createParticleSystem() { const particleCount = 50; const particles = new THREE.BufferGeometry(); const particlePositions = new Float32Array(particleCount * 3); for (let i = 0; i < particleCount * 3; i += 3) { particlePositions[i] = (Math.random() - 0.5) * 50; particlePositions[i + 1] = Math.random() * 30 + 5; particlePositions[i + 2] = (Math.random() - 0.5) * 50; } particles.setAttribute('position', new THREE.BufferAttribute(particlePositions, 3)); const particleMaterial = new THREE.PointsMaterial({ color: 0xFFD700, size: 0.1, transparent: true, opacity: 0.3, blending: THREE.AdditiveBlending }); particleSystem = new THREE.Points(particles, particleMaterial); scene.add(particleSystem); }
        function addMouseControls() {
            let mouseDown = false; let mouseX = 0, mouseY = 0; let targetCameraX = 0, targetCameraZ = 15;
            const uiPanels = ['.menu-panel', '.game-hud', '.chat-panel', '.actions-panel', '.pot-display', '.modal'];
            function isMouseOverUI(eventTarget) { return uiPanels.some(selector => eventTarget.closest(selector)); }
            canvas.addEventListener('mousedown', (event) => { if (isMouseOverUI(event.target)) return; mouseDown = true; mouseX = event.clientX; mouseY = event.clientY; });
            canvas.addEventListener('mouseup', () => { mouseDown = false; });
            canvas.addEventListener('mousemove', (event) => { if (isMouseOverUI(event.target) && !mouseDown) return; if (!cameraAnimating && mouseDown) { const deltaX = event.clientX - mouseX; const deltaY = event.clientY - mouseY; targetCameraX += deltaX * 0.01; targetCameraZ += deltaY * 0.01; targetCameraZ = Math.max(8, Math.min(25, targetCameraZ)); mouseX = event.clientX; mouseY = event.clientY; } });
            canvas.addEventListener('wheel', (event) => { if (isMouseOverUI(event.target)) return; if (!cameraAnimating) { targetCameraZ += event.deltaY * 0.01; targetCameraZ = Math.max(8, Math.min(25, targetCameraZ)); } });
            function updateCamera() { if (!cameraAnimating) { const radius = targetCameraZ; camera.position.x = Math.sin(targetCameraX) * radius; camera.position.z = Math.cos(targetCameraX) * radius; camera.position.y = 12; camera.lookAt(0, 0, 0); } requestAnimationFrame(updateCamera); } updateCamera();
        }
        function animate() { requestAnimationFrame(animate); if (tableGroup) tableGroup.rotation.y += 0.0005; if (particleSystem) particleSystem.rotation.y += 0.001; processAnimationQueue(); renderer.render(scene, camera); }
        function processAnimationQueue() { if (animationQueue.length > 0) { const animation = animationQueue[0]; if (animation.update()) animationQueue.shift(); } }
        function updateTableVisuals() {
            clearTableObjects(); if (!gameState) return;
            gameState.community_cards.forEach((card, index) => { setTimeout(() => { const position = new THREE.Vector3(-2 + index * 1, 0.3, 0); const cardObj = createCard3D(card.suit, card.rank, position, 0, true); scene.add(cardObj); tableCards.push(cardObj); cardObj.scale.set(0, 0, 0); gsap.to(cardObj.scale, { duration: 0.5, x: 1, y: 1, z: 1, ease: "back.out(1.7)" }); }, index * 100); });
            const players = Object.values(gameState.players);
            players.forEach((player, index) => {
                if (index < playerPositions.length) {
                    const pos = playerPositions[index];
                    if (player.cards && player.cards.length > 0) { player.cards.forEach((card, cardIndex) => { const cardPosition = new THREE.Vector3(pos.cardX + (cardIndex - 0.5) * 0.3, 0.3, pos.cardZ); const faceUp = card.suit !== 'back'; const cardObj = createCard3D(card.suit, card.rank, cardPosition, pos.angle, faceUp); scene.add(cardObj); if (!playerCardObjects[player.id]) playerCardObjects[player.id] = []; playerCardObjects[player.id].push(cardObj); }); }
                    if (player.current_bet > 0) { const chipPosition = new THREE.Vector3(pos.chipX, 0.3, pos.chipZ); animateChipStack(chipPosition, player.current_bet); }
                }
            });
            if (gameState.pot > 0) { const potPosition = new THREE.Vector3(0, 0.3, 2); animateChipStack(potPosition, gameState.pot); }
        }
        function animateChipStack(position, amount) { const chipCount = Math.min(Math.floor(amount / getChipValue(amount)), 10); const chipStack = createChip3D(amount, position, chipCount); scene.add(chipStack); chipStacks.push(chipStack); chipStack.position.y = 5; gsap.to(chipStack.position, { duration: 0.6, y: 0.3, ease: "bounce.out" }); }
        function clearTableObjects() { tableCards.forEach(card => scene.remove(card)); tableCards = []; Object.values(playerCardObjects).forEach(cards => cards.forEach(card => scene.remove(card))); playerCardObjects = {}; chipStacks.forEach(chips => scene.remove(chips)); chipStacks = []; }
        function connectWebSocket() { const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:'; const wsUrl = `${protocol}//${window.location.host}/ws`; ws = new WebSocket(wsUrl); ws.onopen = function() { console.log('Connected'); isConnected = true; hideLoadingScreen(); showMainMenu(); showNotification('Connected to Royal Poker 3D!', 'success'); }; ws.onmessage = function(event) { const message = JSON.parse(event.data); handleServerMessage(message); }; ws.onclose = function() { console.log('Disconnected'); isConnected = false; showLoadingScreen('Connection lost. Reconnecting...'); showNotification('Connection lost. Reconnecting...', 'error'); setTimeout(connectWebSocket, 3000); }; ws.onerror = function(error) { console.error('WebSocket error:', error); showNotification('Connection error', 'error'); }; }
        function sendMessage(action, payload = {}) { if (ws && ws.readyState === WebSocket.OPEN) { ws.send(JSON.stringify({ action, payload })); } else { showNotification('Not connected', 'error'); } }
        function handleServerMessage(message) {
            console.log('Received:', message);
            switch (message.type) {
                case 'connected': if (!previousGameState) showNotification(`Welcome! Server v${message.data.server_info.version}`, 'success'); break;
                case 'room_created': case 'room_joined': currentRoom = message.data.room_code; isPlayer = true; showGameInterface(); showNotification(`Joined room ${currentRoom}`, 'success'); animateCameraToTable(); break;
                case 'spectating': currentRoom = message.data.room_code; isPlayer = false; showGameInterface(); showNotification(`Spectating room ${currentRoom}`, 'info'); animateCameraToTable(); break;
                case 'room_left': showMainMenu(); showNotification('Left room', 'info'); animateCameraToMenu(); break;
                case 'game_state': gameState = message.data; updateGameInterface(); updateTableVisuals(); break;
                case 'game_started': showNotification('Game started!', 'success'); break;
                case 'room_list': updateRoomList(message.data.rooms); break;
                case 'hand_history': updateHandHistory(message.data.history); break;
                case 'error': showNotification('Error: ' + message.message, 'error'); break;
                case 'kicked_from_room': showMainMenu(); showNotification(`Kicked from room ${message.data.room_code}`, 'error'); animateCameraToMenu(); break;
            }
        }
        function animateCameraToTable() { cameraAnimating = true; gsap.to(camera.position, { duration: 1.5, x: 0, y: 12, z: 15, ease: "power2.inOut", onComplete: () => { cameraAnimating = false; camera.lookAt(0, 0, 0); } }); }
        function animateCameraToMenu() { cameraAnimating = true; gsap.to(camera.position, { duration: 1.5, x: 0, y: 12, z: 15, ease: "power2.inOut", onComplete: () => { cameraAnimating = false; camera.lookAt(0, 0, 0); } }); }
        function hideLoadingScreen() { const loadingScreen = document.getElementById('loadingScreen'); gsap.to(loadingScreen, { duration: 1, opacity: 0, onComplete: () => loadingScreen.style.display = 'none' }); }
        function showLoadingScreen(text = 'Loading casino experience...') { const loadingScreen = document.getElementById('loadingScreen'); loadingScreen.querySelector('.loading-text').textContent = text; loadingScreen.style.display = 'flex'; gsap.to(loadingScreen, { duration: 0.5, opacity: 1 }); }
        function showMainMenu() { ['menuPanel'].forEach(id=>document.getElementById(id).classList.remove('hidden')); ['gameHUD', 'potDisplay', 'actionsPanel', 'chatPanel', 'playerCards', 'tournamentInfo', 'actionTimer', 'roomListModal', 'handHistoryModal'].forEach(id=>document.getElementById(id).classList.add('hidden')); currentRoom = null; gameState = null; isPlayer = false; previousGameState = null; clearTableObjects(); }
        function showGameInterface() { ['gameHUD', 'chatPanel', 'playerCards'].forEach(id=>document.getElementById(id).classList.remove('hidden')); ['menuPanel'].forEach(id=>document.getElementById(id).classList.add('hidden')); if (currentRoom) document.getElementById('currentRoom').textContent = currentRoom; }
        function updateGameInterface() {
            if (!gameState) return;
            document.getElementById('phaseText').textContent = gameState.phase.replace(/_/g, ' ').toUpperCase();
            document.getElementById('handNumber').textContent = gameState.hand_number;
            document.getElementById('potAmountHUD').textContent = gameState.pot.toLocaleString();
            if (gameState.pot > 0 || (gameState.side_pots && gameState.side_pots.length > 0)) {
                 document.getElementById('potDisplay').classList.remove('hidden');
                 document.getElementById('potAmount').textContent = gameState.pot.toLocaleString();
                 const sidePotsEl = document.getElementById('sidePots');
                 if (gameState.side_pots && gameState.side_pots.length > 0) { sidePotsEl.innerHTML = gameState.side_pots.map((sp, i) => `Side Pot ${i + 1}: ${sp.amount.toLocaleString()} (${sp.eligible_players_count} players)`).join('<br>'); } else { sidePotsEl.innerHTML = ''; }
            } else { document.getElementById('potDisplay').classList.add('hidden'); }

            const myPlayerId = ws ? JSON.parse(atob(ws.url.split('/ws?token=')[1] || 'e30=')).player_id || null : null; // This is example, proper ID needed
            const clientPlayerId = gameState.players && Object.values(gameState.players).find(p => p.connection_id === playerIdFromSomewhere)?.id; // Need a way to get actual client's player ID
            
            const thisClientPlayer = gameState.players[Object.keys(gameState.players).find(pid => gameState.players[pid].id === (previousGameState ? previousGameState.client_player_id_for_hud : null) || document.getElementById('playerName').value )]; //This is hacky, use actual ID
            if (gameState.is_player && gameState.players && clientPlayerId && gameState.players[clientPlayerId]) {
                document.getElementById('moneyAmount').textContent = gameState.players[clientPlayerId].money.toLocaleString();
                document.getElementById('playerBetAmount').textContent = gameState.players[clientPlayerId].current_bet.toLocaleString();
            } else { // Spectator or no specific player context
                 document.getElementById('moneyAmount').textContent = "N/A";
                 document.getElementById('playerBetAmount').textContent = "N/A";
            }


            if (gameState.tournament_info) { document.getElementById('tournamentInfo').classList.remove('hidden'); document.getElementById('tournamentLevel').textContent = gameState.tournament_info.level; document.getElementById('tournamentBlinds').textContent = `${gameState.settings.small_blind}/${gameState.settings.big_blind}`; if (gameState.tournament_info.next_level_time) updateTournamentTimer(gameState.tournament_info.next_level_time); } else { document.getElementById('tournamentInfo').classList.add('hidden'); }
            if (gameState.can_act && gameState.time_left > 0 && !gameState.players[gameState.current_player_id]?.is_ai) { document.getElementById('actionTimer').classList.remove('hidden'); document.getElementById('timerSeconds').textContent = Math.ceil(gameState.time_left); } else { document.getElementById('actionTimer').classList.add('hidden'); }
            const startBtn = document.getElementById('startGameBtn'); startBtn.style.display = (gameState.phase === 'waiting' && Object.values(gameState.players).filter(p => !p.is_ai).length >= 1 && Object.keys(gameState.players).length >= gameState.settings.min_players ) ? 'block' : 'none';
            if (gameState.can_act && gameState.available_actions && gameState.available_actions.length > 0) { document.getElementById('actionsPanel').classList.remove('hidden'); updateActionButtons(); } else { document.getElementById('actionsPanel').classList.add('hidden'); }
            updatePlayerCards(); updateChat();
            if (gameState.paused && (!previousGameState || gameState.paused !== previousGameState.paused)) { showNotification(`Game paused: ${gameState.pause_reason}`, 'warning'); }
            previousGameState = JSON.parse(JSON.stringify(gameState)); 
            if(clientPlayerId) previousGameState.client_player_id_for_hud = clientPlayerId; // Store for next update
        }
        function updateActionButtons() {
            if (!gameState || !gameState.available_actions) return; const actions = gameState.available_actions;
            ['foldBtn', 'checkBtn', 'callBtn', 'raiseBtn', 'allInBtn'].forEach(id => { const btn = document.getElementById(id); btn.disabled = true; btn.style.display = 'none'; if (id==='raiseBtn') btn.parentElement.style.display = 'none'; });
            actions.forEach(action => {
                let btn;
                switch (action.action) {
                    case 'fold': btn = document.getElementById('foldBtn'); btn.disabled = false; btn.style.display = 'inline-block'; break;
                    case 'check': btn = document.getElementById('checkBtn'); btn.disabled = false; btn.style.display = 'inline-block'; break;
                    case 'call': btn = document.getElementById('callBtn'); btn.disabled = false; btn.style.display = 'inline-block'; document.getElementById('callAmount').textContent = action.amount.toLocaleString(); break;
                    case 'raise':
                        const raiseControls = document.getElementById('raiseBtn').parentElement; raiseControls.style.display = 'flex';
                        document.getElementById('raiseBtn').disabled = false;
                        const raiseSlider = document.getElementById('raiseSlider'); const raiseAmountInput = document.getElementById('raiseAmountInput');
                        raiseSlider.min = action.min_amount; raiseSlider.max = action.max_amount;
                        raiseAmountInput.min = action.min_amount; raiseAmountInput.max = action.max_amount;
                        const currentVal = parseInt(raiseAmountInput.value);
                        if (isNaN(currentVal) || currentVal < action.min_amount || currentVal > action.max_amount) {
                            raiseAmountInput.value = action.min_amount;
                        }
                        raiseSlider.value = raiseAmountInput.value;
                        break;
                    case 'all_in': btn = document.getElementById('allInBtn'); btn.disabled = false; btn.style.display = 'inline-block'; btn.innerHTML = `🔥 ALL IN ${action.amount.toLocaleString()}`; break;
                }
            });
        }
        function updatePlayerCards() {
            const playerCardsContainer = document.getElementById('playerCards'); playerCardsContainer.innerHTML = ''; if (!gameState || !gameState.players) return;
            Object.values(gameState.players).forEach(player => {
                const playerCard = document.createElement('div'); playerCard.className = 'player-card';
                if (player.is_current_player) playerCard.classList.add('current-player');
                if (player.status === 'folded') playerCard.classList.add('folded');
                if (player.status === 'all_in') playerCard.classList.add('all-in');
                playerCard.innerHTML = `<div class="player-avatar" style="background-color: ${player.color}">${player.is_ai ? '🤖' : player.name.charAt(0).toUpperCase()}</div><div class="player-name">${player.name} ${player.is_ai ? '(AI)' : ''}</div><div class="player-money">$${player.money.toLocaleString()}</div>${player.current_bet > 0 ? `<div style="color: var(--primary-gold); font-size: 0.9rem;">Bet: $${player.current_bet.toLocaleString()}</div>` : ''}${player.last_action ? `<div class="player-action">${player.last_action.toUpperCase()}</div>` : ''}${player.is_dealer ? '<div style="position: absolute; top: -5px; left: -5px; background: gold; color: black; border-radius: 50%; width: 20px; height: 20px; display: flex; align-items: center; justify-content: center; font-size: 0.8rem; font-weight: bold;">D</div>' : ''}`;
                playerCardsContainer.appendChild(playerCard);
                gsap.from(playerCard, { duration: 0.3, scale: 0, ease: "back.out(1.7)" });
            });
        }
        function updateChat() {
            if (!gameState || !gameState.chat_messages) return; const chatMessages = document.getElementById('chatMessages'); const shouldScroll = chatMessages.scrollTop + chatMessages.clientHeight >= chatMessages.scrollHeight - 20; chatMessages.innerHTML = '';
            gameState.chat_messages.forEach(msg => { const msgDiv = document.createElement('div'); msgDiv.className = 'chat-message'; msgDiv.style.borderLeftColor = msg.player_color || '#ffffff'; msgDiv.innerHTML = `<span class="chat-player-name" style="color: ${msg.player_color || '#ffffff'}">${msg.player_name}:</span> <span>${escapeHtml(msg.message)}</span> <span class="chat-timestamp">${msg.formatted_time}</span>`; chatMessages.appendChild(msgDiv); });
            if (shouldScroll) chatMessages.scrollTop = chatMessages.scrollHeight;
        }
        function escapeHtml(unsafe) { return unsafe.replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;").replace(/'/g, "&#039;"); }
        function updateTournamentTimer(nextLevelTime) { const now = new Date(); const next = new Date(nextLevelTime); const diff = next - now; if (diff > 0) { const minutes = Math.floor(diff / 60000); const seconds = Math.floor((diff % 60000) / 1000); document.getElementById('tournamentTimer').textContent = `${minutes}:${seconds.toString().padStart(2, '0')}`; } }
        function createQuickRoom() { const playerName = document.getElementById('playerName').value.trim() || 'Anonymous'; sendMessage('create_room', { player_name: playerName, game_mode: 'cash_game', small_blind: 25, big_blind: 50, max_players: 8, num_ai_players: parseInt(document.getElementById('numAiPlayers').value) || 0 }); isPlayer = true; }
        function createCustomRoom() { const payload = { player_name: document.getElementById('playerName').value.trim() || 'Anonymous', room_name: document.getElementById('roomName').value.trim(), game_mode: document.getElementById('gameMode').value, max_players: parseInt(document.getElementById('maxPlayers').value), small_blind: parseInt(document.getElementById('smallBlind').value), big_blind: parseInt(document.getElementById('bigBlind').value), buy_in: parseInt(document.getElementById('buyIn').value), password: document.getElementById('roomPassword').value.trim(), num_ai_players: parseInt(document.getElementById('numAiPlayers').value) }; sendMessage('create_room', payload); isPlayer = true; }
        function joinRoom() { const roomCode = document.getElementById('roomCode').value.trim().toUpperCase(); const playerName = document.getElementById('playerName').value.trim() || 'Anonymous'; if (!roomCode) { showNotification('Please enter a room code', 'error'); return; } sendMessage('join_room', { room_code: roomCode, player_name: playerName }); isPlayer = true; }
        function spectateRoom() { const roomCode = document.getElementById('roomCode').value.trim().toUpperCase(); if (!roomCode) { showNotification('Please enter a room code', 'error'); return; } sendMessage('spectate', { room_code: roomCode }); isPlayer = false; }
        function leaveRoom() { sendMessage('leave_room'); }
        function startGame() { sendMessage('start_game'); }
        function pauseGame() { sendMessage('pause_game'); }
        function playerAction(action) { let payload = { action_type: action }; if (action === 'raise') { payload.amount = parseInt(document.getElementById('raiseAmountInput').value) || 0; } sendMessage('player_action', payload); }
        function sendChat() { const chatInput = document.getElementById('chatInput'); const message = chatInput.value.trim(); if (message && message.length <= 200) { sendMessage('send_chat', { message }); chatInput.value = ''; } else if (message.length > 200) { showNotification('Message too long (max 200 chars)', 'error'); } }
        function toggleChat() { chatCollapsed = !chatCollapsed; document.getElementById('chatMessages').style.display = chatCollapsed ? 'none' : 'block'; document.getElementById('chatToggle').textContent = chatCollapsed ? '+' : '−'; }
        function updateRaiseAmountDisplay() { document.getElementById('raiseAmountInput').value = document.getElementById('raiseSlider').value; }
        function updateRaiseSliderFromInput() { document.getElementById('raiseSlider').value = document.getElementById('raiseAmountInput').value; }
        function showRoomList() { document.getElementById('roomListModal').classList.remove('hidden'); sendMessage('get_room_list'); }
        function hideRoomList() { document.getElementById('roomListModal').classList.add('hidden'); }
        function refreshRoomList() { sendMessage('get_room_list'); }
        function updateRoomList(rooms) { const roomList = document.getElementById('roomList'); if (rooms.length === 0) { roomList.innerHTML = '<div style="text-align: center; color: #ccc; padding: 20px;">No public rooms</div>'; return; } roomList.innerHTML = rooms.map(room => `<div style="background: rgba(255,255,255,0.1); border-radius: 10px; padding: 15px; margin-bottom: 10px; border: 1px solid var(--primary-gold);"><div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 10px;"><strong style="color: var(--primary-gold);">${room.name}</strong><span style="background: var(--primary-gold); color: black; padding: 2px 8px; border-radius: 12px; font-size: 0.8rem;">${room.code}</span></div><div style="display: grid; grid-template-columns: 1fr 1fr; gap: 10px; font-size: 0.9rem;"><div>👥 ${room.players}/${room.max_players}</div><div>👁️ ${room.spectators}</div><div>${room.game_mode.replace('_',' ')}</div><div>💰 ${room.small_blind}/${room.big_blind}</div></div><div style="margin-top: 10px; text-align: center;"><button class="action-button" onclick="joinRoomByCode('${room.code}')" style="margin-right: 10px;">Join</button><button class="action-button" onclick="spectateRoomByCode('${room.code}')">Spectate</button></div></div>`).join(''); }
        function joinRoomByCode(roomCode) { document.getElementById('roomCode').value = roomCode; hideRoomList(); joinRoom(); }
        function spectateRoomByCode(roomCode) { document.getElementById('roomCode').value = roomCode; hideRoomList(); spectateRoom(); }
        function showHandHistory() { document.getElementById('handHistoryModal').classList.remove('hidden'); sendMessage('get_hand_history'); }
        function hideHandHistory() { document.getElementById('handHistoryModal').classList.add('hidden'); }
        function updateHandHistory(history) { const content = document.getElementById('handHistoryContent'); if (history.length === 0) { content.innerHTML = '<div style="text-align: center; color: #ccc; padding: 20px;">No hands played.</div>'; return; } content.innerHTML = history.map(hand => `<div style="background: rgba(255,255,255,0.1); border-radius: 10px; padding: 15px; margin-bottom: 15px; border: 1px solid var(--primary-gold);"><div style="display: flex; justify-content: space-between; margin-bottom: 10px;"><strong style="color: var(--primary-gold);">Hand #${hand.hand_number}</strong><span style="color: #ccc; font-size: 0.9rem;">${new Date(hand.timestamp).toLocaleString()}</span></div><div style="margin-bottom: 10px;"><strong>Community:</strong> ${hand.community_cards.map(c => `${c.rank}${c.suit[0].toUpperCase()}`).join(' ')}</div><div style="margin-bottom: 10px;"><strong>Pot:</strong> ${hand.total_pot_collected.toLocaleString()}</div><div><strong>Winners:</strong> ${hand.winners.map(w => `${w.name} (${w.hand_desc})`).join(', ') || 'N/A'}</div></div>`).join(''); }
        function showNotification(message, type = 'info') { const notification = document.createElement('div'); notification.className = `notification ${type}`; notification.textContent = message; document.body.appendChild(notification); setTimeout(() => { if (notification.parentNode) { gsap.to(notification, { duration: 0.5, x: 300, opacity: 0, onComplete: () => { if (notification.parentNode) notification.parentNode.removeChild(notification); } }); } }, 4000); }
        window.addEventListener('resize', function() { if(camera && renderer) { camera.aspect = window.innerWidth / window.innerHeight; camera.updateProjectionMatrix(); renderer.setSize(window.innerWidth, window.innerHeight); }});
        document.addEventListener('keydown', function(event) { if (!gameState || !gameState.can_act || document.getElementById('chatInput') === document.activeElement || document.getElementById('playerName') === document.activeElement || document.getElementById('roomCode') === document.activeElement ) return; const key = event.key.toLowerCase(); if (key === 'f' && !document.getElementById('foldBtn').disabled) playerAction('fold'); else if (key === 'c') { if (!document.getElementById('checkBtn').disabled) playerAction('check'); else if (!document.getElementById('callBtn').disabled) playerAction('call'); } else if (key === 'r' && !document.getElementById('raiseBtn').disabled) playerAction('raise'); else if (key === 'a' && !document.getElementById('allInBtn').disabled) playerAction('all_in'); });
        window.addEventListener('load', function() { initThreeJS(); connectWebSocket(); showLoadingScreen(); });
        const style = document.createElement('style'); style.textContent = `@keyframes timerPulse { 0%, 100% { transform: translateX(-50%) scale(1); } 50% { transform: translateX(-50%) scale(1.1); } }`; document.head.appendChild(style);
    </script>
</body>
</html>
"""

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run(app, host="0.0.0.0", port=port)
