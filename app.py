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
RATE_LIMIT_MESSAGES_PER_SECOND = 15 # For chat and general messages
RATE_LIMIT_ACTIONS_PER_SECOND = 2 # For game actions like bet, fold, etc.
MAX_CHAT_MESSAGES = 100
HAND_EVALUATION_CACHE_SIZE = 10000
AUTO_FOLD_TIMEOUT = 30  # seconds
TOURNAMENT_BLIND_INCREASE_INTERVAL = 600  # 10 minutes
MAX_ROOMS = 1000
SESSION_TIMEOUT = 3600  # 1 hour
MAX_AI_PLAYERS = 7 # Max AI players that can be added to a room

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
    is_ai: bool = False # New field for AI players
    ai_difficulty: str = "medium" # For future AI enhancements
    
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
        # Deal to players who are not sitting out or eliminated
        players_to_deal = [p for p in self.players.values() if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED]]
        for _ in range(count):
            for player in players_to_deal: # Iterate through original list to maintain order for dealing
                if player.status == PlayerStatus.ACTIVE: # Only deal if active at the moment of dealing this card
                    if self.deck:
                        player.cards.append(self.deck.pop())


    def deal_community_cards(self, count: int):
        for _ in range(count):
            if self.deck:
                self.community_cards.append(self.deck.pop())

    def get_active_players(self) -> List[Player]: # Players currently able to make decisions in the game
        return [p for p in self.players.values() if p.status not in [PlayerStatus.FOLDED, PlayerStatus.ELIMINATED, PlayerStatus.SITTING_OUT]]

    def get_seated_players(self) -> List[Player]: # All players at the table, including those sitting out (for position calculation)
        return sorted([p for p in self.players.values() if p.status != PlayerStatus.ELIMINATED], key=lambda p: p.position)


    def get_players_in_hand(self) -> List[Player]: # Players still involved in the current hand (active or all-in)
        return [p for p in self.players.values() if p.status in [PlayerStatus.ACTIVE, PlayerStatus.ALL_IN]]

    def calculate_side_pots(self):
        self.side_pots = []
        players_in_hand_sorted = sorted([p for p in self.get_players_in_hand() if p.total_bet_this_hand > 0], key=lambda p: p.total_bet_this_hand)
        
        if not players_in_hand_sorted:
            return

        all_bets = sorted(list(set(p.total_bet_this_hand for p in players_in_hand_sorted)))
        
        last_bet_level = 0
        for bet_level in all_bets:
            current_pot_amount = 0
            eligible_for_this_pot = set()
            
            for p in self.players.values(): # Consider all players who contributed to the pot
                if p.total_bet_this_hand >= bet_level:
                    current_pot_amount += (bet_level - last_bet_level)
                    eligible_for_this_pot.add(p.id)
                elif p.total_bet_this_hand > last_bet_level: # Player is all-in for less than current bet_level but more than last
                    current_pot_amount += (p.total_bet_this_hand - last_bet_level)
                    eligible_for_this_pot.add(p.id)

            if current_pot_amount > 0 and len(eligible_for_this_pot) > 1 : # Side pot only if multiple players eligible
                self.side_pots.append(SidePot(amount=current_pot_amount, eligible_players=eligible_for_this_pot))
            elif current_pot_amount > 0 and len(eligible_for_this_pot) == 1 and self.side_pots: # If only one eligible, refund to main or previous side pot
                 # This logic needs refinement, usually this means the pot just grows or money is returned if no contest
                 pass


            last_bet_level = bet_level
        
        # The main pot is what's left or the first "side pot" if all bets are equal
        if self.side_pots:
            main_pot_total = sum(sp.amount for sp in self.side_pots)
            self.pot -= main_pot_total # Adjust main pot
        # This side pot logic needs careful review for edge cases. A common approach is iterative.

    def update_activity(self):
        self.last_activity = datetime.now()

class PokerAI:
    def __init__(self, player_id: str, room_code: str, game: 'AdvancedPokerGame'):
        self.player_id = player_id
        self.room_code = room_code
        self.game = game

    async def decide_action(self):
        await asyncio.sleep(random.uniform(1.5, 4.0)) # Simulate AI "thinking" time

        if self.room_code not in self.game.rooms: return
        room = self.game.rooms[self.room_code]
        
        if self.player_id not in room.players: return
        player = room.players[self.player_id]

        # Ensure it's still this AI's turn and it can act
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
            # Attempt to fold if possible, as a fallback (though get_available_actions should always return fold)
            if self.game.player_action(self.room_code, self.player_id, PlayerAction.FOLD, 0):
                 logger.info(f"AI {player.name} performed fallback FOLD action.")
            return

        possible_action_details = {a['action']: a for a in available_actions}
        
        action_to_take = None
        action_amount = 0

        # Extremely basic AI logic:
        # Priority: Check > Call (small amounts) > Fold
        if PlayerAction.CHECK.value in possible_action_details:
            action_to_take = PlayerAction.CHECK
        elif PlayerAction.CALL.value in possible_action_details:
            call_details = possible_action_details[PlayerAction.CALL.value]
            call_amount = call_details.get('amount', 0)
            # Only call if it's less than 20% of AI's money, or random chance
            if call_amount <= player.money * 0.2 or random.random() < 0.5:
                action_to_take = PlayerAction.CALL
                action_amount = call_amount
            else: # Too expensive to call, try to fold
                 if PlayerAction.FOLD.value in possible_action_details:
                    action_to_take = PlayerAction.FOLD
        elif PlayerAction.FOLD.value in possible_action_details:
            action_to_take = PlayerAction.FOLD
        
        # If AI decides to raise (e.g. has good cards - not implemented here)
        # For now, AI will not raise proactively with this logic.
        # if PlayerAction.RAISE.value in possible_action_details and random.random() < 0.1: # 10% chance to raise min
        #     action_to_take = PlayerAction.RAISE
        #     action_amount = possible_action_details[PlayerAction.RAISE.value]['min_amount']


        if action_to_take:
            logger.info(f"AI {player.name} decided action: {action_to_take.value} with amount {action_amount}")
            if not self.game.player_action(self.room_code, self.player_id, action_to_take, action_amount):
                logger.error(f"AI {player.name} failed to perform action {action_to_take.value}")
                # Fallback if chosen action somehow fails - try to fold
                if PlayerAction.FOLD.value in possible_action_details:
                     self.game.player_action(self.room_code, self.player_id, PlayerAction.FOLD, 0)

        else: # Should ideally not happen if logic above is sound
            logger.warning(f"AI {player.name} could not decide on an action. Defaulting to FOLD.")
            if PlayerAction.FOLD.value in possible_action_details:
                self.game.player_action(self.room_code, self.player_id, PlayerAction.FOLD, 0)


class AdvancedPokerGame:
    def __init__(self):
        self.rooms: Dict[str, Room] = {}
        self.connections: Dict[str, WebSocket] = {}
        self.player_rooms: Dict[str, str] = {}
        self.player_sessions: Dict[str, str] = {}  # player_id -> session_id
        self.rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.action_rate_limits: Dict[str, List[float]] = defaultdict(list) # Separate for game actions
        self.hand_evaluation_cache: Dict[str, HandEvaluation] = {}
        self.running = True
        self.global_stats = {
            'total_hands': 0,
            'total_players': 0,
            'active_rooms': 0,
            'biggest_pot': 0
        }

    def generate_room_code(self) -> str:
        return ''.join(random.choices('ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789', k=6)) # Shorter code

    def create_room(self, owner_id: str, room_settings: GameSettings, room_name: str = None, num_ai_players: int = 0) -> str:
        if len(self.rooms) >= MAX_ROOMS:
            raise Exception("Maximum number of rooms reached")
            
        room_code = self.generate_room_code()
        while room_code in self.rooms:
            room_code = self.generate_room_code()
        
        room_name = room_name or f"Room {room_code}"
        
        new_room = Room(
            code=room_code,
            name=room_name,
            players={},
            spectators=set(),
            deck=[],
            community_cards=[],
            settings=room_settings,
            owner_id=owner_id,
            room_type=RoomType.PRIVATE if room_settings.password else RoomType.PUBLIC
        )
        self.rooms[room_code] = new_room
        
        # Add AI players
        # Ensure total players (owner + AI) does not exceed max_players
        actual_num_ai = min(num_ai_players, room_settings.max_players -1, MAX_AI_PLAYERS)

        for i in range(actual_num_ai):
            ai_player_id = f"AI_{str(uuid.uuid4())[:6]}"
            ai_player_name = f"Bot {random.choice(['Ace', 'King', 'Queen', 'Jack', 'Ten'])} {i+1}" # More thematic names
            
            ai_player = Player(
                id=ai_player_id,
                name=ai_player_name,
                money=room_settings.buy_in if room_settings.buy_in > 0 else (TOURNAMENT_STARTING_MONEY if room_settings.game_mode == GameMode.TOURNAMENT else STARTING_MONEY),
                is_ai=True,
                avatar=f"avatar_ai_{random.randint(1,5)}", # Assuming 5 AI avatars
                color=f"#{random.randint(0x50, 0xAA):02x}{random.randint(0x50, 0xAA):02x}{random.randint(0x50, 0xAA):02x}", # Muted/robotic colors
                position=i + 1 # Tentative position, will be set properly on game start
            )
            new_room.players[ai_player_id] = ai_player
        
        logger.info(f"Room {room_code} ('{room_name}') created by player {owner_id} with {actual_num_ai} AI players.")
        return room_code

    def join_room(self, room_code: str, player_id: str, player_name: str, password: str = None) -> bool:
        if room_code not in self.rooms:
            return False
        
        room = self.rooms[room_code]
        
        if room.settings.password and room.settings.password != password:
            return False
        
        if len(room.players) >= room.settings.max_players:
            return False # Room is full
        
        if player_id in room.players: # Rejoining
            room.players[player_id].connection_id = player_id # Update connection ID
            room.players[player_id].name = player_name # Allow name update on rejoin
            if room.players[player_id].status == PlayerStatus.SITTING_OUT: # If was sitting out, make active
                 room.players[player_id].status = PlayerStatus.ACTIVE
            logger.info(f"Player {player_name} ({player_id}) re-joined room {room_code}")
            self.player_rooms[player_id] = room_code
            room.update_activity()
            return True
        
        player = Player(
            id=player_id,
            name=player_name,
            # Position will be properly assigned when game starts or player sits
            position=len(room.players), # Temporary position
            money=room.settings.buy_in if room.settings.buy_in > 0 else (TOURNAMENT_STARTING_MONEY if room.settings.game_mode == GameMode.TOURNAMENT else STARTING_MONEY),
            avatar=f"avatar_{random.randint(1, 10)}",
            color=f"#{random.randint(0, 0xFFFFFF):06x}",
            connection_id=player_id
        )
        
        room.players[player_id] = player
        self.player_rooms[player_id] = room_code
        room.update_activity()
        
        logger.info(f"Player {player_name} ({player_id}) joined room {room_code}")
        return True

    def leave_room(self, player_id: str, force: bool = False):
        if player_id not in self.player_rooms:
            if player_id in self.connections: # Was connected but not in a room
                 logger.info(f"Player {player_id} (not in room) is leaving.")
            return
        
        room_code = self.player_rooms[player_id]
        if room_code not in self.rooms:
            del self.player_rooms[player_id]
            return

        room = self.rooms[room_code]
        player_name = "Unknown"
        
        if player_id in room.players:
            player = room.players[player_id]
            player_name = player.name
            
            if room.settings.game_mode == GameMode.TOURNAMENT and not force and player.status != PlayerStatus.ELIMINATED:
                player.status = PlayerStatus.SITTING_OUT # In tournaments, disconnected players sit out
                player.connection_id = None # Mark as disconnected
                logger.info(f"Player {player.name} ({player_id}) disconnected from tournament in room {room_code}, now sitting out.")
            else:
                del room.players[player_id]
                logger.info(f"Player {player.name} ({player_id}) left room {room_code}.")
        
        if player_id in room.spectators:
            room.spectators.remove(player_id)
            logger.info(f"Spectator {player_id} left room {room_code}.") # Use name if available
        
        del self.player_rooms[player_id]
        
        # If owner leaves, try to assign a new owner (human player first)
        if room.owner_id == player_id and any(not p.is_ai for p in room.players.values()):
            new_owner = next((p.id for p in room.players.values() if not p.is_ai), None)
            if new_owner:
                room.owner_id = new_owner
                logger.info(f"Room {room_code} ownership transferred to {room.players[new_owner].name}.")
            elif room.players: # Only AI left
                 room.owner_id = next(iter(room.players.keys())) # First AI becomes owner
                 logger.info(f"Room {room_code} ownership transferred to AI {room.players[room.owner_id].name}.")


        # If room becomes empty of human players and only AI, or completely empty
        if not any(not p.is_ai for p in room.players.values()) and not room.spectators:
            logger.info(f"Room {room_code} is now empty of human players/spectators. Deleting room.")
            del self.rooms[room_code]
        elif not room.players and not room.spectators: # Completely empty
            logger.info(f"Room {room_code} is empty. Deleting room.")
            del self.rooms[room_code]


    def spectate_room(self, room_code: str, player_id: str, password: str = None) -> bool:
        if room_code not in self.rooms:
            return False
        
        room = self.rooms[room_code]
        
        if room.settings.password and room.settings.password != password:
            return False
        
        room.spectators.add(player_id)
        self.player_rooms[player_id] = room_code
        room.update_activity()
        logger.info(f"Player {player_id} started spectating room {room_code}")
        return True

    def start_game(self, room_code: str, force_start: bool = False):
        if room_code not in self.rooms: return False
        room = self.rooms[room_code]
        
        # Count players ready to play (not eliminated, not already sitting out by choice before game start)
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
        room.current_bet = room.settings.big_blind # Initial bet is big blind
        room.min_raise = room.settings.big_blind
        
        # Assign positions to all seated players (human + AI, not eliminated)
        seated_players = sorted([p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED], key=lambda p: p.id) # Consistent sort for initial positions
        for i, player in enumerate(seated_players):
            player.position = i
            player.reset_for_new_hand() # Reset AI players too
            if player.money <= 0 and room.settings.game_mode != GameMode.TOURNAMENT : # Replenish AI/Player money in cash games if 0
                player.money = room.settings.buy_in if room.settings.buy_in > 0 else STARTING_MONEY
            if player.connection_id is None and not player.is_ai and player.status == PlayerStatus.ACTIVE: # If human disconnected and was active
                player.status = PlayerStatus.SITTING_OUT


        # Rotate dealer based on seated players list
        room.dealer_index = (room.dealer_index + 1) % len(seated_players)
        
        self.set_player_blinds(room, seated_players) # Use seated_players for blind setting
        
        self.post_blinds_and_ante(room) # Uses players marked as SB/BB
        
        room.deal_cards(2)
        
        room.current_player_index = self.get_first_player_to_act_idx(room, seated_players)
        room.last_action_time = time.time()
        
        self.global_stats['total_hands'] += 1
        
        logger.info(f"Game started in room {room_code}, hand #{room.hand_number}. Dealer: {seated_players[room.dealer_index].name}. First to act: {seated_players[room.current_player_index].name if room.current_player_index != -1 else 'N/A'}")
        
        # If first player to act is AI, trigger its action
        if room.current_player_index != -1 and seated_players[room.current_player_index].is_ai:
            asyncio.create_task(self.check_for_ai_turn(room_code))

        return True

    def set_player_blinds(self, room: Room, seated_players: List[Player]):
        num_seated = len(seated_players)
        if num_seated < 2: return

        # Clear previous blind statuses
        for p in seated_players:
            p.is_dealer = False
            p.is_small_blind = False
            p.is_big_blind = False
        
        # Find players who are not sitting out for blind assignment
        eligible_for_blinds = [p for p in seated_players if p.status != PlayerStatus.SITTING_OUT]
        num_eligible = len(eligible_for_blinds)

        if num_eligible < 2: # Not enough eligible players to assign blinds
            logger.warning(f"Not enough eligible players ({num_eligible}) for blinds in room {room.code}")
            # This scenario might need special handling, e.g., wait or auto-fold hand
            return

        # Rotate dealer among ELIGIBLE players for fairness if previous dealer sat out.
        # For simplicity here, we use dealer_index from seated_players. If that player is sitting out, blinds skip.
        
        dealer_player = seated_players[room.dealer_index]
        dealer_player.is_dealer = True

        # Find SB and BB among ELIGIBLE players, skipping SITTING_OUT players
        
        # Small Blind: first eligible player after dealer
        sb_player = None
        current_idx = room.dealer_index
        for _ in range(num_seated): # Max search iterations
            current_idx = (current_idx + 1) % num_seated
            if seated_players[current_idx].status != PlayerStatus.SITTING_OUT:
                sb_player = seated_players[current_idx]
                break
        
        if sb_player:
            sb_player.is_small_blind = True
            # Big Blind: first eligible player after SB
            bb_player = None
            sb_idx_in_seated = seated_players.index(sb_player)
            current_idx = sb_idx_in_seated
            for _ in range(num_seated):
                current_idx = (current_idx + 1) % num_seated
                if seated_players[current_idx].status != PlayerStatus.SITTING_OUT:
                    bb_player = seated_players[current_idx]
                    break
            if bb_player:
                bb_player.is_big_blind = True
            else: # Should not happen if num_eligible >= 2
                logger.error(f"Could not assign Big Blind in room {room.code}")
        else:
            logger.error(f"Could not assign Small Blind in room {room.code}")


    def post_blinds_and_ante(self, room: Room):
        # Post ante from all players involved in the hand (active or all-in, not sitting out from start)
        players_for_ante = [p for p in room.players.values() if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED]]

        if room.settings.ante > 0:
            for player in players_for_ante:
                ante_amount = min(room.settings.ante, player.money)
                player.money -= ante_amount
                # Ante doesn't count towards current_bet for matching, but is part of total_bet_this_hand and pot
                player.total_bet_this_hand += ante_amount 
                room.pot += ante_amount
                if player.money == 0: player.status = PlayerStatus.ALL_IN
        
        # Post blinds
        sb_player = next((p for p in room.players.values() if p.is_small_blind), None)
        bb_player = next((p for p in room.players.values() if p.is_big_blind), None)

        if sb_player:
            blind_amount = min(room.settings.small_blind, sb_player.money)
            sb_player.money -= blind_amount
            sb_player.current_bet += blind_amount
            sb_player.total_bet_this_hand += blind_amount
            room.pot += blind_amount
            if sb_player.money == 0: sb_player.status = PlayerStatus.ALL_IN
        
        if bb_player:
            blind_amount = min(room.settings.big_blind, bb_player.money)
            bb_player.money -= blind_amount
            bb_player.current_bet += blind_amount
            bb_player.total_bet_this_hand += blind_amount
            room.pot += blind_amount
            if bb_player.money == 0: bb_player.status = PlayerStatus.ALL_IN
        
        room.current_bet = room.settings.big_blind # Current bet to match is big blind


    def get_first_player_to_act_idx(self, room: Room, seated_players: List[Player]) -> int:
        num_seated = len(seated_players)
        if num_seated < 2: return -1 

        bb_player = next((p for p in seated_players if p.is_big_blind), None)
        if not bb_player: # No BB (e.g. everyone sitting out)
            logger.warning(f"No Big Blind found to determine first actor in room {room.code}")
            # Attempt to find first non-sitting out player after dealer
            start_idx = room.dealer_index
            for i in range(num_seated):
                current_player_idx = (start_idx + 1 + i) % num_seated
                if seated_players[current_player_idx].status != PlayerStatus.SITTING_OUT:
                    return current_player_idx
            return -1 # No one can act

        bb_idx_in_seated = seated_players.index(bb_player)
        
        # Find first player after BB who is not sitting out
        current_idx = bb_idx_in_seated
        for _ in range(num_seated):
            current_idx = (current_idx + 1) % num_seated
            if seated_players[current_idx].status != PlayerStatus.SITTING_OUT:
                return current_idx
        
        return -1 # Should not happen if BB was found and there are eligible players

    async def check_for_ai_turn(self, room_code: str):
        if room_code not in self.rooms: return
        room = self.rooms[room_code]

        if room.phase in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER] or room.paused:
            return

        # Use get_active_players for who can currently act, but map current_player_index to the original seated_players list
        seated_players = room.get_seated_players() # These are the players with fixed positions for the hand
        if not seated_players or not (0 <= room.current_player_index < len(seated_players)):
            return

        current_player_at_table = seated_players[room.current_player_index]
        
        # The actual player object from room.players dict
        current_player_obj = room.players.get(current_player_at_table.id)

        if current_player_obj and current_player_obj.is_ai and current_player_obj.can_act():
            # Check if it's really this AI's turn based on current active players list
            active_players_for_turn_check = room.get_active_players()
            if active_players_for_turn_check:
                 # Find the AI in the active players list to confirm its turn
                 # This is tricky because current_player_index refers to seated_players
                 # A better way: who is next to act based on game logic?
                 # For now, assume if seated_players[room.current_player_index] is AI and can_act(), it's its turn.
                logger.info(f"AI player {current_player_obj.name}'s turn in room {room_code}")
                ai_instance = PokerAI(current_player_obj.id, room_code, self)
                asyncio.create_task(ai_instance.decide_action())


    def player_action(self, room_code: str, player_id: str, action: PlayerAction, amount: int = 0) -> bool:
        if room_code not in self.rooms: return False
        room = self.rooms[room_code]
        
        if player_id not in room.players: return False
        player = room.players[player_id]

        # Determine current actor based on room.current_player_index and seated_players
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
            player.last_action_time = time.time() # Player specific
            room.last_action_time = time.time() # Room specific, for timeout
            
            if room.phase != GamePhase.WAITING: # Don't count sit_in/sit_out as hands_played
                 player.stats.hands_played += 1
            
            self.advance_game(room_code) # This will handle moving to next player or phase
        
        return success

    def process_player_action(self, room: Room, player: Player, action: PlayerAction, amount: int) -> bool:
        # Ensure amounts are positive for bet/raise
        amount = max(0, amount)

        if action == PlayerAction.FOLD:
            player.status = PlayerStatus.FOLDED
            logger.info(f"Player {player.name} FOLDED.")
            return True
            
        elif action == PlayerAction.CHECK:
            # Can only check if current bet to player is 0 (i.e. player.current_bet == room.current_bet)
            # Or if it's pre-flop and player is BB and current_bet is BB_amount (BB option)
            is_bb_option = (room.phase == GamePhase.PRE_FLOP and 
                            player.is_big_blind and 
                            player.current_bet == room.settings.big_blind and
                            room.current_bet == room.settings.big_blind)

            if player.current_bet < room.current_bet and not is_bb_option:
                logger.warning(f"Player {player.name} tried to CHECK but needs to call ${room.current_bet - player.current_bet}")
                return False
            logger.info(f"Player {player.name} CHECKED.")
            return True
            
        elif action == PlayerAction.CALL:
            amount_to_call = room.current_bet - player.current_bet
            if amount_to_call <= 0 : # Trying to call when no bet to call, or already matched
                # This could be a "check" if amount_to_call is 0. Or an error.
                # For simplicity, if it's 0, treat as check if valid, else error.
                if amount_to_call == 0: return self.process_player_action(room, player, PlayerAction.CHECK, 0)
                logger.warning(f"Player {player.name} tried to CALL but amount to call is ${amount_to_call}")
                return False

            actual_call = min(amount_to_call, player.money)
            
            player.money -= actual_call
            player.current_bet += actual_call
            player.total_bet_this_hand += actual_call
            room.pot += actual_call
            
            if player.money == 0:
                player.status = PlayerStatus.ALL_IN
                logger.info(f"Player {player.name} CALLED ${actual_call} and is ALL-IN.")
            else:
                logger.info(f"Player {player.name} CALLED ${actual_call}.")
            return True
            
        elif action == PlayerAction.RAISE:
            # Amount here is the additional amount to raise BY, on top of current_bet
            # So, player's new total bet for this round will be room.current_bet + amount
            
            # Min raise validation:
            # 1. Raise must be at least room.min_raise
            # 2. If going all-in for less than min_raise, it's allowed but doesn't re-open betting for already acted players.
            
            bet_needed_to_call = room.current_bet - player.current_bet
            total_player_bet_if_raise = player.current_bet + bet_needed_to_call + amount # Call + Raise Amount
            
            if player.money < (bet_needed_to_call + amount): # Not enough money for full intended raise
                # This is an all-in raise.
                actual_raise_amount_possible = player.money - bet_needed_to_call
                if actual_raise_amount_possible <=0: # Cannot even call
                    logger.warning(f"Player {player.name} tried to RAISE (all-in) but cannot even call.")
                    return False # Should have just called all-in

                amount_put_in = player.money # Goes all-in
                player.current_bet += amount_put_in
                player.total_bet_this_hand += amount_put_in
                room.pot += amount_put_in
                player.money = 0
                player.status = PlayerStatus.ALL_IN

                # Does this all-in constitute a "full" raise to re-open betting?
                # A raise is "full" if the amount raised BY (actual_raise_amount_possible) is >= room.min_raise
                if actual_raise_amount_possible >= room.min_raise:
                    room.min_raise = actual_raise_amount_possible # New min_raise for next player
                # else: min_raise stays the same, betting not fully re-opened for prior actors.

                room.current_bet = player.current_bet # Update room's current highest bet
                logger.info(f"Player {player.name} RAISED ALL-IN to ${player.current_bet} (raised by ${actual_raise_amount_possible}).")

            else: # Sufficient money for the raise
                if amount < room.min_raise:
                    logger.warning(f"Player {player.name} tried to RAISE by ${amount}, less than min_raise ${room.min_raise}")
                    return False 

                amount_put_in = bet_needed_to_call + amount
                player.money -= amount_put_in
                player.current_bet += amount_put_in
                player.total_bet_this_hand += amount_put_in
                room.pot += amount_put_in
                
                room.current_bet = player.current_bet # New highest bet
                room.min_raise = amount # The amount raised BY becomes the new min_raise
                logger.info(f"Player {player.name} RAISED to ${player.current_bet} (raised by ${amount}).")

            return True
            
        elif action == PlayerAction.ALL_IN:
            if player.money <= 0: return False # Already all-in or broke
            
            amount_to_all_in = player.money
            
            player.current_bet += amount_to_all_in
            player.total_bet_this_hand += amount_to_all_in
            room.pot += amount_to_all_in
            player.money = 0
            player.status = PlayerStatus.ALL_IN
            
            # If this all-in is a raise
            if player.current_bet > room.current_bet:
                raised_by_amount = player.current_bet - room.current_bet # This is amount player put in MORE than previous highest bet
                                                                      # More accurately, it's player.current_bet (new total) - old_room.current_bet
                                                                      # No, it should be: player.current_bet - (original player.current_bet + (room.current_bet - original player.current_bet))
                                                                      # Simpler: if player.current_bet (their total for the round) > room.current_bet (highest before their action)
                                                                      # then raised_by_amount is (player.current_bet - room.current_bet)
                # The 'raised_by_amount' is tricky. It's the additional amount over the previous highest bet.
                # If player.current_bet was X, room.current_bet was Y. Player goes all in with M.
                # New player.current_bet = X + M.
                # If X+M > Y, then they raised. The amount they *additionally* raised by, on top of calling Y, is (X+M) - Y.
                # This (X+M)-Y must be >= room.min_raise to be a "full" raise.
                
                # Let's use the amount player added this turn: amount_to_all_in
                # If (player.current_bet - amount_to_all_in) was their bet before this all-in action.
                # And room.current_bet was the target.
                # The portion of amount_to_all_in used to call is (room.current_bet - (player.current_bet - amount_to_all_in) )
                # The portion that is a raise is amount_to_all_in - that_call_portion.
                
                # Simpler: the amount they bet *more* than the previous `room.current_bet`
                amount_raised_over_current_bet = player.current_bet - room.current_bet 
                if amount_raised_over_current_bet >= room.min_raise:
                    room.min_raise = amount_raised_over_current_bet
                
                room.current_bet = player.current_bet
            
            logger.info(f"Player {player.name} went ALL-IN with ${amount_to_all_in}.")
            return True
            
        elif action == PlayerAction.SIT_OUT:
            player.status = PlayerStatus.SITTING_OUT
            logger.info(f"Player {player.name} is SITTING OUT.")
            # If it was this player's turn, the game should advance.
            return True
            
        elif action == PlayerAction.SIT_IN:
            if player.status == PlayerStatus.SITTING_OUT:
                player.status = PlayerStatus.ACTIVE
                logger.info(f"Player {player.name} is SITTING IN.")
                # Player will be dealt in next hand. If mid-hand, they wait.
                return True
            return False
        
        return False

    def advance_game(self, room_code: str):
        if room_code not in self.rooms: return
        room = self.rooms[room_code]
        
        # Check if hand is over due to folds
        players_still_in_hand = room.get_players_in_hand()
        if len(players_still_in_hand) <= 1 and room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN]:
            logger.info(f"Hand ends early in room {room_code} as only {len(players_still_in_hand)} player(s) remain.")
            self.end_hand(room_code)
            return
        
        # Check if betting round is complete
        if self.is_betting_round_complete(room):
            logger.info(f"Betting round complete for phase {room.phase.value} in room {room_code}.")
            self.advance_phase(room_code)
        else:
            self.move_to_next_player(room)
            # If next player is AI, trigger its action
            seated_players = room.get_seated_players()
            if seated_players and 0 <= room.current_player_index < len(seated_players):
                if seated_players[room.current_player_index].is_ai:
                    asyncio.create_task(self.check_for_ai_turn(room_code))


    def move_to_next_player(self, room: Room):
        seated_players = room.get_seated_players()
        if not seated_players: return

        num_seated = len(seated_players)
        
        # Start searching from current_player_index + 1
        start_search_idx = room.current_player_index
        
        for i in range(num_seated):
            next_player_candidate_idx = (start_search_idx + 1 + i) % num_seated
            candidate_player = seated_players[next_player_candidate_idx]
            
            # Player must be ACTIVE (not FOLDED, ALL_IN, SITTING_OUT, ELIMINATED) to take a turn
            if candidate_player.status == PlayerStatus.ACTIVE and candidate_player.money > 0:
                room.current_player_index = next_player_candidate_idx
                room.last_action_time = time.time()
                logger.info(f"Next player to act in room {room.code}: {candidate_player.name} (Index {room.current_player_index})")
                return
        
        # If loop completes, no one can act, which implies betting round might be over or hand ends.
        # This state should be caught by is_betting_round_complete or player count checks.
        logger.warning(f"Could not find next active player in room {room.code}. Current index: {room.current_player_index}")


    def is_betting_round_complete(self, room: Room) -> bool:
        # Players who are ACTIVE (not folded, not all-in, not sitting out)
        active_players_for_betting = [p for p in room.players.values() if p.status == PlayerStatus.ACTIVE and p.money > 0]

        if not active_players_for_betting: # No one left to act (e.g. all but one folded or all-in)
            return True
        
        # All active players must have acted in this round (last_action is not None)
        # AND their current_bet must match the room.current_bet
        # Exception: Big Blind pre-flop option.
        
        num_acted_this_round = 0
        highest_bet_this_round = room.current_bet

        for player in room.get_players_in_hand(): # Consider players still in the hand (active or all-in)
            if player.last_action is not None: # Player has taken an action in this betting round
                num_acted_this_round +=1
            
            # If player is active (not all-in) and their bet is less than highest, round is not over
            if player.status == PlayerStatus.ACTIVE and player.current_bet < highest_bet_this_round and player.money > 0:
                return False
        
        # Check if everyone who is supposed to act has acted
        # At least one bet/raise must have occurred unless it's checked around
        # And all players still in hand (not folded) who are not all-in have bet the same amount.
        
        # A simpler check:
        # All players who are not folded and not all-in must have:
        # 1. Acted in this round (last_action is not None for this round).
        # 2. Have player.current_bet == room.current_bet.
        
        # A betting round ends when:
        # 1. All players have had a turn to act.
        # 2. All players who haven't folded have bet the same amount of money for the round,
        #    OR are all-in.

        # This requires tracking who has acted *since the last raise*.
        # For now, simplified: if all non-folded, non-all-in players have current_bet == room.current_bet,
        # and have had a chance to act (e.g. last_action is not None for this round).

        # More robust: check if the turn has come back to the player who made the last aggressive action (bet/raise)
        # or if everyone has checked.
        
        # Simplified check for now:
        players_to_check = [p for p in room.players.values() if p.status == PlayerStatus.ACTIVE and p.money > 0]
        if not players_to_check: return True # All are all-in or folded

        # Check if all active players have had a turn AND their bets are settled.
        # The check `player.last_action is None` is for the very start of a betting round.
        # Once someone bets/raises, `room.current_bet` increases. Others must call/raise/fold.
        # The round ends when actions return to the last aggressor and they check or call,
        # or if everyone checks, or if all subsequent players fold to a bet/raise.

        # A common way: if all players who are still in the hand (not folded) and are not all-in
        # have voluntarily put in the same amount of chips OR have had the chance to act on the current bet.
        
        # If everyone has acted at least once this round AND all active players have bets equal to current_bet
        for p in players_to_check:
            if p.last_action is None and room.phase != GamePhase.PRE_FLOP: # Pre-flop, blinds haven't acted yet initially
                 # BB might not have last_action but can act if no raise
                if room.phase == GamePhase.PRE_FLOP and p.is_big_blind and room.current_bet == room.settings.big_blind:
                    pass # BB has option
                else:
                    return False # Someone hasn't acted
            if p.current_bet < room.current_bet:
                return False # Someone needs to call
        
        # Ensure that the player whose turn it is has already had a chance to act on current bet
        # This means if turn comes back to last raiser, and they haven't acted again.
        seated_players = room.get_seated_players()
        if seated_players and 0 <= room.current_player_index < len(seated_players):
            current_player_to_act = seated_players[room.current_player_index]
            # If this player made the last raise, and it's their turn again, the round is over if they check/call.
            # The provided logic is a simplification. True round completion is complex.
            # For now, if all active players have matching bets and have acted (or BB option), assume complete.

        return True


    def advance_phase(self, room_code: str):
        if room_code not in self.rooms: return
        room = self.rooms[room_code]
        
        # Reset per-round betting states for all players in the room
        for player in room.players.values():
            player.current_bet = 0 # Current bet for this round resets
            player.last_action = None # Reset last_action for the new round
        
        room.current_bet = 0 # Room's current bet to match for the new round is 0
        room.min_raise = room.settings.big_blind # Min raise resets to big blind for new round
        
        # Advance phase and deal cards
        if room.phase == GamePhase.PRE_FLOP:
            room.phase = GamePhase.FLOP
            room.deal_community_cards(3)
            logger.info(f"Room {room.code} advanced to FLOP. Community cards: {[str(c) for c in room.community_cards]}")
        elif room.phase == GamePhase.FLOP:
            room.phase = GamePhase.TURN
            room.deal_community_cards(1)
            logger.info(f"Room {room.code} advanced to TURN. Community cards: {[str(c) for c in room.community_cards]}")
        elif room.phase == GamePhase.TURN:
            room.phase = GamePhase.RIVER
            room.deal_community_cards(1)
            logger.info(f"Room {room.code} advanced to RIVER. Community cards: {[str(c) for c in room.community_cards]}")
        elif room.phase == GamePhase.RIVER:
            logger.info(f"Room {room.code} betting on RIVER complete, advancing to SHOWDOWN.")
            room.phase = GamePhase.SHOWDOWN 
            self.end_hand(room_code) # Showdown is part of end_hand
            return # end_hand will set next phase (WAITING or GAME_OVER)
        
        # Set first player to act in the new betting round (typically SB or first active player after dealer)
        seated_players = room.get_seated_players()
        if not seated_players: return

        # Find first player after dealer who is ACTIVE and not ALL-IN
        start_idx = room.dealer_index 
        found_next_actor = False
        for i in range(len(seated_players)):
            candidate_idx = (start_idx + 1 + i) % len(seated_players)
            player_candidate = seated_players[candidate_idx]
            if player_candidate.status == PlayerStatus.ACTIVE and player_candidate.money > 0:
                room.current_player_index = candidate_idx
                room.last_action_time = time.time()
                logger.info(f"First player to act in {room.phase.value} for room {room.code}: {player_candidate.name}")
                found_next_actor = True
                # If this player is AI, trigger its action
                if player_candidate.is_ai:
                    asyncio.create_task(self.check_for_ai_turn(room_code))
                break
        
        if not found_next_actor:
            # This can happen if all remaining players are all-in.
            # In this case, no more betting, deal remaining cards and go to showdown.
            logger.info(f"No active player found to start betting in {room.phase.value} for room {room.code}. Advancing phase again.")
            if room.phase != GamePhase.SHOWDOWN: # Avoid infinite loop if stuck
                self.advance_phase(room_code) # Keep dealing cards until showdown


    def end_hand(self, room_code: str):
        if room_code not in self.rooms: return
        room = self.rooms[room_code]
        
        if room.phase != GamePhase.SHOWDOWN: # If hand ended before showdown (e.g. all but one folded)
            room.phase = GamePhase.SHOWDOWN # Mark as showdown for winner display / pot distribution
        
        logger.info(f"Ending hand #{room.hand_number} in room {room.code}. Phase: {room.phase.value}")
        
        # Calculate side pots based on total_bet_this_hand for all involved players
        # This needs to be accurate before determining winners.
        # For simplicity, let's assume pot and total_bet_this_hand are correct for now.
        # Proper side pot calculation is complex.

        # Determine winners (even if only one player left, they "win" the pot)
        winners_evaluations = self.determine_winners(room) # Dict[player_id, HandEvaluation]
        
        # Distribute winnings (main pot and side pots)
        self.distribute_winnings(room, winners_evaluations)
        
        self.save_hand_history(room) # TODO: Include winner info in history
        
        if room.settings.game_mode == GameMode.TOURNAMENT:
            self.update_tournament(room) # Check for eliminations, blind increases
        
        # Check for game over conditions (especially in tournaments)
        active_human_players = [p for p in room.players.values() if not p.is_ai and p.status != PlayerStatus.ELIMINATED and p.money > 0]
        
        if room.settings.game_mode == GameMode.TOURNAMENT:
            # Tournament ends if one player (human or AI) has all chips, or specific conditions met
            surviving_players = [p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED and p.money > 0]
            if len(surviving_players) <= 1:
                room.phase = GamePhase.GAME_OVER
                self.end_tournament(room, surviving_players[0] if surviving_players else None)
                logger.info(f"Tournament in room {room.code} ended. Winner: {surviving_players[0].name if surviving_players else 'N/A'}")
                # Optionally, could auto-close room or reset for new game after a delay
                return # Don't auto-start next hand for game over

        room.phase = GamePhase.WAITING
        
        # Auto-start next hand if enough players are ready
        # "Ready" means not eliminated and (for humans) connected or (for AI) present.
        players_for_next_hand = [p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED and (p.is_ai or p.connection_id is not None or p.status != PlayerStatus.SITTING_OUT)]
        
        if len(players_for_next_hand) >= room.settings.min_players:
            logger.info(f"Room {room.code} has enough players ({len(players_for_next_hand)}), scheduling next hand.")
            asyncio.create_task(self.auto_start_next_hand(room_code, delay=8)) # Increased delay
        else:
            logger.info(f"Room {room.code} waiting for players for next hand ({len(players_for_next_hand)}/{room.settings.min_players}).")

    # ... (determine_winners, evaluate_hand, full_hand_evaluation, evaluate_5_card_hand, get_hand_description) ...
    # ... (distribute_winnings, save_hand_history, update_tournament, resume_tournament_after_break, end_tournament) ...
    # ... (auto_start_next_hand, add_chat_message, check_rate_limit, cleanup_inactive_rooms) ...

    def determine_winners(self, room: Room) -> Dict[str, HandEvaluation]:
        players_to_evaluate = [p for p in room.players.values() if p.status != PlayerStatus.FOLDED and p.status != PlayerStatus.ELIMINATED and p.cards]
        
        if not players_to_evaluate:
            # This can happen if everyone folded but one, that one player takes the pot by default.
            # Or if there was an error dealing cards.
            winner_by_default = next((p for p in room.get_players_in_hand()), None)
            if winner_by_default:
                 # Create a dummy evaluation for default winner
                 return {winner_by_default.id: HandEvaluation(HandRank.HIGH_CARD, 0, [], "Default Winner", [])}
            return {}

        evaluations = {}
        for player in players_to_evaluate:
            # Ensure community cards are part of evaluation if phase is appropriate
            cards_to_eval = player.cards
            if room.phase in [GamePhase.FLOP, GamePhase.TURN, GamePhase.RIVER, GamePhase.SHOWDOWN]:
                cards_to_eval = player.cards + room.community_cards
            
            if len(cards_to_eval) >= 5: # Need at least 5 cards to make a poker hand
                hand_eval = self.evaluate_hand(cards_to_eval)
                evaluations[player.id] = hand_eval
            elif player.cards : # Less than 5 cards (e.g. pre-flop all-in, no community cards yet, or hand ended early)
                # Use high card of player's hole cards if showdown occurs very early
                # This is a simplified fallback. Real poker would deal out remaining community cards.
                # For now, evaluate based on available cards. If less than 5, it's complex.
                # Let's assume for now if showdown, community cards are always dealt to 5.
                # If hand ends before flop and multiple all-ins, cards would be dealt.
                # This indicates a need for run_it_to_end_if_all_in() logic.
                 # Fallback: create a simple high card eval for their hole cards
                player.cards.sort(key=lambda c: c.value(), reverse=True)
                hc_val = sum(c.value() * (10**(2*(1-i))) for i, c in enumerate(player.cards[:2])) # Simplified value
                evaluations[player.id] = HandEvaluation(
                    rank=HandRank.HIGH_CARD, 
                    value=hc_val, 
                    cards=player.cards[:], 
                    description=f"High Card {player.cards[0].rank if player.cards else ''}",
                    kickers=[c.value() for c in player.cards]
                )


        return evaluations

    def evaluate_hand(self, cards: List[Card]) -> HandEvaluation:
        # Create cache key
        card_key = ''.join(sorted([f"{c.suit[0]}{c.rank}" for c in cards]))
        
        if card_key in self.hand_evaluation_cache:
            return self.hand_evaluation_cache[card_key]
        
        if len(cards) < 5: # Not enough cards to form a 5-card hand
             # Handle this gracefully, perhaps return a very low ranked "incomplete hand"
             # Or, if this is reached, it implies community cards should have been dealt.
             # For now, make a high card eval from what's available.
            sorted_cards = sorted(cards, key=lambda c: c.value(), reverse=True)
            hc_val = sum(c.value() * (10**(2*(len(sorted_cards)-1-i))) for i, c in enumerate(sorted_cards))
            return HandEvaluation(HandRank.HIGH_CARD, hc_val, sorted_cards, "Incomplete Hand", [c.value() for c in sorted_cards])

        hand_eval = self.full_hand_evaluation(cards)
        
        if len(self.hand_evaluation_cache) < HAND_EVALUATION_CACHE_SIZE:
            self.hand_evaluation_cache[card_key] = hand_eval
        
        return hand_eval

    def full_hand_evaluation(self, all_cards: List[Card]) -> HandEvaluation:
        from itertools import combinations
        
        best_hand_eval_details = (HandRank.HIGH_CARD, 0, []) # rank, value, best 5 cards values
        best_five_card_combo = []

        if len(all_cards) < 5: # Should be caught by evaluate_hand, but as safeguard
            # Fallback if somehow less than 5 cards reach here for full evaluation
            sorted_cards = sorted(all_cards, key=lambda c: c.value(), reverse=True)
            hc_val = sum(c.value() * (10**(2*(len(sorted_cards)-1-i))) for i, c in enumerate(sorted_cards))
            return HandEvaluation(HandRank.HIGH_CARD, hc_val, sorted_cards, 
                                  f"High Card {sorted_cards[0].rank if sorted_cards else 'N/A'}", 
                                  [c.value() for c in sorted_cards])


        for combo_cards_obj in combinations(all_cards, 5):
            current_rank, current_value, current_card_values = self.evaluate_5_card_hand(list(combo_cards_obj))
            
            if current_rank > best_hand_eval_details[0] or \
               (current_rank == best_hand_eval_details[0] and current_value > best_hand_eval_details[1]):
                best_hand_eval_details = (current_rank, current_value, current_card_values)
                best_five_card_combo = list(combo_cards_obj)
        
        return HandEvaluation(
            rank=best_hand_eval_details[0],
            value=best_hand_eval_details[1],
            cards=sorted(best_five_card_combo, key=lambda c: c.value(), reverse=True), # Store the best 5 cards
            description=self.get_hand_description(best_hand_eval_details[0], best_hand_eval_details[2]), # Use card values for desc
            kickers=best_hand_eval_details[2] # Store the value list used for ranking
        )

    def evaluate_5_card_hand(self, cards: List[Card]) -> Tuple[HandRank, int, List[int]]:
        cards.sort(key=lambda x: x.value(), reverse=True)
        values = [c.value() for c in cards]
        suits = [c.suit for c in cards]
        
        is_flush = len(set(suits)) == 1
        
        is_straight = False
        unique_values = sorted(list(set(values)), reverse=True) # For A-5 straight
        if len(unique_values) >= 5: # Standard straight check
            if all(unique_values[i] - unique_values[i+1] == 1 for i in range(4)):
                 is_straight = True
                 # Use the actual straight values, not necessarily highest 5 if more make a straight (e.g. 7 cards)
                 # This function assumes it's passed exactly 5 cards.
                 # The `values` list is already sorted list of 5 card values.
                 if values[0] - values[4] == 4 and len(set(values))==5 : # Ensure no pairs in straight values
                    is_straight = True


        # Ace-low straight (Wheel: A, 2, 3, 4, 5)
        if set(values) == {14, 2, 3, 4, 5}:
            is_straight = True
            # For ranking A-5 straight, Ace is treated as low (value 1 or 5 usually)
            # Let's use 5 as high card for wheel (A,5,4,3,2) -> values becomes [5,4,3,2,14(acts as 1)]
            # For value calculation, use [5,4,3,2,1] where 1 is ace.
            straight_values_for_ranking = [5,4,3,2,1] # Value of cards if it's a wheel for tie-breaking
        elif is_straight:
            straight_values_for_ranking = values[:] # Use original values for other straights


        value_counts = Counter(values)
        counts = sorted(value_counts.values(), reverse=True)
        # Primary (rank value) and kickers used for tie-breaking
        # Example: Pair of Aces (14), Kicker K (13), Q (12), J (11)
        # Value: 14 * 100^3 + 13 * 100^2 + 12 * 100^1 + 11 * 100^0
        # We will return a list of values [primary_rank_value, kicker1, kicker2, ...]

        # Royal Flush (Ace high straight flush)
        if is_straight and is_flush and values[0] == 14 and values[4] == 10 : # Ten, J, Q, K, A of same suit
            return HandRank.ROYAL_FLUSH, values[0], straight_values_for_ranking # Values are [14,13,12,11,10]

        # Straight Flush
        if is_straight and is_flush:
            return HandRank.STRAIGHT_FLUSH, straight_values_for_ranking[0], straight_values_for_ranking

        # Four of a Kind
        if counts == [4, 1]:
            four_val = [v for v, c in value_counts.items() if c == 4][0]
            kicker_val = [v for v, c in value_counts.items() if c == 1][0]
            return HandRank.FOUR_OF_A_KIND, four_val * 15 + kicker_val, [four_val, kicker_val] # Value: 4kind_val, kicker_val

        # Full House
        if counts == [3, 2]:
            three_val = [v for v, c in value_counts.items() if c == 3][0]
            pair_val = [v for v, c in value_counts.items() if c == 2][0]
            return HandRank.FULL_HOUSE, three_val * 15 + pair_val, [three_val, pair_val]

        # Flush (non-straight)
        if is_flush:
            # Value is based on high card, then next high, etc.
            flush_value = 0
            for i, v in enumerate(values): flush_value += v * (15**(4-i))
            return HandRank.FLUSH, flush_value, values

        # Straight (non-flush)
        if is_straight:
            return HandRank.STRAIGHT, straight_values_for_ranking[0], straight_values_for_ranking # Highest card of straight

        # Three of a Kind
        if counts == [3, 1, 1]:
            three_val = [v for v, c in value_counts.items() if c == 3][0]
            kickers = sorted([v for v, c in value_counts.items() if c == 1], reverse=True)
            val_composite = three_val * (15**2) + kickers[0] * 15 + kickers[1]
            return HandRank.THREE_OF_A_KIND, val_composite, [three_val] + kickers

        # Two Pair
        if counts == [2, 2, 1]:
            pairs_vals = sorted([v for v, c in value_counts.items() if c == 2], reverse=True)
            kicker_val = [v for v, c in value_counts.items() if c == 1][0]
            val_composite = pairs_vals[0] * (15**2) + pairs_vals[1] * 15 + kicker_val
            return HandRank.TWO_PAIR, val_composite, pairs_vals + [kicker_val]

        # One Pair
        if counts == [2, 1, 1, 1]:
            pair_val = [v for v, c in value_counts.items() if c == 2][0]
            kickers = sorted([v for v, c in value_counts.items() if c == 1], reverse=True)
            val_composite = pair_val * (15**3) + kickers[0] * (15**2) + kickers[1] * 15 + kickers[2]
            return HandRank.PAIR, val_composite, [pair_val] + kickers
        
        # High Card
        hc_value = 0
        for i, v in enumerate(values): hc_value += v * (15**(4-i))
        return HandRank.HIGH_CARD, hc_value, values

    def get_hand_description(self, rank: HandRank, best_card_values: List[int]) -> str:
        # best_card_values is the list [primary, kicker1, kicker2,...] from evaluate_5_card_hand
        card_names = {14: 'Ace', 13: 'King', 12: 'Queen', 11: 'Jack', 10: 'Ten', 9:'Nine', 8:'Eight', 7:'Seven', 6:'Six', 5:'Five', 4:'Four', 3:'Three', 2:'Two', 1:'Ace (low)'}
        
        def name(value): return card_names.get(value, str(value))

        if not best_card_values: return rank.name.replace('_', ' ') # Fallback

        if rank == HandRank.ROYAL_FLUSH: return "Royal Flush"
        if rank == HandRank.STRAIGHT_FLUSH: return f"Straight Flush, {name(best_card_values[0])} high"
        if rank == HandRank.FOUR_OF_A_KIND: return f"Four of a Kind, {name(best_card_values[0])}s"
        if rank == HandRank.FULL_HOUSE: return f"Full House, {name(best_card_values[0])}s full of {name(best_card_values[1])}s"
        if rank == HandRank.FLUSH: return f"Flush, {name(best_card_values[0])} high"
        if rank == HandRank.STRAIGHT: return f"Straight, {name(best_card_values[0])} high"
        if rank == HandRank.THREE_OF_A_KIND: return f"Three of a Kind, {name(best_card_values[0])}s"
        if rank == HandRank.TWO_PAIR: return f"Two Pair, {name(best_card_values[0])}s and {name(best_card_values[1])}s"
        if rank == HandRank.PAIR: return f"Pair of {name(best_card_values[0])}s"
        return f"High Card {name(best_card_values[0])}"

    def distribute_winnings(self, room: Room, winners_evals: Dict[str, HandEvaluation]):
        # This is a simplified distribution. Proper side pot handling is complex.
        # For now, we'll assume a single pot (room.pot) and distribute it.
        # TODO: Implement full side pot distribution.

        if not winners_evals: # No evaluations, likely everyone folded but one
            remaining_player_ids = [p.id for p in room.get_players_in_hand()]
            if len(remaining_player_ids) == 1:
                winner_id = remaining_player_ids[0]
                room.players[winner_id].money += room.pot
                room.players[winner_id].stats.hands_won += 1
                room.players[winner_id].stats.total_winnings += room.pot
                if room.pot > room.players[winner_id].stats.biggest_pot:
                    room.players[winner_id].stats.biggest_pot = room.pot
                logger.info(f"Player {room.players[winner_id].name} wins pot of ${room.pot} by default.")
                self.global_stats['biggest_pot'] = max(self.global_stats['biggest_pot'], room.pot)
                room.pot = 0
            else: # Error or no one left
                 logger.warning(f"No winners evaluated and not a single player remaining in hand for room {room.code}. Pot: ${room.pot}")

            return

        # Find the best hand among all evaluations
        best_rank_val = HandRank.HIGH_CARD
        best_numeric_val = 0
        for eval_data in winners_evals.values():
            if eval_data.rank > best_rank_val:
                best_rank_val = eval_data.rank
                best_numeric_val = eval_data.value
            elif eval_data.rank == best_rank_val and eval_data.value > best_numeric_val:
                best_numeric_val = eval_data.value
        
        # Collect all players who have this best hand
        actual_winners_ids = [pid for pid, eval_data in winners_evals.items() 
                              if eval_data.rank == best_rank_val and eval_data.value == best_numeric_val]

        if not actual_winners_ids:
            logger.error(f"No winners found after evaluation in room {room.code}. This should not happen.")
            return

        pot_to_distribute = room.pot # Simplified: using main pot only for now
        if pot_to_distribute <=0 and not room.side_pots: # No money to distribute
            logger.info(f"No pot to distribute in room {room.code}.")
            return

        winnings_per_winner = pot_to_distribute // len(actual_winners_ids)
        remainder = pot_to_distribute % len(actual_winners_ids)
        
        winner_names_log = []
        for i, winner_id in enumerate(actual_winners_ids):
            player = room.players[winner_id]
            amount_won = winnings_per_winner + (1 if i < remainder else 0)
            player.money += amount_won
            player.stats.hands_won += 1
            player.stats.total_winnings += amount_won
            if amount_won > player.stats.biggest_pot:
                player.stats.biggest_pot = amount_won
            self.global_stats['biggest_pot'] = max(self.global_stats['biggest_pot'], amount_won)
            winner_names_log.append(f"{player.name} (won ${amount_won})")
        
        logger.info(f"Pot of ${pot_to_distribute} distributed to: {', '.join(winner_names_log)} in room {room.code}.")
        room.pot = 0 # Main pot is now distributed


    def save_hand_history(self, room: Room):
        # ... (implementation as before, might need to add actual winner later)
        pass

    def update_tournament(self, room: Room):
        if room.settings.game_mode != GameMode.TOURNAMENT:
            return
        
        # Eliminate players with no money
        for player in list(room.players.values()): # Iterate over copy for safe removal/modification
            if player.money <= 0 and player.status != PlayerStatus.ELIMINATED:
                player.status = PlayerStatus.ELIMINATED
                # Assign rank - lower rank is better. Higher number means eliminated earlier.
                # This ranking is basic; proper tournament ranking considers tie-breakers.
                player.tournament_rank = len([p for p in room.players.values() if p.status == PlayerStatus.ELIMINATED])
                logger.info(f"Player {player.name} eliminated from tournament in room {room.code}. Rank: {player.tournament_rank}")


        if datetime.now() >= room.tournament_next_level:
            room.tournament_level += 1
            new_sb = math.ceil(room.settings.small_blind * 1.5 / 5) * 5 # Increase and round to nearest 5
            new_bb = math.ceil(room.settings.big_blind * 1.5 / 5) * 5
            room.settings.small_blind = new_sb
            room.settings.big_blind = new_bb
            room.tournament_next_level = datetime.now() + timedelta(seconds=TOURNAMENT_BLIND_INCREASE_INTERVAL)
            logger.info(f"Room {room.code} tournament level up: {room.tournament_level}. Blinds: {new_sb}/{new_bb}")
            
            if room.tournament_level % 5 == 0: # Break every 5 levels
                room.phase = GamePhase.TOURNAMENT_BREAK
                room.paused = True
                room.pause_reason = f"Tournament Break - Level {room.tournament_level} (5 min)"
                logger.info(f"Room {room.code} on tournament break for 5 minutes.")
                asyncio.create_task(self.resume_tournament_after_break(room.code))

    async def resume_tournament_after_break(self, room_code: str):
        await asyncio.sleep(300)  # 5 minute break
        if room_code in self.rooms:
            room = self.rooms[room_code]
            if room.paused and room.phase == GamePhase.TOURNAMENT_BREAK : # Check if still paused for this reason
                room.paused = False
                room.pause_reason = ""
                room.phase = GamePhase.WAITING # Ready for next hand
                logger.info(f"Tournament break ended in room {room.code}.")
                # Potentially auto-start if conditions met
                players_for_next_hand = [p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED]
                if len(players_for_next_hand) >= room.settings.min_players:
                    asyncio.create_task(self.auto_start_next_hand(room_code, delay=2))


    def end_tournament(self, room: Room, winner: Optional[Player]):
        logger.info(f"Tournament ended in room {room.code}.")
        if winner:
            winner.tournament_rank = 1 # Ensure winner is rank 1
            logger.info(f"Winner: {winner.name}")
        
        # Finalize ranks for any remaining players based on chip count
        # This part needs more robust ranking logic for ties.
        # For now, eliminated players already got their rank.
        # Players not eliminated (if any besides winner) can be ranked by money.
        
        # Room will go to GAME_OVER phase, then client UI can show final standings.


    async def auto_start_next_hand(self, room_code: str, delay: int = 5):
        await asyncio.sleep(delay)
        if room_code in self.rooms:
            room = self.rooms[room_code]
            if room.phase == GamePhase.WAITING and not room.paused:
                # Ensure min players are still there and not all sitting out (excluding AI)
                ready_players = [p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED and (p.is_ai or p.status != PlayerStatus.SITTING_OUT)]
                if len(ready_players) >= room.settings.min_players:
                    logger.info(f"Auto-starting next hand in room {room_code}.")
                    self.start_game(room_code)
                else:
                    logger.info(f"Auto-start next hand in room {room_code} aborted: not enough ready players ({len(ready_players)}/{room.settings.min_players}).")

    def add_chat_message(self, room_code: str, player_id: str, message: str):
        if room_code not in self.rooms: return
        room = self.rooms[room_code]
        
        player_name = "Spectator"
        player_color = "#CCCCCC" # Default for spectators
        
        if player_id in room.players:
            player = room.players[player_id]
            player_name = player.name
            player_color = player.color
        elif player_id == "SYSTEM": # For system messages
            player_name = "SYSTEM"
            player_color = "#FFD700" # Gold for system
        
        # Sanitize message? For now, assume it's fine.
        
        chat_msg = {
            "id": str(uuid.uuid4()),
            "player_id": player_id,
            "player_name": player_name,
            "player_color": player_color,
            "message": message, # Should be sanitized/validated for length on client and here
            "timestamp": time.time(),
            "formatted_time": datetime.now().strftime("%H:%M:%S")
        }
        
        room.chat_messages.append(chat_msg)
        if len(room.chat_messages) > MAX_CHAT_MESSAGES:
            room.chat_messages = room.chat_messages[-MAX_CHAT_MESSAGES:]
        
        room.update_activity()

    def check_rate_limit(self, player_id: str, limit_type: str = "message") -> bool:
        now = time.time()
        
        if limit_type == "message":
            rate_limit_dict = self.rate_limits
            max_per_second = RATE_LIMIT_MESSAGES_PER_SECOND
        elif limit_type == "action":
            rate_limit_dict = self.action_rate_limits
            max_per_second = RATE_LIMIT_ACTIONS_PER_SECOND
        else:
            return True # Unknown limit type, allow

        # Clean up old timestamps
        rate_limit_dict[player_id] = [t for t in rate_limit_dict[player_id] if now - t < 1.0]
        
        if len(rate_limit_dict[player_id]) >= max_per_second:
            logger.warning(f"Rate limit exceeded for player {player_id}, type {limit_type}.")
            return False
        
        rate_limit_dict[player_id].append(now)
        return True

    def cleanup_inactive_rooms(self):
        current_time = datetime.now()
        rooms_to_delete = []
        
        for room_code, room in list(self.rooms.items()): # Iterate over copy
            # Delete room if inactive for too long OR if it's an empty public room for a while
            is_empty_public_room = room.room_type == RoomType.PUBLIC and not room.players and not room.spectators
            long_inactivity = current_time - room.last_activity > timedelta(seconds=SESSION_TIMEOUT)
            short_inactivity_empty_public = is_empty_public_room and (current_time - room.created_at > timedelta(minutes=15))


            if long_inactivity or short_inactivity_empty_public :
                rooms_to_delete.append(room_code)
        
        for room_code in rooms_to_delete:
            logger.info(f"Cleaning up inactive/empty room {room_code}")
            if room_code in self.rooms: # Check again, might have been deleted by other means
                # Notify any connected players/spectators if possible (they shouldn't be if inactive)
                room_to_del = self.rooms[room_code]
                all_user_ids_in_room = list(room_to_del.players.keys()) + list(room_to_del.spectators)
                for user_id in all_user_ids_in_room:
                    if user_id in self.connections:
                         # This part needs an async task if sending websocket message here
                         # For simplicity, just log and remove.
                         logger.info(f"Removing player {user_id} from player_rooms due to room cleanup.")
                         if user_id in self.player_rooms: del self.player_rooms[user_id]
                del self.rooms[room_code]

    def get_game_state(self, room_code: str, player_id: str) -> dict:
        if room_code not in self.rooms:
            return {"error": "Room not found"} # Return error structure
        
        room = self.rooms[room_code]
        is_player_in_room = player_id in room.players
        is_spectator = player_id in room.spectators
        
        seated_players = room.get_seated_players() # For consistent indexing if needed
        current_player_obj = None
        if seated_players and 0 <= room.current_player_index < len(seated_players):
            current_player_id_at_table = seated_players[room.current_player_index].id
            current_player_obj = room.players.get(current_player_id_at_table)

        players_data = {}
        for pid, p_obj in room.players.items():
            is_this_player_current_actor = current_player_obj and current_player_obj.id == pid

            player_data = {
                "id": p_obj.id, "name": p_obj.name, "money": p_obj.money,
                "current_bet": p_obj.current_bet, "total_bet_this_hand": p_obj.total_bet_this_hand,
                "status": p_obj.status.value, "position": p_obj.position,
                "last_action": p_obj.last_action.value if p_obj.last_action else None,
                "avatar": p_obj.avatar, "color": p_obj.color,
                "is_dealer": p_obj.is_dealer, "is_small_blind": p_obj.is_small_blind, "is_big_blind": p_obj.is_big_blind,
                "time_bank": p_obj.time_bank,
                "is_current_player": is_this_player_current_actor,
                "tournament_rank": p_obj.tournament_rank,
                "is_ai": p_obj.is_ai, # Added for AI
                "stats": asdict(p_obj.stats) # Simpler conversion
            }
            
            # Card visibility logic
            show_cards = False
            if pid == player_id and not p_obj.is_ai: # Player sees their own cards
                show_cards = True
            elif room.phase == GamePhase.SHOWDOWN: # Everyone sees cards at showdown
                # Except for folded players unless they were all-in and part of showdown
                if p_obj.status != PlayerStatus.FOLDED or p_obj.is_all_in():
                    show_cards = True
            # Spectators see cards at showdown (same as players)
            # AI cards are generally hidden unless showdown (for fairness if playing against AI)

            if show_cards and p_obj.cards:
                player_data["cards"] = [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in p_obj.cards]
            elif p_obj.cards: # Player has cards but they are hidden
                player_data["cards"] = [{"suit": "back", "rank": "back", "id": f"back_{i}_{pid}"} for i in range(len(p_obj.cards))]
            else: # No cards
                player_data["cards"] = []
            
            players_data[pid] = player_data
        
        # Time left calculation
        time_left_for_action = 0
        if current_player_obj and current_player_obj.status == PlayerStatus.ACTIVE and \
           room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER] and \
           not room.paused :
            time_left_for_action = max(0, room.settings.auto_fold_timeout - (time.time() - room.last_action_time))
            if current_player_obj.is_ai: # AI doesn't use UI timer, but good to have state
                time_left_for_action = room.settings.auto_fold_timeout # Reset for AI display

        can_this_player_act = (is_player_in_room and 
                               current_player_obj and 
                               current_player_obj.id == player_id and 
                               not room.players[player_id].is_ai and # Humans act via UI
                               room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER] and 
                               not room.paused and
                               room.players[player_id].status == PlayerStatus.ACTIVE)


        game_state = {
            "room_code": room.code, "room_name": room.name, "phase": room.phase.value,
            "pot": room.pot, "current_bet": room.current_bet, "min_raise": room.min_raise,
            # current_player_index still refers to seated_players for table display consistency
            "current_player_id_acting": current_player_obj.id if current_player_obj else None,
            "dealer_index": room.dealer_index, # Index in seated_players
            "players": players_data,
            "community_cards": [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in room.community_cards],
            "chat_messages": room.chat_messages[-30:],  # Last 30 messages
            "is_player": is_player_in_room, "is_spectator": is_spectator,
            "spectator_count": len(room.spectators), "hand_number": room.hand_number,
            "settings": {
                "small_blind": room.settings.small_blind, "big_blind": room.settings.big_blind,
                "ante": room.settings.ante, "max_players": room.settings.max_players,
                "game_mode": room.settings.game_mode.value, "auto_fold_timeout": room.settings.auto_fold_timeout
            },
            "tournament_info": {
                "level": room.tournament_level,
                "next_level_time": room.tournament_next_level.isoformat() if room.settings.game_mode == GameMode.TOURNAMENT else None
            } if room.settings.game_mode == GameMode.TOURNAMENT else None,
            "side_pots": [{"amount": sp.amount, "eligible_players_count": len(sp.eligible_players)} for sp in room.side_pots], # Count for brevity
            "paused": room.paused, "pause_reason": room.pause_reason,
            "time_left_for_action": time_left_for_action,
            "can_act": can_this_player_act,
            "available_actions": self.get_available_actions(room, player_id) if can_this_player_act else []
        }
        return game_state

    def get_available_actions(self, room: Room, player_id: str) -> List[Dict]:
        if player_id not in room.players: return []
        player = room.players[player_id]

        if not player.can_act() or player.is_ai : return [] # AI actions are server-side
        
        actions = []
        
        # Fold
        actions.append({"action": PlayerAction.FOLD.value, "label": "Fold"})
        
        # Check / Call
        bet_to_match = room.current_bet
        player_current_round_bet = player.current_bet

        if player_current_round_bet == bet_to_match : # Can check
             # Also includes BB pre-flop if no raise
            actions.append({"action": PlayerAction.CHECK.value, "label": "Check"})
        else: # Must call or raise or fold
            amount_to_call = bet_to_match - player_current_round_bet
            if amount_to_call > 0:
                actual_call_amount = min(amount_to_call, player.money)
                actions.append({
                    "action": PlayerAction.CALL.value, 
                    "label": f"Call ${actual_call_amount}" + (" (All-in)" if actual_call_amount == player.money else ""),
                    "amount": actual_call_amount
                })

        # Raise (can only raise if player has more money than needed to call the current bet)
        money_after_call = player.money - max(0, bet_to_match - player_current_round_bet)
        if money_after_call > 0 :
            # Min amount to raise BY is room.min_raise
            # Max amount to raise BY is whatever money they have left after calling
            min_raise_by = room.min_raise
            max_raise_by = money_after_call # This is the max they can add ON TOP of a call

            if max_raise_by >= min_raise_by : # Can make at least a min raise
                actions.append({
                    "action": PlayerAction.RAISE.value, 
                    "label": "Raise", 
                    "min_amount": min_raise_by, # This is raise BY amount
                    "max_amount": max_raise_by  # This is raise BY amount
                })
        
        # All-in (always an option if player has money, unless already covered by Call All-in)
        if player.money > 0:
            # Avoid duplicate "All-in" if Call action already results in All-in for the same amount
            is_call_all_in = any(a['action'] == PlayerAction.CALL.value and a['amount'] == player.money for a in actions)
            if not is_call_all_in:
                 actions.append({
                    "action": PlayerAction.ALL_IN.value, 
                    "label": f"All-In ${player.money}", 
                    "amount": player.money
                })
        
        return actions

    def get_room_list(self) -> List[Dict]:
        rooms_data = []
        for room_code, room in self.rooms.items():
            if room.room_type == RoomType.PUBLIC: # Only show public rooms
                human_players = len([p for p in room.players.values() if not p.is_ai])
                ai_players = len([p for p in room.players.values() if p.is_ai])
                
                rooms_data.append({
                    "code": room_code, "name": room.name,
                    "players": f"{human_players}H + {ai_players}AI", # Distinguish human/AI
                    "max_players": room.settings.max_players,
                    "spectators": len(room.spectators), "phase": room.phase.value,
                    "game_mode": room.settings.game_mode.value,
                    "small_blind": room.settings.small_blind, "big_blind": room.settings.big_blind,
                    "created_at": room.created_at.isoformat(),
                    "has_password": bool(room.settings.password)
                })
        return sorted(rooms_data, key=lambda r: r['created_at'], reverse=True) # Show newest first


# Global game instance
game = AdvancedPokerGame()

# WebSocket message models
class WSMessage(BaseModel):
    action: str
    payload: dict = Field(default_factory=dict)

class CreateRoomRequest(BaseModel): # For backend validation if used in HTTP endpoint
    player_name: str = "Anonymous"
    room_name: str = ""
    game_mode: str = GameMode.CASH_GAME.value
    small_blind: int = SMALL_BLIND
    big_blind: int = BIG_BLIND
    max_players: int = MAX_PLAYERS_PER_ROOM
    buy_in: int = 0
    password: Optional[str] = None
    num_ai_players: int = Field(default=0, ge=0, le=MAX_AI_PLAYERS)


# FastAPI app with lifespan
@asynccontextmanager
async def lifespan(app: FastAPI):
    logger.info("Starting advanced poker game server...")
    game_task = asyncio.create_task(game_loop())
    cleanup_task = asyncio.create_task(cleanup_loop())
    yield
    logger.info("Shutting down poker game server...")
    game.running = False
    game_task.cancel()
    cleanup_task.cancel()
    try:
        await game_task
        await cleanup_task
    except asyncio.CancelledError:
        logger.info("Background tasks cancelled.")

app = FastAPI(
    title="Advanced 3D Multiplayer Poker",
    description="Professional casino-quality poker game with 3D graphics",
    version="2.0.1", # Incremented version
    lifespan=lifespan
)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"], allow_credentials=True, allow_methods=["*"], allow_headers=["*"],
)

async def game_loop():
    while game.running:
        try:
            current_time = time.time()
            
            for room_code, room in list(game.rooms.items()): # Iterate over copy
                if room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER] and not room.paused:
                    seated_players = room.get_seated_players()
                    if seated_players and 0 <= room.current_player_index < len(seated_players):
                        current_player_at_table = seated_players[room.current_player_index]
                        current_player_obj = room.players.get(current_player_at_table.id)

                        if current_player_obj and not current_player_obj.is_ai and current_player_obj.status == PlayerStatus.ACTIVE:
                            if current_time - room.last_action_time > room.settings.auto_fold_timeout:
                                logger.info(f"Auto-folding player {current_player_obj.name} in room {room_code} due to timeout.")
                                game.player_action(room_code, current_player_obj.id, PlayerAction.FOLD)
                        # AI turn logic is now handled by check_for_ai_turn called after actions/phase changes.
            
            # Broadcast game state
            for room_code, room in list(game.rooms.items()): # Iterate over copy
                connected_user_ids_in_room = set()
                for pid, p in room.players.items():
                    if p.connection_id and pid in game.connections: # Human players
                        connected_user_ids_in_room.add(pid)
                for spec_id in room.spectators:
                    if spec_id in game.connections:
                        connected_user_ids_in_room.add(spec_id)

                for user_id in list(connected_user_ids_in_room): # Iterate over copy
                    ws_conn = game.connections.get(user_id)
                    if ws_conn:
                        try:
                            game_state_for_user = game.get_game_state(room_code, user_id)
                            await ws_conn.send_json({"type": "game_state", "data": game_state_for_user})
                        except WebSocketDisconnect:
                            logger.warning(f"WebSocketDisconnect while broadcasting to {user_id} in room {room_code}. Cleaning up.")
                            game.leave_room(user_id) # Handles removing from connections too via finally block in ws_endpoint
                        except Exception as e:
                            logger.error(f"Error broadcasting game state to {user_id}: {e}")
                            # Potentially remove broken connection here too, or let ws_endpoint handle it
                            if user_id in game.connections: del game.connections[user_id]
                            game.leave_room(user_id)

            await asyncio.sleep(1.0 / GAME_UPDATE_RATE)
        except asyncio.CancelledError:
            logger.info("Game loop cancelled.")
            break
        except Exception as e:
            logger.exception(f"Critical error in game loop: {e}") # Use logger.exception for stack trace
            await asyncio.sleep(1.0) # Prevent rapid error loops

async def cleanup_loop():
    while game.running:
        try:
            await asyncio.sleep(300)  # Run every 5 minutes
            game.cleanup_inactive_rooms()
            logger.info("Ran cleanup task for inactive rooms.")
        except asyncio.CancelledError:
            logger.info("Cleanup loop cancelled.")
            break
        except Exception as e:
            logger.exception(f"Error in cleanup loop: {e}")


@app.get("/", response_class=HTMLResponse)
async def get_poker_game_html(): # Renamed to avoid conflict if HTML is served differently
    return HTMLResponse(content=ADVANCED_HTML_TEMPLATE)

@app.get("/api/rooms")
async def http_get_rooms():
    return {"rooms": game.get_room_list()}

@app.get("/api/stats")
async def http_get_stats():
    return {
        "global_stats": game.global_stats,
        "active_rooms": len(game.rooms),
        "connected_players": len([conn_id for conn_id, ws in game.connections.items() if game.player_rooms.get(conn_id)])
    }

@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    player_id = str(uuid.uuid4()) # Unique ID for this connection session
    await websocket.accept()
    game.connections[player_id] = websocket
    logger.info(f"Player {player_id} connected via WebSocket.")
    
    try:
        await websocket.send_json({
            "type": "connected",
            "data": {
                "player_id": player_id, # This ID is for the WebSocket connection itself
                "server_info": {"version": "2.0.1"}
            }
        })
        
        while True:
            data = await websocket.receive_text()
            if not game.check_rate_limit(player_id, "message"): # General message rate limit
                await websocket.send_json({"type": "error", "message": "Message rate limit exceeded. Slow down."})
                continue
            
            try:
                message = WSMessage.model_validate_json(data)
                await handle_websocket_message(websocket, player_id, message)
            except ValidationError as e:
                await websocket.send_json({"type": "error", "message": f"Invalid message: {e}"})
            # Catch other exceptions per message to keep connection alive if possible
            except Exception as e:
                logger.exception(f"Error processing WebSocket message from {player_id}: {e}")
                await websocket.send_json({"type": "error", "message": "Server error processing your request."})
                
    except WebSocketDisconnect:
        logger.info(f"Player {player_id} WebSocket disconnected.")
    except Exception as e:
        logger.exception(f"Unexpected error in WebSocket handler for {player_id}: {e}")
    finally:
        logger.info(f"Cleaning up for player {player_id}.")
        if player_id in game.connections:
            del game.connections[player_id]
        # leave_room also removes from player_rooms if joined
        game.leave_room(player_id) 
        logger.info(f"Player {player_id} fully cleaned up.")


async def handle_websocket_message(websocket: WebSocket, player_id: str, message: WSMessage):
    action = message.action
    payload = message.payload
    
    # Most actions require player to be in a room, except create/join/spectate/list
    current_room_code = game.player_rooms.get(player_id)

    try:
        if action == "create_room":
            player_name = payload.get("player_name", f"Player_{player_id[:6]}")
            num_ai = int(payload.get("num_ai_players", 0))
            num_ai = max(0, min(num_ai, MAX_AI_PLAYERS)) # Sanitize

            room_settings = GameSettings(
                small_blind=int(payload.get("small_blind", SMALL_BLIND)),
                big_blind=int(payload.get("big_blind", BIG_BLIND)),
                max_players=min(int(payload.get("max_players", MAX_PLAYERS_PER_ROOM)), MAX_PLAYERS_PER_ROOM),
                game_mode=GameMode(payload.get("game_mode", "cash_game")),
                buy_in=int(payload.get("buy_in", 0)),
                password=payload.get("password") if payload.get("password") else None
            )
            
            # Ensure max_players accommodates owner + AI
            if 1 + num_ai > room_settings.max_players:
                await websocket.send_json({"type": "error", "message": f"Max players ({room_settings.max_players}) too low for you + {num_ai} AI."})
                return

            new_room_code = game.create_room(player_id, room_settings, payload.get("room_name", ""), num_ai_players=num_ai)
            
            if game.join_room(new_room_code, player_id, player_name): # Owner auto-joins
                await websocket.send_json({
                    "type": "room_created", # Client uses this to know it also joined
                    "data": {"room_code": new_room_code, "room_name": game.rooms[new_room_code].name}
                })
            else: # Should not happen if create_room succeeded and join logic is sound
                await websocket.send_json({"type": "error", "message": "Failed to join the room after creation."})
        
        elif action == "join_room":
            room_code_to_join = payload.get("room_code", "").upper()
            player_name_to_join = payload.get("player_name", f"Player_{player_id[:6]}")
            password_to_join = payload.get("password", "")
            
            if game.join_room(room_code_to_join, player_id, player_name_to_join, password_to_join):
                await websocket.send_json({"type": "room_joined", "data": {"room_code": room_code_to_join}})
            else:
                await websocket.send_json({"type": "error", "message": "Failed to join room. Invalid code, password, or room full."})
        
        elif action == "leave_room":
            if current_room_code:
                game.leave_room(player_id) # This will also clear player_id from game.player_rooms
                await websocket.send_json({"type": "room_left", "data": {"room_code": current_room_code}})
            else:
                await websocket.send_json({"type": "error", "message": "You are not in a room."})

        elif action == "spectate":
            # ... (implementation as before) ...
            pass
        
        elif action == "start_game":
            if current_room_code and game.rooms[current_room_code].owner_id == player_id:
                if game.start_game(current_room_code):
                    # Game state will be broadcast, no specific message needed here unless for confirmation
                    # await websocket.send_json({"type": "game_started_confirmation"}) # Optional
                    pass
                else:
                    await websocket.send_json({"type": "error", "message": "Cannot start game (e.g., not enough players)."})
            elif not current_room_code:
                 await websocket.send_json({"type": "error", "message": "Not in a room."})
            else:
                 await websocket.send_json({"type": "error", "message": "Only room owner can start game."})

        elif action == "player_action":
            if not current_room_code:
                await websocket.send_json({"type": "error", "message": "Not in a room."})
                return
            if not game.check_rate_limit(player_id, "action"): # Stricter rate limit for game actions
                await websocket.send_json({"type": "error", "message": "Action rate limit exceeded. Please wait."})
                return
                
            action_type_str = payload.get("action_type")
            action_amount = int(payload.get("amount", 0))
            try:
                poker_action_enum = PlayerAction(action_type_str)
                if game.player_action(current_room_code, player_id, poker_action_enum, action_amount):
                    # Action accepted, game state will update. Optionally send confirmation.
                    # await websocket.send_json({"type": "action_feedback", "status": "accepted"})
                    pass
                else:
                    # Get more specific error? For now, generic.
                    game_state_now = game.get_game_state(current_room_code, player_id)
                    available_now = game_state_now.get("available_actions", [])
                    await websocket.send_json({"type": "error", 
                                               "message": "Invalid action or not your turn.",
                                               "debug_available_actions": available_now})
            except ValueError: # Invalid PlayerAction string
                await websocket.send_json({"type": "error", "message": "Unknown action type."})
        
        elif action == "send_chat":
            if not current_room_code:
                await websocket.send_json({"type": "error", "message": "Not in a room to chat."})
                return
            message_text = payload.get("message", "")
            if 0 < len(message_text.strip()) <= 200: # Validate length and non-empty
                game.add_chat_message(current_room_code, player_id, message_text.strip())
                # Chat messages are sent via game_state, no specific confirmation needed
            elif len(message_text.strip()) > 200:
                await websocket.send_json({"type": "error", "message": "Chat message too long (max 200 chars)."})
            # else: empty message, ignore silently
        
        elif action == "get_room_list":
            await websocket.send_json({"type": "room_list", "data": {"rooms": game.get_room_list()}})
        
        # ... (other actions: get_hand_history, pause_game, kick_player) ...
        # Ensure they check current_room_code and ownership where necessary.

        else:
            await websocket.send_json({"type": "error", "message": f"Unknown action: {action}"})
            
    except Exception as e: # Catch-all for safety within handler
        logger.exception(f"Error handling WebSocket action '{action}' for player {player_id}: {e}")
        await websocket.send_json({"type": "error", "message": f"Server error processing action '{action}'."})

# Advanced HTML Template (JavaScript changes are integrated within this template)
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

        .menu-panel { top: 50%; left: 50%; transform: translate(-50%, -50%); text-align: center; min-width: 400px; max-width: 90vw; max-height: 90vh; overflow-y: auto; }
        .menu-title { font-family: 'Orbitron', monospace; font-size: 3rem; font-weight: 900; color: var(--primary-gold); text-shadow: 0 0 20px rgba(255, 215, 0, 0.8); margin-bottom: 30px; animation: glow 2s ease-in-out infinite alternate; }
        @keyframes glow { from { text-shadow: 0 0 20px rgba(255, 215, 0, 0.8); } to { text-shadow: 0 0 30px rgba(255, 215, 0, 1), 0 0 40px rgba(255, 215, 0, 0.8); } }
        .menu-section { margin-bottom: 25px; padding: 20px; background: rgba(255, 255, 255, 0.05); border-radius: 10px; border: 1px solid rgba(255, 215, 0, 0.3); }
        .menu-section h3 { color: var(--secondary-gold); margin-bottom: 15px; font-size: 1.2rem; }

        .game-hud { 
            top: 20px; left: 20px; max-width: 350px; 
            max-height: calc(100vh - 40px - 150px); /* Reserve space for bottom actions + padding */
            overflow-y: auto; 
        }
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
        .action-button.fold { background: linear-gradient(135deg, var(--casino-red), #ff6b6b); color: white; }
        .action-button.call { background: linear-gradient(135deg, #28a745, #20c997); color: white; }
        .action-button.raise { background: linear-gradient(135deg, var(--casino-blue), #6c5ce7); color: white;}
        .action-button.all-in { background: linear-gradient(135deg, #ff4757, #ff3742); animation: allInPulse 1s infinite; color: white; }
        @keyframes allInPulse { 0%, 100% { box-shadow: 0 5px 15px rgba(255, 71, 87, 0.3); } 50% { box-shadow: 0 5px 25px rgba(255, 71, 87, 0.6); } }

        .raise-controls { display: flex; align-items: center; gap: 10px; background: rgba(255, 255, 255, 0.1); padding: 10px; border-radius: 8px; }
        .raise-slider { flex: 1; -webkit-appearance: none; appearance: none; height: 8px; background: rgba(255, 255, 255, 0.3); border-radius: 4px; outline: none; }
        .raise-slider::-webkit-slider-thumb { -webkit-appearance: none; appearance: none; width: 20px; height: 20px; background: var(--primary-gold); border-radius: 50%; cursor: pointer; }

        .chat-panel { 
            top: 20px; right: 20px; width: 320px; 
            /* height: 400px;  Replaced with max-height */
            max-height: calc(100vh - 40px - 150px); /* Reserve space for bottom actions + padding */
            display: flex; flex-direction: column; 
        }
        .chat-header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 15px; padding-bottom: 10px; border-bottom: 2px solid var(--primary-gold); }
        .chat-title { font-family: 'Orbitron', monospace; font-weight: 700; color: var(--primary-gold); }
        .chat-toggle { background: none; border: 2px solid var(--primary-gold); color: var(--primary-gold); border-radius: 6px; padding: 5px 10px; cursor: pointer; transition: all 0.3s ease; }
        .chat-toggle:hover { background: var(--primary-gold); color: var(--text-dark); }
        #chatMessages { flex: 1; overflow-y: auto; background: rgba(255, 255, 255, 0.05); border-radius: 8px; padding: 15px; margin-bottom: 15px; border: 1px solid rgba(255, 215, 0, 0.2); min-height: 50px; /* Prevent collapse */ }
        .chat-message { margin-bottom: 10px; padding: 8px 12px; border-radius: 8px; background: rgba(255, 255, 255, 0.1); border-left: 3px solid; animation: slideInChat 0.3s ease-out; word-wrap: break-word; }
        @keyframes slideInChat { from { opacity: 0; transform: translateX(20px); } to { opacity: 1; transform: translateX(0); } }
        .chat-player-name { font-weight: 700; margin-right: 8px; }
        .chat-timestamp { font-size: 0.8rem; opacity: 0.6; float: right; }
        .chat-input-container { display: flex; gap: 10px; margin-top: auto; /* Pushes to bottom if chat-panel has flex */ }

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

        input, select { padding: 12px 15px; border: 2px solid var(--primary-gold); border-radius: 8px; background: rgba(255, 255, 255, 0.1); color: var(--text-light); font-size: 1rem; transition: all 0.3s ease; backdrop-filter: blur(10px); }
        input:focus, select:focus { outline: none; border-color: var(--secondary-gold); box-shadow: 0 0 15px rgba(255, 215, 0, 0.3); }
        input::placeholder { color: rgba(255, 255, 255, 0.6); }
        select option { background-color: var(--dark-green); color: var(--text-light); }

        ::-webkit-scrollbar { width: 8px; }
        ::-webkit-scrollbar-track { background: rgba(255, 255, 255, 0.1); border-radius: 4px; }
        ::-webkit-scrollbar-thumb { background: var(--primary-gold); border-radius: 4px; }
        ::-webkit-scrollbar-thumb:hover { background: var(--secondary-gold); }

        @media (max-width: 768px) {
            .menu-panel { min-width: 90vw; padding: 15px; font-size: 0.9rem;}
            .menu-title { font-size: 2rem; }
            .menu-section { padding: 15px; }
            .menu-section h3 { font-size: 1.1rem; }
            .action-button { padding: 12px 18px; font-size: 0.9rem; }

            .game-hud { max-width: calc(50vw - 30px); padding: 10px; font-size: 0.9rem;}
            .hud-item { padding: 6px 10px; margin-bottom: 8px; }
            .game-hud .action-button { padding: 10px 12px; font-size: 0.8rem; }


            .chat-panel { width: calc(50vw - 30px); padding: 10px; font-size: 0.9rem;}
            .chat-title { font-size: 1.1rem;}
            #chatMessages { padding: 10px; }
            .chat-message { padding: 6px 10px; }
            .chat-input-container input { padding: 10px; }
            .chat-input-container .action-button { padding: 10px 12px; font-size: 0.8rem; }


            .actions-panel { bottom: 20px; gap: 10px; }
            .player-cards { bottom: 80px; gap: 10px; }
            .player-card { min-width: 120px; padding: 10px; font-size: 0.9rem; }
            .pot-display { font-size: 1.5rem; padding: 20px; min-width: 120px; min-height: 120px; }
        }

        .hidden { display: none !important; }
        .fade-in { animation: fadeIn 0.5s ease-out; }
        .fade-out { animation: fadeOut 0.5s ease-out; }
        @keyframes fadeIn { from { opacity: 0; } to { opacity: 1; } }
        @keyframes fadeOut { from { opacity: 1; } to { opacity: 0; } }
        .slide-up { animation: slideUp 0.5s ease-out; }
        @keyframes slideUp { from { transform: translateY(20px); opacity: 0; } to { transform: translateY(0); opacity: 1; } }

        .tournament-info { position: absolute; top: 20px; left: 50%; transform: translateX(-50%); background: linear-gradient(135deg, rgba(25, 25, 112, 0.9), rgba(138, 43, 226, 0.8)); border: 2px solid var(--primary-gold); border-radius: 10px; padding: 15px 25px; text-align: center; backdrop-filter: blur(10px); }
        .tournament-level { font-family: 'Orbitron', monospace; font-size: 1.2rem; font-weight: 700; color: var(--primary-gold); margin-bottom: 5px; }
        .tournament-timer { color: var(--text-light); font-size: 0.9rem; }

        .notification { position: fixed; top: 20px; right: 20px; background: linear-gradient(135deg, rgba(40, 167, 69, 0.9), rgba(32, 201, 151, 0.9)); color: var(--text-light); padding: 15px 20px; border-radius: 8px; border-left: 4px solid var(--primary-gold); box-shadow: 0 5px 15px var(--shadow); z-index: 9999; animation: slideInNotification 0.5s ease-out; max-width: 300px; pointer-events: auto; }
        .notification.error { background: linear-gradient(135deg, rgba(220, 20, 60, 0.9), rgba(255, 107, 107, 0.9)); }
        .notification.warning { background: linear-gradient(135deg, rgba(255, 193, 7, 0.9), rgba(255, 235, 59, 0.9)); color: var(--text-dark); }
        @keyframes slideInNotification { from { transform: translateX(100%); opacity: 0; } to { transform: translateX(0); opacity: 1; } }

        .modal { position: fixed; top: 0; left: 0; width: 100%; height: 100%; background: rgba(0, 0, 0, 0.8); display: flex; justify-content: center; align-items: center; z-index: 9998; pointer-events: auto; } /* Ensure modal is interactive */
        .modal-content { background: linear-gradient(135deg, rgba(10, 42, 31, 0.95), rgba(26, 93, 58, 0.95)); border: 2px solid var(--primary-gold); border-radius: 15px; padding: 30px; max-width: 80vw; max-height: 80vh; overflow-y: auto; backdrop-filter: blur(15px); }
        .modal-header { display: flex; justify-content: space-between; align-items: center; margin-bottom: 20px; padding-bottom: 15px; border-bottom: 2px solid var(--primary-gold); }
        .modal-title { font-family: 'Orbitron', monospace; font-size: 1.5rem; font-weight: 700; color: var(--primary-gold); }
        .modal-close { background: none; border: 2px solid var(--casino-red); color: var(--casino-red); border-radius: 6px; padding: 8px 15px; cursor: pointer; font-weight: 700; transition: all 0.3s ease; }
        .modal-close:hover { background: var(--casino-red); color: var(--text-light); }
        
        #actionTimer { position: absolute; top: 25%; left: 50%; transform: translateX(-50%); background: rgba(220, 20, 60, 0.9); color: white; padding: 10px 20px; border-radius: 25px; font-family: 'Orbitron', monospace; font-weight: 700; font-size: 1.2rem; animation: timerPulse 1s infinite; }
        @keyframes timerPulse { 0%, 100% { transform: translateX(-50%) scale(1); } 50% { transform: translateX(-50%) scale(1.1); } }

    </style>
</head>
<body>
    <div id="loadingScreen">
        <div class="loading-logo">🎰 ROYAL POKER 3D</div>
        <div class.loading-spinner"></div>
        <div class="loading-text">Loading casino experience...</div>
    </div>

    <div id="gameContainer">
        <canvas id="canvas"></canvas>
        
        <div class="ui-overlay">
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
                        <div><label>Game Mode:</label><select id="gameMode" style="width: 100%;"><option value="cash_game">Cash Game</option><option value="tournament">Tournament</option><option value="sit_and_go">Sit & Go</option></select></div>
                        <div><label>Max Players:</label><input type="number" id="maxPlayers" min="2" max="10" value="8" style="width: 100%;"></div>
                        <div><label>Small Blind:</label><input type="number" id="smallBlind" min="1" value="25" step="5" style="width: 100%;"></div>
                        <div><label>Big Blind:</label><input type="number" id="bigBlind" min="2" value="50" step="5" style="width: 100%;"></div>
                        <div><label>Buy-in (0 for default):</label><input type="number" id="buyIn" min="0" value="1000" step="100" style="width: 100%;"></div>
                        <div><label>AI Players (0-7):</label><input type="number" id="numAiPlayers" min="0" max="7" value="0" style="width: 100%;"></div>
                        <div style="grid-column: span 2;"><label>Password (Optional):</label><input type="password" id="roomPassword" placeholder="Leave empty for public" style="width: 100%;"></div>
                    </div>
                    <input type="text" id="roomName" placeholder="Room Name (Optional)" style="width: 100%; margin-bottom: 15px;">
                    <button class="action-button" onclick="createCustomRoom()">🎪 Create Custom Room</button>
                </div>
                <div class="menu-section"><h3>Browse Rooms</h3><button class="action-button" onclick="showRoomList()">🏛️ Browse Public Rooms</button></div>
                <div style="margin-top: 20px; font-size: 14px; color: #ccc; text-align: center;">💰 Starting money: $1,000 | 🎯 Blinds: $25/$50<br>🏆 Tournament mode available | 👥 Up to 10 players</div>
            </div>

            <div id="roomListModal" class="modal hidden"><div class="modal-content"><div class="modal-header"><h2 class="modal-title">🏛️ Public Rooms</h2><button class="modal-close" onclick="hideRoomList()">✕</button></div><div id="roomList" style="max-height: 400px; overflow-y: auto;"><div style="text-align: center; color: #ccc; padding: 20px;">Loading rooms...</div></div><div style="margin-top: 20px; text-align: center;"><button class="action-button" onclick="refreshRoomList()">🔄 Refresh</button></div></div></div>
            
            <div id="gameHUD" class="ui-panel game-hud hidden">
                <div class="hud-item"><span class="hud-label">🏠 Room:</span><span class="hud-value" id="currentRoom">-</span></div>
                <div class="hud-item"><span class="hud-label">🎮 Phase:</span><span class="hud-value" id="phaseText">Waiting</span></div>
                <div class="hud-item"><span class="hud-label">💰 My Money:</span><span class="hud-value">$<span id="myMoneyAmount">0</span></span></div>
                <div class="hud-item"><span class="hud-label">🎯 To Call:</span><span class="hud-value">$<span id="betToMatch">0</span></span></div>
                <div class="hud-item"><span class="hud-label">🃏 Hand #:</span><span class="hud-value" id="handNumber">0</span></div>
                <div style="margin-top: 20px; display: flex; flex-direction: column; gap: 10px;">
                    <button class="action-button" onclick="startGame()" id="startGameBtn" style="width: 100%;">🚀 Start Game</button>
                    <button class="action-button" onclick="showHandHistory()" style="width: 100%;">📊 Hand History</button>
                    <button class="action-button" onclick="pauseGame()" id="pauseGameBtn" style="width: 100%;">⏸️ Pause Game</button>
                    <button class="action-button fold" onclick="leaveRoom()" style="width: 100%;">🚪 Leave Room</button>
                </div>
            </div>

            <div id="tournamentInfo" class="tournament-info hidden"><div class="tournament-level">🏆 Level <span id="tournamentLevel">1</span></div><div class="tournament-timer">Next level in: <span id="tournamentTimer">10:00</span></div><div style="margin-top: 5px; font-size: 0.8rem;">Blinds: $<span id="tournamentBlinds">25/50</span></div></div>
            <div id="potDisplay" class="pot-display hidden"><div style="font-size: 1rem; margin-bottom: 5px;">💰 POT</div><div>$<span id="potAmount">0</span></div><div id="sidePots" style="font-size: 0.8rem; margin-top: 5px; color: rgba(0,0,0,0.7);"></div></div>
            <div id="actionTimer" class="hidden">⏰ <span id="timerSeconds">30</span>s</div>
            
            <div id="actionsPanel" class="actions-panel hidden">
                <button class="action-button fold" onclick="playerAction('fold')" id="foldBtn">🚫 Fold</button>
                <button class="action-button" onclick="playerAction('check')" id="checkBtn">✅ Check</button>
                <button class="action-button call" onclick="playerAction('call')" id="callBtn">📞 Call $<span id="callAmount">0</span></button>
                <div id="raiseControlsContainer" class="raise-controls" style="display:none;"> <!-- Initially hidden -->
                    <span style="color: var(--primary-gold); font-weight: 700;">Raise By:</span>
                    <input type="range" id="raiseSlider" class="raise-slider" min="50" max="1000" value="100" oninput="updateRaiseAmountDisplay()" onchange="updateRaiseAmountDisplay()">
                    <input type="number" id="raiseAmountInput" min="50" value="100" style="width: 80px;" oninput="updateRaiseSliderFromInput()">
                    <button class="action-button raise" onclick="playerAction('raise')" id="raiseBtn">📈 Raise</button>
                </div>
                <button class="action-button all-in" onclick="playerAction('all_in')" id="allInBtn">🔥 ALL IN</button>
            </div>

            <div id="chatPanel" class="chat-panel hidden"><div class="chat-header"><h3 class="chat-title">💬 Chat</h3><button class="chat-toggle" onclick="toggleChat()" id="chatToggle">−</button></div><div id="chatMessages"></div><div class="chat-input-container"><input type="text" id="chatInput" placeholder="Type message..." style="flex: 1;" onkeypress="if(event.key==='Enter') sendChat()" maxlength="200"><button class="action-button" onclick="sendChat()">Send</button></div></div>
            <div id="playerCards" class="player-cards hidden"></div>
            <div id="handHistoryModal" class="modal hidden"><div class="modal-content"><div class="modal-header"><h2 class="modal-title">📊 Hand History</h2><button class="modal-close" onclick="hideHandHistory()">✕</button></div><div id="handHistoryContent" style="max-height: 400px; overflow-y: auto;"><div style="text-align: center; color: #ccc; padding: 20px;">No hands played yet.</div></div></div></div>
        </div>
    </div>

    <script>
        // --- Start of JavaScript ---
        let ws = null;
        let scene, camera, renderer; // Removed controls, handled manually for now
        let pokerTable, tableGroup;
        let cards = [], chips = [], playerPositions3D = [];
        let cardMaterials = {}, chipMaterials = {};
        let gameState = null;
        let myPlayerId = null; // Store the player's own ID received from server
        let isConnected = false;
        let currentRoomCode = null;
        let animationQueue = [];
        
        let cameraAnimating = false;
        let uiActive = false; // True if a major UI panel (menu, modal) is active

        let tableCards3D = [];
        let playerCardObjects3D = {}; // Stores 3D card objects for each player
        let chipStacks3D = []; // Stores 3D chip stack objects
        
        let initialConnectionNotified = false;
        let connectionLostNotified = false;
        let lastPauseReasonNotified = "";
        let chatCollapsed = false;

        // Helper to update uiActive state based on visible panels
        function updateUiActiveState() {
            const menuPanelVisible = !document.getElementById('menuPanel').classList.contains('hidden');
            const roomListModalVisible = !document.getElementById('roomListModal').classList.contains('hidden');
            const handHistoryModalVisible = !document.getElementById('handHistoryModal').classList.contains('hidden');
            
            uiActive = menuPanelVisible || roomListModalVisible || handHistoryModalVisible;
        }
        
        function initThreeJS() {
            const canvas = document.getElementById('canvas');
            scene = new THREE.Scene();
            scene.fog = new THREE.Fog(0x051a11, 15, 50);
            setupLighting();
            camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, 1000);
            camera.position.set(0, 12, 15); // Default menu view
            camera.lookAt(0, 0, 0);
            renderer = new THREE.WebGLRenderer({ canvas: canvas, antialias: true, alpha: true, powerPreference: "high-performance" });
            renderer.setSize(window.innerWidth, window.innerHeight);
            renderer.setPixelRatio(Math.min(window.devicePixelRatio, 2));
            renderer.shadowMap.enabled = true;
            renderer.shadowMap.type = THREE.PCFSoftShadowMap;
            renderer.toneMapping = THREE.ACESFilmicToneMapping;
            renderer.toneMappingExposure = 1.2;
            // renderer.outputEncoding = THREE.sRGBEncoding; // Removed, can cause issues if not handled consistently

            createCasinoEnvironment();
            createPokerTable3D(); // Renamed to avoid conflict
            createCardMaterials();
            createChipMaterials();
            addMouseCameraControls(); // Renamed
            // createParticleSystem(); // Optional, can add back if desired
            animate();
        }

        function setupLighting() { /* ... (No changes from your original) ... */ 
            const ambientLight = new THREE.AmbientLight(0x404040, 0.5); // Slightly brighter ambient
            scene.add(ambientLight);
            const mainLight = new THREE.DirectionalLight(0xffffff, 1.0); // Brighter main
            mainLight.position.set(5, 15, 5); // Adjusted position
            mainLight.castShadow = true;
            mainLight.shadow.mapSize.width = 2048; mainLight.shadow.mapSize.height = 2048;
            mainLight.shadow.camera.near = 0.5; mainLight.shadow.camera.far = 50;
            mainLight.shadow.camera.left = -15; mainLight.shadow.camera.right = 15;
            mainLight.shadow.camera.top = 15; mainLight.shadow.camera.bottom = -15;
            scene.add(mainLight);
            const tableLight1 = new THREE.SpotLight(0xffd700, 1.0, 30, Math.PI / 3, 0.3, 1); // Stronger spotlight
            tableLight1.position.set(0, 8, 0);
            tableLight1.target.position.set(0, 0, 0);
            tableLight1.castShadow = true;
            scene.add(tableLight1); scene.add(tableLight1.target);
        }
        function createCasinoEnvironment() { /* ... (No changes from your original) ... */ 
            const floorGeometry = new THREE.PlaneGeometry(100,100);
            const floorMaterial = new THREE.MeshStandardMaterial({color: 0x1a1a1a, roughness: 0.8, metalness: 0.2});
            const floor = new THREE.Mesh(floorGeometry, floorMaterial);
            floor.rotation.x = -Math.PI / 2; floor.position.y = -0.5; floor.receiveShadow = true;
            scene.add(floor);
        }

        function createPokerTable3D() {
            tableGroup = new THREE.Group();
            const tableGeometry = new THREE.CylinderGeometry(7, 7, 0.4, 64);
            const tableMaterial = new THREE.MeshStandardMaterial({ color: 0x8B4513, roughness: 0.6, metalness: 0.3 });
            pokerTable = new THREE.Mesh(tableGeometry, tableMaterial);
            pokerTable.position.y = -0.2; pokerTable.receiveShadow = true; pokerTable.castShadow = true;
            tableGroup.add(pokerTable);
            const feltGeometry = new THREE.CylinderGeometry(6.5, 6.5, 0.05, 64);
            const feltMaterial = new THREE.MeshStandardMaterial({ color: 0x0d4d2a, roughness: 0.9 });
            const tableFelt = new THREE.Mesh(feltGeometry, feltMaterial);
            tableFelt.position.y = 0.25; tableFelt.receiveShadow = true;
            tableGroup.add(tableFelt);
            scene.add(tableGroup);
            createPlayerPositions3D();
        }
        function createPlayerPositions3D() { /* ... (No changes, uses playerPositions3D) ... */
            playerPositions3D = [];
            for (let i = 0; i < 10; i++) {
                const angle = (i / 10) * Math.PI * 2;
                playerPositions3D.push({
                    angle: angle,
                    x: Math.cos(angle) * 5, z: Math.sin(angle) * 5, // Player UI card position relative to table center
                    cardX: Math.cos(angle) * 4.2, cardZ: Math.sin(angle) * 4.2, // 3D card position
                    chipX: Math.cos(angle) * 3.5, chipZ: Math.sin(angle) * 3.5  // 3D chip position
                });
            }
        }
        function createCardMaterials() { /* ... (No changes from your original) ... */ 
             cardMaterials.back = new THREE.MeshStandardMaterial({color: 0x2E4BC6, roughness: 0.7});
             ['hearts', 'diamonds', 'clubs', 'spades'].forEach(suit => {
                cardMaterials[suit] = new THREE.MeshStandardMaterial({color: 0xffffff, roughness: 0.8});
             });
        }
        function createChipMaterials() { /* ... (No changes from your original) ... */
            const defaultMaterial = {roughness: 0.5, metalness: 0.1};
            chipMaterials = {
                1: new THREE.MeshStandardMaterial({ color: 0xFFFFFF, ...defaultMaterial }),
                5: new THREE.MeshStandardMaterial({ color: 0xFF0000, ...defaultMaterial }),  
                25: new THREE.MeshStandardMaterial({ color: 0x00AA00, ...defaultMaterial }),
                100: new THREE.MeshStandardMaterial({ color: 0x000000, ...defaultMaterial }),
                500: new THREE.MeshStandardMaterial({ color: 0x800080, ...defaultMaterial }),
                1000: new THREE.MeshStandardMaterial({ color: 0xFFD700, ...defaultMaterial }),
            };
        }
        function createCard3DObject(suit, rank, position, rotationY = 0, faceUp = true) { /* ... (Similar, ensure y rotation for player pos) ... */
            const cardGroup = new THREE.Group();
            const cardGeometry = new THREE.PlaneGeometry(0.9, 1.3);
            const material = faceUp && suit !== 'back' ? cardMaterials[suit] || cardMaterials.back : cardMaterials.back;
            const cardMesh = new THREE.Mesh(cardGeometry, material);
            cardMesh.rotation.x = -Math.PI / 2; 
            // cardMesh.rotation.z = rotationZ; // If needed for tilt
            cardMesh.castShadow = true; cardMesh.receiveShadow = true;
            cardGroup.add(cardMesh);
            // TODO: Add 3D text or texture for rank/suit if faceUp
            cardGroup.position.copy(position);
            cardGroup.rotation.y = rotationY; // Orient towards table center or player
            return cardGroup;
        }
        function createChip3DStack(value, position, count = 1) { /* ... (Similar) ... */
            const chipGroup = new THREE.Group();
            for (let i = 0; i < count; i++) {
                const chipGeometry = new THREE.CylinderGeometry(0.2, 0.2, 0.05, 16); // Slimmer chips
                const chipValueKey = Object.keys(chipMaterials).reverse().find(key => value >= parseInt(key)) || 1;
                const chipMaterial = chipMaterials[chipValueKey] || chipMaterials[1];
                const chip = new THREE.Mesh(chipGeometry, chipMaterial);
                chip.position.y = i * 0.055; // Stack them up
                chip.castShadow = true; chip.receiveShadow = true;
                chipGroup.add(chip);
            }
            chipGroup.position.copy(position);
            return chipGroup;
        }

        function addMouseCameraControls() {
            let mouseDown = false; let lastMouseX = null; let lastMouseY = null;
            let targetRotationX = camera.rotation.x;
            let targetRotationY = camera.rotation.y;
            let targetZoom = camera.position.z;

            canvas.addEventListener('mousedown', (e) => { if (uiActive || cameraAnimating) return; mouseDown = true; lastMouseX = e.clientX; lastMouseY = e.clientY; });
            canvas.addEventListener('mouseup', () => { mouseDown = false; });
            canvas.addEventListener('mouseleave', () => { mouseDown = false; }); // Stop drag if mouse leaves canvas
            canvas.addEventListener('mousemove', (e) => {
                if (uiActive || cameraAnimating || !mouseDown) return;
                const deltaX = e.clientX - lastMouseX;
                // const deltaY = e.clientY - lastMouseY; // For X-axis rotation (pitch)

                // Y-axis rotation (yaw) around table center (0,0,0)
                // This requires rotating camera position around origin, not just camera.rotation.y
                const currentRadius = Math.sqrt(camera.position.x**2 + camera.position.z**2);
                let currentAngle = Math.atan2(camera.position.x, camera.position.z);
                currentAngle -= deltaX * 0.005; // Adjust sensitivity
                
                camera.position.x = currentRadius * Math.sin(currentAngle);
                camera.position.z = currentRadius * Math.cos(currentAngle);
                camera.lookAt(0, 0, 0); // Always look at table center

                lastMouseX = e.clientX; lastMouseY = e.clientY;
            });
            canvas.addEventListener('wheel', (e) => {
                if (uiActive || cameraAnimating) return;
                e.preventDefault(); // Prevent page scroll
                targetZoom += e.deltaY * 0.01;
                targetZoom = Math.max(8, Math.min(25, targetZoom)); // Zoom limits
                // Adjust camera position along its current view vector towards/away from origin
                const direction = new THREE.Vector3();
                camera.getWorldDirection(direction);
                // For zoom, it's easier to move along the vector from origin to camera
                const positionMagnitude = camera.position.length();
                camera.position.normalize().multiplyScalar(targetZoom);

                // Ensure Y position doesn't get too low/high if perspective changes
                camera.position.y = Math.max(5, Math.min(15, camera.position.y + (targetZoom > positionMagnitude ? 0.1: -0.1) * (e.deltaY > 0 ? 1: -1) ));
                camera.lookAt(0,0,0);

            });
        }

        function animate() {
            requestAnimationFrame(animate);
            // GSAP handles its own updates for specific animations
            renderer.render(scene, camera);
        }
        
        function animateCameraToTable() {
            cameraAnimating = true;
            gsap.to(camera.position, { duration: 1.5, x: 0, y: 10, z: 13, ease: "power2.inOut", onUpdate: () => camera.lookAt(0,0,0), onComplete: () => cameraAnimating = false });
        }
        function animateCameraToMenu() {
            cameraAnimating = true;
            gsap.to(camera.position, { duration: 1.5, x: 0, y: 12, z: 15, ease: "power2.inOut", onUpdate: () => camera.lookAt(0,0,0), onComplete: () => cameraAnimating = false });
        }

        function updateTableVisuals3D() {
            clearTable3DObjects();
            if (!gameState || !playerPositions3D.length) return;

            // Community Cards
            gameState.community_cards.forEach((card, index) => {
                const pos = new THREE.Vector3(-2 + index * 1, 0.3, 0); // Centered on table
                const cardObj = createCard3DObject(card.suit, card.rank, pos, 0, true);
                scene.add(cardObj); tableCards3D.push(cardObj);
                gsap.from(cardObj.scale, {duration: 0.5, x:0, y:0, z:0, ease: "back.out(1.7)", delay: index * 0.1});
            });

            // Player Cards and Chips
            Object.values(gameState.players).forEach((player) => {
                const playerUIIndex = player.position; // Assuming player.position is 0 to N-1 index at table
                if (playerUIIndex >= 0 && playerUIIndex < playerPositions3D.length) {
                    const p3dPos = playerPositions3D[playerUIIndex];
                    
                    // Player cards
                    if (player.cards && player.cards.length > 0) {
                        playerCardObjects3D[player.id] = [];
                        player.cards.forEach((card, cardIdx) => {
                            const cardOffset = (cardIdx - (player.cards.length - 1) / 2) * 0.5; // Spread cards slightly
                            const cardPosition = new THREE.Vector3(p3dPos.cardX + cardOffset * Math.cos(p3dPos.angle + Math.PI/2), 0.3, p3dPos.cardZ + cardOffset * Math.sin(p3dPos.angle + Math.PI/2));
                            const faceUp = card.suit !== 'back';
                            const cardObj = createCard3DObject(card.suit, card.rank, cardPosition, p3dPos.angle, faceUp);
                            scene.add(cardObj); playerCardObjects3D[player.id].push(cardObj);
                            gsap.from(cardObj.position, {duration: 0.5, y: 2, ease: "bounce.out", delay: 0.5 + cardIdx * 0.1});
                        });
                    }
                    // Player bet chips (simplified: one stack for current_bet in front of player)
                    if (player.current_bet > 0) {
                         const chipPos = new THREE.Vector3(p3dPos.chipX, 0.25, p3dPos.chipZ);
                         const chipStack = createChip3DStack(player.current_bet, chipPos, Math.min(5, Math.ceil(player.current_bet/100))); // Max 5 visible chips in stack
                         scene.add(chipStack); chipStacks3D.push(chipStack);
                         gsap.from(chipStack.scale, {duration: 0.3, x:0,y:0,z:0, ease:"elastic.out(1,0.5)", delay:0.8});
                    }
                }
            });

            // Pot Chips
            if (gameState.pot > 0) {
                const potPosition = new THREE.Vector3(0, 0.25, 1.5); // Pot slightly forward on table
                const potChips = createChip3DStack(gameState.pot, potPosition, Math.min(10, Math.ceil(gameState.pot/200))); // Max 10 visible chips
                scene.add(potChips); chipStacks3D.push(potChips);
                gsap.from(potChips.scale, {duration: 0.5, x:0,y:0,z:0, ease:"elastic.out(1,0.3)", delay:0.2});
            }
        }
        function clearTable3DObjects() {
            tableCards3D.forEach(c => scene.remove(c)); tableCards3D = [];
            Object.values(playerCardObjects3D).flat().forEach(c => scene.remove(c)); playerCardObjects3D = {};
            chipStacks3D.forEach(s => scene.remove(s)); chipStacks3D = [];
        }

        function connectWebSocket() {
            const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
            const wsUrl = `${protocol}//${window.location.host}/ws`;
            ws = new WebSocket(wsUrl);
            ws.onopen = function() {
                isConnected = true; hideLoadingScreen(); showMainMenu();
                if (!initialConnectionNotified) { showNotification('Connected to Royal Poker 3D!', 'success'); initialConnectionNotified = true; }
                connectionLostNotified = false;
            };
            ws.onmessage = function(event) { const message = JSON.parse(event.data); handleServerMessage(message); };
            ws.onclose = function() {
                isConnected = false; showLoadingScreen('Connection lost. Reconnecting...');
                if (!connectionLostNotified) { showNotification('Connection lost. Attempting to reconnect...', 'error'); connectionLostNotified = true; }
                initialConnectionNotified = false; 
                setTimeout(connectWebSocket, 3000);
            };
            ws.onerror = function(error) { console.error('WebSocket error:', error); showNotification('Connection error occurred', 'error');};
        }
        function sendMessage(action, payload = {}) { if (ws && ws.readyState === WebSocket.OPEN) { ws.send(JSON.stringify({ action, payload })); } else { showNotification('Not connected to server', 'error'); } }

        function handleServerMessage(message) {
            console.log('Received:', message.type, message.data);
            switch (message.type) {
                case 'connected': myPlayerId = message.data.player_id; showNotification(`Welcome! Your ID: ${myPlayerId.substring(0,6)}. Server: ${message.data.server_info.version}`, 'success'); break;
                case 'room_created': case 'room_joined':
                    currentRoomCode = message.data.room_code; showGameInterface();
                    showNotification(`Joined room: ${message.data.room_name || currentRoomCode}`, 'success'); animateCameraToTable(); break;
                case 'spectating': currentRoomCode = message.data.room_code; showGameInterface(); showNotification(`Spectating room ${currentRoomCode}`, 'info'); animateCameraToTable(); break;
                case 'room_left': showMainMenu(); showNotification('Left room: ' + message.data.room_code, 'info'); animateCameraToMenu(); currentRoomCode = null; gameState = null; clearTable3DObjects(); break;
                case 'game_state': gameState = message.data; updateGameInterface(); updateTableVisuals3D(); break; // Use 3D update
                case 'game_started': showNotification('Game started! Good luck!', 'success'); break;
                case 'room_list': updateRoomList(message.data.rooms); break;
                case 'hand_history': updateHandHistory(message.data.history); break;
                case 'error': showNotification('Error: ' + message.message, 'error'); break;
                default: console.log('Unknown message type:', message.type);
            }
        }
        
        function hideLoadingScreen() { const el = document.getElementById('loadingScreen'); gsap.to(el, { duration: 1, opacity: 0, onComplete: () => el.style.display = 'none' }); updateUiActiveState();}
        function showLoadingScreen(text = 'Loading casino experience...') { const el = document.getElementById('loadingScreen'); el.querySelector('.loading-text').textContent = text; el.style.display = 'flex'; gsap.to(el, { duration: 0.5, opacity: 1 }); updateUiActiveState();}
        function showMainMenu() { document.getElementById('menuPanel').classList.remove('hidden'); document.getElementById('gameHUD').classList.add('hidden'); document.getElementById('potDisplay').classList.add('hidden'); document.getElementById('actionsPanel').classList.add('hidden'); document.getElementById('chatPanel').classList.add('hidden'); document.getElementById('playerCards').classList.add('hidden'); document.getElementById('tournamentInfo').classList.add('hidden'); document.getElementById('actionTimer').classList.add('hidden'); currentRoomCode = null; gameState = null; updateUiActiveState(); clearTable3DObjects(); }
        function showGameInterface() { document.getElementById('menuPanel').classList.add('hidden'); document.getElementById('gameHUD').classList.remove('hidden'); document.getElementById('chatPanel').classList.remove('hidden'); document.getElementById('playerCards').classList.remove('hidden'); if (currentRoomCode) document.getElementById('currentRoom').textContent = currentRoomCode; updateUiActiveState(); }

        function updateGameInterface() {
            if (!gameState) return;
            document.getElementById('phaseText').textContent = gameState.phase.replace(/_/g, ' ').toUpperCase();
            document.getElementById('handNumber').textContent = gameState.hand_number;
            document.getElementById('betToMatch').textContent = gameState.current_bet.toLocaleString();

            const myPlayerData = gameState.players[myPlayerId];
            if (myPlayerData) {
                document.getElementById('myMoneyAmount').textContent = myPlayerData.money.toLocaleString();
            } else { // Spectator or player not yet in players list
                 document.getElementById('myMoneyAmount').textContent = "N/A";
            }


            if (gameState.pot > 0 || (gameState.side_pots && gameState.side_pots.length > 0)) {
                document.getElementById('potDisplay').classList.remove('hidden');
                document.getElementById('potAmount').textContent = gameState.pot.toLocaleString();
                const sidePotsEl = document.getElementById('sidePots');
                if (gameState.side_pots && gameState.side_pots.length > 0) {
                    sidePotsEl.innerHTML = gameState.side_pots.map((sp, i) => `Side ${i+1}: ${sp.amount.toLocaleString()} (${sp.eligible_players_count} players)`).join('<br>');
                } else { sidePotsEl.innerHTML = ''; }
            } else { document.getElementById('potDisplay').classList.add('hidden'); }

            if (gameState.tournament_info) { /* ... (No changes) ... */ } else { document.getElementById('tournamentInfo').classList.add('hidden'); }
            
            if (gameState.can_act && gameState.time_left_for_action > 0) {
                document.getElementById('actionTimer').classList.remove('hidden');
                document.getElementById('timerSeconds').textContent = Math.ceil(gameState.time_left_for_action);
            } else { document.getElementById('actionTimer').classList.add('hidden'); }

            const startBtn = document.getElementById('startGameBtn');
            const ownerId = gameState.players && Object.values(gameState.players).length > 0 ? Object.values(gameState.players).find(p=>p.id === myPlayerId && gameState.owner_id === myPlayerId) : false; // Check if I am owner
            // A better check for owner: backend should send room.owner_id in game_state
            const roomOwner = gameState.owner_id; // Assuming it's sent in gameState
            
            if (gameState.phase === 'waiting' && Object.keys(gameState.players).length >= 2 && myPlayerId === roomOwner) {
                startBtn.style.display = 'block';
            } else { startBtn.style.display = 'none'; }

            document.getElementById('actionsPanel').style.display = (gameState.can_act && gameState.available_actions && gameState.available_actions.length > 0) ? 'flex' : 'none';
            if (gameState.can_act) updateActionButtons();
            
            updatePlayerCards(); updateChat();
            if (gameState.paused && gameState.pause_reason !== lastPauseReasonNotified) { showNotification(`Game paused: ${gameState.pause_reason}`, 'warning'); lastPauseReasonNotified = gameState.pause_reason; }
            else if (!gameState.paused) { lastPauseReasonNotified = "";}
        }

        function updateActionButtons() {
            if (!gameState || !gameState.available_actions) return;
            const actions = gameState.available_actions;
            ['foldBtn', 'checkBtn', 'callBtn', 'raiseControlsContainer', 'allInBtn'].forEach(id => {
                const el = document.getElementById(id);
                if(el) { el.style.display = 'none'; if(el.tagName === 'BUTTON') el.disabled = true;}
            });
            
            actions.forEach(action => {
                if (action.action === 'fold') { document.getElementById('foldBtn').style.display = 'inline-block'; document.getElementById('foldBtn').disabled = false; }
                if (action.action === 'check') { document.getElementById('checkBtn').style.display = 'inline-block'; document.getElementById('checkBtn').disabled = false; }
                if (action.action === 'call') { document.getElementById('callBtn').style.display = 'inline-block'; document.getElementById('callBtn').disabled = false; document.getElementById('callAmount').textContent = action.amount.toLocaleString(); }
                if (action.action === 'raise') { 
                    document.getElementById('raiseControlsContainer').style.display = 'flex'; 
                    document.getElementById('raiseBtn').disabled = false;
                    const slider = document.getElementById('raiseSlider'); const input = document.getElementById('raiseAmountInput');
                    slider.min = action.min_amount; slider.max = action.max_amount; input.min = action.min_amount; input.max = action.max_amount;
                    input.value = Math.max(action.min_amount, Math.min(parseInt(input.value) || action.min_amount, action.max_amount) ); // Keep current if valid, else min
                    slider.value = input.value;
                }
                if (action.action === 'all_in') { document.getElementById('allInBtn').style.display = 'inline-block'; document.getElementById('allInBtn').disabled = false; document.getElementById('allInBtn').innerHTML = `🔥 ALL IN ${action.amount.toLocaleString()}`; }
            });
        }
        function updateRaiseAmountDisplay() { document.getElementById('raiseAmountInput').value = document.getElementById('raiseSlider').value; }
        function updateRaiseSliderFromInput() { document.getElementById('raiseSlider').value = document.getElementById('raiseAmountInput').value; }

        function updatePlayerCards() {
            const container = document.getElementById('playerCards'); container.innerHTML = '';
            if (!gameState || !gameState.players) return;
            Object.values(gameState.players).sort((a,b) => a.position - b.position).forEach(player => {
                const cardDiv = document.createElement('div'); cardDiv.className = 'player-card';
                if (player.is_current_player) cardDiv.classList.add('current-player');
                if (player.status === 'folded') cardDiv.classList.add('folded');
                if (player.status === 'all_in') cardDiv.classList.add('all-in');
                
                let aiIcon = player.is_ai ? '<span style="font-size:0.8em; opacity:0.7;">🤖</span>' : '';
                let dealerIcon = player.is_dealer ? '<span style="position: absolute; top: -8px; left: -8px; background: gold; color: black; border-radius: 50%; width: 20px; height: 20px; display: flex; align-items: center; justify-content: center; font-size: 0.7rem; font-weight: bold; box-shadow: 0 0 5px black;">D</span>' : '';
                let blindText = '';
                if(player.is_small_blind) blindText = '<span style="font-size:0.7em; color:lightblue;">SB</span>';
                if(player.is_big_blind) blindText = '<span style="font-size:0.7em; color:lightgreen;">BB</span>';

                cardDiv.innerHTML = `
                    <div class="player-avatar" style="background-color: ${player.color}">${player.name.charAt(0).toUpperCase()}</div>
                    <div class="player-name">${aiIcon} ${player.name} ${blindText}</div>
                    <div class="player-money">${player.money.toLocaleString()}</div>
                    ${player.current_bet > 0 ? `<div style="color: var(--primary-gold); font-size: 0.9rem;">Bet: ${player.current_bet.toLocaleString()}</div>` : ''}
                    ${player.last_action ? `<div class="player-action">${player.last_action.toUpperCase()}</div>` : ''}
                    ${dealerIcon}
                `;
                container.appendChild(cardDiv);
                gsap.from(cardDiv, { duration: 0.3, scale: 0.5, opacity: 0, delay: player.position * 0.05 });
            });
        }
        function updateChat() { /* ... (No changes from your original, ensure it scrolls correctly) ... */ 
            if (!gameState || !gameState.chat_messages) return;
            const chatMessagesEl = document.getElementById('chatMessages');
            const shouldScroll = chatMessagesEl.scrollTop + chatMessagesEl.clientHeight >= chatMessagesEl.scrollHeight - 20; // Threshold
            chatMessagesEl.innerHTML = gameState.chat_messages.map(msg => 
                `<div class="chat-message" style="border-left-color: ${msg.player_color || '#ffffff'};">
                    <span class="chat-player-name" style="color: ${msg.player_color || '#ffffff'}">${msg.player_name}:</span>
                    <span>${msg.message}</span>
                    <span class="chat-timestamp">${msg.formatted_time}</span>
                </div>`
            ).join('');
            if (shouldScroll) chatMessagesEl.scrollTop = chatMessagesEl.scrollHeight;
        }
        function updateTournamentTimer(nextLevelTimeStr) { /* ... (No changes from your original) ... */ }

        function createQuickRoom() { const name = document.getElementById('playerName').value.trim() || 'Player'; sendMessage('create_room', { player_name: name, game_mode: 'cash_game', small_blind: 25, big_blind: 50, max_players: 8, num_ai_players: 0 }); }
        function createCustomRoom() {
            const payload = {
                player_name: document.getElementById('playerName').value.trim() || 'Player',
                room_name: document.getElementById('roomName').value.trim(),
                game_mode: document.getElementById('gameMode').value,
                max_players: parseInt(document.getElementById('maxPlayers').value),
                small_blind: parseInt(document.getElementById('smallBlind').value),
                big_blind: parseInt(document.getElementById('bigBlind').value),
                buy_in: parseInt(document.getElementById('buyIn').value),
                password: document.getElementById('roomPassword').value.trim(),
                num_ai_players: parseInt(document.getElementById('numAiPlayers').value)
            };
            sendMessage('create_room', payload);
        }
        function joinRoom() { const code = document.getElementById('roomCode').value.trim().toUpperCase(); const name = document.getElementById('playerName').value.trim() || 'Player'; if (!code) { showNotification('Please enter a room code', 'error'); return; } sendMessage('join_room', { room_code: code, player_name: name }); }
        function spectateRoom() { const code = document.getElementById('roomCode').value.trim().toUpperCase(); if (!code) { showNotification('Please enter a room code', 'error'); return; } sendMessage('spectate', { room_code: code }); }
        function leaveRoom() { sendMessage('leave_room'); }
        function startGame() { sendMessage('start_game'); }
        function pauseGame() { sendMessage('pause_game'); } // Assuming only owner can, backend validates
        function playerAction(action) {
            let payload = { action_type: action };
            if (action === 'raise') { payload.amount = parseInt(document.getElementById('raiseAmountInput').value) || 0; }
            // For call, amount is determined by server or can be sent if UI shows it. Here, server calculates based on 'call' action.
            sendMessage('player_action', payload);
        }
        function sendChat() { const input = document.getElementById('chatInput'); const msg = input.value.trim(); if (msg && msg.length <= 200) { sendMessage('send_chat', { message: msg }); input.value = ''; } else if (msg.length > 200) { showNotification('Message too long (max 200 characters)', 'error'); } }
        function toggleChat() { chatCollapsed = !chatCollapsed; document.getElementById('chatMessages').style.display = chatCollapsed ? 'none' : 'block'; document.getElementById('chatToggle').textContent = chatCollapsed ? '+' : '−'; }
        
        function showRoomList() { document.getElementById('roomListModal').classList.remove('hidden'); sendMessage('get_room_list'); updateUiActiveState(); }
        function hideRoomList() { document.getElementById('roomListModal').classList.add('hidden'); updateUiActiveState(); }
        function refreshRoomList() { sendMessage('get_room_list'); } // No need for separate UI active update if modal stays open
        function updateRoomList(rooms) {
            const listEl = document.getElementById('roomList');
            if (rooms.length === 0) { listEl.innerHTML = '<div style="text-align: center; color: #ccc; padding: 20px;">No public rooms available</div>'; return; }
            listEl.innerHTML = rooms.map(room => `
                <div style="background: rgba(255,255,255,0.1); border-radius: 10px; padding: 15px; margin-bottom: 10px; border: 1px solid var(--primary-gold);">
                    <div style="display: flex; justify-content: space-between; align-items: center; margin-bottom: 10px;"><strong style="color: var(--primary-gold);">${room.name} (${room.code})</strong> <span style="font-size:0.8em;">${room.game_mode.replace('_',' ')}</span></div>
                    <div style="display: grid; grid-template-columns: 1fr 1fr; gap: 10px; font-size: 0.9rem;">
                        <div>👥 ${room.players} / ${room.max_players}</div><div>👁️ ${room.spectators}</div>
                        <div>🎲 ${room.phase.replace('_',' ')}</div><div>💰 ${room.small_blind}/${room.big_blind}</div>
                    </div>
                    <div style="margin-top: 10px; text-align: center;"><button class="action-button" onclick="joinRoomByCode('${room.code}')" style="margin-right: 10px;">Join</button><button class="action-button" onclick="spectateRoomByCode('${room.code}')">Spectate</button></div>
                </div>`).join('');
        }
        function joinRoomByCode(code) { document.getElementById('roomCode').value = code; hideRoomList(); joinRoom(); }
        function spectateRoomByCode(code) { document.getElementById('roomCode').value = code; hideRoomList(); spectateRoom(); }

        function showHandHistory() { document.getElementById('handHistoryModal').classList.remove('hidden'); sendMessage('get_hand_history'); updateUiActiveState(); }
        function hideHandHistory() { document.getElementById('handHistoryModal').classList.add('hidden'); updateUiActiveState(); }
        function updateHandHistory(history) { /* ... (No changes from your original) ... */ }
        
        function showNotification(message, type = 'info') {
            const container = document.body; // Or a dedicated notification container
            const notification = document.createElement('div');
            notification.className = `notification ${type}`;
            notification.textContent = message;
            container.appendChild(notification);
            gsap.from(notification, {duration: 0.5, x: "100%", opacity: 0, ease: "power2.out"});
            setTimeout(() => {
                gsap.to(notification, {duration: 0.5, x: "100%", opacity: 0, ease: "power2.in", onComplete: () => {
                    if (notification.parentNode) notification.parentNode.removeChild(notification);
                }});
            }, 4000);
        }

        window.addEventListener('resize', function() { if(camera && renderer) { camera.aspect = window.innerWidth / window.innerHeight; camera.updateProjectionMatrix(); renderer.setSize(window.innerWidth, window.innerHeight); }});
        document.addEventListener('keydown', function(event) { /* ... (No changes from your original) ... */ });
        window.addEventListener('load', function() { initThreeJS(); connectWebSocket(); showLoadingScreen(); updateUiActiveState(); });
        // --- End of JavaScript ---
    </script>
</body>
</html>
"""

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run(app, host="0.0.0.0", port=port, ws_ping_interval=20, ws_ping_timeout=20) # Added ping for keepalive
