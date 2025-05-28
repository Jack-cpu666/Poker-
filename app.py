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
from fastapi.responses import HTMLResponse, FileResponse
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel, ValidationError, Field as PydanticField

# Configure advanced logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s - [%(filename)s:%(lineno)d]', # Added filename/lineno
    handlers=[
        logging.StreamHandler(),
        # logging.FileHandler('poker_game.log') if os.environ.get('LOG_FILE') else logging.NullHandler()
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
GAME_UPDATE_RATE = 15 # Reduced for less load during testing
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
    value: int # Combined strength value for easy comparison
    cards_used: List[Card]
    description: str
    kickers: List[int] = field(default_factory=list) # Numerical values of kickers for tie-breaking

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
    vpip: float = 0.0 # Voluntarily Put In Pot
    pfr: float = 0.0  # Pre-Flop Raise
    aggression_factor: float = 0.0
    showdown_percentage: float = 0.0


@dataclass
class Player:
    id: str
    name: str
    money: int = STARTING_MONEY
    current_bet: int = 0 # Bet in the current betting round
    total_bet_this_hand: int = 0 # Total bet accumulated throughout the current hand
    cards: List[Card] = field(default_factory=list)
    status: PlayerStatus = PlayerStatus.ACTIVE
    position: int = 0 # Table position (0 = dealer, 1 = sb, etc., logical, not UI fixed)
    last_action: Optional[PlayerAction] = None
    last_action_time: float = 0
    last_action_amount: int = 0 # The amount associated with the last action (e.g., raise amount)
    avatar: str = "default" # URL or identifier for avatar
    color: str = "#ffffff"  # Player's color for UI elements
    is_dealer: bool = False
    is_small_blind: bool = False
    is_big_blind: bool = False
    time_bank: int = 30 # Seconds, for timed decisions
    connection_id: Optional[str] = None # WebSocket connection ID if connected
    stats: PlayerStats = field(default_factory=PlayerStats)
    session_id: str = field(default_factory=lambda: str(uuid.uuid4())) # For session tracking
    tournament_rank: int = 0 # 0 if not yet eliminated or N/A
    is_ai: bool = False
    actions_this_hand: List[Dict] = field(default_factory=list) # Record of actions: {"action": "raise", "amount": 100, "phase": "flop"}

    def can_act(self) -> bool:
        return self.status == PlayerStatus.ACTIVE and self.money > 0

    def is_all_in_for_hand(self) -> bool:
        # This considers if they've bet everything they had at the start of this hand or earlier this hand
        return self.status == PlayerStatus.ALL_IN or (self.money == 0 and self.total_bet_this_hand > 0)


    def reset_for_new_hand(self):
        self.cards = []
        self.current_bet = 0
        self.total_bet_this_hand = 0 # Reset for the new hand
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
    tournament_structure: Dict = field(default_factory=dict) # e.g., {"levels": [{"sb": 25, "bb": 50, "ante": 0, "duration_minutes": 10}, ...]}
    buy_in: int = 0 # 0 for free, or amount for cash games/tournaments
    password: Optional[str] = None # For private rooms
    ai_players: int = 0 # Number of AI players to add

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
    pot: int = 0 # Total pot from all player bets in the current hand
    side_pots: List[SidePot] = field(default_factory=list)
    current_bet_to_match: int = 0 # The highest bet amount players need to match in the current round
    min_raise_amount: int = BIG_BLIND # The minimum additional amount for a valid raise
    chat_messages: List[Dict] = field(default_factory=list)
    last_action_timestamp: float = 0 # Timestamp of the last player action, for timeouts
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
    _player_order_for_hand: List[str] = field(default_factory=list) # player_ids in order of action for current hand
    _current_player_order_index: int = 0 # Index into _player_order_for_hand for current actor

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
        logger.info(f"Room {self.code}: Dealing cards. Deck size: {len(self.deck)}")
        for _ in range(2): # Two cards per player
            for player_id in self._player_order_for_hand:
                player = self.players.get(player_id)
                if player and player.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED]:
                    if self.deck:
                        player.cards.append(self.deck.pop())
                    else:
                        logger.error(f"Room {self.code}: Deck ran out of cards while dealing to {player_id}!")
                        return # Major issue

    def deal_community_cards(self, count: int):
        logger.info(f"Room {self.code}: Dealing {count} community cards. Deck size: {len(self.deck)}")
        if self.deck and count > 0: self.deck.pop() # Burn one card
        for _ in range(count):
            if self.deck:
                self.community_cards.append(self.deck.pop())
            else:
                logger.error(f"Room {self.code}: Deck ran out of cards while dealing community cards!")
                return

    def get_active_players_in_hand(self) -> List[Player]:
        """Returns players who are still active (not folded, eliminated, or sitting out) in the current hand."""
        return [
            p for p_id in self._player_order_for_hand
            if (p := self.players.get(p_id)) and p.status not in [PlayerStatus.FOLDED, PlayerStatus.ELIMINATED, PlayerStatus.SITTING_OUT]
        ]

    def get_players_eligible_for_pot(self) -> List[Player]:
        """Returns players who could potentially win a pot (not folded or eliminated)."""
        return [
            p for p in self.players.values()
            if p.status not in [PlayerStatus.FOLDED, PlayerStatus.ELIMINATED]
        ]

    def calculate_side_pots(self):
        logger.info(f"Room {self.code}: Calculating side pots. Current main pot: {self.pot}")
        self.side_pots = []

        # Players who have contributed to the pot and are not folded/eliminated
        contending_players = sorted(
            [p for p in self.get_players_eligible_for_pot() if p.total_bet_this_hand > 0],
            key=lambda p: p.total_bet_this_hand
        )

        if not contending_players:
            logger.info(f"Room {self.code}: No contending players for side pot calculation.")
            if self.pot > 0: # If there's a main pot but no contenders (e.g. everyone folded but one)
                 # This should be handled by win-by-default logic mostly, but as a fallback:
                eligible_main_pot_players = {p.id for p in self.get_players_eligible_for_pot()}
                if eligible_main_pot_players:
                    self.side_pots.append(SidePot(amount=self.pot, eligible_players=eligible_main_pot_players))
            return

        # Get unique bet amounts from players who are all-in or have contributed
        all_in_bet_levels = sorted(list(set(p.total_bet_this_hand for p in contending_players)))

        last_bet_level_processed = 0
        remaining_main_pot_amount = self.pot

        for bet_level in all_in_bet_levels:
            if bet_level <= last_bet_level_processed: # Only process new, higher bet levels
                continue

            # Amount this pot will take from each contributing player for this specific bet level
            contribution_this_level = bet_level - last_bet_level_processed
            current_side_pot_amount = 0
            eligible_for_this_pot = set()

            for player in self.players.values(): # Iterate all players to see who contributed up to this level
                if player.total_bet_this_hand > last_bet_level_processed:
                    actual_contribution = min(player.total_bet_this_hand - last_bet_level_processed, contribution_this_level)
                    current_side_pot_amount += actual_contribution
                    if player.status not in [PlayerStatus.FOLDED, PlayerStatus.ELIMINATED]:
                        eligible_for_this_pot.add(player.id)

            if current_side_pot_amount > 0 and eligible_for_this_pot:
                self.side_pots.append(SidePot(amount=current_side_pot_amount, eligible_players=eligible_for_this_pot))
                remaining_main_pot_amount -= current_side_pot_amount

            last_bet_level_processed = bet_level

        # Any remaining pot after all all-in levels are processed is the true "main pot"
        # contested by players who matched the highest all-in or more.
        if remaining_main_pot_amount > 0:
            eligible_final_main_pot = {
                p.id for p in contending_players if p.total_bet_this_hand >= last_bet_level_processed
            }
            if eligible_final_main_pot: # Ensure there are actually players eligible
                 self.side_pots.append(SidePot(amount=remaining_main_pot_amount, eligible_players=eligible_final_main_pot))
            elif self.pot > 0 and not self.side_pots: # Fallback if logic above fails for simple cases
                eligible_players = {p.id for p in self.get_players_eligible_for_pot()}
                if eligible_players:
                    self.side_pots.append(SidePot(amount=self.pot, eligible_players=eligible_players))


        # Ensure pots are ordered by amount (typically smallest first for distribution)
        self.side_pots.sort(key=lambda sp: sp.amount)
        # Filter out empty pots just in case
        self.side_pots = [sp for sp in self.side_pots if sp.amount > 0 and sp.eligible_players]

        logger.info(f"Room {self.code} calculated {len(self.side_pots)} side pots: {self.side_pots}")


    def update_activity(self):
        self.last_activity = datetime.now()

    def get_player_acting_next(self, start_player_id: Optional[str]) -> Optional[str]:
        if not self._player_order_for_hand:
            logger.warning(f"Room {self.code}: get_player_acting_next called with empty _player_order_for_hand.")
            return None

        try:
            current_idx_in_order = self._player_order_for_hand.index(start_player_id) if start_player_id else -1
        except ValueError:
            logger.warning(f"get_player_acting_next: start_player_id {start_player_id} not in _player_order_for_hand for room {self.code}. Trying to find first valid actor.")
            current_idx_in_order = -1 # Start search from beginning of order

        for i in range(len(self._player_order_for_hand)):
            next_idx_in_order = (current_idx_in_order + 1 + i) % len(self._player_order_for_hand)
            next_player_id_check = self._player_order_for_hand[next_idx_in_order]
            player = self.players.get(next_player_id_check)

            if player and player.can_act() and not player.is_all_in_for_hand():
                # Additional check: ensure this player hasn't already matched the current bet unless they were the BB and it was checked to them.
                # This is complex. The betting round completion logic should handle this.
                # For now, just ensure they can act.
                return player.id
        logger.info(f"Room {self.code}: No player found to act next after {start_player_id}.")
        return None


class AdvancedPokerGame:
    def __init__(self):
        self.rooms: Dict[str, Room] = {}
        self.connections: Dict[str, WebSocket] = {} # player_id -> WebSocket
        self.player_rooms: Dict[str, str] = {} # player_id -> room_code
        self.rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.action_rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.hand_evaluation_cache: Dict[str, HandEvaluation] = {} # Cache key: frozenset of (rank, suit) tuples
        self.running = True
        self.global_stats = {'total_hands': 0, 'total_players': 0, 'active_rooms': 0, 'biggest_pot': 0}

    def generate_room_code(self) -> str:
        return ''.join(random.choices('ABCDEFGHJKLMNPQRSTUVWXYZ23456789', k=6))

    def create_room(self, creator_player_id: str, room_settings: GameSettings, room_name: Optional[str] = None) -> Optional[str]:
        if len(self.rooms) >= MAX_ROOMS:
            logger.error("Maximum number of rooms reached")
            return None
        room_code = self.generate_room_code()
        while room_code in self.rooms:
            room_code = self.generate_room_code()

        room_name = room_name or f"Room {room_code}"
        final_room_type = RoomType.PRIVATE if room_settings.password else RoomType.PUBLIC
        if room_settings.game_mode == GameMode.TOURNAMENT:
             final_room_type = RoomType.TOURNAMENT # Tournaments can be public or private via password still

        self.rooms[room_code] = Room(
            code=room_code, name=room_name, players={}, spectators=set(),
            deck=[], community_cards=[], settings=room_settings,
            owner_id=creator_player_id, room_type=final_room_type
        )
        logger.info(f"Room {room_code} ({room_name}) created by player {creator_player_id} with type {final_room_type.value}.")

        for i in range(room_settings.ai_players):
            ai_player_id = f"AI_{str(uuid.uuid4())[:8]}"
            ai_money = room_settings.buy_in if room_settings.buy_in > 0 else \
                       (TOURNAMENT_STARTING_MONEY if room_settings.game_mode == GameMode.TOURNAMENT else STARTING_MONEY)
            ai_player = Player(id=ai_player_id, name=f"AI Bot {i+1}", money=ai_money, is_ai=True,
                               avatar=f"avatar_ai_{random.randint(1,3)}", color=f"#{random.randint(0x808080, 0xFFFFFF):06x}")
            self.rooms[room_code].players[ai_player_id] = ai_player
        logger.info(f"Added {room_settings.ai_players} AI players to room {room_code}.")
        return room_code

    def join_room(self, room_code: str, player_id: str, player_name: str, password: Optional[str] = None) -> bool:
        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"Attempt to join non-existent room {room_code} by {player_id}")
            return False

        if room.settings.password and room.settings.password != password:
            logger.warning(f"Password mismatch for room {room_code} by {player_id}")
            return False

        # Count human players already in the room
        human_players_count = sum(1 for p in room.players.values() if not p.is_ai)
        if human_players_count >= room.settings.max_players: # Assuming max_players in settings is for humans
            logger.warning(f"Room {room_code} is full for human players (max: {room.settings.max_players}, current: {human_players_count})")
            return False

        if player_id in room.players: # Rejoining player
            rejoining_player = room.players[player_id]
            if rejoining_player.is_ai:
                logger.warning(f"Human player {player_id} attempting to join as existing AI {rejoining_player.name}")
                return False # Cannot replace an AI this way
            rejoining_player.connection_id = player_id # Update connection ID
            rejoining_player.name = player_name # Allow name update on rejoin
            if rejoining_player.status == PlayerStatus.ELIMINATED and room.settings.game_mode != GameMode.TOURNAMENT:
                # Allow re-buy in cash games if eliminated (simplified)
                rejoining_player.status = PlayerStatus.ACTIVE
                rejoining_player.money = room.settings.buy_in if room.settings.buy_in > 0 else STARTING_MONEY
                logger.info(f"Player {player_name} ({player_id}) re-bought into room {room_code}.")
            else:
                logger.info(f"Player {player_name} ({player_id}) re-joined room {room_code}.")
        else: # New player
            player_money = room.settings.buy_in if room.settings.buy_in > 0 else \
                           (TOURNAMENT_STARTING_MONEY if room.settings.game_mode == GameMode.TOURNAMENT else STARTING_MONEY)
            player = Player(
                id=player_id, name=player_name, money=player_money,
                avatar=f"avatar_{random.randint(1, 10)}", color=f"#{random.randint(0, 0xFFFFFF):06x}",
                connection_id=player_id, is_ai=False
            )
            room.players[player_id] = player
            logger.info(f"Player {player_name} ({player_id}) joined room {room_code} with ${player_money}.")

        self.player_rooms[player_id] = room_code
        room.update_activity()
        return True

    def leave_room(self, player_id: str, force: bool = False):
        logger.info(f"Player {player_id} attempting to leave room. Force: {force}")
        room_code = self.player_rooms.pop(player_id, None)
        if not room_code:
            logger.info(f"Player {player_id} tried to leave but was not in any room.")
            return

        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"Player {player_id} was in room {room_code}, but room not found during leave.")
            return

        player_obj = room.players.get(player_id)

        if player_obj:
            logger.info(f"Player {player_obj.name} ({player_id}) leaving room {room_code}.")
            if room.phase not in [GamePhase.WAITING, GamePhase.GAME_OVER] and \
               player_obj.status not in [PlayerStatus.FOLDED, PlayerStatus.ELIMINATED, PlayerStatus.SITTING_OUT]:
                logger.info(f"Player {player_obj.name} was active in hand, folding due to leave.")
                player_obj.status = PlayerStatus.FOLDED # Fold them if they leave mid-hand
                # If it was their turn, advance game
                if room.current_player_id == player_id:
                    logger.info(f"It was {player_obj.name}'s turn. Advancing game flow after fold-on-leave.")
                    # This needs to be an async call if advance_game_flow is async
                    asyncio.create_task(self.trigger_advance_game_flow(room_code)) # Use a helper if direct call causes issues
            # Actually remove the player object
            del room.players[player_id]
            logger.info(f"Player {player_obj.name} ({player_id}) removed from room {room_code} players dict.")


        room.spectators.discard(player_id) # Also remove from spectators if they were one

        if not any(not p.is_ai for p in room.players.values()) and not room.spectators:
            logger.info(f"Room {room_code} is empty of human players and spectators. Closing room.")
            if room_code in self.rooms:
                del self.rooms[room_code]
                logger.info(f"Room {room_code} deleted.")
        elif room.owner_id == player_id and any(not p.is_ai for p in room.players.values()):
            # Transfer ownership if owner leaves and other human players exist
            new_owner = next((pid for pid, p_obj in room.players.items() if not p_obj.is_ai), None)
            if new_owner:
                room.owner_id = new_owner
                logger.info(f"Room owner {player_id} left. New owner of room {room_code} is {new_owner}.")
            else:
                logger.info(f"Owner {player_id} left room {room_code}, no other human players to transfer ownership to.")
        room.update_activity()

    async def trigger_advance_game_flow(self, room_code: str):
        # Helper to ensure advance_game_flow is called from an async context if needed
        # (though player_action already handles this)
        self.advance_game_flow(room_code)


    def start_game(self, room_code: str) -> bool:
        room = self.rooms.get(room_code)
        if not room:
            logger.error(f"start_game called for non-existent room {room_code}")
            return False

        eligible_players = [p for p in room.players.values() if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED] and p.money > 0]
        if len(eligible_players) < room.settings.min_players:
            logger.warning(f"Cannot start game in room {room_code}: Not enough players ({len(eligible_players)}/{room.settings.min_players})")
            return False

        if room.phase != GamePhase.WAITING and room.phase != GamePhase.GAME_OVER: # Allow start from GAME_OVER
            logger.warning(f"Game already in progress or in unexpected state in room {room_code}. Phase: {room.phase}")
            return False

        logger.info(f"Starting game in room {room_code}...")
        room.phase = GamePhase.PRE_FLOP
        room.hand_number += 1
        room.shuffle_deck()
        room.community_cards = []
        room.pot = 0
        room.side_pots = [] # Clear side pots from previous hand

        # Reset players for the new hand
        for player in room.players.values():
            player.reset_for_new_hand() # This also sets status to ACTIVE if not SITTING_OUT/ELIMINATED

        # Determine player order and dealer for this hand
        # Players who are not SITTING_OUT or ELIMINATED and have money
        active_players_for_seating = [p for p in room.players.values() if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED] and p.money > 0]
        if not active_players_for_seating:
            logger.error(f"Room {room.code}: No active players to start game with.")
            room.phase = GamePhase.WAITING
            return False

        active_player_ids_for_seating = [p.id for p in active_players_for_seating]

        if not room.dealer_player_id or room.dealer_player_id not in active_player_ids_for_seating:
            # If no dealer or dealer is not active, pick first active player
            room.dealer_player_id = active_player_ids_for_seating[0]
        else:
            # Move dealer button to the next active player
            try:
                current_dealer_idx = active_player_ids_for_seating.index(room.dealer_player_id)
                next_dealer_idx = (current_dealer_idx + 1) % len(active_player_ids_for_seating)
                room.dealer_player_id = active_player_ids_for_seating[next_dealer_idx]
            except ValueError: # Should not happen if previous check is robust
                 room.dealer_player_id = active_player_ids_for_seating[0]


        # Set dealer flag
        if room.dealer_player_id in room.players:
            room.players[room.dealer_player_id].is_dealer = True

        # Establish player order for this hand, starting from player left of dealer
        dealer_actual_idx_in_ordered_list = -1
        # Create an ordered list of active players starting from dealer for rotation
        ordered_players_for_blinds = []
        try:
            start_idx = active_player_ids_for_seating.index(room.dealer_player_id)
            ordered_players_for_blinds = active_player_ids_for_seating[start_idx:] + active_player_ids_for_seating[:start_idx]
            # Now rotate so it starts from Small Blind position
            room._player_order_for_hand = ordered_players_for_blinds[1:] + ordered_players_for_blinds[:1]
        except ValueError:
            logger.error(f"Dealer {room.dealer_player_id} not in active_player_ids_for_seating. Defaulting order.")
            room._player_order_for_hand = active_player_ids_for_seating # Fallback

        num_players_in_hand_order = len(room._player_order_for_hand)
        logger.info(f"Room {room.code}: Player order for hand: {room._player_order_for_hand}. Dealer: {room.dealer_player_id}")

        # Assign Blinds
        if num_players_in_hand_order >= 2:
            # Small Blind is player left of dealer (first in _player_order_for_hand if dealer is last)
            # Heads-up: Dealer is SB, other player is BB
            sb_player_id = room.dealer_player_id if num_players_in_hand_order == 2 else room._player_order_for_hand[0]
            bb_player_id = room._player_order_for_hand[0] if num_players_in_hand_order != 2 else room._player_order_for_hand[1]
            if num_players_in_hand_order == 2: # Specific heads-up adjustment to _player_order_for_hand
                 room._player_order_for_hand = [sb_player_id, bb_player_id] # SB acts first pre-flop

            if sb_player_id in room.players: room.players[sb_player_id].is_small_blind = True
            if bb_player_id in room.players: room.players[bb_player_id].is_big_blind = True
            logger.info(f"Room {self.rooms[room_code].code}: SB: {sb_player_id}, BB: {bb_player_id}")
        elif num_players_in_hand_order == 1: # Only one player, should not happen if min_players is 2
             logger.warning(f"Room {room_code}: Only one player in hand order. Cannot assign blinds properly.")
             room.phase = GamePhase.WAITING
             return False


        self.post_blinds_and_ante(room)
        room.current_bet_to_match = room.settings.big_blind # Initial bet to match is BB
        room.min_raise_amount = room.settings.big_blind # Initial min raise is BB size

        room.deal_cards()

        # Determine first player to act pre-flop
        if num_players_in_hand_order > 0:
            if num_players_in_hand_order == 2: # Heads-up, SB (dealer) acts first
                room.current_player_id = room._player_order_for_hand[0]
            elif num_players_in_hand_order > 2: # UTG (player after BB) acts first
                bb_idx_in_order = -1
                for i, p_id in enumerate(room._player_order_for_hand):
                    if room.players[p_id].is_big_blind:
                        bb_idx_in_order = i
                        break
                if bb_idx_in_order != -1:
                    room.current_player_id = room._player_order_for_hand[(bb_idx_in_order + 1) % num_players_in_hand_order]
                else: # Fallback if BB not found (should not happen)
                    room.current_player_id = room._player_order_for_hand[2 % num_players_in_hand_order] # Approx UTG
            else: # Should not happen if min players is 2
                room.current_player_id = None
        else:
            room.current_player_id = None # No one to act

        if not room.current_player_id:
            logger.error(f"Room {room_code}: Could not determine current player to start the game.")
            room.phase = GamePhase.WAITING
            return False

        room.last_action_timestamp = time.time()
        self.global_stats['total_hands'] += 1
        logger.info(f"Game started in room {room_code}, hand #{room.hand_number}. Dealer: {room.dealer_player_id}, Current Player: {room.current_player_id}, Order: {room._player_order_for_hand}")

        # If first player is AI, trigger AI action
        if room.current_player_id and room.players[room.current_player_id].is_ai:
            asyncio.create_task(self.ai_perform_action(room_code, room.current_player_id))
        return True

    def post_blinds_and_ante(self, room: Room):
        logger.info(f"Room {room.code}: Posting blinds and antes.")
        # Ante
        if room.settings.ante > 0:
            for player_id in room._player_order_for_hand: # Iterate through players in action order
                player = room.players.get(player_id)
                if player and player.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED] and player.money > 0:
                    ante_amount = min(room.settings.ante, player.money)
                    player.money -= ante_amount
                    player.total_bet_this_hand += ante_amount # Antes contribute to total bet for side pot calcs
                    room.pot += ante_amount
                    player.actions_this_hand.append({"action": "ante", "amount": ante_amount, "phase": room.phase.value})
                    logger.info(f"Player {player.name} posted ante ${ante_amount}.")
                    if player.money == 0:
                        player.status = PlayerStatus.ALL_IN
                        logger.info(f"Player {player.name} is all-in due to ante.")

        # Blinds
        # Iterate using _player_order_for_hand as it's set up for action order
        for player_id in room._player_order_for_hand:
            player = room.players.get(player_id)
            if not player or player.status in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED] or player.money == 0:
                continue

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
                player.current_bet += blind_amount # This is their bet for this round
                player.total_bet_this_hand += blind_amount # Also contributes to total for the hand
                room.pot += blind_amount
                player.actions_this_hand.append({"action": action_label, "amount": blind_amount, "phase": room.phase.value})
                logger.info(f"Player {player.name} posted {action_label} ${blind_amount}.")
                if player.money == 0:
                    player.status = PlayerStatus.ALL_IN
                    logger.info(f"Player {player.name} is all-in due to posting {action_label}.")
        logger.info(f"Room {room.code}: Blinds/antes posted. Pot: {room.pot}")

    async def ai_perform_action(self, room_code: str, player_id: str):
        await asyncio.sleep(random.uniform(AI_ACTION_DELAY_MIN, AI_ACTION_DELAY_MAX)) # Simulate thinking
        room = self.rooms.get(room_code)
        if not room or room.current_player_id != player_id:
            logger.info(f"AI {player_id} in room {room_code}: Action aborted, not AI's turn or room gone.")
            return
        player = room.players.get(player_id)
        if not player or not player.is_ai or not player.can_act():
            logger.info(f"AI {player.name} ({player_id}) in room {room_code}: Action aborted, cannot act (status: {player.status if player else 'N/A'}).")
            return

        available_actions = self.get_available_actions(room, player_id)
        if not available_actions:
            logger.warning(f"AI {player.name} in room {room_code} has no available actions. Forcing fold if possible or logging.")
            if any(a['action'] == PlayerAction.FOLD.value for a in self.get_available_actions(room, player_id, force_check=True)): # Check if fold is inherently possible
                 self.player_action(room_code, player_id, PlayerAction.FOLD, 0)
            return


        # Simple AI logic:
        action_to_perform = None
        amount_to_perform = 0
        rand_choice = random.random()

        can_check = any(a['action'] == PlayerAction.CHECK.value for a in available_actions)
        can_call = any(a['action'] == PlayerAction.CALL.value for a in available_actions)
        can_raise = any(a['action'] == PlayerAction.RAISE.value for a in available_actions)

        if rand_choice < 0.15 and any(a['action'] == PlayerAction.FOLD.value for a in available_actions): # 15% fold
            action_to_perform = PlayerAction.FOLD
        elif rand_choice < 0.75: # 60% chance to check or call
            if can_check:
                action_to_perform = PlayerAction.CHECK
            elif can_call:
                action_to_perform = PlayerAction.CALL
                call_action_details = next(a for a in available_actions if a['action'] == PlayerAction.CALL.value)
                amount_to_perform = call_action_details['amount'] # This is the amount to call
            # If neither check nor call, will fall through to raise/all-in or fold logic
        elif can_raise: # 10% chance to raise (if possible)
            action_to_perform = PlayerAction.RAISE
            raise_action_details = next(a for a in available_actions if a['action'] == PlayerAction.RAISE.value)
            # Raise a random amount between min and a portion of their stack, or min_raise
            # This is the raise amount ON TOP of call
            raise_val = random.randint(raise_action_details['min_amount'], min(raise_action_details['max_amount'], player.money // 3))
            amount_to_perform = max(raise_action_details['min_amount'], raise_val)
        elif any(a['action'] == PlayerAction.ALL_IN.value for a in available_actions) and player.money > 0: # Fallback to all-in if raise failed and can all-in
             action_to_perform = PlayerAction.ALL_IN
        # Fallback strategies if initial choices aren't available
        if action_to_perform is None:
            if can_call:
                action_to_perform = PlayerAction.CALL
                call_action_details = next(a for a in available_actions if a['action'] == PlayerAction.CALL.value)
                amount_to_perform = call_action_details['amount']
            elif can_check:
                action_to_perform = PlayerAction.CHECK
            elif any(a['action'] == PlayerAction.ALL_IN.value for a in available_actions) and player.money > 0 :
                action_to_perform = PlayerAction.ALL_IN
            else: # Must fold if no other option
                action_to_perform = PlayerAction.FOLD

        # If action is CALL or RAISE and player doesn't have enough, it becomes ALL_IN implicitly by player_action logic
        # But AI should be smart enough to choose ALL_IN if it wants to bet more than it has (excluding current bet)
        if action_to_perform == PlayerAction.CALL and amount_to_perform >= player.money :
             action_to_perform = PlayerAction.ALL_IN
             amount_to_perform = 0 # All-in doesn't need an amount passed this way
        elif action_to_perform == PlayerAction.RAISE:
             # amount_to_perform is the raise ON TOP OF CALL
             amount_to_call = room.current_bet_to_match - player.current_bet
             total_bet_for_raise = amount_to_call + amount_to_perform
             if total_bet_for_raise >= player.money:
                  action_to_perform = PlayerAction.ALL_IN
                  amount_to_perform = 0


        logger.info(f"AI {player.name} ({player_id}) in room {room_code} chose: {action_to_perform.value} with amount {amount_to_perform if action_to_perform == PlayerAction.RAISE else (amount_to_perform if action_to_perform == PlayerAction.CALL else 0)}")
        self.player_action(room_code, player_id, action_to_perform, amount_to_perform)

    def player_action(self, room_code: str, player_id: str, action_type: PlayerAction, amount: int = 0) -> bool:
        room = self.rooms.get(room_code)
        if not room:
            logger.error(f"Player action by {player_id} for non-existent room {room_code}.")
            return False
        player = room.players.get(player_id)
        if not player:
            logger.error(f"Player action by non-existent player {player_id} in room {room_code}.")
            return False

        if room.current_player_id != player_id:
            logger.warning(f"Action by {player.name} ({player_id}) but not their turn (current: {room.current_player_id}) in room {room_code}.")
            return False
        if not player.can_act() and action_type not in [PlayerAction.SIT_OUT, PlayerAction.SIT_IN]:
            logger.warning(f"Player {player.name} ({player_id}) cannot act (status: {player.status.value}, money: {player.money}) for action {action_type.value}.")
            return False

        logger.info(f"Processing action: Player {player.name} ({player_id}), Action: {action_type.value}, Amount: {amount}, Room: {room_code}")

        # Store money before action for stats on amount_put_in_pot_this_action
        money_before_action = player.money
        current_bet_before_action = player.current_bet

        success = self.process_player_action(room, player, action_type, amount)

        if success:
            player.last_action = action_type
            player.last_action_time = time.time()
            room.last_action_timestamp = time.time() # Reset auto-fold timer

            # Calculate amount actually put into pot by this specific action
            # This is tricky due to current_bet vs total_bet_this_hand logic
            # Simplified: money change or current_bet change indicates money moved
            amount_put_in_pot_this_action = (money_before_action - player.money) + (player.current_bet - current_bet_before_action if action_type not in [PlayerAction.FOLD, PlayerAction.CHECK] else 0)
            if action_type == PlayerAction.ALL_IN:
                amount_put_in_pot_this_action = money_before_action # They bet all they had left.
            elif action_type == PlayerAction.RAISE:
                # 'amount' passed to player_action for RAISE is the raise ON TOP of call.
                # amount_to_call_this_turn was (room.current_bet_to_match - current_bet_before_action)
                # total_additional_money_this_action = amount_to_call_this_turn + amount
                # So this 'amount' is correct for last_action_amount if it's "raise X"
                # However, player.last_action_amount should perhaps be the TOTAL bet made in that turn
                # For RAISE X to Y, Y is player.current_bet.
                player.last_action_amount = player.current_bet # The total bet size after raising
            elif action_type == PlayerAction.CALL:
                player.last_action_amount = player.current_bet # Total bet size after calling
            else: # FOLD, CHECK
                 player.last_action_amount = 0


            player.actions_this_hand.append({
                "action": action_type.value,
                "amount": amount_put_in_pot_this_action, # How much this specific action added to their bet
                "total_bet_this_round": player.current_bet, # Their total bet in this betting round
                "phase": room.phase.value
            })

            # Update VPIP/PFR stats (simplified)
            if room.phase == GamePhase.PRE_FLOP:
                is_first_voluntary_action = not any(
                    act['action'] in [PlayerAction.CALL.value, PlayerAction.RAISE.value]
                    for act in player.actions_this_hand[:-1] # Exclude current action
                    if act['phase'] == GamePhase.PRE_FLOP.value
                )
                if is_first_voluntary_action and action_type in [PlayerAction.CALL, PlayerAction.RAISE, PlayerAction.ALL_IN]:
                    # This is a simplified VPIP calc, happens once per hand if they play.
                    # A more accurate VPIP needs to be calculated at hand end.
                    # For now, this is fine for basic stats.
                    player.stats.vpip = (player.stats.vpip * player.stats.hands_played + 1) / (player.stats.hands_played + 1 if player.stats.hands_played > 0 else 1)
                    if action_type == PlayerAction.RAISE:
                         player.stats.pfr = (player.stats.pfr * player.stats.hands_played + 1) / (player.stats.hands_played + 1 if player.stats.hands_played > 0 else 1)

            if action_type not in [PlayerAction.SIT_OUT, PlayerAction.SIT_IN]:
                # hands_played should arguably be incremented at the start of a hand if dealt in.
                # For simplicity, we'll increment it here for any game action.
                # A more robust way is to do it when player is dealt cards and doesn't sit out.
                # This might slightly inflate hands_played if a player makes multiple actions.
                # Let's move hands_played increment to when hand starts / player is dealt in.
                pass # Hands played incremented elsewhere or at end of hand.


            self.advance_game_flow(room_code)
            logger.info(f"Player {player.name} action {action_type.value} processed successfully. New money: ${player.money}, current_bet: ${player.current_bet}, total_bet_hand: ${player.total_bet_this_hand}")
        else:
            logger.warning(f"Player action {action_type.value} by {player.name} failed processing in room {room_code}.")
        return success

    def process_player_action(self, room: Room, player: Player, action: PlayerAction, amount: int) -> bool:
        # `amount` is the raise amount for RAISE action (on top of call)
        # `amount` is typically 0 for FOLD, CHECK, ALL_IN (server calculates all_in amount)
        # `amount` for CALL could be passed as the specific call amount, but server can also calculate it.
        # We will assume `amount` for CALL means "this is how much I am calling"

        if action == PlayerAction.FOLD:
            player.status = PlayerStatus.FOLDED
            return True

        if action == PlayerAction.CHECK:
            if player.current_bet < room.current_bet_to_match:
                logger.warning(f"{player.name} cannot CHECK. Bet to match: {room.current_bet_to_match}, player's current_bet: {player.current_bet}")
                return False
            return True

        if action == PlayerAction.CALL:
            amount_needed_to_call = room.current_bet_to_match - player.current_bet
            if amount_needed_to_call <= 0: # Already matched or trying to call 0
                logger.info(f"{player.name} attempting to call with nothing to call or already called. current_bet: {player.current_bet}, to_match: {room.current_bet_to_match}")
                return True # Effectively a check if current_bet >= room.current_bet_to_match

            actual_call_amount = min(amount_needed_to_call, player.money)

            player.money -= actual_call_amount
            player.current_bet += actual_call_amount
            player.total_bet_this_hand += actual_call_amount
            room.pot += actual_call_amount

            if player.money == 0:
                player.status = PlayerStatus.ALL_IN
            return True

        if action == PlayerAction.RAISE:
            # `amount` is the raise ON TOP OF a call.
            amount_to_call_first = room.current_bet_to_match - player.current_bet
            if amount_to_call_first < 0: amount_to_call_first = 0 # If player already bet more (should not happen if logic is right)

            # Total additional money player needs to put in for this action (call part + raise part)
            total_additional_money_for_action = amount_to_call_first + amount

            if amount <= 0: # Raise amount itself must be positive
                logger.warning(f"{player.name} RAISE failed: Raise amount ({amount}) must be positive.")
                return False
            if total_additional_money_for_action > player.money:
                logger.warning(f"{player.name} RAISE failed: Not enough money. Needs {total_additional_money_for_action}, has {player.money}.")
                return False # Cannot bet more than they have

            # A raise must be at least room.min_raise_amount, UNLESS it's an all-in that results in a raise.
            # `amount` is the raise value itself (on top of a call).
            is_all_in_raise = (player.money == total_additional_money_for_action)
            if not is_all_in_raise and amount < room.min_raise_amount:
                logger.warning(f"{player.name} RAISE too small. Raise amount: {amount}, MinRaise required: {room.min_raise_amount}")
                return False

            # Process the bet
            player.money -= total_additional_money_for_action
            player.current_bet += total_additional_money_for_action # current_bet becomes the new total for this round
            player.total_bet_this_hand += total_additional_money_for_action
            room.pot += total_additional_money_for_action

            # Update room's betting state
            new_bet_to_match = player.current_bet
            # The new minimum raise amount for OTHERS is the size of THIS player's raise amount (`amount`)
            # unless this raise was an "incomplete" all-in raise.
            if not is_all_in_raise or (is_all_in_raise and amount >= room.min_raise_amount):
                 room.min_raise_amount = amount # This raise sets new min_raise_amount if it's a "full" raise or a "full" all-in raise

            room.current_bet_to_match = new_bet_to_match

            if player.money == 0:
                player.status = PlayerStatus.ALL_IN
            return True

        if action == PlayerAction.ALL_IN:
            if player.money <= 0:
                logger.warning(f"{player.name} ALL_IN failed: No money to go all-in with.")
                return False # Already all-in or no money

            all_in_amount_this_action = player.money # They are betting all their REMAINING money

            # This all_in_amount_this_action is added to their current_bet for this round
            # and to their total_bet_this_hand.
            player.money = 0
            player.current_bet += all_in_amount_this_action
            player.total_bet_this_hand += all_in_amount_this_action
            room.pot += all_in_amount_this_action
            player.status = PlayerStatus.ALL_IN

            # If this all-in constitutes a raise (i.e., their new current_bet > room.current_bet_to_match before this action)
            if player.current_bet > room.current_bet_to_match:
                # The size of the raise part of this all-in
                raise_portion_of_all_in = player.current_bet - room.current_bet_to_match
                if raise_portion_of_all_in >= room.min_raise_amount:
                    # If this all-in is a "full" raise or more, it sets the new min_raise_amount for others
                    room.min_raise_amount = raise_portion_of_all_in
                # Else, it's an incomplete all-in raise, min_raise_amount for others doesn't change, they can only call or re-raise fully.
                room.current_bet_to_match = player.current_bet # This is the new amount to match
            # If all-in is just a call, current_bet_to_match and min_raise_amount don't change.
            return True

        if action == PlayerAction.SIT_OUT:
            if room.phase == GamePhase.WAITING or room.phase == GamePhase.GAME_OVER:
                player.status = PlayerStatus.SITTING_OUT
            else: # If in a hand, treat as fold for this hand, then sit out for next
                player.status = PlayerStatus.FOLDED
                # TODO: Add a flag player.will_sit_out_next_hand = True
            return True
        if action == PlayerAction.SIT_IN:
            if player.status == PlayerStatus.SITTING_OUT:
                player.status = PlayerStatus.ACTIVE
                # TODO: player.will_sit_out_next_hand = False
                return True
            return False
        return False

    def advance_game_flow(self, room_code: str):
        room = self.rooms.get(room_code)
        if not room:
            logger.error(f"advance_game_flow: Room {room_code} not found.")
            return

        logger.info(f"Room {room.code}: Advancing game flow. Current phase: {room.phase.value}, Current player: {room.current_player_id}")

        # Check for hand end by single player remaining
        active_players_still_in_hand = room.get_active_players_in_hand()
        if len(active_players_still_in_hand) <= 1:
            if room.phase not in [GamePhase.SHOWDOWN, GamePhase.GAME_OVER]:
                logger.info(f"Room {room.code}: Hand ending early. Active players in hand: {len(active_players_still_in_hand)}. Proceeding to end_hand.")
                # If only one player left, they win the pot. This is handled in end_hand.
                # Need to ensure any uncalled bets are returned if applicable, or pot awarded.
                # end_hand calculates side pots and awards them.
                self.end_hand(room_code) # This will handle awarding pot(s)
                return
            # If already in showdown or game over, let those processes complete.


        # Determine if betting round is complete
        # Betting is complete if:
        # 1. All active (not folded, not all-in) players have the same current_bet amount.
        # 2. AND that amount is >= room.current_bet_to_match.
        # 3. AND the action has made its way back to the player who made the last aggressive action (bet/raise),
        #    OR (for pre-flop) to the Big Blind if it was checked/called around to them.

        players_who_can_still_act = [
            p for p_id in room._player_order_for_hand
            if (p := room.players.get(p_id)) and p.status == PlayerStatus.ACTIVE and not p.is_all_in_for_hand() and p.money > 0
        ]

        if not players_who_can_still_act: # All remaining players are all-in or folded
            logger.info(f"Room {room.code}: No players can still act. Advancing phase (likely to showdown).")
            self.advance_phase(room_code)
            return

        all_bets_matched_this_round = True
        first_actor_this_betting_round = None # TODO: Track who opened betting or last raised

        # Simpler check for now: are all non-all-in, non-folded players' current_bets equal to current_bet_to_match?
        # AND has the action completed a full circle since the last bet/raise?
        # A common way: betting ends when all players have had a turn since the last aggressive action,
        # and all who haven't folded have an equal amount wagered for the round.

        # More robust check:
        action_is_closed = True
        num_active_non_all_in_players = 0
        last_aggressor_id = None # Player who last bet or raised

        # Find last aggressor based on actions_this_hand in current phase
        for p_id_ordered in reversed(room._player_order_for_hand): # Check recent actions
            p_ordered = room.players.get(p_id_ordered)
            if p_ordered and p_ordered.actions_this_hand:
                # Look for last bet/raise in the current game phase
                for act_hist in reversed(p_ordered.actions_this_hand):
                    if act_hist["phase"] == room.phase.value and act_hist["action"] in [PlayerAction.RAISE.value, PlayerAction.ALL_IN.value if act_hist["total_bet_this_round"] > room.current_bet_to_match else None]: # Check if all-in was a raise
                        # Check if BB's initial post is the "aggressor" if no raises yet pre-flop
                        if not (room.phase == GamePhase.PRE_FLOP and p_ordered.is_big_blind and act_hist["action"] == "big_blind" and room.current_bet_to_match == room.settings.big_blind):
                            last_aggressor_id = p_id_ordered
                            break
                if last_aggressor_id: break
        if not last_aggressor_id and room.phase == GamePhase.PRE_FLOP: # If no raise pre-flop, BB is effectively last aggressor IF action is on them
             bb_player = next((p for p in room.players.values() if p.is_big_blind), None)
             if bb_player: last_aggressor_id = bb_player.id


        for p_id_check in room._player_order_for_hand:
            p_check = room.players.get(p_id_check)
            if p_check and p_check.status == PlayerStatus.ACTIVE and not p_check.is_all_in_for_hand():
                num_active_non_all_in_players +=1
                # If player's current bet is less than what's needed to match, betting is not over
                if p_check.current_bet < room.current_bet_to_match:
                    action_is_closed = False
                    break
                # Pre-flop: Big Blind has option to raise if only called to them
                if room.phase == GamePhase.PRE_FLOP and \
                   p_check.is_big_blind and \
                   p_check.current_bet == room.settings.big_blind and \
                   room.current_bet_to_match == room.settings.big_blind and \
                   p_check.last_action is None: # BB hasn't acted yet on this "bet"
                    action_is_closed = False
                    break
                # General case: if the current player to act IS the last aggressor, and all others have matched/folded, round is over.
                # This is implicitly handled if we iterate and the next player to act is the one who made the current_bet_to_match.
                if p_check.id == last_aggressor_id and p_check.last_action in [PlayerAction.RAISE, PlayerAction.CALL, PlayerAction.CHECK, PlayerAction.ALL_IN]: # Aggressor has acted
                    pass # Condition met for this player, continue checking others. If all others match, round is over.


        if num_active_non_all_in_players == 0 and len(active_players_still_in_hand) > 1 : # All remaining are all-in
            logger.info(f"Room {room.code}: All remaining active players are all-in. Advancing phase.")
            self.advance_phase(room_code)
            return

        if action_is_closed:
            logger.info(f"Room {room.code}: Betting round complete (action_is_closed=True). Advancing phase from {room.phase.value}.")
            self.advance_phase(room_code)
            return

        # If betting not complete, find next player
        next_player_id_to_act = room.get_player_acting_next(room.current_player_id)

        if next_player_id_to_act:
            room.current_player_id = next_player_id_to_act
            room.last_action_timestamp = time.time() # Reset timer for the new player
            logger.info(f"Room {room.code}: Next player is {room.current_player_id}. Previous was {player_id if 'player_id' in locals() else 'N/A'}")
            if room.players[next_player_id_to_act].is_ai:
                asyncio.create_task(self.ai_perform_action(room_code, next_player_id_to_act))
        else: # No one can act, but betting wasn't considered closed. This might mean everyone folded.
            logger.info(f"Room {room.code}: No player found to act next, but action_is_closed was false. Likely all remaining players folded or are all-in. Advancing phase (showdown or hand end).")
            self.advance_phase(room_code) # This should lead to showdown or hand end if only one remains.
            return

    def advance_phase(self, room_code: str):
        room = self.rooms.get(room_code)
        if not room:
            logger.error(f"advance_phase: Room {room_code} not found.")
            return

        logger.info(f"Room {room.code}: Advancing phase from {room.phase.value}. Community cards: {[str(c) for c in room.community_cards]}")

        # Reset player's current_bet for the new betting round, but keep total_bet_this_hand
        for player in room.players.values():
            player.current_bet = 0
            player.last_action = None # Clear last action for the new round
            player.last_action_amount = 0

        room.current_bet_to_match = 0 # No bet to match at start of new round
        room.min_raise_amount = room.settings.big_blind # Reset min raise for new round

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
        elif current_phase == GamePhase.SHOWDOWN: # End of hand, prepare for next
            logger.info(f"Room {room.code}: Hand ended (was SHOWDOWN). Preparing next hand.")
            # Hand history and tournament state updates are done in end_hand
            asyncio.create_task(self.prepare_next_hand(room_code))
            return # Don't proceed further in this function
        else:
            logger.warning(f"Room {room.code}: Advance_phase called from unexpected phase: {current_phase}. No change.")
            return

        if next_phase:
            room.phase = next_phase
            logger.info(f"Room {room.code}: Advanced to phase {room.phase.value}. Community: {[str(c) for c in room.community_cards]}")

            if next_phase == GamePhase.SHOWDOWN:
                logger.info(f"Room {room.code}: Reached SHOWDOWN. Calling end_hand.")
                self.end_hand(room_code)
                return

            # Determine first player to act in post-flop rounds (or if all-in skip betting)
            # Post-flop, action starts with the first active player to the left of the dealer button.
            # _player_order_for_hand is SB, BB, UTG, ..., Dealer (for 3+ players)
            # For HU, _player_order_for_hand is [SB(Dealer), BB(Other)] pre-flop. Post-flop, BB(Other) is first.

            first_player_to_act_this_round_id = None
            # Check if any betting is even needed (e.g., all but one player is all-in)
            active_non_all_in_players = [
                p for p_id in room._player_order_for_hand
                if (p := room.players.get(p_id)) and p.status == PlayerStatus.ACTIVE and not p.is_all_in_for_hand() and p.money > 0
            ]

            if len(active_non_all_in_players) < 2 : # 0 or 1 player can bet
                logger.info(f"Room {room.code}: Less than 2 players can bet in {room.phase.value}. Fast-forwarding phase.")
                if room.phase != GamePhase.SHOWDOWN: # Avoid infinite loop if already at river
                    self.advance_phase(room_code) # Skip betting, go to next card or showdown
                return

            # If betting is needed, find the first actor
            if room._player_order_for_hand:
                if len(room._player_order_for_hand) == 2 and room.phase != GamePhase.PRE_FLOP: # HU Post-flop
                    # BB (non-dealer in HU) acts first post-flop. _player_order_for_hand is [SB/Dealer, BB]
                    bb_player_id_hu = room._player_order_for_hand[1]
                    sb_player_id_hu = room._player_order_for_hand[0]
                    bb_player = room.players.get(bb_player_id_hu)
                    sb_player = room.players.get(sb_player_id_hu)

                    if bb_player and bb_player.status == PlayerStatus.ACTIVE and not bb_player.is_all_in_for_hand():
                        first_player_to_act_this_round_id = bb_player_id_hu
                    elif sb_player and sb_player.status == PlayerStatus.ACTIVE and not sb_player.is_all_in_for_hand(): # If BB folded/all-in
                        first_player_to_act_this_round_id = sb_player_id_hu
                else: # 3+ players post-flop, or pre-flop (pre-flop first actor already set)
                      # Iterate in defined action order (SB, BB, UTG... Dealer)
                    for p_id_ordered in room._player_order_for_hand:
                        player = room.players.get(p_id_ordered)
                        if player and player.status == PlayerStatus.ACTIVE and not player.is_all_in_for_hand() and player.money > 0:
                            first_player_to_act_this_round_id = player.id
                            break

            room.current_player_id = first_player_to_act_this_round_id
            room.last_action_timestamp = time.time() # Reset timer for the new player

            if not room.current_player_id: # Should not happen if active_non_all_in_players >= 2
                logger.error(f"Room {room.code}: Could not determine first player to act in {room.phase.value} despite active players.")
                # Potentially advance again if stuck
                if room.phase != GamePhase.SHOWDOWN: self.advance_phase(room_code)
                return

            logger.info(f"Room {room.code}: First to act in {room.phase.value} is {room.current_player_id}")
            if room.players[room.current_player_id].is_ai:
                asyncio.create_task(self.ai_perform_action(room_code, room.current_player_id))
        else:
            logger.error(f"Room {room.code}: No next phase determined from {current_phase}. This should not happen.")


    def end_hand(self, room_code: str):
        room = self.rooms.get(room_code)
        if not room:
            logger.error(f"end_hand: Room {room_code} not found.")
            return

        # Ensure phase is showdown if not already (e.g. if everyone folded before river)
        if room.phase != GamePhase.SHOWDOWN:
            logger.info(f"Room {room.code}: Ending hand #{room.hand_number}. Phase was {room.phase.value}, setting to SHOWDOWN.")
            room.phase = GamePhase.SHOWDOWN
        else:
            logger.info(f"Room {room.code}: Ending hand #{room.hand_number}. Already in SHOWDOWN.")


        # Players who are eligible to win pots (not folded, not eliminated)
        # Side pot calculation should use total_bet_this_hand to determine eligibility for each pot
        room.calculate_side_pots() # This should correctly reflect who put money where

        players_in_showdown_for_eval = [
            p for p in room.get_players_eligible_for_pot() # Not folded, not eliminated
            if p.status != PlayerStatus.FOLDED and p.cards # Must have cards to be evaluated
        ]

        evaluated_hands: Dict[str, HandEvaluation] = {}
        if players_in_showdown_for_eval:
            logger.info(f"Room {room.code}: Evaluating hands for {len(players_in_showdown_for_eval)} players.")
            for player in players_in_showdown_for_eval:
                if player.cards: # Should always be true due to filter above
                    combined_cards = player.cards + room.community_cards
                    eval_result = self.evaluate_hand(combined_cards)
                    evaluated_hands[player.id] = eval_result
                    logger.info(f"Player {player.name} ({player.id}) hand: {[str(c) for c in player.cards]}, Community: {[str(c) for c in room.community_cards]}, Eval: {eval_result.description} (Rank: {eval_result.rank.value}, Value: {eval_result.value})")
        else:
            logger.info(f"Room {room.code}: No players eligible for hand evaluation in showdown (e.g., one player left).")

        all_winners_info_for_history: Dict[str, Dict] = {} # For hand history saving

        if not room.side_pots and room.pot > 0: # If calculate_side_pots didn't create any but there's a pot
            logger.warning(f"Room {room.code}: Main pot {room.pot} exists but no side_pots generated. Creating one fallback pot.")
            eligible_players_for_fallback_pot = {p.id for p in room.get_players_eligible_for_pot() if p.total_bet_this_hand > 0}
            if eligible_players_for_fallback_pot:
                room.side_pots.append(SidePot(amount=room.pot, eligible_players=eligible_players_for_fallback_pot))
            else: # e.g. everyone folded except one who didn't bet (blinds returned?) - complex
                logger.warning(f"Room {room.code}: Pot {room.pot} exists but no eligible players for fallback pot.")


        for i, pot_info in enumerate(room.side_pots):
            logger.info(f"Distributing Pot #{i+1} (Amount: {pot_info.amount}, Eligible IDs: {pot_info.eligible_players})")

            # Filter evaluated_hands to only those eligible for *this specific pot*
            eligible_evaluated_hands_for_this_pot = {
                pid: evaluated_hands[pid] for pid in pot_info.eligible_players if pid in evaluated_hands
            }

            if not eligible_evaluated_hands_for_this_pot:
                # This can happen if all eligible players for this pot folded, or only one remains who didn't need evaluation.
                # Or if a player was eligible but their hand couldn't be evaluated (e.g. no cards - shouldn't happen with filters)
                non_folded_eligibles_for_this_pot = [
                    p_id for p_id in pot_info.eligible_players
                    if (p := room.players.get(p_id)) and p.status != PlayerStatus.FOLDED
                ]
                if len(non_folded_eligibles_for_this_pot) == 1:
                    winner_id = non_folded_eligibles_for_this_pot[0]
                    winner_player = room.players.get(winner_id)
                    logger.info(f"Side Pot #{i+1} (Uncontested): Player {winner_player.name} ({winner_id}) wins ${pot_info.amount}.")
                    winner_player.money += pot_info.amount
                    pot_info.winner_ids = [winner_id]
                    pot_info.winning_hand_description = "Won by default (last remaining in pot)"

                    if winner_id not in all_winners_info_for_history:
                        all_winners_info_for_history[winner_id] = {"amount_won": 0, "hand_description": "Won by default"}
                    all_winners_info_for_history[winner_id]["amount_won"] += pot_info.amount
                    # No specific hand description needed if uncontested by evaluation
                elif len(non_folded_eligibles_for_this_pot) > 1:
                    logger.error(f"Side Pot #{i+1}: Multiple non-folded eligibles but no evaluated hands for them. Pot: {pot_info.amount}, Eligibles: {non_folded_eligibles_for_this_pot}. This is an anomaly.")
                else:
                    logger.warning(f"Side Pot #{i+1}: No non-folded eligible players for this pot {pot_info.amount}. This might be okay if all folded (pot awarded earlier or error in logic). Original eligibles: {pot_info.eligible_players}")
                continue # Move to next pot

            # Find best hand among those eligible for this pot
            best_hand_eval_for_pot = max(eligible_evaluated_hands_for_this_pot.values(), key=lambda h_eval: h_eval.value)
            current_pot_winner_ids = [
                pid for pid, hand_eval in eligible_evaluated_hands_for_this_pot.items()
                if hand_eval.value == best_hand_eval_for_pot.value # Compare by combined strength value
            ]

            pot_info.winner_ids = current_pot_winner_ids
            pot_info.winning_hand_description = best_hand_eval_for_pot.description

            if current_pot_winner_ids:
                winnings_per_winner = pot_info.amount // len(current_pot_winner_ids)
                remainder = pot_info.amount % len(current_pot_winner_ids) # For uneven splits

                for Ridx, winner_id in enumerate(current_pot_winner_ids):
                    player_to_award = room.players.get(winner_id)
                    if player_to_award:
                        amount_won_this_pot_slice = winnings_per_winner + (1 if Ridx < remainder else 0)
                        player_to_award.money += amount_won_this_pot_slice
                        logger.info(f"Side Pot #{i+1}: Player {player_to_award.name} ({winner_id}) wins ${amount_won_this_pot_slice} with {best_hand_eval_for_pot.description}")

                        if winner_id not in all_winners_info_for_history:
                            all_winners_info_for_history[winner_id] = {"amount_won": 0, "hand_description": best_hand_eval_for_pot.description}
                        all_winners_info_for_history[winner_id]["amount_won"] += amount_won_this_pot_slice
                    else:
                        logger.error(f"Side Pot #{i+1}: Winner player ID {winner_id} not found in room players!")
            else:
                logger.error(f"Side Pot #{i+1}: No winners determined for pot {pot_info.amount} among {eligible_evaluated_hands_for_this_pot.keys()}. This should not happen.")

        room.pot = 0 # All pot money should now be in side_pots or distributed

        # Update player stats for overall winners
        for p_id, win_info in all_winners_info_for_history.items():
            player = room.players.get(p_id)
            if player:
                player.stats.total_winnings += win_info["amount_won"]
                player.stats.hands_won += 1 # Increment once per hand won, even if multiple pots
                if win_info["amount_won"] > player.stats.biggest_pot:
                    player.stats.biggest_pot = win_info["amount_won"]
                if win_info["amount_won"] > self.global_stats['biggest_pot']:
                    self.global_stats['biggest_pot'] = win_info["amount_won"]
            else:
                logger.error(f"Player {p_id} won but not found in room for stats update.")

        # Increment hands_played for all players who were dealt into the hand and didn't sit out pre-deal
        for p_id in room._player_order_for_hand: # Assuming this list contains all dealt-in players
            player = room.players.get(p_id)
            if player and player.status != PlayerStatus.SITTING_OUT: # Should already be filtered by _player_order_for_hand logic
                player.stats.hands_played +=1


        self.save_hand_history(room, all_winners_info_for_history)

        if room.settings.game_mode == GameMode.TOURNAMENT:
            self.update_tournament_state(room) # Check for eliminations, blind increases

        # This will eventually call prepare_next_hand
        asyncio.create_task(self.prepare_next_hand(room_code))


    async def prepare_next_hand(self, room_code: str, delay: int = 7): # Delay for players to see results
        logger.info(f"Room {room_code}: Preparing for next hand in {delay} seconds.")
        await asyncio.sleep(delay)

        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"Room {room_code} not found during prepare_next_hand (likely closed).")
            return
        if room.paused: # If game got paused during the delay
            logger.info(f"Room {room_code}: Game is paused. Next hand prep deferred.")
            return


        room.community_cards = [] # Clear for UI
        # Side pots are already cleared by start_game/end_hand logic, but good to ensure
        room.side_pots = []

        # Update player statuses (e.g., if someone was folded for leaving, they are now fully out or handled by leave_room)
        # Check for eliminations in cash games (money = 0)
        if room.settings.game_mode == GameMode.CASH_GAME:
            for p in list(room.players.values()): # Iterate copy in case of modification
                if not p.is_ai and p.money <= 0 and p.status != PlayerStatus.ELIMINATED:
                    logger.info(f"Cash game: Player {p.name} has no money, setting to ELIMINATED (can rejoin/rebuy).")
                    p.status = PlayerStatus.ELIMINATED # In cash game, can rejoin/rebuy

        active_players_for_next_game = [
            p for p in room.players.values()
            if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED] and p.money > 0
        ]

        if room.settings.game_mode == GameMode.TOURNAMENT and len(active_players_for_next_game) <= 1:
            room.phase = GamePhase.GAME_OVER
            logger.info(f"Room {room_code}: Tournament ended. Winner(s) determined or only one player left.")
            # Broadcast final tournament state if needed
            # Game loop will send this state
            if active_players_for_next_game:
                winner = active_players_for_next_game[0]
                winner.tournament_rank = 1
                logger.info(f"Tournament Winner: {winner.name}")
            return

        room.phase = GamePhase.WAITING # Set to waiting before attempting to start

        if len(active_players_for_next_game) >= room.settings.min_players:
            logger.info(f"Room {room.code}: Automatically starting next hand. Eligible players: {len(active_players_for_next_game)}")
            self.start_game(room_code)
        else:
            logger.info(f"Room {room_code}: Waiting for more players. Need {room.settings.min_players}, have {len(active_players_for_next_game)} eligible.")
            # Game loop will send WAITING state

    def evaluate_hand(self, cards: List[Card]) -> HandEvaluation:
        # Create a canonical cache key: frozenset of sorted (rank, suit) tuples
        # Card ranks need to be consistently represented, e.g., '10' vs 'T'
        # Assuming Card.value() gives numerical rank and Card.suit_value() gives numerical suit
        # For simplicity, using (rank_str, suit_str)
        canonical_card_tuples = tuple(sorted([(c.rank, c.suit) for c in cards]))
        cache_key = str(canonical_card_tuples) # Simple string representation for dict key

        if cache_key in self.hand_evaluation_cache:
            return self.hand_evaluation_cache[cache_key]

        eval_result = self.full_hand_evaluation(cards)

        if len(self.hand_evaluation_cache) < HAND_EVALUATION_CACHE_SIZE:
            self.hand_evaluation_cache[cache_key] = eval_result
        return eval_result

    def full_hand_evaluation(self, all_cards: List[Card]) -> HandEvaluation:
        from itertools import combinations # Keep import local if only used here

        if len(all_cards) < 5:
            # This should ideally not happen if called with player cards + community cards
            logger.warning(f"Attempted to evaluate hand with < 5 cards: {len(all_cards)}")
            return HandEvaluation(HandRank.HIGH_CARD, 0, [], "Invalid hand (<5 cards)")

        best_eval_for_player = HandEvaluation(HandRank.HIGH_CARD, 0, [], "High Card") # Default worst hand

        for five_card_combo_list in combinations(all_cards, 5):
            current_combo_eval_rank, current_combo_eval_value, current_kickers, sorted_combo_cards = self.evaluate_5_card_hand(list(five_card_combo_list))

            # Compare with the player's best hand found so far for these `all_cards`
            if current_combo_eval_rank > best_eval_for_player.rank or \
               (current_combo_eval_rank == best_eval_for_player.rank and current_combo_eval_value > best_eval_for_player.value):
                best_eval_for_player.rank = current_combo_eval_rank
                best_eval_for_player.value = current_combo_eval_value # This is the primary comparison metric
                best_eval_for_player.cards_used = sorted_combo_cards
                best_eval_for_player.kickers = current_kickers # Store numerical kickers
                best_eval_for_player.description = self.get_hand_description(current_combo_eval_rank, current_kickers)

        return best_eval_for_player


    def evaluate_5_card_hand(self, five_cards: List[Card]) -> Tuple[HandRank, int, List[int], List[Card]]:
        # Card.value() returns int (A=14), Card.suit returns string
        # Sort cards by rank, high to low. Aces are high (14) for now.
        # Ace_low (A=1) is handled specifically for A-5 straights.
        sorted_cards = sorted(five_cards, key=lambda c: c.value(), reverse=True)
        values = [c.value() for c in sorted_cards] # Numerical values [14, 13, ..., 2]
        suits = [c.suit for c in sorted_cards]

        is_flush = len(set(suits)) == 1

        # Straight check (Ace can be high or low)
        is_straight = False
        unique_values_desc = sorted(list(set(values)), reverse=True) # [14, 5, 4, 3, 2] for wheel
        if len(unique_values_desc) == 5:
            # Normal straight: 10, 9, 8, 7, 6 -> values[0]-values[4] == 4
            if unique_values_desc[0] - unique_values_desc[4] == 4:
                is_straight = True
                straight_high_card_value = unique_values_desc[0] # Primary kicker for straight
            # Ace-low straight (Wheel): A, 5, 4, 3, 2 -> values are [14,5,4,3,2] -> unique_values_desc is [14,5,4,3,2]
            elif unique_values_desc == [14, 5, 4, 3, 2]:
                is_straight = True
                straight_high_card_value = 5 # Ace plays as 1, so 5 is high card for A-5 straight value
                # For actual kickers list, A is still part of it, but represented as 5 for ranking value.
                # We'll use the transformed values for kickers if it's a wheel.
                values = [5,4,3,2,1] # Transform A to 1 for wheel ranking strength
            else: straight_high_card_value = 0
        else: straight_high_card_value = 0


        # Counts of each rank
        value_counts = Counter(values) # Original values (Ace=14) for pairs, trips etc.
        # Tuples of (count, value), sorted by count desc, then value desc
        # e.g., for KKKQQ: [(3,13), (2,12)]
        # e.g., for KKQJJ: [(2,13), (2,11), (1,12)]
        # e.g., for KKKQJ: [(3,13), (1,12), (1,11)]
        sorted_value_counts = sorted(value_counts.items(), key=lambda item: (item[1], item[0]), reverse=True)

        rank = HandRank.HIGH_CARD
        kickers_for_strength = values # Default kickers are just card values, high to low

        if is_straight and is_flush:
            if straight_high_card_value == 14: # TJQKA (Royal Flush values are standard)
                 rank = HandRank.ROYAL_FLUSH
                 kickers_for_strength = values # [14,13,12,11,10]
            else: # Other straight flushes
                 rank = HandRank.STRAIGHT_FLUSH
                 # If wheel straight flush, values were already transformed to [5,4,3,2,1]
                 kickers_for_strength = values if straight_high_card_value == 5 else [straight_high_card_value] + [v for v in unique_values_desc[1:]] # General straight flush
                 if straight_high_card_value == 5: kickers_for_strength = [5,4,3,2,1] # Wheel specific

        elif sorted_value_counts[0][1] == 4: # Four of a Kind
            rank = HandRank.FOUR_OF_A_KIND
            quad_value = sorted_value_counts[0][0]
            kicker_val = sorted_value_counts[1][0] # The 5th card
            kickers_for_strength = [quad_value, kicker_val]

        elif sorted_value_counts[0][1] == 3 and sorted_value_counts[1][1] == 2: # Full House
            rank = HandRank.FULL_HOUSE
            trips_value = sorted_value_counts[0][0]
            pair_value = sorted_value_counts[1][0]
            kickers_for_strength = [trips_value, pair_value]

        elif is_flush:
            rank = HandRank.FLUSH
            kickers_for_strength = values # All 5 cards, high to low, determine flush strength

        elif is_straight:
            rank = HandRank.STRAIGHT
            # values was already transformed for wheel if it's an A-5 straight
            kickers_for_strength = values if straight_high_card_value == 5 else [straight_high_card_value] + [v for v in unique_values_desc[1:]]
            if straight_high_card_value == 5: kickers_for_strength = [5,4,3,2,1] # Wheel specific

        elif sorted_value_counts[0][1] == 3: # Three of a Kind
            rank = HandRank.THREE_OF_A_KIND
            trips_value = sorted_value_counts[0][0]
            kicker1 = sorted_value_counts[1][0]
            kicker2 = sorted_value_counts[2][0]
            kickers_for_strength = [trips_value, kicker1, kicker2]

        elif sorted_value_counts[0][1] == 2 and sorted_value_counts[1][1] == 2: # Two Pair
            rank = HandRank.TWO_PAIR
            high_pair_value = sorted_value_counts[0][0]
            low_pair_value = sorted_value_counts[1][0]
            kicker_val = sorted_value_counts[2][0]
            kickers_for_strength = [high_pair_value, low_pair_value, kicker_val]

        elif sorted_value_counts[0][1] == 2: # One Pair
            rank = HandRank.PAIR
            pair_value = sorted_value_counts[0][0]
            kicker1 = sorted_value_counts[1][0]
            kicker2 = sorted_value_counts[2][0]
            kicker3 = sorted_value_counts[3][0]
            kickers_for_strength = [pair_value, kicker1, kicker2, kicker3]

        # Default is HIGH_CARD, kickers_for_strength already set to `values`

        # Calculate a single integer value for hand strength comparison
        hand_strength_value = self._calculate_hand_strength_value(rank, kickers_for_strength)
        return rank, hand_strength_value, kickers_for_strength, sorted_cards


    def _calculate_hand_strength_value(self, rank: HandRank, card_values_for_strength: List[int]) -> int:
        # Ensure card_values_for_strength are numerically sortable (e.g., A=14, K=13 ... 2=2, or for wheel A=1 but passed as 5 for straight high)
        # Pad with zeros if fewer than 5 kickers (e.g. for quads, full house)
        padded_kickers = (card_values_for_strength + [0,0,0,0,0])[:5]

        # Higher rank is better. For same rank, higher kicker values are better.
        # Rank is most significant, then primary kicker, then secondary, etc.
        # Max card value is 14 (Ace). Use 2 hex digits (or base 15/16) per kicker to avoid collision.
        # Example: Rank * (15^5) + K1*(15^4) + K2*(15^3) + K3*(15^2) + K4*(15^1) + K5*(15^0)
        value = int(rank) * (15**5) # Max kicker value is 14, so base 15 is safe.
        multiplier = 15**4
        for val in padded_kickers:
            value += val * multiplier
            if multiplier > 1: # Avoid dividing by zero or going negative
                multiplier //= 15
            elif multiplier == 1: # last kicker done
                break
        return value

    def get_hand_description(self, rank: HandRank, kicker_values: List[int]) -> str:
        # Kicker_values are numerical (A=14, or A=1 for wheel in strength calc but desc might show Ace)
        def rank_to_str(v):
            if v == 14: return "Ace"
            if v == 13: return "King"
            if v == 12: return "Queen"
            if v == 11: return "Jack"
            if v == 1: return "Ace (low)" # For wheel description if needed
            return str(v)

        desc_kickers_str = [rank_to_str(k) for k in kicker_values]

        if rank == HandRank.ROYAL_FLUSH: return "Royal Flush"
        if rank == HandRank.STRAIGHT_FLUSH:
            # kicker_values for wheel straight flush might be [5,4,3,2,1]
            # If first kicker is 5 and it's a straight flush, it's Ace-5.
            high_card_name = "Ace" if kicker_values[0] == 5 and kicker_values == [5,4,3,2,1] else desc_kickers_str[0]
            return f"Straight Flush, {high_card_name} high"
        if rank == HandRank.FOUR_OF_A_KIND: return f"Four of a Kind, {desc_kickers_str[0]}s, {desc_kickers_str[1]} kicker"
        if rank == HandRank.FULL_HOUSE: return f"Full House, {desc_kickers_str[0]}s full of {desc_kickers_str[1]}s"
        if rank == HandRank.FLUSH: return f"Flush, {desc_kickers_str[0]} high ({', '.join(desc_kickers_str[1:])} kickers)"
        if rank == HandRank.STRAIGHT:
            high_card_name = "Ace" if kicker_values[0] == 5 and kicker_values == [5,4,3,2,1] else desc_kickers_str[0]
            return f"Straight, {high_card_name} high"
        if rank == HandRank.THREE_OF_A_KIND: return f"Three of a Kind, {desc_kickers_str[0]}s ({desc_kickers_str[1]}, {desc_kickers_str[2]} kickers)"
        if rank == HandRank.TWO_PAIR: return f"Two Pair, {desc_kickers_str[0]}s and {desc_kickers_str[1]}s ({desc_kickers_str[2]} kicker)"
        if rank == HandRank.PAIR: return f"Pair of {desc_kickers_str[0]}s ({', '.join(desc_kickers_str[1:4])} kickers)"
        if rank == HandRank.HIGH_CARD: return f"High Card {desc_kickers_str[0]} ({', '.join(desc_kickers_str[1:])} kickers)"
        return rank.name.replace('_', ' ').title()


    def save_hand_history(self, room: Room, winners_info: Dict[str, Dict]):
        # `winners_info` example: { "player_id1": {"amount_won": 1000, "hand_description": "Royal Flush"}, ... }
        if not room: return
        logger.info(f"Saving hand history for room {room.code}, hand #{room.hand_number}")
        hand_data = {
            'hand_number': room.hand_number,
            'timestamp': datetime.now().isoformat(),
            'players': [],
            'community_cards': [{'suit': c.suit, 'rank': c.rank, "id": c.id} for c in room.community_cards],
            'total_pot_distributed': sum(sp.amount for sp in room.side_pots if sp.amount > 0), # Sum of actual distributed money
            'side_pots_details': [
                {"amount": sp.amount, "eligible_players": list(sp.eligible_players),
                 "winner_ids": sp.winner_ids, "winning_hand_description": sp.winning_hand_description}
                for sp in room.side_pots if sp.amount > 0 # Only include pots that had money
            ],
            'winners_summary': winners_info # Overall summary of who won what in the hand
        }

        for p_id, player_obj in room.players.items():
            # Calculate initial money for this hand before winnings/losses
            # money_at_hand_start = player_obj.money (current)
            #                        - (amount won by this player this hand)
            #                        + (total bet by this player this hand)
            amount_won_this_hand = winners_info.get(p_id, {}).get("amount_won", 0)
            initial_money_for_hand = player_obj.money - amount_won_this_hand + player_obj.total_bet_this_hand

            player_detail = {
                'id': player_obj.id,
                'name': player_obj.name,
                'initial_money': initial_money_for_hand,
                'final_money': player_obj.money,
                'cards': [{'suit': c.suit, 'rank': c.rank, "id": c.id} for c in player_obj.cards] if player_obj.cards else [],
                'actions': player_obj.actions_this_hand, # List of dicts from player obj
                'total_bet_this_hand': player_obj.total_bet_this_hand,
                'status_at_end_of_hand': player_obj.status.value # Status after hand resolved
            }
            # Add win specific info directly to player detail too if they won
            if p_id in winners_info:
                player_detail['amount_won_this_hand'] = winners_info[p_id]["amount_won"]
                player_detail['winning_hand_description_if_any'] = winners_info[p_id]["hand_description"]
            hand_data['players'].append(player_detail)

        room.hand_history.append(hand_data)
        if len(room.hand_history) > 50: # Keep last 50 hands
            room.hand_history = room.hand_history[-50:]
        logger.info(f"Room {room.code}: Hand #{room.hand_number} history saved. Total entries: {len(room.hand_history)}")

    def update_tournament_state(self, room: Room):
        if room.settings.game_mode != GameMode.TOURNAMENT:
            return
        logger.info(f"Updating tournament state for room {room.code}")
        eliminated_this_hand = []
        current_active_players = [p for p in room.players.values() if p.status != PlayerStatus.ELIMINATED]
        num_players_at_start_of_hand = len(current_active_players) # Approx, better to use total registered if available

        for p_id, player in room.players.items():
            if player.money <= 0 and player.status != PlayerStatus.ELIMINATED:
                player.status = PlayerStatus.ELIMINATED
                # Tournament rank is based on order of elimination
                # Total players in tournament initially matters. For simplicity, use current total players.
                # A more robust ranking needs to count players at tournament start.
                num_already_eliminated = sum(1 for p_check in room.players.values() if p_check.tournament_rank > 0)
                player.tournament_rank = len(room.players) - num_already_eliminated # Higher number = earlier elimination
                eliminated_this_hand.append(player.name)
        if eliminated_this_hand:
            logger.info(f"Tournament {room.code}: Players eliminated this hand: {', '.join(eliminated_this_hand)}")

        # Blind increase logic (example, can be more complex from tournament_structure)
        if datetime.now() >= room.tournament_next_blind_increase:
            room.tournament_level += 1
            # Example: blinds double every level (highly aggressive for testing)
            new_sb = room.settings.small_blind * 2
            new_bb = room.settings.big_blind * 2
            new_ante = room.settings.ante
            if room.settings.tournament_structure and "levels" in room.settings.tournament_structure:
                levels = room.settings.tournament_structure["levels"]
                if room.tournament_level -1 < len(levels):
                    level_data = levels[room.tournament_level -1]
                    new_sb = level_data.get("sb", new_sb)
                    new_bb = level_data.get("bb", new_bb)
                    new_ante = level_data.get("ante", new_ante if new_ante > 0 else 0) # Ante might be 0
                    increase_interval_min = level_data.get("duration_minutes", TOURNAMENT_BLIND_INCREASE_INTERVAL // 60)
                    room.tournament_next_blind_increase = datetime.now() + timedelta(minutes=increase_interval_min)
                else: # Out of predefined levels, keep increasing by factor
                    room.tournament_next_blind_increase = datetime.now() + timedelta(seconds=TOURNAMENT_BLIND_INCREASE_INTERVAL)
            else: # Default increase if no structure
                 room.tournament_next_blind_increase = datetime.now() + timedelta(seconds=TOURNAMENT_BLIND_INCREASE_INTERVAL)


            room.settings.small_blind = new_sb
            room.settings.big_blind = new_bb
            room.settings.ante = new_ante

            logger.info(f"Tournament {room.code}: Level up to {room.tournament_level}. Blinds: {room.settings.small_blind}/{room.settings.big_blind}, Ante: {room.settings.ante}. Next increase at {room.tournament_next_blind_increase.strftime('%Y-%m-%d %H:%M:%S')}")

            # Tournament Break Logic (e.g., every N levels)
            if room.tournament_level % 5 == 0: # Break every 5 levels
                room.phase = GamePhase.TOURNAMENT_BREAK
                room.paused = True
                # Duration of break, e.g. 5 minutes (300 seconds)
                break_duration_seconds = 300 # Can be configurable
                room.pause_reason = f"Tournament Break (Level {room.tournament_level}) - Resumes in {break_duration_seconds // 60} min"
                logger.info(f"Tournament {room.code}: Starting break for {break_duration_seconds}s. Reason: {room.pause_reason}")
                asyncio.create_task(self.resume_tournament_after_break(room.code, break_duration_seconds))


    async def resume_tournament_after_break(self, room_code: str, break_duration_seconds: int):
        await asyncio.sleep(break_duration_seconds)
        room = self.rooms.get(room_code)
        if room and room.paused and room.phase == GamePhase.TOURNAMENT_BREAK:
            room.paused = False
            room.pause_reason = ""
            room.phase = GamePhase.WAITING # Will trigger start_game if conditions met
            logger.info(f"Tournament {room.code}: Break ended. Resuming game.")
            # Game loop will pick up and broadcast new state, potentially start next hand via prepare_next_hand logic
            # (if prepare_next_hand was deferred due to pause) or by WAITING state check.
            # Explicitly call prepare_next_hand if game was mid-hand and should auto-resume.
            # For now, setting to WAITING is safer and relies on game loop.
        else:
            logger.info(f"Tournament {room_code}: Resume conditions not met (room gone, not paused, or not in break phase).")


    def get_game_state(self, room_code: str, for_player_id: str) -> dict:
        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"get_game_state called for non-existent room {room_code}")
            return {"error": "Room not found"}

        is_player_actually_in_game = for_player_id in room.players and not room.players[for_player_id].is_ai
        is_spectator = for_player_id in room.spectators

        current_player_obj = room.players.get(room.current_player_id) if room.current_player_id else None

        players_data = {}
        for p_id, p_obj in room.players.items():
            player_data = {
                "id": p_obj.id, "name": p_obj.name, "money": p_obj.money,
                "current_bet": p_obj.current_bet, "total_bet_this_hand": p_obj.total_bet_this_hand,
                "status": p_obj.status.value,
                "last_action": p_obj.last_action.value if p_obj.last_action else None,
                "last_action_amount": p_obj.last_action_amount,
                "avatar": p_obj.avatar, "color": p_obj.color,
                "is_dealer": p_obj.is_dealer, "is_small_blind": p_obj.is_small_blind, "is_big_blind": p_obj.is_big_blind,
                "time_bank": p_obj.time_bank,
                "is_current_player": current_player_obj and current_player_obj.id == p_id,
                "tournament_rank": p_obj.tournament_rank,
                "is_ai": p_obj.is_ai,
                "stats": asdict(p_obj.stats) # Send player stats
            }

            # Card visibility logic
            show_cards_to_this_client = False
            if p_id == for_player_id: # Always show own cards
                show_cards_to_this_client = True
            elif room.phase == GamePhase.SHOWDOWN and p_obj.status != PlayerStatus.FOLDED and p_obj.cards:
                 # Show non-folded hands at showdown to everyone (players and spectators)
                show_cards_to_this_client = True
            # Add more conditions if needed (e.g. specific spectator settings)

            if show_cards_to_this_client and p_obj.cards:
                player_data["cards"] = [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in p_obj.cards]
            elif p_obj.cards: # Cards exist but shouldn't be shown to this client
                player_data["cards"] = [{"suit": "back", "rank": "back", "id": f"back_{i}_{p_id}"} for i in range(len(p_obj.cards))]
            else: # No cards
                player_data["cards"] = []
            players_data[p_id] = player_data

        # Time left for current player's action
        time_left_for_action = 0
        if current_player_obj and room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER, GamePhase.TOURNAMENT_BREAK] and not room.paused:
            time_left_for_action = max(0, room.settings.auto_fold_timeout - (time.time() - room.last_action_timestamp))


        game_state = {
            "room_code": room.code, "room_name": room.name, "phase": room.phase.value,
            "pot": room.pot, # This is the total accumulated before side pot calc for display consistency
            "current_bet_to_match": room.current_bet_to_match,
            "min_raise_amount": room.min_raise_amount,
            "current_player_id": room.current_player_id,
            "dealer_player_id": room.dealer_player_id,
            "players": players_data,
            "community_cards": [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in room.community_cards],
            "chat_messages": room.chat_messages[-30:], # Send recent N messages
            "is_player_in_game": is_player_actually_in_game, # If the requesting client is a player in this room
            "is_spectator": is_spectator,
            "spectator_count": len(room.spectators),
            "hand_number": room.hand_number,
            "settings": { # Subset of room settings relevant to client
                "small_blind": room.settings.small_blind, "big_blind": room.settings.big_blind,
                "ante": room.settings.ante, "max_players": room.settings.max_players, # Max human players
                "game_mode": room.settings.game_mode.value,
                "auto_fold_timeout": room.settings.auto_fold_timeout,
                "ai_players": room.settings.ai_players, # Number of AIs configured
                "min_players": room.settings.min_players,
            },
            "tournament_info": {
                "level": room.tournament_level,
                "next_blind_increase_time": room.tournament_next_blind_increase.isoformat()
            } if room.settings.game_mode == GameMode.TOURNAMENT else None,
            "side_pots": [ # Simplified for client display
                {"amount": sp.amount, "eligible_players_count": len(sp.eligible_players),
                 "winner_ids": sp.winner_ids, "winning_hand": sp.winning_hand_description}
                for sp in room.side_pots
            ],
            "paused": room.paused, "pause_reason": room.pause_reason,
            "time_left_for_action": time_left_for_action,
            "can_act": (is_player_actually_in_game and current_player_obj and current_player_obj.id == for_player_id and
                        room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER, GamePhase.TOURNAMENT_BREAK] and
                        not room.paused),
            "available_actions": self.get_available_actions(room, for_player_id) if is_player_actually_in_game else []
        }
        return game_state

    def get_available_actions(self, room: Room, player_id: str, force_check: bool = False) -> List[Dict]:
        player = room.players.get(player_id)
        if not player: return []
        if not force_check and (not player.can_act() or room.current_player_id != player_id or room.paused):
            return []

        actions = [{"action": PlayerAction.FOLD.value, "label": "Fold"}]
        amount_to_call = room.current_bet_to_match - player.current_bet

        if amount_to_call <= 0: # Can check if no bet to call, or already called/bet more
            actions.append({"action": PlayerAction.CHECK.value, "label": "Check"})
        else: # Must call or fold or raise
            # Amount to call is capped by player's remaining money
            actual_call_amount = min(amount_to_call, player.money)
            actions.append({
                "action": PlayerAction.CALL.value,
                "label": f"Call ${actual_call_amount}",
                "amount": actual_call_amount
            })

        # Raise action conditions
        # Player must have money *after* making a call to be able to raise further.
        money_after_potential_call = player.money - (actual_call_amount if amount_to_call > 0 else 0)

        if money_after_potential_call > 0:
            # Min raise amount (on top of call) is room.min_raise_amount
            # Max raise amount (on top of call) is their remaining stack after calling
            min_raise_on_top = room.min_raise_amount
            max_raise_on_top = money_after_potential_call

            if max_raise_on_top >= min_raise_on_top : # Only possible to raise if they can meet min_raise
                actions.append({
                    "action": PlayerAction.RAISE.value,
                    "label": "Raise",
                    "min_amount": min_raise_on_top, # This is the amount to add ON TOP of call
                    "max_amount": max_raise_on_top  # Max they can add ON TOP of call
                })

        # All-in is always an option if they have money (even if it's just to call all-in)
        if player.money > 0:
            actions.append({
                "action": PlayerAction.ALL_IN.value,
                "label": f"All-In ${player.money}",
                "amount": player.money # The total amount they'd be putting in if they chose all-in FROM THEIR STACK
            })
        return actions

    def add_chat_message(self, room_code: str, player_id: str, message_text: str):
        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"Chat message for non-existent room {room_code}")
            return

        player = room.players.get(player_id) # Player might be None if it's a spectator by ID
        player_name = player.name if player else f"Spectator_{player_id[:4]}"
        player_color = player.color if player else "#cccccc" # Default color for spectators

        # Basic message sanitization (more can be added)
        cleaned_message = message_text.strip()
        if not cleaned_message: return # Ignore empty messages

        chat_msg = {
            "player_id": player_id,
            "player_name": player_name,
            "player_color": player_color,
            "message": cleaned_message[:200], # Max length
            "timestamp": time.time(), # Unix timestamp
            "formatted_time": datetime.now().strftime("%H:%M:%S") # Human-readable
        }
        room.chat_messages.append(chat_msg)
        if len(room.chat_messages) > MAX_CHAT_MESSAGES:
            room.chat_messages = room.chat_messages[-MAX_CHAT_MESSAGES:] # Keep last N
        logger.info(f"Chat in {room_code} by {player_name}: {cleaned_message}")
        room.update_activity()

    def check_rate_limit(self, client_id: str, type: str = "message") -> bool:
        limit_dict = self.rate_limits if type == "message" else self.action_rate_limits
        max_per_second = RATE_LIMIT_MESSAGES_PER_SECOND if type == "message" else RATE_LIMIT_ACTIONS_PER_SECOND

        current_time = time.time()
        # Clean out old timestamps
        limit_dict[client_id] = [t for t in limit_dict[client_id] if current_time - t <= 1.0]

        if len(limit_dict[client_id]) < max_per_second:
            limit_dict[client_id].append(current_time)
            return True
        else:
            logger.warning(f"Rate limit exceeded for {client_id} (type: {type}). Count: {len(limit_dict[client_id])}")
            return False


# Global game instance
game = AdvancedPokerGame()

# WebSocket message models (Pydantic)
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
    logger.info("Game loop started.")
    while game.running:
        loop_start_time = time.perf_counter()
        try:
            current_time_for_actions = time.time() # Consistent time for this loop iteration
            # Auto-fold logic
            for room_code, room in list(game.rooms.items()): # Iterate copy in case room is deleted
                if room.phase not in [GamePhase.WAITING, GamePhase.SHOWDOWN, GamePhase.GAME_OVER, GamePhase.TOURNAMENT_BREAK] and \
                   not room.paused and room.current_player_id:
                    current_player = room.players.get(room.current_player_id)
                    if current_player and not current_player.is_ai: # Only auto-fold human players
                        if current_time_for_actions - room.last_action_timestamp > room.settings.auto_fold_timeout:
                            logger.info(f"Auto-folding player {current_player.name} ({current_player.id}) in room {room_code} due to timeout.")
                            game.player_action(room_code, current_player.id, PlayerAction.FOLD)
                            # player_action will call advance_game_flow, which will trigger new state broadcast

            # Broadcasting game state
            for room_code, room in list(game.rooms.items()):
                user_ids_in_room_or_spectating = set()
                for p_id, player_obj in room.players.items():
                    if not player_obj.is_ai and player_obj.connection_id: # Active human players
                        user_ids_in_room_or_spectating.add(player_obj.connection_id)
                user_ids_in_room_or_spectating.update(room.spectators) # Add spectators

                if not user_ids_in_room_or_spectating: continue # No one to broadcast to

                connections_to_broadcast_to: List[Tuple[str, WebSocket]] = []
                for user_id in list(user_ids_in_room_or_spectating): # Iterate copy for safe removal
                    ws_conn = game.connections.get(user_id)
                    if ws_conn:
                        connections_to_broadcast_to.append((user_id, ws_conn))
                    else:
                        logger.warning(f"User {user_id} listed in room {room_code} (player/spectator) but no WebSocket connection found. Cleaning up.")
                        game.leave_room(user_id, force=True) # Attempt to clean up stale association

                if connections_to_broadcast_to:
                    broadcast_tasks = []
                    for user_id, ws_conn in connections_to_broadcast_to:
                        try:
                            game_state_for_user = game.get_game_state(room_code, user_id)
                            if "error" not in game_state_for_user: # Basic check if state is valid
                                broadcast_tasks.append(
                                    ws_conn.send_json({"type": "game_state", "data": game_state_for_user})
                                )
                            else:
                                logger.error(f"Error generating game state for {user_id} in {room_code}: {game_state_for_user.get('error')}")
                        except Exception as e:
                            logger.error(f"Error preparing game_state for user {user_id} in room {room_code}: {e}", exc_info=True)
                            # Don't add to broadcast_tasks if preparation failed

                    if broadcast_tasks:
                        results = await asyncio.gather(*broadcast_tasks, return_exceptions=True)
                        for i, result in enumerate(results):
                            if isinstance(result, Exception):
                                failed_user_id, _ = connections_to_broadcast_to[i] # Get user_id for failed task
                                logger.error(f"Failed to broadcast to WebSocket for user {failed_user_id}: {result}")
                                # Handle broken connection: remove from game.connections and trigger leave_room
                                if failed_user_id in game.connections:
                                    del game.connections[failed_user_id]
                                game.leave_room(failed_user_id, force=True)


            # Sleep to maintain game update rate
            elapsed_time = time.perf_counter() - loop_start_time
            sleep_duration = max(0, (1.0 / GAME_UPDATE_RATE) - elapsed_time)
            await asyncio.sleep(sleep_duration)

        except Exception as e:
            logger.exception(f"CRITICAL ERROR in game_loop: {e}")
            await asyncio.sleep(1.0) # Prevent rapid error loops

async def handle_websocket_message(websocket: WebSocket, player_id: str, message: WSMessage):
    action = message.action
    payload_dict = message.payload
    logger.info(f"Handling WebSocket message from {player_id}: Action: {action}, Payload: {payload_dict}")

    try:
        if action == "create_room":
            try:
                create_payload = CreateRoomPayload(**payload_dict)
            except ValidationError as e:
                logger.warning(f"Invalid create_room payload from {player_id}: {e.errors()}")
                await websocket.send_json({"type": "error", "message": f"Invalid create room data: {e.errors()}"})
                return

            game_settings = GameSettings(
                small_blind=create_payload.small_blind, big_blind=create_payload.big_blind,
                max_players=min(create_payload.max_players, MAX_PLAYERS_PER_ROOM), # Ensure not over global max
                game_mode=GameMode(create_payload.game_mode), buy_in=create_payload.buy_in,
                password=create_payload.password if create_payload.password else None,
                ai_players=min(create_payload.ai_players, MAX_PLAYERS_PER_ROOM -1) # AI count cannot exceed total minus 1 human
            )
            room_code = game.create_room(player_id, game_settings, create_payload.room_name)
            if not room_code:
                await websocket.send_json({"type": "error", "message": "Failed to create room (server limit or error)."})
                return

            # Creator automatically joins the room
            if game.join_room(room_code, player_id, create_payload.player_name):
                await websocket.send_json({"type": "room_created", "data": {"room_code": room_code, "room_name": game.rooms[room_code].name}})
            else: # Should not happen if create_room succeeded and join logic is sound
                await websocket.send_json({"type": "error", "message": "Failed to join newly created room (unexpected error)."})


        elif action == "join_room":
            if player_id in game.player_rooms:
                await websocket.send_json({"type": "error", "message": "You are already in a room."})
                return
            room_code = payload_dict.get("room_code")
            player_name = payload_dict.get("player_name", "Player") # Default name if not provided
            password = payload_dict.get("password")

            if not room_code or not isinstance(room_code, str):
                 await websocket.send_json({"type": "error", "message": "Invalid room code provided."}); return

            if game.join_room(room_code, player_id, player_name, password):
                await websocket.send_json({"type": "room_joined", "data": {"room_code": room_code}})
            else:
                await websocket.send_json({"type": "error", "message": "Failed to join room (invalid code, password, full, or other issue)."})

        elif action == "spectate_room":
            room_code = payload_dict.get("room_code")
            if not room_code or not isinstance(room_code, str):
                 await websocket.send_json({"type": "error", "message": "Invalid room code for spectate."}); return
            room = game.rooms.get(room_code)
            if room:
                if player_id in room.players and not room.players[player_id].is_ai:
                     await websocket.send_json({"type": "error", "message": "You are already a player in this room. Leave first to spectate."}); return
                room.spectators.add(player_id)
                game.player_rooms[player_id] = room_code # Track spectator for disconnects
                await websocket.send_json({"type": "spectating", "data": {"room_code": room_code}})
                logger.info(f"Player {player_id} is now spectating room {room_code}")
            else:
                await websocket.send_json({"type": "error", "message": "Room not found for spectating."})

        elif action == "leave_room":
            game.leave_room(player_id) # leave_room handles removal from player_rooms
            await websocket.send_json({"type": "room_left"}) # Client will handle UI update (e.g., back to menu)

        elif action == "start_game":
            if player_id not in game.player_rooms:
                await websocket.send_json({"type": "error", "message": "You are not in a room."}); return
            room_code = game.player_rooms[player_id]
            room = game.rooms.get(room_code)
            if not room: # Should not happen if player_rooms is consistent
                await websocket.send_json({"type": "error", "message": "Internal error: Room not found."}); return

            if room.owner_id == player_id:
                if game.start_game(room_code):
                    # Game state update will be sent by the game loop
                    logger.info(f"Game started in room {room_code} by owner {player_id}.")
                    # Optionally send an immediate ack: await websocket.send_json({"type": "game_started_ack"})
                else:
                    await websocket.send_json({"type": "error", "message": "Cannot start game (not enough players, or already started?)."})
            else:
                await websocket.send_json({"type": "error", "message": "Only the room owner can start the game."})

        elif action == "player_action":
            if not game.check_rate_limit(player_id, "action"):
                await websocket.send_json({"type": "error", "message": "Action rate limit exceeded. Please wait a moment."})
                return
            if player_id not in game.player_rooms:
                await websocket.send_json({"type": "error", "message": "You are not in a room to perform an action."}); return
            room_code = game.player_rooms[player_id]

            action_type_str = payload_dict.get("action_type")
            amount = payload_dict.get("amount", 0)
            if not isinstance(amount, int): amount = 0 # Ensure amount is int

            try:
                poker_action_enum = PlayerAction(action_type_str)
                if not game.player_action(room_code, player_id, poker_action_enum, amount):
                     # player_action logs details, send generic error to client
                     await websocket.send_json({"type": "error", "message": "Invalid action, not your turn, or other game rule violation."})
            except ValueError: # Invalid action_type_str for Enum
                logger.warning(f"Invalid action type '{action_type_str}' from {player_id}.")
                await websocket.send_json({"type": "error", "message": f"Invalid action type: {action_type_str}"})

        elif action == "send_chat_message":
            if not game.check_rate_limit(player_id, "message"):
                await websocket.send_json({"type": "error", "message": "Chat rate limit exceeded."}); return
            if player_id not in game.player_rooms: # Check if associated with any room (player or spectator)
                await websocket.send_json({"type": "error", "message": "You must be in a room to chat."}); return
            room_code = game.player_rooms[player_id] # player_rooms includes spectators

            message_text = payload_dict.get("message")
            if message_text and isinstance(message_text, str) and 0 < len(message_text.strip()) <= 200:
                game.add_chat_message(room_code, player_id, message_text.strip())
                # Chat messages are broadcast via game_state update
            else:
                await websocket.send_json({"type": "error", "message": "Invalid chat message (empty or too long)."})

        elif action == "get_room_list":
            public_rooms = []
            for r_code, r_obj in game.rooms.items():
                # Filter for public, non-password protected, waiting rooms
                if r_obj.room_type == RoomType.PUBLIC and not r_obj.settings.password and \
                   (r_obj.phase == GamePhase.WAITING or r_obj.phase == GamePhase.GAME_OVER):
                    human_player_count = sum(1 for p_in_r in r_obj.players.values() if not p_in_r.is_ai)
                    public_rooms.append({
                        "code": r_code,
                        "name": r_obj.name,
                        "players": human_player_count, # Show human player count
                        "max_players": r_obj.settings.max_players, # Max human players
                        "game_mode": r_obj.settings.game_mode.value,
                        "blinds": f"{r_obj.settings.small_blind}/{r_obj.settings.big_blind}",
                        "ai_players": r_obj.settings.ai_players
                    })
            await websocket.send_json({"type": "room_list", "data": {"rooms": public_rooms}})

        elif action == "get_hand_history":
            if player_id not in game.player_rooms:
                await websocket.send_json({"type": "error", "message": "Not in a room."}); return
            room_code = game.player_rooms[player_id]
            room = game.rooms.get(room_code)
            if room:
                await websocket.send_json({"type": "hand_history", "data": {"history": room.hand_history[-10:]}}) # Send last 10
            else:
                await websocket.send_json({"type": "error", "message": "Room not found for history."})
        else:
            logger.warning(f"Unknown action '{action}' received from {player_id}.")
            await websocket.send_json({"type": "error", "message": f"Unknown action: {action}"})

    except WebSocketDisconnect: # Re-raise to be caught by the main websocket_endpoint loop
        raise
    except Exception as e:
        logger.exception(f"Error handling WebSocket message (action: {action}) from {player_id}: {e}")
        try:
            await websocket.send_json({"type": "error", "message": "Server error processing your request."})
        except Exception: # If sending error also fails
            logger.error(f"Failed to send error notification back to {player_id} after previous error.")


# --- FastAPI App Setup ---
@asynccontextmanager
async def lifespan(app_instance: FastAPI): # Renamed app to app_instance
    logger.info("Application startup: Initializing game loop...")
    asyncio.create_task(game_loop())
    # asyncio.create_task(game.cleanup_inactive_rooms_periodically()) # If you add a cleanup task
    logger.info("Advanced Poker Game Server Started with Game Loop Running.")
    yield
    # Shutdown
    game.running = False # Signal game loop to stop
    logger.info("Advanced Poker Game Server Shutting Down...")
    # Add any other cleanup needed here
    await asyncio.sleep(1) # Give game loop a moment to exit
    logger.info("Shutdown complete.")


app = FastAPI(lifespan=lifespan)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"], # Or specify your frontend origin for production
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

# --- HTTP Routes ---
@app.get("/", response_class=HTMLResponse)
async def get_root(request: Request):
    logger.info(f"GET / request from {request.client.host}")
    # Ensure 'index.html' is in the same directory as this script
    # or adjust the path.
    # For Render/cloud deployment, this path might need to be relative to a 'static' dir.
    # For local, same dir is easiest.
    if os.path.exists("index.html"):
        return FileResponse("index.html")
    else:
        logger.error("index.html not found in the current working directory.")
        return HTMLResponse(content="<h1>Error: Frontend (index.html) not found.</h1><p>Please ensure index.html is in the correct location relative to the server script.</p>", status_code=500)


@app.get("/health")
async def health_check():
    return {
        "status": "ok",
        "active_rooms": len(game.rooms),
        "connected_websockets": len(game.connections),
        "global_stats": game.global_stats
    }

# --- WebSocket Route ---
@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    player_id_conn = str(uuid.uuid4()) # Unique ID for this specific WebSocket connection instance
    logger.info(f"--- WebSocket connection attempt received. Assigning temp ID: {player_id_conn} ---")
    try:
        await websocket.accept()
        logger.info(f"--- WebSocket connection accepted for {player_id_conn} ---")
    except Exception as e:
        logger.error(f"--- WebSocket FAILED to accept for {player_id_conn}: {e} ---", exc_info=True)
        return # Cannot proceed if accept fails

    game.connections[player_id_conn] = websocket # Store connection with this temp ID
    # This player_id_conn is used as `myPlayerId` on the client until they join/create a room
    # and get a persistent Player object ID. For actions, the client sends its known `myPlayerId`.
    # Server uses `player_id_conn` to map WebSocket to `Player` object after join.

    game.global_stats['total_players'] += 1 # Simplistic count of connections, not unique players
    logger.info(f"WebSocket {player_id_conn} connected successfully.")

    try:
        await websocket.send_json({
            "type": "connected",
            "data": {"player_id": player_id_conn, "message": "Welcome to the Royal Poker 3D!"}
        })
        logger.info(f"--- Sent 'connected' message to {player_id_conn} ---")
    except Exception as e:
        logger.error(f"--- FAILED to send 'connected' message to {player_id_conn}: {e} ---", exc_info=True)
        # Connection likely already dead, proceed to finally block for cleanup
        # but no `raise` here as the outer try handles the disconnect.

    try:
        while True:
            data = await websocket.receive_text()
            logger.debug(f"Received raw data from {player_id_conn}: {data[:200]}...") # Log snippet
            try:
                message_data = json.loads(data)
                # Basic validation of top-level structure
                if not isinstance(message_data, dict) or "action" not in message_data:
                    raise ValueError("Message must be a JSON object with an 'action' field.")
                ws_message = WSMessage(**message_data) # Validate with Pydantic model
            except json.JSONDecodeError:
                logger.warning(f"Invalid JSON received from {player_id_conn}: {data}")
                await websocket.send_json({"type": "error", "message": "Invalid JSON format."})
                continue # Wait for next message
            except (ValidationError, ValueError) as e: # Catch Pydantic errors or our manual ValueError
                error_msg = e.errors() if isinstance(e, ValidationError) else str(e)
                logger.warning(f"Invalid WSMessage structure from {player_id_conn}: {error_msg}")
                await websocket.send_json({"type": "error", "message": f"Invalid message structure: {error_msg}"})
                continue

            # Use player_id_conn for handle_websocket_message, as this is the ID known to game.connections
            await handle_websocket_message(websocket, player_id_conn, ws_message)

    except WebSocketDisconnect:
        logger.info(f"WebSocket {player_id_conn} disconnected.")
    except Exception as e:
        logger.exception(f"Unexpected error in WebSocket connection for {player_id_conn}: {e}")
    finally:
        logger.info(f"Cleaning up resources for WebSocket {player_id_conn}.")
        if player_id_conn in game.connections:
            del game.connections[player_id_conn]
        # Player object in a room (if any) associated with this player_id_conn
        # will be handled by leave_room logic (e.g., if game_loop tries to send and fails,
        # or if player_id_conn was also used as the Player object's ID)
        # For robustness, explicitly call leave_room if this connection ID was a player's ID.
        # If player_id_conn is just a temporary ID, leave_room might need to find the Player obj by connection_id.
        # Current leave_room takes the Player's actual ID.
        # Find if this connection_id was associated with an active player object
        actual_player_id_to_remove = None
        for room_code_iter in list(game.rooms.keys()): # Iterate keys to allow room deletion
            room_iter = game.rooms.get(room_code_iter)
            if room_iter:
                for p_id_iter, p_obj_iter in list(room_iter.players.items()):
                    if p_obj_iter.connection_id == player_id_conn:
                        actual_player_id_to_remove = p_obj_iter.id
                        break
                if actual_player_id_to_remove:
                    break
            if room_iter and player_id_conn in room_iter.spectators: # Also check if it was a spectator
                actual_player_id_to_remove = player_id_conn # Spectator uses connection_id as its main ID in player_rooms
                break


        if actual_player_id_to_remove:
            logger.info(f"WebSocket {player_id_conn} was associated with player/spectator ID {actual_player_id_to_remove}. Triggering leave_room.")
            game.leave_room(actual_player_id_to_remove, force=True)
        else:
            # If player_id_conn was never upgraded to a full player (e.g. disconnected before joining a room)
            # ensure it's cleaned from player_rooms if it was added as a spectator placeholder.
            # This case should be covered if actual_player_id_to_remove was set for spectator
             logger.info(f"WebSocket {player_id_conn} was not found as an active player/spectator. No explicit leave_room needed beyond connection removal.")

        logger.info(f"Finished cleanup for WebSocket {player_id_conn}.")


if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    logger.info(f"Starting Uvicorn server on host 0.0.0.0, port {port}")
    # When running directly, for Render this will be overridden by their start command.
    # For local testing:
    uvicorn.run("app:app", host="0.0.0.0", port=port, reload=True, ws_ping_interval=20, ws_ping_timeout=20)
