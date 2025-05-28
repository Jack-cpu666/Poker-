import asyncio
import json
import logging
import os
import random
import string
import uuid
from collections import Counter
from dataclasses import dataclass, field
from enum import Enum
from functools import cmp_to_key
from itertools import combinations
from typing import Dict, List, Optional, Set, Tuple, Any

from fastapi import FastAPI, HTTPException, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse
from pydantic import BaseModel, Field, validator
from starlette.websockets import WebSocketState as StarletteWebSocketState

# Load .env file for local development
from dotenv import load_dotenv
load_dotenv()

# 1. GLOBAL CONFIG & STATE
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

PORT = int(os.getenv("PORT", "8000"))

rooms: Dict[str, "Room"] = {}
room_locks: Dict[str, asyncio.Lock] = {}
global_rooms_lock = asyncio.Lock()

# 2. POKER GAME CORE MODELS & LOGIC

# --- Card and Deck ---
SUITS = ["H", "D", "C", "S"]  # Hearts, Diamonds, Clubs, Spades
RANKS = ["2", "3", "4", "5", "6", "7", "8", "9", "T", "J", "Q", "K", "A"]
RANK_VALUES = {rank: i for i, rank in enumerate(RANKS, 2)} # T=10, J=11, Q=12, K=13, A=14

@dataclass
class Card:
    id: str
    suit: str
    rank: str
    face_up: bool = False
    position: Dict[str, float] = field(default_factory=lambda: {"x": 0, "y": 0, "z": 0})
    owner_id: Optional[str] = None # player_id, "deck", "table", "community"

    def to_dict(self):
        return {
            "id": self.id, "suit": self.suit, "rank": self.rank,
            "face_up": self.face_up, "position": self.position, "owner_id": self.owner_id
        }
    
    def get_value(self) -> int:
        return RANK_VALUES[self.rank]

@dataclass
class Deck:
    cards: List[Card] = field(default_factory=list)

    def __post_init__(self):
        if not self.cards:
            self.cards = [
                Card(id=f"{suit}_{rank}", suit=suit, rank=rank, owner_id="deck")
                for suit in SUITS for rank in RANKS
            ]
            self.shuffle()

    def shuffle(self):
        random.shuffle(self.cards)
        for i, card in enumerate(self.cards):
            card.owner_id = "deck"
            card.face_up = False
            card.position = {"x": 0, "y": 0, "z": i * 0.01}

    def draw(self) -> Optional[Card]:
        return self.cards.pop() if self.cards else None

    def add_card(self, card: Card):
        card.owner_id = "deck"; card.face_up = False
        self.cards.append(card)

    def to_dict(self):
        return {"card_count": len(self.cards)}

# --- Poker Hand Evaluation ---
class HandRank(Enum):
    HIGH_CARD = 0
    ONE_PAIR = 1
    TWO_PAIR = 2
    THREE_OF_A_KIND = 3
    STRAIGHT = 4
    FLUSH = 5
    FULL_HOUSE = 6
    FOUR_OF_A_KIND = 7
    STRAIGHT_FLUSH = 8
    # ROYAL_FLUSH is a specific Straight Flush

@dataclass
class PokerHand:
    rank: HandRank
    rank_values: List[int]  # Values defining the rank (e.g., [10, 9, 8, 7, 6] for a T-high straight)
                               # For pairs/trips etc., it's [PairValue, Kicker1, Kicker2, ...]
    hand_cards: List[Card] # The 5 cards forming the best hand

    def __lt__(self, other: "PokerHand") -> bool:
        if self.rank.value < other.rank.value:
            return True
        if self.rank.value > other.rank.value:
            return False
        # Same rank, compare rank_values
        for s_val, o_val in zip(self.rank_values, other.rank_values):
            if s_val < o_val:
                return True
            if s_val > o_val:
                return False
        return False # Tie

def get_best_poker_hand(seven_cards: List[Card]) -> PokerHand:
    best_hand_overall = None
    for five_card_combo in combinations(seven_cards, 5):
        current_eval = evaluate_five_card_hand(list(five_card_combo))
        if best_hand_overall is None or current_eval > best_hand_overall:
            best_hand_overall = current_eval
    return best_hand_overall

def evaluate_five_card_hand(hand: List[Card]) -> PokerHand: # hand is exactly 5 cards
    hand.sort(key=lambda c: c.get_value(), reverse=True)
    values = [c.get_value() for c in hand]
    suits = [c.suit for c in hand]
    value_counts = Counter(values)
    
    is_flush = len(set(suits)) == 1
    
    # Check for straight (Ace can be low or high)
    is_straight = False
    unique_sorted_values = sorted(list(set(values)), reverse=True)
    if len(unique_sorted_values) >= 5: # Should always be true for 5 distinct cards for straight
        # Normal straight
        for i in range(len(unique_sorted_values) - 4):
            if unique_sorted_values[i] - unique_sorted_values[i+4] == 4:
                is_straight = True
                straight_high_value = unique_sorted_values[i]
                break
        # Ace-low straight (A, 2, 3, 4, 5)
        if not is_straight and set(values) == {14, 2, 3, 4, 5}: # Ace, 2, 3, 4, 5
            is_straight = True
            straight_high_value = 5 # Value of 5 for A-5 straight
            # Re-order values for A-5 straight rank_values
            values = [v if v != 14 else 1 for v in values]
            values.sort(reverse=True)

    if is_straight and is_flush:
        return PokerHand(HandRank.STRAIGHT_FLUSH, [straight_high_value], hand)

    quads = [v for v, count in value_counts.items() if count == 4]
    if quads:
        kicker = [v for v in values if v != quads[0]][0]
        return PokerHand(HandRank.FOUR_OF_A_KIND, [quads[0], kicker], hand)

    trips = [v for v, count in value_counts.items() if count == 3]
    pairs = [v for v, count in value_counts.items() if count == 2]
    
    if trips and pairs:
        return PokerHand(HandRank.FULL_HOUSE, [trips[0], pairs[0]], hand)

    if is_flush:
        return PokerHand(HandRank.FLUSH, values, hand)

    if is_straight:
        # For A-5 straight, values were already adjusted
        return PokerHand(HandRank.STRAIGHT, [straight_high_value] + [v for v in values if v != straight_high_value][:4], hand)

    if trips:
        kickers = sorted([v for v in values if v != trips[0]], reverse=True)[:2]
        return PokerHand(HandRank.THREE_OF_A_KIND, [trips[0]] + kickers, hand)

    if len(pairs) == 2:
        pairs.sort(reverse=True)
        kicker = [v for v in values if v not in pairs][0]
        return PokerHand(HandRank.TWO_PAIR, pairs + [kicker], hand)
    
    if len(pairs) == 1:
        kickers = sorted([v for v in values if v != pairs[0]], reverse=True)[:3]
        return PokerHand(HandRank.ONE_PAIR, [pairs[0]] + kickers, hand)
        
    return PokerHand(HandRank.HIGH_CARD, values[:5], hand)


# --- Player ---
class PlayerAction(Enum):
    FOLD = "fold"
    CHECK = "check"
    CALL = "call"
    BET = "bet"
    RAISE = "raise"

@dataclass
class Player:
    id: str
    name: str
    ws: WebSocket
    hand: List[Card] = field(default_factory=list)
    balance: int = 1000  # Starting balance
    current_bet_in_round: int = 0 # Amount bet in the current betting round
    folded: bool = False
    is_all_in: bool = False
    is_host: bool = False
    seat_index: int = -1 # Position at the table

    async def send_json(self, data: dict):
        if self.ws.application_state == StarletteWebSocketState.CONNECTED:
            try: await self.ws.send_json(data)
            except Exception as e: logger.error(f"Error sending to player {self.id}: {e}")
        else: logger.warning(f"Player {self.id} ws not connected.")

    def to_dict(self, show_hand_to_player: bool = False):
        # For poker, players usually only see their own hand unless it's showdown
        hand_to_show = []
        if show_hand_to_player: # This player is requesting their own state
            hand_to_show = [card.to_dict() for card in self.hand]
        elif self.hand : # Other players see card backs or count
            hand_to_show = [Card(id=f"back_{i}", suit="", rank="", owner_id=self.id, face_up=False).to_dict() for i in range(len(self.hand))]

        return {
            "id": self.id, "name": self.name, "is_host": self.is_host,
            "balance": self.balance, "current_bet_in_round": self.current_bet_in_round,
            "folded": self.folded, "is_all_in": self.is_all_in,
            "seat_index": self.seat_index,
            "hand": hand_to_show, # Only show actual cards to self or at showdown
            "hand_card_count": len(self.hand)
        }
    
    def reset_for_new_hand(self):
        self.hand.clear()
        self.current_bet_in_round = 0
        self.folded = False
        self.is_all_in = False


# --- Game State Enums ---
class GamePhase(Enum):
    WAITING_FOR_PLAYERS = "WAITING_FOR_PLAYERS"
    PREFLOP = "PREFLOP"
    FLOP = "FLOP"
    TURN = "TURN"
    RIVER = "RIVER"
    SHOWDOWN = "SHOWDOWN"
    HAND_OVER = "HAND_OVER"


# --- Room ---
@dataclass
class Room:
    id: str
    players: Dict[str, Player] = field(default_factory=dict) # player_id -> Player
    player_order: List[str] = field(default_factory=list) # IDs of players in seat order
    spectators: List[WebSocket] = field(default_factory=list)
    deck: Deck = field(default_factory=Deck)
    chat_messages: List[Dict] = field(default_factory=list)
    max_players: int = 6
    is_private: bool = False
    password: Optional[str] = None
    host_id: Optional[str] = None

    # Poker specific state
    game_phase: GamePhase = GamePhase.WAITING_FOR_PLAYERS
    community_cards: List[Card] = field(default_factory=list)
    pot: int = 0
    current_bet_to_match: int = 0 # Highest bet in the current round
    current_player_turn_id: Optional[str] = None
    dealer_button_player_id: Optional[str] = None # Player ID of the dealer
    small_blind_amount: int = 10
    big_blind_amount: int = 20
    last_raiser_id: Optional[str] = None # ID of the player who made the last bet/raise
    min_raise_amount: int = 0

    hand_winners_info: List[Dict] = field(default_factory=list) # Store info about winners for client display

    async def broadcast(self, message: dict, exclude_player_ids: Optional[List[str]] = None):
        # (Same as previous, simplified for brevity)
        if exclude_player_ids is None: exclude_player_ids = []
        active_conns = []
        for p_id, p in list(self.players.items()):
            if p_id not in exclude_player_ids:
                if p.ws.application_state == StarletteWebSocketState.CONNECTED:
                    active_conns.append(p.ws.send_json(message))
        for spec_ws in list(self.spectators):
            if spec_ws.application_state == StarletteWebSocketState.CONNECTED:
                active_conns.append(spec_ws.send_json(message))
            else: self.spectators.remove(spec_ws)
        if active_conns: await asyncio.gather(*active_conns, return_exceptions=True)

    def get_player_view_state(self, player_id: Optional[str]):
        """Returns the game state tailored for a specific player or spectator."""
        players_data = []
        is_showdown = self.game_phase == GamePhase.SHOWDOWN or self.game_phase == GamePhase.HAND_OVER
        
        for p_obj_id in self.player_order:
            p_obj = self.players[p_obj_id]
            # At showdown, or if it's this player, show their hand. Otherwise, show card count/backs.
            show_hand = is_showdown or (player_id is not None and p_obj.id == player_id)
            p_data = p_obj.to_dict(show_hand_to_player=show_hand)
            if not show_hand and not is_showdown and p_obj.hand : # If not showdown and not self, ensure hand shows backs
                 p_data["hand"] = [Card(id=f"back_{i}_{p_obj.id}", suit="", rank="", owner_id=p_obj.id, face_up=False).to_dict() for i in range(len(p_obj.hand))]
            players_data.append(p_data)

        return {
            "room_id": self.id,
            "players": players_data,
            "spectator_count": len(self.spectators),
            "chat_messages": self.chat_messages[-20:],
            "max_players": self.max_players,
            "is_private": self.is_private,
            "host_id": self.host_id,
            # Poker specific
            "game_phase": self.game_phase.value,
            "community_cards": [c.to_dict() for c in self.community_cards],
            "pot": self.pot,
            "current_bet_to_match": self.current_bet_to_match,
            "current_player_turn_id": self.current_player_turn_id,
            "dealer_button_player_id": self.dealer_button_player_id,
            "small_blind_amount": self.small_blind_amount,
            "big_blind_amount": self.big_blind_amount,
            "min_raise_amount": self.min_raise_amount,
            "hand_winners_info": self.hand_winners_info if (self.game_phase == GamePhase.SHOWDOWN or self.game_phase == GamePhase.HAND_OVER) else []
        }

    async def broadcast_game_state(self, specific_player_id_for_private_hand_view: Optional[str] = None):
        """Broadcasts tailored game state to all players and spectators."""
        # For spectators, they get a general view (no private hands unless showdown)
        spectator_state = self.get_player_view_state(None)
        for spec_ws in list(self.spectators):
            if spec_ws.application_state == StarletteWebSocketState.CONNECTED:
                try: await spec_ws.send_json({"action": "game_state_update", "payload": spectator_state})
                except Exception as e: logger.error(f"Error sending to spectator: {e}")
            else: self.spectators.remove(spec_ws)

        # For players, they get their specific view
        for p_id, p_obj in list(self.players.items()):
            player_specific_state = self.get_player_view_state(p_id)
            await p_obj.send_json({"action": "game_state_update", "payload": player_specific_state})
            if specific_player_id_for_private_hand_view == p_id: # Send dealt cards info
                if p_obj.hand: # Only if they have cards.
                    await p_obj.send_json({
                        "action": "hole_cards_dealt",
                        "payload": {"cards": [c.to_dict() for c in p_obj.hand]}
                    })


    def add_player(self, player: Player):
        if len(self.players) >= self.max_players:
            raise HTTPException(status_code=403, detail="Room is full")
        
        if not self.host_id:
            player.is_host = True
            self.host_id = player.id
        
        # Assign seat index
        available_seats = list(set(range(self.max_players)) - set(p.seat_index for p in self.players.values()))
        if not available_seats: # Should not happen if max_players check is done
            raise Exception("No available seats logic error")
        player.seat_index = min(available_seats)
        
        self.players[player.id] = player
        
        # Rebuild player_order based on seat_index
        sorted_players = sorted(self.players.values(), key=lambda p: p.seat_index)
        self.player_order = [p.id for p in sorted_players]

        if self.game_phase == GamePhase.WAITING_FOR_PLAYERS and len(self.players) < 2:
             logger.info(f"Player {player.name} joined. Waiting for more players.")
        # If game was in progress, this player joins as waiting for next hand.

    def remove_player(self, player_id: str):
        if player_id not in self.players: return None
        
        player_leaving = self.players[player_id]
        
        # If player had bet in current hand, their bets stay in pot (usually)
        # Or handle folding logic if game is active.
        if self.game_phase not in [GamePhase.WAITING_FOR_PLAYERS, GamePhase.HAND_OVER]:
            if player_leaving and not player_leaving.folded:
                player_leaving.folded = True # Mark as folded if they leave mid-hand
                logger.info(f"Player {player_id} left mid-hand, auto-folding.")
                # Check if this triggers end of hand or next turn
                if self.current_player_turn_id == player_id:
                    asyncio.create_task(self._handle_player_fold_or_leave(player_leaving))


        del self.players[player_id]
        self.player_order = [pid for pid in self.player_order if pid != player_id]

        new_host_id = None
        if player_id == self.host_id:
            if self.players:
                new_host_id = self.player_order[0] # Next player in order becomes host
                self.players[new_host_id].is_host = True
                self.host_id = new_host_id
            else: self.host_id = None
        
        # If only one player left in an active game, they win the pot.
        active_players_in_hand = [p for p_id_active in self.player_order if (p := self.players.get(p_id_active)) and not p.folded and not p.is_all_in]
        if self.game_phase not in [GamePhase.WAITING_FOR_PLAYERS, GamePhase.HAND_OVER] and len(active_players_in_hand) <=1 :
             # This might need to be an async task if it involves broadcasting
             asyncio.create_task(self.check_hand_end_due_to_folds())

        return new_host_id
    
    async def _handle_player_fold_or_leave(self, player: Player):
        # This function is called when a player folds or leaves, and it was their turn.
        # It needs to check conditions and advance the game.
        logger.info(f"Handling fold/leave for player {player.id} whose turn it was.")
        
        num_active_players = sum(1 for p_id in self.player_order if (p_obj := self.players.get(p_id)) and not p_obj.folded)
        if num_active_players <= 1:
            await self.check_hand_end_due_to_folds()
        else:
            await self.progress_to_next_player_action()


    # --- POKER GAME FLOW METHODS ---
    async def start_new_hand(self):
        if len(self.player_order) < 2:
            await self.broadcast({"action": "error", "payload": {"message": "Need at least 2 players to start."}})
            return

        self.deck = Deck() # Fresh, shuffled deck
        self.community_cards.clear()
        self.pot = 0
        self.current_bet_to_match = self.big_blind_amount
        self.min_raise_amount = self.big_blind_amount
        self.last_raiser_id = None
        self.hand_winners_info.clear()

        for p_id in self.player_order:
            player = self.players[p_id]
            player.reset_for_new_hand()
            if player.balance == 0: # Player is broke, cannot participate
                player.folded = True # Mark as folded for this hand

        # Determine dealer: move button clockwise
        if self.dealer_button_player_id is None or self.dealer_button_player_id not in self.player_order:
            self.dealer_button_player_id = self.player_order[0]
        else:
            current_dealer_idx = self.player_order.index(self.dealer_button_player_id)
            self.dealer_button_player_id = self.player_order[(current_dealer_idx + 1) % len(self.player_order)]
        
        # Blinds (handle cases with 2 players - HU)
        # Players who can post blinds (non-zero balance)
        eligible_players_for_blinds = [p_id for p_id in self.player_order if self.players[p_id].balance > 0]
        if not eligible_players_for_blinds or len(eligible_players_for_blinds) < 2 and len(self.player_order) >=2 : # Not enough players with money for blinds
            await self.broadcast({"action": "error", "payload": {"message": "Not enough players with balance for blinds. Game cannot start."}})
            self.game_phase = GamePhase.WAITING_FOR_PLAYERS
            return

        dealer_idx_in_ordered_list = self.player_order.index(self.dealer_button_player_id)

        num_players_in_game = len(self.player_order)
        
        # Small Blind
        sb_player_idx = (dealer_idx_in_ordered_list + 1) % num_players_in_game
        if num_players_in_game == 2: # Heads-up, dealer is SB
            sb_player_idx = dealer_idx_in_ordered_list
        sb_player = self.players[self.player_order[sb_player_idx]]
        sb_amount = min(self.small_blind_amount, sb_player.balance)
        sb_player.balance -= sb_amount
        sb_player.current_bet_in_round = sb_amount
        self.pot += sb_amount
        if sb_player.balance == 0: sb_player.is_all_in = True
        logger.info(f"Player {sb_player.name} posts SB: {sb_amount}")

        # Big Blind
        bb_player_idx = (sb_player_idx + 1) % num_players_in_game
        bb_player = self.players[self.player_order[bb_player_idx]]
        bb_amount = min(self.big_blind_amount, bb_player.balance)
        bb_player.balance -= bb_amount
        bb_player.current_bet_in_round = bb_amount
        self.pot += bb_amount
        if bb_player.balance == 0: bb_player.is_all_in = True
        logger.info(f"Player {bb_player.name} posts BB: {bb_amount}")

        self.current_bet_to_match = bb_amount # BB sets the initial bet to match
        self.last_raiser_id = bb_player.id # BB is effectively the first "raiser"

        # Deal hole cards
        start_deal_idx = (sb_player_idx + 1) % num_players_in_game # Start dealing to player after SB (or BB in HU)
        for _ in range(2): # Two cards each
            for i in range(num_players_in_game):
                player_to_deal_idx = (start_deal_idx + i) % num_players_in_game
                player = self.players[self.player_order[player_to_deal_idx]]
                if not player.folded: # Don't deal to players who are broke and folded
                    card = self.deck.draw()
                    if card:
                        card.owner_id = player.id
                        # card.face_up = True # For player to see, but backend keeps it generic
                        player.hand.append(card)
        
        self.game_phase = GamePhase.PREFLOP
        
        # Determine first player to act (UTG)
        utg_player_idx = (bb_player_idx + 1) % num_players_in_game
        self.current_player_turn_id = self.player_order[utg_player_idx]
        
        # Ensure current player is not folded (e.g. was broke)
        while self.players[self.current_player_turn_id].folded or self.players[self.current_player_turn_id].is_all_in :
             utg_player_idx = (utg_player_idx + 1) % num_players_in_game
             self.current_player_turn_id = self.player_order[utg_player_idx]
             if self.current_player_turn_id == self.player_order[(bb_player_idx + 1) % num_players_in_game]: # Cycled through all
                 logger.warning("All players folded or all-in before action. This shouldn't happen typically.")
                 # This case could lead to immediate showdown or next round if all are all-in
                 await self.check_betting_round_end()
                 return


        logger.info(f"New hand started. Dealer: {self.players[self.dealer_button_player_id].name}. Turn: {self.players[self.current_player_turn_id].name}")
        await self.broadcast_game_state(specific_player_id_for_private_hand_view="unused") # Pass any ID to trigger private hand view logic for each client

    async def handle_player_action(self, player_id: str, action_type: PlayerAction, amount: Optional[int] = 0):
        if player_id != self.current_player_turn_id:
            await self.players[player_id].send_json({"action": "error", "payload": {"message": "Not your turn."}})
            return
        if self.game_phase not in [GamePhase.PREFLOP, GamePhase.FLOP, GamePhase.TURN, GamePhase.RIVER]:
            await self.players[player_id].send_json({"action": "error", "payload": {"message": "Not in a betting phase."}})
            return

        player = self.players[player_id]
        if player.folded or player.is_all_in: # Should not happen if turn logic is correct
            await self.players[player_id].send_json({"action": "error", "payload": {"message": "Already folded or all-in."}})
            await self.progress_to_next_player_action() # Skip them
            return

        previous_bet_this_round = player.current_bet_in_round
        
        valid_action = False
        if action_type == PlayerAction.FOLD:
            player.folded = True
            valid_action = True
            logger.info(f"Player {player.name} folds.")
        
        elif action_type == PlayerAction.CHECK:
            # Can only check if current bet is 0 or player already matched current_bet_to_match
            if player.current_bet_in_round == self.current_bet_to_match:
                valid_action = True
                logger.info(f"Player {player.name} checks.")
            else:
                await player.send_json({"action": "error", "payload": {"message": "Cannot check, must call or raise."}})
                return

        elif action_type == PlayerAction.CALL:
            call_amount = self.current_bet_to_match - player.current_bet_in_round
            if call_amount <= 0: # Effectively a check if already matched
                 valid_action = True # Allow call if already matched (becomes a check)
                 logger.info(f"Player {player.name} calls (effectively checks).")
            elif player.balance >= call_amount:
                player.balance -= call_amount
                player.current_bet_in_round += call_amount
                self.pot += call_amount
                valid_action = True
                logger.info(f"Player {player.name} calls {call_amount}.")
            elif player.balance > 0 and player.balance < call_amount : # All-in call
                self.pot += player.balance
                player.current_bet_in_round += player.balance
                player.balance = 0
                player.is_all_in = True
                valid_action = True
                logger.info(f"Player {player.name} calls all-in for {player.current_bet_in_round - previous_bet_this_round}.")
            else: # No balance to call
                await player.send_json({"action": "error", "payload": {"message": "Not enough balance to call. Must fold or go all-in (if applicable)."}})
                return

        elif action_type == PlayerAction.BET or action_type == PlayerAction.RAISE:
            required_bet_amount = amount # This is the TOTAL bet for the round for this player
            if required_bet_amount is None or required_bet_amount <= self.current_bet_to_match:
                await player.send_json({"action": "error", "payload": {"message": f"Bet/Raise amount must be greater than current bet to match ({self.current_bet_to_match})."}})
                return

            actual_raise_amount = required_bet_amount - self.current_bet_to_match
            if actual_raise_amount < self.min_raise_amount and (self.current_bet_to_match > 0 or self.game_phase != GamePhase.PREFLOP): # Min raise rule (unless opening bet pre-flop)
                 # Exception: If player is all-in, they can "raise" for less than min_raise if that's all they have
                 if required_bet_amount < player.balance + player.current_bet_in_round: # Not an all-in raise
                    await player.send_json({"action": "error", "payload": {"message": f"Minimum raise is {self.min_raise_amount} over the previous bet/raise."}})
                    return

            amount_to_add_to_pot = required_bet_amount - player.current_bet_in_round
            
            if player.balance >= amount_to_add_to_pot:
                player.balance -= amount_to_add_to_pot
                player.current_bet_in_round = required_bet_amount
                self.pot += amount_to_add_to_pot
                self.current_bet_to_match = required_bet_amount
                self.last_raiser_id = player.id
                self.min_raise_amount = required_bet_amount - previous_bet_this_round # The size of this raise becomes next min_raise
                if self.game_phase == GamePhase.PREFLOP and previous_bet_this_round == self.big_blind_amount:
                     # If re-raising the BB, the min_raise_amount is the amount of the re-raise itself.
                     self.min_raise_amount = required_bet_amount - self.big_blind_amount
                elif self.game_phase == GamePhase.PREFLOP and previous_bet_this_round < self.big_blind_amount and self.current_bet_to_match == self.big_blind_amount:
                    # First raise over BB
                    self.min_raise_amount = self.current_bet_to_match - self.big_blind_amount
                else:
                    self.min_raise_amount = self.current_bet_to_match - previous_bet_this_round # if previous_bet_this_round was a call of a prior bet. this may need review.
                    if self.min_raise_amount < self.big_blind_amount : self.min_raise_amount = self.big_blind_amount # Raise always at least BB

                valid_action = True
                logger.info(f"Player {player.name} {'bets' if action_type == PlayerAction.BET else 'raises'} to {required_bet_amount}.")
            elif player.balance > 0 and player.balance < amount_to_add_to_pot: # All-in bet/raise
                amount_to_add_to_pot = player.balance # They bet all they have
                player.current_bet_in_round += amount_to_add_to_pot
                self.pot += amount_to_add_to_pot
                player.balance = 0
                player.is_all_in = True
                
                if player.current_bet_in_round > self.current_bet_to_match: # Is it a "real" raise to reopen betting?
                    self.current_bet_to_match = player.current_bet_in_round
                    self.last_raiser_id = player.id
                    # Min raise amount update based on this all-in raise, if it's a full raise.
                    # This part of logic is complex for partial all-in raises.
                    # For simplicity: if all-in reopens betting, min_raise is based on the previous full raise or BB.
                    # This is one of the trickiest parts of NLHE rules.
                    # A simple rule: if an all-in is less than a full raise, it doesn't reopen betting for players who have already acted.
                    # The `last_raiser_id` correctly tracks who the action needs to return to.
                
                valid_action = True
                logger.info(f"Player {player.name} {'bets' if action_type == PlayerAction.BET else 'raises'} all-in for {amount_to_add_to_pot}, total in round {player.current_bet_in_round}.")
            else:
                await player.send_json({"action": "error", "payload": {"message": "Not enough balance."}})
                return
        
        if valid_action:
            await self.check_betting_round_end()
        else: # Should have been caught by specific action logic.
            await player.send_json({"action": "error", "payload": {"message": "Invalid action or server error."}})


    async def check_betting_round_end(self):
        active_players_not_all_in = [p for p_id in self.player_order if (p := self.players.get(p_id)) and not p.folded and not p.is_all_in]
        num_active_players = sum(1 for p_id in self.player_order if (p_obj := self.players.get(p_id)) and not p_obj.folded)

        if num_active_players <= 1:
            await self.progress_to_showdown_or_next_round(pot_awarded_pre_showdown=True)
            return

        # Betting round ends if all non-folded, non-all-in players have bet the same amount,
        # and action has returned to the last raiser (or player after BB if no raise pre-flop).
        all_matched_or_all_in = True
        next_player_candidate = None
        
        # Find next player to act
        current_player_idx = self.player_order.index(self.current_player_turn_id)
        
        for i in range(1, len(self.player_order) + 1):
            potential_next_player_idx = (current_player_idx + i) % len(self.player_order)
            player_obj = self.players[self.player_order[potential_next_player_idx]]
            
            if not player_obj.folded and not player_obj.is_all_in:
                if player_obj.current_bet_in_round < self.current_bet_to_match:
                    all_matched_or_all_in = False # Someone still needs to act to match
                    next_player_candidate = player_obj.id
                    break 
                # Check if action has completed a full circle back to the last raiser or equivalent
                if player_obj.id == self.last_raiser_id or \
                   (self.last_raiser_id is None and self.game_phase == GamePhase.PREFLOP and player_obj.current_bet_in_round == self.big_blind_amount and self.player_order.index(player_obj.id) == (self.player_order.index(self.dealer_button_player_id)+2)%len(self.player_order) ): # BB check option
                    # If it got back to the last raiser and they matched, round ends (unless they were BB and it's pre-flop first action)
                    # This condition is complex. Simpler: if current player was last raiser, and they checked/called, round ends.
                    # More robust: if loop completes and all active players have `current_bet_in_round == self.current_bet_to_match`
                    # OR if the action is on the `last_raiser_id` and they `check` or `call`.
                    pass # Continue checking if others need to act before this raiser.
            
            # If we've looped through all players and everyone who isn't folded/all-in has matched the current_bet_to_match,
            # AND the current player is the one who would have been next after the last_raiser_id (or BB if no raise)
            # then the betting round is over.
            # This is complex. Let's use a simpler check:
            #   1. All non-folded, non-all-in players have player.current_bet_in_round == self.current_bet_to_match
            #   2. OR Action is on last_raiser_id and they check/call (meaning no further raise)
            #   3. OR (Preflop only) Action is on BB, no raise before them, and they check.

        # Refined end-of-round check:
        betting_over = True
        player_acted_on_current_bet = 0
        for p_id_check in self.player_order:
            p_check = self.players[p_id_check]
            if not p_check.folded and not p_check.is_all_in:
                if p_check.current_bet_in_round < self.current_bet_to_match:
                    betting_over = False # Someone still needs to act
                    next_player_candidate = p_check.id # This is the next player
                    break
                # Count players who have had a chance to act on the current bet size
                # This means their current_bet_in_round is self.current_bet_to_match
                if p_check.current_bet_in_round == self.current_bet_to_match:
                    player_acted_on_current_bet +=1
        
        # If betting_over is still true, it means all active, non-all-in players have matched.
        # We also need to ensure that the action has made it around to the person who made the last aggressive action (or BB)
        # The current player (self.current_player_turn_id) just acted.
        # If self.last_raiser_id made the bet that others are calling, and the action is now on self.last_raiser_id
        # (meaning it has come back around to them), and they check/call, the round ends.
        # This is effectively covered if all active players have matched the current_bet_to_match
        # AND (the player who just acted was the last_raiser_id OR the player who just acted was the BB and checked preflop with no prior raise)

        if betting_over and player_acted_on_current_bet >= len(active_players_not_all_in) and len(active_players_not_all_in) > 0:
             # Check if the player WHO JUST ACTED was the one to close the action
            actor = self.players[self.current_player_turn_id]
            is_bb_closing_preflop_no_raise = (
                self.game_phase == GamePhase.PREFLOP and
                actor.current_bet_in_round == self.big_blind_amount and # BB
                self.current_bet_to_match == self.big_blind_amount # No raise before BB
            )
            is_raiser_closing_action = (self.last_raiser_id == actor.id)

            if actor.current_bet_in_round == self.current_bet_to_match: # They called or checked
                if is_raiser_closing_action or is_bb_closing_preflop_no_raise or (self.last_raiser_id is None and len(active_players_not_all_in) > 0): # Ensure everyone has acted on the bet
                    # Check if everyone had a chance to act since the last raise
                    acted_since_last_raise_count = 0
                    for p_id_chk in self.player_order:
                        p_chk_obj = self.players[p_id_chk]
                        if not p_chk_obj.folded and not p_chk_obj.is_all_in:
                            if p_chk_obj.current_bet_in_round == self.current_bet_to_match:
                                acted_since_last_raise_count +=1
                    
                    if acted_since_last_raise_count == len(active_players_not_all_in):
                        logger.info(f"Betting round ended. Phase: {self.game_phase.value}")
                        await self.progress_to_showdown_or_next_round()
                        return
                    else: # Not everyone acted on this bet yet, find next player
                        next_player_candidate = self._find_next_active_player(self.current_player_turn_id)


        if next_player_candidate:
            self.current_player_turn_id = next_player_candidate
            logger.info(f"Next turn: {self.players[self.current_player_turn_id].name}")
            await self.broadcast_game_state()
        else: # Should be covered by betting_over logic, but as a fallback
            # This implies everyone is all-in or folded except maybe one, or round truly ended.
            logger.info(f"Betting round likely ended or only all-ins remain. Phase: {self.game_phase.value}")
            await self.progress_to_showdown_or_next_round()


    def _find_next_active_player(self, current_player_id: str, ignore_last_raiser_check=False) -> Optional[str]:
        current_idx = self.player_order.index(current_player_id)
        for i in range(1, len(self.player_order) + 1):
            next_idx = (current_idx + i) % len(self.player_order)
            next_player = self.players[self.player_order[next_idx]]
            if not next_player.folded and not next_player.is_all_in:
                # If ignore_last_raiser_check is False, the betting round might end if we reach the last raiser
                # and they don't need to act again. This is handled in check_betting_round_end.
                # This helper just finds the *next available* player.
                return next_player.id
        return None # No active player found (e.g. all folded/all-in)


    async def progress_to_next_player_action(self):
        """Advances turn to the next player who can act."""
        next_player_id = self._find_next_active_player(self.current_player_turn_id)
        if next_player_id:
            self.current_player_turn_id = next_player_id
            logger.info(f"Progressing turn to: {self.players[self.current_player_turn_id].name}")
            await self.broadcast_game_state()
        else:
            # No one else can act (e.g. all folded or all-in)
            logger.info("No more players to act in this round. Progressing phase or showdown.")
            await self.check_betting_round_end() # This will likely lead to next round/showdown

    async def check_hand_end_due_to_folds(self):
        active_players = [p for p_id in self.player_order if (p := self.players.get(p_id)) and not p.folded]
        if len(active_players) == 1:
            winner = active_players[0]
            logger.info(f"Hand ends. Player {winner.name} wins ${self.pot} as only one left.")
            winner.balance += self.pot
            self.pot = 0
            self.game_phase = GamePhase.HAND_OVER
            self.hand_winners_info = [{"player_id": winner.id, "player_name": winner.name, "amount_won": winner.balance - (winner.balance - self.pot), "hand_description": "All others folded"}] # amount won is tricky if balance was updated already
            await self.broadcast_game_state()
            # Could add a delay then offer to start new hand
        elif len(active_players) == 0: # Should not happen if logic is correct
            logger.error("Error: No active players left, but hand didn't resolve.")
            self.game_phase = GamePhase.HAND_OVER # Reset
            await self.broadcast_game_state()


    async def progress_to_showdown_or_next_round(self, pot_awarded_pre_showdown=False):
        # Reset per-round state for players for next betting round (if any)
        self.current_bet_to_match = 0
        self.min_raise_amount = self.big_blind_amount # Reset min raise for new street
        self.last_raiser_id = None # Action starts fresh
        for p_obj in self.players.values():
             p_obj.current_bet_in_round = 0 # Bets are now part of main pot

        if pot_awarded_pre_showdown: # Hand ended because all but one folded
             self.game_phase = GamePhase.HAND_OVER
             # Winner already awarded in check_hand_end_due_to_folds
             await self.broadcast_game_state()
             return

        # Determine if we need to go to showdown or deal more cards
        players_in_hand = [p for p_id in self.player_order if (p := self.players.get(p_id)) and not p.folded]
        if len(players_in_hand) <= 1: # Should have been caught by check_hand_end_due_to_folds or similar
            await self.check_hand_end_due_to_folds() # Award pot to the one remaining
            return

        if self.game_phase == GamePhase.PREFLOP:
            self.game_phase = GamePhase.FLOP
            for _ in range(3): self.community_cards.append(self.deck.draw())
            logger.info(f"Dealing Flop: {[c.id for c in self.community_cards[-3:]]}")
        elif self.game_phase == GamePhase.FLOP:
            self.game_phase = GamePhase.TURN
            self.community_cards.append(self.deck.draw())
            logger.info(f"Dealing Turn: {self.community_cards[-1].id}")
        elif self.game_phase == GamePhase.TURN:
            self.game_phase = GamePhase.RIVER
            self.community_cards.append(self.deck.draw())
            logger.info(f"Dealing River: {self.community_cards[-1].id}")
        elif self.game_phase == GamePhase.RIVER:
            await self.resolve_showdown()
            return # Showdown handles its own broadcast and phase change
        else: # Game was already over or in invalid state
            logger.warning(f"Progress called in unexpected phase: {self.game_phase}")
            self.game_phase = GamePhase.HAND_OVER
            await self.broadcast_game_state()
            return

        # Set next player to act for the new round (first non-folded, non-all-in player after dealer)
        dealer_idx = self.player_order.index(self.dealer_button_player_id)
        next_actor_found = False
        for i in range(1, len(self.player_order) + 1):
            player_to_act_idx = (dealer_idx + i) % len(self.player_order)
            player = self.players[self.player_order[player_to_act_idx]]
            if not player.folded and not player.is_all_in:
                self.current_player_turn_id = player.id
                next_actor_found = True
                break
        
        if not next_actor_found: # All remaining are all-in, proceed to showdown or deal remaining cards
            if self.game_phase != GamePhase.RIVER: # If not river yet, deal all remaining cards
                while self.game_phase != GamePhase.RIVER:
                    if self.game_phase == GamePhase.FLOP: # Was preflop, now flop done, deal turn
                         self.game_phase = GamePhase.TURN; self.community_cards.append(self.deck.draw())
                    elif self.game_phase == GamePhase.TURN: # Was flop, now turn done, deal river
                         self.game_phase = GamePhase.RIVER; self.community_cards.append(self.deck.draw())
                    elif self.game_phase == GamePhase.PREFLOP: # Should not happen if logic is right, but for safety
                         for _ in range(3): self.community_cards.append(self.deck.draw()) # Flop
                         self.community_cards.append(self.deck.draw()) # Turn
                         self.community_cards.append(self.deck.draw()) # River
                         self.game_phase = GamePhase.RIVER
                await self.resolve_showdown()

            else: # Already at River and all are all-in
                 await self.resolve_showdown()

        else: # There is a player to act
            logger.info(f"Starting betting round for {self.game_phase.value}. Turn: {self.players[self.current_player_turn_id].name}")
            await self.broadcast_game_state()


    async def resolve_showdown(self):
        self.game_phase = GamePhase.SHOWDOWN
        logger.info("--- SHOWDOWN ---")
        
        eligible_players = [p for p_id in self.player_order if (p := self.players.get(p_id)) and not p.folded]
        if not eligible_players:
            logger.error("Showdown called with no eligible players.")
            self.game_phase = GamePhase.HAND_OVER
            await self.broadcast_game_state()
            return

        # Evaluate hands for all eligible players
        player_hands: List[Tuple[Player, PokerHand]] = []
        for player in eligible_players:
            if not player.hand or len(player.hand) != 2: # Should always have 2 cards if not folded
                logger.warning(f"Player {player.name} in showdown with invalid hand: {player.hand}")
                continue
            
            # Ensure community cards are revealed for evaluation
            for card in self.community_cards: card.face_up = True
            for card in player.hand: card.face_up = True # Reveal hole cards

            combined_cards = player.hand + self.community_cards
            if len(combined_cards) < 5 : # Should not happen in Holdem if river is reached
                 logger.warning(f"Player {player.name} has < 5 cards for showdown.")
                 continue
            
            best_hand = get_best_poker_hand(combined_cards)
            player_hands.append((player, best_hand))
            logger.info(f"Player {player.name}: Hand Rank {best_hand.rank.name}, Values {best_hand.rank_values}, Cards: {[c.id for c in best_hand.hand_cards]}")

        if not player_hands:
             logger.error("No valid hands to evaluate at showdown.")
             self.game_phase = GamePhase.HAND_OVER
             await self.broadcast_game_state()
             return

        # Sort players by hand strength (strongest first)
        player_hands.sort(key=lambda x: x[1], reverse=True)

        # Distribute pot (handles side pots implicitly for now with all-in logic, but full side pot logic is complex)
        # Simple pot distribution: Winner(s) take all. For ties, split pot.
        # This simplified version doesn't handle complex side pots for multiple all-ins correctly.
        # A full side-pot implementation is beyond single-file scope for now.
        
        winners = []
        best_evaluated_hand = player_hands[0][1]
        for p, evaluated_hand in player_hands:
            if not (evaluated_hand < best_evaluated_hand) and not (best_evaluated_hand < evaluated_hand) : # Tie
                winners.append(p)
            else:
                break # Sorted, so no one else can win

        self.hand_winners_info = []
        if winners:
            win_amount_each = self.pot // len(winners)
            remainder = self.pot % len(winners) # Distribute remainder if any (e.g. to first winner)
            
            logger.info(f"Winner(s) of ${self.pot}:")
            for i, winner_player in enumerate(winners):
                actual_win = win_amount_each
                if i == 0 and remainder > 0: actual_win += remainder
                
                winner_player.balance += actual_win
                # Find their hand from player_hands for description
                winning_hand_obj = next(ph for p, ph in player_hands if p.id == winner_player.id)

                win_info = {
                    "player_id": winner_player.id,
                    "player_name": winner_player.name,
                    "amount_won": actual_win,
                    "hand_description": f"{winning_hand_obj.rank.name} ({', '.join(RANKS[v-2] for v in winning_hand_obj.rank_values[:2])})" # Simpler desc
                }
                self.hand_winners_info.append(win_info)
                logger.info(f"- {winner_player.name} with {winning_hand_obj.rank.name} (Cards: {[c.id for c in winning_hand_obj.hand_cards]}), wins ${actual_win}")
        else:
            logger.error("No winners determined at showdown, pot remains.") # Should not happen

        self.pot = 0 # Pot distributed
        self.game_phase = GamePhase.HAND_OVER # Prepare for next hand
        await self.broadcast_game_state()


# --- WebSocket Message Models (Pydantic) ---
class CreateRoomPayload(BaseModel):
    max_players: Optional[int] = Field(default=6, ge=2, le=8) # Poker usually 2-10
    is_private: Optional[bool] = False
    password: Optional[str] = None
    # Poker specific options (future)
    # small_blind: Optional[int] = 10
    # big_blind: Optional[int] = 20

class JoinRoomPayload(BaseModel): room_code: str; password: Optional[str] = None
class SendChatPayload(BaseModel): message: str = Field(..., min_length=1, max_length=200)
class SpectatePayload(BaseModel): room_code: str

class PlayerPokerActionPayload(BaseModel):
    action: PlayerAction
    amount: Optional[int] = Field(default=0, ge=0)

    @validator('amount', pre=True, always=True)
    def ensure_amount_for_bet_raise(cls, v, values):
        action = values.get('action')
        if action in [PlayerAction.BET, PlayerAction.RAISE] and (v is None or v <= 0):
            # Amount here is total bet for the round. Server will calculate actual raise/bet needed.
            # For simplicity, client sends desired total bet. Min value will be validated by server based on game state.
             if v is None or v <=0 : raise ValueError("Amount must be positive for bet/raise.")
        return v


# 3. HELPER FUNCTIONS
def generate_room_code(length: int = 6) -> str:
    return "".join(random.choices(string.ascii_uppercase + string.digits, k=length))

# Connection Manager (simplified)
class ConnectionManager:
    def __init__(self): self.active_connections: Dict[str, WebSocket] = {}
    async def connect(self, ws: WebSocket, p_id: str): await ws.accept(); self.active_connections[p_id] = ws
    def disconnect(self, p_id: str):
        if p_id in self.active_connections: del self.active_connections[p_id]
manager = ConnectionManager()


# 4. FASTAPI APP
app = FastAPI(title="Real-Time Multiplayer Poker Game")

# 5. WEBSOCKET ENDPOINT
@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    player_id = str(uuid.uuid4())
    await manager.connect(websocket, player_id)
    current_room_code: Optional[str] = None
    player_obj_ref: Optional[Player] = None # Keep a ref to the player object once in room

    try:
        while True:
            data = await websocket.receive_json()
            action_name = data.get("action")
            payload = data.get("payload", {})
            
            room: Optional[Room] = None
            room_lock: Optional[asyncio.Lock] = None

            if current_room_code and current_room_code in rooms:
                room_lock = room_locks[current_room_code]
                await room_lock.acquire()
                room = rooms.get(current_room_code)
                if not room:
                    await websocket.send_json({"action": "error", "payload": {"message": "Room closed."}})
                    if room_lock.locked(): room_lock.release()
                    current_room_code = None # No longer in this room
                    continue
                if player_id in room.players: # Update player_obj_ref if they are in room
                    player_obj_ref = room.players[player_id]


            try:
                if action_name == "create_room":
                    async with global_rooms_lock:
                        params = CreateRoomPayload(**payload)
                        room_code = generate_room_code()
                        while room_code in rooms: room_code = generate_room_code()
                        
                        new_room = Room(id=room_code, max_players=params.max_players,
                                        is_private=params.is_private, password=params.password)
                        # SB/BB can be set here from params if added
                        
                        temp_player = Player(id=player_id, name=f"Player_{player_id[:4]}", ws=websocket, balance=1000)
                        new_room.add_player(temp_player) # This sets host and seat
                        player_obj_ref = temp_player
                        
                        rooms[room_code] = new_room
                        room_locks[room_code] = asyncio.Lock()
                        current_room_code = room_code
                    
                    await websocket.send_json({
                        "action": "room_created",
                        "payload": {
                            "room_code": room_code, "player_id": player_id,
                            "room_state": new_room.get_player_view_state(player_id)
                        }
                    })
                    logger.info(f"Player {player_id} created room {room_code}")

                elif action_name == "join_room":
                    params = JoinRoomPayload(**payload)
                    # (Join room logic similar to before, but add_player now handles seat assignment)
                    # On successful join, send "joined_room" with get_player_view_state(player_id)
                    # and broadcast "player_joined" with get_player_view_state(None) to others.
                    # Simplified for brevity, main part is player object now has balance and seat.
                    # Ensure player is created with Player(..., balance=1000)
                    target_room_code = params.room_code
                    async with global_rooms_lock:
                        if target_room_code not in rooms: raise HTTPException(status_code=404, detail="Room not found")
                        target_room_lock = room_locks.get(target_room_code)
                        if not target_room_lock: raise HTTPException(status_code=500, detail="Room lock error")
                    
                    async with target_room_lock:
                        room_to_join = rooms.get(target_room_code)
                        if not room_to_join: raise HTTPException(status_code=404, detail="Room not found")
                        if room_to_join.is_private and room_to_join.password != params.password:
                            raise HTTPException(status_code=403, detail="Incorrect password")
                        
                        new_player = Player(id=player_id, name=f"Player_{player_id[:4]}", ws=websocket, balance=1000)
                        room_to_join.add_player(new_player) # Handles max players, seat
                        player_obj_ref = new_player
                        current_room_code = target_room_code
                    
                    await websocket.send_json({
                        "action": "joined_room",
                        "payload": {
                            "room_code": target_room_code, "player_id": player_id,
                            "room_state": room_to_join.get_player_view_state(player_id)
                        }
                    })
                    # Broadcast full state to everyone as player list and order changed
                    await room_to_join.broadcast_game_state()
                    logger.info(f"Player {player_id} joined room {target_room_code}")

                elif action_name == "spectate":
                    # (Spectate logic similar to before)
                    # On successful spectate, send "spectating_room" with get_player_view_state(None)
                    params = SpectatePayload(**payload)
                    target_room_code = params.room_code
                    async with global_rooms_lock:
                         if target_room_code not in rooms: raise HTTPException(status_code=404, detail="Room not found")
                         target_room_lock = room_locks.get(target_room_code)
                    async with target_room_lock:
                        room_to_spectate = rooms.get(target_room_code)
                        if not room_to_spectate: raise HTTPException(status_code=404, detail="Room not found")
                        room_to_spectate.spectators.append(websocket)
                        current_room_code = target_room_code # To help with cleanup if spectator disconnects
                    await websocket.send_json({
                        "action": "spectating_room",
                        "payload": {"room_state": room_to_spectate.get_player_view_state(None)}
                    })
                    await room_to_spectate.broadcast_game_state() # Update spectator count for others


                # --- Actions requiring user to be in a room AND a registered player ---
                elif room and player_obj_ref: # player_obj_ref is set if player successfully joined/created
                    if action_name == "send_chat":
                        params = SendChatPayload(**payload)
                        chat_message = {"sender_id": player_id, "sender_name": player_obj_ref.name, "message": params.message, "timestamp": asyncio.get_event_loop().time()}
                        room.chat_messages.append(chat_message)
                        # Broadcast only chat message for efficiency if game state is large
                        await room.broadcast({"action": "new_chat_message", "payload": chat_message})
                    
                    # POKER ACTIONS
                    elif action_name == "start_game" and player_obj_ref.is_host:
                        if room.game_phase == GamePhase.WAITING_FOR_PLAYERS or room.game_phase == GamePhase.HAND_OVER:
                            if len(room.player_order) >= 2:
                                await room.start_new_hand()
                                # start_new_hand calls broadcast_game_state
                            else:
                                await websocket.send_json({"action": "error", "payload": {"message": "Need at least 2 players."}})
                        else:
                            await websocket.send_json({"action": "error", "payload": {"message": "Game already in progress."}})
                    
                    elif action_name == "player_bet_action":
                        params = PlayerPokerActionPayload(**payload)
                        await room.handle_player_action(player_id, params.action, params.amount)
                        # handle_player_action will call broadcast_game_state or progress turn
                    
                    # (Placeholder for other actions like "leave_room" if needed explicitly beyond disconnect)
                
                elif action_name == "leave_room": # Explicit leave
                    break # Exit loop, finally block will handle cleanup

                else:
                    await websocket.send_json({"action": "error", "payload": {"message": f"Unknown action '{action_name}' or not in a room properly."}})
            
            except HTTPException as e:
                 await websocket.send_json({"action": "error", "payload": {"message": e.detail}})
            except ValueError as e: # For Pydantic validation errors
                 await websocket.send_json({"action": "error", "payload": {"message": str(e)}})
            except Exception as e:
                logger.error(f"Error processing action {action_name} for player {player_id}: {e}", exc_info=True)
                await websocket.send_json({"action": "error", "payload": {"message": f"Server error: {str(e)}"}})
            finally:
                if room_lock and room_lock.locked():
                    room_lock.release()

    except WebSocketDisconnect:
        logger.info(f"Player {player_id} (WebSocket) disconnected.")
    except Exception as e:
        logger.error(f"Unhandled WebSocket exception for player {player_id}: {e}", exc_info=True)
    finally:
        manager.disconnect(player_id)
        if current_room_code and current_room_code in rooms:
            # Acquire lock for the specific room for cleanup
            async with room_locks.get(current_room_code, asyncio.Lock()): # Get existing or new temp lock if somehow deleted
                room_to_leave = rooms.get(current_room_code)
                if room_to_leave:
                    was_player_in_game = player_id in room_to_leave.players
                    new_host_id_after_leave = None

                    if was_player_in_game:
                        # Player leaving game logic (auto-fold, etc.)
                        player_leaving_obj = room_to_leave.players.get(player_id) # Get obj before removing
                        if player_leaving_obj and room_to_leave.game_phase not in [GamePhase.WAITING_FOR_PLAYERS, GamePhase.HAND_OVER] and not player_leaving_obj.folded:
                             player_leaving_obj.folded = True
                             logger.info(f"Player {player_id} disconnected mid-hand, auto-folding.")
                             # If it was their turn, game needs to advance
                             if room_to_leave.current_player_turn_id == player_id:
                                 # This should be scheduled as a task to not block disconnect
                                 asyncio.create_task(room_to_leave._handle_player_fold_or_leave(player_leaving_obj))
                        
                        new_host_id_after_leave = room_to_leave.remove_player(player_id)
                        logger.info(f"Player {player_id} removed from room {current_room_code}.")
                    
                    if websocket in room_to_leave.spectators:
                        room_to_leave.spectators.remove(websocket)
                        logger.info(f"WebSocket (player {player_id}) removed from spectators of room {current_room_code}.")

                    if not room_to_leave.players and not room_to_leave.spectators:
                        async with global_rooms_lock: # Lock for modifying 'rooms' dict
                            if current_room_code in rooms:
                                del rooms[current_room_code]
                                if current_room_code in room_locks: del room_locks[current_room_code]
                                logger.info(f"Room {current_room_code} closed as it's empty.")
                    elif was_player_in_game: # Only broadcast if a game player left
                        # Update game state for remaining players (e.g., new host, player list)
                        # The check_hand_end_due_to_folds or _handle_player_fold_or_leave should trigger necessary state updates.
                        # For now, a general broadcast to reflect player list change.
                        await room_to_leave.broadcast_game_state()
        
        if websocket.application_state != StarletteWebSocketState.DISCONNECTED:
            try: await websocket.close()
            except Exception: pass


# 6. HTTP ENDPOINT FOR FRONTEND
HTML_CONTENT_POKER = """
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Real-Time Poker Game</title>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js"></script>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/tween.js/18.6.4/tween.umd.js"></script>
    <style>
        body { margin: 0; font-family: 'Segoe UI', Tahoma, Geneva, Verdana, sans-serif; display: flex; height: 100vh; background-color: #1a1a1a; color: #e0e0e0; }
        #game-container { flex-grow: 1; position: relative; background:radial-gradient(ellipse at center, #2c3e50 0%,#000000 100%);}
        #canvas-container { width: 100%; height: 100%; }
        #ui-container { width: 380px; background-color: #2b2b2b; padding: 15px; display: flex; flex-direction: column; overflow-y: auto; border-left: 2px solid #444; }
        .ui-section { margin-bottom: 15px; padding: 12px; background-color: #3c3c3c; border-radius: 6px; box-shadow: 0 2px 4px rgba(0,0,0,0.2); }
        h2, h3 { margin-top: 0; border-bottom: 1px solid #555; padding-bottom: 8px; color: #00aaff; }
        button, input[type="text"], input[type="password"], input[type="number"] { padding: 10px; margin: 6px 0; border-radius: 4px; border: 1px solid #555; background-color: #4f4f4f; color: #e0e0e0; }
        input[type="text"], input[type="password"], input[type="number"] { width: calc(100% - 22px); }
        button { background-color: #007bff; color: white; cursor: pointer; transition: background-color 0.2s ease; }
        button:hover { background-color: #0056b3; }
        button:disabled { background-color: #555; cursor: not-allowed; }
        button.secondary { background-color: #6c757d; }
        button.secondary:hover { background-color: #545b62; }
        button.action-btn { margin-right: 5px; padding: 8px 12px; font-size: 0.9em;}
        #chat-messages { height: 120px; overflow-y: scroll; border: 1px solid #555; padding: 8px; margin-bottom: 8px; background-color: #2a2a2a; border-radius: 4px;}
        .chat-message { margin-bottom: 6px; font-size: 0.9em; }
        .chat-message .sender { font-weight: bold; color: #7fdbff; } /* Light blue */
        #player-info { font-size: 1em; margin-bottom: 10px; padding: 8px; background-color: #444; border-radius: 4px; }
        .player-list-item { list-style: none; padding: 5px 0; border-bottom: 1px solid #4a4a4a; font-size:0.9em;}
        .player-list-item:last-child { border-bottom: none; }
        .player-list-item.is-host strong { color: #ffc107; } /* Gold for host */
        .player-list-item.is-turn { background-color: #005b8f; padding-left:5px; border-radius:3px;}
        .player-list-item.folded { text-decoration: line-through; color: #888; }
        .player-list-item .balance { color: #28a745; font-weight: bold; } /* Green for balance */
        .player-list-item .bet { color: #ffc107; } /* Yellow for bet */
        #game-status-info { padding: 10px; background-color: #444; border-radius: 4px; margin-bottom: 10px; }
        #game-status-info p { margin: 4px 0; font-size: 0.95em; }
        #community-cards-ui, #pot-ui { font-weight: bold; color: #00aaff; }
        #action-buttons button { margin: 5px; }
        .winner-info { background-color: #28a745; color: white; padding: 10px; margin-top:10px; border-radius: 5px; text-align: center; }
    </style>
</head>
<body>
    <div id="game-container">
        <div id="canvas-container"></div>
    </div>
    <div id="ui-container">
        <div class="ui-section">
            <h2>Connection</h2>
            <input type="text" id="room-code-input" placeholder="Room Code (blank to create)">
            <input type="password" id="room-password-input" placeholder="Password (optional)">
            <button id="connect-button">Create/Join Room</button>
            <button id="spectate-button">Spectate Room</button>
            <div id="player-info">Status: Not connected.</div>
        </div>

        <div class="ui-section" id="room-info-section" style="display:none;">
            <h3>Room: <span id="current-room-code"></span> (<span id="game-phase-ui"></span>)</h3>
            <p>Max: <span id="max-players-info"></span> | Private: <span id="is-private-info"></span> | Specs: <span id="spectator-count">0</span></p>
            <h4>Players (<span id="player-count">0</span>):</h4>
            <ul id="player-list"></ul>
            <button id="leave-room-button" class="secondary">Leave Room</button>
            <button id="start-game-button" style="display:none;" class="action-btn">Start Game</button>
        </div>
        
        <div class="ui-section" id="gameplay-section" style="display:none;">
            <h3>Game Status</h3>
            <div id="game-status-info">
                <p>Pot: <span id="pot-ui">$0</span></p>
                <p>Community Cards: <span id="community-cards-ui">None</span></p>
                <p>To Call: <span id="to-call-ui">$0</span> | Min Raise: <span id="min-raise-ui">$0</span></p>
            </div>
            <div id="winner-display"></div>

            <h3>Your Actions</h3>
            <div id="action-buttons" style="display:none;">
                <button id="fold-button" class="action-btn secondary">Fold</button>
                <button id="check-button" class="action-btn">Check</button>
                <button id="call-button" class="action-btn">Call</button>
                <input type="number" id="bet-amount-input" placeholder="Amount" style="width: 80px; margin-right:5px;">
                <button id="bet-button" class="action-btn">Bet</button>
                <button id="raise-button" class="action-btn">Raise</button>
            </div>
        </div>

        <div class="ui-section" id="chat-section" style="display:none;">
            <h3>Chat</h3>
            <div id="chat-messages"></div>
            <input type="text" id="chat-input" placeholder="Type message...">
            <button id="send-chat-button">Send</button>
        </div>
    </div>

    <script type="module">
        // Three.js, TWEEN.js are global via CDN
        const THREE = window.THREE;
        const TWEEN = window.TWEEN;

        let scene, camera, renderer, raycaster, mouse;
        let ws;
        let myPlayerId = null;
        let currentRoomState = null;
        
        const cardObjects = {}; // { cardId: { mesh: THREE.Mesh, data: CardData } }
        const chipObjects = {}; // { playerId_or_pot: THREE.Group of chip meshes }
        const playerPositions = []; // Store {x,y,z} for each seat index
        const playerInfoMeshes = {}; // { playerId: THREE.Sprite for name/balance }

        const cardDimensions = { width: 0.5, height: 0.7, depth: 0.015 };
        const chipRadius = 0.08; const chipHeight = 0.03;

        // --- WebSocket Logic ---
        function connectWebSocket() {
            const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
            ws = new WebSocket(`${protocol}//${window.location.host}/ws`);
            ws.onopen = () => { console.log("WebSocket connected."); document.getElementById('player-info').textContent = "Status: Connected. Create or join room."; };
            ws.onmessage = (event) => { const data = JSON.parse(event.data); console.log("Received:", data); handleWebSocketMessage(data); };
            ws.onclose = () => { console.log("WebSocket disconnected."); myPlayerId = null; currentRoomState = null; updateUIForConnectionState(false); clearScene(); document.getElementById('player-info').textContent = "Status: Disconnected. Refresh."; };
            ws.onerror = (error) => { console.error("WebSocket error:", error); document.getElementById('player-info').textContent = "Status: Connection error.";};
        }

        function sendMessage(action, payload) {
            if (ws && ws.readyState === WebSocket.OPEN) ws.send(JSON.stringify({ action, payload }));
            else console.error("WebSocket not connected.");
        }

        function handleWebSocketMessage(data) {
            const { action, payload } = data;
            switch (action) {
                case "error": alert(`Error: ${payload.message}`); break;
                case "room_created": case "joined_room":
                    myPlayerId = payload.player_id;
                    currentRoomState = payload.room_state;
                    document.getElementById('player-info').textContent = `My ID: ${myPlayerId.substring(0,8)}. Balance: $${currentRoomState.players.find(p=>p.id===myPlayerId)?.balance || 'N/A'}`;
                    updateUIForConnectionState(true, currentRoomState.host_id === myPlayerId);
                    updateFullUI(currentRoomState);
                    synchronizeFullScene(currentRoomState);
                    break;
                case "spectating_room":
                    currentRoomState = payload.room_state;
                    myPlayerId = null; // Spectator
                    document.getElementById('player-info').textContent = `Spectating Room: ${currentRoomState.room_id}`;
                    updateUIForConnectionState(true, false, true);
                    updateFullUI(currentRoomState);
                    synchronizeFullScene(currentRoomState);
                    break;
                case "game_state_update":
                    currentRoomState = payload; // Payload is the full room state
                    updateFullUI(currentRoomState);
                    synchronizeFullScene(currentRoomState);
                     if (myPlayerId && currentRoomState.players.find(p=>p.id===myPlayerId)) {
                        document.getElementById('player-info').textContent = `My ID: ${myPlayerId.substring(0,8)}. Balance: $${currentRoomState.players.find(p=>p.id===myPlayerId).balance}`;
                    }
                    break;
                case "hole_cards_dealt": // Specific to player, cards are in payload.cards
                    // Server's game_state_update will include player's hand count but not details
                    // This message provides the actual card data for the player's own hand.
                    // We need to merge this into local currentRoomState if player matches.
                    if (myPlayerId && currentRoomState) {
                        const me = currentRoomState.players.find(p => p.id === myPlayerId);
                        if (me) {
                            me.hand = payload.cards; // Update local hand with actual card data
                             // Animate these specific cards. synchronizeFullScene will handle general positioning.
                            payload.cards.forEach(cardData => animateCardDeal(cardData, me.seat_index, me.hand.indexOf(cardData)));
                        }
                    }
                    updateFullUI(currentRoomState); // Re-render UI which might use hand details
                    break;
                case "new_chat_message": appendChatMessage(payload); break;
                // Other specific animations or updates can be handled here.
            }
        }

        // --- UI Logic ---
        document.getElementById('connect-button').onclick = () => {
            const roomCode = document.getElementById('room-code-input').value.trim();
            const password = document.getElementById('room-password-input').value;
            if (roomCode) sendMessage("join_room", { room_code: roomCode, password: password || undefined });
            else sendMessage("create_room", { password: password || undefined });
        };
        document.getElementById('spectate-button').onclick = () => {
            const roomCode = document.getElementById('room-code-input').value.trim();
            if (roomCode) sendMessage("spectate", { room_code: roomCode });
            else alert("Enter Room Code to spectate.");
        };
        document.getElementById('leave-room-button').onclick = () => sendMessage("leave_room", {});
        document.getElementById('start-game-button').onclick = () => sendMessage("start_game", {});
        document.getElementById('send-chat-button').onclick = () => {
            const msg = document.getElementById('chat-input').value;
            if(msg) { sendMessage("send_chat", { message: msg }); document.getElementById('chat-input').value = ""; }
        };
         document.getElementById('chat-input').onkeypress = (e) => {if (e.key === 'Enter') document.getElementById('send-chat-button').click();};


        // Poker action buttons
        document.getElementById('fold-button').onclick = () => sendMessage("player_bet_action", { action: "fold" });
        document.getElementById('check-button').onclick = () => sendMessage("player_bet_action", { action: "check" });
        document.getElementById('call-button').onclick = () => sendMessage("player_bet_action", { action: "call" });
        document.getElementById('bet-button').onclick = () => {
            const amount = parseInt(document.getElementById('bet-amount-input').value);
            if (!isNaN(amount) && amount > 0) sendMessage("player_bet_action", { action: "bet", amount: amount });
            else alert("Invalid bet amount.");
        };
        document.getElementById('raise-button').onclick = () => {
            const amount = parseInt(document.getElementById('bet-amount-input').value);
            if (!isNaN(amount) && amount > 0) sendMessage("player_bet_action", { action: "raise", amount: amount });
            else alert("Invalid raise amount.");
        };


        function updateUIForConnectionState(isConnected, isHost = false, isSpectator = false) {
            document.getElementById('room-info-section').style.display = isConnected ? 'block' : 'none';
            document.getElementById('chat-section').style.display = isConnected ? 'block' : 'none';
            document.getElementById('gameplay-section').style.display = isConnected && !isSpectator ? 'block' : 'none';
            document.getElementById('start-game-button').style.display = isConnected && isHost && !isSpectator ? 'inline-block' : 'none';
            
            document.getElementById('connect-button').disabled = isConnected;
            document.getElementById('spectate-button').disabled = isConnected;
        }

        function updateFullUI(state) {
            if (!state) return;
            document.getElementById('current-room-code').textContent = state.room_id;
            document.getElementById('game-phase-ui').textContent = state.game_phase.replace(/_/g, ' ');
            document.getElementById('max-players-info').textContent = state.max_players;
            document.getElementById('is-private-info').textContent = state.is_private ? 'Yes' : 'No';
            document.getElementById('spectator-count').textContent = state.spectator_count || 0;
            document.getElementById('player-count').textContent = state.players.length;

            const playerListUL = document.getElementById('player-list');
            playerListUL.innerHTML = "";
            state.players.forEach(p => {
                const li = document.createElement('li');
                li.className = 'player-list-item';
                let namePrefix = "";
                if (p.id === state.dealer_button_player_id) namePrefix += "D ";
                if (p.id === myPlayerId) namePrefix = "YOU " + namePrefix;
                
                li.innerHTML = `${namePrefix}<strong>${p.name}</strong> (Seat ${p.seat_index}) 
                              <span class="balance">$${p.balance}</span> 
                              ${p.current_bet_in_round > 0 ? `<span class="bet">Bet: $${p.current_bet_in_round}</span>` : ''}
                              ${p.is_all_in ? '<span style="color:red;">ALL-IN</span>' : ''}`;
                if (p.id === state.current_player_turn_id) li.classList.add('is-turn');
                if (p.folded) li.classList.add('folded');
                if (p.is_host) li.classList.add('is-host');
                playerListUL.appendChild(li);
            });

            document.getElementById('pot-ui').textContent = `$${state.pot}`;
            document.getElementById('community-cards-ui').textContent = state.community_cards.length > 0 ? state.community_cards.map(c => c.id.replace('_','')).join(' ') : "None";
            document.getElementById('to-call-ui').textContent = `$${Math.max(0, state.current_bet_to_match - (myPlayerId && state.players.find(p=>p.id===myPlayerId)?.current_bet_in_round || 0) )}`;
            document.getElementById('min-raise-ui').textContent = `$${state.min_raise_amount}`;

            const winnerDisplay = document.getElementById('winner-display');
            winnerDisplay.innerHTML = "";
            if (state.game_phase === "HAND_OVER" && state.hand_winners_info && state.hand_winners_info.length > 0) {
                state.hand_winners_info.forEach(winfo => {
                    const div = document.createElement('div');
                    div.className = 'winner-info';
                    div.textContent = `${winfo.player_name} wins $${winfo.amount_won} with ${winfo.hand_description}`;
                    winnerDisplay.appendChild(div);
                });
            }


            // Action buttons visibility
            const actionButtonsDiv = document.getElementById('action-buttons');
            const me = myPlayerId ? state.players.find(p => p.id === myPlayerId) : null;
            if (me && state.current_player_turn_id === myPlayerId && !me.folded && !me.is_all_in) {
                actionButtonsDiv.style.display = 'block';
                const toCall = state.current_bet_to_match - me.current_bet_in_round;
                document.getElementById('check-button').style.display = toCall <= 0 ? 'inline-block' : 'none';
                document.getElementById('call-button').style.display = toCall > 0 ? 'inline-block' : 'none';
                if (toCall > 0) document.getElementById('call-button').textContent = `Call $${toCall}`;
                
                // Bet/Raise logic: if current_bet_to_match is 0, it's a BET. Otherwise, RAISE.
                document.getElementById('bet-button').style.display = state.current_bet_to_match === 0 ? 'inline-block' : 'none';
                document.getElementById('raise-button').style.display = state.current_bet_to_match > 0 ? 'inline-block' : 'none';
                document.getElementById('bet-amount-input').min = state.current_bet_to_match + state.min_raise_amount; // Min total bet
                document.getElementById('bet-amount-input').value = state.current_bet_to_match + state.min_raise_amount;


            } else {
                actionButtonsDiv.style.display = 'none';
            }
            document.getElementById('start-game-button').disabled = !(state.game_phase === "WAITING_FOR_PLAYERS" || state.game_phase === "HAND_OVER");

        }

        function appendChatMessage(msg) { /* Same as before */ 
            const chatDiv = document.getElementById('chat-messages');
            const msgDiv = document.createElement('div'); msgDiv.className = 'chat-message';
            const senderSpan = document.createElement('span'); senderSpan.className = 'sender';
            senderSpan.textContent = `${msg.sender_name || msg.sender_id}: `;
            msgDiv.appendChild(senderSpan); msgDiv.append(document.createTextNode(msg.message));
            chatDiv.appendChild(msgDiv); chatDiv.scrollTop = chatDiv.scrollHeight;
        }

        // --- Three.js Scene Logic ---
        function initThreeJS() {
            const container = document.getElementById('canvas-container');
            scene = new THREE.Scene();
            // scene.background = new THREE.Color(0x282c34); // Darker for poker

            camera = new THREE.PerspectiveCamera(60, container.clientWidth / container.clientHeight, 0.1, 1000);
            camera.position.set(0, 4.5, 5.5); // Higher, more angled view for table
            camera.lookAt(0, 0, 0);

            renderer = new THREE.WebGLRenderer({ antialias: true, alpha: true }); // Alpha for background gradient
            renderer.setSize(container.clientWidth, container.clientHeight);
            renderer.shadowMap.enabled = true;
            container.appendChild(renderer.domElement);

            // Lighting
            const ambientLight = new THREE.AmbientLight(0xffffff, 0.7); scene.add(ambientLight);
            const spotLight = new THREE.SpotLight(0xffffff, 0.8, 20, Math.PI / 4, 1, 2);
            spotLight.position.set(0, 10, 0); spotLight.castShadow = true; scene.add(spotLight);
            // const dirLight = new THREE.DirectionalLight(0xffffff, 0.5); 
            // dirLight.position.set(3,5,2); dirLight.castShadow = true; scene.add(dirLight);


            // Poker Table
            const tableGeometry = new THREE.CylinderGeometry(3.5, 3.5, 0.2, 64); // Wider, thinner
            const tableMaterial = new THREE.MeshStandardMaterial({ color: 0x006000 }); // Dark green felt
            const table = new THREE.Mesh(tableGeometry, tableMaterial);
            table.position.y = -0.1; table.receiveShadow = true; scene.add(table);
            const tableEdgeGeometry = new THREE.CylinderGeometry(3.6, 3.6, 0.25, 64);
            const tableEdgeMaterial = new THREE.MeshStandardMaterial({color: 0x503010}); // Wood color
            const tableEdge = new THREE.Mesh(tableEdgeGeometry, tableEdgeMaterial);
            tableEdge.position.y = -0.125; scene.add(tableEdge);


            // Define player seat positions (example for 6 players)
            const radius = 2.8;
            for (let i = 0; i < 6; i++) { // Max players = 6 for this example layout
                const angle = (i / 6) * Math.PI * 2;
                playerPositions.push({
                    x: radius * Math.cos(angle),
                    y: cardDimensions.height / 2 + 0.02, // Slightly above table for cards
                    z: radius * Math.sin(angle),
                    rotationY: -angle + Math.PI/2 // Cards face center
                });
            }
            
            // Placeholder for deck
            const deckPlaceholderGeo = new THREE.BoxGeometry(cardDimensions.width*1.2, 0.3, cardDimensions.height*1.2);
            const deckPlaceholderMat = new THREE.MeshStandardMaterial({color:0x444444, transparent:true, opacity:0.5});
            const deckPlaceholder = new THREE.Mesh(deckPlaceholderGeo, deckPlaceholderMat);
            deckPlaceholder.position.set(-1.5, 0.15, 0);
            scene.add(deckPlaceholder);
            deckPlaceholder.name = "deck_placeholder";


            // Raycasting (if needed for card interaction, less crucial for poker UI buttons)
            // window.addEventListener('resize', onWindowResize, false); // Add if needed
            animate();
        }
        
        function animate() { requestAnimationFrame(animate); TWEEN.update(); renderer.render(scene, camera); }

        function createCardTexture(suit, rank, isFaceUp, cardWidthPx = 100, cardHeightPx = 140) {
            // (Same as before, ensure it handles suit/rank being null for back)
            const canvas = document.createElement('canvas'); canvas.width = cardWidthPx; canvas.height = cardHeightPx;
            const ctx = canvas.getContext('2d');
            ctx.fillStyle = isFaceUp ? '#FEFEFE' : '#B22222'; // White face, Dark Red back
            ctx.fillRect(0, 0, cardWidthPx, cardHeightPx);
            ctx.strokeStyle = '#333'; ctx.lineWidth = 2; ctx.strokeRect(1, 1, cardWidthPx - 2, cardHeightPx - 2);

            if (isFaceUp && suit && rank) {
                let suitColor = (suit === 'H' || suit === 'D') ? 'red' : 'black';
                ctx.fillStyle = suitColor; ctx.font = 'bold 18px Arial';
                let suitSymbol = {'H':'♥','D':'♦','C':'♣','S':'♠'}[suit] || '';
                ctx.textAlign = 'left'; ctx.fillText(rank, 8, 22); ctx.fillText(suitSymbol, 8, 42);
                ctx.textAlign = 'right'; ctx.scale(-1,1); ctx.fillText(rank, -cardWidthPx + 8, cardHeightPx -10); ctx.scale(-1,1); // Bottom right rank
                ctx.font = 'bold 30px Arial'; ctx.textAlign = 'center'; ctx.fillText(suitSymbol, cardWidthPx/2, cardHeightPx/2 + 10);
            } else if(!isFaceUp) { /* complex back pattern */ 
                ctx.strokeStyle = 'rgba(255,255,255,0.3)'; ctx.lineWidth=1;
                for(let i=0; i<cardWidthPx; i+=10) { ctx.beginPath(); ctx.moveTo(i,0); ctx.lineTo(i,cardHeightPx); ctx.stroke(); }
                for(let j=0; j<cardHeightPx; j+=10) { ctx.beginPath(); ctx.moveTo(0,j); ctx.lineTo(cardWidthPx,j); ctx.stroke(); }
            }
            return new THREE.CanvasTexture(canvas);
        }
        
        function createOrUpdateCardMesh(cardData) {
            let cardObj = cardObjects[cardData.id];
            if (!cardObj) {
                const geometry = new THREE.BoxGeometry(cardDimensions.width, cardDimensions.height, cardDimensions.depth);
                const materials = [ // Order: px, nx, py, ny, pz (front), nz (back)
                    new THREE.MeshStandardMaterial({color:0xcccccc}), new THREE.MeshStandardMaterial({color:0xcccccc}),
                    new THREE.MeshStandardMaterial({color:0xcccccc}), new THREE.MeshStandardMaterial({color:0xcccccc}),
                    new THREE.MeshStandardMaterial({ map: createCardTexture(cardData.suit, cardData.rank, cardData.face_up) }), // Front face
                    new THREE.MeshStandardMaterial({ map: createCardTexture(null, null, false) })  // Back face
                ];
                const mesh = new THREE.Mesh(geometry, materials);
                mesh.castShadow = true; mesh.userData.cardId = cardData.id;
                scene.add(mesh);
                cardObj = { mesh: mesh, data: cardData };
                cardObjects[cardData.id] = cardObj;
                 // Initial position (e.g. deck)
                const deckPos = scene.getObjectByName("deck_placeholder")?.position || new THREE.Vector3(-1.5,0.1,0);
                mesh.position.copy(deckPos);
                mesh.position.y += 0.2; // Above deck
            } else { // Update existing card
                cardObj.data = cardData; // Update data reference
                cardObj.mesh.material[4].map = createCardTexture(cardData.suit, cardData.rank, cardData.face_up);
                cardObj.mesh.material[4].map.needsUpdate = true;
                // Back texture is constant, but if card flips, the front material (index 4) shows back if face_up is false
            }
            
            // Position and animate card
            positionCard(cardObj.mesh, cardData);
            return cardObj.mesh;
        }

        function positionCard(mesh, cardData, animate = true) {
            let targetPos = new THREE.Vector3();
            let targetRot = new THREE.Euler();
            const player = currentRoomState.players.find(p => p.id === cardData.owner_id);

            if (cardData.owner_id === "deck") { // Should not happen often here, deck is abstract
                const deckGfxPos = scene.getObjectByName("deck_placeholder")?.position || new THREE.Vector3(-1.5,0.1,0);
                targetPos.copy(deckGfxPos);
                targetPos.y += cardData.position.z || 0; // Stack in deck visual
                targetRot.set(Math.PI / 2, 0, 0); // Lay flat
            } else if (cardData.owner_id === "community") {
                const communityCardIndex = currentRoomState.community_cards.findIndex(c => c.id === cardData.id);
                targetPos.set(-1 + communityCardIndex * (cardDimensions.width + 0.1), 0.01, 0); // Center of table
                targetRot.set(Math.PI / 2, 0, 0); // Lay flat, face up
                 if (!cardData.face_up) targetRot.y = Math.PI; // Spin if face down initially (should not happen for community)
            } else if (player) { // Player's hand
                const seat = playerPositions[player.seat_index];
                if (!seat) { console.error("Invalid seat index for player", player); return; }
                
                const handCardIndex = player.hand.findIndex(c => c.id === cardData.id);
                const isMyCard = player.id === myPlayerId;

                targetPos.set(
                    seat.x + (handCardIndex - (player.hand.length - 1) / 2) * (cardDimensions.width * (isMyCard ? 0.6 : 0.3)), // Tighter spread for others
                    seat.y, 
                    seat.z
                );
                if (isMyCard) targetPos.y += 0.05; // Slightly raise my cards

                targetRot.set(isMyCard ? Math.PI / 2.5 : Math.PI / 2, seat.rotationY, 0); // Tilt my cards, others flat from my view
                
                // If card is face down for me (shouldn't be if it's my hand and dealt) or for others, apply Y rotation
                if (!cardData.face_up || (player.id !== myPlayerId && !currentRoomState.game_phase === "SHOWDOWN")) {
                     //This rotation flips the card around its local Y after X rotation
                     //targetRot.z += Math.PI; // This flips it over its width axis
                     // Better: ensure texture on material[4] is correct (face or back) based on face_up
                }
            } else { // Card is on table (e.g. discarded, though not used in poker)
                targetPos.set(cardData.position.x, cardDimensions.depth/2, cardData.position.y);
                targetRot.set(Math.PI / 2, 0, cardData.face_up ? 0 : Math.PI);
            }

            if(animate) {
                new TWEEN.Tween(mesh.position).to(targetPos, 600).easing(TWEEN.Easing.Quadratic.Out).start();
                new TWEEN.Tween(mesh.rotation).to({x: targetRot.x, y: targetRot.y, z: targetRot.z}, 600).easing(TWEEN.Easing.Quadratic.Out).start();
            } else {
                mesh.position.copy(targetPos);
                mesh.rotation.copy(targetRot);
            }
        }
        
        function animateCardDeal(cardData, seatIndex, handCardIndex) {
            // Animate from deck to player
            const cardMesh = cardObjects[cardData.id]?.mesh;
            if(!cardMesh) return;

            const deckPos = scene.getObjectByName("deck_placeholder")?.position.clone() || new THREE.Vector3(-1.5,0.1,0);
            deckPos.y += 0.5; // Start above deck
            cardMesh.position.copy(deckPos);
            cardMesh.rotation.set(Math.PI/2, 0, 0); // Start flat like on deck

            const player = currentRoomState.players.find(p => p.seat_index === seatIndex);
            if(!player) return;
            
            const seat = playerPositions[seatIndex];
            const targetPos = new THREE.Vector3(
                 seat.x + (handCardIndex - (player.hand_card_count -1 ) / 2) * (cardDimensions.width * (player.id === myPlayerId ? 0.6:0.3)),
                 seat.y,
                 seat.z
            );
             const isMyCard = player.id === myPlayerId;
             const targetRot = new THREE.Euler(isMyCard ? Math.PI / 2.5 : Math.PI / 2, seat.rotationY, 0);


            // Mid-point for arc animation
            const midPos = targetPos.clone().add(deckPos).multiplyScalar(0.5);
            midPos.y += 1.0; // Arc upwards

            new TWEEN.Tween(cardMesh.position)
                .to({ x: [midPos.x, targetPos.x], y: [midPos.y, targetPos.y], z: [midPos.z, targetPos.z] }, 800)
                .interpolation(TWEEN.Interpolation.Bezier)
                .easing(TWEEN.Easing.Quadratic.Out)
                .start();
            new TWEEN.Tween(cardMesh.rotation)
                .to({x: targetRot.x, y: targetRot.y, z: targetRot.z}, 800)
                .easing(TWEEN.Easing.Quadratic.Out)
                .onComplete(() => { // After animation, update texture if it's my card being revealed
                    if(isMyCard && cardData.face_up) {
                        cardMesh.material[4].map = createCardTexture(cardData.suit, cardData.rank, true);
                        cardMesh.material[4].map.needsUpdate = true;
                    }
                })
                .start();
        }


        function synchronizeFullScene(state) {
            if (!state) return;
            const allServerCardIds = new Set();
            state.players.forEach(p => p.hand.forEach(c => allServerCardIds.add(c.id)));
            state.community_cards.forEach(c => allServerCardIds.add(c.id));

            // Remove stale cards
            for (const cardId in cardObjects) {
                if (!allServerCardIds.has(cardId)) {
                    scene.remove(cardObjects[cardId].mesh);
                    delete cardObjects[cardId];
                }
            }

            // Update/create cards
            state.players.forEach(p => {
                p.hand.forEach(cardData => {
                    const mesh = createOrUpdateCardMesh(cardData);
                    // Animation for dealing is handled by 'hole_cards_dealt' or specific logic.
                    // Here, we just ensure position for existing cards or newly joined player's view.
                    // positionCard(mesh, cardData, false); // Use false if specific deal animations are primary
                });
            });
            state.community_cards.forEach((cardData, index) => {
                const mesh = createOrUpdateCardMesh(cardData);
                 // Animate community cards appearing (e.g. from deck spot)
                const deckPos = scene.getObjectByName("deck_placeholder")?.position.clone() || new THREE.Vector3(-1.5,0.1,0);
                deckPos.y += 0.5;
                
                const existingCardObj = cardObjects[cardData.id];
                if(existingCardObj && !existingCardObj.initialPositionSet) { // Only animate if newly added to scene
                    mesh.position.copy(deckPos); // Start at deck
                    positionCard(mesh, cardData, true); // Animate to its spot
                    existingCardObj.initialPositionSet = true;
                } else {
                    positionCard(mesh, cardData, false); // Just snap if already there or re-sync
                }

            });

            // Update chips and player info displays
            updateAllPlayerChipDisplays(state.players);
            updatePotChips(state.pot);
            updatePlayerInfoMeshes(state.players);
        }
        
        function createChipStack(amount, basePosition, color = 0xffcc00) {
            const stackGroup = new THREE.Group();
            const numChips = Math.max(1, Math.min(15, Math.ceil(amount / (currentRoomState?.big_blind_amount || 20) / 2))); // Max 15 visual chips
            for (let i = 0; i < numChips; i++) {
                const geometry = new THREE.CylinderGeometry(chipRadius, chipRadius, chipHeight, 16);
                const material = new THREE.MeshStandardMaterial({ color: color });
                const chip = new THREE.Mesh(geometry, material);
                chip.position.set(basePosition.x, basePosition.y + i * chipHeight + chipHeight/2, basePosition.z);
                chip.castShadow = true;
                stackGroup.add(chip);
            }
            return stackGroup;
        }

        function updateAllPlayerChipDisplays(players) {
            players.forEach(player => {
                if (chipObjects["player_" + player.id]) scene.remove(chipObjects["player_" + player.id]);
                if (player.current_bet_in_round > 0 && player.seat_index !== -1) {
                    const seatPos = playerPositions[player.seat_index];
                    const chipBasePos = new THREE.Vector3(seatPos.x * 0.8, 0, seatPos.z * 0.8); // Closer to center from player
                    chipObjects["player_" + player.id] = createChipStack(player.current_bet_in_round, chipBasePos, 0x007bff);
                    scene.add(chipObjects["player_" + player.id]);
                }
            });
        }

        function updatePotChips(potAmount) {
            if (chipObjects["pot"]) scene.remove(chipObjects["pot"]);
            if (potAmount > 0) {
                chipObjects["pot"] = createChipStack(potAmount, new THREE.Vector3(0, 0, -0.5), 0x28a745); // Green chips for pot
                scene.add(chipObjects["pot"]);
            }
        }
        
        function makeTextSprite(message, params) {
            // Simplified from examples: create canvas, draw text, use as sprite material
            const fontface = params.fontface || "Arial";
            const fontsize = params.fontsize || 18;
            const R = params.textColor ? params.textColor.R : 0;
            const G = params.textColor ? params.textColor.G : 0;
            const B = params.textColor ? params.textColor.B : 0;
            const A = params.textColor ? params.textColor.A : 1;

            const canvas = document.createElement('canvas');
            const context = canvas.getContext('2d');
            context.font = "Bold " + fontsize + "px " + fontface;
            const metrics = context.measureText(message);
            canvas.width = metrics.width + params.padding || 0; // Add padding
            canvas.height = fontsize + params.padding || 0;
            context.font = "Bold " + fontsize + "px " + fontface; // Re-set font after canvas resize
            context.fillStyle = `rgba(${params.backgroundColor.r}, ${params.backgroundColor.g}, ${params.backgroundColor.b}, ${params.backgroundColor.a})`;
            context.fillRect(0,0,canvas.width, canvas.height);
            context.fillStyle = `rgba(${R},${G},${B},${A})`;
            context.fillText(message, params.padding/2, fontsize + params.padding/2 - (fontsize/8) /* rough baseline adj */); // Draw text with padding

            const texture = new THREE.Texture(canvas);
            texture.needsUpdate = true;
            const spriteMaterial = new THREE.SpriteMaterial({ map: texture });
            const sprite = new THREE.Sprite(spriteMaterial);
            sprite.scale.set(canvas.width/100 * (params.scale || 1) , canvas.height/100 * (params.scale || 1), 1.0); // Adjust scale
            return sprite;
        }

        function updatePlayerInfoMeshes(players) {
            players.forEach(player => {
                if (playerInfoMeshes[player.id]) scene.remove(playerInfoMeshes[player.id]);
                if (player.seat_index !== -1) {
                    const seatPos = playerPositions[player.seat_index];
                    const text = `${player.name}\n$${player.balance}`;
                    const sprite = makeTextSprite(text, {
                        fontsize: 24, fontface: "Arial", padding: 8,
                        textColor: { R: 230, G: 230, B: 230, A: 1 },
                        backgroundColor: { r: 50, g: 50, b: 50, a: 0.7 },
                        scale: 1.8
                    });
                    sprite.position.set(seatPos.x, seatPos.y + 0.7, seatPos.z); // Position above player seat
                    playerInfoMeshes[player.id] = sprite;
                    scene.add(sprite);
                }
            });
             // Remove info for players no longer in state
            Object.keys(playerInfoMeshes).forEach(pid => {
                if (!players.find(p => p.id === pid)) {
                    scene.remove(playerInfoMeshes[pid]);
                    delete playerInfoMeshes[pid];
                }
            });
        }


        function clearScene() {
            Object.values(cardObjects).forEach(co => scene.remove(co.mesh));
            Object.keys(cardObjects).forEach(key => delete cardObjects[key]);
            Object.values(chipObjects).forEach(group => scene.remove(group));
            Object.keys(chipObjects).forEach(key => delete chipObjects[key]);
            Object.values(playerInfoMeshes).forEach(mesh => scene.remove(mesh));
            Object.keys(playerInfoMeshes).forEach(key => delete playerInfoMeshes[key]);
            // Remove deck placeholder if it's a dynamic object
        }
        
        // --- Initialization ---
        initThreeJS();
        connectWebSocket();

    </script>
</body>
</html>
"""

@app.get("/", response_class=HTMLResponse)
async def get_frontend_poker():
    return HTML_CONTENT_POKER

# 7. MAIN EXECUTION BLOCK (No change)
if __name__ == "__main__":
    import uvicorn
    logger.info(f"Starting Poker server on http://localhost:{PORT}")
    # Consider using workers for production, but for single file dev, this is fine.
    uvicorn.run("app:app", host="0.0.0.0", port=PORT, reload=True, workers=1)
