import asyncio
import json
import logging
import os
import random
import time
import uuid
from typing import Dict, List, Optional, Set
from enum import Enum
from dataclasses import dataclass, asdict, field
from collections import defaultdict
from contextlib import asynccontextmanager
from datetime import datetime, timedelta

import uvicorn
from fastapi import FastAPI, WebSocket, WebSocketDisconnect, HTTPException, Request
from fastapi.responses import HTMLResponse, FileResponse
from fastapi.middleware.cors import CORSMiddleware
from pydantic import BaseModel, ValidationError, Field as PydanticField

# Configure logging
logging.basicConfig(
    level=logging.INFO,
    format='%(asctime)s - %(name)s - %(levelname)s - %(message)s - [%(filename)s:%(lineno)d]',
    handlers=[logging.StreamHandler()]
)
logger = logging.getLogger(__name__)

# Game Constants
STARTING_MONEY = 1000
MIN_BET = 10
MAX_BET = 500
MAX_PLAYERS_PER_ROOM = 6
RATE_LIMIT_MESSAGES_PER_SECOND = 10
RATE_LIMIT_ACTIONS_PER_SECOND = 5
MAX_CHAT_MESSAGES = 100
MAX_ROOMS = 100
SESSION_TIMEOUT = 3600
DEALER_HIT_THRESHOLD = 16  # Dealer hits on 16, stands on 17

class GamePhase(Enum):
    WAITING = "waiting"
    DEALING = "dealing"
    PLAYER_TURNS = "player_turns"
    DEALER_TURN = "dealer_turn"
    PAYOUT = "payout"
    GAME_OVER = "game_over"

class PlayerAction(Enum):
    HIT = "hit"
    STAND = "stand"
    DOUBLE_DOWN = "double_down"
    SPLIT = "split"
    SURRENDER = "surrender"
    PLACE_BET = "place_bet"

class PlayerStatus(Enum):
    ACTIVE = "active" 
    STANDING = "standing"
    BUST = "bust"
    BLACKJACK = "blackjack"
    SITTING_OUT = "sitting_out"
    ELIMINATED = "eliminated"

class HandResult(Enum):
    WIN = "win"
    LOSE = "lose" 
    PUSH = "push"
    BLACKJACK = "blackjack"
    BUST = "bust"

@dataclass
class Card:
    suit: str  # hearts, diamonds, clubs, spades
    rank: str  # A, 2-10, J, Q, K
    id: str = field(default_factory=lambda: str(uuid.uuid4()))

    def __str__(self):
        return f"{self.rank}{self.suit[0].upper()}"

    def blackjack_value(self, current_total: int = 0) -> int:
        """Return the blackjack value of this card"""
        if self.rank in ['J', 'Q', 'K']:
            return 10
        elif self.rank == 'A':
            # Ace is 11 unless it would bust, then it's 1
            return 11 if current_total + 11 <= 21 else 1
        else:
            return int(self.rank)

@dataclass
class Hand:
    cards: List[Card] = field(default_factory=list)
    bet_amount: int = 0
    is_split: bool = False
    is_doubled: bool = False
    is_surrendered: bool = False
    result: Optional[HandResult] = None
    payout: int = 0

    def get_value(self) -> int:
        """Calculate the best possible value of this hand"""
        total = 0
        aces = 0
        
        for card in self.cards:
            if card.rank == 'A':
                aces += 1
                total += 11
            elif card.rank in ['J', 'Q', 'K']:
                total += 10
            else:
                total += int(card.rank)
        
        # Convert aces from 11 to 1 if needed
        while total > 21 and aces > 0:
            total -= 10
            aces -= 1
            
        return total

    def is_bust(self) -> bool:
        return self.get_value() > 21

    def is_blackjack(self) -> bool:
        return len(self.cards) == 2 and self.get_value() == 21

    def can_split(self) -> bool:
        return len(self.cards) == 2 and self.cards[0].rank == self.cards[1].rank

    def can_double_down(self) -> bool:
        return len(self.cards) == 2 and not self.is_split

@dataclass
class Player:
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

    def get_current_hand(self) -> Hand:
        if self.current_hand_index < len(self.hands):
            return self.hands[self.current_hand_index]
        return self.hands[0] if self.hands else Hand()

    def can_act(self) -> bool:
        current_hand = self.get_current_hand()
        return (self.status == PlayerStatus.ACTIVE and 
                not current_hand.is_bust() and 
                not current_hand.is_surrendered and
                self.get_current_hand().get_value() < 21)

    def reset_for_new_hand(self):
        self.hands = [Hand()]
        self.current_hand_index = 0
        if self.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED]:
            self.status = PlayerStatus.ACTIVE

@dataclass
class Room:
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

    def __post_init__(self):
        if not self.deck:
            self.deck = self.create_deck()
        if not hasattr(self, 'dealer_hand') or not self.dealer_hand:
            self.dealer_hand = Hand()

    def create_deck(self) -> List[Card]:
        """Create a standard 52-card deck and shuffle it"""
        suits = ["hearts", "diamonds", "clubs", "spades"]
        ranks = ["A", "2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K"]
        deck = [Card(suit, rank) for suit in suits for rank in ranks]
        random.shuffle(deck)
        return deck

    def shuffle_deck(self):
        self.deck = self.create_deck()

    def deal_card(self) -> Optional[Card]:
        if len(self.deck) < 10:  # Reshuffle if deck is low
            self.shuffle_deck()
        return self.deck.pop() if self.deck else None

    def get_active_players(self) -> List[Player]:
        return [p for p in self.players.values() 
                if p.status not in [PlayerStatus.SITTING_OUT, PlayerStatus.ELIMINATED] 
                and p.money >= self.min_bet]

    def advance_to_next_player(self):
        if self._current_player_turn_index < len(self._player_turn_order) - 1:
            self._current_player_turn_index += 1
            self.current_player_id = self._player_turn_order[self._current_player_turn_index]
        else:
            # All players have acted, move to dealer turn
            self.current_player_id = None
            self.phase = GamePhase.DEALER_TURN

    def update_activity(self):
        self.last_activity = datetime.now()

class BlackjackGame:
    def __init__(self):
        self.rooms: Dict[str, Room] = {}
        self.connections: Dict[str, WebSocket] = {}
        self.player_rooms: Dict[str, str] = {}
        self.rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.action_rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.running = True

    def generate_room_code(self) -> str:
        return ''.join(random.choices('ABCDEFGHJKLMNPQRSTUVWXYZ23456789', k=6))

    def create_room(self, creator_player_id: str, room_name: Optional[str] = None) -> Optional[str]:
        if len(self.rooms) >= MAX_ROOMS:
            logger.error("Maximum number of rooms reached")
            return None
        
        room_code = self.generate_room_code()
        while room_code in self.rooms:
            room_code = self.generate_room_code()

        room_name = room_name or f"Blackjack {room_code}"
        
        self.rooms[room_code] = Room(
            code=room_code, 
            name=room_name, 
            players={}, 
            spectators=set(),
            deck=[], 
            dealer_hand=Hand(),
            owner_id=creator_player_id
        )
        
        logger.info(f"Room {room_code} ({room_name}) created by player {creator_player_id}")
        return room_code

    def join_room(self, room_code: str, player_id: str, player_name: str) -> bool:
        room = self.rooms.get(room_code)
        if not room:
            logger.warning(f"Attempt to join non-existent room {room_code} by {player_id}")
            return False

        if len([p for p in room.players.values() if not p.is_ai]) >= MAX_PLAYERS_PER_ROOM:
            logger.warning(f"Room {room_code} is full")
            return False

        if player_id in room.players:  # Rejoining player
            rejoining_player = room.players[player_id]
            rejoining_player.connection_id = player_id
            rejoining_player.name = player_name
            logger.info(f"Player {player_name} ({player_id}) re-joined room {room_code}")
        else:  # New player
            player = Player(
                id=player_id, 
                name=player_name, 
                money=STARTING_MONEY,
                avatar=f"avatar_{random.randint(1, 10)}", 
                color=f"#{random.randint(0, 0xFFFFFF):06x}",
                connection_id=player_id
            )
            room.players[player_id] = player
            logger.info(f"Player {player_name} ({player_id}) joined room {room_code}")

        self.player_rooms[player_id] = room_code
        room.update_activity()
        return True

    def leave_room(self, player_id: str, force: bool = False):
        logger.info(f"Player {player_id} attempting to leave room. Force: {force}")
        room_code = self.player_rooms.pop(player_id, None)
        if not room_code:
            return

        room = self.rooms.get(room_code)
        if not room:
            return

        if player_id in room.players:
            player_obj = room.players[player_id]
            logger.info(f"Player {player_obj.name} ({player_id}) leaving room {room_code}")
            del room.players[player_id]

        room.spectators.discard(player_id)

        # Close room if empty
        if not any(not p.is_ai for p in room.players.values()) and not room.spectators:
            logger.info(f"Room {room_code} is empty. Closing room.")
            if room_code in self.rooms:
                del self.rooms[room_code]
        # Transfer ownership if needed
        elif room.owner_id == player_id and any(not p.is_ai for p in room.players.values()):
            new_owner = next((pid for pid, p_obj in room.players.items() if not p_obj.is_ai), None)
            if new_owner:
                room.owner_id = new_owner
                logger.info(f"Room owner transferred to {new_owner}")

        room.update_activity()

    def start_game(self, room_code: str) -> bool:
        room = self.rooms.get(room_code)
        if not room:
            return False

        active_players = room.get_active_players()
        if len(active_players) < 1:
            logger.warning(f"Cannot start game in room {room_code}: No players with money")
            return False

        if room.phase not in [GamePhase.WAITING, GamePhase.GAME_OVER]:
            logger.warning(f"Game already in progress in room {room_code}")
            return False

        logger.info(f"Starting blackjack game in room {room_code}")
        room.phase = GamePhase.DEALING
        room.hand_number += 1
        room.shuffle_deck()
        room.dealer_hand = Hand()

        # Reset all players for new hand
        for player in room.players.values():
            player.reset_for_new_hand()

        # Set up turn order
        room._player_turn_order = [p.id for p in active_players]
        room._current_player_turn_index = 0
        room.current_player_id = room._player_turn_order[0] if room._player_turn_order else None

        return True

    def deal_initial_cards(self, room_code: str):
        room = self.rooms.get(room_code)
        if not room or room.phase != GamePhase.DEALING:
            return

        active_players = room.get_active_players()
        
        # Deal 2 cards to each player and dealer
        for _ in range(2):
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
        for player in active_players:
            if player.hands[0].is_blackjack():
                player.status = PlayerStatus.BLACKJACK

        # Move to player turns
        room.phase = GamePhase.PLAYER_TURNS
        room.current_player_id = room._player_turn_order[0] if room._player_turn_order else None

    def player_action(self, room_code: str, player_id: str, action: PlayerAction, amount: int = 0) -> bool:
        room = self.rooms.get(room_code)
        if not room:
            return False

        player = room.players.get(player_id)
        if not player:
            return False

        logger.info(f"Processing action: {player.name} - {action.value} - Amount: {amount}")

        if action == PlayerAction.PLACE_BET:
            return self.process_place_bet(room, player, amount)
        elif action == PlayerAction.HIT:
            return self.process_hit(room, player)
        elif action == PlayerAction.STAND:
            return self.process_stand(room, player)
        elif action == PlayerAction.DOUBLE_DOWN:
            return self.process_double_down(room, player)
        elif action == PlayerAction.SPLIT:
            return self.process_split(room, player)
        elif action == PlayerAction.SURRENDER:
            return self.process_surrender(room, player)

        return False

    def process_place_bet(self, room: Room, player: Player, amount: int) -> bool:
        if room.phase != GamePhase.WAITING:
            return False
        
        if amount < room.min_bet or amount > room.max_bet or amount > player.money:
            return False

        player.money -= amount
        player.hands[0].bet_amount = amount
        return True

    def process_hit(self, room: Room, player: Player) -> bool:
        if room.phase != GamePhase.PLAYER_TURNS or room.current_player_id != player.id:
            return False

        current_hand = player.get_current_hand()
        card = room.deal_card()
        if not card:
            return False

        current_hand.cards.append(card)

        if current_hand.is_bust():
            player.status = PlayerStatus.BUST
            self.advance_player_turn(room)
        elif current_hand.get_value() == 21:
            self.advance_player_turn(room)

        return True

    def process_stand(self, room: Room, player: Player) -> bool:
        if room.phase != GamePhase.PLAYER_TURNS or room.current_player_id != player.id:
            return False

        player.status = PlayerStatus.STANDING
        self.advance_player_turn(room)
        return True

    def process_double_down(self, room: Room, player: Player) -> bool:
        if room.phase != GamePhase.PLAYER_TURNS or room.current_player_id != player.id:
            return False

        current_hand = player.get_current_hand()
        if not current_hand.can_double_down() or player.money < current_hand.bet_amount:
            return False

        # Double the bet
        player.money -= current_hand.bet_amount
        current_hand.bet_amount *= 2
        current_hand.is_doubled = True

        # Deal one card and stand
        card = room.deal_card()
        if card:
            current_hand.cards.append(card)

        if current_hand.is_bust():
            player.status = PlayerStatus.BUST

        self.advance_player_turn(room)
        return True

    def process_split(self, room: Room, player: Player) -> bool:
        if room.phase != GamePhase.PLAYER_TURNS or room.current_player_id != player.id:
            return False

        current_hand = player.get_current_hand()
        if not current_hand.can_split() or player.money < current_hand.bet_amount:
            return False

        # Create new hand with second card
        second_card = current_hand.cards.pop()
        new_hand = Hand(cards=[second_card], bet_amount=current_hand.bet_amount, is_split=True)
        player.hands.append(new_hand)
        player.money -= current_hand.bet_amount

        # Deal new cards to both hands
        for hand in player.hands:
            card = room.deal_card()
            if card:
                hand.cards.append(card)

        return True

    def process_surrender(self, room: Room, player: Player) -> bool:
        if room.phase != GamePhase.PLAYER_TURNS or room.current_player_id != player.id:
            return False

        current_hand = player.get_current_hand()
        if len(current_hand.cards) != 2:
            return False

        current_hand.is_surrendered = True
        # Return half the bet
        player.money += current_hand.bet_amount // 2
        
        self.advance_player_turn(room)
        return True

    def advance_player_turn(self, room: Room):
        # Check if current player has more hands to play
        current_player = room.players.get(room.current_player_id)
        if current_player and current_player.current_hand_index < len(current_player.hands) - 1:
            current_player.current_hand_index += 1
            return

        # Move to next player
        room.advance_to_next_player()
        
        if room.phase == GamePhase.DEALER_TURN:
            self.play_dealer_hand(room)

    def play_dealer_hand(self, room: Room):
        # Dealer reveals hole card and plays
        while room.dealer_hand.get_value() <= DEALER_HIT_THRESHOLD:
            card = room.deal_card()
            if card:
                room.dealer_hand.cards.append(card)
            else:
                break

        room.phase = GamePhase.PAYOUT
        self.calculate_payouts(room)

    def calculate_payouts(self, room: Room):
        dealer_value = room.dealer_hand.get_value()
        dealer_bust = room.dealer_hand.is_bust()

        for player in room.players.values():
            for hand in player.hands:
                if hand.is_surrendered:
                    hand.result = HandResult.LOSE
                    continue

                hand_value = hand.get_value()
                
                if hand.is_bust():
                    hand.result = HandResult.BUST
                    hand.payout = 0
                elif hand.is_blackjack() and not room.dealer_hand.is_blackjack():
                    hand.result = HandResult.BLACKJACK
                    hand.payout = int(hand.bet_amount * 2.5)  # 3:2 payout
                    player.money += hand.payout
                elif dealer_bust or hand_value > dealer_value:
                    hand.result = HandResult.WIN
                    hand.payout = hand.bet_amount * 2
                    player.money += hand.payout
                elif hand_value == dealer_value:
                    hand.result = HandResult.PUSH
                    hand.payout = hand.bet_amount  # Return bet
                    player.money += hand.payout
                else:
                    hand.result = HandResult.LOSE
                    hand.payout = 0

        # Update player stats
        for player in room.players.values():
            player.total_hands_played += 1
            won_any_hand = any(hand.result in [HandResult.WIN, HandResult.BLACKJACK] for hand in player.hands)
            if won_any_hand:
                player.total_hands_won += 1
            total_winnings = sum(hand.payout - hand.bet_amount for hand in player.hands)
            player.total_winnings += total_winnings

        room.phase = GamePhase.GAME_OVER
        # Automatically prepare for next hand after delay
        asyncio.create_task(self.prepare_next_hand(room.code))

    async def prepare_next_hand(self, room_code: str, delay: int = 5):
        await asyncio.sleep(delay)
        room = self.rooms.get(room_code)
        if not room:
            return

        # Reset for next hand
        room.phase = GamePhase.WAITING
        for player in room.players.values():
            player.reset_for_new_hand()
        room.dealer_hand = Hand()
        room.current_player_id = None

    def get_game_state(self, room_code: str, for_player_id: str) -> dict:
        room = self.rooms.get(room_code)
        if not room:
            return {"error": "Room not found"}

        is_player = for_player_id in room.players and not room.players[for_player_id].is_ai
        is_spectator = for_player_id in room.spectators

        players_data = {}
        for p_id, p_obj in room.players.items():
            hands_data = []
            for hand in p_obj.hands:
                hand_data = {
                    "cards": [{"suit": c.suit, "rank": c.rank, "id": c.id} for c in hand.cards],
                    "value": hand.get_value(),
                    "bet_amount": hand.bet_amount,
                    "is_bust": hand.is_bust(),
                    "is_blackjack": hand.is_blackjack(),
                    "is_doubled": hand.is_doubled,
                    "is_surrendered": hand.is_surrendered,
                    "result": hand.result.value if hand.result else None,
                    "payout": hand.payout
                }
                hands_data.append(hand_data)

            player_data = {
                "id": p_obj.id,
                "name": p_obj.name,
                "money": p_obj.money,
                "hands": hands_data,
                "current_hand_index": p_obj.current_hand_index,
                "status": p_obj.status.value,
                "avatar": p_obj.avatar,
                "color": p_obj.color,
                "is_current_player": room.current_player_id == p_id,
                "is_ai": p_obj.is_ai,
                "stats": {
                    "total_hands_played": p_obj.total_hands_played,
                    "total_hands_won": p_obj.total_hands_won,
                    "total_winnings": p_obj.total_winnings
                }
            }
            players_data[p_id] = player_data

        # Dealer hand - hide hole card until dealer turn
        dealer_cards = []
        for i, card in enumerate(room.dealer_hand.cards):
            if i == 1 and room.phase in [GamePhase.DEALING, GamePhase.PLAYER_TURNS] and len(room.dealer_hand.cards) > 1:
                # Hide hole card
                dealer_cards.append({"suit": "back", "rank": "back", "id": "hidden"})
            else:
                dealer_cards.append({"suit": card.suit, "rank": card.rank, "id": card.id})

        game_state = {
            "room_code": room.code,
            "room_name": room.name,
            "phase": room.phase.value,
            "current_player_id": room.current_player_id,
            "players": players_data,
            "dealer_hand": {
                "cards": dealer_cards,
                "value": room.dealer_hand.get_value() if room.phase in [GamePhase.DEALER_TURN, GamePhase.PAYOUT, GamePhase.GAME_OVER] else None
            },
            "chat_messages": room.chat_messages[-30:],
            "is_player_in_game": is_player,
            "is_spectator": is_spectator,
            "spectator_count": len(room.spectators),
            "hand_number": room.hand_number,
            "min_bet": room.min_bet,
            "max_bet": room.max_bet,
            "can_act": (is_player and room.current_player_id == for_player_id and 
                       room.phase == GamePhase.PLAYER_TURNS),
            "available_actions": self.get_available_actions(room, for_player_id) if is_player else []
        }
        return game_state

    def get_available_actions(self, room: Room, player_id: str) -> List[Dict]:
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
            
            if current_hand.can_split() and player.money >= current_hand.bet_amount:
                actions.append({"action": PlayerAction.SPLIT.value, "label": "Split"})
            
            if len(current_hand.cards) == 2:
                actions.append({"action": PlayerAction.SURRENDER.value, "label": "Surrender"})

        return actions

    def add_chat_message(self, room_code: str, player_id: str, message_text: str):
        room = self.rooms.get(room_code)
        if not room:
            return

        player = room.players.get(player_id)
        player_name = player.name if player else f"Spectator_{player_id[:4]}"
        player_color = player.color if player else "#cccccc"

        cleaned_message = message_text.strip()
        if not cleaned_message:
            return

        chat_msg = {
            "player_id": player_id,
            "player_name": player_name,
            "player_color": player_color,
            "message": cleaned_message[:200],
            "timestamp": time.time(),
            "formatted_time": datetime.now().strftime("%H:%M:%S")
        }
        
        room.chat_messages.append(chat_msg)
        if len(room.chat_messages) > MAX_CHAT_MESSAGES:
            room.chat_messages = room.chat_messages[-MAX_CHAT_MESSAGES:]
        
        logger.info(f"Chat in {room_code} by {player_name}: {cleaned_message}")
        room.update_activity()

    def check_rate_limit(self, client_id: str, limit_type: str = "message") -> bool:
        limit_dict = self.rate_limits if limit_type == "message" else self.action_rate_limits
        max_per_second = RATE_LIMIT_MESSAGES_PER_SECOND if limit_type == "message" else RATE_LIMIT_ACTIONS_PER_SECOND

        current_time = time.time()
        limit_dict[client_id] = [t for t in limit_dict[client_id] if current_time - t <= 1.0]

        if len(limit_dict[client_id]) < max_per_second:
            limit_dict[client_id].append(current_time)
            return True
        else:
            logger.warning(f"Rate limit exceeded for {client_id} (type: {limit_type})")
            return False

# Global game instance
game = BlackjackGame()

# WebSocket message models
class WSMessage(BaseModel):
    action: str
    payload: dict = PydanticField(default_factory=dict)

class CreateRoomPayload(BaseModel):
    player_name: str = "Anonymous"
    room_name: Optional[str] = None

async def game_loop():
    logger.info("Game loop started.")
    while game.running:
        try:
            # Check for games in dealing phase that need initial cards dealt
            for room_code, room in list(game.rooms.items()):
                if room.phase == GamePhase.DEALING and not room.dealer_hand.cards:
                    game.deal_initial_cards(room_code)

            # Broadcast game state to all connected clients
            for room_code, room in list(game.rooms.items()):
                connections_to_broadcast = []
                
                # Get all human players and spectators in room
                user_ids_in_room = set()
                for p_id, player_obj in room.players.items():
                    if not player_obj.is_ai and player_obj.connection_id:
                        user_ids_in_room.add(player_obj.connection_id)
                user_ids_in_room.update(room.spectators)

                for user_id in list(user_ids_in_room):
                    ws_conn = game.connections.get(user_id)
                    if ws_conn:
                        connections_to_broadcast.append((user_id, ws_conn))
                    else:
                        game.leave_room(user_id, force=True)

                if connections_to_broadcast:
                    broadcast_tasks = []
                    for user_id, ws_conn in connections_to_broadcast:
                        try:
                            game_state = game.get_game_state(room_code, user_id)
                            if "error" not in game_state:
                                broadcast_tasks.append(
                                    ws_conn.send_json({"type": "game_state", "data": game_state})
                                )
                        except Exception as e:
                            logger.error(f"Error preparing game_state for user {user_id}: {e}")

                    if broadcast_tasks:
                        results = await asyncio.gather(*broadcast_tasks, return_exceptions=True)
                        for i, result in enumerate(results):
                            if isinstance(result, Exception):
                                failed_user_id, _ = connections_to_broadcast[i]
                                logger.error(f"Failed to broadcast to {failed_user_id}: {result}")
                                if failed_user_id in game.connections:
                                    del game.connections[failed_user_id]
                                game.leave_room(failed_user_id, force=True)

            await asyncio.sleep(1/15)  # 15 FPS update rate

        except Exception as e:
            logger.exception(f"Error in game_loop: {e}")
            await asyncio.sleep(1.0)

async def handle_websocket_message(websocket: WebSocket, player_id: str, message: WSMessage):
    action = message.action
    payload = message.payload
    logger.info(f"Handling message from {player_id}: {action}")

    try:
        if action == "create_room":
            try:
                create_payload = CreateRoomPayload(**payload)
            except ValidationError as e:
                await websocket.send_json({"type": "error", "message": f"Invalid create room data: {e.errors()}"})
                return

            room_code = game.create_room(player_id, create_payload.room_name)
            if not room_code:
                await websocket.send_json({"type": "error", "message": "Failed to create room"})
                return

            if game.join_room(room_code, player_id, create_payload.player_name):
                await websocket.send_json({"type": "room_created", "data": {"room_code": room_code}})
            else:
                await websocket.send_json({"type": "error", "message": "Failed to join created room"})

        elif action == "join_room":
            room_code = payload.get("room_code")
            player_name = payload.get("player_name", "Player")

            if not room_code:
                await websocket.send_json({"type": "error", "message": "Invalid room code"})
                return

            if game.join_room(room_code, player_id, player_name):
                await websocket.send_json({"type": "room_joined", "data": {"room_code": room_code}})
            else:
                await websocket.send_json({"type": "error", "message": "Failed to join room"})

        elif action == "spectate_room":
            room_code = payload.get("room_code")
            if not room_code:
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
                    logger.info(f"Game started in room {room_code}")
                else:
                    await websocket.send_json({"type": "error", "message": "Cannot start game"})
            else:
                await websocket.send_json({"type": "error", "message": "Only room owner can start game"})

        elif action == "player_action":
            if not game.check_rate_limit(player_id, "action"):
                await websocket.send_json({"type": "error", "message": "Action rate limit exceeded"})
                return
            
            room_code = game.player_rooms.get(player_id)
            if not room_code:
                await websocket.send_json({"type": "error", "message": "Not in a room"})
                return

            action_type_str = payload.get("action_type")
            amount = payload.get("amount", 0)

            try:
                blackjack_action = PlayerAction(action_type_str)
                if not game.player_action(room_code, player_id, blackjack_action, amount):
                    await websocket.send_json({"type": "error", "message": "Invalid action"})
            except ValueError:
                await websocket.send_json({"type": "error", "message": f"Invalid action type: {action_type_str}"})

        elif action == "send_chat_message":
            if not game.check_rate_limit(player_id, "message"):
                await websocket.send_json({"type": "error", "message": "Chat rate limit exceeded"})
                return
            
            room_code = game.player_rooms.get(player_id)
            if not room_code:
                await websocket.send_json({"type": "error", "message": "Must be in a room to chat"})
                return

            message_text = payload.get("message")
            if message_text and isinstance(message_text, str) and 0 < len(message_text.strip()) <= 200:
                game.add_chat_message(room_code, player_id, message_text.strip())
            else:
                await websocket.send_json({"type": "error", "message": "Invalid chat message"})

        elif action == "get_room_list":
            public_rooms = []
            for r_code, r_obj in game.rooms.items():
                if r_obj.phase in [GamePhase.WAITING, GamePhase.GAME_OVER]:
                    human_players = sum(1 for p in r_obj.players.values() if not p.is_ai)
                    public_rooms.append({
                        "code": r_code,
                        "name": r_obj.name,
                        "players": human_players,
                        "max_players": MAX_PLAYERS_PER_ROOM,
                        "phase": r_obj.phase.value
                    })
            await websocket.send_json({"type": "room_list", "data": {"rooms": public_rooms}})

        else:
            await websocket.send_json({"type": "error", "message": f"Unknown action: {action}"})

    except WebSocketDisconnect:
        raise
    except Exception as e:
        logger.exception(f"Error handling message: {e}")
        try:
            await websocket.send_json({"type": "error", "message": "Server error"})
        except Exception:
            pass

@asynccontextmanager
async def lifespan(app_instance: FastAPI):
    logger.info("Starting Blackjack server...")
    asyncio.create_task(game_loop())
    yield
    game.running = False
    logger.info("Blackjack server shutting down...")

app = FastAPI(lifespan=lifespan)

app.add_middleware(
    CORSMiddleware,
    allow_origins=["*"],
    allow_credentials=True,
    allow_methods=["*"],
    allow_headers=["*"],
)

@app.get("/", response_class=HTMLResponse)
async def get_root(request: Request):
    if os.path.exists("index.html"):
        return FileResponse("index.html")
    else:
        return HTMLResponse(content="<h1>Blackjack server running, but index.html not found</h1>", status_code=404)

@app.get("/health")
async def health_check():
    return {
        "status": "ok",
        "active_rooms": len(game.rooms),
        "connected_players": len(game.connections)
    }

@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    player_id = str(uuid.uuid4())
    logger.info(f"WebSocket connection from {player_id}")
    
    try:
        await websocket.accept()
        game.connections[player_id] = websocket
        
        await websocket.send_json({
            "type": "connected",
            "data": {"player_id": player_id, "message": "Welcome to Royal Blackjack 3D!"}
        })

        while True:
            data = await websocket.receive_text()
            try:
                message_data = json.loads(data)
                if not isinstance(message_data, dict) or "action" not in message_data:
                    raise ValueError("Invalid message format")
                ws_message = WSMessage(**message_data)
                await handle_websocket_message(websocket, player_id, ws_message)
            except (json.JSONDecodeError, ValidationError, ValueError) as e:
                await websocket.send_json({"type": "error", "message": f"Invalid message: {str(e)}"})

    except WebSocketDisconnect:
        logger.info(f"WebSocket {player_id} disconnected")
    except Exception as e:
        logger.exception(f"WebSocket error for {player_id}: {e}")
    finally:
        if player_id in game.connections:
            del game.connections[player_id]
        game.leave_room(player_id, force=True)

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run("app:app", host="0.0.0.0", port=port, reload=True)
