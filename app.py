import asyncio
import json
import logging
import os
import random
import time
import uuid
from typing import Dict, List, Optional, Set
from enum import Enum
from dataclasses import dataclass, asdict
from collections import defaultdict
from contextlib import asynccontextmanager

import uvicorn
from fastapi import FastAPI, WebSocket, WebSocketDisconnect, HTTPException
from fastapi.responses import HTMLResponse
from pydantic import BaseModel, ValidationError

# Configure logging
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

# Game Constants
STARTING_MONEY = 1000
SMALL_BLIND = 25
BIG_BLIND = 50
MAX_PLAYERS_PER_ROOM = 8
GAME_UPDATE_RATE = 30  # 30 FPS
RATE_LIMIT_MESSAGES_PER_SECOND = 10

class GamePhase(Enum):
    WAITING = "waiting"
    PRE_FLOP = "pre_flop"
    FLOP = "flop"
    TURN = "turn"
    RIVER = "river"
    SHOWDOWN = "showdown"
    GAME_OVER = "game_over"

class PlayerAction(Enum):
    FOLD = "fold"
    CHECK = "check"
    CALL = "call"
    RAISE = "raise"
    ALL_IN = "all_in"

@dataclass
class Card:
    suit: str  # hearts, diamonds, clubs, spades
    rank: str  # 2-10, J, Q, K, A
    
    def __str__(self):
        return f"{self.rank}{self.suit[0].upper()}"
    
    def value(self):
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

@dataclass
class Player:
    id: str
    name: str
    money: int = STARTING_MONEY
    current_bet: int = 0
    cards: List[Card] = None
    is_folded: bool = False
    is_all_in: bool = False
    position: int = 0
    last_action: Optional[PlayerAction] = None
    
    def __post_init__(self):
        if self.cards is None:
            self.cards = []

@dataclass
class Room:
    code: str
    players: Dict[str, Player]
    spectators: Set[str]
    deck: List[Card]
    community_cards: List[Card]
    current_player_index: int = 0
    dealer_index: int = 0
    phase: GamePhase = GamePhase.WAITING
    pot: int = 0
    current_bet: int = 0
    chat_messages: List[Dict] = None
    last_action_time: float = 0
    
    def __post_init__(self):
        if self.chat_messages is None:
            self.chat_messages = []
        if not self.deck:
            self.deck = self.create_deck()
        if not self.community_cards:
            self.community_cards = []

    def create_deck(self) -> List[Card]:
        suits = ["hearts", "diamonds", "clubs", "spades"]
        ranks = ["2", "3", "4", "5", "6", "7", "8", "9", "10", "J", "Q", "K", "A"]
        deck = [Card(suit, rank) for suit in suits for rank in ranks]
        random.shuffle(deck)
        return deck

    def deal_cards(self):
        # Deal 2 cards to each player
        for player in self.players.values():
            if not player.is_folded:
                player.cards = [self.deck.pop(), self.deck.pop()]

    def deal_community_cards(self, count: int):
        for _ in range(count):
            if self.deck:
                self.community_cards.append(self.deck.pop())

class PokerGame:
    def __init__(self):
        self.rooms: Dict[str, Room] = {}
        self.connections: Dict[str, WebSocket] = {}
        self.player_rooms: Dict[str, str] = {}
        self.rate_limits: Dict[str, List[float]] = defaultdict(list)
        self.running = True

    def generate_room_code(self) -> str:
        return ''.join(random.choices('ABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789', k=6))

    def create_room(self, player_id: str) -> str:
        room_code = self.generate_room_code()
        while room_code in self.rooms:
            room_code = self.generate_room_code()
        
        self.rooms[room_code] = Room(
            code=room_code,
            players={},
            spectators=set(),
            deck=[],
            community_cards=[]
        )
        logger.info(f"Room {room_code} created by player {player_id}")
        return room_code

    def join_room(self, room_code: str, player_id: str, player_name: str) -> bool:
        if room_code not in self.rooms:
            return False
        
        room = self.rooms[room_code]
        if len(room.players) >= MAX_PLAYERS_PER_ROOM:
            return False
        
        player = Player(id=player_id, name=player_name, position=len(room.players))
        room.players[player_id] = player
        self.player_rooms[player_id] = room_code
        
        logger.info(f"Player {player_name} joined room {room_code}")
        return True

    def leave_room(self, player_id: str):
        if player_id not in self.player_rooms:
            return
        
        room_code = self.player_rooms[player_id]
        room = self.rooms[room_code]
        
        if player_id in room.players:
            del room.players[player_id]
        if player_id in room.spectators:
            room.spectators.remove(player_id)
        
        del self.player_rooms[player_id]
        
        # If room is empty, delete it
        if not room.players and not room.spectators:
            del self.rooms[room_code]
            logger.info(f"Room {room_code} deleted (empty)")

    def spectate_room(self, room_code: str, player_id: str) -> bool:
        if room_code not in self.rooms:
            return False
        
        room = self.rooms[room_code]
        room.spectators.add(player_id)
        self.player_rooms[player_id] = room_code
        return True

    def start_game(self, room_code: str):
        room = self.rooms[room_code]
        if len(room.players) < 2:
            return
        
        room.phase = GamePhase.PRE_FLOP
        room.deck = room.create_deck()
        room.community_cards = []
        room.pot = 0
        room.current_bet = BIG_BLIND
        
        # Reset players
        for player in room.players.values():
            player.cards = []
            player.current_bet = 0
            player.is_folded = False
            player.is_all_in = False
            player.last_action = None
        
        # Set blinds
        players_list = list(room.players.values())
        if len(players_list) >= 2:
            small_blind_player = players_list[room.dealer_index]
            big_blind_player = players_list[(room.dealer_index + 1) % len(players_list)]
            
            small_blind_player.current_bet = SMALL_BLIND
            small_blind_player.money -= SMALL_BLIND
            room.pot += SMALL_BLIND
            
            big_blind_player.current_bet = BIG_BLIND
            big_blind_player.money -= BIG_BLIND
            room.pot += BIG_BLIND
        
        room.deal_cards()
        room.current_player_index = (room.dealer_index + 2) % len(players_list)

    def player_action(self, room_code: str, player_id: str, action: PlayerAction, amount: int = 0):
        room = self.rooms[room_code]
        player = room.players[player_id]
        
        if action == PlayerAction.FOLD:
            player.is_folded = True
        elif action == PlayerAction.CALL:
            call_amount = min(room.current_bet - player.current_bet, player.money)
            player.money -= call_amount
            player.current_bet += call_amount
            room.pot += call_amount
        elif action == PlayerAction.RAISE:
            total_bet = room.current_bet + amount
            bet_amount = min(total_bet - player.current_bet, player.money)
            player.money -= bet_amount
            player.current_bet += bet_amount
            room.pot += bet_amount
            room.current_bet = player.current_bet
        elif action == PlayerAction.CHECK:
            pass  # No money movement
        elif action == PlayerAction.ALL_IN:
            room.pot += player.money
            player.current_bet += player.money
            player.money = 0
            player.is_all_in = True
            if player.current_bet > room.current_bet:
                room.current_bet = player.current_bet
        
        player.last_action = action
        self.advance_game(room_code)

    def advance_game(self, room_code: str):
        room = self.rooms[room_code]
        active_players = [p for p in room.players.values() if not p.is_folded]
        
        if len(active_players) <= 1:
            self.end_hand(room_code)
            return
        
        # Move to next player
        room.current_player_index = (room.current_player_index + 1) % len(room.players)
        
        # Check if betting round is complete
        if self.is_betting_round_complete(room):
            self.advance_phase(room_code)

    def is_betting_round_complete(self, room: Room) -> bool:
        active_players = [p for p in room.players.values() if not p.is_folded and not p.is_all_in]
        if len(active_players) <= 1:
            return True
        
        # Check if all active players have matched the current bet
        for player in active_players:
            if player.current_bet < room.current_bet and player.money > 0:
                return False
        return True

    def advance_phase(self, room_code: str):
        room = self.rooms[room_code]
        
        # Reset current bets for next round
        for player in room.players.values():
            player.current_bet = 0
        room.current_bet = 0
        
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

    def end_hand(self, room_code: str):
        room = self.rooms[room_code]
        active_players = [p for p in room.players.values() if not p.is_folded]
        
        if len(active_players) == 1:
            # Single winner
            winner = active_players[0]
            winner.money += room.pot
        else:
            # Determine winners by hand strength (simplified)
            winner = max(active_players, key=lambda p: self.evaluate_hand(p.cards + room.community_cards))
            winner.money += room.pot
        
        # Reset for next hand
        room.pot = 0
        room.dealer_index = (room.dealer_index + 1) % len(room.players)
        room.phase = GamePhase.WAITING
        
        # Remove players with no money
        broke_players = [pid for pid, p in room.players.items() if p.money <= 0]
        for pid in broke_players:
            del room.players[pid]
            if pid in self.player_rooms:
                del self.player_rooms[pid]

    def evaluate_hand(self, cards: List[Card]) -> int:
        # Simplified hand evaluation - just return highest card value
        return max(card.value() for card in cards)

    def add_chat_message(self, room_code: str, player_id: str, message: str):
        if room_code in self.rooms:
            room = self.rooms[room_code]
            player_name = "Spectator"
            if player_id in room.players:
                player_name = room.players[player_id].name
            
            chat_msg = {
                "id": str(uuid.uuid4()),
                "player_id": player_id,
                "player_name": player_name,
                "message": message,
                "timestamp": time.time()
            }
            room.chat_messages.append(chat_msg)
            
            # Keep only last 50 messages
            if len(room.chat_messages) > 50:
                room.chat_messages = room.chat_messages[-50:]

    def check_rate_limit(self, player_id: str) -> bool:
        now = time.time()
        self.rate_limits[player_id] = [t for t in self.rate_limits[player_id] if now - t < 1.0]
        
        if len(self.rate_limits[player_id]) >= RATE_LIMIT_MESSAGES_PER_SECOND:
            return False
        
        self.rate_limits[player_id].append(now)
        return True

    def get_game_state(self, room_code: str, player_id: str) -> dict:
        if room_code not in self.rooms:
            return {}
        
        room = self.rooms[room_code]
        is_player = player_id in room.players
        
        # Convert players to dict format
        players_data = {}
        for pid, player in room.players.items():
            player_data = {
                "id": player.id,
                "name": player.name,
                "money": player.money,
                "current_bet": player.current_bet,
                "is_folded": player.is_folded,
                "is_all_in": player.is_all_in,
                "position": player.position,
                "last_action": player.last_action.value if player.last_action else None
            }
            
            # Only show cards to the player themselves or in showdown
            if pid == player_id or room.phase == GamePhase.SHOWDOWN:
                player_data["cards"] = [{"suit": c.suit, "rank": c.rank} for c in player.cards]
            else:
                player_data["cards"] = [{"suit": "back", "rank": "back"}] * len(player.cards)
            
            players_data[pid] = player_data
        
        return {
            "room_code": room.code,
            "phase": room.phase.value,
            "pot": room.pot,
            "current_bet": room.current_bet,
            "current_player_index": room.current_player_index,
            "dealer_index": room.dealer_index,
            "players": players_data,
            "community_cards": [{"suit": c.suit, "rank": c.rank} for c in room.community_cards],
            "chat_messages": room.chat_messages[-10:],  # Last 10 messages
            "is_player": is_player,
            "spectator_count": len(room.spectators)
        }

# Global game instance
game = PokerGame()

# WebSocket message models
class WSMessage(BaseModel):
    action: str
    payload: dict = {}

# FastAPI app with lifespan
@asynccontextmanager
async def lifespan(app: FastAPI):
    # Startup
    logger.info("Starting poker game server...")
    game_task = asyncio.create_task(game_loop())
    
    yield
    
    # Shutdown
    logger.info("Shutting down poker game server...")
    game.running = False
    game_task.cancel()
    try:
        await game_task
    except asyncio.CancelledError:
        pass

app = FastAPI(lifespan=lifespan)

async def game_loop():
    """Main game loop that broadcasts game state at 30 FPS"""
    while game.running:
        try:
            # Broadcast game state to all connected clients
            for room_code, room in game.rooms.items():
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
                    for user_id in room_users:
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
            
            await asyncio.sleep(1.0 / GAME_UPDATE_RATE)  # 30 FPS
        except Exception as e:
            logger.error(f"Error in game loop: {e}")
            await asyncio.sleep(1.0)

@app.get("/", response_class=HTMLResponse)
async def get_poker_game():
    return HTMLResponse(content=HTML_TEMPLATE)

@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    await websocket.accept()
    player_id = str(uuid.uuid4())
    game.connections[player_id] = websocket
    
    try:
        while True:
            data = await websocket.receive_text()
            
            # Rate limiting
            if not game.check_rate_limit(player_id):
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
    
    if action == "create_room":
        room_code = game.create_room(player_id)
        player_name = payload.get("player_name", f"Player_{player_id[:8]}")
        game.join_room(room_code, player_id, player_name)
        await websocket.send_json({
            "type": "room_created",
            "data": {"room_code": room_code}
        })
    
    elif action == "join_room":
        room_code = payload.get("room_code", "").upper()
        player_name = payload.get("player_name", f"Player_{player_id[:8]}")
        
        if game.join_room(room_code, player_id, player_name):
            await websocket.send_json({
                "type": "room_joined",
                "data": {"room_code": room_code}
            })
        else:
            await websocket.send_json({
                "type": "error",
                "message": "Failed to join room"
            })
    
    elif action == "leave_room":
        game.leave_room(player_id)
        await websocket.send_json({"type": "room_left"})
    
    elif action == "spectate":
        room_code = payload.get("room_code", "").upper()
        if game.spectate_room(room_code, player_id):
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
            game.start_game(room_code)
    
    elif action == "player_action":
        if player_id in game.player_rooms:
            room_code = game.player_rooms[player_id]
            action_type = payload.get("action_type")
            amount = payload.get("amount", 0)
            
            try:
                poker_action = PlayerAction(action_type)
                game.player_action(room_code, player_id, poker_action, amount)
            except ValueError:
                await websocket.send_json({
                    "type": "error",
                    "message": "Invalid action type"
                })
    
    elif action == "send_chat":
        if player_id in game.player_rooms:
            room_code = game.player_rooms[player_id]
            message_text = payload.get("message", "")
            if message_text.strip():
                game.add_chat_message(room_code, player_id, message_text.strip())

# HTML Template with Three.js 3D Poker Game
HTML_TEMPLATE = """
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>3D Multiplayer Poker</title>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js"></script>
    <style>
        body {
            margin: 0;
            padding: 0;
            background: linear-gradient(135deg, #0f4c3a, #1a5d4a);
            font-family: 'Arial', sans-serif;
            overflow: hidden;
        }

        #gameContainer {
            position: relative;
            width: 100vw;
            height: 100vh;
        }

        #canvas {
            display: block;
        }

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
            background: rgba(0, 0, 0, 0.8);
            border-radius: 10px;
            padding: 20px;
            color: white;
            pointer-events: auto;
            border: 2px solid #ffd700;
        }

        .menu-panel {
            top: 50%;
            left: 50%;
            transform: translate(-50%, -50%);
            text-align: center;
            min-width: 300px;
        }

        .game-hud {
            top: 20px;
            left: 20px;
            max-width: 300px;
        }

        .actions-panel {
            bottom: 20px;
            left: 50%;
            transform: translateX(-50%);
            display: flex;
            gap: 10px;
        }

        .chat-panel {
            top: 20px;
            right: 20px;
            width: 280px;
            height: 300px;
            display: flex;
            flex-direction: column;
        }

        #chatMessages {
            flex: 1;
            overflow-y: auto;
            background: rgba(255, 255, 255, 0.1);
            border-radius: 5px;
            padding: 10px;
            margin-bottom: 10px;
        }

        .chat-input-container {
            display: flex;
            gap: 5px;
        }

        button {
            background: linear-gradient(135deg, #ffd700, #ffed4e);
            border: none;
            border-radius: 5px;
            padding: 12px 20px;
            color: #333;
            font-weight: bold;
            cursor: pointer;
            transition: all 0.3s ease;
        }

        button:hover {
            background: linear-gradient(135deg, #ffed4e, #ffd700);
            transform: translateY(-2px);
            box-shadow: 0 4px 8px rgba(0, 0, 0, 0.3);
        }

        button:disabled {
            background: #666;
            cursor: not-allowed;
            transform: none;
        }

        input {
            padding: 10px;
            border: 2px solid #ffd700;
            border-radius: 5px;
            background: rgba(255, 255, 255, 0.9);
            color: #333;
            font-size: 14px;
        }

        .player-info {
            background: rgba(0, 100, 0, 0.8);
            border: 2px solid #ffd700;
            border-radius: 10px;
            padding: 10px;
            margin: 5px;
            text-align: center;
            color: white;
            min-width: 120px;
        }

        .current-player {
            border-color: #ff4444;
            box-shadow: 0 0 20px rgba(255, 68, 68, 0.5);
        }

        .folded-player {
            opacity: 0.5;
            filter: grayscale(100%);
        }

        .pot-display {
            position: absolute;
            top: 50%;
            left: 50%;
            transform: translate(-50%, -50%);
            background: rgba(255, 215, 0, 0.9);
            color: #333;
            padding: 20px;
            border-radius: 50%;
            border: 3px solid #ffd700;
            font-size: 24px;
            font-weight: bold;
            pointer-events: none;
            min-width: 100px;
            text-align: center;
        }

        .hidden {
            display: none !important;
        }

        .loading {
            position: absolute;
            top: 50%;
            left: 50%;
            transform: translate(-50%, -50%);
            color: white;
            font-size: 24px;
        }
    </style>
</head>
<body>
    <div id="gameContainer">
        <canvas id="canvas"></canvas>
        
        <div class="ui-overlay">
            <!-- Main Menu -->
            <div id="menuPanel" class="ui-panel menu-panel">
                <h1 style="color: #ffd700; margin-bottom: 30px;">🃏 3D Poker Royal 🃏</h1>
                <div style="margin-bottom: 20px;">
                    <input type="text" id="playerName" placeholder="Enter your name" value="Player" style="width: 200px; margin-bottom: 15px;">
                </div>
                <div style="display: flex; flex-direction: column; gap: 15px;">
                    <button onclick="createRoom()">Create New Room</button>
                    <div style="display: flex; gap: 10px; align-items: center;">
                        <input type="text" id="roomCode" placeholder="Room Code" style="flex: 1;">
                        <button onclick="joinRoom()">Join Room</button>
                    </div>
                    <button onclick="spectateRoom()">Spectate Room</button>
                </div>
                <div style="margin-top: 20px; font-size: 14px; color: #ccc;">
                    Starting money: $1,000 | Blinds: $25/$50
                </div>
            </div>

            <!-- Game HUD -->
            <div id="gameHUD" class="ui-panel game-hud hidden">
                <div id="roomInfo" style="margin-bottom: 15px;">
                    <strong>Room: <span id="currentRoom">-</span></strong>
                </div>
                <div id="gamePhase" style="margin-bottom: 15px;">
                    Phase: <span id="phaseText">Waiting</span>
                </div>
                <div id="playerMoney" style="margin-bottom: 15px;">
                    Money: $<span id="moneyAmount">1000</span>
                </div>
                <div id="currentBet" style="margin-bottom: 15px;">
                    Current Bet: $<span id="betAmount">0</span>
                </div>
                <button onclick="startGame()" id="startGameBtn" style="width: 100%;">Start Game</button>
                <button onclick="leaveRoom()" style="width: 100%; margin-top: 10px; background: #dc3545;">Leave Room</button>
            </div>

            <!-- Pot Display -->
            <div id="potDisplay" class="pot-display hidden">
                POT<br>$<span id="potAmount">0</span>
            </div>

            <!-- Action Buttons -->
            <div id="actionsPanel" class="actions-panel hidden">
                <button onclick="playerAction('fold')" id="foldBtn">Fold</button>
                <button onclick="playerAction('check')" id="checkBtn">Check</button>
                <button onclick="playerAction('call')" id="callBtn">Call $<span id="callAmount">0</span></button>
                <div style="display: flex; align-items: center; gap: 5px;">
                    <input type="number" id="raiseAmount" min="1" value="50" style="width: 80px;">
                    <button onclick="playerAction('raise')" id="raiseBtn">Raise</button>
                </div>
                <button onclick="playerAction('all_in')" id="allInBtn">All In</button>
            </div>

            <!-- Chat Panel -->
            <div id="chatPanel" class="chat-panel hidden">
                <h3 style="margin: 0 0 10px 0; color: #ffd700;">Chat</h3>
                <div id="chatMessages"></div>
                <div class="chat-input-container">
                    <input type="text" id="chatInput" placeholder="Type message..." style="flex: 1;" onkeypress="if(event.key==='Enter') sendChat()">
                    <button onclick="sendChat()">Send</button>
                </div>
            </div>

            <!-- Loading Screen -->
            <div id="loading" class="loading">
                Connecting to game server...
            </div>
        </div>
    </div>

    <script>
        // Game State
        let ws = null;
        let scene, camera, renderer;
        let pokerTable, cards = [], chips = [];
        let gameState = null;
        let isConnected = false;
        let isPlayer = false;
        let currentRoom = null;

        // Initialize Three.js scene
        function initThreeJS() {
            const canvas = document.getElementById('canvas');
            
            // Scene
            scene = new THREE.Scene();
            scene.background = new THREE.Color(0x0a2a1f);

            // Camera
            camera = new THREE.PerspectiveCamera(75, window.innerWidth / window.innerHeight, 0.1, 1000);
            camera.position.set(0, 8, 12);
            camera.lookAt(0, 0, 0);

            // Renderer
            renderer = new THREE.WebGLRenderer({ canvas: canvas, antialias: true });
            renderer.setSize(window.innerWidth, window.innerHeight);
            renderer.shadowMap.enabled = true;
            renderer.shadowMap.type = THREE.PCFSoftShadowMap;

            // Lighting
            const ambientLight = new THREE.AmbientLight(0x404040, 0.4);
            scene.add(ambientLight);

            const directionalLight = new THREE.DirectionalLight(0xffffff, 0.8);
            directionalLight.position.set(10, 10, 5);
            directionalLight.castShadow = true;
            directionalLight.shadow.mapSize.width = 2048;
            directionalLight.shadow.mapSize.height = 2048;
            scene.add(directionalLight);

            const pointLight = new THREE.PointLight(0xffd700, 0.6, 100);
            pointLight.position.set(0, 5, 0);
            scene.add(pointLight);

            // Create poker table
            createPokerTable();

            // Start render loop
            animate();
        }

        function createPokerTable() {
            // Table surface
            const tableGeometry = new THREE.CylinderGeometry(6, 6, 0.3, 32);
            const tableMaterial = new THREE.MeshLambertMaterial({ color: 0x0d4d2a });
            pokerTable = new THREE.Mesh(tableGeometry, tableMaterial);
            pokerTable.position.y = -0.15;
            pokerTable.receiveShadow = true;
            scene.add(pokerTable);

            // Table edge
            const edgeGeometry = new THREE.TorusGeometry(6, 0.2, 8, 32);
            const edgeMaterial = new THREE.MeshLambertMaterial({ color: 0x8b4513 });
            const tableEdge = new THREE.Mesh(edgeGeometry, edgeMaterial);
            tableEdge.position.y = 0;
            scene.add(tableEdge);

            // Table felt pattern
            const feltGeometry = new THREE.CylinderGeometry(5.5, 5.5, 0.05, 32);
            const feltMaterial = new THREE.MeshLambertMaterial({ color: 0x1a5d3a });
            const tableFelt = new THREE.Mesh(feltGeometry, feltMaterial);
            tableFelt.position.y = 0.2;
            scene.add(tableFelt);
        }

        function createCard(suit, rank, position, rotation = 0) {
            // Card geometry
            const cardGeometry = new THREE.PlaneGeometry(0.8, 1.2);
            
            // Card material (simplified - just colors)
            let cardColor = 0xffffff;
            if (suit === 'back') {
                cardColor = 0x4444aa;
            } else if (suit === 'hearts' || suit === 'diamonds') {
                cardColor = 0xffaaaa;
            }
            
            const cardMaterial = new THREE.MeshLambertMaterial({ 
                color: cardColor,
                side: THREE.DoubleSide
            });
            
            const card = new THREE.Mesh(cardGeometry, cardMaterial);
            card.position.copy(position);
            card.rotation.x = -Math.PI / 2;
            card.rotation.z = rotation;
            card.castShadow = true;
            
            // Add text (simplified)
            if (suit !== 'back') {
                const textGeometry = new THREE.PlaneGeometry(0.3, 0.3);
                const textMaterial = new THREE.MeshBasicMaterial({ 
                    color: (suit === 'hearts' || suit === 'diamonds') ? 0xff0000 : 0x000000,
                    transparent: true
                });
                const text = new THREE.Mesh(textGeometry, textMaterial);
                text.position.set(position.x, position.y + 0.01, position.z);
                text.rotation.x = -Math.PI / 2;
                text.rotation.z = rotation;
                scene.add(text);
            }
            
            return card;
        }

        function createChip(value, position) {
            const chipGeometry = new THREE.CylinderGeometry(0.3, 0.3, 0.1, 16);
            let chipColor = 0xffffff;
            
            if (value >= 100) chipColor = 0x000000;
            else if (value >= 50) chipColor = 0x0066cc;
            else if (value >= 25) chipColor = 0x00cc00;
            else if (value >= 10) chipColor = 0xffaa00;
            else chipColor = 0xff0000;
            
            const chipMaterial = new THREE.MeshLambertMaterial({ color: chipColor });
            const chip = new THREE.Mesh(chipGeometry, chipMaterial);
            chip.position.copy(position);
            chip.castShadow = true;
            
            return chip;
        }

        function updateTableVisuals() {
            // Clear existing cards and chips
            cards.forEach(card => scene.remove(card));
            chips.forEach(chip => scene.remove(chip));
            cards = [];
            chips = [];

            if (!gameState) return;

            // Community cards
            gameState.community_cards.forEach((card, index) => {
                const position = new THREE.Vector3(-2 + index, 0.25, 0);
                const cardMesh = createCard(card.suit, card.rank, position);
                scene.add(cardMesh);
                cards.push(cardMesh);
            });

            // Player cards and positions
            const playerCount = Object.keys(gameState.players).length;
            Object.values(gameState.players).forEach((player, index) => {
                const angle = (index / playerCount) * Math.PI * 2;
                const radius = 4;
                const x = Math.cos(angle) * radius;
                const z = Math.sin(angle) * radius;
                
                // Player cards
                if (player.cards && player.cards.length > 0) {
                    player.cards.forEach((card, cardIndex) => {
                        const cardPosition = new THREE.Vector3(
                            x + (cardIndex - 0.5) * 0.5,
                            0.25,
                            z
                        );
                        const cardMesh = createCard(card.suit, card.rank, cardPosition, angle);
                        scene.add(cardMesh);
                        cards.push(cardMesh);
                    });
                }

                // Player chips (bet)
                if (player.current_bet > 0) {
                    const chipPosition = new THREE.Vector3(x * 0.7, 0.25, z * 0.7);
                    const chipMesh = createChip(player.current_bet, chipPosition);
                    scene.add(chipMesh);
                    chips.push(chipMesh);
                }
            });

            // Pot chips in center
            if (gameState.pot > 0) {
                const potPosition = new THREE.Vector3(0, 0.25, 2);
                const potChip = createChip(gameState.pot, potPosition);
                scene.add(potChip);
                chips.push(potChip);
            }
        }

        function animate() {
            requestAnimationFrame(animate);
            
            // Rotate table slowly
            if (pokerTable) {
                pokerTable.rotation.y += 0.001;
            }
            
            // Animate cards and chips
            cards.forEach((card, index) => {
                card.rotation.y = Math.sin(Date.now() * 0.001 + index) * 0.1;
            });
            
            renderer.render(scene, camera);
        }

        // WebSocket connection
        function connectWebSocket() {
            const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
            const wsUrl = `${protocol}//${window.location.host}/ws`;
            
            ws = new WebSocket(wsUrl);
            
            ws.onopen = function() {
                console.log('Connected to game server');
                isConnected = true;
                document.getElementById('loading').classList.add('hidden');
            };
            
            ws.onmessage = function(event) {
                const message = JSON.parse(event.data);
                handleServerMessage(message);
            };
            
            ws.onclose = function() {
                console.log('Disconnected from server');
                isConnected = false;
                document.getElementById('loading').classList.remove('hidden');
                document.getElementById('loading').textContent = 'Connection lost. Reconnecting...';
                
                // Attempt to reconnect
                setTimeout(connectWebSocket, 3000);
            };
            
            ws.onerror = function(error) {
                console.error('WebSocket error:', error);
            };
        }

        function sendMessage(action, payload = {}) {
            if (ws && ws.readyState === WebSocket.OPEN) {
                ws.send(JSON.stringify({ action, payload }));
            }
        }

        function handleServerMessage(message) {
            console.log('Received:', message);
            
            switch (message.type) {
                case 'room_created':
                case 'room_joined':
                    currentRoom = message.data.room_code;
                    showGameInterface();
                    break;
                    
                case 'spectating':
                    currentRoom = message.data.room_code;
                    isPlayer = false;
                    showGameInterface();
                    break;
                    
                case 'room_left':
                    showMainMenu();
                    break;
                    
                case 'game_state':
                    gameState = message.data;
                    updateGameInterface();
                    updateTableVisuals();
                    break;
                    
                case 'error':
                    alert('Error: ' + message.message);
                    break;
            }
        }

        // UI Functions
        function showMainMenu() {
            document.getElementById('menuPanel').classList.remove('hidden');
            document.getElementById('gameHUD').classList.add('hidden');
            document.getElementById('potDisplay').classList.add('hidden');
            document.getElementById('actionsPanel').classList.add('hidden');
            document.getElementById('chatPanel').classList.add('hidden');
            currentRoom = null;
            gameState = null;
            isPlayer = false;
        }

        function showGameInterface() {
            document.getElementById('menuPanel').classList.add('hidden');
            document.getElementById('gameHUD').classList.remove('hidden');
            document.getElementById('chatPanel').classList.remove('hidden');
            
            if (currentRoom) {
                document.getElementById('currentRoom').textContent = currentRoom;
            }
        }

        function updateGameInterface() {
            if (!gameState) return;

            // Update HUD
            document.getElementById('phaseText').textContent = gameState.phase.replace('_', ' ').toUpperCase();
            
            // Show/hide pot
            if (gameState.pot > 0) {
                document.getElementById('potDisplay').classList.remove('hidden');
                document.getElementById('potAmount').textContent = gameState.pot;
            } else {
                document.getElementById('potDisplay').classList.add('hidden');
            }

            // Update player money if we're a player
            if (gameState.is_player && gameState.players) {
                const myPlayerId = Object.keys(gameState.players).find(id => 
                    gameState.players[id].cards && gameState.players[id].cards.length > 0 && 
                    gameState.players[id].cards[0].suit !== 'back'
                );
                
                if (myPlayerId && gameState.players[myPlayerId]) {
                    document.getElementById('moneyAmount').textContent = gameState.players[myPlayerId].money;
                }
            }

            document.getElementById('betAmount').textContent = gameState.current_bet;

            // Show/hide start game button
            const startBtn = document.getElementById('startGameBtn');
            if (gameState.phase === 'waiting' && Object.keys(gameState.players).length >= 2) {
                startBtn.style.display = 'block';
            } else {
                startBtn.style.display = 'none';
            }

            // Show/hide action buttons
            if (gameState.is_player && gameState.phase !== 'waiting' && gameState.phase !== 'game_over') {
                document.getElementById('actionsPanel').classList.remove('hidden');
                updateActionButtons();
            } else {
                document.getElementById('actionsPanel').classList.add('hidden');
            }

            // Update chat
            updateChat();
        }

        function updateActionButtons() {
            if (!gameState || !gameState.players) return;

            const callAmount = Math.max(0, gameState.current_bet);
            document.getElementById('callAmount').textContent = callAmount;
            
            // Enable/disable buttons based on game state
            document.getElementById('checkBtn').disabled = gameState.current_bet > 0;
            document.getElementById('callBtn').disabled = gameState.current_bet === 0;
        }

        function updateChat() {
            if (!gameState || !gameState.chat_messages) return;

            const chatMessages = document.getElementById('chatMessages');
            chatMessages.innerHTML = '';
            
            gameState.chat_messages.forEach(msg => {
                const msgDiv = document.createElement('div');
                msgDiv.style.marginBottom = '5px';
                msgDiv.style.color = '#fff';
                msgDiv.innerHTML = `<strong>${msg.player_name}:</strong> ${msg.message}`;
                chatMessages.appendChild(msgDiv);
            });
            
            chatMessages.scrollTop = chatMessages.scrollHeight;
        }

        // Game Actions
        function createRoom() {
            const playerName = document.getElementById('playerName').value.trim() || 'Anonymous';
            sendMessage('create_room', { player_name: playerName });
            isPlayer = true;
        }

        function joinRoom() {
            const roomCode = document.getElementById('roomCode').value.trim().toUpperCase();
            const playerName = document.getElementById('playerName').value.trim() || 'Anonymous';
            
            if (!roomCode) {
                alert('Please enter a room code');
                return;
            }
            
            sendMessage('join_room', { room_code: roomCode, player_name: playerName });
            isPlayer = true;
        }

        function spectateRoom() {
            const roomCode = document.getElementById('roomCode').value.trim().toUpperCase();
            
            if (!roomCode) {
                alert('Please enter a room code');
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

        function playerAction(action) {
            let payload = { action_type: action };
            
            if (action === 'raise') {
                const amount = parseInt(document.getElementById('raiseAmount').value) || 0;
                payload.amount = amount;
            }
            
            sendMessage('player_action', payload);
        }

        function sendChat() {
            const chatInput = document.getElementById('chatInput');
            const message = chatInput.value.trim();
            
            if (message) {
                sendMessage('send_chat', { message });
                chatInput.value = '';
            }
        }

        // Handle window resize
        window.addEventListener('resize', function() {
            camera.aspect = window.innerWidth / window.innerHeight;
            camera.updateProjectionMatrix();
            renderer.setSize(window.innerWidth, window.innerHeight);
        });

        // Initialize everything
        window.addEventListener('load', function() {
            initThreeJS();
            connectWebSocket();
        });
    </script>
</body>
</html>
"""

# Requirements.txt content
REQUIREMENTS_TXT = """fastapi==0.104.1
uvicorn[standard]==0.24.0
websockets==12.0
pydantic==2.5.0
redis==5.0.1
python-multipart==0.0.6
"""

if __name__ == "__main__":
    port = int(os.environ.get("PORT", 8000))
    uvicorn.run(app, host="0.0.0.0", port=port)
