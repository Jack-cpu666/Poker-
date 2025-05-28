# app.py
# 0. IMPORTS
import asyncio
import json
import logging
import os
import random
import string
import uuid
from dataclasses import dataclass, field
from typing import Dict, List, Optional, Set, Tuple, Any

from fastapi import FastAPI, HTTPException, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse
from pydantic import BaseModel, Field
from starlette.websockets import WebSocketState as StarletteWebSocketState


# Load .env file for local development
from dotenv import load_dotenv
load_dotenv()

# 1. GLOBAL CONFIG & STATE
logging.basicConfig(level=logging.INFO)
logger = logging.getLogger(__name__)

PORT = int(os.getenv("PORT", "8000"))
# REDIS_URL = os.getenv("REDIS_URL") # Example of env var support
# DATABASE_URL = os.getenv("DATABASE_URL") # Example of env var support

# In-memory storage
rooms: Dict[str, "Room"] = {}
room_locks: Dict[str, asyncio.Lock] = {}
global_rooms_lock = asyncio.Lock() # Lock for modifying the 'rooms' dict itself

# 2. DATA MODELS (Pydantic for WebSocket messages, dataclasses for internal state)

# --- Game Core Models (dataclasses) ---
SUITS = ["H", "D", "C", "S"]  # Hearts, Diamonds, Clubs, Spades
RANKS = ["2", "3", "4", "5", "6", "7", "8", "9", "T", "J", "Q", "K", "A"]

@dataclass
class Card:
    id: str  # Unique ID, e.g., "H_A" for Ace of Hearts, or unique like "card_0"
    suit: str
    rank: str
    face_up: bool = False
    position: Dict[str, float] = field(default_factory=lambda: {"x": 0, "y": 0, "z": 0}) # For cards on table
    owner_id: Optional[str] = None # player_id, "deck", "table"

    def to_dict(self):
        return {
            "id": self.id, "suit": self.suit, "rank": self.rank,
            "face_up": self.face_up, "position": self.position, "owner_id": self.owner_id
        }

@dataclass
class Deck:
    cards: List[Card] = field(default_factory=list)

    def __post_init__(self):
        if not self.cards: # Only fill if cards list is empty
            self.cards = [
                Card(id=f"{suit}_{rank}", suit=suit, rank=rank)
                for suit in SUITS for rank in RANKS
            ]
            self.shuffle()

    def shuffle(self):
        random.shuffle(self.cards)
        # Reset positions and ownership for deck cards
        for i, card in enumerate(self.cards):
            card.owner_id = "deck"
            card.face_up = False
            card.position = {"x": 0, "y": 0, "z": i * 0.01} # Stacked in deck

    def draw(self) -> Optional[Card]:
        return self.cards.pop() if self.cards else None

    def add_card(self, card: Card):
        self.cards.append(card)

    def to_dict(self):
        return {"card_count": len(self.cards)}


@dataclass
class Player:
    id: str
    name: str
    ws: WebSocket
    hand: List[Card] = field(default_factory=list)
    is_host: bool = False

    async def send_json(self, data: dict):
        if self.ws.application_state == StarletteWebSocketState.CONNECTED:
            try:
                await self.ws.send_json(data)
            except Exception as e:
                logger.error(f"Error sending to player {self.id}: {e}")
        else:
            logger.warning(f"Player {self.id} websocket not connected, cannot send message.")

    def to_dict(self, include_hand_details: bool = True):
        return {
            "id": self.id,
            "name": self.name,
            "is_host": self.is_host,
            "hand_card_count": len(self.hand),
            "hand": [card.to_dict() for card in self.hand] if include_hand_details else []
        }


@dataclass
class Room:
    id: str
    players: Dict[str, Player] = field(default_factory=dict)
    spectators: List[WebSocket] = field(default_factory=list)
    deck: Deck = field(default_factory=Deck)
    table_cards: List[Card] = field(default_factory=list) # Cards played on the table
    chat_messages: List[Dict] = field(default_factory=list)
    max_players: int = 4
    is_private: bool = False
    password: Optional[str] = None
    host_id: Optional[str] = None

    async def broadcast(self, message: dict, exclude_player_ids: Optional[List[str]] = None):
        if exclude_player_ids is None:
            exclude_player_ids = []

        active_connections = []
        for p_id, player in list(self.players.items()):
            if p_id not in exclude_player_ids:
                if player.ws.application_state == StarletteWebSocketState.CONNECTED:
                    active_connections.append(player.ws.send_json(message))
                else:
                    logger.warning(f"Player {p_id} in room {self.id} disconnected, removing.")
                    # Potentially handle disconnection more robustly here
                    # For now, just log, main disconnect handler will clean up.

        for spec_ws in list(self.spectators):
             if spec_ws.application_state == StarletteWebSocketState.CONNECTED:
                active_connections.append(spec_ws.send_json(message))
             else:
                logger.warning(f"Spectator in room {self.id} disconnected, removing.")
                self.spectators.remove(spec_ws) # Basic cleanup

        if active_connections:
            await asyncio.gather(*active_connections, return_exceptions=True)


    def get_full_room_state(self, player_id_perspective: Optional[str] = None):
        # For this sandbox, all players see all hands.
        # In a real game, you might hide other players' hands.
        return {
            "room_id": self.id,
            "players": [p.to_dict(include_hand_details=True) for p in self.players.values()],
            "table_cards": [c.to_dict() for c in self.table_cards],
            "deck_state": self.deck.to_dict(),
            "chat_messages": self.chat_messages[-20:], # Last 20 messages
            "max_players": self.max_players,
            "is_private": self.is_private,
            "host_id": self.host_id
        }

    def add_player(self, player: Player):
        if len(self.players) == 0 and not self.host_id:
            player.is_host = True
            self.host_id = player.id
        self.players[player.id] = player

    def remove_player(self, player_id: str):
        if player_id in self.players:
            del self.players[player_id]
            if player_id == self.host_id: # If host leaves, assign new host or close room
                if self.players:
                    new_host_id = list(self.players.keys())[0]
                    self.players[new_host_id].is_host = True
                    self.host_id = new_host_id
                    logger.info(f"Room {self.id}: Host changed to {new_host_id}")
                    return new_host_id # Return new host ID to broadcast
                else: # No players left
                    self.host_id = None # Room effectively empty, could be cleaned up
        return None


# --- WebSocket Message Models (Pydantic) ---
class CreateRoomPayload(BaseModel):
    max_players: Optional[int] = Field(default=4, ge=1, le=8)
    is_private: Optional[bool] = False
    password: Optional[str] = None

class JoinRoomPayload(BaseModel):
    room_code: str
    password: Optional[str] = None

class SendChatPayload(BaseModel):
    message: str = Field(..., min_length=1, max_length=200)

class SpectatePayload(BaseModel):
    room_code: str

class PlayCardPayload(BaseModel):
    card_id: str
    target_position: Dict[str, float] # {x, y, z}

class DealCardsPayload(BaseModel):
    cards_per_player: Optional[int] = Field(default=5, ge=1, le=10)

class FlipCardPayload(BaseModel):
    card_id: str


# 3. HELPER FUNCTIONS
def generate_room_code(length: int = 6) -> str:
    return "".join(random.choices(string.ascii_uppercase + string.digits, k=length))

# 4. CARD ASSETS - Will be handled by Three.js dynamic texture generation

# 5. FASTAPI APP INITIALIZATION
app = FastAPI(title="Real-Time Multiplayer Card Game")

# Connection Manager (simplified)
class ConnectionManager:
    def __init__(self):
        self.active_connections: Dict[str, WebSocket] = {} # player_id -> WebSocket

    async def connect(self, websocket: WebSocket, player_id: str):
        await websocket.accept()
        self.active_connections[player_id] = websocket
        logger.info(f"Player {player_id} connected.")

    def disconnect(self, player_id: str):
        if player_id in self.active_connections:
            del self.active_connections[player_id]
        logger.info(f"Player {player_id} disconnected.")

    async def get_player_id_from_ws(self, websocket: WebSocket) -> Optional[str]:
        for p_id, ws in self.active_connections.items():
            if ws == websocket:
                return p_id
        return None

manager = ConnectionManager()


# 6. WEBSOCKET ENDPOINT
@app.websocket("/ws")
async def websocket_endpoint(websocket: WebSocket):
    player_id = str(uuid.uuid4()) # Generate unique player ID
    await manager.connect(websocket, player_id)
    current_room_code: Optional[str] = None

    try:
        while True:
            data = await websocket.receive_json()
            action = data.get("action")
            payload = data.get("payload", {})
            
            room: Optional[Room] = None
            room_lock: Optional[asyncio.Lock] = None

            if current_room_code and current_room_code in rooms: # Lock specific room for operations
                room_lock = room_locks[current_room_code]
                await room_lock.acquire()
                room = rooms.get(current_room_code) # Re-fetch room after acquiring lock
                if not room: # Room might have been deleted while waiting for lock
                    await websocket.send_json({"action": "error", "payload": {"message": "Room not found or closed."}})
                    if room_lock.locked(): room_lock.release()
                    continue

            try:
                if action == "create_room":
                    async with global_rooms_lock:
                        params = CreateRoomPayload(**payload)
                        room_code = generate_room_code()
                        while room_code in rooms:
                            room_code = generate_room_code()
                        
                        new_room = Room(
                            id=room_code, 
                            max_players=params.max_players,
                            is_private=params.is_private,
                            password=params.password
                        )
                        player = Player(id=player_id, name=f"Player_{player_id[:4]}", ws=websocket)
                        new_room.add_player(player)
                        
                        rooms[room_code] = new_room
                        room_locks[room_code] = asyncio.Lock()
                        current_room_code = room_code
                    
                    await websocket.send_json({
                        "action": "room_created",
                        "payload": {
                            "room_code": room_code,
                            "player_id": player_id,
                            "room_state": new_room.get_full_room_state(player_id)
                        }
                    })
                    logger.info(f"Player {player_id} created room {room_code}")

                elif action == "join_room":
                    params = JoinRoomPayload(**payload)
                    target_room_code = params.room_code
                    
                    async with global_rooms_lock: # Protect access to `rooms` dict briefly
                        if target_room_code not in rooms:
                            raise HTTPException(status_code=404, detail="Room not found")
                        
                        # Acquire specific room lock before modifying room state
                        target_room_lock = room_locks.get(target_room_code)
                        if not target_room_lock: # Should not happen if room exists
                             raise HTTPException(status_code=500, detail="Room lock not found")
                    
                    async with target_room_lock:
                        room_to_join = rooms.get(target_room_code)
                        if not room_to_join: # Double check after acquiring lock
                            raise HTTPException(status_code=404, detail="Room not found")

                        if room_to_join.is_private and room_to_join.password != params.password:
                            raise HTTPException(status_code=403, detail="Incorrect password")
                        if len(room_to_join.players) >= room_to_join.max_players:
                            raise HTTPException(status_code=403, detail="Room is full")

                        player = Player(id=player_id, name=f"Player_{player_id[:4]}", ws=websocket)
                        room_to_join.add_player(player)
                        current_room_code = target_room_code
                    
                    await websocket.send_json({
                        "action": "joined_room",
                        "payload": {
                            "room_code": target_room_code,
                            "player_id": player_id,
                            "room_state": room_to_join.get_full_room_state(player_id)
                        }
                    })
                    await room_to_join.broadcast({
                        "action": "player_joined",
                        "payload": {
                            "player": player.to_dict(),
                            "room_state": room_to_join.get_full_room_state()
                        }
                    }, exclude_player_ids=[player_id])
                    logger.info(f"Player {player_id} joined room {target_room_code}")

                elif action == "spectate":
                    params = SpectatePayload(**payload)
                    target_room_code = params.room_code
                    
                    async with global_rooms_lock:
                         if target_room_code not in rooms:
                            raise HTTPException(status_code=404, detail="Room not found")
                         target_room_lock = room_locks.get(target_room_code)
                         if not target_room_lock:
                             raise HTTPException(status_code=500, detail="Room lock not found")

                    async with target_room_lock:
                        room_to_spectate = rooms.get(target_room_code)
                        if not room_to_spectate:
                             raise HTTPException(status_code=404, detail="Room not found")
                        
                        room_to_spectate.spectators.append(websocket)
                        current_room_code = target_room_code # Mark as associated with this room for cleanup

                    await websocket.send_json({
                        "action": "spectating_room",
                        "payload": {"room_state": room_to_spectate.get_full_room_state()}
                    })
                    await room_to_spectate.broadcast({
                        "action": "spectator_joined",
                        "payload": {"spectator_count": len(room_to_spectate.spectators)}
                    })
                    logger.info(f"Spectator (originally player {player_id}) started spectating room {target_room_code}")

                # Actions requiring user to be in a room (room and room_lock are already acquired)
                elif room and player_id in room.players:
                    player_obj = room.players[player_id]

                    if action == "send_chat":
                        params = SendChatPayload(**payload)
                        chat_message = {"sender_id": player_id, "sender_name": player_obj.name, "message": params.message, "timestamp": asyncio.get_event_loop().time()}
                        room.chat_messages.append(chat_message)
                        await room.broadcast({"action": "new_chat_message", "payload": chat_message})
                    
                    elif action == "draw_card":
                        drawn_card = room.deck.draw()
                        if drawn_card:
                            drawn_card.owner_id = player_id
                            drawn_card.face_up = True # Player sees their own card
                            player_obj.hand.append(drawn_card)
                            
                            # Notify player about the specific card they drew
                            await player_obj.send_json({
                                "action": "card_drawn_to_hand",
                                "payload": {"card": drawn_card.to_dict()}
                            })
                            # Notify everyone about general state change
                            await room.broadcast({
                                "action": "game_state_update",
                                "payload": room.get_full_room_state()
                            })
                        else:
                            await websocket.send_json({"action": "error", "payload": {"message": "Deck is empty."}})
                    
                    elif action == "play_card": # Move card from hand OR table to table
                        params = PlayCardPayload(**payload)
                        card_to_play_id = params.card_id
                        target_pos = params.target_position
                        
                        card_found: Optional[Card] = None
                        source_location = None # "hand" or "table"

                        # Check player's hand
                        for card in player_obj.hand:
                            if card.id == card_to_play_id:
                                card_found = card
                                player_obj.hand.remove(card)
                                source_location = "hand"
                                break
                        
                        # If not in hand, check table (anyone can move table cards)
                        if not card_found:
                            for card in room.table_cards:
                                if card.id == card_to_play_id:
                                    card_found = card
                                    # No need to remove from table_cards list yet, just update its properties
                                    source_location = "table"
                                    break
                        
                        if card_found:
                            card_found.owner_id = "table"
                            card_found.position = target_pos
                            card_found.face_up = True # Cards on table usually face up

                            if source_location == "hand": # if it came from hand, add it to table
                                room.table_cards.append(card_found)
                            
                            await room.broadcast({
                                "action": "card_played",
                                "payload": {
                                    "card": card_found.to_dict(),
                                    "player_id": player_id, # who initiated the move
                                    "room_state": room.get_full_room_state()
                                }
                            })
                        else:
                            await websocket.send_json({"action": "error", "payload": {"message": "Card not found or not playable."}})

                    elif action == "flip_card":
                        params = FlipCardPayload(**payload)
                        card_to_flip_id = params.card_id
                        card_flipped: Optional[Card] = None

                        # Check player's hand (can only flip own cards)
                        for card in player_obj.hand:
                            if card.id == card_to_flip_id:
                                card.face_up = not card.face_up
                                card_flipped = card
                                break
                        
                        # Check table cards (anyone can flip table cards)
                        if not card_flipped:
                            for card in room.table_cards:
                                if card.id == card_to_flip_id:
                                    card.face_up = not card.face_up
                                    card_flipped = card
                                    break
                        
                        if card_flipped:
                            await room.broadcast({
                                "action": "card_flipped",
                                "payload": {
                                    "card_id": card_flipped.id,
                                    "face_up": card_flipped.face_up,
                                    "owner_id": card_flipped.owner_id, # To know if it's in hand or table
                                    "player_id_flipper": player_id # who initiated flip
                                }
                            })
                        else:
                             await websocket.send_json({"action": "error", "payload": {"message": "Card not found."}})

                    # Host actions
                    elif player_obj.is_host:
                        if action == "deal_cards":
                            params = DealCardsPayload(**payload)
                            cards_to_deal = params.cards_per_player
                            for _ in range(cards_to_deal):
                                for p_id_to_deal, p_obj_to_deal in room.players.items():
                                    if not room.deck.cards: break # Stop if deck empty
                                    card = room.deck.draw()
                                    if card:
                                        card.owner_id = p_id_to_deal
                                        card.face_up = False # Default to face down in hand
                                        p_obj_to_deal.hand.append(card)
                            await room.broadcast({
                                "action": "game_state_update", # Full update after dealing
                                "payload": room.get_full_room_state()
                            })

                        elif action == "shuffle_deck":
                            # Collect all cards back to deck
                            all_cards_in_play = []
                            for p in room.players.values():
                                all_cards_in_play.extend(p.hand)
                                p.hand.clear()
                            all_cards_in_play.extend(room.table_cards)
                            room.table_cards.clear()
                            
                            for card_to_return in all_cards_in_play:
                                room.deck.add_card(card_to_return)
                            
                            room.deck.shuffle()
                            await room.broadcast({
                                "action": "deck_shuffled",
                                "payload": {"room_state": room.get_full_room_state()}
                            })
                        
                        elif action == "reset_game": # Resets deck, hands, table
                            room.deck = Deck() # New shuffled deck
                            room.table_cards.clear()
                            for p_obj_reset in room.players.values():
                                p_obj_reset.hand.clear()
                            await room.broadcast({
                                "action": "game_reset",
                                "payload": {"room_state": room.get_full_room_state()}
                            })
                
                elif action == "leave_room":
                    # Handled in finally block after loop, if current_room_code is set
                    break # Exit the while loop, which will trigger cleanup

                else:
                    await websocket.send_json({"action": "error", "payload": {"message": f"Unknown action '{action}' or not in a room."}})
            
            except HTTPException as e: # For join room errors etc.
                 await websocket.send_json({"action": "error", "payload": {"message": e.detail}})
            except Exception as e: # Catch other errors during action processing
                logger.error(f"Error processing action {action} for player {player_id}: {e}", exc_info=True)
                await websocket.send_json({"action": "error", "payload": {"message": f"Server error: {str(e)}"}})
            finally:
                if room_lock and room_lock.locked():
                    room_lock.release()

    except WebSocketDisconnect:
        logger.info(f"Player {player_id} (WebSocket) disconnected.")
    except Exception as e:
        logger.error(f"Unhandled exception for player {player_id} WebSocket: {e}", exc_info=True)
    finally:
        # Cleanup on disconnect or leave_room
        manager.disconnect(player_id)
        if current_room_code and current_room_code in rooms:
            async with room_locks[current_room_code]: # Ensure exclusive access for cleanup
                room_to_leave = rooms.get(current_room_code)
                if room_to_leave:
                    is_player_in_room = player_id in room_to_leave.players
                    new_host_id = None
                    if is_player_in_room:
                        # Return cards to deck if player leaves
                        player_obj_leaving = room_to_leave.players[player_id]
                        for card_in_hand in player_obj_leaving.hand:
                            card_in_hand.owner_id = "deck"
                            card_in_hand.face_up = False
                            room_to_leave.deck.add_card(card_in_hand)
                        room_to_leave.deck.shuffle() # Shuffle after adding cards

                        new_host_id = room_to_leave.remove_player(player_id)
                        logger.info(f"Player {player_id} removed from room {current_room_code}.")
                    
                    # Remove from spectators if they were spectating
                    # A bit tricky as ws object is needed, not player_id for spectators list.
                    # Simplified: If this ws was in spectators list, remove it.
                    # Proper way: track ws objects for spectators separately.
                    if websocket in room_to_leave.spectators:
                        room_to_leave.spectators.remove(websocket)
                        logger.info(f"WebSocket (formerly player {player_id}) removed from spectators of room {current_room_code}.")

                    if not room_to_leave.players and not room_to_leave.spectators: # If room becomes empty
                        async with global_rooms_lock:
                            if current_room_code in rooms: # Check again before deleting
                                del rooms[current_room_code]
                                del room_locks[current_room_code]
                                logger.info(f"Room {current_room_code} is empty and has been closed.")
                    elif is_player_in_room: # Only broadcast if a player left (not just a spectator that never fully joined as player)
                         await room_to_leave.broadcast({
                            "action": "player_left",
                            "payload": {
                                "player_id": player_id,
                                "new_host_id": new_host_id, # If host changed
                                "room_state": room_to_leave.get_full_room_state()
                            }
                        })
        
        if websocket.application_state != StarletteWebSocketState.DISCONNECTED:
            try:
                await websocket.close()
            except Exception:
                pass # Already closed or error during close


# 7. HTTP ENDPOINT FOR FRONTEND
HTML_CONTENT = """
<!DOCTYPE html>
<html lang="en">
<head>
    <meta charset="UTF-8">
    <meta name="viewport" content="width=device-width, initial-scale=1.0">
    <title>Real-Time Card Game</title>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js"></script>
    <script src="https://cdnjs.cloudflare.com/ajax/libs/tween.js/18.6.4/tween.umd.js"></script>
    <style>
        body { margin: 0; font-family: Arial, sans-serif; display: flex; height: 100vh; background-color: #333; color: #fff; }
        #game-container { flex-grow: 1; position: relative; }
        #canvas-container { width: 100%; height: 100%; }
        #ui-container { width: 350px; background-color: #444; padding: 15px; display: flex; flex-direction: column; overflow-y: auto; }
        .ui-section { margin-bottom: 15px; padding: 10px; background-color: #555; border-radius: 5px; }
        h2, h3 { margin-top: 0; border-bottom: 1px solid #666; padding-bottom: 5px;}
        button, input { padding: 8px; margin: 5px 0; border-radius: 3px; border: none; }
        input[type="text"], input[type="password"] { width: calc(100% - 18px); background-color: #3a3a3a; color: #fff; }
        button { background-color: #007bff; color: white; cursor: pointer; }
        button:hover { background-color: #0056b3; }
        button.secondary { background-color: #6c757d; }
        button.secondary:hover { background-color: #545b62; }
        #chat-messages { height: 150px; overflow-y: scroll; border: 1px solid #666; padding: 5px; margin-bottom: 5px; background-color: #3a3a3a;}
        .chat-message { margin-bottom: 5px; font-size: 0.9em; }
        .chat-message .sender { font-weight: bold; color: #6cb2eb; }
        .player-list-item, .spectator-info { font-size: 0.9em; padding: 3px 0;}
        .player-list-item.is-host { font-weight: bold; color: #ffc107; }
        #player-info { font-size: 0.9em; }
        .card-in-hand-ui { display: inline-block; background-color: #666; padding: 5px; margin: 2px; border-radius: 3px; cursor: pointer; }
    </style>
</head>
<body>
    <div id="game-container">
        <div id="canvas-container"></div>
    </div>
    <div id="ui-container">
        <div class="ui-section">
            <h2>Connection</h2>
            <input type="text" id="room-code-input" placeholder="Room Code (leave blank to create)">
            <input type="password" id="room-password-input" placeholder="Password (if private)">
            <button id="connect-button">Create/Join Room</button>
            <button id="spectate-button">Spectate Room</button>
            <div id="player-info">Not connected.</div>
        </div>

        <div class="ui-section" id="room-info-section" style="display:none;">
            <h3>Room: <span id="current-room-code"></span></h3>
            <p>Max Players: <span id="max-players-info"></span> | Private: <span id="is-private-info"></span></p>
            <h4>Players (<span id="player-count">0</span>):</h4>
            <ul id="player-list"></ul>
            <h4>Spectators: <span id="spectator-count">0</span></h4>
            <button id="leave-room-button" class="secondary">Leave Room</button>
        </div>
        
        <div class="ui-section" id="game-actions-section" style="display:none;">
            <h3>Game Actions (Host Only)</h3>
            <input type="number" id="deal-cards-count" value="5" min="1" max="10" style="width: 50px;">
            <button id="deal-cards-button">Deal Cards</button>
            <button id="shuffle-deck-button">Shuffle All & Reset Deck</button>
            <button id="reset-game-button">Full Reset Game</button>
        </div>

        <div class="ui-section" id="player-actions-section" style="display:none;">
            <h3>Your Actions</h3>
            <button id="draw-card-button">Draw Card</button>
            <div id="my-hand-ui"><h4>Your Hand:</h4></div>
        </div>

        <div class="ui-section" id="chat-section" style="display:none;">
            <h3>Chat</h3>
            <div id="chat-messages"></div>
            <input type="text" id="chat-input" placeholder="Type message...">
            <button id="send-chat-button">Send</button>
        </div>
    </div>

    <script type="module">
        // Using type="module" for Three.js imports if needed, but CDNs handle global THREE object
        const THREE = window.THREE;
        const TWEEN = window.TWEEN;

        let scene, camera, renderer, raycaster, mouse;
        let ws;
        let myPlayerId = null;
        let currentRoomState = null;
        
        const cardObjects = {}; // Store Three.js card objects { cardId: mesh }
        const cardDimensions = { width: 0.7, height: 1, depth: 0.02 };
        const handDisplayHeight = -2.5; // Y position for player's hand cards

        // --- WebSocket Logic ---
        function connectWebSocket() {
            const protocol = window.location.protocol === 'https:' ? 'wss:' : 'ws:';
            ws = new WebSocket(`${protocol}//${window.location.host}/ws`);

            ws.onopen = () => {
                console.log("WebSocket connected.");
                document.getElementById('player-info').textContent = "Connected. Create or join a room.";
            };

            ws.onmessage = (event) => {
                const data = JSON.parse(event.data);
                console.log("Received:", data);
                handleWebSocketMessage(data);
            };

            ws.onclose = () => {
                console.log("WebSocket disconnected.");
                myPlayerId = null;
                currentRoomState = null;
                updateUIForConnectionState(false);
                // Clear scene? Or show "disconnected" message
                clearScene();
                document.getElementById('player-info').textContent = "Disconnected. Refresh to reconnect.";
            };

            ws.onerror = (error) => {
                console.error("WebSocket error:", error);
                document.getElementById('player-info').textContent = "Connection error. Refresh.";
            };
        }

        function sendMessage(action, payload) {
            if (ws && ws.readyState === WebSocket.OPEN) {
                ws.send(JSON.stringify({ action, payload }));
            } else {
                console.error("WebSocket not connected.");
            }
        }

        function handleWebSocketMessage(data) {
            const { action, payload } = data;
            switch (action) {
                case "error":
                    alert(`Error: ${payload.message}`);
                    break;
                case "room_created":
                case "joined_room":
                    myPlayerId = payload.player_id;
                    currentRoomState = payload.room_state;
                    document.getElementById('player-info').textContent = `Player ID: ${myPlayerId}`;
                    updateUIForConnectionState(true, currentRoomState.host_id === myPlayerId);
                    updateRoomUI(currentRoomState);
                    synchronizeFullScene(currentRoomState);
                    break;
                case "spectating_room":
                    currentRoomState = payload.room_state;
                     myPlayerId = null; // Spectators don't have a player ID in the game logic
                    document.getElementById('player-info').textContent = `Spectating Room: ${currentRoomState.room_id}`;
                    updateUIForConnectionState(true, false, true); // isConnected, isHost (false), isSpectator (true)
                    updateRoomUI(currentRoomState);
                    synchronizeFullScene(currentRoomState);
                    break;
                case "player_joined":
                case "player_left":
                case "game_state_update":
                case "deck_shuffled":
                case "game_reset":
                    currentRoomState = payload.room_state;
                    updateRoomUI(currentRoomState);
                    synchronizeFullScene(currentRoomState);
                    if (myPlayerId && currentRoomState.host_id === myPlayerId) {
                        document.getElementById('game-actions-section').style.display = 'block';
                    } else if (myPlayerId) {
                         document.getElementById('game-actions-section').style.display = 'none';
                    }
                    break;
                case "card_drawn_to_hand": // Specific to the player who drew
                    // Add card to local representation of hand & scene
                    const newCard = payload.card;
                    if(currentRoomState && myPlayerId) { // Add to local state and then redraw
                        const me = currentRoomState.players.find(p => p.id === myPlayerId);
                        if (me) me.hand.push(newCard);
                    }
                    updateHandUI();
                    createOrUpdateCardMesh(newCard, true); // true for animate
                    break;
                case "card_played":
                    currentRoomState = payload.room_state; // Update full state
                    updateRoomUI(currentRoomState); // Includes hand UI
                    synchronizeFullScene(currentRoomState); // Re-syncs all cards
                    break;
                case "card_flipped":
                    const { card_id, face_up, owner_id } = payload;
                    const cardMesh = cardObjects[card_id];
                    if (cardMesh) {
                        flipCardAnimation(cardMesh, face_up);
                        // Update local state representation if needed
                        const cardData = findCardInState(card_id);
                        if(cardData) cardData.face_up = face_up;
                    }
                    updateHandUI(); // In case it was a hand card
                    break;
                case "new_chat_message":
                    appendChatMessage(payload);
                    break;
                case "spectator_joined":
                    if(currentRoomState) currentRoomState.spectator_count = payload.spectator_count;
                    updateRoomUI(currentRoomState);
                    break;
            }
        }
        
        function findCardInState(cardId) {
            if (!currentRoomState) return null;
            for (let p of currentRoomState.players) {
                for (let c of p.hand) if (c.id === cardId) return c;
            }
            for (let c of currentRoomState.table_cards) if (c.id === cardId) return c;
            return null;
        }

        // --- UI Logic ---
        document.getElementById('connect-button').onclick = () => {
            const roomCode = document.getElementById('room-code-input').value.trim();
            const password = document.getElementById('room-password-input').value;
            if (roomCode) {
                sendMessage("join_room", { room_code: roomCode, password: password || undefined });
            } else {
                sendMessage("create_room", { password: password || undefined }); // Add other params later if needed
            }
        };
        
        document.getElementById('spectate-button').onclick = () => {
            const roomCode = document.getElementById('room-code-input').value.trim();
            if (roomCode) {
                sendMessage("spectate", { room_code: roomCode });
            } else {
                alert("Please enter a Room Code to spectate.");
            }
        };

        document.getElementById('leave-room-button').onclick = () => {
            sendMessage("leave_room", {});
            // UI will update on WebSocket close or server message
        };
        
        document.getElementById('send-chat-button').onclick = () => {
            const message = document.getElementById('chat-input').value;
            if (message) {
                sendMessage("send_chat", { message });
                document.getElementById('chat-input').value = "";
            }
        };
        document.getElementById('chat-input').onkeypress = (e) => {
            if (e.key === 'Enter') document.getElementById('send-chat-button').click();
        };

        document.getElementById('draw-card-button').onclick = () => sendMessage("draw_card", {});
        document.getElementById('deal-cards-button').onclick = () => {
            const count = parseInt(document.getElementById('deal-cards-count').value);
            sendMessage("deal_cards", { cards_per_player: count });
        };
        document.getElementById('shuffle-deck-button').onclick = () => sendMessage("shuffle_deck", {});
        document.getElementById('reset-game-button').onclick = () => sendMessage("reset_game", {});

        function updateUIForConnectionState(isConnected, isHost = false, isSpectator = false) {
            document.getElementById('room-info-section').style.display = isConnected ? 'block' : 'none';
            document.getElementById('chat-section').style.display = isConnected ? 'block' : 'none';
            
            if (isConnected && !isSpectator) {
                document.getElementById('player-actions-section').style.display = 'block';
                document.getElementById('game-actions-section').style.display = isHost ? 'block' : 'none';
            } else {
                document.getElementById('player-actions-section').style.display = 'none';
                document.getElementById('game-actions-section').style.display = 'none';
            }
            
            // Disable connection buttons if connected
            document.getElementById('connect-button').disabled = isConnected;
            document.getElementById('spectate-button').disabled = isConnected;
            document.getElementById('room-code-input').disabled = isConnected;
            document.getElementById('room-password-input').disabled = isConnected;
        }

        function updateRoomUI(roomState) {
            if (!roomState) return;
            document.getElementById('current-room-code').textContent = roomState.room_id;
            document.getElementById('max-players-info').textContent = roomState.max_players;
            document.getElementById('is-private-info').textContent = roomState.is_private ? 'Yes' : 'No';
            
            const playerList = document.getElementById('player-list');
            playerList.innerHTML = "";
            roomState.players.forEach(p => {
                const li = document.createElement('li');
                li.textContent = `${p.name} (${p.hand_card_count} cards)`;
                li.className = 'player-list-item';
                if (p.id === myPlayerId) li.style.color = "#a0e0ff"; // Highlight self
                if (p.id === roomState.host_id) li.classList.add('is-host');
                playerList.appendChild(li);
            });
            document.getElementById('player-count').textContent = roomState.players.length;
            document.getElementById('spectator-count').textContent = roomState.spectator_count || 0; // Spectator count from server

            updateHandUI();
        }

        function updateHandUI() {
            if (!currentRoomState || !myPlayerId) {
                document.getElementById('my-hand-ui').innerHTML = "<h4>Your Hand:</h4>";
                return;
            }
            const me = currentRoomState.players.find(p => p.id === myPlayerId);
            if (!me) {
                document.getElementById('my-hand-ui').innerHTML = "<h4>Your Hand:</h4>";
                return;
            }

            const handDiv = document.getElementById('my-hand-ui');
            handDiv.innerHTML = "<h4>Your Hand:</h4>"; // Clear previous
            me.hand.forEach(card => {
                const cardSpan = document.createElement('span');
                cardSpan.className = 'card-in-hand-ui';
                cardSpan.textContent = `${card.rank}${card.suit} (${card.face_up ? 'Up' : 'Down'})`;
                cardSpan.onclick = () => { // Click to flip
                     sendMessage("flip_card", { card_id: card.id });
                };
                // For drag-and-drop to table, this UI element could be a starting point
                // but actual dragging will be of the Three.js object.
                handDiv.appendChild(cardSpan);
            });
        }
        
        function appendChatMessage(msg) {
            const chatDiv = document.getElementById('chat-messages');
            const msgDiv = document.createElement('div');
            msgDiv.className = 'chat-message';
            
            const senderSpan = document.createElement('span');
            senderSpan.className = 'sender';
            senderSpan.textContent = `${msg.sender_name || msg.sender_id}: `;
            
            msgDiv.appendChild(senderSpan);
            msgDiv.append(document.createTextNode(msg.message));
            chatDiv.appendChild(msgDiv);
            chatDiv.scrollTop = chatDiv.scrollHeight;
        }

        // --- Three.js Scene Logic ---
        function initThreeJS() {
            const container = document.getElementById('canvas-container');
            scene = new THREE.Scene();
            scene.background = new THREE.Color(0x282c34);

            camera = new THREE.PerspectiveCamera(75, container.clientWidth / container.clientHeight, 0.1, 1000);
            camera.position.set(0, 1.5, 4); // Slightly elevated view
            camera.lookAt(0, 0, 0);

            renderer = new THREE.WebGLRenderer({ antialias: true });
            renderer.setSize(container.clientWidth, container.clientHeight);
            renderer.shadowMap.enabled = true;
            container.appendChild(renderer.domElement);

            // Lighting
            const ambientLight = new THREE.AmbientLight(0xffffff, 0.6);
            scene.add(ambientLight);
            const directionalLight = new THREE.DirectionalLight(0xffffff, 0.8);
            directionalLight.position.set(5, 10, 7.5);
            directionalLight.castShadow = true;
            scene.add(directionalLight);

            // Ground plane (table)
            const planeGeometry = new THREE.PlaneGeometry(10, 10);
            const planeMaterial = new THREE.MeshStandardMaterial({ color: 0x3D5734 }); // Green felt
            const plane = new THREE.Mesh(planeGeometry, planeMaterial);
            plane.rotation.x = -Math.PI / 2;
            plane.receiveShadow = true;
            scene.add(plane);

            // Raycasting for card interaction
            raycaster = new THREE.Raycaster();
            mouse = new THREE.Vector2();
            container.addEventListener('mousemove', onMouseMove, false);
            container.addEventListener('mousedown', onMouseDown, false);
            // Add touch events for mobile later if needed

            window.addEventListener('resize', onWindowResize, false);
            animate();
        }
        
        let selectedObject = null;
        let planeIntersect = new THREE.Vector3(); // To store intersection point with the table plane

        function onMouseMove(event) {
            event.preventDefault();
            const rect = renderer.domElement.getBoundingClientRect();
            mouse.x = ((event.clientX - rect.left) / rect.width) * 2 - 1;
            mouse.y = -((event.clientY - rect.top) / rect.height) * 2 + 1;

            if (selectedObject) {
                raycaster.setFromCamera(mouse, camera);
                const tablePlane = scene.children.find(c => c.geometry instanceof THREE.PlaneGeometry);
                const intersects = raycaster.intersectObject(tablePlane);
                if (intersects.length > 0) {
                    planeIntersect.copy(intersects[0].point);
                    // Dragging logic: update selectedObject's visual position.
                    // On mouse up, send final position to server.
                    // For now, we only use this for click. Drag to be implemented later.
                }
            }
        }

        function onMouseDown(event) {
            if (event.button !== 0) return; // Only left click

            raycaster.setFromCamera(mouse, camera);
            const cardMeshes = Object.values(cardObjects);
            const intersects = raycaster.intersectObjects(cardMeshes);

            if (intersects.length > 0) {
                const clickedCardMesh = intersects[0].object;
                const cardId = clickedCardMesh.userData.cardId;
                
                // If it's my card in hand, or a card on table, allow actions.
                const cardData = findCardInState(cardId);
                if (!cardData) return;

                if (event.ctrlKey || event.metaKey) { // Ctrl/Cmd + Click to flip
                    sendMessage("flip_card", { card_id: cardId });
                } else { // Simple click could select for dragging.
                    // For now, if it's a hand card, clicking UI element flips it.
                    // If it's a table card, this is where dragging would start.
                    // This demo uses "play_card" to move from hand -> table via UI button implicitly,
                    // or by sending explicit coords for cards already on table if UI supported.
                    // The current 'play_card' requires target_position.
                    // Simple interpretation: if card is on table, click to pick up, click again to place.
                    // More complex: drag and drop.
                    // For this simplified version, we'll not implement visual dragging.
                    // Instead, actions like "play card to center" or specific slots could be buttons.
                    // The play_card payload with {x,y,z} implies client specifies target.
                    // Let's assume user types in coords or clicks a "play to random spot" button for now.
                    // For this example, let's make click on table card move it randomly
                    if (cardData.owner_id === 'table') {
                        const randomX = (Math.random() - 0.5) * 4;
                        const randomZ = (Math.random() - 0.5) * 4;
                        sendMessage("play_card", {
                            card_id: cardId,
                            target_position: { x: randomX, y: cardDimensions.depth / 2, z: randomZ }
                        });
                    }
                }
            }
        }

        function onWindowResize() {
            const container = document.getElementById('canvas-container');
            camera.aspect = container.clientWidth / container.clientHeight;
            camera.updateProjectionMatrix();
            renderer.setSize(container.clientWidth, container.clientHeight);
        }

        function animate() {
            requestAnimationFrame(animate);
            TWEEN.update();
            renderer.render(scene, camera);
        }

        function createCardTexture(suit, rank, isFaceUp, cardWidthPx = 140, cardHeightPx = 200) {
            const canvas = document.createElement('canvas');
            canvas.width = cardWidthPx;
            canvas.height = cardHeightPx;
            const ctx = canvas.getContext('2d');

            // Background
            ctx.fillStyle = isFaceUp ? '#FFF' : '#6A0DAD'; // White for face, Purple for back
            ctx.fillRect(0, 0, cardWidthPx, cardHeightPx);
            ctx.strokeStyle = '#000';
            ctx.lineWidth = 2;
            ctx.strokeRect(1, 1, cardWidthPx - 2, cardHeightPx - 2); // Border

            if (isFaceUp) {
                // Suit and Rank
                let suitColor = (suit === 'H' || suit === 'D') ? 'red' : 'black';
                ctx.fillStyle = suitColor;
                ctx.font = 'bold 24px Arial';
                
                let suitSymbol = '';
                if (suit === 'H') suitSymbol = '♥';
                else if (suit === 'D') suitSymbol = '♦';
                else if (suit === 'C') suitSymbol = '♣';
                else if (suit === 'S') suitSymbol = '♠';

                ctx.textAlign = 'left';
                ctx.fillText(rank, 10, 30);
                ctx.fillText(suitSymbol, 10, 60);

                ctx.textAlign = 'right';
                ctx.scale(-1,1); // Flip context for bottom-right text
                ctx.fillText(rank, -cardWidthPx + 10, cardHeightPx - 15);
                ctx.scale(-1,1); // Flip back
                
                ctx.textAlign = 'center';
                ctx.font = 'bold 48px Arial';
                ctx.fillText(suitSymbol, cardWidthPx / 2, cardHeightPx / 2 + 15);
            } else {
                // Card back design (simple pattern)
                ctx.fillStyle = 'rgba(255,255,255,0.2)';
                for(let i=0; i<10; i++) {
                     ctx.beginPath();
                     ctx.arc(Math.random()*cardWidthPx, Math.random()*cardHeightPx, Math.random()*10+5, 0, Math.PI*2);
                     ctx.fill();
                }
            }
            return new THREE.CanvasTexture(canvas);
        }
        
        function createOrUpdateCardMesh(cardData, animate = false) {
            let cardMesh = cardObjects[cardData.id];
            if (!cardMesh) {
                const geometry = new THREE.BoxGeometry(cardDimensions.width, cardDimensions.height, cardDimensions.depth);
                
                // Materials for front and back
                const materials = [
                    new THREE.MeshStandardMaterial({ map: createCardTexture(cardData.suit, cardData.rank, true), side: THREE.FrontSide }), // right
                    new THREE.MeshStandardMaterial({ map: createCardTexture(cardData.suit, cardData.rank, true), side: THREE.FrontSide }), // left
                    new THREE.MeshStandardMaterial({ color: 0xeeeeee }), // top
                    new THREE.MeshStandardMaterial({ color: 0xeeeeee }), // bottom
                    new THREE.MeshStandardMaterial({ map: createCardTexture(cardData.suit, cardData.rank, true) }), // front - face
                    new THREE.MeshStandardMaterial({ map: createCardTexture(cardData.suit, cardData.rank, false) })  // back
                ];

                cardMesh = new THREE.Mesh(geometry, materials);
                cardMesh.castShadow = true;
                cardMesh.userData.cardId = cardData.id;
                scene.add(cardMesh);
                cardObjects[cardData.id] = cardMesh;

                // Initial position (e.g. off-screen or deck position)
                cardMesh.position.set(0, cardDimensions.height / 2 + 5, 0); // Start high up
            }
            
            // Update textures if face_up status changed (or initial setup)
            // This logic might need refinement based on how flipCardAnimation works
            const faceMaterialIndex = 4; 
            const backMaterialIndex = 5;
            if (cardData.face_up) {
                cardMesh.material[faceMaterialIndex].map = createCardTexture(cardData.suit, cardData.rank, true);
                cardMesh.material[backMaterialIndex].map = createCardTexture(cardData.suit, cardData.rank, false); // Ensure back is still back texture
            } else {
                cardMesh.material[faceMaterialIndex].map = createCardTexture(cardData.suit, cardData.rank, false); // Show back texture on front face if card is face down
                cardMesh.material[backMaterialIndex].map = createCardTexture(cardData.suit, cardData.rank, true); // Show face texture on back face if card is face down
            }
            cardMesh.material.forEach(m => { if(m.map) m.map.needsUpdate = true; });


            // Determine target position and rotation
            let targetPos, targetRotY;
            if (cardData.owner_id === "deck") { // Should not happen for individual card updates usually
                targetPos = { x: -3, y: cardDimensions.depth / 2 + cardData.position.z, z: 0 }; // Deck position
                targetRotY = cardData.face_up ? 0 : Math.PI;
            } else if (cardData.owner_id === "table") {
                targetPos = { x: cardData.position.x, y: cardDimensions.depth / 2 + (cardData.position.z || 0), z: cardData.position.y }; // Server y is client z
                targetRotY = cardData.face_up ? 0 : Math.PI;
            } else { // Player's hand
                const player = currentRoomState.players.find(p => p.id === cardData.owner_id);
                const playerIndex = currentRoomState.players.indexOf(player);
                const handCardIndex = player.hand.findIndex(c => c.id === cardData.id);

                if (cardData.owner_id === myPlayerId) { // Current player's hand
                    const handSpread = 3;
                    targetPos = {
                        x: (handCardIndex - (player.hand.length -1) / 2) * (cardDimensions.width + 0.1),
                        y: cardDimensions.height / 2, // Display cards upright in hand view
                        z: handDisplayHeight + 2 // Closer to camera
                    };
                    targetRotY = cardData.face_up ? 0 : Math.PI; // Y rotation for flip
                    cardMesh.rotation.x = Math.PI / 4; // Tilt hand cards for better view
                } else { // Other players' hands (simplified placeholder positions)
                    targetPos = {
                        x: -2 + playerIndex * 2, // Spread players around
                        y: cardDimensions.depth / 2,
                        z: -3 + handCardIndex * 0.05 // Stack their cards
                    };
                    targetRotY = Math.PI; // Other players' cards are face down
                }
            }
            
            const targetRotation = new THREE.Euler(cardMesh.rotation.x, targetRotY, cardMesh.rotation.z, 'YXZ');

            if (animate) {
                new TWEEN.Tween(cardMesh.position)
                    .to(targetPos, 500)
                    .easing(TWEEN.Easing.Quadratic.Out)
                    .start();
                
                // Animate rotation properly for flip
                const currentRot = { y: cardMesh.rotation.y };
                new TWEEN.Tween(currentRot)
                    .to({ y: targetRotY }, 500)
                    .easing(TWEEN.Easing.Quadratic.Out)
                    .onUpdate(() => cardMesh.rotation.y = currentRot.y)
                    .start();

            } else {
                cardMesh.position.set(targetPos.x, targetPos.y, targetPos.z);
                cardMesh.rotation.y = targetRotY;
            }
        }

        function flipCardAnimation(cardMesh, toFaceUp) {
            const targetRotY = cardMesh.rotation.y + Math.PI; // Add PI for a 180 degree flip
            
            new TWEEN.Tween(cardMesh.rotation)
                .to({ y: targetRotY }, 500)
                .easing(TWEEN.Easing.Quadratic.Out)
                .onComplete(() => {
                    // After animation, update textures to correctly show face/back
                    const cardData = findCardInState(cardMesh.userData.cardId);
                    if (cardData) {
                        const faceMaterialIndex = 4; 
                        const backMaterialIndex = 5;
                        // We assume cardData.face_up is now the new state
                        if (cardData.face_up) { // Card is now face up
                            cardMesh.material[faceMaterialIndex].map = createCardTexture(cardData.suit, cardData.rank, true);
                            cardMesh.material[backMaterialIndex].map = createCardTexture(cardData.suit, cardData.rank, false);
                        } else { // Card is now face down
                            cardMesh.material[faceMaterialIndex].map = createCardTexture(cardData.suit, cardData.rank, false); // Show back on "front face"
                            cardMesh.material[backMaterialIndex].map = createCardTexture(cardData.suit, cardData.rank, true);  // Show face on "back face"
                        }
                        cardMesh.material.forEach(m => { if(m.map) m.map.needsUpdate = true; });
                    }
                })
                .start();
        }


        function synchronizeFullScene(roomState) {
            if (!roomState) return;
            // Remove cards that are no longer in state
            const allCardIdsInState = new Set();
            roomState.players.forEach(p => p.hand.forEach(c => allCardIdsInState.add(c.id)));
            roomState.table_cards.forEach(c => allCardIdsInState.add(c.id));
            // Deck cards are not individually managed in Three.js scene, only as a count/pile visually

            for (const cardId in cardObjects) {
                if (!allCardIdsInState.has(cardId)) {
                    scene.remove(cardObjects[cardId]);
                    delete cardObjects[cardId];
                }
            }

            // Update/create cards
            roomState.players.forEach(p => {
                p.hand.forEach(cardData => createOrUpdateCardMesh(cardData, true));
            });
            roomState.table_cards.forEach(cardData => createOrUpdateCardMesh(cardData, true));
            
            // Update deck visual (e.g., a simple representation)
            updateDeckVisual(roomState.deck_state.card_count);
        }
        
        let deckMesh = null;
        function updateDeckVisual(cardCount) {
            if (deckMesh) scene.remove(deckMesh);
            if (cardCount > 0) {
                // Simple representation: a stack of cards
                const deckHeight = cardCount * cardDimensions.depth * 2; // Exaggerate height
                const geometry = new THREE.BoxGeometry(cardDimensions.width, deckHeight, cardDimensions.height); // Note: height is depth here due to rotation
                const material = new THREE.MeshStandardMaterial({map: createCardTexture(null,null,false)}); // Show back
                deckMesh = new THREE.Mesh(geometry, material);
                deckMesh.position.set(-3, deckHeight / 2, 0); // Deck position
                deckMesh.rotation.y = Math.PI / 2; // Rotate to see width/height correctly
                deckMesh.castShadow = true;
                scene.add(deckMesh);
            }
        }

        function clearScene() {
            for (const cardId in cardObjects) {
                scene.remove(cardObjects[cardId]);
            }
            if(deckMesh) scene.remove(deckMesh);
            deckMesh = null;
            Object.keys(cardObjects).forEach(key => delete cardObjects[key]);
        }
        
        // --- Initialization ---
        initThreeJS();
        connectWebSocket();

    </script>
</body>
</html>
"""

@app.get("/", response_class=HTMLResponse)
async def get_frontend():
    return HTML_CONTENT

# 8. MAIN EXECUTION BLOCK
if __name__ == "__main__":
    import uvicorn
    logger.info(f"Starting server on http://localhost:{PORT}")
    uvicorn.run("app:app", host="0.0.0.0", port=PORT, reload=True) # reload=True for dev
