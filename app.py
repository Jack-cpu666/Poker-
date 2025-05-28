# app.py
import os, json, uuid, random, string
import asyncio
from fastapi import FastAPI, WebSocket, WebSocketDisconnect
from fastapi.responses import HTMLResponse
from fastapi.middleware.cors import CORSMiddleware
from dotenv import load_dotenv

load_dotenv()

app = FastAPI()
app.add_middleware(CORSMiddleware, allow_origins=["*"], allow_methods=["*"], allow_headers=["*"])

def gen_code():
    return "".join(random.choice(string.ascii_uppercase + string.digits) for _ in range(6))

class Room:
    def __init__(self, code, max_players, is_private, password):
        self.code = code
        self.max_players = max_players
        self.is_private = is_private
        self.password = password or ""
        self.players: dict[str, WebSocket] = {}
        self.spectators: dict[str, WebSocket] = {}
        self.deck: list[str] = []
        self.hands: dict[str, list[str]] = {}

    def build_deck(self):
        suits = ["♠","♥","♦","♣"]
        ranks = ["A","2","3","4","5","6","7","8","9","10","J","Q","K"]
        self.deck = [f"{r}-{s}" for s in suits for r in ranks]
        random.shuffle(self.deck)

    def deal_hands(self, num_cards=5):
        self.build_deck()
        for uid in self.players:
            self.hands[uid] = [ self.deck.pop() for _ in range(num_cards) ]
        return self.hands

    async def broadcast(self, action: str, payload: dict):
        msg = json.dumps({"action": action, "payload": payload})
        conns = list(self.players.values()) + list(self.spectators.values())
        for ws in conns:
            await ws.send_text(msg)

rooms: dict[str, Room] = {}

@app.get("/")
async def homepage():
    html = r"""
<!DOCTYPE html>
<html>
<head>
    <meta charset="utf-8"><title>Multiplayer Card Game</title>
    <style>
      body { margin:0; overflow:hidden; }
      #ui { position:absolute; top:10px; left:10px; background:rgba(255,255,255,0.8); padding:8px; border-radius:6px; }
      #chat { position:absolute; bottom:10px; left:10px; background:rgba(255,255,255,0.8); padding:8px; border-radius:6px; max-height:200px; overflow-y:auto; }
      #messages { list-style:none; padding:0; margin:0; max-height:140px; overflow-y:auto; }
    </style>
</head>
<body>
  <div id="ui">
    <input id="roomCodeInput" placeholder="Room Code"/>
    <button onclick="createRoom()">Create</button>
    <button onclick="joinRoom()">Join</button>
    <button onclick="dealCards()">Deal</button>
  </div>
  <div id="chat">
    <ul id="messages"></ul>
    <input id="chatInput" placeholder="Message"/>
    <button onclick="sendChat()">Send</button>
  </div>
  <canvas id="gameCanvas"></canvas>
  <script src="https://cdnjs.cloudflare.com/ajax/libs/three.js/r128/three.min.js"></script>
  <script>
    const ws = new WebSocket(`ws://${location.host}/ws`);
    let userId = null, hands = {};
    ws.onmessage = evt => {
      const {action,payload:p} = JSON.parse(evt.data);
      if(action==="room_created"){
        alert("Room: "+p.room_code);
        userId = p.user_id;
      }
      else if(action==="room_update"){
        console.log("Players:",p.players);
      }
      else if(action==="deal_cards"){
        hands = p.hands;
        renderHands();
      }
      else if(action==="draw_card"){
        const {player_id,card} = p;
        hands[player_id] = hands[player_id]||[];
        hands[player_id].push(card);
        renderHands();
      }
      else if(action==="play_card"){
        const {player_id,card} = p;
        const idx = hands[player_id]?.indexOf(card);
        if(idx>=0) hands[player_id].splice(idx,1);
        renderHands();
        animatePlay(card,player_id);
      }
      else if(action==="chat_message"){
        const {player_id,message} = p;
        let li = document.createElement("li");
        li.textContent = player_id+": "+message;
        document.getElementById("messages").appendChild(li);
      }
    };
    function createRoom(){ ws.send(JSON.stringify({action:"create_room",payload:{max_players:4,is_private:false}})); }
    function joinRoom(){
      let code = document.getElementById("roomCodeInput").value;
      ws.send(JSON.stringify({action:"join_room",payload:{room_code:code}}));
    }
    function dealCards(){ ws.send(JSON.stringify({action:"deal_cards"})); }
    function sendChat(){
      let msg = document.getElementById("chatInput").value;
      ws.send(JSON.stringify({action:"send_chat",payload:{message:msg}}));
    }

    // Three.js setup
    let scene, camera, renderer, cardMeshes = {};
    function init3D(){
      scene = new THREE.Scene();
      camera = new THREE.PerspectiveCamera(75,innerWidth/innerHeight,0.1,1000);
      renderer = new THREE.WebGLRenderer({canvas:document.getElementById("gameCanvas"),antialias:true});
      renderer.setSize(innerWidth,innerHeight);
      camera.position.z = 7;
      let light = new THREE.DirectionalLight(0xffffff,1);
      light.position.set(0,1,1);
      scene.add(light);
      animate();
    }
    function createCardMesh(card){
      let [rank,suit] = card.split("-");
      let w=1, h=1.4;
      let c = document.createElement("canvas");
      c.width=256; c.height=384;
      let ctx = c.getContext("2d");
      ctx.fillStyle="white"; ctx.fillRect(0,0,256,384);
      ctx.fillStyle="black"; ctx.font="48px serif"; ctx.fillText(rank+suit,20,60);
      let tex = new THREE.CanvasTexture(c);
      let geom = new THREE.PlaneGeometry(w,h);
      let mat = new THREE.MeshLambertMaterial({map:tex});
      return new THREE.Mesh(geom,mat);
    }
    function renderHands(){
      Object.values(cardMeshes).forEach(m=>scene.remove(m));
      cardMeshes = {};
      let posMap = [[-4,0],[ -1.5,0 ],[1.5,0],[4,0]];
      let uids = Object.keys(hands);
      uids.forEach((uid,i)=>{
        hands[uid].forEach((card,j)=>{
          let m = createCardMesh(card);
          m.position.set(posMap[i][0] + j*0.35, posMap[i][1]-2, 0);
          m.rotation.y = Math.PI; 
          scene.add(m);
          cardMeshes[`${uid}_${card}`] = m;
        });
      });
    }
    function animatePlay(card,uid){
      let key = `${uid}_${card}`;
      let m = cardMeshes[key];
      if(!m) return;
      let start = m.position.clone(), end = new THREE.Vector3(0,0,0);
      let frames = 60, count=0;
      function step(){
        count++;
        m.position.lerpVectors(start,end,count/frames);
        if(count<frames) requestAnimationFrame(step);
      }
      step();
    }
    function animate(){
      requestAnimationFrame(animate);
      renderer.render(scene,camera);
    }
    window.addEventListener("resize", ()=>{
      camera.aspect = innerWidth/innerHeight;
      camera.updateProjectionMatrix();
      renderer.setSize(innerWidth,innerHeight);
    });
    init3D();
  </script>
</body>
</html>
    """
    return HTMLResponse(html)

@app.websocket("/ws")
async def ws_endpoint(ws: WebSocket):
    await ws.accept()
    user_id = str(uuid.uuid4())
    current: Room | None = None
    try:
        while True:
            data = await ws.receive_text()
            msg = json.loads(data)
            action, payload = msg.get("action"), msg.get("payload", {})
            if action == "create_room":
                code = gen_code()
                room = Room(code, payload.get("max_players",4), payload.get("is_private",False), payload.get("password",""))
                rooms[code] = room
                current = room
                room.players[user_id] = ws
                room.hands[user_id] = []
                await ws.send_text(json.dumps({"action":"room_created","payload":{"room_code":code,"user_id":user_id}}))
            elif action == "join_room":
                code = payload.get("room_code","")
                room = rooms.get(code)
                if not room:
                    await ws.send_text(json.dumps({"action":"error","payload":{"message":"Room not found"}}))
                elif room.is_private and room.password != payload.get("password",""):
                    await ws.send_text(json.dumps({"action":"error","payload":{"message":"Invalid password"}}))
                elif len(room.players) >= room.max_players:
                    await ws.send_text(json.dumps({"action":"error","payload":{"message":"Room full"}}))
                else:
                    current = room
                    room.players[user_id] = ws
                    room.hands[user_id] = []
                    await room.broadcast("room_update",{"players":list(room.players.keys()),"spectators":list(room.spectators.keys())})
            elif action == "deal_cards" and current:
                hands = current.deal_hands()
                await current.broadcast("deal_cards",{"hands":hands})
            elif action == "draw_card" and current:
                if not current.deck: current.build_deck()
                card = current.deck.pop()
                current.hands[user_id].append(card)
                await current.broadcast("draw_card",{"player_id":user_id,"card":card})
            elif action == "play_card" and current:
                card = payload.get("card")
                if card in current.hands[user_id]:
                    current.hands[user_id].remove(card)
                    await current.broadcast("play_card",{"player_id":user_id,"card":card})
            elif action == "send_chat" and current:
                msg_txt = payload.get("message","")
                await current.broadcast("chat_message",{"player_id":user_id,"message":msg_txt})
            elif action == "spectate":
                code = payload.get("room_code","")
                room = rooms.get(code)
                if room:
                    current = room
                    room.spectators[user_id] = ws
                    await ws.send_text(json.dumps({"action":"room_update","payload":{"players":list(room.players.keys()),"spectators":list(room.spectators.keys())}}))
                else:
                    await ws.send_text(json.dumps({"action":"error","payload":{"message":"Room not found"}}))
            else:
                await ws.send_text(json.dumps({"action":"error","payload":{"message":"Unknown action"}}))
    except WebSocketDisconnect:
        if current:
            current.players.pop(user_id, None)
            current.spectators.pop(user_id, None)
            await current.broadcast("room_update",{"players":list(current.players.keys()),"spectators":list(current.spectators.keys())})
