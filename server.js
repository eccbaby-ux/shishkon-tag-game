import path from 'path';
import express from 'express';
import { createServer } from 'http';
import { Server } from 'socket.io';

const app = express();
const httpServer = createServer(app);
const io = new Server(httpServer);

app.get('/', (req, res) => {
    res.sendFile(path.join(process.cwd(), 'index.html'));
});
app.use(express.static('.'));

const MAZE_SIZE = 30;
const CELL_SIZE = 52;
const PLAYER_W = 30;
const PLAYER_H = 30;
const ROUND_SECONDS = 120;

function shuffleInPlace(arr) {
    for (let i = arr.length - 1; i > 0; i--) {
        const j = Math.floor(Math.random() * (i + 1));
        [arr[i], arr[j]] = [arr[j], arr[i]];
    }
    return arr;
}

function generateMaze() {
    const maze = Array.from({ length: MAZE_SIZE }, () => Array(MAZE_SIZE).fill(1));
    const shuffledDirs = () =>
        shuffleInPlace([
            [0, 2],
            [0, -2],
            [2, 0],
            [-2, 0]
        ]);

    function carve(r, c) {
        maze[r][c] = 0;
        for (const [dr, dc] of shuffledDirs()) {
            const nr = r + dr;
            const nc = c + dc;
            if (nr >= 1 && nr < MAZE_SIZE - 1 && nc >= 1 && nc < MAZE_SIZE - 1 && maze[nr][nc] === 1) {
                maze[r + dr / 2][c + dc / 2] = 0;
                carve(nr, nc);
            }
        }
    }

    const maxR = MAZE_SIZE - 4;
    const maxStartOdd = maxR % 2 === 1 ? maxR : maxR - 1;
    const oddCount = Math.floor((maxStartOdd - 1) / 2) + 1;
    const startR = 1 + 2 * Math.floor(Math.random() * oddCount);
    const startC = 1 + 2 * Math.floor(Math.random() * oddCount);
    carve(startR, startC);

    const candidates = [];
    for (let r = 1; r < MAZE_SIZE - 1; r++) {
        for (let c = 1; c < MAZE_SIZE - 1; c++) {
            if (maze[r][c] !== 1) continue;
            const horiz = maze[r][c - 1] === 0 && maze[r][c + 1] === 0;
            const vert = maze[r - 1][c] === 0 && maze[r + 1][c] === 0;
            if (horiz || vert) candidates.push([r, c]);
        }
    }
    shuffleInPlace(candidates);
    const braidCount = Math.floor(candidates.length * 0.52);
    for (let i = 0; i < braidCount; i++) {
        const [r, c] = candidates[i];
        maze[r][c] = 0;
    }

    const extraPasses = Math.floor(candidates.length * 0.08);
    for (let i = braidCount; i < braidCount + extraPasses && i < candidates.length; i++) {
        const [r, c] = candidates[i];
        if (maze[r][c] === 1) maze[r][c] = 0;
    }

    return maze;
}

let maze = generateMaze();

function touchesWall(x, y, w, h) {
    const c0 = Math.floor(x / CELL_SIZE);
    const c1 = Math.floor((x + w - 1) / CELL_SIZE);
    const r0 = Math.floor(y / CELL_SIZE);
    const r1 = Math.floor((y + h - 1) / CELL_SIZE);
    for (let r = r0; r <= r1; r++) {
        for (let c = c0; c <= c1; c++) {
            if (r < 0 || r >= MAZE_SIZE || c < 0 || c >= MAZE_SIZE || maze[r][c] === 1) {
                return true;
            }
        }
    }
    return false;
}

function findValidSpawnPoint() {
    const pathCells = [];
    for (let r = 0; r < MAZE_SIZE; r++) {
        for (let c = 0; c < MAZE_SIZE; c++) {
            if (maze[r][c] === 0) pathCells.push({ r, c });
        }
    }
    const pick =
        pathCells.length === 0
            ? { r: 1, c: 1 }
            : pathCells[Math.floor(Math.random() * pathCells.length)];
    return {
        x: pick.c * CELL_SIZE + (CELL_SIZE - PLAYER_W) / 2,
        y: pick.r * CELL_SIZE + (CELL_SIZE - PLAYER_H) / 2
    };
}

let players = {};
let gameTimer = ROUND_SECONDS;
let taggerId = null;
let roundActive = true;

const TAG_IMMUNITY_MS = 2000;
const BOT_ID = 'BOT_1';
const BOT_TICK_MS = 33;
const BOT_STEP = 5.5;
const BOT_NODE_REACH = 14;

let botCellPath = [];
let botWaypointIdx = 0;

function getCellOfPlayer(pl) {
    const cx = pl.x + PLAYER_W / 2;
    const cy = pl.y + PLAYER_H / 2;
    return {
        r: Math.min(MAZE_SIZE - 1, Math.max(0, Math.floor(cy / CELL_SIZE))),
        c: Math.min(MAZE_SIZE - 1, Math.max(0, Math.floor(cx / CELL_SIZE)))
    };
}

function randomWalkableCellCoords() {
    const cells = [];
    for (let r = 0; r < MAZE_SIZE; r++) {
        for (let c = 0; c < MAZE_SIZE; c++) {
            if (maze[r][c] === 0) cells.push([r, c]);
        }
    }
    if (cells.length === 0) return { r: 1, c: 1 };
    const [r, c] = cells[Math.floor(Math.random() * cells.length)];
    return { r, c };
}

function bfsPath(sr, sc, tr, tc) {
    if (maze[sr]?.[sc] !== 0 || maze[tr]?.[tc] !== 0) return null;
    const parent = Object.create(null);
    const startKey = `${sr},${sc}`;
    parent[startKey] = null;
    const q = [[sr, sc]];
    const dirs = [
        [0, 1],
        [1, 0],
        [0, -1],
        [-1, 0]
    ];
    while (q.length) {
        const [r, c] = q.shift();
        if (r === tr && c === tc) {
            const out = [];
            let k = `${r},${c}`;
            while (k) {
                const [rr, cc] = k.split(',').map(Number);
                out.unshift([rr, cc]);
                k = parent[k];
            }
            return out;
        }
        for (const [dr, dc] of dirs) {
            const nr = r + dr;
            const nc = c + dc;
            if (nr < 0 || nr >= MAZE_SIZE || nc < 0 || nc >= MAZE_SIZE) continue;
            if (maze[nr][nc] !== 0) continue;
            const nk = `${nr},${nc}`;
            if (nk in parent) continue;
            parent[nk] = `${r},${c}`;
            q.push([nr, nc]);
        }
    }
    return null;
}

function nearestHuman(bot) {
    let best = null;
    let bestD = Infinity;
    for (const id in players) {
        const p = players[id];
        if (p.isBot) continue;
        const d = Math.hypot(p.x - bot.x, p.y - bot.y);
        if (d < bestD) {
            bestD = d;
            best = p;
        }
    }
    return best;
}

function resetBotPathState() {
    botCellPath = [];
    botWaypointIdx = 0;
}

function replanBotPath() {
    const bot = players[BOT_ID];
    if (!bot) return;
    const { r: sr, c: sc } = getCellOfPlayer(bot);
    if (maze[sr][sc] !== 0) return;
    for (let tries = 0; tries < 16; tries++) {
        let tr;
        let tc;
        if (bot.isTagger) {
            const h = nearestHuman(bot);
            if (h) {
                const t = getCellOfPlayer(h);
                tr = t.r;
                tc = t.c;
            } else {
                const w = randomWalkableCellCoords();
                tr = w.r;
                tc = w.c;
            }
        } else {
            const w = randomWalkableCellCoords();
            tr = w.r;
            tc = w.c;
        }
        const path = bfsPath(sr, sc, tr, tc);
        if (path && path.length >= 2) {
            botCellPath = path;
            botWaypointIdx = 1;
            return;
        }
    }
    resetBotPathState();
}

function stepBotAlongPath() {
    const bot = players[BOT_ID];
    if (!bot || botCellPath.length === 0 || botWaypointIdx >= botCellPath.length) return;
    const [wr, wc] = botCellPath[botWaypointIdx];
    const targetX = wc * CELL_SIZE + (CELL_SIZE - PLAYER_W) / 2;
    const targetY = wr * CELL_SIZE + (CELL_SIZE - PLAYER_H) / 2;
    const dx = targetX - bot.x;
    const dy = targetY - bot.y;
    const dist = Math.hypot(dx, dy);
    if (dist < BOT_NODE_REACH) {
        botWaypointIdx++;
        if (botWaypointIdx >= botCellPath.length) {
            resetBotPathState();
        }
        return;
    }
    const step = Math.min(BOT_STEP, dist);
    let nx = bot.x;
    let ny = bot.y;
    if (Math.abs(dx) >= Math.abs(dy)) {
        nx += Math.sign(dx) * Math.min(step, Math.abs(dx));
    } else {
        ny += Math.sign(dy) * Math.min(step, Math.abs(dy));
    }
    if (!touchesWall(nx, ny, PLAYER_W, PLAYER_H)) {
        bot.x = nx;
        bot.y = ny;
        return;
    }
    const tryNx = bot.x + Math.sign(dx) * Math.min(step, Math.abs(dx));
    if (!touchesWall(tryNx, bot.y, PLAYER_W, PLAYER_H)) {
        bot.x = tryNx;
        return;
    }
    const tryNy = bot.y + Math.sign(dy) * Math.min(step, Math.abs(dy));
    if (!touchesWall(bot.x, tryNy, PLAYER_W, PLAYER_H)) {
        bot.y = tryNy;
        return;
    }
    resetBotPathState();
}

function applyTag(oldTaggerId, newTaggerId) {
    const T = players[oldTaggerId];
    const N = players[newTaggerId];
    if (!T || !N) return;
    T.isTagger = false;
    T.immuneUntil = Date.now() + TAG_IMMUNITY_MS;
    N.isTagger = true;
    N.immuneUntil = 0;
    taggerId = newTaggerId;
    io.emit('tagEvent', {
        oldTagger: oldTaggerId,
        newTagger: newTaggerId,
        immuneUntil: T.immuneUntil
    });
}

function attemptTagFrom(taggerPlId) {
    const tagger = players[taggerPlId];
    if (!tagger || !tagger.isTagger) return;
    for (const id in players) {
        if (id === taggerPlId) continue;
        const p = players[id];
        const dist = Math.hypot(p.x - tagger.x, p.y - tagger.y);
        if (dist < 30 && Date.now() > (p.immuneUntil || 0)) {
            applyTag(taggerPlId, id);
            return;
        }
    }
}

function createBotPlayer() {
    const spawn = findValidSpawnPoint();
    return {
        x: spawn.x,
        y: spawn.y,
        id: BOT_ID,
        name: 'Bot-Terminator',
        color: '#00b894',
        isTagger: false,
        immuneUntil: 0,
        isBot: true
    };
}

function ensureBotInGame() {
    if (players[BOT_ID]) return;
    players[BOT_ID] = createBotPlayer();
    const ids = Object.keys(players);
    for (const id of ids) players[id].isTagger = false;
    const tagger = ids[Math.floor(Math.random() * ids.length)];
    players[tagger].isTagger = true;
    taggerId = tagger;
    resetBotPathState();
}

function playerPayload(pl) {
    const now = Date.now();
    const until = pl.immuneUntil ?? 0;
    return {
        x: pl.x,
        y: pl.y,
        id: pl.id,
        name: pl.name,
        color: pl.color,
        isTagger: pl.isTagger,
        immuneUntil: until,
        isImmune: now < until,
        isBot: !!pl.isBot
    };
}

function playersForClients() {
    const now = Date.now();
    const out = {};
    for (const id in players) {
        const pl = players[id];
        const until = pl.immuneUntil ?? 0;
        out[id] = {
            x: pl.x,
            y: pl.y,
            id: pl.id,
            name: pl.name,
            color: pl.color,
            isTagger: pl.isTagger,
            immuneUntil: until,
            isImmune: now < until,
            isBot: !!pl.isBot
        };
    }
    return out;
}

function randomPlayerColor() {
    return '#' + Math.floor(Math.random() * 16777215).toString(16).padStart(6, '0');
}

function sanitizePlayerName(raw) {
    let name = typeof raw === 'string' ? raw.trim() : '';
    if (!name) name = 'Player';
    if (name.length > 24) name = name.slice(0, 24);
    return name;
}

function resetGame() {
    maze = generateMaze();
    gameTimer = ROUND_SECONDS;
    const ids = Object.keys(players);
    for (const id of ids) {
        const pos = findValidSpawnPoint();
        players[id].x = pos.x;
        players[id].y = pos.y;
        players[id].isTagger = false;
        players[id].immuneUntil = 0;
    }
    if (ids.length > 0) {
        const tagger = ids[Math.floor(Math.random() * ids.length)];
        players[tagger].isTagger = true;
        taggerId = tagger;
    } else {
        taggerId = null;
    }
    resetBotPathState();
    io.emit('gameReset', {
        maze,
        cellSize: CELL_SIZE,
        size: MAZE_SIZE,
        players: playersForClients(),
        timer: gameTimer
    });
}

setInterval(() => {
    if (!roundActive) return;
    if (gameTimer > 0 && Object.keys(players).length > 0) {
        gameTimer--;
        io.emit('timerUpdate', gameTimer);
        if (gameTimer === 0) {
            roundActive = false;
            io.emit('gameOver', taggerId);
            setTimeout(() => {
                resetGame();
                roundActive = true;
            }, 5000);
        }
    }
}, 1000);

io.on('connection', (socket) => {
    console.log('חיבור חדש:', socket.id);

    socket.on('joinGame', (payload) => {
        if (players[socket.id]) return;

        const name = sanitizePlayerName(payload && payload.name);
        const spawn = findValidSpawnPoint();
        players[socket.id] = {
            x: spawn.x,
            y: spawn.y,
            id: socket.id,
            name,
            color: randomPlayerColor(),
            isTagger: false,
            immuneUntil: 0
        };

        socket.emit('mazeData', {
            maze,
            cellSize: CELL_SIZE,
            size: MAZE_SIZE
        });
        io.emit('currentPlayers', playersForClients());
    });

    // עדכון תנועה
    socket.on('playerMovement', (movementData) => {
        if (players[socket.id]) {
            const nx = movementData.x;
            const ny = movementData.y;
            if (touchesWall(nx, ny, PLAYER_W, PLAYER_H)) {
                socket.emit('positionCorrection', {
                    x: players[socket.id].x,
                    y: players[socket.id].y
                });
                return;
            }
            players[socket.id].x = nx;
            players[socket.id].y = ny;

            attemptTagFrom(socket.id);
            socket.broadcast.emit('playerMoved', playerPayload(players[socket.id]));
        }
    });

    socket.on('disconnect', () => {
        if (!players[socket.id]) return;
        const wasTagger = taggerId === socket.id;
        delete players[socket.id];
        io.emit('playerDisconnected', socket.id);
        if (wasTagger) {
            const ids = Object.keys(players);
            if (ids.length > 0) {
                for (const id of ids) players[id].isTagger = false;
                const next = ids[Math.floor(Math.random() * ids.length)];
                players[next].isTagger = true;
                players[next].immuneUntil = 0;
                taggerId = next;
                io.emit('currentPlayers', playersForClients());
            } else {
                taggerId = null;
            }
        }
    });
});

setInterval(() => {
    if (!roundActive || !players[BOT_ID]) return;
    const bot = players[BOT_ID];
    if (botCellPath.length === 0 || botWaypointIdx >= botCellPath.length) {
        replanBotPath();
    } else if (bot.isTagger) {
        const h = nearestHuman(bot);
        if (h) {
            const { r, c } = getCellOfPlayer(h);
            const end = botCellPath[botCellPath.length - 1];
            if (!end || end[0] !== r || end[1] !== c) replanBotPath();
        }
    }
    stepBotAlongPath();
    if (botCellPath.length === 0) replanBotPath();
    attemptTagFrom(BOT_ID);
    io.emit('playerMoved', playerPayload(bot));
}, BOT_TICK_MS);

ensureBotInGame();

const PORT = Number(process.env.PORT) || 3000;
httpServer.listen(PORT, () => {
    console.log(`השרת רץ על פורט ${PORT}`);
});