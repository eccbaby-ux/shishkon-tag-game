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

function getHumanCount() {
    let n = 0;
    for (const id in players) {
        if (!players[id].isBot) n++;
    }
    return n;
}

const TAG_IMMUNITY_MS = 2000;
const BOT_ID = 'BOT_1';
const BOT_TICK_MS = 33;
/** Must match client BASE_MOVE_STEP in index.html. */
const HUMAN_BASE_MOVE_STEP = 6;
const BOT_STEP = HUMAN_BASE_MOVE_STEP * 2;
/** Max pixels per wall probe so 2× speed cannot skip through walls between checks. */
const BOT_COLLISION_SUBSTEP = 3;
const BOT_NODE_REACH = 14;
/** Viewport-style range: ±pixels on X/Y from bot. Humans inside are "seen" (walls do not block). */
const BOT_VISION_RANGE = 400;
const BOT_PATROL_MIN_MANHATTAN = 15;

let botCellPath = [];
let botWaypointIdx = 0;
let botWanderTr = -1;
let botWanderTc = -1;
let botLastPlannedMode = null;
let botLastGoalKey = '';
/** Last grid cell of a human while they were inside vision box; -1 = none. Used when they leave the box. */
let botLastSeenR = -1;
let botLastSeenC = -1;

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

/** Patrol target at least BOT_PATROL_MIN_MANHATTAN Manhattan steps away (reduces small loops). */
function randomPatrolCellFarFrom(sr, sc) {
    for (let attempt = 0; attempt < 100; attempt++) {
        const w = randomWalkableCellCoords();
        const man = Math.abs(w.r - sr) + Math.abs(w.c - sc);
        if (man >= BOT_PATROL_MIN_MANHATTAN) return w;
    }
    let best = randomWalkableCellCoords();
    let bestM = Math.abs(best.r - sr) + Math.abs(best.c - sc);
    for (let i = 0; i < 80; i++) {
        const w = randomWalkableCellCoords();
        const man = Math.abs(w.r - sr) + Math.abs(w.c - sc);
        if (man > bestM) {
            bestM = man;
            best = w;
        }
    }
    return best;
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

function pixelDistCenters(a, b) {
    const ax = a.x + PLAYER_W / 2;
    const ay = a.y + PLAYER_H / 2;
    const bx = b.x + PLAYER_W / 2;
    const by = b.y + PLAYER_H / 2;
    return Math.hypot(ax - bx, ay - by);
}

function isHumanInBotViewportRect(bot, human) {
    return (
        Math.abs(bot.x - human.x) <= BOT_VISION_RANGE &&
        Math.abs(bot.y - human.y) <= BOT_VISION_RANGE
    );
}

/** Humans inside vision box only (no wall / LOS check). */
function getHumansInBotViewport(bot) {
    const out = [];
    for (const id in players) {
        const p = players[id];
        if (p.isBot) continue;
        if (!isHumanInBotViewportRect(bot, p)) continue;
        out.push(p);
    }
    return out;
}

function pickClosestVisibleHuman(bot, visible) {
    let best = null;
    let bestD = Infinity;
    for (const p of visible) {
        const d = pixelDistCenters(bot, p);
        if (d < bestD) {
            bestD = d;
            best = p;
        }
    }
    return best;
}

function isHumanTaggerVisibleToBot(bot) {
    const tag = taggerId ? players[taggerId] : null;
    if (!tag || tag.isBot) return false;
    return isHumanInBotViewportRect(bot, tag);
}

/** Farthest walkable cell along ray from tagger through bot (run away). */
function fleeTargetCell(bot, tagger) {
    const bx = bot.x + PLAYER_W / 2;
    const by = bot.y + PLAYER_H / 2;
    const tx = tagger.x + PLAYER_W / 2;
    const ty = tagger.y + PLAYER_H / 2;
    let dx = bx - tx;
    let dy = by - ty;
    const len = Math.hypot(dx, dy) || 1;
    dx /= len;
    dy /= len;
    const start = getCellOfPlayer(bot);
    let bestR = start.r;
    let bestC = start.c;
    let px = bx;
    let py = by;
    const stepPx = CELL_SIZE * 0.4;
    const maxSteps = MAZE_SIZE * 4;
    for (let i = 0; i < maxSteps; i++) {
        px += dx * stepPx;
        py += dy * stepPx;
        const r = Math.min(MAZE_SIZE - 1, Math.max(0, Math.floor(py / CELL_SIZE)));
        const c = Math.min(MAZE_SIZE - 1, Math.max(0, Math.floor(px / CELL_SIZE)));
        if (maze[r][c] !== 0) break;
        bestR = r;
        bestC = c;
    }
    return { r: bestR, c: bestC };
}

function computeBotGoal(bot) {
    if (!bot.isTagger) {
        botLastSeenR = -1;
        botLastSeenC = -1;
    }

    if (bot.isTagger) {
        const visible = getHumansInBotViewport(bot);
        if (visible.length > 0) {
            const target = pickClosestVisibleHuman(bot, visible);
            const { r, c } = getCellOfPlayer(target);
            botLastSeenR = r;
            botLastSeenC = c;
            return { mode: 'chase', tr: r, tc: c };
        }
        const { r: br, c: bc } = getCellOfPlayer(bot);
        if (
            botLastSeenR >= 0 &&
            botLastSeenC >= 0 &&
            botLastSeenR < MAZE_SIZE &&
            botLastSeenC < MAZE_SIZE &&
            maze[botLastSeenR][botLastSeenC] === 0
        ) {
            if (br === botLastSeenR && bc === botLastSeenC) {
                botLastSeenR = -1;
                botLastSeenC = -1;
                botWanderTr = -1;
                botWanderTc = -1;
            } else {
                return { mode: 'pursue', tr: botLastSeenR, tc: botLastSeenC };
            }
        } else {
            botLastSeenR = -1;
            botLastSeenC = -1;
        }
        if (botWanderTr < 0) {
            const w = randomPatrolCellFarFrom(br, bc);
            botWanderTr = w.r;
            botWanderTc = w.c;
        }
        return { mode: 'wtag', tr: botWanderTr, tc: botWanderTc };
    }
    if (isHumanTaggerVisibleToBot(bot)) {
        const tag = players[taggerId];
        const f = fleeTargetCell(bot, tag);
        return { mode: 'flee', tr: f.r, tc: f.c };
    }
    if (botWanderTr < 0) {
        const { r: br, c: bc } = getCellOfPlayer(bot);
        const w = randomPatrolCellFarFrom(br, bc);
        botWanderTr = w.r;
        botWanderTc = w.c;
    }
    return { mode: 'wrun', tr: botWanderTr, tc: botWanderTc };
}

function resetBotPathState() {
    botCellPath = [];
    botWaypointIdx = 0;
}

function resetBotAiNavState() {
    resetBotPathState();
    botWanderTr = -1;
    botWanderTc = -1;
    botLastPlannedMode = null;
    botLastGoalKey = '';
    botLastSeenR = -1;
    botLastSeenC = -1;
}


function buildBotPathToGoal(bot, tr, tc) {
    const { r: sr, c: sc } = getCellOfPlayer(bot);
    if (maze[sr][sc] !== 0) return false;
    const path = bfsPath(sr, sc, tr, tc);
    if (path && path.length >= 2) {
        botCellPath = path;
        botWaypointIdx = 1;
        return true;
    }
    return false;
}

function replanBotPathForGoal(bot, goal) {
    const tr = goal.tr;
    const tc = goal.tc;
    if (goal.mode === 'wtag' || goal.mode === 'wrun') {
        const { r: sr, c: sc } = getCellOfPlayer(bot);
        let wr = tr;
        let wc = tc;
        for (let tries = 0; tries < 28; tries++) {
            if (buildBotPathToGoal(bot, wr, wc)) return;
            const w = randomPatrolCellFarFrom(sr, sc);
            wr = w.r;
            wc = w.c;
            botWanderTr = wr;
            botWanderTc = wc;
        }
    } else {
        for (let tries = 0; tries < 8; tries++) {
            if (buildBotPathToGoal(bot, tr, tc)) return;
        }
        if (goal.mode === 'pursue') {
            botLastSeenR = -1;
            botLastSeenC = -1;
        }
    }
    resetBotPathState();
    botLastGoalKey = '';
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
            botLastGoalKey = '';
            if (botLastPlannedMode === 'wtag' || botLastPlannedMode === 'wrun') {
                botWanderTr = -1;
                botWanderTc = -1;
            }
            if (botLastPlannedMode === 'pursue') {
                botLastSeenR = -1;
                botLastSeenC = -1;
                botWanderTr = -1;
                botWanderTc = -1;
            }
        }
        return;
    }
    const totalStep = Math.min(BOT_STEP, dist);
    const signX = Math.sign(dx);
    const signY = Math.sign(dy);
    const capX = Math.min(totalStep, Math.abs(dx));
    const capY = Math.min(totalStep, Math.abs(dy));
    const preferX = Math.abs(dx) >= Math.abs(dy);

    function advanceCardinal(useX, cap) {
        let rem = cap;
        while (rem > 1e-6) {
            const chunk = Math.min(BOT_COLLISION_SUBSTEP, rem);
            const nx = bot.x + (useX ? signX * chunk : 0);
            const ny = bot.y + (useX ? 0 : signY * chunk);
            if (touchesWall(nx, ny, PLAYER_W, PLAYER_H)) return false;
            bot.x = nx;
            bot.y = ny;
            rem -= chunk;
        }
        return true;
    }

    if (preferX) {
        if (advanceCardinal(true, capX)) return;
        if (advanceCardinal(false, capY)) return;
    } else {
        if (advanceCardinal(false, capY)) return;
        if (advanceCardinal(true, capX)) return;
    }
    resetBotPathState();
    botLastGoalKey = '';
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

function removeBotFromGame() {
    if (!players[BOT_ID]) return;
    delete players[BOT_ID];
    resetBotAiNavState();
    const ids = Object.keys(players);
    for (const id of ids) players[id].isTagger = false;
    if (ids.length > 0) {
        const next = ids[Math.floor(Math.random() * ids.length)];
        players[next].isTagger = true;
        taggerId = next;
    } else {
        taggerId = null;
    }
}

function ensureBotInGame() {
    if (players[BOT_ID]) return;
    players[BOT_ID] = createBotPlayer();
    const ids = Object.keys(players);
    for (const id of ids) players[id].isTagger = false;
    const tagger = ids[Math.floor(Math.random() * ids.length)];
    players[tagger].isTagger = true;
    taggerId = tagger;
    resetBotAiNavState();
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
    resetBotAiNavState();
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

        if (getHumanCount() >= 2 && players[BOT_ID]) {
            removeBotFromGame();
        } else if (getHumanCount() === 1) {
            ensureBotInGame();
        }

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
        const sid = socket.id;
        delete players[sid];
        io.emit('playerDisconnected', sid);

        const humans = getHumanCount();

        if (humans === 0) {
            if (players[BOT_ID]) {
                delete players[BOT_ID];
                resetBotAiNavState();
            }
            taggerId = null;
            io.emit('currentPlayers', playersForClients());
            return;
        }

        if (humans === 1) {
            ensureBotInGame();
            io.emit('currentPlayers', playersForClients());
            return;
        }

        if (players[BOT_ID]) removeBotFromGame();

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
    if (!roundActive) return;
    const bot = players[BOT_ID];
    if (!bot) return;
    let goal = computeBotGoal(bot);
    if (goal.mode !== botLastPlannedMode) {
        resetBotPathState();
        botLastPlannedMode = goal.mode;
        if (goal.mode === 'wtag' || goal.mode === 'wrun') {
            botWanderTr = -1;
            botWanderTc = -1;
        }
        goal = computeBotGoal(bot);
    }
    const key = `${goal.mode}|${goal.tr}|${goal.tc}`;
    if (
        key !== botLastGoalKey ||
        botCellPath.length === 0 ||
        botWaypointIdx >= botCellPath.length
    ) {
        replanBotPathForGoal(bot, goal);
        botLastGoalKey = key;
    }
    stepBotAlongPath();
    if (!players[BOT_ID]) return;
    attemptTagFrom(BOT_ID);
    const botAfter = players[BOT_ID];
    if (!botAfter) return;
    io.emit('playerMoved', playerPayload(botAfter));
}, BOT_TICK_MS);

const PORT = Number(process.env.PORT) || 3000;
httpServer.listen(PORT, () => {
    console.log(`השרת רץ על פורט ${PORT}`);
});