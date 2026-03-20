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

const MAZE_SIZE = 50;
const CELL_SIZE = 52;
const PLAYER_W = 30;
const PLAYER_H = 30;

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

const maze = generateMaze();

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

function randomOpenSpawn() {
    const open = [];
    for (let r = 0; r < MAZE_SIZE; r++) {
        for (let c = 0; c < MAZE_SIZE; c++) {
            if (maze[r][c] === 0) {
                const x = c * CELL_SIZE + (CELL_SIZE - PLAYER_W) / 2;
                const y = r * CELL_SIZE + (CELL_SIZE - PLAYER_H) / 2;
                if (!touchesWall(x, y, PLAYER_W, PLAYER_H)) {
                    open.push({ x, y });
                }
            }
        }
    }
    return open[Math.floor(Math.random() * open.length)];
}

let players = {};
let gameTimer = 300;
let taggerId = null;

// לוגיקת טיימר
setInterval(() => {
    if (gameTimer > 0 && Object.keys(players).length > 0) {
        gameTimer--;
        io.emit('timerUpdate', gameTimer);
    } else if (gameTimer === 0) {
        io.emit('gameOver', taggerId);
    }
}, 1000);

io.on('connection', (socket) => {
    console.log('שחקן התחבר:', socket.id);

    const spawn = randomOpenSpawn();
    players[socket.id] = {
        x: spawn.x,
        y: spawn.y,
        id: socket.id,
        color: '#' + Math.floor(Math.random()*16777215).toString(16),
        isTagger: false
    };

    socket.emit('mazeData', {
        maze,
        cellSize: CELL_SIZE,
        size: MAZE_SIZE
    });

    // אם זה השחקן הראשון, הוא התופס
    if (Object.keys(players).length === 1) {
        players[socket.id].isTagger = true;
        taggerId = socket.id;
    }

    io.emit('currentPlayers', players);

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

            // בדיקת התנגשות (תפיסה)
            if (players[socket.id].isTagger) {
                for (let id in players) {
                    if (id !== socket.id) {
                        let p = players[id];
                        let dist = Math.hypot(p.x - players[socket.id].x, p.y - players[socket.id].y);
                        if (dist < 30) { // מרחק נגיעה
                            players[socket.id].isTagger = false;
                            players[id].isTagger = true;
                            taggerId = id;
                            io.emit('currentPlayers', players);
                        }
                    }
                }
            }
            socket.broadcast.emit('playerMoved', players[socket.id]);
        }
    });

    socket.on('disconnect', () => {
        delete players[socket.id];
        io.emit('playerDisconnected', socket.id);
    });
});

const PORT = Number(process.env.PORT) || 3000;
httpServer.listen(PORT, () => {
    console.log(`השרת רץ על פורט ${PORT}`);
});