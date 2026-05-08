// Shape Definitions (from Lean 4 source)
const SHAPES = {
    Monomino: [[0, 0]],
    Domino: [[0, 0], [1, 0]],
    Tromino_I: [[0, 0], [1, 0], [2, 0]],
    Tromino_L: [[0, 0], [1, 0], [0, 1]],
    Tetromino_O: [[0, 0], [1, 0], [0, 1], [1, 1]],
    Tetromino_I: [[0, 0], [1, 0], [2, 0], [3, 0]],
    Tetromino_T: [[0, 0], [1, 0], [2, 0], [1, 1]],
    Tetromino_L: [[0, 0], [1, 0], [2, 0], [0, 1]],
    Tetromino_S: [[0, 0], [1, 0], [1, 1], [2, 1]],
    Pentomino_F: [[1, 0], [2, 0], [0, 1], [1, 1], [1, 2]],
    Snakey_Hexomino: [[0, 0], [1, 0], [1, 1], [1, 2], [1, 3], [2, 3]]
};

// Game State
let currentTurn = 'Maker'; // 'Maker' or 'Breaker'
let board = {}; // key: "x,y", value: 'Maker' or 'Breaker'
let targetShapeName = 'Pentomino_F';
let gameMode = 'pvp';
let showPaving = false;
let gameOver = false;
let lastMove = null;
let aiThinking = false;

// D3 Configuration
const cellSize = 40;
const gridSize = 20; // 20x20 visible grid
const margin = 20;

// Initialize SVG
const svg = d3.select("#grid-svg")
    .attr("width", gridSize * cellSize + margin * 2)
    .attr("height", gridSize * cellSize + margin * 2);

const g = svg.append("g")
    .attr("transform", `translate(${margin}, ${margin})`);

const pavingG = g.append("g").attr("id", "paving-layer");
const gridG = g.append("g").attr("id", "grid-layer");
const piecesG = g.append("g").attr("id", "pieces-layer");
const winHighlightG = g.append("g").attr("id", "win-highlight-layer");

// --- Helper Functions ---

// TODO: When integrating with mathgod.org, replace this with the seed from random.org
function seededRandom() {
    return Math.random();
}

function getOrientations(shape) {
    const orientations = [];
    let current = shape.map(p => [...p]);

    for (let r = 0; r < 4; r++) {
        // Rotate 90 deg
        current = current.map(([x, y]) => [-y, x]);
        orientations.push(normalize(current));
        
        // Reflect
        const reflected = current.map(([x, y]) => [-x, y]);
        orientations.push(normalize(reflected));
    }
    
    // Remove duplicates
    const seen = new Set();
    return orientations.filter(o => {
        const key = JSON.stringify(o.sort((a, b) => a[0] - b[0] || a[1] - b[1]));
        if (seen.has(key)) return false;
        seen.add(key);
        return true;
    });
}

function normalize(shape) {
    const minX = Math.min(...shape.map(p => p[0]));
    const minY = Math.min(...shape.map(p => p[1]));
    return shape.map(([x, y]) => [x - minX, y - minY]);
}

function checkWin(player) {
    const playerPoints = Object.keys(board)
        .filter(k => board[k] === player)
        .map(k => k.split(',').map(Number));

    if (playerPoints.length === 0) return null;

    const orientations = getOrientations(SHAPES[targetShapeName]);

    // Check all player pieces as the potential start (first point) of the orientation
    for (let point of playerPoints) {
        for (let orientation of orientations) {
            const [ox0, oy0] = orientation[0];
            const originX = point[0] - ox0;
            const originY = point[1] - oy0;
            
            let allPresent = true;
            let currentShapePoints = [];
            
            for (let [ox, oy] of orientation) {
                const targetX = originX + ox;
                const targetY = originY + oy;
                if (board[`${targetX},${targetY}`] !== player) {
                    allPresent = false;
                    break;
                }
                currentShapePoints.push([targetX, targetY]);
            }

            if (allPresent) return currentShapePoints;
        }
    }
    return null;
}

function updateTurnDisplay() {
    const display = d3.select("#turn-display");
    let text = currentTurn;
    if (aiThinking) text += " (Thinking...)";
    display.text(text)
        .attr("class", `status-value turn-${currentTurn.toLowerCase()}`);
}

function drawGrid() {
    const cells = [];
    for (let i = 0; i < gridSize; i++) {
        for (let j = 0; j < gridSize; j++) {
            cells.push({x: i, y: j});
        }
    }

    const cellSelection = gridG.selectAll(".cell")
        .data(cells, d => `${d.x},${d.y}`);

    cellSelection.enter()
        .append("rect")
        .attr("class", "cell")
        .attr("x", d => d.x * cellSize)
        .attr("y", d => d.y * cellSize)
        .attr("width", cellSize)
        .attr("height", cellSize)
        .on("click", (event, d) => handleCellClick(d.x, d.y));
}

// --- AI Logic ---

function aiMove() {
    if (gameOver) return;
    
    aiThinking = true;
    updateTurnDisplay();

    let aiPlayer = currentTurn;
    let mode = (gameMode.includes('optimal')) ? 'optimal' : 'random';
    
    let validCells = [];
    for (let x = 0; x < gridSize; x++) {
        for (let y = 0; y < gridSize; y++) {
            if (!board[`${x},${y}`]) validCells.push({x, y});
        }
    }
    
    if (validCells.length === 0) {
        aiThinking = false;
        updateTurnDisplay();
        return;
    }
    
    let selectedCell = null;
    
    if (mode === 'random') {
        let adjacentCells = [];
        for (let cell of validCells) {
            // Check if adjacent to a Maker (Blue) piece
            let isAdj = false;
            let dirs = [[0,1], [0,-1], [1,0], [-1,0]];
            for (let [dx, dy] of dirs) {
                if (board[`${cell.x + dx},${cell.y + dy}`] === 'Maker') {
                    isAdj = true;
                    break;
                }
            }
            if (isAdj) adjacentCells.push(cell);
        }
        
        // If there are adjacent cells, pick from them. Otherwise, pick from any valid cell.
        let pool = adjacentCells.length > 0 ? adjacentCells : validCells;
        selectedCell = pool[Math.floor(seededRandom() * pool.length)];
    } else {
        selectedCell = getOptimalMove(aiPlayer, validCells);
    }
    
    if (selectedCell) {
        setTimeout(() => {
            aiThinking = false;
            handleCellClick(selectedCell.x, selectedCell.y, true);
        }, 600); // Slightly longer delay to show "Thinking"
    } else {
        aiThinking = false;
        updateTurnDisplay();
    }
}

function getOptimalMove(player, validCells) {
    // 1. Paving Strategy for Breaker vs Boxy (Tetromino_O)
    if (player === 'Breaker' && targetShapeName === 'Tetromino_O' && lastMove && lastMove.player === 'Maker') {
        let x = lastMove.x;
        let y = lastMove.y;
        let px, py;
        if (y % 2 === 0) {
            px = (x % 2 === 0) ? x + 1 : x - 1;
        } else {
            px = (x % 2 === 1) ? x + 1 : x - 1;
        }
        py = y;
        if (px >= 0 && px < gridSize && !board[`${px},${py}`]) {
            return {x: px, y: py};
        }
    }
    
    // 2. General Heuristic
    let scores = {};
    const orientations = getOrientations(SHAPES[targetShapeName]);
    
    for (let x = 0; x < gridSize; x++) {
        for (let y = 0; y < gridSize; y++) {
            for (let orientation of orientations) {
                let m = 0;
                let b = 0;
                let valid = true;
                let cells = [];
                for (let [ox, oy] of orientation) {
                    let tx = x + ox;
                    let ty = y + oy;
                    if (tx < 0 || tx >= gridSize || ty < 0 || ty >= gridSize) {
                        valid = false;
                        break;
                    }
                    let owner = board[`${tx},${ty}`];
                    if (owner === 'Maker') m++;
                    else if (owner === 'Breaker') b++;
                    cells.push(`${tx},${ty}`);
                }
                
                if (!valid) continue;
                
                if (player === 'Maker') {
                    if (b === 0) { // Shape viable for Maker
                        let score = Math.pow(10, m); 
                        for (let c of cells) {
                            if (!board[c]) {
                                scores[c] = (scores[c] || 0) + score;
                            }
                        }
                    }
                } else {
                    // Breaker: block Maker's most dangerous threats
                    if (b === 0) {
                        let score = Math.pow(10, m);
                        for (let c of cells) {
                            if (!board[c]) {
                                scores[c] = (scores[c] || 0) + score;
                            }
                        }
                    }
                }
            }
        }
    }
    
    let bestCell = null;
    let bestScore = -1;
    let cx = gridSize / 2;
    let cy = gridSize / 2;
    
    for (let cell of validCells) {
        let key = `${cell.x},${cell.y}`;
        // Base score from heuristics
        let score = (scores[key] || 0);
        
        // Add tiny weight to prefer center (especially good for first moves)
        score += (2 - (Math.abs(cell.x - cx) + Math.abs(cell.y - cy)) / 10);
        
        // Add random noise to break exact ties
        score += seededRandom() * 0.1;
        
        if (score > bestScore) {
            bestScore = score;
            bestCell = cell;
        }
    }
    
    return bestCell;
}

function checkAITurn() {
    if (gameOver) return;
    const isAITurn = (gameMode === 'p_vs_ai_random' || gameMode === 'p_vs_ai_optimal') && currentTurn === 'Breaker' ||
                     (gameMode === 'ai_random_vs_p' || gameMode === 'ai_optimal_vs_p') && currentTurn === 'Maker';
                     
    if (isAITurn) {
        aiMove();
    }
}

// --- Main Game Actions ---

function handleCellClick(x, y, isAI = false) {
    if (gameOver) return;
    
    const isAITurn = (gameMode === 'p_vs_ai_random' || gameMode === 'p_vs_ai_optimal') && currentTurn === 'Breaker' ||
                     (gameMode === 'ai_random_vs_p' || gameMode === 'ai_optimal_vs_p') && currentTurn === 'Maker';
                     
    if (isAITurn && !isAI) return; // Prevent human from clicking during AI turn

    const key = `${x},${y}`;
    if (board[key]) return;

    board[key] = currentTurn;
    lastMove = {x, y, player: currentTurn};
    renderPieces();

    const winPoints = checkWin(currentTurn);
    if (winPoints) {
        gameOver = true;
        highlightWin(winPoints);
        d3.select("#win-status").style("display", "block");
        d3.select("#winner-name").text(`${currentTurn.toUpperCase()} WINS!`);
        return;
    }

    currentTurn = currentTurn === 'Maker' ? 'Breaker' : 'Maker';
    updateTurnDisplay();
    
    checkAITurn();
}

function renderPieces() {
    const pieces = Object.entries(board).map(([key, player]) => {
        const [x, y] = key.split(',').map(Number);
        return {x, y, player};
    });

    const pieceSelection = piecesG.selectAll(".piece")
        .data(pieces, d => `${d.x},${d.y}`);

    pieceSelection.enter()
        .append("circle")
        .attr("class", d => `piece ${d.player.toLowerCase()}-piece`)
        .attr("cx", d => d.x * cellSize + cellSize / 2)
        .attr("cy", d => d.y * cellSize + cellSize / 2)
        .attr("r", 0)
        .transition()
        .duration(300)
        .attr("r", cellSize * 0.35);

    pieceSelection.exit().remove();
}

function highlightWin(points) {
    winHighlightG.selectAll(".winning-highlight")
        .data(points)
        .enter()
        .append("rect")
        .attr("class", "winning-highlight")
        .attr("x", d => d[0] * cellSize)
        .attr("y", d => d[1] * cellSize)
        .attr("width", cellSize)
        .attr("height", cellSize)
        .attr("rx", 4)
        .style("opacity", 0)
        .transition()
        .duration(500)
        .style("opacity", 1);
}

function updatePreview() {
    const shape = SHAPES[targetShapeName];
    const preview = d3.select("#shape-preview");
    preview.selectAll("*").remove();

    // Find bounds to center
    const minX = Math.min(...shape.map(p => p[0]));
    const maxX = Math.max(...shape.map(p => p[0]));
    const minY = Math.min(...shape.map(p => p[1]));
    const maxY = Math.max(...shape.map(p => p[1]));
    
    const width = maxX - minX + 1;
    const height = maxY - minY + 1;
    const offsetX = Math.floor((5 - width) / 2);
    const offsetY = Math.floor((5 - height) / 2);

    for (let y = 0; y < 5; y++) {
        for (let x = 0; x < 5; x++) {
            const isActive = shape.some(p => p[0] - minX + offsetX === x && p[1] - minY + offsetY === y);
            preview.append("div")
                .attr("class", `preview-cell ${isActive ? 'active' : ''}`);
        }
    }
}

function drawPaving() {
    pavingG.selectAll("*").remove();
    if (!showPaving) return;

    // Brickwork paving strategy
    // p1.y = p2.y && p1.x + 1 = p2.x && (even y, even x) || (odd y, odd x)
    for (let y = 0; y < gridSize; y++) {
        for (let x = 0; x < gridSize - 1; x++) {
            const isPairStart = (y % 2 === 0 && x % 2 === 0) || (y % 2 === 1 && x % 2 === 1);
            if (isPairStart) {
                pavingG.append("rect")
                    .attr("class", "paving-pair")
                    .attr("x", x * cellSize + 4)
                    .attr("y", y * cellSize + 4)
                    .attr("width", cellSize * 2 - 8)
                    .attr("height", cellSize - 8)
                    .attr("rx", 4);
            }
        }
    }
}

// --- Event Listeners ---

d3.select("#shape-selector").on("change", function() {
    targetShapeName = this.value;
    updatePreview();
    resetGame();
});

d3.select("#game-mode").on("change", function() {
    gameMode = this.value;
    resetGame();
});

d3.select("#reset-btn").on("click", resetGame);

d3.select("#toggle-paving").on("click", function() {
    showPaving = !showPaving;
    this.textContent = showPaving ? "Hide Paving Strategy" : "Show Paving Strategy";
    drawPaving();
});

function resetGame() {
    board = {};
    currentTurn = 'Maker';
    gameOver = false;
    lastMove = null;
    piecesG.selectAll("*").remove();
    winHighlightG.selectAll("*").remove();
    d3.select("#win-status").style("display", "none");
    updateTurnDisplay();
    checkAITurn();
}

// Initialize
function init() {
    gameMode = d3.select("#game-mode").property("value") || 'pvp';
    drawGrid();
    updatePreview();
    updateTurnDisplay();
    drawPaving();
    checkAITurn();
}

init();
