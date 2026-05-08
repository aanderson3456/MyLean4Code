class VanEck {
    constructor() {
        this.lastSeen = new Map();
        this.sequence = [0];
        this.n = 0;
    }
    next() {
        let current_val = this.sequence[this.n];
        let next_val = 0;
        if (this.lastSeen.has(current_val)) {
            next_val = this.n - this.lastSeen.get(current_val);
        }
        this.lastSeen.set(current_val, this.n);
        this.n++;
        this.sequence.push(next_val);
        return {
            n: this.n,
            a: next_val,
            na: this.n - next_val
        };
    }
}

let vanEck = new VanEck();
let data = [{ n: 0, a: 0, na: 0 }];
let maxDomain = 50;
const MAX_STEPS = 20000;

// Setup D3
const svg = d3.select("#d3-plot");
const margin = { top: 20, right: 30, bottom: 30, left: 50 };
let width, height;
let xScale, yScale;
let xAxis, yAxis;
let lineN, lineA, lineNA;

let g, xAxisG, yAxisG, gridG;
let pathN, pathA, pathNA;

function initD3() {
    const container = document.querySelector('.plot-container');
    const rect = container.getBoundingClientRect();
    width = rect.width - margin.left - margin.right;
    height = rect.height - margin.top - margin.bottom;

    svg.selectAll("*").remove();

    g = svg.append("g")
        .attr("transform", `translate(${margin.left},${margin.top})`);

    xScale = d3.scaleLinear().domain([0, maxDomain]).range([0, width]);
    yScale = d3.scaleLinear().domain([0, maxDomain]).range([height, 0]);

    xAxis = d3.axisBottom(xScale).ticks(10);
    yAxis = d3.axisLeft(yScale).ticks(10);

    // Add Grid Lines
    gridG = g.append("g").attr("class", "grid");
    function updateGrid() {
        gridG.selectAll("*").remove();
        gridG.selectAll("line.horizontalGrid").data(yScale.ticks(10)).enter()
            .append("line")
            .attr("class", "grid-line")
            .attr("x1", 0).attr("x2", width).attr("y1", d => yScale(d)).attr("y2", d => yScale(d));
        gridG.selectAll("line.verticalGrid").data(xScale.ticks(10)).enter()
            .append("line")
            .attr("class", "grid-line")
            .attr("y1", 0).attr("y2", height).attr("x1", d => xScale(d)).attr("x2", d => xScale(d));
    }
    updateGrid();
    window.updateGridLines = updateGrid;

    xAxisG = g.append("g")
        .attr("class", "axis")
        .attr("transform", `translate(0,${height})`)
        .call(xAxis);

    yAxisG = g.append("g")
        .attr("class", "axis")
        .call(yAxis);

    lineN = d3.line().x(d => xScale(d.n)).y(d => yScale(d.n));
    lineA = d3.line().x(d => xScale(d.n)).y(d => yScale(d.a));
    lineNA = d3.line().x(d => xScale(d.n)).y(d => yScale(d.na));

    pathN = g.append("path").attr("class", "line-n").attr("d", lineN(data));
    pathA = g.append("path").attr("class", "line-a").attr("d", lineA(data));
    pathNA = g.append("path").attr("class", "line-na").attr("d", lineNA(data));
}

function updateD3() {
    let currentN = data[data.length - 1].n;
    if (currentN > maxDomain * 0.95) {
        maxDomain = Math.max(50, currentN * 1.5);
        xScale.domain([0, maxDomain]);
        yScale.domain([0, maxDomain]);
        
        xAxisG.transition().duration(200).call(xAxis);
        yAxisG.transition().duration(200).call(yAxis);
        window.updateGridLines();
    }

    pathN.attr("d", lineN(data));
    pathA.attr("d", lineA(data));
    pathNA.attr("d", lineNA(data));
}

window.addEventListener('resize', initD3);
initD3();

// UI Elements
const valN = document.getElementById('val-n');
const valA = document.getElementById('val-a');
const valNA = document.getElementById('val-na');

const horse1 = document.getElementById('horse-1');
const horse2 = document.getElementById('horse-2');
const horse3 = document.getElementById('horse-3');

function updateUI(item) {
    valN.textContent = item.n;
    valA.textContent = item.a;
    valNA.textContent = item.na;

    let trackMax = maxDomain;
    const pct1 = Math.min(100, Math.max(0, (item.n / trackMax) * 100));
    const pct2 = Math.min(100, Math.max(0, (item.a / trackMax) * 100));
    const pct3 = Math.min(100, Math.max(0, (item.na / trackMax) * 100));

    horse1.style.left = pct1 + '%';
    horse2.style.left = pct2 + '%';
    horse3.style.left = pct3 + '%';
}

function step() {
    let item = vanEck.next();
    data.push(item);
    updateUI(item);
    updateD3();
}

let intervalId = null;
let gallopFrame = null;
let mode = 'pause';

function setMode(newMode) {
    mode = newMode;
    
    document.querySelectorAll('.buttons button').forEach(b => b.classList.remove('active'));
    
    if (intervalId) clearInterval(intervalId);
    if (gallopFrame) cancelAnimationFrame(gallopFrame);
    intervalId = null;
    gallopFrame = null;

    if (mode === 'pause') {
        document.getElementById('btn-pause').classList.add('active');
    } else if (mode === 'walk') {
        step();
        setMode('pause'); 
    } else if (mode === 'trot') {
        document.getElementById('btn-trot').classList.add('active');
        intervalId = setInterval(step, 500);
    } else if (mode === 'cavort') {
        document.getElementById('btn-cavort').classList.add('active');
        intervalId = setInterval(step, 50);
    } else if (mode === 'gallop') {
        document.getElementById('btn-gallop').classList.add('active');
        
        function gallopStep() {
            if (mode !== 'gallop') return;
            
            let item;
            for(let i=0; i<15; i++) {
                if (data.length > MAX_STEPS) break;
                item = vanEck.next();
                data.push(item);
            }
            if (item) updateUI(item);
            updateD3();
            
            if(data.length > MAX_STEPS) {
               setMode('pause');
               alert("Ran out of steam! The horses need a rest. 🐎 (Max steps reached)");
               return;
            }
            gallopFrame = requestAnimationFrame(gallopStep);
        }
        gallopFrame = requestAnimationFrame(gallopStep);
    }
}

document.getElementById('btn-walk').addEventListener('click', () => setMode('walk'));
document.getElementById('btn-trot').addEventListener('click', () => setMode('trot'));
document.getElementById('btn-cavort').addEventListener('click', () => setMode('cavort'));
document.getElementById('btn-gallop').addEventListener('click', () => setMode('gallop'));
document.getElementById('btn-pause').addEventListener('click', () => setMode('pause'));

document.getElementById('btn-reset').addEventListener('click', () => {
    setMode('pause');
    vanEck = new VanEck();
    data = [{ n: 0, a: 0, na: 0 }];
    maxDomain = 50;
    initD3();
    updateUI(data[0]);
});

updateUI(data[0]);
