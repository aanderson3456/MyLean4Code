document.addEventListener('DOMContentLoaded', () => {
    // DOM Elements
    const nSlider = document.getElementById('n-slider');
    const kSlider = document.getElementById('k-slider');
    const nVal = document.getElementById('n-val');
    const kVal = document.getElementById('k-val');
    const playBtn = document.getElementById('play-btn');
    const hoverInfo = document.getElementById('hover-info');
    const formulationDiv = document.getElementById('katex-formulation');
    
    const prevCodeBtn = document.getElementById('prev-code-btn');
    const nextCodeBtn = document.getElementById('next-code-btn');
    const codeLabelDiv = document.getElementById('code-label');

    const rowOrderSelect = document.getElementById('row-order');
    const colOrderSelect = document.getElementById('col-order');

    // State
    let n = parseInt(nSlider.value);
    let k = parseInt(kSlider.value);
    let isPlaying = false;
    let playInterval;

    let maximalCodes = [];
    let currentCodeIndex = -1;
    let activeTab = 'matrix';

    // Helpers
    const toBin = (num, length) => num.toString(2).padStart(length, '0');
    
    const dS = (x) => {
        let dels = new Set();
        for (let i = 0; i < x.length; i++) {
            dels.add(x.slice(0, i) + x.slice(i + 1));
        }
        return Array.from(dels);
    };

    const dS_k = (x, kVal) => {
        let dels = new Set();
        for (let i = 0; i < kVal; i++) {
            dels.add(x.slice(0, i) + x.slice(i + 1));
        }
        return Array.from(dels);
    };

    // Graph and Code algorithms (Bron-Kerbosch for maximal cliques)
    const computeMaximalCodes = (currentN) => {
        const rows = Math.pow(2, currentN);
        const words = [];
        for (let i = 0; i < rows; i++) words.push(toBin(i, currentN));

        const complement = Array.from({length: rows}, () => new Set());
        for (let i = 0; i < rows; i++) {
            const s1 = new Set(dS(words[i]));
            for (let j = i + 1; j < rows; j++) {
                const s2 = new Set(dS(words[j]));
                let intersect = false;
                for (let el of s1) {
                    if (s2.has(el)) { intersect = true; break; }
                }
                if (!intersect) {
                    complement[i].add(j);
                    complement[j].add(i);
                }
            }
        }

        let maximalCliques = [];
        const bronKerbosch = (R, P, X) => {
            if (P.size === 0 && X.size === 0) {
                maximalCliques.push(new Set(R));
                return;
            }
            const P_arr = Array.from(P);
            const pivot = P_arr.length > 0 ? P_arr[0] : Array.from(X)[0];
            const pivot_neighbors = complement[pivot] || new Set();
            
            for (let v of P_arr) {
                if (pivot_neighbors.has(v)) continue;
                
                let newR = new Set(R);
                newR.add(v);
                
                let newP = new Set();
                for (let node of P) {
                    if (complement[v].has(node)) newP.add(node);
                }
                
                let newX = new Set();
                for (let node of X) {
                    if (complement[v].has(node)) newX.add(node);
                }
                
                bronKerbosch(newR, newP, newX);
                
                P.delete(v);
                X.add(v);
            }
        };

        let allNodes = new Set();
        for (let i=0; i<rows; i++) allNodes.add(i);
        bronKerbosch(new Set(), allNodes, new Set());

        let codes = [];
        for (let clique of maximalCliques) {
            let arr = Array.from(clique);
            
            // check perfect
            let unionDels = new Set();
            for (let idx of arr) {
                for (let del of dS(words[idx])) {
                    unionDels.add(del);
                }
            }
            let isPerfect = unionDels.size === Math.pow(2, currentN - 1);

            // check VT
            let isVT = -1;
            for (let a = 0; a <= currentN; a++) {
                let matchesVT = true;
                for (let idx of arr) {
                    let w = words[idx];
                    let sum = 0;
                    for (let i=0; i<currentN; i++) {
                        if (w[i] === '1') sum += (i + 1);
                    }
                    if ((sum % (currentN + 1)) !== a) {
                        matchesVT = false;
                        break;
                    }
                }
                if (matchesVT) {
                    isVT = a;
                    break;
                }
            }

            codes.push({
                indices: arr,
                isPerfect: isPerfect,
                vt: isVT,
                size: arr.length
            });
        }

        // Sort: VT(0) first, then other VTs, then other perfects, then size descending
        codes.sort((a, b) => {
            if (a.vt === 0 && b.vt !== 0) return -1;
            if (b.vt === 0 && a.vt !== 0) return 1;
            if (a.vt !== -1 && b.vt === -1) return -1;
            if (b.vt !== -1 && a.vt === -1) return 1;
            if (a.vt !== -1 && b.vt !== -1) return a.vt - b.vt;
            if (a.isPerfect && !b.isPerfect) return -1;
            if (!a.isPerfect && b.isPerfect) return 1;
            return b.size - a.size;
        });

        maximalCodes = codes;
        currentCodeIndex = codes.length > 0 ? 0 : -1;
        updateCodeUI();
    };

    const updateCodeUI = () => {
        if (currentCodeIndex === -1) {
            codeLabelDiv.textContent = "None";
            codeLabelDiv.className = "code-label";
            return;
        }
        
        let c = maximalCodes[currentCodeIndex];
        let label = "";
        
        if (c.vt !== -1) label = `VT(${c.vt})`;
        else label = `Set-Maximal Code`;
        
        if (c.isPerfect) {
            label += ` PERFECT`;
            codeLabelDiv.className = "code-label perfect";
        } else {
            codeLabelDiv.className = "code-label";
        }
        
        label += ` (Size: ${c.size})`;
        codeLabelDiv.textContent = label;
    };

    // Sorting implementations for rows and columns
    const getSortedRows = (currentN, orderType) => {
        let list = [];
        const size = Math.pow(2, currentN);
        for (let i = 0; i < size; i++) {
            let x = toBin(i, currentN);
            let wt = 0;
            let syn = 0;
            for (let j = 0; j < currentN; j++) {
                if (x[j] === '1') {
                    wt++;
                    syn += (j + 1);
                }
            }
            syn = syn % (currentN + 1);
            
            let runCount = 0;
            if (currentN > 0) {
                runCount = 1;
                for (let j = 1; j < currentN; j++) {
                    if (x[j] !== x[j-1]) runCount++;
                }
            }
            list.push({ idx: i, x, wt, syn, runCount });
        }
        
        if (orderType === 'weight') {
            list.sort((a, b) => (a.wt !== b.wt) ? a.wt - b.wt : a.idx - b.idx);
        } else if (orderType === 'syndrome') {
            list.sort((a, b) => (a.syn !== b.syn) ? a.syn - b.syn : a.idx - b.idx);
        } else if (orderType === 'runs') {
            list.sort((a, b) => (a.runCount !== b.runCount) ? a.runCount - b.runCount : a.idx - b.idx);
        }
        return list;
    };

    const getSortedCols = (currentN, orderType) => {
        let list = [];
        const size = Math.pow(2, currentN - 1);
        for (let i = 0; i < size; i++) {
            let y = toBin(i, currentN - 1);
            let wt = 0;
            let syn = 0;
            for (let j = 0; j < currentN - 1; j++) {
                if (y[j] === '1') {
                    wt++;
                    syn += (j + 1);
                }
            }
            syn = syn % currentN;
            list.push({ idx: i, y, wt, syn });
        }
        
        if (orderType === 'weight') {
            list.sort((a, b) => (a.wt !== b.wt) ? a.wt - b.wt : a.idx - b.idx);
        } else if (orderType === 'syndrome') {
            list.sort((a, b) => (a.syn !== b.syn) ? a.syn - b.syn : a.idx - b.idx);
        }
        return list;
    };

    // Matrix Generation
    const generateData = (currentN, currentK) => {
        const rows = Math.pow(2, currentN);
        const cols = Math.pow(2, currentN - 1);
        let data = [];
        
        const activeCode = currentCodeIndex !== -1 ? new Set(maximalCodes[currentCodeIndex].indices) : null;

        for (let i = 0; i < rows; i++) {
            const x = toBin(i, currentN);
            const currentDels = new Set(dS_k(x, currentK));
            const prevDels = new Set(dS_k(x, currentK - 1));
            const inCode = activeCode ? activeCode.has(i) : true;
            
            for (let j = 0; j < cols; j++) {
                const y = toBin(j, currentN - 1);
                
                let state = 0; // empty
                if (currentDels.has(y)) {
                    if (prevDels.has(y)) {
                        state = 1; // already filled
                    } else {
                        state = 2; // newly filled
                    }
                }
                
                data.push({
                    row: i,
                    col: j,
                    x: x,
                    y: y,
                    state: state,
                    inCode: inCode
                });
            }
        }
        return { data, rows, cols, activeCode };
    };

    // Render Formulation Text
    const updateFormulationText = (tab) => {
        let latex = '';
        if (tab === 'matrix') {
            if (k === 0) {
                latex = `A_{${n},0}(x,y) = 0`;
            } else {
                latex = `A_{${n},${k}}(x,y) = A_{${n},${k-1}}(x,y) + B_{${n},${k}}(x,y) \\quad \\text{(window size } k\\text{)}`;
            }
        } else if (tab === 'transitions') {
            latex = `\\text{Checksum Shift: } \\text{Syn}(x) - \\text{Syn}(y) \\equiv i \\cdot x_i + \\sum_{j=i+1}^n x_j \\pmod{n+1}`;
        } else if (tab === 'invariants') {
            latex = `\\text{Run-Count Deletion Card: } |dS(x) \\cap B^{n-1}_{\\text{wt}(x)}| = r_0(x) \\quad \\text{and} \\quad |dS(x) \\cap B^{n-1}_{\\text{wt}(x)-1}| = r_1(x)`;
        }
        
        katex.render(latex, formulationDiv, {
            displayMode: true,
            throwOnError: false
        });
    };

    // Tab 1: Draw Matrix
    const margin = { top: 40, right: 40, bottom: 40, left: 60 };
    const colors = ['#38bdf8', '#c084fc', '#f472b6', '#34d399', '#fbbf24', '#f87171'];

    const drawMatrix = () => {
        const container = document.getElementById('matrix-container');
        if (!container) return;
        
        // Dynamically recreate SVG on each draw to avoid 0-dimension race conditions on page load
        d3.select('#matrix-container svg').remove();
        
        let width = container.clientWidth || 600;
        let height = container.clientHeight || 500;
        if (width < 100) width = 600;
        if (height < 100) height = 500;
        
        const svg = d3.select('#matrix-container')
            .append('svg')
            .attr('width', '100%')
            .attr('height', '100%')
            .attr('viewBox', `0 0 ${width} ${height}`)
            .attr('preserveAspectRatio', 'xMidYMid meet');
            
        const g = svg.append('g');
        const xAxisGroup = svg.append('g');
        const yAxisGroup = svg.append('g');
        
        const rowOrderVal = rowOrderSelect.value;
        const colOrderVal = colOrderSelect.value;
        
        const sortedRows = getSortedRows(n, rowOrderVal);
        const sortedCols = getSortedCols(n, colOrderVal);
        
        const rowPosMap = {};
        sortedRows.forEach((item, pos) => { rowPosMap[item.idx] = pos; });
        const colPosMap = {};
        sortedCols.forEach((item, pos) => { colPosMap[item.idx] = pos; });

        const { data, rows, cols, activeCode } = generateData(n, k);
        
        const innerWidth = width - margin.left - margin.right;
        const innerHeight = height - margin.top - margin.bottom;
        
        const cellWidth = innerWidth / cols;
        const cellHeight = innerHeight / rows;
        const cellSize = Math.min(cellWidth, cellHeight);
        
        const gridWidth = cellSize * cols;
        const gridHeight = cellSize * rows;
        const offsetX = (width - gridWidth) / 2;
        const offsetY = (height - gridHeight) / 2;

        g.attr('transform', `translate(${offsetX},${offsetY})`);
        
        let codeColorIdx = currentCodeIndex === -1 ? 0 : currentCodeIndex % colors.length;
        let activeColor = colors[codeColorIdx];

        const cells = g.selectAll('.matrix-cell')
            .data(data, d => `${d.row}-${d.col}`);

        cells.enter()
            .append('rect')
            .attr('class', 'matrix-cell')
            .merge(cells)
            .attr('x', d => colPosMap[d.col] * cellSize)
            .attr('y', d => rowPosMap[d.row] * cellSize)
            .attr('width', cellSize)
            .attr('height', cellSize)
            .style('opacity', d => d.inCode ? 1 : 0.15)
            .attr('fill', d => {
                if (d.state === 0) return 'var(--cell-empty)';
                if (activeCode) {
                    if (d.state === 1) return activeColor;
                    if (d.state === 2) return '#ffffff';
                }
                return d.state === 1 ? 'var(--cell-filled)' : 'var(--cell-new)';
            })
            .on('mouseover', function(event, d) {
                d3.select(this).style('stroke', '#fff').style('stroke-width', '2px').style('opacity', 1);
                hoverInfo.classList.remove('empty');
                
                let deletedIndexStr = "";
                let i_idx = -1;
                for(let i=0; i<n; i++) {
                    if (d.x.slice(0, i) + d.x.slice(i+1) === d.y) {
                        i_idx = i;
                        break;
                    }
                }
                
                if (i_idx !== -1 && i_idx < k) {
                    const wtX = d.x.split('1').length - 1;
                    const wtY = d.y.split('1').length - 1;
                    const bit = d.x[i_idx];
                    deletedIndexStr = `<br/><span style="color:var(--accent-secondary)">Deleted index ${i_idx+1} ('${bit}')</span><br/><span style="color:var(--text-muted)">wt shift: ${wtX} &rarr; ${wtY}</span>`;
                }
                
                // VT syndrome info
                let wtX = 0, synX = 0;
                for(let j=0; j<n; j++) if(d.x[j] === '1') { wtX++; synX += (j+1); }
                synX = synX % (n+1);

                let wtY = 0, synY = 0;
                for(let j=0; j<n-1; j++) if(d.y[j] === '1') { wtY++; synY += (j+1); }
                synY = synY % n;

                hoverInfo.innerHTML = `
                    <div style="margin-bottom:8px"><strong>x ∈ B<sup>${n}</sup>:</strong> <span style="color:var(--accent-primary)">${d.x}</span> (wt ${wtX}, syn ${synX})</div>
                    <div style="margin-bottom:8px"><strong>y ∈ B<sup>${n-1}</sup>:</strong> <span style="color:var(--accent-primary)">${d.y}</span> (wt ${wtY}, syn ${synY})</div>
                    <div><strong>A<sub>${n},${k}</sub>(x,y):</strong> ${d.state > 0 ? '1' : '0'} ${deletedIndexStr}</div>
                `;
            })
            .on('mouseout', function(event, d) {
                d3.select(this)
                    .style('stroke', null)
                    .style('stroke-width', null)
                    .style('opacity', d.inCode ? 1 : 0.15);
                hoverInfo.classList.add('empty');
                hoverInfo.innerHTML = 'Hover over a highlighted cell to see details.';
            });

        cells.exit().remove();

        // Draw Dividers
        const rowDividers = [];
        for (let i = 0; i < sortedRows.length - 1; i++) {
            let cur = sortedRows[i];
            let next = sortedRows[i+1];
            if (rowOrderVal === 'weight' && cur.wt !== next.wt) rowDividers.push(i + 1);
            else if (rowOrderVal === 'syndrome' && cur.syn !== next.syn) rowDividers.push(i + 1);
            else if (rowOrderVal === 'runs' && cur.runCount !== next.runCount) rowDividers.push(i + 1);
        }

        const colDividers = [];
        for (let i = 0; i < sortedCols.length - 1; i++) {
            let cur = sortedCols[i];
            let next = sortedCols[i+1];
            if (colOrderVal === 'weight' && cur.wt !== next.wt) colDividers.push(i + 1);
            else if (colOrderVal === 'syndrome' && cur.syn !== next.syn) colDividers.push(i + 1);
        }

        const rDivs = g.selectAll('.row-divider').data(rowDividers);
        rDivs.enter().append('line')
            .attr('class', 'matrix-divider row-divider')
            .merge(rDivs)
            .transition().duration(400)
            .attr('x1', 0)
            .attr('x2', gridWidth)
            .attr('y1', d => d * cellSize)
            .attr('y2', d => d * cellSize);
        rDivs.exit().remove();

        const cDivs = g.selectAll('.col-divider').data(colDividers);
        cDivs.enter().append('line')
            .attr('class', 'matrix-divider col-divider')
            .merge(cDivs)
            .transition().duration(400)
            .attr('x1', d => d * cellSize)
            .attr('x2', d => d * cellSize)
            .attr('y1', 0)
            .attr('y2', gridHeight);
        cDivs.exit().remove();
        
        // Axis ticks
        const xAxisLabels = [];
        for(let i=0; i<cols; i++) {
            if (cols <= 32 || i % Math.ceil(cols/16) === 0) xAxisLabels.push({i, label:sortedCols[i].y});
        }
        
        const yAxisLabels = [];
        for(let i=0; i<rows; i++) {
            if (rows <= 32 || i % Math.ceil(rows/16) === 0) {
                yAxisLabels.push({
                    i, 
                    label:sortedRows[i].x, 
                    inCode: activeCode ? activeCode.has(sortedRows[i].idx) : true,
                    syn: sortedRows[i].syn
                });
            }
        }

        xAxisGroup.attr('transform', `translate(${offsetX},${offsetY - 10})`);
        const xTicks = xAxisGroup.selectAll('.x-tick').data(xAxisLabels, d => d.label);
        xTicks.enter().append('text')
            .attr('class', 'axis-label x-tick')
            .attr('text-anchor', 'end')
            .merge(xTicks)
            .transition().duration(400)
            .attr('transform', d => `translate(${d.i * cellSize + cellSize/2},0) rotate(-45)`)
            .text(d => d.label);
        xTicks.exit().remove();

        yAxisGroup.attr('transform', `translate(${offsetX - 10},${offsetY})`);
        const yTicks = yAxisGroup.selectAll('.y-tick').data(yAxisLabels, d => d.label);
        yTicks.enter().append('text')
            .attr('class', d => d.inCode ? 'axis-label y-tick highlight' : 'axis-label y-tick')
            .merge(yTicks)
            .attr('class', d => d.inCode ? 'axis-label y-tick highlight' : 'axis-label y-tick')
            .style('fill', d => d.inCode && activeCode ? activeColor : null)
            .transition().duration(400)
            .attr('y', d => d.i * cellSize + cellSize/2)
            .text(d => d.label);
        yTicks.exit().remove();
    };

    // Tab 2: Draw transitions
    const drawTransitions = () => {
        const container = document.getElementById('transitions-container');
        if (!container) return;
        
        container.innerHTML = '';
        const width = container.clientWidth || 800;
        const height = container.clientHeight || 500;
        
        const svgTrans = d3.select('#transitions-container')
            .append('svg')
            .attr('width', '100%')
            .attr('height', '100%')
            .attr('viewBox', `0 0 ${width} ${height}`);
            
        const leftWords = getSortedRows(n, 'syndrome');
        const rightWords = getSortedCols(n, 'syndrome');
        
        const leftBySyn = d3.group(leftWords, d => d.syn);
        const rightBySyn = d3.group(rightWords, d => d.syn);
        
        const leftX = width * 0.28;
        const rightX = width * 0.72;
        
        let leftCoords = {};
        let rightCoords = {};
        
        const activeHeight = height - 60;
        
        // Left scaling
        const totalLeftNodes = leftWords.length;
        const paddingNodeLeft = Math.min(18, activeHeight / (totalLeftNodes + (n + 1) * 1.5));
        const paddingGroupLeft = paddingNodeLeft * 1.5;
        
        let currentY = 30;
        const leftGroups = [];
        for (let a = 0; a <= n; a++) {
            const wordsInGroup = leftBySyn.get(a) || [];
            const startY = currentY;
            wordsInGroup.forEach((w) => {
                leftCoords[w.x] = { x: leftX, y: currentY, data: w };
                currentY += paddingNodeLeft;
            });
            if (wordsInGroup.length > 0) {
                leftGroups.push({ syn: a, startY: startY - 4, endY: currentY - paddingNodeLeft + 4 });
                currentY += paddingGroupLeft;
            }
        }
        
        // Right scaling
        const totalRightNodes = rightWords.length;
        const paddingNodeRight = Math.min(18, activeHeight / (totalRightNodes + n * 1.5));
        const paddingGroupRight = paddingNodeRight * 1.5;
        
        currentY = 30;
        const rightGroups = [];
        for (let a = 0; a < n; a++) {
            const wordsInGroup = rightBySyn.get(a) || [];
            const startY = currentY;
            wordsInGroup.forEach((w) => {
                rightCoords[w.y] = { x: rightX, y: currentY, data: w };
                currentY += paddingNodeRight;
            });
            if (wordsInGroup.length > 0) {
                rightGroups.push({ syn: a, startY: startY - 4, endY: currentY - paddingNodeRight + 4 });
                currentY += paddingGroupRight;
            }
        }

        // Draw left group frames
        svgTrans.selectAll('.left-group-rect')
            .data(leftGroups)
            .enter()
            .append('rect')
            .attr('class', 'left-group-rect')
            .attr('x', leftX - 45)
            .attr('y', d => d.startY)
            .attr('width', 90)
            .attr('height', d => d.endY - d.startY)
            .attr('rx', 6)
            .attr('fill', 'rgba(255,255,255,0.015)')
            .attr('stroke', 'rgba(255,255,255,0.08)')
            .attr('stroke-width', 1);

        svgTrans.selectAll('.left-group-label')
            .data(leftGroups)
            .enter()
            .append('text')
            .attr('class', 'flow-group-label')
            .attr('x', leftX - 55)
            .attr('y', d => (d.startY + d.endY)/2)
            .attr('text-anchor', 'end')
            .attr('alignment-baseline', 'middle')
            .text(d => `Syn ${d.syn}`);

        // Draw right group frames
        svgTrans.selectAll('.right-group-rect')
            .data(rightGroups)
            .enter()
            .append('rect')
            .attr('class', 'right-group-rect')
            .attr('x', rightX - 45)
            .attr('y', d => d.startY)
            .attr('width', 90)
            .attr('height', d => d.endY - d.startY)
            .attr('rx', 6)
            .attr('fill', 'rgba(255,255,255,0.015)')
            .attr('stroke', 'rgba(255,255,255,0.08)')
            .attr('stroke-width', 1);

        svgTrans.selectAll('.right-group-label')
            .data(rightGroups)
            .enter()
            .append('text')
            .attr('class', 'flow-group-label')
            .attr('x', rightX + 55)
            .attr('y', d => (d.startY + d.endY)/2)
            .attr('text-anchor', 'start')
            .attr('alignment-baseline', 'middle')
            .text(d => `Syn ${d.syn}`);

        // Links
        const links = [];
        leftWords.forEach(w => {
            const x = w.x;
            for (let i = 0; i < n; i++) {
                const y = x.slice(0, i) + x.slice(i + 1);
                if (rightCoords[y]) {
                    links.push({
                        source: x,
                        target: y,
                        delIndex: i,
                        bit: x[i]
                    });
                }
            }
        });

        const pathGenerator = (d) => {
            const src = leftCoords[d.source];
            const tgt = rightCoords[d.target];
            return d3.linkHorizontal()({
                source: [src.x + 10, src.y],
                target: [tgt.x - 10, tgt.y]
            });
        };

        const linkPaths = svgTrans.selectAll('.flow-link')
            .data(links)
            .enter()
            .append('path')
            .attr('class', 'flow-link')
            .attr('d', pathGenerator)
            .attr('stroke', d => d.bit === '0' ? 'var(--accent-primary)' : 'var(--accent-secondary)')
            .attr('stroke-width', 1.2);

        // Nodes left
        const leftNodeSel = svgTrans.selectAll('.left-node')
            .data(leftWords)
            .enter()
            .append('g')
            .attr('class', 'left-node')
            .attr('transform', d => `translate(${leftCoords[d.x].x},${leftCoords[d.x].y})`);

        leftNodeSel.append('circle')
            .attr('class', 'node-circle')
            .attr('r', 4)
            .attr('fill', 'var(--text-main)');

        leftNodeSel.append('text')
            .attr('class', 'flow-text')
            .attr('x', -8)
            .attr('y', 0)
            .attr('text-anchor', 'end')
            .attr('alignment-baseline', 'middle')
            .text(d => d.x);

        // Nodes right
        const rightNodeSel = svgTrans.selectAll('.right-node')
            .data(rightWords)
            .enter()
            .append('g')
            .attr('class', 'right-node')
            .attr('transform', d => `translate(${rightCoords[d.y].x},${rightCoords[d.y].y})`);

        rightNodeSel.append('circle')
            .attr('class', 'node-circle')
            .attr('r', 4)
            .attr('fill', 'var(--text-main)');

        rightNodeSel.append('text')
            .attr('class', 'flow-text')
            .attr('x', 8)
            .attr('y', 0)
            .attr('text-anchor', 'start')
            .attr('alignment-baseline', 'middle')
            .text(d => d.y);

        // Hover interactions
        leftNodeSel.on('mouseover', function(event, d) {
            d3.select(this).select('circle').attr('r', 6).attr('fill', 'var(--accent-primary)');
            d3.select(this).select('text').classed('highlighted', true);
            
            const targetSet = new Set();
            linkPaths.classed('highlighted', l => {
                if (l.source === d.x) {
                    targetSet.add(l.target);
                    return true;
                }
                return false;
            });
            
            rightNodeSel.filter(r => targetSet.has(r.y))
                .select('circle')
                .attr('r', 5)
                .attr('fill', 'var(--accent-secondary)');
            rightNodeSel.filter(r => targetSet.has(r.y))
                .select('text')
                .classed('highlighted', true);
                
            hoverInfo.classList.remove('empty');
            let detailsHtml = `
                <div style="margin-bottom:12px"><strong>Selected x:</strong> <span style="color:var(--accent-primary); font-size:1.1rem">${d.x}</span></div>
                <div style="margin-bottom:8px"><strong>Weight wt(x):</strong> ${d.wt}</div>
                <div style="margin-bottom:12px"><strong>Syn(x) mod ${n+1}:</strong> ${d.syn}</div>
                <div style="border-top:1px solid var(--border-color); padding-top:8px"><strong>Deletions & Shifts:</strong></div>
            `;
            
            const dels = [];
            for (let i = 0; i < n; i++) {
                const y = d.x.slice(0, i) + d.x.slice(i + 1);
                const bit = d.x[i];
                
                let synY = 0;
                for(let j=0; j<y.length; j++) if (y[j] === '1') synY += (j + 1);
                synY = synY % n;
                
                const wtY = bit === '1' ? d.wt - 1 : d.wt;
                
                // Formula shift: i * x_i + Sum_{j=i+1}^n x_j
                let sumTrailing = 0;
                for(let j=i+1; j<n; j++) if(d.x[j] === '1') sumTrailing++;
                let rawShift = (i + 1) * (bit === '1' ? 1 : 0) + sumTrailing;
                let mathShift = rawShift % (n + 1);
                
                dels.push({ idx: i + 1, bit, y, wtY, synY, mathShift });
            }
            
            dels.forEach(del => {
                detailsHtml += `
                    <div style="margin-top:8px; font-size:0.85rem; line-height:1.4">
                        🗑️ Idx ${del.idx} ('${del.bit}') &rarr; <span style="color:var(--accent-secondary)">${del.y}</span>
                        <br>&nbsp;&nbsp;wt: ${d.wt} &rarr; ${del.wtY} | Syn: ${d.syn} &rarr; ${del.synY}
                        <br>&nbsp;&nbsp;<span style="color:var(--text-muted)">Shift &Delta; &equiv; ${del.mathShift} mod ${n+1}</span>
                    </div>
                `;
            });
            
            hoverInfo.innerHTML = detailsHtml;
        });

        leftNodeSel.on('mouseout', function() {
            d3.select(this).select('circle').attr('r', 4).attr('fill', 'var(--text-main)');
            d3.select(this).select('text').classed('highlighted', false);
            linkPaths.classed('highlighted', false);
            rightNodeSel.select('circle').attr('r', 4).attr('fill', 'var(--text-main)');
            rightNodeSel.select('text').classed('highlighted', false);
            
            hoverInfo.classList.add('empty');
            hoverInfo.innerHTML = 'Hover over a node to see details.';
        });

        rightNodeSel.on('mouseover', function(event, d) {
            d3.select(this).select('circle').attr('r', 6).attr('fill', 'var(--accent-secondary)');
            d3.select(this).select('text').classed('highlighted', true);
            
            const sourceSet = new Set();
            linkPaths.classed('highlighted', l => {
                if (l.target === d.y) {
                    sourceSet.add(l.source);
                    return true;
                }
                return false;
            });
            
            leftNodeSel.filter(l => sourceSet.has(l.x))
                .select('circle')
                .attr('r', 5)
                .attr('fill', 'var(--accent-primary)');
            leftNodeSel.filter(l => sourceSet.has(l.x))
                .select('text')
                .classed('highlighted', true);
                
            hoverInfo.classList.remove('empty');
            let detailsHtml = `
                <div style="margin-bottom:12px"><strong>Selected y:</strong> <span style="color:var(--accent-secondary); font-size:1.1rem">${d.y}</span></div>
                <div style="margin-bottom:8px"><strong>Weight wt(y):</strong> ${d.wt}</div>
                <div style="margin-bottom:12px"><strong>Syn(y) mod ${n}:</strong> ${d.syn}</div>
                <div style="border-top:1px solid var(--border-color); padding-top:8px"><strong>Sources (wt &rarr; y):</strong></div>
            `;
            
            leftWords.filter(w => sourceSet.has(w.x)).forEach(src => {
                let deletedIdx = -1;
                for(let i=0; i<n; i++) {
                    if (src.x.slice(0, i) + src.x.slice(i+1) === d.y) { deletedIdx = i+1; break; }
                }
                detailsHtml += `
                    <div style="margin-top:6px; font-size:0.85rem">
                        📥 From <span style="color:var(--accent-primary)">${src.x}</span> (Syn ${src.syn})
                        <br>&nbsp;&nbsp;via deleting index ${deletedIdx}
                    </div>
                `;
            });
            
            hoverInfo.innerHTML = detailsHtml;
        });

        rightNodeSel.on('mouseout', function() {
            d3.select(this).select('circle').attr('r', 4).attr('fill', 'var(--text-main)');
            d3.select(this).select('text').classed('highlighted', false);
            linkPaths.classed('highlighted', false);
            leftNodeSel.select('circle').attr('r', 4).attr('fill', 'var(--text-main)');
            leftNodeSel.select('text').classed('highlighted', false);
            
            hoverInfo.classList.add('empty');
            hoverInfo.innerHTML = 'Hover over a node to see details.';
        });
    };

    // Tab 3: Invariant Explorer
    const drawInvariants = () => {
        const container = document.getElementById('invariants-container');
        if (!container) return;
        
        container.innerHTML = '';
        
        let code = maximalCodes[currentCodeIndex] || { vt: 0, indices: [] };
        let a = code.vt !== -1 ? code.vt : 0;
        
        const activeCode = new Set(code.indices);
        const C = Array(n + 1).fill(0);
        
        for (let i = 0; i < Math.pow(2, n); i++) {
            let x = toBin(i, n);
            let wt = 0;
            for (let cVal of x) if (cVal === '1') wt++;
            if (activeCode.has(i)) C[wt]++;
        }
        
        const S = Array(n + 1).fill(0);
        for (let i = 0; i < Math.pow(2, n); i++) {
            let x = toBin(i, n);
            let wt = 0, syn = 0;
            for (let j = 0; j < n; j++) if (x[j] === '1') { wt++; syn += (j + 1); }
            syn = syn % (n + 1);
            if (syn === a) S[wt]++;
        }

        let html = `
            <div class="explorer-grid">
                <div class="table-section">
                    <h4>
                        <span>Weight-Slice Recurrence Check</span>
                        <span style="font-size:0.85rem; font-weight:normal; color:var(--accent-primary)">VT(${a})</span>
                    </h4>
                    <p style="font-size:0.85rem; color:var(--text-muted); margin-bottom:12px; line-height:1.4">
                        Equation: $C(k) + C(k-1) = S(n, k, a)$ where $C(k) = |VT(a) \\cap B^n_k|$.
                        Observe that when $a \\ge 2$, boundary wraps in modular arithmetic create mismatches.
                    </p>
                    <table class="invariants-table">
                        <thead>
                            <tr>
                                <th>Weight $k$</th>
                                <th>Slice $C(k)$</th>
                                <th>LHS: $C(k) + C(k-1)$</th>
                                <th>RHS: $S(n, k, ${a})$</th>
                                <th>Status</th>
                            </tr>
                        </thead>
                        <tbody>
        `;
        
        for (let kVal = 0; kVal <= n; kVal++) {
            let lhs = C[kVal] + (kVal > 0 ? C[kVal-1] : 0);
            let rhs = S[kVal];
            let isMatch = lhs === rhs;
            let rowClass = isMatch ? "" : "mismatch";
            let statusBadge = isMatch ? '<span class="match-badge">Match</span>' : '<span class="mismatch-badge">Mismatch</span>';
            
            html += `
                <tr class="${rowClass}">
                    <td>${kVal}</td>
                    <td>${C[kVal]}</td>
                    <td>${lhs}</td>
                    <td>${rhs}</td>
                    <td>${statusBadge}</td>
                </tr>
            `;
        }
        
        html += `
                        </tbody>
                    </table>
                </div>
                
                <div class="table-section">
                    <h4>Run-Counts Cardinality Verifier</h4>
                    <p style="font-size:0.85rem; color:var(--text-muted); margin-bottom:12px; line-height:1.4">
                        Select $x \\in B^n$ to verify the run-count cardinality bijections proven in <code>RunCounts.lean</code>:
                        <br>&bull; $|dS(x) \\cap B^{n-1}_{\\text{wt}(x)}| = r_0(x)$ (runs of 0s)
                        <br>&bull; $|dS(x) \\cap B^{n-1}_{\\text{wt}(x)-1}| = r_1(x)$ (runs of 1s)
                    </p>
                    
                    <div class="control-group" style="margin-bottom:16px">
                        <label for="verifier-word-select" style="font-size:0.85rem">Select Word $x$:</label>
                        <select id="verifier-word-select" class="select-control">
        `;
        
        for (let i = 0; i < Math.pow(2, n); i++) {
            let x = toBin(i, n);
            html += `<option value="${x}">${x} (wt: ${x.split('1').length - 1})</option>`;
        }
        
        html += `
                        </select>
                    </div>
                    
                    <div id="runcounts-verifier-results"></div>
                </div>
            </div>
        `;
        
        container.innerHTML = html;
        
        const select = document.getElementById('verifier-word-select');
        select.addEventListener('change', (e) => {
            updateRunCountsVerifier(e.target.value);
        });
        
        updateRunCountsVerifier(toBin(0, n));
        
        // Render math in the generated content
        renderMathInElement(container, {
            delimiters: [
                {left: '$$', right: '$$', display: true},
                {left: '$', right: '$', display: false}
            ],
            throwOnError: false
        });
    };

    const updateRunCountsVerifier = (x) => {
        const resultsDiv = document.getElementById('runcounts-verifier-results');
        if (!resultsDiv) return;
        
        let wtX = 0;
        for (let cVal of x) if (cVal === '1') wtX++;
        
        let r0 = 0;
        let r1 = 0;
        let currentRun = null;
        for (let i = 0; i < x.length; i++) {
            if (x[i] !== currentRun) {
                currentRun = x[i];
                if (currentRun === '0') r0++;
                else r1++;
            }
        }
        
        const dels = dS(x);
        const delsSameWt = [];
        const delsDecWt = [];
        
        dels.forEach(y => {
            let wtY = 0;
            for (let cVal of y) if (cVal === '1') wtY++;
            if (wtY === wtX) {
                delsSameWt.push(y);
            } else if (wtY === wtX - 1) {
                delsDecWt.push(y);
            }
        });
        
        resultsDiv.innerHTML = `
            <div style="background:rgba(0,0,0,0.25); padding:16px; border-radius:8px; border:1px solid var(--border-color)">
                <div style="display:flex; justify-content:space-between; margin-bottom:12px; border-bottom:1px solid var(--border-color); padding-bottom:8px">
                    <span><strong>Runs of 0s (r₀):</strong> <span style="color:var(--accent-primary); font-weight:bold; font-size:1.05rem">${r0}</span></span>
                    <span><strong>Runs of 1s (r₁):</strong> <span style="color:var(--accent-secondary); font-weight:bold; font-size:1.05rem">${r1}</span></span>
                </div>
                
                <div style="margin-top:12px">
                    <div style="font-weight:600; font-size:0.85rem; color:var(--accent-primary); margin-bottom:4px">
                        Same-Weight Deletions (wt = ${wtX}): count = ${delsSameWt.length}
                    </div>
                    <div style="font-family:monospace; font-size:0.85rem; padding:8px; background:rgba(0,0,0,0.4); border-radius:4px; max-height: 50px; overflow-y: auto">
                        ${delsSameWt.length > 0 ? delsSameWt.join(', ') : 'None'}
                    </div>
                    <div style="font-size:0.8rem; color:var(--text-muted); margin-top:4px">
                        Theorem: ${delsSameWt.length === r0 ? '<span class="match-badge">Verified (= r₀)</span>' : '<span class="mismatch-badge">Mismatch</span>'}
                    </div>
                </div>

                <div style="margin-top:16px">
                    <div style="font-weight:600; font-size:0.85rem; color:var(--accent-secondary); margin-bottom:4px">
                        Decreasing-Weight Deletions (wt = ${wtX - 1}): count = ${delsDecWt.length}
                    </div>
                    <div style="font-family:monospace; font-size:0.85rem; padding:8px; background:rgba(0,0,0,0.4); border-radius:4px; max-height: 50px; overflow-y: auto">
                        ${delsDecWt.length > 0 ? delsDecWt.join(', ') : 'None'}
                    </div>
                    <div style="font-size:0.8rem; color:var(--text-muted); margin-top:4px">
                        Theorem: ${delsDecWt.length === r1 ? '<span class="match-badge">Verified (= r₁)</span>' : '<span class="mismatch-badge">Mismatch</span>'}
                    </div>
                </div>
            </div>
        `;
    };

    const renderActiveTab = () => {
        if (activeTab === 'matrix') {
            drawMatrix();
        } else if (activeTab === 'transitions') {
            drawTransitions();
        } else if (activeTab === 'invariants') {
            drawInvariants();
        }
        updateFormulationText(activeTab);
    };

    // Event Listeners
    nSlider.addEventListener('input', (e) => {
        n = parseInt(e.target.value);
        nVal.textContent = n;
        kSlider.max = n;
        if (k > n) {
            k = n;
            kSlider.value = n;
            kVal.textContent = n;
        }
        computeMaximalCodes(n);
        renderActiveTab();
    });

    kSlider.addEventListener('input', (e) => {
        k = parseInt(e.target.value);
        kVal.textContent = k;
        renderActiveTab();
    });

    rowOrderSelect.addEventListener('change', () => {
        if (activeTab === 'matrix') drawMatrix();
    });

    colOrderSelect.addEventListener('change', () => {
        if (activeTab === 'matrix') drawMatrix();
    });

    playBtn.addEventListener('click', () => {
        if (isPlaying) {
            clearInterval(playInterval);
            playBtn.textContent = '▶ Auto Play';
            playBtn.classList.remove('playing');
        } else {
            playBtn.textContent = '⏸ Pause';
            playBtn.classList.add('playing');
            
            playInterval = setInterval(() => {
                k++;
                if (k > n) k = 0;
                kSlider.value = k;
                kVal.textContent = k;
                renderActiveTab();
            }, 1000);
        }
        isPlaying = !isPlaying;
    });

    prevCodeBtn.addEventListener('click', () => {
        if (maximalCodes.length === 0) return;
        currentCodeIndex--;
        if (currentCodeIndex < 0) currentCodeIndex = maximalCodes.length - 1;
        updateCodeUI();
        renderActiveTab();
    });

    nextCodeBtn.addEventListener('click', () => {
        if (maximalCodes.length === 0) return;
        currentCodeIndex++;
        if (currentCodeIndex >= maximalCodes.length) currentCodeIndex = 0;
        updateCodeUI();
        renderActiveTab();
    });

    window.addEventListener('resize', () => {
        renderActiveTab();
    });

    // Tabs navigation
    const tabs = document.querySelectorAll('.tab-btn');
    const contents = document.querySelectorAll('.tab-content');

    tabs.forEach(tab => {
        tab.addEventListener('click', () => {
            tabs.forEach(t => t.classList.remove('active'));
            contents.forEach(c => c.classList.remove('active'));
            
            tab.classList.add('active');
            activeTab = tab.dataset.tab;
            
            const targetContent = document.getElementById(`tab-${activeTab}`);
            if (targetContent) targetContent.classList.add('active');
            
            renderActiveTab();
        });
    });

    // Init
    computeMaximalCodes(n);
    renderActiveTab();
});
