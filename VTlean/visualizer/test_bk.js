const toBin = (num, length) => num.toString(2).padStart(length, '0');

const dS = (x) => {
    let dels = new Set();
    for (let i = 0; i < x.length; i++) {
        dels.add(x.slice(0, i) + x.slice(i + 1));
    }
    return Array.from(dels);
};

const n = 4;
const rows = Math.pow(2, n);
const words = [];
for (let i = 0; i < rows; i++) words.push(toBin(i, n));

const complement = Array.from({length: rows}, () => new Set());
for (let i = 0; i < rows; i++) {
    const s1 = new Set(dS(words[i]));
    for (let j = i + 1; j < rows; j++) {
        const s2 = new Set(dS(words[j]));
        let intersect = false;
        for (let el of s1) {
            if (s2.has(el)) { intersect = true; break; }
        }
        if (!intersect) { // Complement graph! (edges = non-conflicting)
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
}

let allNodes = new Set();
for (let i=0; i<rows; i++) allNodes.add(i);
bronKerbosch(new Set(), allNodes, new Set());

console.log("Found", maximalCliques.length, "maximal codes for n=", n);
console.log(maximalCliques.map(s => Array.from(s).length));
