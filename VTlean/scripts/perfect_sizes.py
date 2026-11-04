"""Enumerate perfect single-deletion-correcting codes (exact covers of {0,1}^(n-1)
by deletion spheres of length-n words) and compare achievable sizes with |VT_a(n)|.
Tests the hypothesis `PerfectSizeBridge` in VTlean/AlgebraicFractal.lean
(formerly the sorry'd theorem `perfect_code_card_eq_sum_T`)."""
import sys, time
from collections import Counter

def dS(x):
    return {x[:i] + x[i+1:] for i in range(len(x))}

def vt_sizes(n):
    cnt = Counter()
    for m in range(2 ** n):
        x = format(m, f"0{n}b")
        cnt[sum((i + 1) for i, b in enumerate(x) if b == "1") % (n + 1)] += 1
    return {a: cnt[a] for a in range(n + 1)}

def solve(n, time_limit):
    words = [format(m, f"0{n}b") for m in range(2 ** n)]
    X = {format(m, f"0{n-1}b") if n > 1 else "": set() for m in range(2 ** (n - 1))}
    Y = {w: dS(w) for w in words}
    for w, cols in Y.items():
        for c in cols:
            X[c].add(w)
    sizes = Counter()
    t0 = time.time()
    timed_out = [False]

    def select(r):
        cols = []
        for j in Y[r]:
            for i in X[j]:
                for k in Y[i]:
                    if k != j:
                        X[k].remove(i)
            cols.append(X.pop(j))
        return cols

    def deselect(r, cols):
        for j in reversed(list(Y[r])):
            X[j] = cols.pop()
            for i in X[j]:
                for k in Y[i]:
                    if k != j:
                        X[k].add(i)

    def search(depth):
        if timed_out[0]:
            return
        if not X:
            sizes[depth] += 1
            return
        if time.time() - t0 > time_limit:
            timed_out[0] = True
            return
        c = min(X, key=lambda c: len(X[c]))
        for r in list(X[c]):
            cols = select(r)
            search(depth + 1)
            deselect(r, cols)

    search(0)
    return sizes, timed_out[0], time.time() - t0

if __name__ == "__main__":
    nmax = int(sys.argv[1]) if len(sys.argv) > 1 else 7
    tl = float(sys.argv[2]) if len(sys.argv) > 2 else 120
    for n in range(2, nmax + 1):
        vt = vt_sizes(n)
        sizes, to, dt = solve(n, tl)
        vt_set = set(vt.values())
        bad = {s: k for s, k in sizes.items() if s not in vt_set}
        print(f"n={n}: VT sizes by a={vt}  |VT_0|={vt[0]}")
        print(f"   perfect-code sizes (size: #codes) = {dict(sorted(sizes.items()))}"
              f"  {'TIMED OUT (partial)' if to else 'complete'}  {dt:.1f}s")
        print(f"   sizes NOT equal to any |VT_a(n)|: {bad or 'none'}"
              f";  any size > |VT_0|: {[s for s in sizes if s > vt[0]] or 'none'}")
        sys.stdout.flush()
