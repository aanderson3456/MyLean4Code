"""
Test vanEck_fiber_sum claim: for a valid Van Eck periodic cycle of length P,
does |S_X| * X = P hold for each distinct value X?

Constraints for a valid cycle v[0..P-1]:
1. v[k] in {1} ∪ [3, P]  (no 0s, no 2s)
2. f(k) = (k + 1 + P - v[k]) % P is a bijection
3. v[f(k)] = v[k]  (Most Recent Occurrence - BUT see note below)

Note: The MRO constraint in the Lean code is actually:
  v(f(k).val) = v(k.val + 1)
which for the Fin P version means v[f(k)] = v[(k+1) % P].
"""
from itertools import product

def test_cycle(P, vals_allowed):
    """Brute force all possible cycles and check constraints."""
    count = 0
    valid = []
    for v in product(vals_allowed, repeat=P):
        # Check f is a bijection
        f = [(k + 1 + P - v[k]) % P for k in range(P)]
        if len(set(f)) != P:
            continue
        
        # Check MRO: v[f(k)] = v[(k+1) % P]
        mro_ok = all(v[f[k]] == v[(k+1) % P] for k in range(P))
        if not mro_ok:
            continue
        
        valid.append(v)
        count += 1
        
        # Check fiber sum claim
        distinct_vals = set(v)
        print(f"  P={P}, v={v}")
        for X in distinct_vals:
            S_X = [k for k in range(P) if v[(k+1) % P] == X]
            fiber_product = len(S_X) * X
            print(f"    X={X}: |S_X|={len(S_X)}, |S_X|*X={fiber_product}, P={P}, ratio={fiber_product/P:.2f}")
        print(f"    f={f}")
        print()
    
    return count, valid

for P in range(4, 9):
    vals = [1] + list(range(3, P+1))
    print(f"=== P = {P}, allowed values = {vals} ===")
    n, valids = test_cycle(P, vals)
    if n == 0:
        print(f"  NO valid cycles found!")
    else:
        print(f"  Found {n} valid cycle(s)")
    print()
