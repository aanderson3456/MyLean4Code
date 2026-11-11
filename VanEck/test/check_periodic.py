# Let's search for periodic sequences of period P with no zeros
# that satisfy the Van Eck condition:
# a(n) = n - 1 - prev(a(n-1)) if seen, else 0.
# Since there are no zeros, it must be that every term is a distance to a previous occurrence.
# So a(n) = n - 1 - prev(a(n-1)).
# Let's write a generator that finds all such periodic sequences.

def solve_periodic(P):
    # We want to find a periodic sequence of period P, values in 1..P.
    # The sequence is defined for all n.
    # To be periodic of period P: a(n) = a(n + P).
    # Since there are no zeros, a(n) in 1..P.
    # Also, for each n, the last occurrence of a(n-1) before n-1 is at n-1-a(n).
    # So a(n-1) = a(n-1-a(n)), and no occurrence in between.
    
    # Let's represent the cycle as a list of length P: v[0], ..., v[P-1].
    # v[i] is the value at index n_2 + i + 1.
    # The condition is: for each i in 0..P-1:
    # v[i] = distance to the previous occurrence of v[i-1] (mod P).
    # Specifically, if X = v[i], then v[i-1] = v[i-1-X], and v[i-1-j] != v[i-1] for 0 < j < X.
    # So X is the unique smallest positive integer such that v[i-1-X] == v[i-1].
    # Note that indices are modulo P.
    
    solutions = []
    def backtrack(idx, current_v):
        if idx == P:
            # Check all conditions (especially wrap-around)
            ok = True
            for i in range(P):
                X = current_v[i]
                # Check that v[i-1-X] == v[i-1]
                if current_v[(i - 1 - X) % P] != current_v[(i - 1) % P]:
                    ok = False
                    break
                # Check no intermediate occurrences
                for j in range(1, X):
                    if current_v[(i - 1 - j) % P] == current_v[(i - 1) % P]:
                        ok = False
                        break
            if ok:
                solutions.append(list(current_v))
            return
        
        for val in range(1, P + 1):
            current_v[idx] = val
            backtrack(idx + 1, current_v)
            
    backtrack(0, [0]*P)
    return solutions

for P in range(1, 6):
    sols = solve_periodic(P)
    print(f"P={P}: found {len(sols)} solutions")
    for sol in sols:
        # Check if v[i - X] == X for all i
        check_h_eq = True
        for i in range(P):
            X = sol[i]
            # We want to check if v[i - X] == X.
            # In index notation, the term at index i (which corresponds to n_2 + i + 1) has value X.
            # We want to check if the term at index i - X (corresponding to n_2 + i + 1 - X) has value X.
            # In mod P, this is sol[(i - X) % P] == X.
            if sol[(i - X) % P] != X:
                check_h_eq = False
        print(f"  sol={sol}, check_h_eq={check_h_eq}")
