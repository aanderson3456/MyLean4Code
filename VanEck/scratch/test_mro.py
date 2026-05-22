def check_mro(v):
    P = len(v)
    for k in range(P):
        val = v[k]
        # find the most recent occurrence of 'val' before k (modulo P)
        # we check distances d from 1 to P
        found = False
        for d in range(1, P+1):
            prev_idx = (k - d) % P
            if v[prev_idx] == val:
                if d != val:
                    print(f"MRO failed at index {k}: value is {val}, but most recent occurrence is {d} steps ago (at index {prev_idx})")
                    return False
                found = True
                break
        if not found:
            print(f"Value {val} only appears once, invalid for cycle")
            return False
    print("MRO satisfied!")
    return True

check_mro([4,6,4,6,4,6])
