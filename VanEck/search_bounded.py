def check_seq(P):
    # We need a sequence of length 2P+4 (from 0 to 2P+3).
    # n_1 = 0, n_2 = P. K = P+3.
    # v(k) = seq[k]
    # We need seq[k] == seq[k+P] for k in 0..P+3.
    # We need seq[P+k] != 0 and != 2 for k in 1..P+3.
    
    # Actually, we can just backtrack to find ANY valid Van Eck prefix.
    seq = [0] * (2*P + 4)
    def backtrack(idx):
        if idx == 2*P + 4:
            # Check periodicity
            for k in range(P+4):
                if seq[k] != seq[k+P]:
                    return False
            # Check no 0, 2
            for k in range(1, P+4):
                if seq[P+k] == 0 or seq[P+k] == 2:
                    return False
            return True
            
        # Try all valid next values based on Van Eck rule
        if idx == 0:
            seq[idx] = 0
            if backtrack(idx+1): return True
        else:
            val = seq[idx-1]
            found = -1
            for j in range(idx-2, -1, -1):
                if seq[j] == val:
                    found = j
                    break
            if found == -1:
                seq[idx] = 0
            else:
                seq[idx] = idx - 1 - found
                
            # Prune if it violates the no 0, 2 rule in the target region
            if idx > P and (seq[idx] == 0 or seq[idx] == 2):
                return False
                
            if backtrack(idx+1): return True
        return False

    return backtrack(0)

for P in range(1, 10):
    if check_seq(P):
        print(f"Found bounded period for P={P}")
    else:
        print(f"No bounded period for P={P}")
