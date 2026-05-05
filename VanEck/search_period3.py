def check_seq(seq):
    P = len(seq)
    for x in seq:
        if x == 0 or x == 2:
            return False
    for i in range(P):
        if seq[i] == 1 and seq[(i+1)%P] == 1:
            return False
    for i in range(P):
        val = seq[i]
        d = seq[(i+1)%P]
        if seq[(i - d) % P] != val:
            return False
        for j in range(1, d):
            if seq[(i - j) % P] == val:
                return False
    return True

# We can use a backtracking approach to find a valid period instead of itertools.product
def solve(P):
    seq = [0] * P
    def backtrack(idx):
        if idx == P:
            if check_seq(seq):
                return True
            return False
        for val in range(1, P+1):
            if val == 2: continue
            if idx > 0 and seq[idx-1] == 1 and val == 1: continue
            seq[idx] = val
            if backtrack(idx+1): return True
        return False
    return backtrack(0)

for P in range(1, 20):
    if solve(P):
        print(f"Found period {P}")
    else:
        print(f"No period of length {P}")
