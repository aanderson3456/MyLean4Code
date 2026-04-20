import itertools

def is_valid_vaneck(seq, M):
    P = len(seq)
    for i in range(P):
        val = seq[i]
        # Check if the next element matches the gap
        # The next element is seq[(i+1)%P]
        # And the gap in seq for val
        gap = None
        for d in range(1, M+1):
            if seq[(i - d) % P] == val:
                gap = d
                break
        if gap is None:
            return False # no previous occurrence found within M steps
        if seq[(i+1) % P] != gap:
            return False
    return True

for M in range(2, 6):
    print(f"Testing M={M}")
    found = False
    for P in range(M, 8):
        # Generate all sequences of length P with elements in 1..M
        for seq in itertools.product(range(1, M+1), repeat=P):
            if max(seq) == M and is_valid_vaneck(seq, M):
                print(f"Found valid sequence for M={M}, P={P}: {seq}")
                found = True
    if not found:
        print(f"No valid sequences for M={M}")

