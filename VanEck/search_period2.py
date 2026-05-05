def check_seq(seq):
    P = len(seq)
    for x in seq:
        if x == 0 or x == 2:
            return False
    # Check consecutive 1s
    for i in range(P):
        if seq[i] == 1 and seq[(i+1)%P] == 1:
            return False
    # Check van eck property
    for i in range(P):
        val = seq[i]
        d = seq[(i+1)%P]
        if seq[(i - d) % P] != val:
            return False
        for j in range(1, d):
            if seq[(i - j) % P] == val:
                return False
    return True

import itertools
for P in range(1, 11):
    found = False
    for seq in itertools.product(range(1, P+1), repeat=P):
        if check_seq(seq):
            print(f"Found period {P}: {seq}")
            found = True
    if not found:
        print(f"No period of length {P}")
