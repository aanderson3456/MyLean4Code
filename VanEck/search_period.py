def check_seq(seq):
    # seq is a list of integers.
    # We treat it as a period.
    # So v(i) = seq[i % P].
    P = len(seq)
    for x in seq:
        if x == 0 or x == 2:
            return False
    # Check van eck property:
    # v(i+1) is the distance to the previous occurrence of v(i)
    # Since it's periodic, the distance must be exactly v(i+1).
    for i in range(P):
        val = seq[i]
        d = seq[(i+1)%P]
        # The previous occurrence of val should be d steps ago.
        # So seq[(i - d) % P] == val
        if seq[(i - d) % P] != val:
            return False
        # And there should be no occurrences in between
        for j in range(1, d):
            if seq[(i - j) % P] == val:
                return False
    return True

for P in range(1, 15):
    import itertools
    # values can be up to P, because gap <= P.
    # actually gap can be anything if it loops, but since it's the distance to previous occurrence,
    # and every element must appear in the period, the gap is <= P.
    # so values are in 1..P.
    found = False
    for seq in itertools.product(range(1, P+1), repeat=P):
        if check_seq(seq):
            print(f"Found period {P}: {seq}")
            found = True
    if not found:
        print(f"No period of length {P}")
