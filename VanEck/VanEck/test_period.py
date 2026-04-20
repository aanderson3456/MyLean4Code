def check_periodic(M):
    # A periodic Van Eck sequence of period P, bounded by M, no zeros.
    # Since it's periodic, every element value IS EXACTLY its distance to the prior occurrence.
    # So seq[i] = distance to previous seq[i-1]
    # Since period is P, the distance is ALWAYS <= P.
    # Also, distance is exactly the gap between identical elements.
    import itertools
    for P in range(1, M+1):
        for seq in itertools.product(range(1, M+1), repeat=P):
            # check if seq is valid
            valid = True
            for i in range(P):
                val = seq[i]
                prev_elem = seq[i-1]
                # the distance to prev_elem in this periodic sequence MUST be exactly val
                # so prev_elem must appear val steps ago: seq[(i - 1 - val) % P] == prev_elem
                if seq[(i - 1 - val) % P] != prev_elem:
                    valid = False
                    break
                # AND it must NOT appear sooner!
                for d in range(1, val):
                    if seq[(i - 1 - d) % P] == prev_elem:
                        valid = False
                        break
                if not valid: break
            if valid:
                print(f"M={M}, P={P} Valid Sequence: {seq}")

print("Checking up to M=6:")
check_periodic(6)
