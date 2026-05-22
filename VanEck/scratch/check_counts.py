def check_periodic():
    for P in range(4, 15):
        # find sequences of length P from {1, 3, 4, ..., P}
        # such that v[k] is the distance to the previous occurrence of v[k-1]
        # v[k] = d means v[k-1] == v[k-1-d]
        # and v[k-1] != v[k-1-j] for 0 < j < d
        import itertools
        allowed = [x for x in range(1, P+1) if x != 2]
        for v in itertools.product(allowed, repeat=P):
            valid = True
            for k in range(P):
                d = v[k]
                prev_val = v[(k-1)%P]
                # the occurrence at distance d should be equal to prev_val
                if v[(k-1-d)%P] != prev_val:
                    valid = False
                    break
                # no earlier occurrence
                found_earlier = False
                for j in range(1, d):
                    if v[(k-1-j)%P] == prev_val:
                        found_earlier = True
                        break
                if found_earlier:
                    valid = False
                    break
            if valid:
                print(f"P={P} valid sequence: {v}")

check_periodic()
