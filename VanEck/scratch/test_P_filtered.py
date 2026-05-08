import itertools

def test_P(P):
    valid = []
    allowed_v = [1] + list(range(3, P+1))
    for v in itertools.product(allowed_v, repeat=P):
        C_P = sum(v)
        if C_P % P != 0:
            continue
        C = C_P // P
        if C < 2:
            continue
            
        f = [(k + 1 - v[k]) % P for k in range(P)]
        if len(set(f)) == P:
            # Check constraints on the period (considering it wraps around since it's periodic)
            # Actually, the sequence evaluates its own period, so the period repeats.
            v_ext = v + v + v
            
            bad = False
            for i in range(len(v_ext) - 1):
                # No consecutive 1s
                if v_ext[i] == 1 and v_ext[i+1] == 1:
                    bad = True
                    break
                # Consecutive equals must be followed by 1
                if v_ext[i] == v_ext[i+1]:
                    if i+2 < len(v_ext) and v_ext[i+2] != 1:
                        bad = True
                        break
                        
            for i in range(len(v_ext) - 2):
                # No alternating pairs (x, y, x)
                if v_ext[i] == v_ext[i+2]:
                    bad = True
                    break
                    
            if not bad:
                valid.append((C, v))
    return valid

for P in range(3, 12):
    res = test_P(P)
    print(f"P={P}, valid={len(res)}")
    if res:
        print("Examples:", res[:2])
