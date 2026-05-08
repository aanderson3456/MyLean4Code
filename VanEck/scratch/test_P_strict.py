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
            v_ext = v + v + v + v
            
            bad = False
            for i in range(P, 2*P):
                x = v_ext[i]
                # The value x is the gap to the previous identical element
                if v_ext[i - x] != v_ext[i]:
                    bad = True
                    break
                # There must be no identical element in between
                for j in range(1, x):
                    if v_ext[i - j] == v_ext[i]:
                        bad = True
                        break
                if bad:
                    break
                    
            if not bad:
                valid.append((C, v))
    return valid

for P in range(3, 12):
    res = test_P(P)
    print(f"P={P}, valid={len(res)}")
    if res:
        print("Examples:", res[:2])
