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
            valid.append((C, v))
    return valid

for P in range(3, 10):
    res = test_P(P)
    print(f"P={P}, valid={len(res)}")
    if res:
        print("Examples:", res[:2])
