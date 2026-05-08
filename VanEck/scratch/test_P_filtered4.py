import itertools

def test_P(P):
    valid = []
    allowed_v = [1] + list(range(3, P+1))
    for v in itertools.product(allowed_v, repeat=P):
        C_P = sum(v)
        if C_P % P != 0: continue
        if C_P // P < 2: continue
            
        f = [(k + 1 - v[k]) % P for k in range(P)]
        if len(set(f)) == P:
            # The value at f(k) MUST match the value at k
            # Wait, f(k) is the index of the PREVIOUS occurrence of v_{k-1}
            # The gap is v_k.
            # So v_{k-1} = v_{f(k)}.
            # Wait, let's use the sequence indexing: v[k] is the sequence value at index k.
            # The gap for v[k] is v[k+1].
            # So v[k+1] = P * d + (k - f(k)).
            # This means f(k) = k - v[k+1] mod P.
            # And the value at f(k) must be the same as the value at k.
            # So v[f(k)] == v[k].
            f_k = [(k - v[(k+1)%P]) % P for k in range(P)]
            if len(set(f_k)) == P:
                match = True
                for k in range(P):
                    if v[f_k[k]] != v[k]:
                        match = False
                        break
                if match:
                    v_ext = v + v + v
                    bad = False
                    for i in range(len(v_ext) - 2):
                        if v_ext[i] == 1 and v_ext[i+1] == 1: bad = True; break
                        if v_ext[i] == v_ext[i+1] and v_ext[i+2] != 1: bad = True; break
                        if v_ext[i+2] == 1 and v_ext[i] != v_ext[i+1]: bad = True; break
                        if v_ext[i] == v_ext[i+2]: bad = True; break
                    if not bad:
                        valid.append(v)
    return valid

for P in range(3, 12):
    res = test_P(P)
    print(f"P={P}, valid={len(res)}")
