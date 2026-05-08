def van_eck(n):
    seq = [0]
    seen = {}
    for i in range(n-1):
        last = seq[-1]
        if last in seen:
            dist = i - seen[last]
            seq.append(dist)
        else:
            seq.append(0)
        seen[last] = i
    return seq

for n in range(1, 20):
    seq = van_eck(n)
    c0 = seq.count(0)
    dist = len(set(seq))
    print(f"n={n}, count 0={c0}, dist={dist}")
