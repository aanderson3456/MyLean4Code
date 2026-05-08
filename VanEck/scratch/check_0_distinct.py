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

seq = van_eck(1000)
c0 = seq.count(0)
distinct = len(set(seq))
print(f"count 0: {c0}, distinct: {distinct}")
