def van_eck(n):
    seq = [0]
    seen = {}
    for i in range(n):
        last = seq[-1]
        if last in seen:
            dist = i - seen[last]
            seq.append(dist)
        else:
            seq.append(0)
        seen[last] = i
    return seq

seq = van_eck(100)
counts = {}
for x in seq:
    counts[x] = counts.get(x, 0) + 1

print(f"count 0: {counts[0]}")
for k, v in counts.items():
    if k != 0 and v >= counts[0] - 2:
        print(f"count {k}: {v}")

