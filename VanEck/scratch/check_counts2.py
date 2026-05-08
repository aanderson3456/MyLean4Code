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

seq = van_eck(100000)
counts = {}
for x in seq:
    counts[x] = counts.get(x, 0) + 1

max_non_zero = 0
for k, v in counts.items():
    if k != 0:
        max_non_zero = max(max_non_zero, v)

print(f"count 0: {counts[0]}")
print(f"max count non-zero: {max_non_zero}")
