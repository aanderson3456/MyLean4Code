prefix = [0, 0, 1, 5, 3, 4, 3, 0, 3, 4]
seq = list(prefix)
last_pos = {}
for i, v in enumerate(prefix):
    last_pos[v] = i

for i in range(len(prefix), len(prefix) + 1000):
    prev = seq[i-1]
    if prev in last_pos and last_pos[prev] < i - 1:
        val = i - 1 - last_pos[prev]
    else:
        val = 0
    last_pos[prev] = i - 1
    seq.append(val)
evens = [x for x in seq[len(prefix):] if x % 2 == 0 and x != 0]
print(f"Evens found: {evens}")
