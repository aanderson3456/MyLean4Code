prefix = [0, 0, 1, 5, 3, 4, 3, 0, 3, 4]
seq = list(prefix)
last_pos = {}
for i, v in enumerate(prefix):
    last_pos[v] = i

for i in range(len(prefix), len(prefix) + 20):
    prev = seq[i-1]
    if prev in last_pos and last_pos[prev] < i - 1:
        val = i - 1 - last_pos[prev]
    else:
        val = 0
    last_pos[prev] = i - 1
    seq.append(val)
print(seq)
