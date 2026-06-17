def van_eck(n):
    seq = []
    seen = {}
    for i in range(n):
        if i == 0:
            val = 0
        else:
            prev = seq[-1]
            if prev in seen:
                val = i - 1 - seen[prev]
            else:
                val = 0
        seq.append(val)
        if i > 0:
            seen[seq[-2]] = i - 1
    return seq

seq = van_eck(100)
for m in range(2, 50):
    X = seq[m]
    if X > 0:
        print(f"m={m}, X={X}, a(m-X)={seq[m-X]}")
