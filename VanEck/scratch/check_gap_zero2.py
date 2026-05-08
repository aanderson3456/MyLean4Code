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
for i in range(1, len(seq)):
    x = seq[i]
    if x > 1:
        # this means seq[i-1] had a gap of x
        # so seq[i-1] == seq[i-1-x]
        # check if there is a 0 strictly between them: seq[i-x : i-1]
        gap_block = seq[i-x : i-1]
        if 0 not in gap_block:
            print(f"Index {i}, x={x}, block={gap_block}")
            break
else:
    print("Every gap > 1 contains a 0!")
