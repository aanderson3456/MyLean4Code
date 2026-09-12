def get_vaneck(n):
    seq = [0]
    last_pos = {0: 0}
    for i in range(1, n):
        prev = seq[i-1]
        if prev in last_pos and last_pos[prev] < i - 1:
            val = i - 1 - last_pos[prev]
        else:
            val = 0
        last_pos[prev] = i - 1
        seq.append(val)
    return seq
# Just a dummy
