# Simulate Van Eck and trace the chain from zb-1
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

seq = get_vaneck(100)
for i in range(len(seq)):
    if seq[i] == 0:
        print(f"Zero at {i}")
        if i > 0:
            # trace back
            curr = i - 1
            print(f"  Trace start at {curr}")
            while seq[curr-1] != 0:
                X = seq[curr]
                curr = curr - 1 - X
                print(f"  Jump to {curr} (value={seq[curr]}, prev_val={seq[curr-1]})")
