def sim():
    seq = [0]
    last_pos = {0: 0}
    for i in range(1, 100):
        prev = seq[i-1]
        if prev in last_pos and last_pos[prev] < i - 1:
            val = i - 1 - last_pos[prev]
            if val % 2 == 0:
                print(f"Failed at step {i}: val {val} is even")
                return
        else:
            val = 0
        last_pos[prev] = i - 1
        seq.append(val)
        print(f"{i}: {val}")
sim()
