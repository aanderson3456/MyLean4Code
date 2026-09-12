def check_prefix(prefix):
    seq = list(prefix)
    last_pos = {}
    for i, v in enumerate(prefix):
        last_pos[v] = i
    
    for i in range(len(prefix), len(prefix) + 50):
        prev = seq[i-1]
        if prev in last_pos and last_pos[prev] < i - 1:
            val = i - 1 - last_pos[prev]
            if val % 2 == 0 and val != 0:
                return False, val, seq
        else:
            val = 0
        last_pos[prev] = i - 1
        seq.append(val)
    return True, 0, seq

import random
for _ in range(10):
    pref = [random.choice([0, 1, 3, 5, 7, 9]) for _ in range(15)]
    success, val, seq = check_prefix(pref)
    if not success:
        print(f"Failed with even {val}. Seq: {seq}")
