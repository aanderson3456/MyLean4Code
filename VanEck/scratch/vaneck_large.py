def van_eck(n):
    a = [0]
    last_seen = {0: 0}
    for i in range(1, n):
        prev = a[-1]
        if prev in last_seen:
            nxt = (i - 1) - last_seen[prev]
        else:
            nxt = 0
        a.append(nxt)
        last_seen[prev] = i - 1
    return a

a = van_eck(500000)
zeros = [i for i, x in enumerate(a) if x == 0]
falses = []
seen = set()
for i, x in enumerate(a):
    if x == 0 and i > 0 and i in zeros:
        # i is zk
        # post_zero is a[i+1]
        if i+1 < len(a):
            post_zero = a[i+1]
            if post_zero not in seen:
                # wait, seen only contains elements before i+1?
                # yes, because we add a[i] to seen below
                falses.append((i, post_zero))
    seen.add(x)
print("Falses found:", falses)
