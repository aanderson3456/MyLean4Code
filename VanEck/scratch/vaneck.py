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

a = van_eck(1000)
zeros = [i for i, x in enumerate(a) if x == 0]
for i in range(1, len(zeros)-1):
    zk = zeros[i]
    dk = zk - zeros[i-1]
    post_zero = a[zk+1]
    # is post_zero old?
    old = post_zero in a[:zk+1]
    print(f"Zero at {zk}, d_k = {dk}, post_zero = {post_zero}, old? {old}")
