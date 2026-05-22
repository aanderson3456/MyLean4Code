def van_eck(n):
    a = [0] * n
    last_seen = {0: 0}
    for i in range(1, n):
        prev = a[i-1]
        if prev in last_seen:
            nxt = (i - 1) - last_seen[prev]
        else:
            nxt = 0
        a[i] = nxt
        last_seen[prev] = i - 1
    return a

n = 10000000
a = van_eck(n)
falses = []
seen = set()
for i in range(len(a)):
    x = a[i]
    if x == 0 and i > 0:
        if i+1 < len(a):
            post_zero = a[i+1]
            if post_zero not in seen:
                falses.append((i, post_zero))
    seen.add(x)
print("Falses found up to 10M:", falses)
