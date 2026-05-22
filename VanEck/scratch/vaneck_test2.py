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

y = []
for i in range(1, len(zeros)):
    y.append(a[zeros[i]-1])

# are the d_k (post-zero values) always in y?
d = []
for i in range(1, len(zeros)-1):
    d.append(a[zeros[i]+1])

print(f"Number of zeros: {len(zeros)}")
print(f"Number of new values (y): {len(y)}")
print(f"Number of post-zero values (d): {len(d)}")

# check how many d are not in y
y_set = set(y)
not_in_y = [x for x in d if x not in y_set]
print(f"post-zero values not in y: {not_in_y}")
