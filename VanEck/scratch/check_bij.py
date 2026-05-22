import itertools
def check_P(P):
    valid = []
    # values can be 3 to P
    for v in itertools.product(range(3, P+1), repeat=P):
        # no consecutive equals
        if any(v[i] == v[(i+1)%P] for i in range(P)):
            continue
        # check bijection
        f = [(i - v[i]) % P for i in range(P)]
        if len(set(f)) == P:
            valid.append(v)
    return valid

for P in range(4, 12):
    valid = check_P(P)
    print(f"P={P}: {len(valid)} valid abstract cycles")
    if len(valid) > 0 and len(valid) <= 5:
        print("   ", valid)
