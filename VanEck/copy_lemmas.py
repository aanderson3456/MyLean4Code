with open("SurjectivityLemmas.lean", "r") as f:
    lines = f.readlines()

ranges = [
    (1, 337),
    (350, 449),
    (469, 471),
    (477, 556),
    (561, 571)
]

with open("FinishedSurjLemmas.lean", "w") as f:
    for start, end in ranges:
        for i in range(start - 1, end):
            f.write(lines[i])
