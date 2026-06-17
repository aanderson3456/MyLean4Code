# Let's check eventually periodic Van Eck sequences.
# Since the actual Van Eck sequence is not known to be periodic (and we want to prove it's not),
# let's generate the actual Van Eck sequence up to 2000 terms and check if there are any
# "pseudo-periodic" tail segments, or simply check if for ANY m where a(m) = X > 0,
# does a(m-X) = X hold when there is a local periodicity?
# Wait, let's look at the actual Van Eck sequence terms.
# Is it possible that for some m, a(m) = X and a(m-X) == X?
# Yes, we saw m=6, X=2, a(4)=2.
# But for m=13, X=2, a(11)=5 != 2.
# Is there any theorem in the codebase that proves `vanEckNthTerm (n_2 + k.val + 1 - X) = X`?
# Let's search SurjectivityLemmas.lean or basic files for "n_2 + k.val + 1 - X" or similar.

import re

# Read InfiniteTwos.lean to see how X is defined and if there is any comment or similar proof.
with open("/Users/austinanderson/GitHub/MyLean4Code/VanEck/InfiniteTwos.lean", "r") as f:
    content = f.read()

# Let's search for "vanEckNthTerm (n_2 + k.val + 1 - X)"
matches = re.findall(r".*vanEckNthTerm \(n_2 \+ k\.val \+ 1 - X\).*", content)
for m in matches:
    print(m)
