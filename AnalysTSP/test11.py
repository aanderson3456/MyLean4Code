import re

with open("WeierstrassLimitR2.lean", "r") as f:
    text = f.read()

text = text.replace("abs_sub_comm a] at hd", "abs_sub_comm ((u ∘ φ) n) a] at hd")
with open("WeierstrassLimitR2_test8.lean", "w") as f:
    f.write(text)

