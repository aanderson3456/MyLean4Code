import re

with open("WeierstrassLimitR2_test.lean", "r") as f:
    text = f.read()

old = """      rw [Subtype.dist_eq]
      exact abs_sub_comm L_val ((x_seq (φ n)).val) ▸ h_abs"""

new = """      rw [Subtype.dist_eq, Real.dist_eq, abs_sub_comm]
      exact h_abs"""

text = text.replace(old, new)
with open("WeierstrassLimitR2_test3.lean", "w") as f:
    f.write(text)

