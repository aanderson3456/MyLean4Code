import re

with open("WeierstrassLimitR2_test.lean", "r") as f:
    text = f.read()

text = text.replace("exact abs_sub_comm _ _ ▸ h_abs", "exact abs_sub_comm L_val ((x_seq (φ n)).val) ▸ h_abs")

with open("WeierstrassLimitR2_test2.lean", "w") as f:
    f.write(text)

