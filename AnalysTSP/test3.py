import re

with open("WeierstrassLimitR2.lean", "r") as f:
    text = f.read()

# 1. Fix line 1447
text = text.replace("abs_sub_comm _ _ ▸ h_d1", "abs_sub_comm L (u (φ N)) ▸ h_d1")

# 2. Fix line 1503
text = text.replace("rw [heq_val, eucDistComm]; unfold euclideanDist", "rw [heq_val]; unfold euclideanDist")

# 3. Fix line 1509
text = text.replace("rwa [Subtype.dist_eq (x_seq (φ n)) L, abs_sub_comm]", "rwa [Subtype.dist_eq (x_seq (φ n)) L, abs_sub_comm ((x_seq (φ n)).val) L.val]")

# 4. Fix line 1513
text = text.replace("rw [← hx_seq (φ n), eucDistComm]", "rw [← hx_seq (φ n), eucDistComm (f L).val _]")

# 5. Fix line 1522
text = text.replace("theorem PathsCompact (S : Set (ℝ × ℝ)) : IsPathInR2 S → IsCompactR2Subcover S", "theorem PathsCompact {ι : Type} (S : Set (ℝ × ℝ)) : IsPathInR2 S → @IsCompactR2Subcover ι S")

with open("WeierstrassLimitR2_test.lean", "w") as f:
    f.write(text)

