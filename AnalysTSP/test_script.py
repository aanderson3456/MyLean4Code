import re

with open("WeierstrassLimitR2.lean", "r") as f:
    content = f.read()

# Replace line 1409
content = content.replace("intro y hy; simp at hy", "intro y hy; exact (Finset.not_mem_empty _ hy).elim")

# Replace line 1455
content = content.replace("simp_rw [Set.mem_iUnion] at ht_cover", "")
content = content.replace("simp_rw [Set.mem_iUnion] at ht_cover ⊢", "simp only [Set.mem_iUnion]")

with open("WeierstrassLimitR2_test.lean", "w") as f:
    f.write(content)

