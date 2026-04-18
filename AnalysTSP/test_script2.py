import re

with open("WeierstrassLimitR2.lean", "r") as f:
    content = f.read()

# Replace line 1409
content = content.replace("intro y hy; simp at hy", "intro y hy; simp [S] at hy")

# Replace line 1455 block
old_block1 = """        rcases hK_nonempty with ⟨x, hx⟩
        simp_rw [Set.mem_iUnion] at ht_cover
        rcases ht_cover hx with ⟨c, hc, _⟩; exact ⟨c, hc⟩
      · intro x hx
        simp_rw [Set.mem_iUnion] at ht_cover ⊢
        rcases ht_cover hx with ⟨c, hc_t, h_dist⟩"""
        
new_block1 = """        rcases hK_nonempty with ⟨x, hx⟩
        have htc := ht_cover hx
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at htc
        rcases htc with ⟨c, hc_t, _⟩; exact ⟨c, hc_t⟩
      · intro x hx
        simp only [Set.mem_iUnion, Set.mem_setOf_eq]
        have htc := ht_cover hx
        simp only [Set.mem_iUnion, Set.mem_setOf_eq] at htc
        rcases htc with ⟨c, hc_t, h_dist⟩"""

content = content.replace(old_block1, new_block1)

# Add haveI : DecidableEq \iota'
content = content.replace("let f' (c : ℝ) : ι' :=", "haveI : DecidableEq ι' := Classical.decEq _\n      let f' (c : ℝ) : ι' :=")

with open("WeierstrassLimitR2_test.lean", "w") as f:
    f.write(content)

