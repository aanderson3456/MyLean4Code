import Mathlib
import VanEck.VanEck.Basic

lemma test (n_2 start : ℕ) (hh : start ≤ n_2) : n_2 + 3 - start = n_2 - start + 3 := by
  have hA : n_2 + 3 = 3 + n_2 := Nat.add_comm _ _
  have hB : 3 + n_2 - start = 3 + (n_2 - start) := Nat.add_sub_assoc hh 3
  have hC : 3 + (n_2 - start) = n_2 - start + 3 := Nat.add_comm _ _
  rw [hA, hB, hC]
