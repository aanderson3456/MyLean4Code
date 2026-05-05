import Mathlib

lemma add_sub_add_right_test (n_1 n_2 k : ℕ) : n_2 + (k - 1) - (n_1 + (k - 1)) = n_2 - n_1 := by {
  exact Nat.add_sub_add_right n_2 (k - 1) n_1
}
