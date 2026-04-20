import VanEck.Basic
open Nat

lemma max_value_implies_M_eq_one_aux (n M k : ℕ) (h_bound : ∀ j ≥ n, vanEckNthTerm j ≤ M)
    (hk : k ≥ n + M)
    (h_kM : vanEckNthTerm k = M)
    (h_no_zeros : ∀ j ≥ n, vanEckNthTerm j ≠ 0) : M = 1 := by {
  sorry
}
