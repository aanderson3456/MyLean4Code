import Mathlib
import VanEck.VanEck

lemma test_bound (n_1 n_2 K : ℕ) 
    (hn1_lt_n2 : n_1 < n_2)
    (h_K_large : K ≥ n_2 - n_1 + 3)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k))
    (k : ℕ) (hk1 : 1 ≤ k) (hkP : k ≤ n_2 - n_1) :
    vanEckNthTerm (n_2 + k) ≤ n_2 - n_1 := by {
  let P := n_2 - n_1
  have h_P_pos : P ≥ 1 := Nat.succ_le_of_lt hn1_lt_n2
  have h_eq : vanEckNthTerm (n_2 + k - 1) = vanEckNthTerm (n_1 + k - 1) := by {
    have h_per_eval := h_per (k - 1) (by omega)
    exact h_per_eval.symm
  }
  have h_occ : vanEckNthTerm (n_2 + k - 1) = vanEckNthTerm (n_2 + k - 1 - P) := by {
    have h1 : n_2 + k - 1 - P = n_1 + k - 1 := by omega
    rw [h1]
    exact h_eq
  }
  have hm := vanEck_term_is_matchSearch (n_2 + k) (by omega)
  have hsub : n_2 + k - 1 + 1 = n_2 + k := by omega
  rw [← hsub] at hm
  -- now hm : vanEckNthTerm (n_2 + k - 1 + 1) = matchSearch (vanEck (n_2 + k - 1)) (n_2 + k - 1)
  sorry
}
