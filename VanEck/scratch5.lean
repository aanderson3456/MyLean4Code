import Mathlib
import VanEck
import VanEck.InfiniteTwos
import VanEck.ImpossiblePatterns

lemma local_periodicity_impossible (n_1 n_2 K : ℕ) 
    (hn1_lt_n2 : n_1 < n_2)
    (h_K_large : K ≥ n_2 - n_1 + 3)
    (h_no_twos : ∀ m > n_1, vanEckNthTerm m ≠ 2)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k)) : 
    False := by {
  have h_no_zero : ∀ k, 1 ≤ k → k ≤ K → vanEckNthTerm (n_2 + k) ≠ 0 := by {
    intro k hk1 hkK h_zero
    have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new (n_2 + k - 1)
    have hsub : n_2 + k - 1 + 1 = n_2 + k := Nat.sub_add_cancel hk1
    rw [hsub] at h_iff
    have h_new := h_iff.mp h_zero
    -- The previous term is vanEckNthTerm (n_2 + k - 1).
    -- But we know it appeared at n_1 + k - 1.
    have h_prev_eq : vanEckNthTerm (n_1 + k - 1) = vanEckNthTerm (n_2 + k - 1) := by {
      have hkm1 : k - 1 ≤ K := Nat.le_trans (Nat.sub_le k 1) hkK
      exact h_per (k - 1) hkm1
    }
    have h_not_new := h_new (n_1 + k - 1) (by {
      calc n_1 + k - 1 < n_2 + k - 1 := Nat.add_lt_add_right hn1_lt_n2 (k - 1)
    })
    exact h_not_new h_prev_eq
  }
  sorry
}
