import VanEck.InfiniteTwos

lemma vanEck_val_divides_period (n_1 n_2 m x : ℕ) (P : ℕ)
    (hP : P = n_2 - n_1)
    (hn1_lt_n2 : n_1 < n_2)
    (h_per : ∀ k ≤ P, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k))
    (hm_ge : m ≥ n_2) (hm_lt : m < n_2 + P)
    (h_val : vanEckNthTerm m = x) (hx_pos : x > 0) (hx_le : x ≤ P) :
    x ∣ P := by {
  sorry
}
