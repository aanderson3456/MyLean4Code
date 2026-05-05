import Mathlib
import VanEck
import VanEck.InfiniteTwos

lemma test (n_1 n_2 K : ℕ) 
    (hn1_lt_n2 : n_1 < n_2)
    (h_K_large : K ≥ n_2 - n_1 + 3)
    (h_no_twos : ∀ m > n_1, vanEckNthTerm m ≠ 2)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k)) : 
    False := by {
  sorry
}
