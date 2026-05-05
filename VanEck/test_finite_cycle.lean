import Mathlib
import VanEck.VanEck
import VanEck.ImpossiblePatterns

lemma finite_cycle_gap_collapse (n_1 n_2 K : ℕ)
    (hn1_lt_n2 : n_1 < n_2)
    (h_K_large : K ≥ n_2 - n_1 + 3)
    (h_no_zero : ∀ k, 1 ≤ k → k ≤ K → vanEckNthTerm (n_2 + k) ≠ 0)
    (h_no_twos : ∀ m > n_1, vanEckNthTerm m ≠ 2)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k)) : False := by {
  let P := n_2 - n_1
  have h_P_pos : P ≥ 1 := Nat.succ_le_of_lt hn1_lt_n2

  -- Step 1: Prove that all elements in the period are bounded by P
  have h_val_le_P : ∀ k, 1 ≤ k → k ≤ P + 1 → vanEckNthTerm (n_2 + k) ≤ P := by {
    intro k hk1 hkP
    -- We know v(n_2+k) is the gap to the previous occurrence.
    -- Since v(n_2+k-1) = v(n_1+k-1) = v(n_2+k-1-P).
    -- The previous occurrence of v(n_2+k-1) is AT LEAST as recent as n_2+k-1-P.
    -- So the gap is AT MOST P.
    sorry
  }

  -- Step 2: The mapping f(k) = k - v(k) is injective.
  have h_inj : ∀ i j, 1 ≤ i → i < j → j ≤ P + 1 → n_2 + i - vanEckNthTerm (n_2 + i) ≠ n_2 + j - vanEckNthTerm (n_2 + j) := by {
    intro i j hi hij hj
    have hi_pos : vanEckNthTerm (n_2 + i) > 0 := Nat.pos_of_ne_zero (h_no_zero i hi (by omega))
    exact vanEck_idx_sub_val_unique (n_2 + i) (n_2 + j) hi_pos (by omega)
  }

  -- Step 3: By evaluating the range of f(k), we map P+1 elements to a set of size P, contradiction!
  -- Wait, for k in 1..P+1:
  -- k - v(n_2+k) >= k - P. So n_2+k - v(n_2+k) >= n_2+k - P >= n_2+1 - P = n_1 + 1.
  -- And n_2+k - v(n_2+k) <= n_2+k - 1 (since v >= 1).
  -- If k <= P, max is n_2+P-1.
  -- Let's trace it carefully.
  sorry
}
