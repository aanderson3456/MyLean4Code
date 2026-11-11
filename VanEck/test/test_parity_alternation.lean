import VanEck
import InfiniteEvens

lemma parity_alternation (N : ℕ) (h_odds : OnlyOddsAndZerosAfter N)
    (X curr prev : ℕ) (h_curr : vanEckNthTerm curr = X) (h_prev : vanEckNthTerm prev = X)
    (h_lt : prev < curr) (h_between : ∀ i, prev < i → i < curr → vanEckNthTerm i ≠ X)
    (h_curr_gt : N < curr) :
    curr % 2 ≠ prev % 2 := by {
  have h_match : listNth (vanEck curr) ((vanEck curr).length - 1) = listNth (vanEck curr) prev := by
    have h_len : (vanEck curr).length = curr + 1 := vanEckLength curr
    have h_len1 : (vanEck curr).length - 1 = curr := by omega
    rw [h_len1]
    have hd_curr : listNth (vanEck curr) curr = vanEckNthTerm curr := rfl
    have hd_prev : listNth (vanEck curr) prev = vanEckNthTerm prev := by
      exact VanEck_deterministic curr prev (Nat.le_of_lt h_lt)
    rw [hd_curr, hd_prev, h_curr, h_prev]
  
  have h_fail : ∀ k, 1 ≤ k → k ≤ curr - prev - 1 → listNth (vanEck curr) ((vanEck curr).length - 1) ≠ listNth (vanEck curr) (prev + k) := by
    intro k hk1 h_le
    have h_len1 : (vanEck curr).length - 1 = curr := by
      have h_len : (vanEck curr).length = curr + 1 := vanEckLength curr
      omega
    rw [h_len1]
    have hd_curr : listNth (vanEck curr) curr = vanEckNthTerm curr := rfl
    have hd_prevk : listNth (vanEck curr) (prev + k) = vanEckNthTerm (prev + k) := by
      exact VanEck_deterministic curr (prev + k) (by omega)
    rw [hd_curr, hd_prevk, h_curr]
    exact fun h => h_between (prev + k) (by omega) (by omega) h.symm
  
  have h_ms := matchSearch_eq_dist (vanEck curr) prev (curr - prev - 1) h_match h_fail
  have h_sub : prev + (curr - prev - 1) + 1 = curr := by omega
  rw [h_sub] at h_ms
  have h_gap := vanEck_is_gap (curr + 1) (by omega)
  have h_len2 : (vanEck curr).length - 1 - prev = curr - prev := by
    have h_len : (vanEck curr).length = curr + 1 := vanEckLength curr
    omega
  rw [h_len2] at h_ms
  have h_sub_c : curr + 1 - 1 = curr := rfl
  rw [h_sub_c] at h_gap
  rw [h_ms] at h_gap
  have h_val : vanEckNthTerm (curr + 1) = curr - prev := h_gap
  
  have h_curr1_gt : curr + 1 > N := by omega
  have h_or := h_odds (curr + 1) h_curr1_gt
  have h_odd : (curr - prev) % 2 = 1 := by
    cases h_or with
    | inl h_zero =>
      have hc : curr - prev = 0 := by
        rw [← h_val]
        exact h_zero
      omega
    | inr h_is_odd =>
      rw [← h_val]
      exact h_is_odd
  omega
}
