import InfiniteEvens
import FinishedSurjLemmas
import Mathlib.Tactic.Omega

lemma zero_gap_odd (N : ℕ) (h_odds : OnlyOddsAndZerosAfter N) 
    (z_a z_b : ℕ) (hz_a : vanEckNthTerm z_a = 0) (hz_b : vanEckNthTerm z_b = 0)
    (hz_lt : z_a < z_b) (h_between : ∀ i, z_a < i → i < z_b → vanEckNthTerm i ≠ 0)
    (h_bounds : N < z_a) :
    z_b % 2 ≠ z_a % 2 := by {
  have h_X : z_b - z_a > 0 := Nat.sub_pos_of_lt hz_lt
  have h_zb_ge_1 : z_b ≥ 1 := by omega
  have h_match : vanEckNthTerm z_b = vanEckNthTerm (z_b - (z_b - z_a)) := by
    have h_sub : z_b - (z_b - z_a) = z_a := Nat.sub_sub_self (Nat.le_of_lt hz_lt)
    rw [h_sub, hz_b, hz_a]
  have h_fail : ∀ i, z_b - (z_b - z_a) < i → i < z_b → vanEckNthTerm z_b ≠ vanEckNthTerm i := by
    intro i hi_gt hi_lt
    have h_sub : z_b - (z_b - z_a) = z_a := Nat.sub_sub_self (Nat.le_of_lt hz_lt)
    rw [h_sub] at hi_gt
    have h_neq := h_between i hi_gt hi_lt
    rw [hz_b]
    exact fun h => h_neq h.symm
  have h_val := gap_determines_value z_b h_zb_ge_1 (z_b - z_a) h_match h_fail h_X
  have h_zb1_gt_N : z_b + 1 > N := by omega
  have h_or := h_odds (z_b + 1) h_zb1_gt_N
  have h_odd : (z_b - z_a) % 2 = 1 := by
    cases h_or with
    | inl h_is_odd => 
      rw [← h_val]
      exact h_is_odd
    | inr h_is_zero => 
      rw [h_val] at h_is_zero
      have hc : z_b - z_a = 0 := h_is_zero
      omega
  omega
}
