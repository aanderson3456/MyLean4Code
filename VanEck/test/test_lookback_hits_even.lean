import VanEck
import FinishedSurjLemmas
import Mathlib.Tactic.Omega

lemma lookback_step (m X : ℕ) (h_X : vanEckNthTerm m = X) (h_X_odd : X % 2 = 1) 
    (h_prev_nz : vanEckNthTerm (m - 1) ≠ 0) :
    ∃ prev < m - 1, vanEckNthTerm prev = vanEckNthTerm (m - 1) ∧ prev % 2 = m % 2 := by {
  have hX_pos : X ≠ 0 := by omega
  have hm_pos : m > 0 := by
    by_contra hc
    have h0 : m = 0 := by omega
    rw [h0] at h_X
    have hv0 : vanEckNthTerm 0 = 0 := rfl
    rw [hv0] at h_X
    omega
  have hm_sub : m - 1 + 1 = m := Nat.sub_add_cancel hm_pos
  have hk : m - 1 ≥ 1 := by
    by_contra hc
    have hm1 : m - 1 = 0 := by omega
    have hm1_eq : m = 1 := by omega
    rw [hm1_eq] at h_X
    have hv1 : vanEckNthTerm 1 = 0 := rfl
    rw [hv1] at h_X
    omega
  have ht := gap_determines_value (m - 1) hk X (by decide) (by rw [hm_sub]; exact h_X) hX_pos
  use (m - 1 - X)
  have h_X_ge_1 : X ≥ 1 := by omega
  have hm1_pos : m - 1 > 0 := hk
  have h_lt : m - 1 - X < m - 1 := Nat.sub_lt hm1_pos h_X_ge_1
  have h_par : (m - 1 - X) % 2 = m % 2 := by
    have h_eq : (m - 1 - X) + X + 1 = m := by omega
    omega
  exact ⟨h_lt, ht.symm, h_par⟩
}

lemma lookback_hits_even (m : ℕ) (h_odd : vanEckNthTerm m % 2 = 1) :
    ∃ curr_k ≤ m, curr_k % 2 = m % 2 ∧ vanEckNthTerm (curr_k - 1) % 2 = 0 := by {
  induction' m using Nat.strong_induction_on with m ih
  by_cases h0 : vanEckNthTerm (m - 1) % 2 = 0
  · exact ⟨m, Nat.le_refl m, rfl, h0⟩
  · have h1 : vanEckNthTerm (m - 1) % 2 = 1 := by omega
    have h_nz : vanEckNthTerm (m - 1) ≠ 0 := by omega
    have h_step := lookback_step m (vanEckNthTerm m) rfl h_odd h_nz
    rcases h_step with ⟨prev, h_prev_lt, h_prev_val, h_prev_par⟩
    have h_prev_odd : vanEckNthTerm prev % 2 = 1 := by
      rw [h_prev_val]
      exact h1
    have h_prev_lt_m : prev < m := by omega
    have h_ih := ih prev h_prev_lt_m h_prev_odd
    rcases h_ih with ⟨curr_k, h_curr_le, h_curr_par, h_curr_even⟩
    have h_le : curr_k ≤ m := by omega
    have h_par : curr_k % 2 = m % 2 := by
      rw [h_curr_par, h_prev_par]
    exact ⟨curr_k, h_le, h_par, h_curr_even⟩
}
