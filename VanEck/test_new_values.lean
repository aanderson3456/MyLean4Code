import Mathlib
import VanEck.VanEck

lemma exists_bound_for_new_values (B : ℕ) : 
    ∃ M, ∀ m > M, vanEckNthTerm m = 0 → vanEckNthTerm (m - 1) > B := by {
  induction' B with B ih
  · use 1
    intro m hm h_zero
    have h_new := (vanEck_mth_term_eq_zero_iff_prev_term_new (m - 1)).mp (by {
      have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.le_of_lt hm)
      rw [hm1]
      exact h_zero
    })
    by_contra h_le_0
    have h_eq_0 : vanEckNthTerm (m - 1) = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_lt h_le_0)
    have hc := h_new 0 (by omega)
    rw [h_eq_0] at hc
    have v0 : vanEckNthTerm 0 = 0 := rfl
    rw [v0] at hc
    exact hc rfl
  · rcases ih with ⟨M_B, h_MB⟩
    by_cases h_ex : ∃ i, vanEckNthTerm i = B + 1 ∧ ∀ j < i, vanEckNthTerm j ≠ B + 1
    · rcases h_ex with ⟨I, hI_eq, hI_first⟩
      use max M_B (I + 1)
      intro m hm h_zero
      have h1 : m > M_B := Nat.lt_of_le_of_lt (Nat.le_max_left _ _) hm
      have hm_prev_gt_B := h_MB m h1 h_zero
      have h2 : m > I + 1 := Nat.lt_of_le_of_lt (Nat.le_max_right _ _) hm
      
      have h_new := (vanEck_mth_term_eq_zero_iff_prev_term_new (m - 1)).mp (by {
        have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
        rw [hm1]
        exact h_zero
      })
      
      by_contra h_le_B1
      have h_eq_B1 : vanEckNthTerm (m - 1) = B + 1 := by omega
      
      have hc := h_new I (by omega)
      rw [h_eq_B1] at hc
      exact hc hI_eq
    · push_neg at h_ex
      use M_B
      intro m hm h_zero
      have hm_prev_gt_B := h_MB m hm h_zero
      
      have h_new := (vanEck_mth_term_eq_zero_iff_prev_term_new (m - 1)).mp (by {
        have hm1 : m - 1 + 1 = m := Nat.sub_add_cancel (by omega)
        rw [hm1]
        exact h_zero
      })
      
      by_contra h_le_B1
      have h_eq_B1 : vanEckNthTerm (m - 1) = B + 1 := by omega
      
      -- If m-1 is the first occurrence of B+1, it satisfies h_ex condition!
      have h_first : ∀ j < m - 1, vanEckNthTerm j ≠ B + 1 := by {
        intro j hj
        have hc := h_new j hj
        rw [h_eq_B1] at hc
        exact hc.symm
      }
      exact h_ex (m - 1) h_eq_B1 h_first
}
