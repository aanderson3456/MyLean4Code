import VanEck.Basic
import VanEck

open List

lemma zero_dom_base (x : ℕ) : (vanEck 0).count x ≤ (vanEck 0).count 0 := by
  change [0].count x ≤ [0].count 0
  by_cases h : x = 0
  · rw [h]
  · have h1 : [0].count x = 0 := by
      apply count_eq_zero_of_not_mem
      intro h_mem
      cases h_mem with
      | head => exact h rfl
      | tail _ h_nil => cases h_nil
    rw [h1]
    exact Nat.zero_le _

lemma vanEck_succ_eq_append (n : ℕ) : vanEck (n + 1) = vanEck n ++ [vanEckNextTerm (vanEck n)] := by
  rfl

lemma count_le_count_add_one (n x : ℕ) : (vanEck (n + 1)).count x ≤ (vanEck n).count x + 1 := by
  rw [vanEck_succ_eq_append n]
  rw [count_append]
  have h1 : [vanEckNextTerm (vanEck n)].count x ≤ 1 := by
    by_cases h : vanEckNextTerm (vanEck n) = x
    · rw [h]
      have hsimp : [x].count x = 1 := by simp
      rw [hsimp]
    · have h0 : [vanEckNextTerm (vanEck n)].count x = 0 := by
        apply count_eq_zero_of_not_mem
        intro h_mem
        cases h_mem with
        | head => exact h rfl
        | tail _ h_nil => cases h_nil
      rw [h0]; exact Nat.zero_le _
  exact Nat.add_le_add_left h1 _

lemma zero_count_monotone (n : ℕ) : (vanEck n).count 0 ≤ (vanEck (n + 1)).count 0 := by
  rw [vanEck_succ_eq_append n]
  rw [count_append]
  exact Nat.le_add_right _ _
