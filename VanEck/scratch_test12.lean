import VanEck.Basic
import VanEck

open List

lemma non_zero_needs_generation (n x : ℕ) (hx : x > 0) : 
    (vanEck (n + 1)).count x > (vanEck n).count x → vanEckNextTerm (vanEck n) = x := by {
  intro h_inc
  have h_append : vanEck (n + 1) = vanEck n ++ [vanEckNextTerm (vanEck n)] := rfl
  rw [h_append] at h_inc
  rw [count_append] at h_inc
  by_cases h_eq : vanEckNextTerm (vanEck n) = x
  · exact h_eq
  · have h_count : [vanEckNextTerm (vanEck n)].count x = 0 := count_eq_zero_of_not_mem (by {
      intro h_mem
      cases h_mem with
      | head => exact h_eq rfl
      | tail _ h_nil => cases h_nil
    })
    rw [h_count] at h_inc
    omega
}
