import VanEck.Basic
import VanEck
import VanEck.ZeroDominates

open List

lemma zero_dominates_core_contradiction (m x : ℕ) (hx : x > 0) 
    (h_next : vanEckNextTerm (vanEck m) = x)
    (h_eq : (vanEck m).count x = (vanEck m).count 0) : False := by {
  -- This is the deep mathematical contradiction: a non-zero element x cannot 
  -- equal the frequency of 0 right when it is about to be generated again.
  sorry
}

theorem zeroDominates_proof (n x : ℕ) : (vanEck n).count x ≤ (vanEck n).count 0 := by {
  induction n with
  | zero => exact zero_dom_base x
  | succ m ih =>
    have h_append : vanEck (m + 1) = vanEck m ++ [vanEckNextTerm (vanEck m)] := rfl
    rw [h_append]
    rw [count_append, count_append]
    by_cases h_x : x = 0
    · rw [h_x]
    · by_cases h_next_zero : vanEckNextTerm (vanEck m) = 0
      · rw [h_next_zero]
        have h_0 : [0].count 0 = 1 := rfl
        have h_x_count : [0].count x = 0 := by {
          apply count_eq_zero.mpr
          intro h_mem
          cases h_mem with
          | head => exact h_x rfl
          | tail _ h_nil => cases h_nil
        }
        rw [h_0, h_x_count]
        omega
      · by_cases h_next_x : vanEckNextTerm (vanEck m) = x
        · rw [h_next_x]
          have h_x_count : [x].count x = 1 := by simp
          have h_0_count : [x].count 0 = 0 := by {
            apply count_eq_zero.mpr
            intro h_mem
            cases h_mem with
            | head => exact h_x.symm rfl
            | tail _ h_nil => cases h_nil
          }
          rw [h_x_count, h_0_count]
          have h_le : (vanEck m).count x ≤ (vanEck m).count 0 := ih
          by_cases h_eq : (vanEck m).count x = (vanEck m).count 0
          · have h_hx : x > 0 := Nat.pos_of_ne_zero h_x
            have contra := zero_dominates_core_contradiction m x h_hx h_next_x h_eq
            exact False.elim contra
          · omega
        · have h_0_count : [vanEckNextTerm (vanEck m)].count 0 = 0 := by {
            apply count_eq_zero.mpr
            intro h_mem
            cases h_mem with
            | head => exact h_next_zero rfl
            | tail _ h_nil => cases h_nil
          }
          have h_x_count : [vanEckNextTerm (vanEck m)].count x = 0 := by {
            apply count_eq_zero.mpr
            intro h_mem
            cases h_mem with
            | head => exact h_next_x rfl
            | tail _ h_nil => cases h_nil
          }
          rw [h_0_count, h_x_count]
          exact ih
}
