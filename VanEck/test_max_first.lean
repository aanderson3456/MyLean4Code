import VanEck.InfiniteTwos

lemma exists_max_first_occurrence (B : ℕ) :
  ∃ N, ∀ x ≤ B, (∃ k, vanEckNthTerm k = x) → ∃ k ≤ N, vanEckNthTerm k = x := by {
  induction B with
  | zero =>
    by_cases h : ∃ k, vanEckNthTerm k = 0
    · rcases h with ⟨k, hk⟩
      exact ⟨k, fun x hx h_ex => by
        have h0 : x = 0 := Nat.eq_zero_of_le_zero hx
        rw [h0]
        exact ⟨k, Nat.le_refl k, hk⟩
      ⟩
    · exact ⟨0, fun x hx h_ex => by
        have h0 : x = 0 := Nat.eq_zero_of_le_zero hx
        rw [h0] at h_ex
        contradiction
      ⟩
  | succ B ih =>
    rcases ih with ⟨N_B, hN_B⟩
    by_cases h : ∃ k, vanEckNthTerm k = B + 1
    · rcases h with ⟨k, hk⟩
      exact ⟨max N_B k, fun x hx h_ex => by
        have h_or := (splitting_le x (B + 1)).mp hx
        rcases h_or with h_lt | h_eq
        · have h_le := Nat.le_of_lt_succ h_lt
          rcases hN_B x h_le h_ex with ⟨k2, hk2_le, hk2_eq⟩
          exact ⟨k2, Nat.le_trans hk2_le (Nat.le_max_left N_B k), hk2_eq⟩
        · rw [h_eq]
          exact ⟨k, Nat.le_max_right N_B k, hk⟩
      ⟩
    · exact ⟨N_B, fun x hx h_ex => by
        have h_or := (splitting_le x (B + 1)).mp hx
        rcases h_or with h_lt | h_eq
        · have h_le := Nat.le_of_lt_succ h_lt
          exact hN_B x h_le h_ex
        · rw [h_eq] at h_ex
          contradiction
      ⟩
}
