import VanEck
import Mathlib
import SurjectivityLemmas

lemma vanEck_le_index (k : ℕ) (hk : k > 0) : vanEckNthTerm k ≤ k := by {
  have ha := vanEck_term_is_matchSearch k hk
  have h_le := matchSearch_le (k - 1)
  have hk_sub : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [ha]
  rw [hk_sub] at h_le
  exact h_le
}

/--
The Monkey Bars Collapse (Rung 5 directly):
If the numbers 1 through n never appear, the very first window of length n + 1
must contain an element >= 2n. But the Van Eck sequence can never generate a 
value greater than its own index! Thus, the local growth bound violently 
collides with the absolute bounding envelope of the sequence on the very first window.
-/
lemma missing_numbers_pigeonhole_contradiction (n : ℕ) (hn : n > 0)
  (h_missing : ∀ k, ∀ s, 1 ≤ s → s ≤ n → vanEckNthTerm k ≠ s) : False := by {
  -- Get the local growth bound for the very first window (m = 0)
  have h_growth := missing_numbers_force_local_growth n hn h_missing 0
  rcases h_growth with ⟨k, hk_ge, hk_le, hk_val⟩
  
  -- Since k <= n, and vanEckNthTerm k <= k, we have vanEckNthTerm k <= n.
  -- We must be careful if k = 0.
  by_cases hk0 : k = 0
  · rw [hk0] at hk_val
    have ha0 : vanEckNthTerm 0 = 0 := rfl
    rw [ha0] at hk_val
    have hn_pos : 2 * n > 0 := Nat.mul_pos (by decide) hn
    exact False.elim (Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hn_pos hk_val))
  · have hk_pos : k > 0 := Nat.pos_of_ne_zero hk0
    have h_bound := vanEck_le_index k hk_pos
    have h_le_n : vanEckNthTerm k ≤ n := by
      have hk_le_n : k ≤ n := by
        have h_zero_add : 0 + n = n := Nat.zero_add n
        rw [← h_zero_add]
        exact hk_le
      exact Nat.le_trans h_bound hk_le_n
      
    -- Now we have 2n <= a(k) <= n.
    have h_contra : 2 * n ≤ n := Nat.le_trans hk_val h_le_n
    have h_2n : 2 * n = n + n := Nat.two_mul n
    rw [h_2n] at h_contra
    have h_zero : n ≤ 0 := Nat.le_of_add_le_add_right h_contra
    exact False.elim (Nat.not_lt_of_le h_zero hn)
}
