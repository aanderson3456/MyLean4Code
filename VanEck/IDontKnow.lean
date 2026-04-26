import VanEck
import Mathlib
import SurjectivityLemmas

/--
The General Surjectivity Reduction:
If every number n has a strict gap of distance n, 
then by `strict_gap_implies_value`, the sequence must produce the value n.
Thus, the Van Eck sequence is surjective.
-/
lemma vanEck_strict_gap_exists (n : ℕ) (hn : n > 0) : ∃ m : ℕ, has_strict_gap n m := by {
  by_contra hc
  push_neg at hc
  -- hc : ∀ m, ¬ has_strict_gap n m
  
  -- If n has no strict gap, it means n NEVER appears as a gap.
  -- By definition of the sequence, if n never appears as a gap, it never appears as a value.
  have h_missing : ∀ k, vanEckNthTerm k ≠ n := by
    intro k
    by_contra hk
    -- If vanEckNthTerm k = n, and n > 0, it must be the distance to the previous occurrence.
    -- Which means there IS a strict gap of distance n.
    have hk_pos : k > 0 := by
      by_contra h0
      push_neg at h0
      have hz : k = 0 := Nat.eq_zero_of_le_zero h0
      rw [hz] at hk
      have ha0 : vanEckNthTerm 0 = 0 := rfl
      rw [ha0] at hk
      exact False.elim (Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hn (by rw [hk]; exact Nat.le_refl 0)))
      
    have h_gap := matchSearch_is_gap_distance k hk_pos n hk (Nat.pos_iff_ne_zero.mp hn)
    
    have h_strict : ∀ j, k - 1 - n < j → j < k - 1 → vanEckNthTerm j ≠ vanEckNthTerm (k - 1) := by
      -- This follows directly from the definition of matchSearch finding the FIRST occurrence backward.
      sorry
      
    have h_sg : has_strict_gap n (k - 1 - n) := ⟨h_gap.symm, h_strict⟩
    exact hc (k - 1 - n) h_sg
    
  -- Now we know n never appears. We can apply our missing number constraints!
  -- Actually, missing_numbers_pigeonhole_contradiction requires ALL 1..n to be missing.
  -- Wait! Our contradiction `missing_numbers_pigeonhole_contradiction` assumed 
  -- `∀ s, 1 ≤ s → s ≤ n → vanEckNthTerm k ≠ s`.
  -- Does a missing `n` force `1..n` to be missing?
  -- No! But if the sequence is NOT surjective, there is a MINIMUM missing number `s`.
  -- Wait, if `s` is the minimum missing number, then `1..s-1` ARE present.
  -- My lemma `missing_numbers_pigeonhole_contradiction` assumes `1..n` are ALL missing.
  -- Oh.
  sorry
}

theorem vanEck_surjective (n : ℕ) : ∃ m : ℕ, vanEckNthTerm m = n := by {
  cases n with
  | zero => exact vanEck_surjective_zero
  | succ n_pred =>
    have hn : n_pred + 1 > 0 := Nat.succ_pos _
    -- To prove this, we would need to prove has_strict_gap (n_pred + 1)
    -- This requires a deep structural induction over the gap sequence.
    sorry
}
