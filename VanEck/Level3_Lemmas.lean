import VanEck
import ImpossiblePatterns
import LimSup
import Mathlib

/--
If an element `x` only appears finitely many times in the Van Eck sequence,
there must exist some maximum index `Z` such that for all `k > Z`, `vanEckNthTerm k ≠ x`.
-/
lemma finite_occurrences_implies_last_index (x : ℕ) (h_finite : ∃ Z, ∀ k > Z, vanEckNthTerm k ≠ x) :
    ∃ Z, vanEckNthTerm Z = x ∧ ∀ k > Z, vanEckNthTerm k ≠ x := by {
  sorry
}

/--
If `x` never appears after index `Z`, then no element after `Z+1` can have its previous occurrence exactly `x` steps ago.
-/
lemma never_appears_again_implies_no_gap_x (x Z : ℕ) (hx : ∀ k > Z, vanEckNthTerm k ≠ x) :
    ∀ k > Z + 1, listNth (vanEck (k - 1)) (k - 1) ≠ listNth (vanEck (k - 1)) (k - 1 - x) := by {
  sorry
}

/--
If 1 only appears finitely many times, there is a point after which no two consecutive elements are equal.
-/
lemma finite_ones_implies_no_consecutive_equal (h_finite : ∃ Z, ∀ k > Z, vanEckNthTerm k ≠ 1) :
    ∃ Z, ∀ k > Z, vanEckNthTerm k ≠ vanEckNthTerm (k + 1) := by {
  sorry
}
