import VanEck
import ImpossiblePatterns
import LimSup
import Mathlib

lemma vanEck_surjective_zero : ∃ m, vanEckNthTerm m = 0 := by {
  use 0
  exact vanEck_head_eq_zero 0
}

lemma vanEck_surjective_one : ∃ m, vanEckNthTerm m = 1 := by {
  use 2
  rfl
}

lemma vanEck_surjective_two : ∃ m, vanEckNthTerm m = 2 := by {
  use 4
  rfl
}
