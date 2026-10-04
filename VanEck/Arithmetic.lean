/-
Copyright (c) 2026 Austin Anderson
SPDX-License-Identifier: MIT

This file records the elementary arithmetical form of the standard,
zero-seeded Van Eck sequence.  It deliberately contains no assertion about
provability or independence from a formal theory.
-/
import VanEck

/--
`VanEckTerm n` is the directly executable zero-seeded Van Eck evaluator.

It uses `List.getD` only to expose an ordinary total arithmetic function; the
theorem below identifies it with the project's established `vanEckNthTerm`.
-/
def VanEckTerm (n : ℕ) : ℕ := (vanEck n).getD n 0

lemma listNth_eq_getD (L : List ℕ) (n : ℕ) : listNth L n = L.getD n 0 := by {
  induction L generalizing n with
  | nil => rfl
  | cons x xs ih =>
    cases n with
    | zero => rfl
    | succ n => exact ih n
}

/-- The executable evaluator agrees with the existing sequence definition. -/
theorem VanEckTerm_eq_vanEckNthTerm (n : ℕ) : VanEckTerm n = vanEckNthTerm n := by {
  unfold VanEckTerm vanEckNthTerm
  exact (listNth_eq_getD (vanEck n) n).symm
}

/-- A predicate has arithmetical `Π⁰₂` form when it is `∀ n, ∃ m` over a decidable matrix. -/
def HasPi2Form (P : Prop) : Prop :=
  ∃ R : ℕ → ℕ → Prop,
    (∀ n m, R n m ∨ ¬ R n m) ∧ (P ↔ ∀ n, ∃ m, R n m)

/-- The concrete infinite-twos assertion for the standard zero seed. -/
def InfiniteTwosStatement : Prop :=
  ∀ N, ∃ m > N, VanEckTerm m = 2

/-- `InfiniteTwosStatement` is a `Π⁰₂` arithmetic statement. -/
theorem infiniteTwosStatement_hasPi2Form : HasPi2Form InfiniteTwosStatement := by {
  refine ⟨fun N m => N < m ∧ VanEckTerm m = 2, ?_, Iff.rfl⟩
  intro N m
  by_cases h_lt : N < m
  · by_cases h_two : VanEckTerm m = 2
    · exact Or.inl ⟨h_lt, h_two⟩
    · exact Or.inr (fun h => h_two h.right)
  · exact Or.inr (fun h => h_lt h.left)
}

/-- The arithmetic statement is extensionally the project's original theorem target. -/
theorem infiniteTwosStatement_iff :
    InfiniteTwosStatement ↔ ∀ N, ∃ m > N, vanEckNthTerm m = 2 := by {
  constructor
  · intro h N
    rcases h N with ⟨m, hm_gt, hm_two⟩
    exact ⟨m, hm_gt, by rw [← VanEckTerm_eq_vanEckNthTerm]; exact hm_two⟩
  · intro h N
    rcases h N with ⟨m, hm_gt, hm_two⟩
    exact ⟨m, hm_gt, by rw [VanEckTerm_eq_vanEckNthTerm]; exact hm_two⟩
}
