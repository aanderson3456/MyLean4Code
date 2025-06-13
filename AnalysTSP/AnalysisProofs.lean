import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean


theorem ZeroPlusNisN (n : ℕ) : 0 + n = n := by {
  induction' n with d hd
  rfl
  rw [← hd]
  rw [Nat.add_assoc]
  simp
}

#print ZeroPlusNisN

open Nat

theorem TwoPlusTwoNeqFive : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by {

}

def LowerBoundReal (r : ℝ) (A : Set ℝ) : Prop :=
  (∀ a ∈ A, a ≥ r)

def GreatestLowerBoundReal (r: ℝ) (A : Set ℝ) : Prop :=
  (LowerBoundReal r A) ∧ (∀ s : ℝ, (LowerBoundReal s A) → r ≥ s)

def reciprocalsOfNaturalNumbers : Set ℝ :=
  { r : ℝ | ∃ n : ℕ, n ≠ 0 ∧ r = 1 / n }

lemma Lemma1 : GreatestLowerBoundReal 0 reciprocalsOfNaturalNumbers := by {
  unfold GreatestLowerBoundReal
  constructor
  unfold LowerBoundReal
  unfold reciprocalsOfNaturalNumbers
  intro a
  intro ha
  cases' ha with n hn
  cases' hn with hn_ne_zero hr_eq_inv_n
  rw [hr_eq_inv_n]
  apply div_nonneg
  exact zero_le_one' ℝ
  exact Nat.cast_nonneg' n
  intro s
  unfold LowerBoundReal reciprocalsOfNaturalNumbers
  intro ha
  by_contra h_contra
  simp at h_contra

-- apply Real.instArchimedean



}
