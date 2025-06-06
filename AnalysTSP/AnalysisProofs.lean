import Mathlib.Data.Nat.Basic
import Mathlib.Tactic.Ring.Basic
import Mathlib.Data.Real.Basic


theorem ZeroPlusNisN (n : ℕ) : 0 + n = n := by {
  induction' n with d hd
  rfl
  rw [← hd]
  rw [Nat.add_assoc]
  simp
}

#print ZeroPlusNisN

def LowerBoundReal (r : ℝ) (A : Set ℝ) : Prop :=
  (∀ a ∈ A, a ≥ r)

def GreatestLowerBoundReal (r: ℝ) (A : Set ℝ) : Prop :=
  (LowerBoundReal r A) ∧ (∀ s : ℝ, (LowerBoundReal s A) → r ≥ s)

def reciprocalsOfNaturalNumbers : Set ℝ :=
  { r : ℝ | ∃ n : ℕ, n ≠ 0 ∧ r = 1 / n }

lemma Lemma1 : GreatestLowerBoundReal 0 reciprocalsOfNaturalNumbers := by {
  unfold GreatestLowerBoundReal
  constructor
  sorry
}
