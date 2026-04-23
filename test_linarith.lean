import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Omega

lemma test_omega (a b : Nat) (h : a ≤ b) : a < b + 1 := by
  linarith
