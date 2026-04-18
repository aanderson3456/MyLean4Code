import Mathlib
example (S : ℕ → Finset ℝ) (h : S 0 = ∅) (y : ℝ) (hy : y ∈ S 0) : False := by
  rw [h] at hy
  simp at hy
