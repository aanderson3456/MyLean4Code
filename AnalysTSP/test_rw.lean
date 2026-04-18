import Mathlib
import AnalysTSP.WeierstrassLimitR2

example (u : ℕ → ℝ) (φ : ℕ → ℕ) (a : ℝ) (n : ℕ) (ε : ℝ)
  (hd : dist ((u ∘ φ) n) a < ε) : abs (a - (u ∘ φ) n) < ε := by
  rw [Real.dist_eq, abs_sub_comm ((u ∘ φ) n) a] at hd
  exact hd
