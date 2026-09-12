import Mathlib

def sqNorm (x : ℝ × ℝ) : ℝ := x.1^2 + x.2^2
noncomputable def euclideanNorm (x : ℝ × ℝ) : ℝ := Real.sqrt (sqNorm x)
noncomputable def sqDist (x y : ℝ × ℝ) : ℝ := sqNorm (x.1 - y.1, x.2 - y.2)
noncomputable def euclideanDist (x y : ℝ × ℝ) : ℝ := Real.sqrt (sqDist x y)

def LimitR2toR (f : ℝ × ℝ → ℝ) (a : ℝ × ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ × ℝ, 0 < euclideanDist x a ∧ euclideanDist x a < δ → |f x - L| < ε

def HasFDerivAt_R2_eps (u v : ℝ × ℝ → ℝ) (ux₀ uy₀ vx₀ vy₀ : ℝ) (a : ℝ × ℝ) : Prop :=
  LimitR2toR (fun h => 
    euclideanNorm (
      (u (a.1 + h.1, a.2 + h.2) - u a) - (ux₀ * h.1 + uy₀ * h.2), 
      (v (a.1 + h.1, a.2 + h.2) - v a) - (vx₀ * h.1 + vy₀ * h.2)
    ) / euclideanNorm h
  ) (0, 0) 0

lemma HasFDerivAt_R2_eps_iff (u v : ℝ × ℝ → ℝ) (ux₀ uy₀ vx₀ vy₀ : ℝ) (a : ℝ × ℝ) :
  HasFDerivAt_R2_eps u v ux₀ uy₀ vx₀ vy₀ a ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ × ℝ,
    0 < euclideanDist x a ∧ euclideanDist x a < δ →
    euclideanNorm (u x - u a - (ux₀ * (x.1 - a.1) + uy₀ * (x.2 - a.2)), 
                   v x - v a - (vx₀ * (x.1 - a.1) + vy₀ * (x.2 - a.2))) < ε * euclideanDist x a := by {
  sorry
}
