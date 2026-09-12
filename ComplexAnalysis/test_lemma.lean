import Mathlib

def sqNorm (x : ℝ × ℝ) : ℝ := x.1^2 + x.2^2
noncomputable def euclideanNorm (x : ℝ × ℝ) : ℝ := Real.sqrt (sqNorm x)
noncomputable def sqDist (x y : ℝ × ℝ) : ℝ := sqNorm (x.1 - y.1, x.2 - y.2)
noncomputable def euclideanDist (x y : ℝ × ℝ) : ℝ := Real.sqrt (sqDist x y)

lemma euclideanNorm_nonneg (x : ℝ × ℝ) : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _

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
  unfold HasFDerivAt_R2_eps LimitR2toR
  apply Iff.intro
  · intro h_lim ε hε
    rcases h_lim ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x hx
    let h := (x.1 - a.1, x.2 - a.2)
    have h_h_dist : euclideanDist h (0,0) = euclideanDist x a := by {
      dsimp [euclideanDist, sqDist, sqNorm, h]
      congr 1
      ring_nf
    }
    have h_norm_h : euclideanNorm h = euclideanDist x a := by {
      dsimp [euclideanNorm, sqNorm, euclideanDist, sqDist, h]
      congr 1
      ring_nf
    }
    have hx_h : 0 < euclideanDist h (0,0) ∧ euclideanDist h (0,0) < δ := by {
      rw [h_h_dist]
      exact hx
    }
    have h_limit := hδ h hx_h
    dsimp only at h_limit
    have h_err_x : a.1 + h.1 = x.1 := by { dsimp [h]; ring }
    have h_err_y : a.2 + h.2 = x.2 := by { dsimp [h]; ring }
    have h_err : euclideanNorm ((u (a.1 + h.1, a.2 + h.2) - u a) - (ux₀ * h.1 + uy₀ * h.2), (v (a.1 + h.1, a.2 + h.2) - v a) - (vx₀ * h.1 + vy₀ * h.2)) = euclideanNorm (u x - u a - (ux₀ * (x.1 - a.1) + uy₀ * (x.2 - a.2)), v x - v a - (vx₀ * (x.1 - a.1) + vy₀ * (x.2 - a.2))) := by {
      rw [h_err_x, h_err_y]
    }
    rw [h_err, h_norm_h] at h_limit
    have h_norm_nonneg : 0 ≤ euclideanNorm (u x - u a - (ux₀ * (x.1 - a.1) + uy₀ * (x.2 - a.2)), v x - v a - (vx₀ * (x.1 - a.1) + vy₀ * (x.2 - a.2))) / euclideanDist x a := by {
      have h1 : 0 ≤ euclideanNorm (u x - u a - (ux₀ * (x.1 - a.1) + uy₀ * (x.2 - a.2)), v x - v a - (vx₀ * (x.1 - a.1) + vy₀ * (x.2 - a.2))) := euclideanNorm_nonneg _
      have h2 : 0 < euclideanDist x a := hx.1
      exact div_nonneg h1 (le_of_lt h2)
    }
    rw [sub_zero, abs_of_nonneg h_norm_nonneg] at h_limit
    have h_pos : 0 < euclideanDist x a := hx.1
    exact (div_lt_iff₀ h_pos).mp h_limit
  · intro h_eps ε hε
    rcases h_eps ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro h hh
    let x := (a.1 + h.1, a.2 + h.2)
    have h_x_dist : euclideanDist x a = euclideanDist h (0,0) := by {
      dsimp [euclideanDist, sqDist, sqNorm, x]
      congr 1
      ring_nf
    }
    have h_norm_h : euclideanNorm h = euclideanDist h (0,0) := by {
      dsimp [euclideanNorm, sqNorm, euclideanDist, sqDist, x]
      congr 1
      ring_nf
    }
    have hh_x : 0 < euclideanDist x a ∧ euclideanDist x a < δ := by {
      rw [h_x_dist]
      exact hh
    }
    have h_eps_bound := hδ x hh_x
    have h_err_x : x.1 - a.1 = h.1 := by { dsimp [x]; ring }
    have h_err_y : x.2 - a.2 = h.2 := by { dsimp [x]; ring }
    have h_err : euclideanNorm (u x - u a - (ux₀ * (x.1 - a.1) + uy₀ * (x.2 - a.2)), v x - v a - (vx₀ * (x.1 - a.1) + vy₀ * (x.2 - a.2))) = euclideanNorm ((u (a.1 + h.1, a.2 + h.2) - u a) - (ux₀ * h.1 + uy₀ * h.2), (v (a.1 + h.1, a.2 + h.2) - v a) - (vx₀ * h.1 + vy₀ * h.2)) := by {
      rw [h_err_x, h_err_y]
    }
    rw [h_err, h_x_dist, ← h_norm_h] at h_eps_bound
    have h_pos : 0 < euclideanNorm h := by {
      rw [h_norm_h]
      exact hh.1
    }
    have h_div := (div_lt_iff₀ h_pos).mpr h_eps_bound
    have h_norm_nonneg : 0 ≤ euclideanNorm ((u (a.1 + h.1, a.2 + h.2) - u a) - (ux₀ * h.1 + uy₀ * h.2), (v (a.1 + h.1, a.2 + h.2) - v a) - (vx₀ * h.1 + vy₀ * h.2)) / euclideanNorm h := by {
      have h1 : 0 ≤ euclideanNorm ((u (a.1 + h.1, a.2 + h.2) - u a) - (ux₀ * h.1 + uy₀ * h.2), (v (a.1 + h.1, a.2 + h.2) - v a) - (vx₀ * h.1 + vy₀ * h.2)) := euclideanNorm_nonneg _
      exact div_nonneg h1 (le_of_lt h_pos)
    }
    rw [sub_zero, abs_of_nonneg h_norm_nonneg]
    exact h_div
}
