#!/bin/bash
cat << 'INNER_EOF' >> R2.lean

lemma polar_partial_r_is_deriv {u : ℝ × ℝ → ℝ} {ux₀ uy₀ : ℝ} {r₀ θ₀ : ℝ}
    (h_diff : HasFDerivAt_R2_eps u (fun _ => 0) ux₀ uy₀ 0 0 (r₀ * Real.cos θ₀, r₀ * Real.sin θ₀)) :
    HasDerivAt_RtoR2_eps (fun r => (u (r * Real.cos θ₀, r * Real.sin θ₀), 0)) 
      (ux₀ * Real.cos θ₀ + uy₀ * Real.sin θ₀, 0) r₀ := by {
  have hγ_diff : HasDerivAt_RtoR2_eps (fun r => (r * Real.cos θ₀, r * Real.sin θ₀)) (Real.cos θ₀, Real.sin θ₀) r₀ := by {
    unfold HasDerivAt_RtoR2_eps
    intro ε hε
    use 1, by norm_num
    intro t ht
    have hd : euclideanDist (t * Real.cos θ₀, t * Real.sin θ₀) ((r₀ * Real.cos θ₀, r₀ * Real.sin θ₀) + (Real.cos θ₀ * (t - r₀), Real.sin θ₀ * (t - r₀))) = 0 := by {
      unfold euclideanDist sqDist
      have h1 : (t * Real.cos θ₀ - ((r₀ * Real.cos θ₀, r₀ * Real.sin θ₀) + (Real.cos θ₀ * (t - r₀), Real.sin θ₀ * (t - r₀))).1) = 0 := by {
        change t * Real.cos θ₀ - (r₀ * Real.cos θ₀ + Real.cos θ₀ * (t - r₀)) = 0
        ring
      }
      have h2 : (t * Real.sin θ₀ - ((r₀ * Real.cos θ₀, r₀ * Real.sin θ₀) + (Real.cos θ₀ * (t - r₀), Real.sin θ₀ * (t - r₀))).2) = 0 := by {
        change t * Real.sin θ₀ - (r₀ * Real.sin θ₀ + Real.sin θ₀ * (t - r₀)) = 0
        ring
      }
      rw [h1, h2]
      norm_num
    }
    rw [hd]
    exact mul_pos hε ht.1
  }
  have h_chain := chain_rule_R2 h_diff (fun r => (r * Real.cos θ₀, r * Real.sin θ₀)) r₀ rfl (Real.cos θ₀, Real.sin θ₀) hγ_diff
  have h_eq : (ux₀ * (Real.cos θ₀, Real.sin θ₀).1 + uy₀ * (Real.cos θ₀, Real.sin θ₀).2,
      0 * (Real.cos θ₀, Real.sin θ₀).1 + 0 * (Real.cos θ₀, Real.sin θ₀).2) = (ux₀ * Real.cos θ₀ + uy₀ * Real.sin θ₀, 0) := by {
    change (ux₀ * Real.cos θ₀ + uy₀ * Real.sin θ₀, 0 * Real.cos θ₀ + 0 * Real.sin θ₀) = (ux₀ * Real.cos θ₀ + uy₀ * Real.sin θ₀, 0)
    have hz : 0 * Real.cos θ₀ + 0 * Real.sin θ₀ = 0 := by ring
    rw [hz]
  }
  rw [h_eq] at h_chain
  exact h_chain
}

lemma polar_partial_theta_is_deriv {u : ℝ × ℝ → ℝ} {ux₀ uy₀ : ℝ} {r₀ θ₀ : ℝ}
    (h_diff : HasFDerivAt_R2_eps u (fun _ => 0) ux₀ uy₀ 0 0 (r₀ * Real.cos θ₀, r₀ * Real.sin θ₀)) :
    HasDerivAt_RtoR2_eps (fun θ => (u (r₀ * Real.cos θ, r₀ * Real.sin θ), 0)) 
      (-ux₀ * r₀ * Real.sin θ₀ + uy₀ * r₀ * Real.cos θ₀, 0) θ₀ := by {
  have hγ_diff : HasDerivAt_RtoR2_eps (fun θ => (r₀ * Real.cos θ, r₀ * Real.sin θ)) (-r₀ * Real.sin θ₀, r₀ * Real.cos θ₀) θ₀ := by {
    sorry -- Requires taking limit of cos and sin
  }
  have h_chain := chain_rule_R2 h_diff (fun θ => (r₀ * Real.cos θ, r₀ * Real.sin θ)) θ₀ rfl (-r₀ * Real.sin θ₀, r₀ * Real.cos θ₀) hγ_diff
  have h_eq : (ux₀ * (-r₀ * Real.sin θ₀, r₀ * Real.cos θ₀).1 + uy₀ * (-r₀ * Real.sin θ₀, r₀ * Real.cos θ₀).2,
      0 * (-r₀ * Real.sin θ₀, r₀ * Real.cos θ₀).1 + 0 * (-r₀ * Real.sin θ₀, r₀ * Real.cos θ₀).2) = (-ux₀ * r₀ * Real.sin θ₀ + uy₀ * r₀ * Real.cos θ₀, 0) := by {
    change (ux₀ * (-r₀ * Real.sin θ₀) + uy₀ * (r₀ * Real.cos θ₀), 0 * (-r₀ * Real.sin θ₀) + 0 * (r₀ * Real.cos θ₀)) = (-ux₀ * r₀ * Real.sin θ₀ + uy₀ * r₀ * Real.cos θ₀, 0)
    have hz : 0 * (-r₀ * Real.sin θ₀) + 0 * (r₀ * Real.cos θ₀) = 0 := by ring
    have h1 : ux₀ * (-r₀ * Real.sin θ₀) + uy₀ * (r₀ * Real.cos θ₀) = -ux₀ * r₀ * Real.sin θ₀ + uy₀ * r₀ * Real.cos θ₀ := by ring
    rw [hz, h1]
  }
  rw [h_eq] at h_chain
  exact h_chain
}
INNER_EOF
