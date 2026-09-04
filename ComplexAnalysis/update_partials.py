import sys

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

proof_ux = """
  have h_x_u : HasPartialDerivX_C_to_R_eps (fun z => u (z.re, z.im)) ux z := by {
    unfold HasPartialDerivX_C_to_R_eps HasFDerivAt_R2_eps at *
    intro ε hε
    rcases h (ε / 2) (half_pos hε) with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x hx
    
    have h_sub_im : z.im - z.im = 0 := sub_self z.im
    have h_sq_zero : (0 : ℝ)^2 = 0 := by ring
    
    have hdist_eq : euclideanDist (x, z.im) (z.re, z.im) = abs (x - z.re) := by {
      unfold euclideanDist sqDist
      dsimp
      rw [h_sub_im, h_sq_zero, add_zero]
      have h_abs_sq : |x - z.re|^2 = (x - z.re)^2 := sq_abs (x - z.re)
      rw [← h_abs_sq, Real.sqrt_sq (abs_nonneg (x - z.re))]
    }
    
    have hdist_pos : 0 < euclideanDist (x, z.im) (z.re, z.im) := by {
      rw [hdist_eq]
      exact hx.1
    }
    have hdist : euclideanDist (x, z.im) (z.re, z.im) < δ := by {
      rw [hdist_eq]
      exact hx.2
    }
    
    have h_bound := hδ (x, z.im) ⟨hdist_pos, hdist⟩
    dsimp at h_bound
    rw [h_sub_im] at h_bound
    
    have h_mul_zero1 : uy * 0 = 0 := mul_zero uy
    have h_mul_zero2 : vy * 0 = 0 := mul_zero vy
    rw [h_mul_zero1, h_mul_zero2, add_zero, add_zero] at h_bound
    
    have h_norm : abs (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)) ≤ euclideanNorm (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re), v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)) := by {
      unfold euclideanNorm sqNorm
      dsimp
      have h_abs_sq : |u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)|^2 = (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re))^2 := sq_abs _
      rw [← h_abs_sq]
      apply Real.le_sqrt_of_sq_le
      have h_sq_nonneg : 0 ≤ (v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)) ^ 2 := sq_nonneg _
      exact le_add_of_nonneg_right h_sq_nonneg
    }
    
    have h_bound2 := le_trans h_norm h_bound
    rw [hdist_eq] at h_bound2
    
    have h_strict : (ε / 2) * abs (x - z.re) < ε * abs (x - z.re) := by {
      have h_half : ε / 2 < ε := by linarith
      exact mul_lt_mul_of_pos_right h_half hx.1
    }
    
    have h_bound3 : abs (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)) < ε * abs (x - z.re) := lt_of_le_of_lt h_bound2 h_strict
    
    dsimp
    have h_im_re : (z.im : ℂ).re = z.im := Complex.ofReal_re z.im
    have h_im_im : (z.im : ℂ).im = 0 := Complex.ofReal_im z.im
    have h_re : ((z.im : ℂ) * I).re = 0 := by simp
    have h_im : ((z.im : ℂ) * I).im = z.im := by simp
    
    rw [h_re, h_im]
    have h_x_0 : x + 0 = x := add_zero x
    have h_0_im : 0 + z.im = z.im := zero_add z.im
    rw [h_x_0, h_0_im]
    
    have h_div : |(u (x, z.im) - u (z.re, z.im)) / (x - z.re) - ux| = |(u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)) / (x - z.re)| := by {
      congr 1
      have hx_ne : x - z.re ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp (abs_pos.mp hx.1))
      calc (u (x, z.im) - u (z.re, z.im)) / (x - z.re) - ux = (u (x, z.im) - u (z.re, z.im)) / (x - z.re) - (ux * (x - z.re)) / (x - z.re) := by rw [mul_div_cancel_right₀ _ hx_ne]
        _ = (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)) / (x - z.re) := by ring
    }
    
    rw [h_div, abs_div]
    exact (div_lt_iff₀ hx.1).mpr h_bound3
  }
"""

proof_uy = """
  have h_y_u : HasPartialDerivY_C_to_R_eps (fun z => u (z.re, z.im)) uy z := by {
    unfold HasPartialDerivY_C_to_R_eps HasFDerivAt_R2_eps at *
    intro ε hε
    rcases h (ε / 2) (half_pos hε) with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro y hy
    
    have h_sub_re : z.re - z.re = 0 := sub_self z.re
    have h_sq_zero : (0 : ℝ)^2 = 0 := by ring
    
    have hdist_eq : euclideanDist (z.re, y) (z.re, z.im) = abs (y - z.im) := by {
      unfold euclideanDist sqDist
      dsimp
      rw [h_sub_re, h_sq_zero, zero_add]
      have h_abs_sq : |y - z.im|^2 = (y - z.im)^2 := sq_abs (y - z.im)
      rw [← h_abs_sq, Real.sqrt_sq (abs_nonneg (y - z.im))]
    }
    
    have hdist_pos : 0 < euclideanDist (z.re, y) (z.re, z.im) := by {
      rw [hdist_eq]
      exact hy.1
    }
    have hdist : euclideanDist (z.re, y) (z.re, z.im) < δ := by {
      rw [hdist_eq]
      exact hy.2
    }
    
    have h_bound := hδ (z.re, y) ⟨hdist_pos, hdist⟩
    dsimp at h_bound
    rw [h_sub_re] at h_bound
    
    have h_mul_zero1 : ux * 0 = 0 := mul_zero ux
    have h_mul_zero2 : vx * 0 = 0 := mul_zero vx
    rw [h_mul_zero1, h_mul_zero2, zero_add, zero_add] at h_bound
    
    have h_norm : abs (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)) ≤ euclideanNorm (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im), v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)) := by {
      unfold euclideanNorm sqNorm
      dsimp
      have h_abs_sq : |u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)|^2 = (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im))^2 := sq_abs _
      rw [← h_abs_sq]
      apply Real.le_sqrt_of_sq_le
      have h_sq_nonneg : 0 ≤ (v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)) ^ 2 := sq_nonneg _
      exact le_add_of_nonneg_right h_sq_nonneg
    }
    
    have h_bound2 := le_trans h_norm h_bound
    rw [hdist_eq] at h_bound2
    
    have h_strict : (ε / 2) * abs (y - z.im) < ε * abs (y - z.im) := by {
      have h_half : ε / 2 < ε := by linarith
      exact mul_lt_mul_of_pos_right h_half hy.1
    }
    
    have h_bound3 : abs (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)) < ε * abs (y - z.im) := lt_of_le_of_lt h_bound2 h_strict
    
    dsimp
    have h_im_re : (y : ℂ).re = y := Complex.ofReal_re y
    have h_im_im : (y : ℂ).im = 0 := Complex.ofReal_im y
    have h_re : ((y : ℂ) * I).re = 0 := by simp
    have h_im : ((y : ℂ) * I).im = y := by simp
    
    rw [h_re, h_im]
    have h_x_0 : z.re + 0 = z.re := add_zero z.re
    have h_0_im : 0 + y = y := zero_add y
    rw [h_x_0, h_0_im]
    
    have h_div : |(u (z.re, y) - u (z.re, z.im)) / (y - z.im) - uy| = |(u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)) / (y - z.im)| := by {
      congr 1
      have hy_ne : y - z.im ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp (abs_pos.mp hy.1))
      calc (u (z.re, y) - u (z.re, z.im)) / (y - z.im) - uy = (u (z.re, y) - u (z.re, z.im)) / (y - z.im) - (uy * (y - z.im)) / (y - z.im) := by rw [mul_div_cancel_right₀ _ hy_ne]
        _ = (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)) / (y - z.im) := by ring
    }
    
    rw [h_div, abs_div]
    exact (div_lt_iff₀ hy.1).mpr h_bound3
  }
"""

proof_vx = """
  have h_x_v : HasPartialDerivX_C_to_R_eps (fun z => v (z.re, z.im)) vx z := by {
    unfold HasPartialDerivX_C_to_R_eps HasFDerivAt_R2_eps at *
    intro ε hε
    rcases h (ε / 2) (half_pos hε) with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x hx
    
    have h_sub_im : z.im - z.im = 0 := sub_self z.im
    have h_sq_zero : (0 : ℝ)^2 = 0 := by ring
    
    have hdist_eq : euclideanDist (x, z.im) (z.re, z.im) = abs (x - z.re) := by {
      unfold euclideanDist sqDist
      dsimp
      rw [h_sub_im, h_sq_zero, add_zero]
      have h_abs_sq : |x - z.re|^2 = (x - z.re)^2 := sq_abs (x - z.re)
      rw [← h_abs_sq, Real.sqrt_sq (abs_nonneg (x - z.re))]
    }
    
    have hdist_pos : 0 < euclideanDist (x, z.im) (z.re, z.im) := by {
      rw [hdist_eq]
      exact hx.1
    }
    have hdist : euclideanDist (x, z.im) (z.re, z.im) < δ := by {
      rw [hdist_eq]
      exact hx.2
    }
    
    have h_bound := hδ (x, z.im) ⟨hdist_pos, hdist⟩
    dsimp at h_bound
    rw [h_sub_im] at h_bound
    
    have h_mul_zero1 : uy * 0 = 0 := mul_zero uy
    have h_mul_zero2 : vy * 0 = 0 := mul_zero vy
    rw [h_mul_zero1, h_mul_zero2, add_zero, add_zero] at h_bound
    
    have h_norm : abs (v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)) ≤ euclideanNorm (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re), v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)) := by {
      unfold euclideanNorm sqNorm
      dsimp
      have h_abs_sq : |v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)|^2 = (v (x, z.im) - v (z.re, z.im) - vx * (x - z.re))^2 := sq_abs _
      rw [← h_abs_sq]
      apply Real.le_sqrt_of_sq_le
      have h_sq_nonneg : 0 ≤ (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)) ^ 2 := sq_nonneg _
      have h_comm : (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)) ^ 2 + (v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)) ^ 2 = (v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)) ^ 2 + (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)) ^ 2 := add_comm _ _
      rw [h_comm]
      exact le_add_of_nonneg_right h_sq_nonneg
    }
    
    have h_bound2 := le_trans h_norm h_bound
    rw [hdist_eq] at h_bound2
    
    have h_strict : (ε / 2) * abs (x - z.re) < ε * abs (x - z.re) := by {
      have h_half : ε / 2 < ε := by linarith
      exact mul_lt_mul_of_pos_right h_half hx.1
    }
    
    have h_bound3 : abs (v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)) < ε * abs (x - z.re) := lt_of_le_of_lt h_bound2 h_strict
    
    dsimp
    have h_im_re : (z.im : ℂ).re = z.im := Complex.ofReal_re z.im
    have h_im_im : (z.im : ℂ).im = 0 := Complex.ofReal_im z.im
    have h_re : ((z.im : ℂ) * I).re = 0 := by simp
    have h_im : ((z.im : ℂ) * I).im = z.im := by simp
    
    rw [h_re, h_im]
    have h_x_0 : x + 0 = x := add_zero x
    have h_0_im : 0 + z.im = z.im := zero_add z.im
    rw [h_x_0, h_0_im]
    
    have h_div : |(v (x, z.im) - v (z.re, z.im)) / (x - z.re) - vx| = |(v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)) / (x - z.re)| := by {
      congr 1
      have hx_ne : x - z.re ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp (abs_pos.mp hx.1))
      calc (v (x, z.im) - v (z.re, z.im)) / (x - z.re) - vx = (v (x, z.im) - v (z.re, z.im)) / (x - z.re) - (vx * (x - z.re)) / (x - z.re) := by rw [mul_div_cancel_right₀ _ hx_ne]
        _ = (v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)) / (x - z.re) := by ring
    }
    
    rw [h_div, abs_div]
    exact (div_lt_iff₀ hx.1).mpr h_bound3
  }
"""

proof_vy = """
  have h_y_v : HasPartialDerivY_C_to_R_eps (fun z => v (z.re, z.im)) vy z := by {
    unfold HasPartialDerivY_C_to_R_eps HasFDerivAt_R2_eps at *
    intro ε hε
    rcases h (ε / 2) (half_pos hε) with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro y hy
    
    have h_sub_re : z.re - z.re = 0 := sub_self z.re
    have h_sq_zero : (0 : ℝ)^2 = 0 := by ring
    
    have hdist_eq : euclideanDist (z.re, y) (z.re, z.im) = abs (y - z.im) := by {
      unfold euclideanDist sqDist
      dsimp
      rw [h_sub_re, h_sq_zero, zero_add]
      have h_abs_sq : |y - z.im|^2 = (y - z.im)^2 := sq_abs (y - z.im)
      rw [← h_abs_sq, Real.sqrt_sq (abs_nonneg (y - z.im))]
    }
    
    have hdist_pos : 0 < euclideanDist (z.re, y) (z.re, z.im) := by {
      rw [hdist_eq]
      exact hy.1
    }
    have hdist : euclideanDist (z.re, y) (z.re, z.im) < δ := by {
      rw [hdist_eq]
      exact hy.2
    }
    
    have h_bound := hδ (z.re, y) ⟨hdist_pos, hdist⟩
    dsimp at h_bound
    rw [h_sub_re] at h_bound
    
    have h_mul_zero1 : ux * 0 = 0 := mul_zero ux
    have h_mul_zero2 : vx * 0 = 0 := mul_zero vx
    rw [h_mul_zero1, h_mul_zero2, zero_add, zero_add] at h_bound
    
    have h_norm : abs (v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)) ≤ euclideanNorm (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im), v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)) := by {
      unfold euclideanNorm sqNorm
      dsimp
      have h_abs_sq : |v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)|^2 = (v (z.re, y) - v (z.re, z.im) - vy * (y - z.im))^2 := sq_abs _
      rw [← h_abs_sq]
      apply Real.le_sqrt_of_sq_le
      have h_sq_nonneg : 0 ≤ (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)) ^ 2 := sq_nonneg _
      have h_comm : (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)) ^ 2 + (v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)) ^ 2 = (v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)) ^ 2 + (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)) ^ 2 := add_comm _ _
      rw [h_comm]
      exact le_add_of_nonneg_right h_sq_nonneg
    }
    
    have h_bound2 := le_trans h_norm h_bound
    rw [hdist_eq] at h_bound2
    
    have h_strict : (ε / 2) * abs (y - z.im) < ε * abs (y - z.im) := by {
      have h_half : ε / 2 < ε := by linarith
      exact mul_lt_mul_of_pos_right h_half hy.1
    }
    
    have h_bound3 : abs (v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)) < ε * abs (y - z.im) := lt_of_le_of_lt h_bound2 h_strict
    
    dsimp
    have h_im_re : (y : ℂ).re = y := Complex.ofReal_re y
    have h_im_im : (y : ℂ).im = 0 := Complex.ofReal_im y
    have h_re : ((y : ℂ) * I).re = 0 := by simp
    have h_im : ((y : ℂ) * I).im = y := by simp
    
    rw [h_re, h_im]
    have h_x_0 : z.re + 0 = z.re := add_zero z.re
    have h_0_im : 0 + y = y := zero_add y
    rw [h_x_0, h_0_im]
    
    have h_div : |(v (z.re, y) - v (z.re, z.im)) / (y - z.im) - vy| = |(v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)) / (y - z.im)| := by {
      congr 1
      have hy_ne : y - z.im ≠ 0 := sub_ne_zero.mpr (sub_ne_zero.mp (abs_pos.mp hy.1))
      calc (v (z.re, y) - v (z.re, z.im)) / (y - z.im) - vy = (v (z.re, y) - v (z.re, z.im)) / (y - z.im) - (vy * (y - z.im)) / (y - z.im) := by rw [mul_div_cancel_right₀ _ hy_ne]
        _ = (v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)) / (y - z.im) := by ring
    }
    
    rw [h_div, abs_div]
    exact (div_lt_iff₀ hy.1).mpr h_bound3
  }
"""

proof_end = """
  exact ⟨h_x_u, h_y_u, h_x_v, h_y_v⟩
}
"""

target = """lemma partials_of_fderiv_R2 {u v : ℝ × ℝ → ℝ} {ux uy vx vy : ℝ} {z : ℂ}
    (h : HasFDerivAt_R2_eps u v ux uy vx vy (z.re, z.im)) :
    HasPartialDerivX_C_to_R_eps (fun z => u (z.re, z.im)) ux z ∧
    HasPartialDerivY_C_to_R_eps (fun z => u (z.re, z.im)) uy z ∧
    HasPartialDerivX_C_to_R_eps (fun z => v (z.re, z.im)) vx z ∧
    HasPartialDerivY_C_to_R_eps (fun z => v (z.re, z.im)) vy z := by {
  sorry
}"""

replacement = target.replace("sorry\n}", proof_ux + proof_uy + proof_vx + proof_vy + proof_end)
content = content.replace(target, replacement)

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
