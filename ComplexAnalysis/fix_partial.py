import re

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

old_block = """lemma partial_deriv_unique_x (f : ℂ → ℝ) (c d : ℝ) (z₀ : ℂ) (hc : HasPartialDerivX_C_to_R_eps f c z₀) (hd : HasPartialDerivX_C_to_R_eps f d z₀) : c = d := by {
  sorry
}"""

new_block = """lemma partial_deriv_unique_x (f : ℂ → ℝ) (c d : ℝ) (z₀ : ℂ) (hc : HasPartialDerivX_C_to_R_eps f c z₀) (hd : HasPartialDerivX_C_to_R_eps f d z₀) : c = d := by {
  by_contra h_neq
  have h_pos : |c - d| / 2 > 0 := by {
    apply div_pos
    · exact abs_pos.mpr (sub_ne_zero.mpr h_neq)
    · norm_num
  }
  
  rcases hc (|c - d| / 2) h_pos with ⟨δ1, hδ1_pos, hc_bound⟩
  rcases hd (|c - d| / 2) h_pos with ⟨δ2, hδ2_pos, hd_bound⟩
  
  let δ := min δ1 δ2
  have hδ_pos : δ > 0 := lt_min hδ1_pos hδ2_pos
  let x := z₀.re + δ / 2
  
  have h_x_dist : |x - z₀.re| = δ / 2 := by {
    calc |x - z₀.re| = |z₀.re + δ / 2 - z₀.re| := rfl
      _ = |δ / 2| := by ring_nf
      _ = δ / 2 := abs_of_pos (half_pos hδ_pos)
  }
  
  have h_x_pos : 0 < |x - z₀.re| := by {
    rw [h_x_dist]
    exact half_pos hδ_pos
  }
  
  have h_x_lt1 : |x - z₀.re| < δ1 := by {
    rw [h_x_dist]
    calc δ / 2 < δ := half_lt_self hδ_pos
      _ ≤ δ1 := min_le_left δ1 δ2
  }
  
  have h_x_lt2 : |x - z₀.re| < δ2 := by {
    rw [h_x_dist]
    calc δ / 2 < δ := half_lt_self hδ_pos
      _ ≤ δ2 := min_le_right δ1 δ2
  }
  
  have hc_val := hc_bound x ⟨h_x_pos, h_x_lt1⟩
  have hd_val := hd_bound x ⟨h_x_pos, h_x_lt2⟩
  
  have h_tri : |c - d| ≤ |(f ((x : ℂ) + (z₀.im : ℂ) * I) - f z₀) / (x - z₀.re) - c| + |(f ((x : ℂ) + (z₀.im : ℂ) * I) - f z₀) / (x - z₀.re) - d| := by {
    calc |c - d| = |-( ((f ((x : ℂ) + (z₀.im : ℂ) * I) - f z₀) / (x - z₀.re) - c) ) + ((f ((x : ℂ) + (z₀.im : ℂ) * I) - f z₀) / (x - z₀.re) - d)| := by {
        congr 1
        ring
      }
      _ ≤ |-( ((f ((x : ℂ) + (z₀.im : ℂ) * I) - f z₀) / (x - z₀.re) - c) )| + |((f ((x : ℂ) + (z₀.im : ℂ) * I) - f z₀) / (x - z₀.re) - d)| := abs_add _ _
      _ = |((f ((x : ℂ) + (z₀.im : ℂ) * I) - f z₀) / (x - z₀.re) - c)| + |((f ((x : ℂ) + (z₀.im : ℂ) * I) - f z₀) / (x - z₀.re) - d)| := by rw [abs_neg]
  }
  
  linarith
}"""

content = content.replace(old_block, new_block)

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
