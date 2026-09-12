import ComplexAnalysis.Sarason.Chapter2

open ComplexAnalysis.R2
open Complex
open Sarason
open Sarason.Ch2

lemma partial_deriv_unique_x (f : ℂ → ℝ) (c d : ℝ) (z₀ : ℂ) 
  (hc : HasPartialDerivX_C_to_R_eps f c z₀) 
  (hd : HasPartialDerivX_C_to_R_eps f d z₀) : c = d := by {
  by_contra h_neq
  have h_pos : |c - d| / 2 > 0 := by {
    change 0 < |c - d| / 2
    refine half_pos ?_
    exact abs_pos.mpr (sub_ne_zero.mpr h_neq)
  }
  rcases hc (|c - d| / 2) h_pos with ⟨δ1, hδ1_pos, hδ1⟩
  rcases hd (|c - d| / 2) h_pos with ⟨δ2, hδ2_pos, hδ2⟩
  set δ := min δ1 δ2
  have hδ_pos : δ > 0 := lt_min hδ1_pos hδ2_pos
  set x := z₀.re + δ / 2
  have hx_diff : x - z₀.re = δ / 2 := by ring
  have hx_dist1 : 0 < |x - z₀.re| := by {
    rw [hx_diff]
    exact abs_pos.mpr (ne_of_gt (half_pos hδ_pos))
  }
  have hx_dist2_1 : |x - z₀.re| < δ1 := by {
    rw [hx_diff, abs_of_pos (half_pos hδ_pos)]
    exact lt_of_lt_of_le (half_lt_self hδ_pos) (min_le_left δ1 δ2)
  }
  have hx_dist2_2 : |x - z₀.re| < δ2 := by {
    rw [hx_diff, abs_of_pos (half_pos hδ_pos)]
    exact lt_of_lt_of_le (half_lt_self hδ_pos) (min_le_right δ1 δ2)
  }
  have hc_bound := hδ1 x ⟨hx_dist1, hx_dist2_1⟩
  have hd_bound := hδ2 x ⟨hx_dist1, hx_dist2_2⟩
  have h1 := (abs_lt.mp hc_bound).1
  have h2 := (abs_lt.mp hc_bound).2
  have h3 := (abs_lt.mp hd_bound).1
  have h4 := (abs_lt.mp hd_bound).2
  rcases le_total 0 (c - d) with h | h
  · have : |c - d| = c - d := abs_of_nonneg h
    linarith
  · have : |c - d| = -(c - d) := abs_of_nonpos h
    linarith
}

