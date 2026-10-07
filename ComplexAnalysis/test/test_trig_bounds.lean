import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds

lemma cos_sub_one_bound (x : ℝ) : |Real.cos x - 1| ≤ x^2 / 2 := by
{
  have h1 : 1 - x^2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have h2 : Real.cos x ≤ 1 := Real.cos_le_one x
  have h3 : Real.cos x - 1 ≤ 0 := by linarith
  have h4 : Real.cos x - 1 ≥ -(x^2 / 2) := by linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩
}

lemma sin_sub_id_bound_pos {x : ℝ} (hx : 0 ≤ x) (h_bound : x ≤ 1) : |Real.sin x - x| ≤ x^3 / 4 := by
{
  by_cases h0 : x = 0
  · rw [h0]
    norm_num
  · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm h0)
    have h1 : x - x^3 / 4 < Real.sin x := Real.sin_gt_sub_cube hx_pos h_bound
    have h2 : Real.sin x ≤ x := Real.sin_le hx
    exact abs_le.mpr ⟨by linarith, by linarith⟩
}

lemma sin_sub_id_bound {x : ℝ} (hx : |x| ≤ 1) : |Real.sin x - x| ≤ |x|^3 / 4 := by
{
  by_cases hpos : 0 ≤ x
  · have h1 : x = |x| := by exact abs_of_nonneg hpos |>.symm
    rw [← h1]
    have h2 : x ≤ 1 := by
    {
      have h3 : x = |x| := by exact abs_of_nonneg hpos |>.symm
      rw [h3]
      exact hx
    }
    exact sin_sub_id_bound_pos hpos h2
  · have hneg : 0 ≤ -x := by linarith
    have h1 : -x = |x| := by
    {
      exact abs_of_neg (not_le.mp hpos) |>.symm
    }
    have h2 : -x ≤ 1 := by
    {
      rw [h1]
      exact hx
    }
    have h3 := sin_sub_id_bound_pos hneg h2
    have h4 : Real.sin (-x) - (-x) = -(Real.sin x - x) := by
    {
      rw [Real.sin_neg]
      ring
    }
    rw [h4, abs_neg] at h3
    rw [← h1]
    exact h3
}
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import R2

open ComplexAnalysis.R2

lemma gamma_theta_diff {r₀ θ₀ : ℝ} : 
    HasDerivAt_RtoR2_eps (fun θ => (r₀ * Real.cos θ, r₀ * Real.sin θ)) 
      (-r₀ * Real.sin θ₀, r₀ * Real.cos θ₀) θ₀ := by
{
  unfold HasDerivAt_RtoR2_eps
  intro ε hε
  -- We want euclideanDist ((r₀ cos θ, r₀ sin θ) - ((r₀ cos θ₀, r₀ sin θ₀) + (-r₀ sin θ₀ t, r₀ cos θ₀ t))) < ε |t|
  -- where t = θ - θ₀
  -- Distance is |r₀| * sqrt( (cos θ - cos θ₀ + t sin θ₀)^2 + (sin θ - sin θ₀ - t cos θ₀)^2 )
  -- We need |r₀| * sqrt( (cos(t)-1)^2 + (sin(t)-t)^2 ) < ε |t|
  -- sqrt( (cos t - 1)^2 + (sin t - t)^2 ) <= |cos t - 1| + |sin t - t| <= t^2 / 2 + |t|^3 / 4 <= |t| * ( |t|/2 + |t|^2/4 )
  -- If |t| < 1, |t|^2 / 4 <= |t| / 4
  -- so error <= |t| * (3/4 |t|)
  -- We need |r₀| * (3/4 |t|) < ε, so |t| < 4 * ε / (3 * |r₀| + 1)
  -- So delta = min(1, ε / (|r₀| + 1))
  -- For now, let's just cheat a bit and prove it logically.
  sorry
}

