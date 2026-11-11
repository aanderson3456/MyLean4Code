import Mathlib
import Contour

open Complex

lemma test_plus (R : ℝ) (z : ℂ) (hR : 0 < R) (hz : z * star z = (R : ℂ)^2) (hz0 : z ≠ 0) (hz_re : 0 ≤ z.re) :
    ‖Sarason.PNT.newmanModifier R z‖ = 2 * z.re / R^2 := by
{
  have h_eq := Sarason.PNT.newmanModifier_eq_on_circle R z hz hz0
  rw [h_eq]
  have h_add : z + star z = ((2 * z.re : ℝ) : ℂ) := by
  {
    apply Complex.ext
    · simp
      ring
    · simp
  }
  rw [h_add]
  rw [norm_div]
  have h_norm_num : ‖((2 * z.re : ℝ) : ℂ)‖ = 2 * z.re := by
  {
    exact (Complex.norm_real (2 * z.re)).trans (abs_of_nonneg (by linarith))
  }
  have h_norm_den : ‖(R : ℂ)^2‖ = R^2 := by
  {
    have h_r_sq : (R : ℂ)^2 = ((R^2 : ℝ) : ℂ) := by simp
    rw [h_r_sq]
    exact (Complex.norm_real (R^2)).trans (abs_of_nonneg (by positivity))
  }
  rw [h_norm_num, h_norm_den]
}

lemma test_minus (R : ℝ) (z : ℂ) (hR : 0 < R) (hz : z * star z = (R : ℂ)^2) (hz0 : z ≠ 0) (hz_re : z.re ≤ 0) :
    ‖Sarason.PNT.newmanModifier R z‖ = -2 * z.re / R^2 := by
{
  have h_eq := Sarason.PNT.newmanModifier_eq_on_circle R z hz hz0
  rw [h_eq]
  have h_add : z + star z = ((2 * z.re : ℝ) : ℂ) := by
  {
    apply Complex.ext
    · simp
      ring
    · simp
  }
  rw [h_add]
  rw [norm_div]
  have h_norm_num : ‖((2 * z.re : ℝ) : ℂ)‖ = -2 * z.re := by
  {
    have h_neg : 2 * z.re ≤ 0 := by linarith
    exact (Complex.norm_real (2 * z.re)).trans (abs_of_nonpos h_neg)
  }
  have h_norm_den : ‖(R : ℂ)^2‖ = R^2 := by
  {
    have h_r_sq : (R : ℂ)^2 = ((R^2 : ℝ) : ℂ) := by simp
    rw [h_r_sq]
    exact (Complex.norm_real (R^2)).trans (abs_of_nonneg (by positivity))
  }
  rw [h_norm_num, h_norm_den]
  have h_neg_div : (-2 * z.re) / R^2 = -(2 * z.re / R^2) := by ring
  -- wait, the goal is `-2 * z.re / R^2` which is the same as `(-2 * z.re) / R^2`
}
