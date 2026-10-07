import Mathlib
import Contour

open Complex Filter TopologicalSpace Metric Bornology Classical MeasureTheory

namespace Sarason.PNT

noncomputable def newman_g (f : ℝ → ℝ) (z : ℂ) : ℂ :=
  ∫ t in Set.Ici (0:ℝ), (f t : ℂ) * Complex.exp (-z * (t : ℂ))

noncomputable def newman_g_T (f : ℝ → ℝ) (T : ℝ) (z : ℂ) : ℂ :=
  ∫ t in (0:ℝ)..T, (f t : ℂ) * Complex.exp (-z * (t : ℂ))

lemma newmanModifier_abs_on_C_plus (R : ℝ) (z : ℂ) (hR : 0 < R) (hz : z * star z = (R : ℂ)^2) (hz0 : z ≠ 0) (hz_re : 0 ≤ z.re) :
    ‖newmanModifier R z‖ = 2 * z.re / R^2 := by
{
  have h_eq := newmanModifier_eq_on_circle R z hz hz0
  rw [h_eq]
  sorry
}

lemma newman_integrand_bound_C_plus {f : ℝ → ℝ} {M R T : ℝ} {z : ℂ}
    (hR : 0 < R) (hT : 0 < T) (hz_sq : z * star z = (R : ℂ)^2) (hz0 : z ≠ 0) (hz_re : 0 < z.re)
    (hf_bound : ∀ t ≥ 0, |f t| ≤ M)
    (hg_diff_bound : ‖newman_g f z - newman_g_T f T z‖ ≤ M * Real.exp (-z.re * T) / z.re) :
    ‖(newman_g f z - newman_g_T f T z) * Complex.exp (z * (T : ℂ)) * newmanModifier R z‖ ≤ 2 * M / R^2 := by
{
  have h_mod := newmanModifier_abs_on_C_plus R z hR hz_sq hz0 (le_of_lt hz_re)
  have h_exp : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
  {
    have h_mul_re : (z * (T : ℂ)).re = z.re * T := by simp
    have h_abs_exp := Complex.norm_exp (z * (T : ℂ))
    rw [h_mul_re] at h_abs_exp
    exact h_abs_exp
  }
  sorry
}

lemma newmanModifier_abs_on_C_minus (R : ℝ) (z : ℂ) (hR : 0 < R) (hz : z * star z = (R : ℂ)^2) (hz0 : z ≠ 0) (hz_re : z.re ≤ 0) :
    ‖newmanModifier R z‖ = -2 * z.re / R^2 := by
{
  have h_eq := newmanModifier_eq_on_circle R z hz hz0
  rw [h_eq]
  sorry
}

lemma newman_integrand_bound_C_minus_gT {f : ℝ → ℝ} {M R T : ℝ} {z : ℂ}
    (hR : 0 < R) (hT : 0 < T) (hz_sq : z * star z = (R : ℂ)^2) (hz0 : z ≠ 0) (hz_re : z.re < 0)
    (hf_bound : ∀ t ≥ 0, |f t| ≤ M)
    (hg_T_bound : ‖newman_g_T f T z‖ ≤ M * (Real.exp (-z.re * T) - 1) / (-z.re)) :
    ‖newman_g_T f T z * Complex.exp (z * (T : ℂ)) * newmanModifier R z‖ ≤ 2 * M / R^2 := by
{
  have h_mod := newmanModifier_abs_on_C_minus R z hR hz_sq hz0 (le_of_lt hz_re)
  have h_exp : ‖Complex.exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
  {
    have h_mul_re : (z * (T : ℂ)).re = z.re * T := by simp
    have h_abs_exp := Complex.norm_exp (z * (T : ℂ))
    rw [h_mul_re] at h_abs_exp
    exact h_abs_exp
  }
  sorry
}

end Sarason.PNT
