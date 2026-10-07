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
  rw [norm_mul, norm_mul, h_mod, h_exp]
  have h1 : ‖newman_g f z - newman_g_T f T z‖ * Real.exp (z.re * T) ≤ (M * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) := by
  {
    exact mul_le_mul_of_nonneg_right hg_diff_bound (Real.exp_pos (z.re * T)).le
  }
  have h2 : ‖newman_g f z - newman_g_T f T z‖ * Real.exp (z.re * T) * (2 * z.re / R^2) ≤ (M * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) * (2 * z.re / R^2) := by
  {
    have h_c_nonneg : 0 ≤ 2 * z.re / R^2 := by positivity
    exact mul_le_mul_of_nonneg_right h1 h_c_nonneg
  }
  have h3 : (M * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) * (2 * z.re / R^2) = 2 * M / R^2 := by
  {
    have h_exp2 : Real.exp (-z.re * T) * Real.exp (z.re * T) = 1 := by
    {
      rw [← Real.exp_add]
      have h_zero : -z.re * T + z.re * T = 0 := by ring
      rw [h_zero, Real.exp_zero]
    }
    have h_re : z.re ≠ 0 := ne_of_gt hz_re
    calc
      (M * Real.exp (-z.re * T) / z.re) * Real.exp (z.re * T) * (2 * z.re / R^2)
        = (M / R^2) * 2 * (Real.exp (-z.re * T) * Real.exp (z.re * T)) * (z.re / z.re) := by ring
      _ = (M / R^2) * 2 * 1 * 1 := by
      {
        rw [h_exp2]
        have h_div : z.re / z.re = 1 := div_self h_re
        rw [h_div]
      }
      _ = 2 * M / R^2 := by ring
  }
  rw [h3] at h2
  exact h2
}

lemma newmanModifier_abs_on_C_minus (R : ℝ) (z : ℂ) (hR : 0 < R) (hz : z * star z = (R : ℂ)^2) (hz0 : z ≠ 0) (hz_re : z.re ≤ 0) :
    ‖newmanModifier R z‖ = -2 * z.re / R^2 := by
{
  have h_eq := newmanModifier_eq_on_circle R z hz hz0
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
    have h_abs := abs_of_nonpos h_neg
    have h_eq2 : -(2 * z.re) = -2 * z.re := by ring
    rw [h_eq2] at h_abs
    exact (Complex.norm_real (2 * z.re)).trans h_abs
  }
  have h_norm_den : ‖(R : ℂ)^2‖ = R^2 := by
  {
    have h_r_sq : (R : ℂ)^2 = ((R^2 : ℝ) : ℂ) := by simp
    rw [h_r_sq]
    exact (Complex.norm_real (R^2)).trans (abs_of_nonneg (by positivity))
  }
  rw [h_norm_num, h_norm_den]
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
  rw [norm_mul, norm_mul, h_mod, h_exp]
  have h1 : ‖newman_g_T f T z‖ * Real.exp (z.re * T) ≤ (M * (Real.exp (-z.re * T) - 1) / (-z.re)) * Real.exp (z.re * T) := by
  {
    exact mul_le_mul_of_nonneg_right hg_T_bound (Real.exp_pos (z.re * T)).le
  }
  have h2 : ‖newman_g_T f T z‖ * Real.exp (z.re * T) * (-2 * z.re / R^2) ≤ (M * (Real.exp (-z.re * T) - 1) / (-z.re)) * Real.exp (z.re * T) * (-2 * z.re / R^2) := by
  {
    have h_c_nonneg : 0 ≤ -2 * z.re / R^2 := by
    {
      have h_neg : 0 ≤ -2 * z.re := by linarith
      positivity
    }
    exact mul_le_mul_of_nonneg_right h1 h_c_nonneg
  }
  have h3 : (M * (Real.exp (-z.re * T) - 1) / (-z.re)) * Real.exp (z.re * T) * (-2 * z.re / R^2) ≤ 2 * M / R^2 := by
  {
    have h_exp2 : Real.exp (-z.re * T) * Real.exp (z.re * T) = 1 := by
    {
      rw [← Real.exp_add]
      have h_zero : -z.re * T + z.re * T = 0 := by ring
      rw [h_zero, Real.exp_zero]
    }
    have h_re : -z.re ≠ 0 := by linarith
    have h_eq : (M * (Real.exp (-z.re * T) - 1) / (-z.re)) * Real.exp (z.re * T) * (-2 * z.re / R^2)
      = (2 * M / R^2) * (1 - Real.exp (z.re * T)) := by
    {
      calc
        (M * (Real.exp (-z.re * T) - 1) / (-z.re)) * Real.exp (z.re * T) * (-2 * z.re / R^2)
          = (M / R^2) * 2 * ((Real.exp (-z.re * T) - 1) * Real.exp (z.re * T)) * (-z.re / -z.re) := by ring
        _ = (M / R^2) * 2 * ((Real.exp (-z.re * T) - 1) * Real.exp (z.re * T)) * 1 := by
        {
          have h_div : -z.re / -z.re = 1 := div_self h_re
          rw [h_div]
        }
        _ = (2 * M / R^2) * (Real.exp (-z.re * T) * Real.exp (z.re * T) - Real.exp (z.re * T)) := by ring
        _ = (2 * M / R^2) * (1 - Real.exp (z.re * T)) := by rw [h_exp2]
    }
    rw [h_eq]
    have h_exp_pos : 0 ≤ Real.exp (z.re * T) := (Real.exp_pos (z.re * T)).le
    have h_sub_le : 1 - Real.exp (z.re * T) ≤ 1 := by linarith
    have h_M_nonneg : 0 ≤ M := by
    {
      have h_abs_M := hf_bound 0 (by linarith)
      have h_abs_pos : 0 ≤ |f 0| := abs_nonneg (f 0)
      exact h_abs_pos.trans h_abs_M
    }
    have h_pos : 0 ≤ 2 * M / R^2 := by positivity
    exact mul_le_of_le_one_right h_pos h_sub_le
  }
  exact h2.trans h3
}

end Sarason.PNT
