import Mathlib

open Complex Filter TopologicalSpace Metric Bornology Classical MeasureTheory Real

lemma test_int_g_calc {x L : ℝ} (hL : 1 < L) (hx_pos : 0 < x) :
    let g := fun (t : ℝ) => L * x * Real.exp (-t) - 1
    ∫ t in (Real.log x)..(Real.log (L * x)), g t = L - 1 - Real.log L := by
{
  intro g
  have hg_int : IntervalIntegrable g volume (Real.log x) (Real.log (L * x)) := by
  {
    have h_cont : Continuous g := by
    {
      apply Continuous.sub
      · apply Continuous.mul continuous_const
        exact continuous_exp.comp continuous_neg
      · exact continuous_const
    }
    exact Continuous.intervalIntegrable h_cont _ _
  }
  have h_deriv : ∀ t ∈ Set.uIcc (Real.log x) (Real.log (L * x)),
    HasDerivAt (fun t => -L * x * Real.exp (-t) - t) (g t) t := by
  {
    intro t ht
    have h0 := HasDerivAt.exp (hasDerivAt_neg t)
    have h1 : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-t)) t := by
    {
      have eq : Real.exp (-t) * -1 = -Real.exp (-t) := by ring
      exact HasDerivAt.congr_deriv h0 eq
    }
    have h2 : HasDerivAt (fun t => -L * x * Real.exp (-t)) (-L * x * -Real.exp (-t)) t := by
    {
      exact HasDerivAt.const_mul (-L * x) h1
    }
    have h3 : HasDerivAt (fun t => -L * x * Real.exp (-t) - t) (-L * x * -Real.exp (-t) - 1) t := by
    {
      exact HasDerivAt.sub h2 (hasDerivAt_id t)
    }
    have h_eq : -L * x * -Real.exp (-t) - 1 = g t := by
    {
      dsimp [g]
      ring
    }
    rw [← h_eq]
    exact h3
  }
  have h_int_g : ∫ t in (Real.log x)..(Real.log (L * x)), g t
    = (-L * x * Real.exp (-Real.log (L * x)) - Real.log (L * x)) - (-L * x * Real.exp (-Real.log x) - Real.log x) := by
  {
    exact intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv hg_int
  }
  rw [h_int_g]
  have h_exp1 : Real.exp (-Real.log (L * x)) = (L * x)⁻¹ := by
  {
    rw [Real.exp_neg, Real.exp_log (mul_pos (by linarith) hx_pos)]
  }
  have h_exp2 : Real.exp (-Real.log x) = x⁻¹ := by
  {
    rw [Real.exp_neg, Real.exp_log hx_pos]
  }
  have h_log_mul : Real.log (L * x) = Real.log L + Real.log x := by
  {
    exact Real.log_mul (by linarith) (ne_of_gt hx_pos)
  }
  rw [h_exp1, h_exp2, h_log_mul]
  have h_Lx_inv : (L * x)⁻¹ = L⁻¹ * x⁻¹ := mul_inv (L) (x)
  rw [h_Lx_inv]
  have hL0 : L ≠ 0 := by linarith
  have hx0 : x ≠ 0 := by linarith
  calc
    (-L * x * (L⁻¹ * x⁻¹) - (Real.log L + Real.log x)) - (-L * x * x⁻¹ - Real.log x)
      = (- (L * L⁻¹) * (x * x⁻¹) - Real.log L - Real.log x) - (-L * (x * x⁻¹) - Real.log x) := by ring
    _ = (-1 * 1 - Real.log L - Real.log x) - (-L * 1 - Real.log x) := by
    {
      rw [mul_inv_cancel₀ hL0, mul_inv_cancel₀ hx0]
    }
    _ = L - 1 - Real.log L := by ring
}
