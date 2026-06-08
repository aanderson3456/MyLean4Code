/- formalization copyright Austin Anderson using Gemini 2026 -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Star

open Complex

/-- 
  Example 1: f(z) = z^2 is holomorphic everywhere.
-/
example (z : ℂ) : DifferentiableAt ℂ (fun z => z^2) z :=
  differentiableAt_pow 2

/-- 
  Example 2: f(z) = conj z is NOT holomorphic.
  We use the fact that the derivative of `conj` is `conj`, 
  which is not complex linear.
-/
example (z : ℂ) : ¬ DifferentiableAt ℂ (fun z => star z) z := by {
  intro h
  -- The real derivative of `star` is `star` itself.
  have hstar : HasFDerivAt star ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) z :=
    HasFDerivAt.star (hasFDerivAt_id (𝕜 := ℝ) z)
  -- If `star` were complex differentiable, its real derivative would be complex linear.
  let f'' := fderiv ℂ (fun z => star z) z
  let L : ℂ →L[ℝ] ℂ := f''.restrictScalars ℝ
  have h_real : HasFDerivAt star L z := h.hasFDerivAt.restrictScalars ℝ
  have hL : ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) = L := hstar.unique h_real
  have h_comm : L I = I * L 1 := by {
    have h_smul := f''.map_smul I 1
    simp at h_smul
    exact h_smul
  }
  have h_star : L I = -I := by {
    rw [← hL]
    simp
  }
  have h_star1 : L 1 = 1 := by {
    rw [← hL]
    simp
  }
  have h_contra : -I = I := by {
    calc -I = L I := h_star.symm
    _ = I * L 1 := h_comm
    _ = I * 1 := by rw [h_star1]
    _ = I := by rw [mul_one]
  }
  have : (2 : ℂ) * I = 0 := by {
    calc (2 : ℂ) * I = I - (-I) := by ring
    _ = I - I := by rw [h_contra]
    _ = 0 := by ring
  }
  have h_mul : (2 : ℂ) = 0 ∨ I = 0 := mul_eq_zero.mp this
  rcases h_mul with h2 | hI
  · norm_num at h2
  · exact I_ne_zero hI
}
