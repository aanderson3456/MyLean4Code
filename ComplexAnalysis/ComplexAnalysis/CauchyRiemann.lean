import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv

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
example (z : ℂ) : ¬ DifferentiableAt ℂ (fun z => star z) z := by
  intro h
  -- The real derivative of `star` is `star` itself.
  have : HasFDerivAt star (starL ℝ : ℂ →L[ℝ] ℂ) z := starL.hasFDerivAt (R := ℝ)
  -- If `star` were complex differentiable, its real derivative would be complex linear.
  let L := h.hasFDerivAt.restrictScalars ℝ
  have : L = starL ℝ := this.unique h.hasFDerivAt.restrictScalars ℝ
  -- But `starL` is not complex linear because star(i) = -i != i * star(1) = i * 1.
  have cl : IsComplexLinear (starL ℝ) := by
    rw [← this]
    exact h.hasFDerivAt.isComplexLinear
  have : star (I : ℂ) = I * star (1 : ℂ) := cl.map_I
  simp at this -- yields -I = I, a contradiction
