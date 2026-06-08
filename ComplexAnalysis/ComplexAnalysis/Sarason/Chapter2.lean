/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Conformal
import ComplexAnalysis.Sarason.Definitions

/-!
# Sarason - Chapter 2: Complex Differentiation

Formalization of Section II of Donald Sarason's "Notes on Complex Function Theory".
Focus: Definition of the derivative, Cauchy-Riemann equations, and Differential Operators.

Credit: Donald Sarason
-/

open Complex Sarason

noncomputable section

namespace Sarason.Ch2

/- 
  §II.1 Definition of the Derivative (Sarason's Weierstrass style).
  DifferentiableAt is defined in Definitions.lean using HasLimitAt_eps.
-/

/-- The ∂ operator (del) for a function f : ℂ → ℂ at point z. -/
def del (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  let L := fderiv ℝ f z
  let df_dx := L 1
  let df_dy := L I
  (1 / 2 : ℂ) * (df_dx - I * df_dy)

/-- The ∂̄ operator (del-bar) for a function f : ℂ → ℂ at point z. -/
def delBar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  let L := fderiv ℝ f z
  let df_dx := L 1
  let df_dy := L I
  (1 / 2 : ℂ) * (df_dx + I * df_dy)

-- Local notation for Sarason's flavor
local notation f "𝓏" => del f
local notation f "𝓏bar" => delBar f

/-- 
  Relating Sarason's Weierstrass derivative to Mathlib's Filter-based HasDerivAt.
-/
theorem differentiableAt_iff_mathlib (f : ℂ → ℂ) (f' : ℂ) (z₀ : ℂ) :
    HasDerivAt_eps f f' z₀ ↔ _root_.HasDerivAt f f' z₀ := by {
  rw [hasDerivAt_iff_eps]
}

/-- 
  §II.6 Cauchy-Riemann Equations (Sarason's version).
-/
theorem hasComplexDerivAt_iff_delBar_eq_zero {f : ℂ → ℂ} {z : ℂ} (h : _root_.DifferentiableAt ℝ f z) :
    (∃ f', HasDerivAt_eps f f' z) ↔ (delBar f z = 0) := by {
  have hd : (∃ f', HasDerivAt_eps f f' z) ↔ DifferentiableAt_eps f z := Iff.rfl
  rw [hd]
  rw [← differentiableAt_iff_eps]
  rw [differentiableAt_complex_iff_differentiableAt_real]
  simp only [h, true_and]
  unfold delBar
  dsimp only
  have : (1 / 2 : ℂ) ≠ 0 := by norm_num
  rw [mul_eq_zero, or_iff_right this]
  simp only [smul_eq_mul]
  constructor
  · intro h_cr
    rw [h_cr]
    have : I * (I * fderiv ℝ f z 1) = - fderiv ℝ f z 1 := by {
      calc I * (I * fderiv ℝ f z 1) = (I * I) * fderiv ℝ f z 1 := by ring
      _ = -1 * fderiv ℝ f z 1 := by rw [I_mul_I]
      _ = - fderiv ℝ f z 1 := by ring
    }
    rw [this]
    ring
  · intro h_delbar
    have h1 : I * (fderiv ℝ f z 1 + I * fderiv ℝ f z I) = I * 0 := by rw [h_delbar]
    simp only [mul_zero, mul_add] at h1
    have h2 : I * (I * fderiv ℝ f z I) = - fderiv ℝ f z I := by {
      calc I * (I * fderiv ℝ f z I) = (I * I) * fderiv ℝ f z I := by ring
      _ = -1 * fderiv ℝ f z I := by rw [I_mul_I]
      _ = - fderiv ℝ f z I := by ring
    }
    rw [h2] at h1
    have h3 : I * fderiv ℝ f z 1 - fderiv ℝ f z I = 0 := by {
      calc I * fderiv ℝ f z 1 - fderiv ℝ f z I = I * fderiv ℝ f z 1 + - fderiv ℝ f z I := by ring
      _ = 0 := h1
    }
    exact (sub_eq_zero.mp h3).symm
}

end Sarason.Ch2

end
