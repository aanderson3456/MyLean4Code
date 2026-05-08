import Mathlib.Analysis.Complex.Basic

/-!
# Sarason - Definitions

Weierstrass-style definitions for limits and continuity to maintain the 
classical flavor of Sarason's notes.
-/

open Complex

namespace Sarason

/-- 
  Weierstrass definition of a limit at a finite point.
  f(z) → L as z → z₀
-/
def HasLimitAt (f : ℂ → ℂ) (L : ℂ) (z₀ : ℂ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ z, 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < δ → ‖f z - L‖ < ε

/-- 
  Weierstrass definition of a limit at infinity.
  f(z) → L as z → ∞
-/
def HasLimitAtInf (f : ℂ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ M > 0, ∀ z, ‖z‖ > M → |f z - L| < ε

/-- 
  Weierstrass definition of complex differentiability at z₀.
  f'(z₀) is the limit of the difference quotient.
-/
def DifferentiableAt (f : ℂ → ℂ) (f' : ℂ) (z₀ : ℂ) : Prop :=
  HasLimitAt (fun z => (f z - f z₀) / (z - z₀)) f' z₀

end Sarason
