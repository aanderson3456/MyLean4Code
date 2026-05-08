import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.InnerProductSpace.PiL2
import ComplexAnalysis.Sarason.Definitions

/-!
# Sarason - Chapter 1: Complex Numbers

Formalization of Section I of Donald Sarason's "Notes on Complex Function Theory".
Focus: The complex plane, stereographic projection, and the chordal metric.

Credit: Donald Sarason
-/

open Complex

namespace Sarason.Ch1

/-! 
  §I.14 The Extended Complex Plane and Stereographic Projection.
  Sarason introduces the Riemann Sphere as the unit sphere S in ℝ³.
  The stereographic projection maps z = x + iy to a point (x₁, x₂, x₃) on S.
-/

/-- 
  The chordal metric ρ(z, w) is the Euclidean distance in ℝ³ between 
  the stereographic projections of z and w.
-/
noncomputable def chordalMetric (z w : ℂ) : ℝ :=
  (2 * ‖z - w‖) / (Real.sqrt (‖z‖ ^ 2 + 1) * Real.sqrt (‖w‖ ^ 2 + 1))

/-- 
  The chordal distance to infinity.
  Exercise: ρ(z, ∞) = 2 / sqrt(|z|² + 1)
-/
noncomputable def chordalMetricToInf (z : ℂ) : ℝ :=
  2 / Real.sqrt (‖z‖ ^ 2 + 1)

/-- 
  Exercise from §I.14:
  Show that the chordal distance from z to infinity is given by 2 / sqrt(|z|² + 1).
  Using the Weierstrass definition of limits.
-/
theorem chordal_dist_limit (z : ℂ) :
  HasLimitAtInf (fun w => chordalMetric z w) (chordalMetricToInf z) := by
  unfold HasLimitAtInf chordalMetric chordalMetricToInf
  intro ε hε
  -- Let C = 2 / sqrt(|z|² + 1). We need to find M such that |w| > M implies C * | |z-w|/sqrt(|w|²+1) - 1 | < ε.
  let C := 2 / Real.sqrt (‖z‖ ^ 2 + 1)
  have hC : 0 < C := by
    apply div_pos (by norm_num)
    apply Real.sqrt_pos.mpr
    linarith [sq_nonneg ‖z‖]
  
  -- We need | |z-w|/sqrt(|w|²+1) - 1 | < ε / C.
  let ε' := ε / C
  have hε' : 0 < ε' := div_pos hε hC

  -- As |w| → ∞, |z-w|/sqrt(|w|²+1) → 1.
  -- Specifically, |w|-|z| ≤ |z-w| ≤ |w|+|z|.
  -- (|w|-|z|)/sqrt(|w|²+1) → 1 and (|w|+|z|)/sqrt(|w|²+1) → 1.
  
  -- For a formal proof, we can simplify:
  -- | |z-w|/sqrt(|w|²+1) - 1 | = | (|z-w| - sqrt(|w|²+1)) / sqrt(|w|²+1) |
  -- Using |z-w| - sqrt(|w|²+1) = (|z-w|² - (|w|²+1)) / (|z-w| + sqrt(|w|²+1))
  -- |z-w|² = |z|² + |w|² - 2Re(z·w*)
  -- |z-w|² - |w|² - 1 = |z|² - 2Re(z·w*) - 1
  -- This is bounded by |z|² + 2|z||w| + 1.
  -- So the term is roughly (2|z||w|) / (|w|·2|w|) = |z|/|w| → 0.
  
  -- To keep it simple, I'll use M such that |w| is large enough to dominate |z| and 1.
  use (2 * ‖z‖ + 1 + (4 * ‖z‖ + 2) / ε')
  intro w hw
  
  -- The detailed inequality manipulation goes here.
  -- For now, I'll provide the high-level steps.
  sorry

end Sarason.Ch1
