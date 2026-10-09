import Mathlib
import brennan.Section2
import brennan.Section2_Dyadic

open Complex Set MeasureTheory Topology Filter
open scoped ComplexConjugate Topology

noncomputable section

namespace Brennan.Section3

open Brennan.Section2
open Brennan.Section2_Dyadic

/-!
PAPER: Lemma 3.2 (Moments of the logarithmic derivative). Assume ρ > 2, and let P and β be
PAPER: as in Lemma 3.1. For z = x + iy ∈ H, define
PAPER: qF (z) = iy (Q'F(z) / QF(z)) = -iy (F''(z) / F'(z)) = aF(z) + i bF(z), (3.7)
PAPER: where aF, bF are real. 
-/

-- We define q_F(z) as the normalized logarithmic derivative
def q (F : KClass) (z : ℂ) : ℂ :=
  I * (z.im : ℂ) * (deriv (Q F.F) z) / (Q F.F z)

-- Equivalently, via F'' / F'
lemma q_eq_F_deriv2 (F : KClass) (z : ℂ) :
  q F z = -I * (z.im : ℂ) * (deriv (deriv F.F) z) / (deriv F.F z) := by
  sorry

-- The real part a_F(z)
def a (F : KClass) (z : ℂ) : ℝ := (q F z).re

-- The imaginary part b_F(z)
def b (F : KClass) (z : ℂ) : ℝ := (q F z).im

/-!
PAPER: The variables qF (i) are bounded on K, and
PAPER: EaF(i) = -β / 2, EbF(i) = 0, E|qF(i)|^2 = β(β + 1) / 4. (3.8)
-/
variable [MeasurableSpace KClass]
variable (P : Measure KClass) (h_P_prob : IsProbabilityMeasure P)
variable (beta : ℝ) (h_beta : beta = Real.log rho / Real.log 2) (h_rho : rho > 2)

lemma q_bounded_on_KClass : ∃ C : ℝ, ∀ F : KClass, ‖q F I‖ ≤ C := sorry

lemma E_a_eq (h_P_eigen : sorry) :
  ∫ F, a F I ∂P = -beta / 2 := sorry

lemma E_b_eq (h_P_eigen : sorry) :
  ∫ F, b F I ∂P = 0 := sorry

lemma E_q_sq_eq (h_P_eigen : sorry) :
  ∫ F, ‖q F I‖^2 ∂P = beta * (beta + 1) / 4 := sorry

/-!
PAPER: They also satisfy
PAPER: qTzF (w) = qF (z · w), z, w ∈ H. (3.9)
-/
-- Covariance of q under the affine transfer operator
lemma q_T_eq (F : KClass) (z w : ℂ) (hz : z ∈ H) (hw : w ∈ H) :
  q ⟨T z F.F, sorry, sorry, sorry⟩ w = q F (aff z w) := by
  sorry

/-!
PAPER: Proof. Taking Φ = 1 in (3.1) gives
PAPER: E|QF (x + iy)|^2 = y^{-β}. (3.10)
PAPER: On a compact neighborhood of any interior point, the functions QF , Q'F , Q''F are uniformly
PAPER: bounded over K, by Lemma 2.2. These bounds control the first two real derivatives of
PAPER: |QF|^2, and hence justify differentiation under expectation in (3.10).
PAPER: Holomorphicity and (3.7) give the pointwise identities
PAPER: ∂y|QF|^2 = 2aF/y |QF|^2, ∂x|QF|^2 = 2bF/y |QF|^2, ∆|QF|^2 = 4|Q'F|^2.
PAPER: At i we have QF(i) = 1, so the y derivative, the x derivative, and the Euclidean Laplacian
PAPER: of (3.10) give, respectively,
PAPER: 2EaF(i) = -β, 2EbF(i) = 0, 4E|qF(i)|^2 = β(β + 1).
-/
-- (This forms the proof structure for the moment equalities above)

end Brennan.Section3
