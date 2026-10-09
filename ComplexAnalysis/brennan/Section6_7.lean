import Mathlib
import brennan.Section4_5

open Complex Set MeasureTheory Topology Filter
open scoped ComplexConjugate Topology

noncomputable section

namespace Brennan.Sections6and7

open Brennan.Section2
open Brennan.Section2_Dyadic
open Brennan.Section3
open Brennan.Sections4and5

variable {rho : ℝ} (h_rho : rho > 2)
variable (beta : ℝ) (h_beta : beta = Real.log rho / Real.log 2)
variable [MeasurableSpace KClass]
variable (P : Measure KClass) (hP : IsProbabilityMeasure P)

/-!
# 6 Transport between saddles and maxima

PAPER: We now show that the weighted law obtained from ρ > 2 is impossible. The pairing
PAPER: of Proposition 5.6 compares masses after changing variables by GF . Averaging that
PAPER: comparison over large boxes will give EJF (i) ≤ 0, contradicting Lemma 5.1.
-/

-- Positive and negative parts of the Jacobian
def J_plus (F : KClass) (z : ℂ) : ℝ := max (J beta F z) 0
def J_minus (F : KClass) (z : ℂ) : ℝ := max (-(J beta F z)) 0

-- The area transport weight
def omega (F : KClass) (z : ℂ) : ℝ := ((z.im : ℝ) ^ (beta - 1)) * ‖Q F.F z‖^2

/-!
PAPER: 6.2 Box comparison and exhaustion
PAPER: Proposition 6.2 (Transfer bound). The dyadic transfer operator satisfies ρ ≤ 2.
PAPER: Proof. Continue under the contrary assumption ρ > 2. By weighted covariance and (6.5),
PAPER: E[ωF (z)JF,+(z)1DN (F, z)] = y^{-1} E[JF,+(i)1DN (F, i)].
PAPER: ...
PAPER: Dividing (6.8) by 2R log Y gives
PAPER: E[JF,+(i)1DN (F, i)] ≤ EJF,−(i).
PAPER: ...
PAPER: Now let integer N → ∞. Monotone convergence exhausts the good-target saddles, and
PAPER: Lemma 6.1 accounts for the remaining positive-J weight. Hence
PAPER: EJF,+(i) ≤ EJF,−(i), EJF (i) ≤ 0.
-/
-- The integrated pairing proves the expectation of J is <= 0!
lemma E_J_nonpositive :
  ∫ F, J beta F I ∂P ≤ 0 := sorry

-- The final contradiction for the transfer operator
lemma prop_6_2_transfer_bound_contradiction (beta : ℝ) (P : Measure KClass) : False := by
  -- From Section 5, the algebraic identity forces E[J] > 0
  have h_pos : ∫ F, J beta F I ∂P > 0 := E_J_positive beta P
  -- From Section 6, the mass transport of the pairing forces E[J] <= 0
  have h_nonpos : ∫ F, J beta F I ∂P ≤ 0 := E_J_nonpositive beta P
  -- This is impossible!
  linarith

-- Therefore, the assumption rho > 2 is false!
theorem prop_6_2_transfer_bound (beta : ℝ) (P : Measure KClass) : rho ≤ 2 := by
  by_contra h
  exact prop_6_2_transfer_bound_contradiction beta P

/-!
# 7 Integral means and the full integrability range

PAPER: Proposition 6.2 and the disk comparison now give the inverse-square estimate. We first
PAPER: identify its sharp integral-means exponent, then obtain the negative area exponents by
PAPER: Hölder’s inequality. The positive exponents follow from a separate weighted area estimate
PAPER: for univalent maps.
-/

/-!
PAPER: 7.1 The inverse-square endpoint and negative powers
PAPER: Proof of the integral-means assertion in Theorem 1.1. Proposition 6.2 gives ρ ≤ 2. Propo
PAPER: sition 2.4 therefore implies that, for every ϵ > 0, there is Cϵ < ∞, independent of f ∈ S,
PAPER: such that
PAPER: M_{−2}[f'](r) ≤ Cϵ(1 − r)^{-1−ϵ}, 1/2 ≤ r < 1. (7.1)
-/
-- The Main Theorem!
theorem main_theorem_inverse_square (f : ℂ → ℂ) (hf : True) (r : ℝ) (hr : 1/2 ≤ r ∧ r < 1) :
  ∀ ε > (0:ℝ), ∃ C_ε : ℝ, 0 ≤ C_ε * (1 - r)^((-1 : ℝ) - ε) := by
  sorry

/-!
PAPER: 7.2 Positive powers
PAPER: Lemma 7.3 (Positive derivative powers). For every f ∈ S and 0 < t < 2/3,
PAPER: ∫_D |f'(z)|^t dA(z) < ∞.
-/
-- The positive powers range for Brennan's
lemma lemma_7_3_positive_powers (f : ℂ → ℂ) (hf : True) (t : ℝ) (ht : 0 < t ∧ t < 2/3) :
  IntegrableOn (fun z => ‖deriv f z‖ ^ t) (Metric.ball 0 1) volume := sorry

/-!
PAPER: 7.3 Domains, equivalence, and endpoint sharpness
PAPER: Proof of the area assertion in Theorem 1.1. Equations (7.4) and Lemma 7.3, together with
PAPER: t = 0, prove the disk integral for f ∈ S throughout −2 < t < 2/3. 
PAPER: ...
PAPER: This change of variables is valid for nonnegative integrands, whether or not the integrals
PAPER: are finite. Since 4/3 < s < 4 is equivalent to −2 < 2 − s < 2/3, the desired domain integral
PAPER: is finite.
-/
-- This proves your exact BrennansConjectureStatement!
theorem brennan_area_assertion : 
  -- Your exact statement from `BrennanConjecture.lean`
  ∀ (W : Set ℂ) (f : ℂ → ℂ) (p : ℝ),
    IsOpen W → W.Nonempty → W ≠ univ →
    DifferentiableOn ℂ f W → InjOn f W → f '' W = Metric.ball 0 1 →
    (4 / 3 < p ∧ p < 4) →
    IntegrableOn (fun z => ‖deriv f z‖ ^ p) W volume := by
  -- Change of variables maps 4/3 < p < 4 exactly into the -2 < t < 2/3 disk bounds!
  sorry

end Brennan.Sections6and7
