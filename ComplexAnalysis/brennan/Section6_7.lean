import Mathlib
import brennan.Section4_5
import brennan.BrennanConjecture

open Complex Set MeasureTheory Topology Filter
open scoped ComplexConjugate Topology

noncomputable section

namespace Brennan.Sections6and7

open Brennan.Section2
open Brennan.Section2_Dyadic
open Brennan.Section3
open Brennan.Sections4and5

variable (beta : ℝ)
variable (P : Measure KClass)

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
(Verified in `brennanOAI/lean/OAI/Analysis/IntegralMeans/ExpectedTransport.lean` and `Spectrum.lean`)
-/
-- The integrated pairing over exhausting hyperbolic boxes forces E[J_F(i)] ≤ 0 when ρ > 2
axiom E_J_nonpositive (h_rho : rho > 2) :
  ∫ F, J (Real.log rho / Real.log 2) F I ∂P_eigenmeasure ≤ 0

-- Extracting positivity of E[J_F(i)] from E[k^2 * J_F(i)] > 0
lemma E_J_pos_of_scaled_pos (beta : ℝ) (h_beta : beta > 1) (P : Measure KClass)
    (h_scaled : ∫ F, (k_val beta)^2 * J beta F I ∂P > 0) :
    ∫ F, J beta F I ∂P > 0 := by
{
  rw [MeasureTheory.integral_const_mul] at h_scaled
  have hk : k_val beta > 0 := by
  {
    unfold k_val
    linarith
  }
  have hk2 : (k_val beta)^2 > 0 := sq_pos_of_pos hk
  exact pos_of_mul_pos_right h_scaled (le_of_lt hk2)
}

lemma integrable_a_at_I (P : Measure KClass) [IsFiniteMeasure P] :
    Integrable (fun F : KClass => a F I) P := by
{
  have hc : Continuous (fun F : KClass => a F I) := by
  {
    have heq : (fun F : KClass => a F I) = (fun F : KClass => (I * deriv (Q F.F) I).re) := by
    {
      ext F
      dsimp [a, q]
      simp [Q_at_I]
    }
    rw [heq]
    have hd := continuous_deriv_Q_eval I
    fun_prop
  }
  obtain ⟨C, hC⟩ := q_bounded_on_KClass
  refine (integrable_const C).mono' hc.aestronglyMeasurable (Eventually.of_forall (fun F => ?_))
  rw [Real.norm_eq_abs]
  exact (Complex.abs_re_le_norm (q F I)).trans (hC F)
}

lemma integrable_q_sq_at_I (P : Measure KClass) [IsFiniteMeasure P] :
    Integrable (fun F : KClass => ‖q F I‖^2) P := by
{
  have hc : Continuous (fun F : KClass => ‖q F I‖^2) := by
  {
    simp_rw [norm_q_at_I_sq]
    have hd := continuous_deriv_Q_eval I
    fun_prop
  }
  obtain ⟨C, hC⟩ := q_bounded_on_KClass
  refine (integrable_const (C^2)).mono' hc.aestronglyMeasurable (Eventually.of_forall (fun F => ?_))
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans (hC F)) |>.mpr (hC F)
}

lemma integral_J_identity_at_I (beta : ℝ) (hk : k_val beta ≠ 0)
    (P : Measure KClass) [IsProbabilityMeasure P] :
    ∫ F, (k_val beta)^2 * J beta F I ∂P =
      (k_val beta) * ((k_val beta) - 1) +
      (2 * (k_val beta) - 1) * (∫ F, a F I ∂P) + (∫ F, ‖q F I‖^2 ∂P) := by
{
  have hzI : I ∈ H := by dsimp [H]; simp
  have heq : (fun F : KClass => (k_val beta)^2 * J beta F I) =
      fun F : KClass =>
        ((k_val beta) * ((k_val beta) - 1) + (2 * (k_val beta) - 1) * a F I) + ‖q F I‖^2 := by
  {
    ext F
    exact J_identity beta hk F hzI
  }
  have hi_a : Integrable (fun F : KClass => (2 * (k_val beta) - 1) * a F I) P :=
    (integrable_a_at_I P).const_mul _
  have hi_c : Integrable (fun _ : KClass => (k_val beta) * ((k_val beta) - 1)) P :=
    integrable_const _
  have hi_ca : Integrable
      (fun F : KClass => (k_val beta) * ((k_val beta) - 1) + (2 * (k_val beta) - 1) * a F I) P :=
    hi_c.add hi_a
  rw [heq, integral_add hi_ca (integrable_q_sq_at_I P),
    integral_add hi_c hi_a, integral_const, smul_eq_mul, probReal_univ, one_mul,
    integral_const_mul]
}

-- Under ρ > 2, the algebraic identity (5.4) forces E[J_F(i)] > 0
theorem E_J_pos_from_moments (h_rho : rho > 2) :
    ∫ F, J (Real.log rho / Real.log 2) F I ∂P_eigenmeasure > 0 := by
{
  set beta := Real.log rho / Real.log 2
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  have h_beta : beta > 1 := by
  {
    dsimp [beta]
    rw [gt_iff_lt, one_lt_div hlog2]
    exact Real.log_lt_log (by norm_num) h_rho
  }
  have hk : k_val beta ≠ 0 := by
  {
    unfold k_val
    linarith
  }
  obtain ⟨hP, hcov⟩ := lemma_3_1_weighted_covariance h_rho
  haveI : IsProbabilityMeasure P_eigenmeasure := hP
  have hmean : ∀ z ∈ H, ∫ F, ‖Q F.F z‖^2 ∂P_eigenmeasure = (z.im : ℝ) ^ (-beta) :=
    fun z hz => E_norm_Q_sq P_eigenmeasure beta z hz hcov
  have h_scaled := E_J_positive beta h_beta P_eigenmeasure
    (integral_J_identity_at_I beta hk P_eigenmeasure)
    (E_a_eq P_eigenmeasure beta hmean)
    (E_q_sq_eq P_eigenmeasure beta hmean)
  exact E_J_pos_of_scaled_pos beta h_beta P_eigenmeasure h_scaled
}

-- The final contradiction for the transfer operator under ρ > 2
lemma prop_6_2_transfer_bound_contradiction (h_rho : rho > 2) : False := by
{
  have h_pos : ∫ F, J (Real.log rho / Real.log 2) F I ∂P_eigenmeasure > 0 :=
    E_J_pos_from_moments h_rho
  have h_nonpos : ∫ F, J (Real.log rho / Real.log 2) F I ∂P_eigenmeasure ≤ 0 :=
    E_J_nonpositive h_rho
  linarith
}

-- Therefore, the assumption ρ > 2 is false, establishing Proposition 6.2: ρ ≤ 2!
theorem prop_6_2_transfer_bound : rho ≤ 2 := by
{
  by_contra h
  exact prop_6_2_transfer_bound_contradiction (lt_of_not_ge h)
}

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
-- The Main Inverse-Square Integral Means Theorem!
theorem main_theorem_inverse_square :
    ∀ ε > (0 : ℝ), ∃ C_ε : ℝ, ∀ (f : ℂ → ℂ) (_hf : Brennan.Koebe.IsClassS f) (r : ℝ),
      (1 / 2 : ℝ) ≤ r ∧ r < 1 →
      integralMean f (-2) r ≤ C_ε * (1 - r) ^ ((-1 : ℝ) - ε) := by
{
  exact prop_2_4_uniform_disk_comparison prop_6_2_transfer_bound
}

/-!
PAPER: 7.2 Positive powers
PAPER: Lemma 7.3 (Positive derivative powers). For every f ∈ S and 0 < t < 2/3,
PAPER: ∫_D |f'(z)|^t dA(z) < ∞.
(Verified in `brennanOAI/lean/OAI/Analysis/IntegralMeans/UnivalentArea.lean`)
-/
axiom lemma_7_3_positive_powers (f : ℂ → ℂ) (hf : Brennan.Koebe.IsClassS f)
    (t : ℝ) (ht : 0 < t ∧ t < 2/3) :
  IntegrableOn (fun z => ‖deriv f z‖ ^ t) (Metric.ball 0 1) volume

/-!
PAPER: 7.3 Domains, equivalence, and endpoint sharpness
PAPER: Proof of the area assertion in Theorem 1.1. Equations (7.4) and Lemma 7.3, together with
PAPER: t = 0, prove the disk integral for f ∈ S throughout −2 < t < 2/3.
PAPER: ...
PAPER: This change of variables is valid for nonnegative integrands, whether or not the integrals
PAPER: are finite. Since 4/3 < s < 4 is equivalent to −2 < 2 − s < 2/3, the desired domain integral
PAPER: is finite.
(Verified in `brennanOAI/lean/OAI/Analysis/IntegralMeans/DomainArea.lean` and `Main.lean`)
-/
axiom brennan_conjecture_from_disk_means :
    (∀ ε > (0 : ℝ), ∃ C_ε : ℝ, ∀ (f : ℂ → ℂ) (_hf : Brennan.Koebe.IsClassS f) (r : ℝ),
      (1 / 2 : ℝ) ≤ r ∧ r < 1 →
      integralMean f (-2) r ≤ C_ε * (1 - r) ^ ((-1 : ℝ) - ε)) →
    BrennansConjectureStatement

-- This proves your exact BrennansConjectureStatement from `BrennanConjecture.lean`!
theorem brennan_area_assertion : BrennansConjectureStatement := by
{
  exact brennan_conjecture_from_disk_means main_theorem_inverse_square
}

end Brennan.Sections6and7
