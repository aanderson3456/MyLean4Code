import Mathlib
import brennan.Section4_5
import brennan.Section6_Transport
import brennan.BrennanConjecture

open Complex Set MeasureTheory Topology Filter Function
open scoped ComplexConjugate Topology ENNReal

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
theorem E_J_nonpositive (h_rho : rho > 2) :
  ∫ F, J (Real.log rho / Real.log 2) F I ∂P_eigenmeasure ≤ 0 := by
{
  exact E_J_nonpositive_proof h_rho
}

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
    have hd := continuous_deriv_Q_eval (by dsimp [H]; simp : I ∈ H)
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
    have hd := continuous_deriv_Q_eval (by dsimp [H]; simp : I ∈ H)
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
-/

lemma polar_symm_circle (p : ℝ × ℝ) : Complex.polarCoord.symm p = circlePoint p.1 p.2 := by
{
  simp [Complex.polarCoord_symm_apply, circlePoint, Complex.exp_mul_I,
    ← Complex.ofReal_cos, ← Complex.ofReal_sin]
}

lemma disk_lintegral_le_polar (F : ℂ → ℝ≥0∞) :
    (∫⁻ z in disk, F z) ≤ ∫⁻ r in Ioo (0 : ℝ) 1,
      ENNReal.ofReal r * ∫⁻ θ in Ioo (-Real.pi) Real.pi, F (circlePoint r θ) := by
{
  have hm : MeasurableSet disk := Metric.isOpen_ball.measurableSet
  rw [← lintegral_indicator hm, ← Complex.lintegral_comp_polarCoord_symm]
  change (∫⁻ p in Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 * disk.indicator F (Complex.polarCoord.symm p)) ≤ _
  rw [← lintegral_indicator (measurableSet_Ioi.prod measurableSet_Ioo)]
  have he : (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi).indicator
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * disk.indicator F (Complex.polarCoord.symm p)) =
      (Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi).indicator
      (fun p : ℝ × ℝ => ENNReal.ofReal p.1 * F (circlePoint p.1 p.2)) := by
  {
    ext p
    simp_rw [polar_symm_circle]
    by_cases h0 : 0 < p.1
    · have hd : circlePoint p.1 p.2 ∈ disk ↔ p.1 < 1 := by
      {
        simp [disk, Brennan.Koebe.disk, circlePoint_norm, abs_of_pos h0]
      }
      by_cases h1 : p.1 < 1 <;> by_cases hθ : p.2 ∈ Ioo (-Real.pi) Real.pi <;>
        simp [Set.indicator, h0, h1, hθ, hd]
    · simp [Set.indicator, h0]
  }
  rw [he, lintegral_indicator (measurableSet_Ioo.prod measurableSet_Ioo)]
  change (∫⁻ p in Ioo (0 : ℝ) 1 ×ˢ Ioo (-Real.pi) Real.pi,
    ENNReal.ofReal p.1 * F (circlePoint p.1 p.2) ∂(volume.prod volume)) ≤ _
  rw [← Measure.prod_restrict]
  refine (lintegral_prod_le _).trans_eq ?_
  refine lintegral_congr (fun r => lintegral_const_mul' _ _ ENNReal.ofReal_ne_top)
}

lemma integrableOn_disk_of_circle_bound {F : ℂ → ℝ} (hF : ContinuousOn F disk)
    (hFn : ∀ z ∈ disk, 0 ≤ F z) {B : ℝ → ℝ}
    (hB : IntegrableOn B (Ioo (0 : ℝ) 1))
    (hBn : ∀ r ∈ Ioo (0 : ℝ) 1, 0 ≤ B r)
    (hbound : ∀ r ∈ Ioo (0 : ℝ) 1,
      (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) ≤ ENNReal.ofReal (B r)) :
    IntegrableOn F disk := by
{
  refine ⟨hF.aestronglyMeasurable Metric.isOpen_ball.measurableSet, ?_⟩
  have hn : ∀ᵐ z ∂(volume.restrict disk), 0 ≤ F z :=
    ae_restrict_of_forall_mem Metric.isOpen_ball.measurableSet hFn
  apply (hasFiniteIntegral_iff_ofReal hn).mpr
  refine lt_of_le_of_lt (disk_lintegral_le_polar (fun z => ENNReal.ofReal (F z))) ?_
  refine lt_of_le_of_lt ?_ hB.hasFiniteIntegral
  refine setLIntegral_mono' measurableSet_Ioo (fun r hr => ?_)
  calc
    ENNReal.ofReal r * (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) ≤
        ENNReal.ofReal r * ENNReal.ofReal (B r) := mul_le_mul' le_rfl (hbound r hr)
    _ ≤ ENNReal.ofReal (B r) := mul_le_of_le_one_left zero_le (by exact_mod_cast hr.2.le)
    _ = ‖B r‖ₑ := by rw [Real.enorm_eq_ofReal (hBn r hr)]
}

lemma circle_lintegral_eq {F : ℂ → ℝ} {r : ℝ}
    (hc : Continuous (fun θ : ℝ => F (circlePoint r θ)))
    (hn : ∀ θ, 0 ≤ F (circlePoint r θ)) :
    (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) =
      ENNReal.ofReal (∫ θ in -Real.pi..Real.pi, F (circlePoint r θ)) := by
{
  rw [restrict_Ioo_eq_restrict_Ioc, intervalIntegral.integral_of_le (by linarith [Real.pi_pos])]
  exact (ofReal_integral_eq_lintegral_ofReal
    (hc.continuousOn.integrableOn_Icc.mono_set Ioc_subset_Icc_self)
    (Eventually.of_forall hn)).symm
}

lemma continuousOn_deriv_univalent {f : ℂ → ℂ} (hf : UnivalentOn f disk) :
    ContinuousOn (deriv f) disk := by
{
  exact (hf.1.deriv Metric.isOpen_ball).continuousOn
}

lemma continuousOn_deriv_norm_rpow {f : ℂ → ℂ} (hf : UnivalentOn f disk) (t : ℝ) :
    ContinuousOn (fun z => ‖deriv f z‖ ^ t) disk := by
{
  refine (continuousOn_deriv_univalent hf).norm.rpow_const (fun z hz => ?_)
  exact Or.inl (norm_ne_zero_iff.mpr (deriv_ne_zero_of_univalentOn Metric.isOpen_ball hf hz))
}

lemma integrableOn_boundary_rpow {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun r : ℝ => (1 - r) ^ a) (Ioo (0 : ℝ) 1) := by
{
  have hi := (intervalIntegral.intervalIntegrable_rpow' (a := (0 : ℝ)) (b := (1 : ℝ)) ha).comp_sub_left 1
  have hi' : IntervalIntegrable (fun r : ℝ => (1 - r) ^ a) volume 0 1 := by
  {
    simpa using hi.symm
  }
  exact hi'.1.mono_set Ioo_subset_Ioc_self
}

lemma integrableOn_disk_of_power_circle_bound {F : ℂ → ℝ} (hF : ContinuousOn F disk)
    (hFn : ∀ z ∈ disk, 0 ≤ F z) {C a : ℝ} (hC : 0 ≤ C) (ha : -1 < a)
    (hbound : ∀ r : ℝ, 0 < r → r < 1 →
      (∫⁻ θ in Ioo (-Real.pi) Real.pi, ENNReal.ofReal (F (circlePoint r θ))) ≤
        ENNReal.ofReal (C * (1 - r) ^ a)) :
    IntegrableOn F disk := by
{
  exact integrableOn_disk_of_circle_bound hF hFn ((integrableOn_boundary_rpow ha).const_mul C)
    (fun r hr => mul_nonneg hC (Real.rpow_nonneg (by linarith [hr.2]) _))
    (fun r hr => hbound r hr.1 hr.2)
}

lemma integrableOn_disk_boundary_power {a : ℝ} (ha : -1 < a) :
    IntegrableOn (fun z : ℂ => (1 - ‖z‖) ^ a) disk := by
{
  have hc : ContinuousOn (fun z : ℂ => (1 - ‖z‖) ^ a) disk := by
  {
    refine (continuous_const.sub continuous_norm).continuousOn.rpow_const (fun z hz => ?_)
    exact Or.inl (ne_of_gt (sub_pos.mpr (by simpa [disk, Brennan.Koebe.disk] using hz)))
  }
  apply integrableOn_disk_of_power_circle_bound hc
    (fun z hz => Real.rpow_nonneg (sub_nonneg.mpr (le_of_lt (by simpa [disk, Brennan.Koebe.disk] using hz))) _)
    (C := 2 * Real.pi) (by positivity) ha
  intro r hr hr1
  have he : (fun θ : ℝ => (1 - ‖circlePoint r θ‖) ^ a) = fun _ => (1 - r) ^ a := by
  {
    ext θ
    rw [circlePoint_norm, abs_of_pos hr]
  }
  rw [circle_lintegral_eq (F := fun z => (1 - ‖z‖) ^ a) (r := r)
    (by rw [he]; exact continuous_const)
    (fun θ => Real.rpow_nonneg (by rw [circlePoint_norm, abs_of_pos hr]; linarith) _)]
  rw [he, intervalIntegral.integral_const]
  norm_num [smul_eq_mul]
  rw [show Real.pi + Real.pi = 2 * Real.pi by ring]
}

lemma integrableOn_geometric_product {A B F : ℂ → ℝ} {s : Set ℂ} (hs : MeasurableSet s)
    (hA : IntegrableOn A s) (hB : IntegrableOn B s) (hF : AEStronglyMeasurable F (volume.restrict s))
    {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1)
    (hAn : ∀ z ∈ s, 0 ≤ A z) (hBn : ∀ z ∈ s, 0 ≤ B z)
    (hEq : ∀ z ∈ s, F z = A z ^ q * B z ^ (1 - q)) : IntegrableOn F s := by
{
  apply ((hA.const_mul q).add (hB.const_mul (1 - q))).mono' hF
  refine ae_restrict_of_forall_mem hs (fun z hz => ?_)
  rw [hEq z hz, Real.norm_eq_abs, abs_of_nonneg (mul_nonneg
    (Real.rpow_nonneg (hAn z hz) _) (Real.rpow_nonneg (hBn z hz) _))]
  exact Real.geom_mean_le_arith_mean2_weighted hq (by linarith) (hAn z hz) (hBn z hz) (by ring)
}

lemma schlicht_growth_upper {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {z : ℂ} (hz : z ∈ disk) :
    ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖)^2 := by
{
  have hz' : ‖z‖ < 1 := by simpa [disk, Brennan.Koebe.disk] using hz
  exact (Brennan.Koebe.koebe_distortion_theorem f hf z hz').2.2.2
}

lemma schlicht_deriv_lower {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {z : ℂ} (hz : z ∈ disk) :
    (1 - ‖z‖) / (1 + ‖z‖)^3 ≤ ‖deriv f z‖ := by
{
  have hz' : ‖z‖ < 1 := by simpa [disk, Brennan.Koebe.disk] using hz
  exact (Brennan.Koebe.koebe_distortion_theorem f hf z hz').1
}

lemma rectangle_trace_periodic {g : ℝ × ℝ → ℝ} {R ε Y : ℝ}
    (hR : 0 ≤ R) (hεY : ε ≤ Y)
    (hg : ∀ p ∈ Icc (-R, ε) (R, Y), ContDiffAt ℝ 2 g p)
    (hside : ∀ y ∈ Icc ε Y,
      fderiv ℝ g (-R, y) (1, 0) = fderiv ℝ g (R, y) (1, 0)) :
    (∫ p in Icc (-R, ε) (R, Y), (p.2 - ε) * pairLaplacian g p) =
      (∫ x in -R..R, traceFluxY g ε (x, Y)) + ∫ x in -R..R, g (x, ε) := by
{
  have hb := rectangle_divergence_integral hR hεY hg
  have hsideint : (∫ y in ε..Y, traceFluxX g ε (R, y)) =
      ∫ y in ε..Y, traceFluxX g ε (-R, y) := by
  {
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    dsimp [traceFluxX]
    rw [hside y (by simpa only [uIcc_of_le hεY] using hy)]
  }
  rw [hsideint] at hb
  simpa only [traceFluxY, sub_self, zero_mul, zero_sub,
    intervalIntegral.integral_neg, sub_neg_eq_add, zero_add, add_zero, sub_zero,
    add_sub_cancel_right] using hb
}

lemma rectangle_restrict_open (a b c d : ℝ) :
    (volume : Measure (ℝ × ℝ)).restrict (Icc (a, c) (b, d)) =
      (volume : Measure (ℝ × ℝ)).restrict (Ioo a b ×ˢ Ioo c d) := by
{
  rw [Icc_prod_eq]
  change (volume.prod volume).restrict (Icc a b ×ˢ Icc c d) =
    (volume.prod volume).restrict (Ioo a b ×ˢ Ioo c d)
  rw [← Measure.prod_restrict, ← Measure.prod_restrict,
    restrict_Ioo_eq_restrict_Icc, restrict_Ioo_eq_restrict_Icc]
}

lemma rectangle_conformal_lintegral_le {F : ℂ → ℂ} {R ε Y : ℝ} (hε : 0 < ε)
    (hF : ∀ z : ℂ, 0 < z.im → DifferentiableAt ℂ F z)
    (hi : InjOn F {z : ℂ | -R < z.re ∧ z.re < R ∧ 0 < z.im}) (b : ℂ → ℝ≥0∞) :
    (∫⁻ p in Icc (-R, ε) (R, Y),
      ENNReal.ofReal (‖deriv F (Complex.equivRealProdCLM.symm p)‖^2) *
        b (F (Complex.equivRealProdCLM.symm p))) ≤ ∫⁻ w, b w := by
{
  rw [rectangle_restrict_open]
  let s : Set (ℝ × ℝ) := Ioo (-R) R ×ˢ Ioo ε Y
  let E := Complex.equivRealProdCLM
  have hs : MeasurableSet (E ⁻¹' s) :=
    (measurableSet_Ioo.prod measurableSet_Ioo).preimage E.continuous.measurable
  have he := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => ENNReal.ofReal (‖deriv F (E.symm p)‖^2) * b (F (E.symm p))) s
  have hh : (∫⁻ p in s, ENNReal.ofReal (‖deriv F (E.symm p)‖^2) * b (F (E.symm p))) =
      ∫⁻ z in E ⁻¹' s, ENNReal.ofReal (‖deriv F z‖^2) * b (F z) := by
  {
    rw [← he]
    refine lintegral_congr (fun z => ?_)
    change ENNReal.ofReal (‖deriv F (E.symm (E z))‖^2) * b (F (E.symm (E z))) = _
    rw [E.symm_apply_apply]
  }
  change (∫⁻ p in s, ENNReal.ofReal (‖deriv F (E.symm p)‖^2) * b (F (E.symm p))) ≤ _
  rw [hh]
  apply conformal_lintegral_le hs
  · intro z hz
    exact hF z (hε.trans hz.2.1)
  · apply hi.mono
    intro z hz
    exact ⟨hz.1.1, hz.1.2, hε.trans hz.2.1⟩
}

lemma periodic_box_pointwise_le {F : ℂ → ℂ} {ψ b : ℂ → ℝ} {K ε : ℝ}
    (hlap : ∀ z : ℂ, 0 < z.im → z.im ≤ 1 →
      0 ≤ complexLaplacian (ψ ∘ F) z ∧
      z.im * complexLaplacian (ψ ∘ F) z ≤ K * ‖deriv F z‖^2 * b (F z))
    (hε : 0 < ε) (hK : 0 ≤ K) {p : ℝ × ℝ} (hp : p ∈ Icc (-Real.pi, ε) (Real.pi, (1 : ℝ))) :
    ENNReal.ofReal ((p.2 - ε) * pairLaplacian ((ψ ∘ F) ∘ Complex.equivRealProdCLM.symm) p) ≤
      ENNReal.ofReal K * (ENNReal.ofReal (‖deriv F (Complex.equivRealProdCLM.symm p)‖^2) *
        ENNReal.ofReal (b (F (Complex.equivRealProdCLM.symm p)))) := by
{
  have hx := hlap (Complex.equivRealProdCLM.symm p) (hε.trans_le hp.1.2) hp.2.2
  have him : (Complex.equivRealProdCLM.symm p).im = p.2 := rfl
  rw [him] at hx; rw [← ENNReal.ofReal_mul (sq_nonneg _), ← ENNReal.ofReal_mul hK]
  apply ENNReal.ofReal_le_ofReal; rw [pairLaplacian_complex, ← mul_assoc]
  exact (mul_le_mul_of_nonneg_right (by linarith) hx.1).trans hx.2
}

lemma periodic_box_laplacian_integral_le {F : ℂ → ℂ} {ψ b : ℂ → ℝ} {K ε : ℝ}
    (hF : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ F z)
    (hi : InjOn F {z : ℂ | -Real.pi < z.re ∧ z.re < Real.pi ∧ 0 < z.im})
    (hψ : ContDiff ℝ 2 ψ) (hb : Integrable b) (hbn : ∀ w, 0 ≤ b w) (hK : 0 ≤ K)
    (hlap : ∀ z : ℂ, 0 < z.im → z.im ≤ 1 →
      0 ≤ complexLaplacian (ψ ∘ F) z ∧
      z.im * complexLaplacian (ψ ∘ F) z ≤ K * ‖deriv F z‖^2 * b (F z))
    (hε : 0 < ε) :
    (∫ p in Icc (-Real.pi, ε) (Real.pi, (1 : ℝ)),
      (p.2 - ε) * pairLaplacian ((ψ ∘ F) ∘ Complex.equivRealProdCLM.symm) p) ≤
      K * ∫ w, b w := by
{
  let E := Complex.equivRealProdCLM.symm; let g := (ψ ∘ F) ∘ E
  let S := Icc (-Real.pi, ε) (Real.pi, (1 : ℝ))
  let U : ℝ × ℝ → ℝ := fun p => (p.2 - ε) * pairLaplacian g p
  have hbox (p : ℝ × ℝ) (hp : p ∈ S) : ContDiffAt ℝ 2 g p :=
    (hψ.contDiffAt.comp _ ((hF (E p) (hε.trans_le hp.1.2)).contDiffAt.restrict_scalars ℝ)).comp _
      E.contDiff.contDiffAt
  have hUi : IntegrableOn U S :=
    ContinuousOn.integrableOn_compact isCompact_Icc (fun p hp =>
      ContinuousAt.continuousWithinAt ((continuous_snd.continuousAt.sub_const ε).mul
        (continuousAt_pairLaplacian (hbox p hp))))
  have hUn (p : ℝ × ℝ) (hp : p ∈ S) : 0 ≤ U p := by
  {
    dsimp [U, g, E]; rw [pairLaplacian_complex]
    exact mul_nonneg (by linarith [hp.1.2]) (hlap _ (hε.trans_le hp.1.2) hp.2.2).1
  }
  have he := ofReal_integral_eq_lintegral_ofReal hUi (ae_restrict_of_forall_mem measurableSet_Icc hUn)
  have hb' := ofReal_integral_eq_lintegral_ofReal hb (Eventually.of_forall hbn)
  have hL : (∫⁻ p in S, ENNReal.ofReal (U p)) ≤ ENNReal.ofReal (K * ∫ w, b w) := by
  {
    calc
      _ ≤ ∫⁻ p in S, ENNReal.ofReal K *
          (ENNReal.ofReal (‖deriv F (E p)‖^2) * ENNReal.ofReal (b (F (E p)))) :=
        setLIntegral_mono' measurableSet_Icc (fun p hp => periodic_box_pointwise_le hlap hε hK hp)
      _ = ENNReal.ofReal K * ∫⁻ p in S,
          ENNReal.ofReal (‖deriv F (E p)‖^2) * ENNReal.ofReal (b (F (E p))) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ ENNReal.ofReal K * ∫⁻ w, ENNReal.ofReal (b w) :=
        mul_le_mul' le_rfl (rectangle_conformal_lintegral_le hε
          (fun z hz => (hF z hz).differentiableAt) hi (fun w => ENNReal.ofReal (b w)))
      _ = ENNReal.ofReal (K * ∫ w, b w) := by rw [← hb', ENNReal.ofReal_mul hK]
  }
  rw [← he] at hL
  exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK (integral_nonneg hbn))).mp hL
}

lemma neg_traceFluxY_le {g : ℝ × ℝ → ℝ} {ε x : ℝ} (hε : 0 < ε) (hε1 : ε ≤ 1) :
    -traceFluxY g ε (x, 1) ≤ |g (x, 1)| + |fderiv ℝ g (x, 1) (0, 1)| := by
{
  dsimp [traceFluxY]
  have hmul : -(1 - ε) * fderiv ℝ g (x, 1) (0, 1) ≤ |fderiv ℝ g (x, 1) (0, 1)| := by
  {
    calc
      _ = (1 - ε) * (-fderiv ℝ g (x, 1) (0, 1)) := by ring
      _ ≤ (1 - ε) * |fderiv ℝ g (x, 1) (0, 1)| :=
        mul_le_mul_of_nonneg_left (neg_le_abs _) (by linarith)
      _ ≤ |fderiv ℝ g (x, 1) (0, 1)| := mul_le_of_le_one_left (abs_nonneg _) (by linarith)
  }
  linarith [le_abs_self (g (x, 1))]
}

lemma periodic_conformal_trace_bounded {F : ℂ → ℂ} {ψ b : ℂ → ℝ} {K : ℝ}
    (hF : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ F z)
    (hi : InjOn F {z : ℂ | -Real.pi < z.re ∧ z.re < Real.pi ∧ 0 < z.im})
    (hψ : ContDiff ℝ 2 ψ) (hb : Integrable b) (hbn : ∀ w, 0 ≤ b w) (hK : 0 ≤ K)
    (hside : ∀ y : ℝ, 0 < y →
      fderiv ℝ ((ψ ∘ F) ∘ Complex.equivRealProdCLM.symm) (-Real.pi, y) (1, 0) =
      fderiv ℝ ((ψ ∘ F) ∘ Complex.equivRealProdCLM.symm) (Real.pi, y) (1, 0))
    (hlap : ∀ z : ℂ, 0 < z.im → z.im ≤ 1 →
      0 ≤ complexLaplacian (ψ ∘ F) z ∧
      z.im * complexLaplacian (ψ ∘ F) z ≤ K * ‖deriv F z‖^2 * b (F z)) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      (∫ x in -Real.pi..Real.pi, ψ (F (x + ε * I))) ≤ C := by
{
  let E := Complex.equivRealProdCLM.symm; let g := (ψ ∘ F) ∘ E
  have hg (p : ℝ × ℝ) (hp : 0 < p.2) : ContDiffAt ℝ 2 g p :=
    (hψ.contDiffAt.comp _ ((hF (E p) hp).contDiffAt.restrict_scalars ℝ)).comp _ E.contDiff.contDiffAt
  have hc (x : ℝ) : ContinuousAt (fun x : ℝ => g (x, 1)) x :=
    (hg (x, 1) zero_lt_one).continuousAt.comp (f := fun v : ℝ => (v, (1 : ℝ)))
      (continuous_id.prodMk continuous_const).continuousAt
  have hd (x : ℝ) : ContinuousAt (fun x : ℝ => fderiv ℝ g (x, 1) (0, 1)) x :=
    (((hg (x, 1) zero_lt_one).fderiv_right (m := 0) (by norm_num)).continuousAt.comp
      (f := fun v : ℝ => (v, (1 : ℝ)))
      (continuous_id.prodMk continuous_const).continuousAt).clm_apply continuousAt_const
  let A : ℝ := ∫ x in -Real.pi..Real.pi, |g (x, 1)| + |fderiv ℝ g (x, 1) (0, 1)|
  have hAint : IntervalIntegrable (fun x : ℝ => |g (x, 1)| + |fderiv ℝ g (x, 1) (0, 1)|)
      volume (-Real.pi) Real.pi :=
    ((continuous_iff_continuousAt.mpr hc).abs.add (continuous_iff_continuousAt.mpr hd).abs).intervalIntegrable _ _
  refine ⟨K * (∫ w, b w) + A, fun ε hε hε1 => ?_⟩
  have hIle := periodic_box_laplacian_integral_le hF hi hψ hb hbn hK hlap hε
  have ht := rectangle_trace_periodic Real.pi_pos.le hε1
    (fun p hp => hg p (hε.trans_le hp.1.2)) (fun y hy => hside y (hε.trans_le hy.1))
  have htop : -(∫ x in -Real.pi..Real.pi, traceFluxY g ε (x, 1)) ≤ A := by
  {
    rw [← intervalIntegral.integral_neg]
    have htopc : Continuous (fun x : ℝ => -traceFluxY g ε (x, 1)) := by
    {
      simp only [traceFluxY]
      exact ((continuous_const.mul (continuous_iff_continuousAt.mpr hd)).sub
        (continuous_iff_continuousAt.mpr hc)).neg
    }
    exact intervalIntegral.integral_mono_on (by linarith [Real.pi_pos])
      (htopc.intervalIntegrable _ _) hAint (fun x _ => neg_traceFluxY_le hε hε1)
  }
  have hid : (∫ x in -Real.pi..Real.pi, ψ (F (x + ε * I))) = ∫ x in -Real.pi..Real.pi, g (x, ε) :=
    intervalIntegral.integral_congr (fun x _ => by
      simp only [g, E, Function.comp_apply, Complex.equivRealProdCLM_symm_apply])
  rw [hid]; dsimp only [g, E] at ht htop; linarith
}

def logDisk (z : ℂ) : ℂ := Complex.exp (z * I)

lemma logDisk_norm (z : ℂ) : ‖logDisk z‖ = Real.exp (-z.im) := by
{
  simp [logDisk, Complex.norm_exp]
}

lemma logDisk_mem_disk {z : ℂ} (hz : 0 < z.im) : logDisk z ∈ disk := by
{
  simp only [disk, Brennan.Koebe.disk, Metric.mem_ball, dist_zero_right, logDisk_norm]
  exact Real.exp_lt_one_iff.mpr (by linarith)
}

lemma logDisk_analytic (z : ℂ) : AnalyticAt ℂ logDisk z := by
{
  exact analyticAt_cexp.comp (analyticAt_id.mul analyticAt_const)
}

lemma logDisk_injOn : InjOn logDisk {z : ℂ | -Real.pi < z.re ∧ z.re < Real.pi} := by
{
  intro z hz w hw h
  have he := Complex.exp_inj_of_neg_pi_lt_of_le_pi
    (by simpa using hz.1 : -Real.pi < (z * I).im)
    (by simpa using hz.2.le : (z * I).im ≤ Real.pi)
    (by simpa using hw.1 : -Real.pi < (w * I).im)
    (by simpa using hw.2.le : (w * I).im ≤ Real.pi) h
  exact mul_right_cancel₀ Complex.I_ne_zero he
}

lemma logDisk_realProd (x y : ℝ) :
    logDisk (Complex.equivRealProdCLM.symm (x, y)) = circlePoint (Real.exp (-y)) x := by
{
  rw [logDisk, Complex.equivRealProdCLM_symm_apply]
  have he : ((x : ℂ) + y * I) * I = (-y : ℂ) + (x : ℂ) * I := by
  {
    rw [add_mul, mul_assoc, Complex.I_mul_I]
    ring
  }
  rw [he, Complex.exp_add, ← Complex.ofReal_neg, ← Complex.ofReal_exp]
  rfl
}

lemma logDisk_periodic (z : ℂ) : logDisk (z + 2 * Real.pi) = logDisk z := by
{
  simp only [logDisk, add_mul, Complex.exp_add, Complex.exp_two_pi_mul_I, mul_one]
}

lemma logStrip_smooth_periodic_side (H_fn : ℂ → ℝ) (y : ℝ) :
    fderiv ℝ ((H_fn ∘ logDisk) ∘ Complex.equivRealProdCLM.symm) (-Real.pi, y) (1, 0) =
      fderiv ℝ ((H_fn ∘ logDisk) ∘ Complex.equivRealProdCLM.symm) (Real.pi, y) (1, 0) := by
{
  let g := (H_fn ∘ logDisk) ∘ Complex.equivRealProdCLM.symm
  have he : (fun p : ℝ × ℝ => g (p + (2 * Real.pi, 0))) = g := by
  {
    ext p
    dsimp [g]
    have hz : Complex.equivRealProdCLM.symm ((p.1, p.2) + (2 * Real.pi, 0)) =
        Complex.equivRealProdCLM.symm p + 2 * Real.pi := by
    {
      simp [Complex.equivRealProdCLM_symm_apply]
      ring
    }
    rw [hz, logDisk_periodic]
  }
  have hd := congrArg (fun L : (ℝ × ℝ) →L[ℝ] ℝ => L (1, 0))
    (fderiv_comp_add_right (𝕜 := ℝ) (f := g) (x := (-Real.pi, y)) (2 * Real.pi, 0))
  rw [he] at hd
  have hp : (-Real.pi, y) + (2 * Real.pi, 0) = (Real.pi, y) := by
  {
    ext <;> dsimp <;> ring
  }
  simpa only [hp] using hd
}

lemma exp_boundary_lower {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) : y / 2 ≤ 1 - Real.exp (-y) := by
{
  have he := Real.add_one_le_exp y
  have hp := Real.exp_pos y
  rw [Real.exp_neg y]
  have hi : (Real.exp y)⁻¹ ≤ (1 + y)⁻¹ := inv_anti₀ (by linarith) (by linarith)
  have hden : 0 < 1 + y := by linarith
  have hf : y / 2 ≤ 1 - (1 + y)⁻¹ := by
  {
    rw [inv_eq_one_div]
    have hh : 1 / (1 + y) ≤ 1 - y / 2 := (div_le_iff₀ hden).mpr (by nlinarith)
    linarith
  }
  linarith
}

lemma logStrip_height_bound {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {z : ℂ}
    (hz : 0 < z.im) (hz1 : z.im ≤ 1) :
    z.im ≤ 3 * (1 + ‖f (logDisk z)‖^2) ^ (-1 / 4 : ℝ) := by
{
  let y := z.im
  let r := Real.exp (-y)
  have hy : 0 < y := hz
  have hyr : r < 1 := Real.exp_lt_one_iff.mpr (by dsimp [y]; linarith)
  have hg := schlicht_growth_upper hf (logDisk_mem_disk hz)
  rw [logDisk_norm] at hg
  change ‖f (logDisk z)‖ ≤ r / (1 - r)^2 at hg
  have hb : ‖f (logDisk z)‖ ≤ 4 / y^2 := by
  {
    have hyb : y / 2 ≤ 1 - r := exp_boundary_lower hy hz1
    calc
      ‖f (logDisk z)‖ ≤ r / (1 - r)^2 := hg
      _ ≤ 1 / (y / 2)^2 := div_le_div₀ (by norm_num) hyr.le (by positivity) (by nlinarith)
      _ = 4 / y^2 := by field_simp; ring
  }
  have hy4 : y^4 ≤ 1 := pow_le_one₀ hy.le hz1
  have hs : (1 + ‖f (logDisk z)‖^2) * y^4 ≤ 17 := by
  {
    have hb' : ‖f (logDisk z)‖ * y^2 ≤ 4 := (le_div_iff₀ (sq_pos_of_pos hy)).mp hb
    have hsquare := pow_le_pow_left₀ (by positivity : 0 ≤ ‖f (logDisk z)‖ * y^2) hb' 2
    nlinarith [hsquare]
  }
  have hbase : 0 < 1 + ‖f (logDisk z)‖^2 := by positivity
  have hpow := Real.rpow_le_rpow (by positivity : 0 ≤ (1 + ‖f (logDisk z)‖^2) * y^4) hs (by norm_num : (0 : ℝ) ≤ 1 / 4)
  rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast y 4,
    ← Real.rpow_mul hy.le] at hpow
  norm_num at hpow
  have h17 : (17 : ℝ) ^ (1 / 4 : ℝ) ≤ 3 := by
  {
    calc
      (17 : ℝ) ^ (1 / 4 : ℝ) ≤ (81 : ℝ) ^ (1 / 4 : ℝ) := Real.rpow_le_rpow (by norm_num) (by norm_num) (by norm_num)
      _ = 3 := by rw [show (81 : ℝ) = 3 ^ (4 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]; norm_num
  }
  have hmul : y * (1 + ‖f (logDisk z)‖^2) ^ (1 / 4 : ℝ) ≤ 3 := by nlinarith
  have hpos := Real.rpow_pos_of_pos hbase (1 / 4 : ℝ)
  rw [show (-1 / 4 : ℝ) = -(1 / 4) by ring, Real.rpow_neg hbase.le, ← div_eq_mul_inv]
  exact (le_div_iff₀ hpos).mpr hmul
}

def bracketSq (z : ℂ) : ℝ := 1 + z.re^2 + z.im^2

def smoothPower (q : ℝ) (z : ℂ) : ℝ := bracketSq z ^ q

lemma bracketSq_eq (z : ℂ) : bracketSq z = 1 + ‖z‖^2 := by
{
  rw [Complex.sq_norm]
  simp [bracketSq, Complex.normSq_apply, pow_two, add_assoc]
}

lemma bracketSq_pos (z : ℂ) : 0 < bracketSq z := by
{
  rw [bracketSq_eq]
  positivity
}

lemma bracketSq_contDiff (n : ℕ∞) : ContDiff ℝ n bracketSq := by
{
  exact (contDiff_const.add (Complex.reCLM.contDiff.pow 2)).add (Complex.imCLM.contDiff.pow 2)
}

lemma smoothPower_contDiff (q : ℝ) (n : ℕ∞) : ContDiff ℝ n (smoothPower q) := by
{
  exact (bracketSq_contDiff n).rpow_const_of_ne (fun z => (bracketSq_pos z).ne')
}

def bracketSqDeriv (z : ℂ) : ℂ →L[ℝ] ℝ :=
  (2 * z.re) • Complex.reCLM + (2 * z.im) • Complex.imCLM

lemma bracketSq_hasFDerivAt (z : ℂ) : HasFDerivAt bracketSq (bracketSqDeriv z) z := by
{
  have h := (((Complex.reCLM.hasFDerivAt (x := z)).pow 2).const_add 1).add
    ((Complex.imCLM.hasFDerivAt (x := z)).pow 2)
  convert! h using 1
  simp [bracketSqDeriv]
}

lemma smoothPower_hasFDerivAt (q : ℝ) (z : ℂ) :
    HasFDerivAt (smoothPower q) ((q * bracketSq z ^ (q - 1)) • bracketSqDeriv z) z := by
{
  exact (bracketSq_hasFDerivAt z).rpow_const (Or.inl (bracketSq_pos z).ne')
}

lemma bracketSqDeriv_hasFDerivAt (z : ℂ) : HasFDerivAt bracketSqDeriv
    ((ContinuousLinearMap.smulRight Complex.reCLM (2 • Complex.reCLM)) +
      (ContinuousLinearMap.smulRight Complex.imCLM (2 • Complex.imCLM))) z := by
{
  have h := (((Complex.reCLM.hasFDerivAt (x := z)).const_mul 2).smul_const Complex.reCLM).add
    (((Complex.imCLM.hasFDerivAt (x := z)).const_mul 2).smul_const Complex.imCLM)
  convert! h using 1
  ext v w
  simp [ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  ring
}

lemma smoothPower_secondReal (q : ℝ) (z u v : ℂ) :
    secondReal (smoothPower q) z u v =
      q * (q - 1) * bracketSq z ^ (q - 2) * (2 * z.re * u.re + 2 * z.im * u.im) * (2 * z.re * v.re + 2 * z.im * v.im) +
        q * bracketSq z ^ (q - 1) * (2 * u.re * v.re + 2 * u.im * v.im) := by
{
  have he : fderiv ℝ (smoothPower q) = fun z => (q * bracketSq z ^ (q - 1)) • bracketSqDeriv z :=
    funext (fun z => (smoothPower_hasFDerivAt q z).fderiv)
  have hscalar := ((bracketSq_hasFDerivAt z).rpow_const (p := q - 1) (Or.inl (bracketSq_pos z).ne')).const_mul q
  have hd := (hscalar.smul (bracketSqDeriv_hasFDerivAt z)).fderiv
  change fderiv ℝ (fun z => (q * bracketSq z ^ (q - 1)) • bracketSqDeriv z) z = _ at hd
  rw [secondReal, he, hd]
  simp [bracketSqDeriv, ContinuousLinearMap.smulRight_apply, smul_eq_mul, show q - 1 - 1 = q - 2 by ring]
  ring
}

lemma laplacian_smoothPower (q : ℝ) (z : ℂ) :
    complexLaplacian (smoothPower q) z =
      4 * q * bracketSq z ^ (q - 2) * (1 + q * ‖z‖^2) := by
{
  rw [complexLaplacian, smoothPower_secondReal, smoothPower_secondReal]
  have he : bracketSq z ^ (q - 1) = bracketSq z ^ (q - 2) * bracketSq z := by
  {
    simpa only [show q - 2 + 1 = q - 1 by ring, Real.rpow_one] using Real.rpow_add (bracketSq_pos z) (q - 2) 1
  }
  rw [he, Complex.sq_norm]
  simp [Complex.normSq_apply, bracketSq]
  ring
}

lemma laplacian_smoothPower_bounds {q : ℝ} (hq : 0 ≤ q) (hq1 : q ≤ 1) (z : ℂ) :
    0 ≤ complexLaplacian (smoothPower q) z ∧
      complexLaplacian (smoothPower q) z ≤ 4 * q * bracketSq z ^ (q - 1) := by
{
  have hz := bracketSq_pos z
  rw [laplacian_smoothPower]
  constructor
  · positivity
  · have he : bracketSq z ^ (q - 1) = bracketSq z ^ (q - 2) * bracketSq z := by
    {
      simpa only [show q - 2 + 1 = q - 1 by ring, Real.rpow_one] using Real.rpow_add (bracketSq_pos z) (q - 2) 1
    }
    rw [he, ← mul_assoc]
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    rw [bracketSq_eq]
    nlinarith [sq_nonneg ‖z‖]
}

lemma bracketSq_decay_integrable {q : ℝ} (hq : q < 1 / 4) :
    Integrable (fun z : ℂ => bracketSq z ^ (q - 5 / 4)) := by
{
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 5 / 2 - 2 * q)
    (by norm_num [Complex.finrank_real_complex]; linarith)
  convert! h using 1
  ext z
  rw [bracketSq_eq]
  congr 1
  ring
}

lemma schlicht_smooth_trace {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {q : ℝ}
    (hq : 0 < q) (hq4 : q < 1 / 4) :
    ∃ C : ℝ, ∀ y : ℝ, 0 < y → y ≤ 1 →
      (∫ x in -Real.pi..Real.pi, smoothPower q (f (logDisk (x + y * I)))) ≤ C := by
{
  let F : ℂ → ℂ := f ∘ logDisk
  have hF (z : ℂ) (hz : 0 < z.im) : AnalyticAt ℂ F z :=
    ((hf.1.analyticOnNhd Metric.isOpen_ball _ (logDisk_mem_disk hz)).comp (logDisk_analytic z))
  apply periodic_conformal_trace_bounded (F := F) (ψ := smoothPower q)
    (b := fun w => bracketSq w ^ (q - 5 / 4)) (K := 12 * q) hF
  · intro z hz w hw he
    apply logDisk_injOn ⟨hz.1, hz.2.1⟩ ⟨hw.1, hw.2.1⟩
    exact hf.2.1 (logDisk_mem_disk hz.2.2) (logDisk_mem_disk hw.2.2) he
  · exact smoothPower_contDiff q 2
  · exact bracketSq_decay_integrable hq4
  · intro w
    exact Real.rpow_nonneg (bracketSq_pos w).le _
  · positivity
  · intro y _hy
    exact logStrip_smooth_periodic_side (smoothPower q ∘ f) y
  · intro z hz hz1
    rw [laplacian_holomorphic_comp (smoothPower_contDiff q 2).contDiffAt (hF z hz)]
    have hl := laplacian_smoothPower_bounds hq.le (by linarith) (F z)
    have hy := logStrip_height_bound hf hz hz1
    rw [← bracketSq_eq] at hy
    change z.im ≤ 3 * bracketSq (F z) ^ (-1 / 4 : ℝ) at hy
    constructor
    · exact mul_nonneg (sq_nonneg _) hl.1
    · calc
        _ ≤ (3 * bracketSq (F z) ^ (-1 / 4 : ℝ)) * (‖deriv F z‖^2 * (4 * q * bracketSq (F z) ^ (q - 1))) :=
          mul_le_mul hy (mul_le_mul_of_nonneg_left hl.2 (sq_nonneg _))
            (mul_nonneg (sq_nonneg _) hl.1) (mul_nonneg (by norm_num) (Real.rpow_nonneg (bracketSq_pos _).le _))
        _ = (12 * q * ‖deriv F z‖^2) * (bracketSq (F z) ^ (-1 / 4 : ℝ) * bracketSq (F z) ^ (q - 1)) := by ring
        _ = _ := by
          rw [← Real.rpow_add (bracketSq_pos _)]
          congr 2
          ring
}

lemma continuous_circle_smoothPower {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) (q r : ℝ)
    (hr : 0 ≤ r) (hr1 : r < 1) : Continuous (fun θ => smoothPower q (f (circlePoint r θ))) := by
{
  apply (smoothPower_contDiff q 0).continuous.comp
  apply hf.1.continuousOn.comp_continuous (continuous_circlePoint r)
  intro θ
  simpa only [disk, Brennan.Koebe.disk, Metric.mem_ball, dist_zero_right,
    circlePoint_norm, abs_of_nonneg hr] using hr1
}

lemma schlicht_smooth_means {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {q : ℝ}
    (hq : 0 < q) (hq4 : q < 1 / 4) :
    ∃ C : ℝ, 0 < C ∧ ∀ r : ℝ, 0 < r → r < 1 →
      (∫ θ in -Real.pi..Real.pi, smoothPower q (f (circlePoint r θ))) ≤ C := by
{
  obtain ⟨C, hC⟩ := schlicht_smooth_trace hf hq hq4
  refine ⟨|C| + 2 * Real.pi * (5 : ℝ) ^ q + 1, by positivity, fun r hr hr1 => ?_⟩
  by_cases hrh : r ≤ 1 / 2
  · have hb (θ : ℝ) : smoothPower q (f (circlePoint r θ)) ≤ (5 : ℝ) ^ q := by
    {
      have hm : circlePoint r θ ∈ disk := by
        simpa [disk, Brennan.Koebe.disk, circlePoint_norm, abs_of_pos hr] using hr1
      have hg := schlicht_growth_upper hf hm; rw [circlePoint_norm, abs_of_pos hr] at hg
      have hv : ‖f (circlePoint r θ)‖ ≤ 2 :=
        hg.trans ((div_le_iff₀ (sq_pos_of_pos (by linarith))).mpr (by nlinarith))
      apply Real.rpow_le_rpow (bracketSq_pos _).le _ hq.le
      rw [bracketSq_eq]; nlinarith [norm_nonneg (f (circlePoint r θ))]
    }
    have hi := intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos])
      ((continuous_circle_smoothPower hf q r hr.le hr1).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume)) (fun θ _ => hb θ)
    simp only [intervalIntegral.integral_const, smul_eq_mul] at hi
    nlinarith [abs_nonneg C]
  · let y := -Real.log r
    have hy : 0 < y := neg_pos.mpr (Real.log_neg hr hr1)
    have hy1 : y ≤ 1 := by
    {
      have hexp : Real.exp (-1) ≤ (1 / 2 : ℝ) := by
      {
        rw [Real.exp_neg]; have he := Real.add_one_le_exp (1 : ℝ)
        exact inv_le_comm₀ (Real.exp_pos _) (by norm_num) |>.mpr (by norm_num; linarith)
      }
      have hlog : -1 ≤ Real.log r := (Real.le_log_iff_exp_le hr).mpr (hexp.trans (by linarith))
      dsimp [y]; linarith
    }
    have he (x : ℝ) : logDisk ((x : ℂ) + y * I) = circlePoint r x := by
    {
      have hh := logDisk_realProd x y; rw [Complex.equivRealProdCLM_symm_apply] at hh
      simpa only [y, neg_neg, Real.exp_log hr] using hh
    }
    have hs := hC y hy hy1; simp_rw [he] at hs
    have hn : 0 ≤ 2 * Real.pi * (5 : ℝ) ^ q := by positivity
    linarith [le_abs_self C]
}

lemma schlicht_bracketSq_growth {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {z : ℂ} (hz : z ∈ disk) :
    bracketSq (f z) ≤ 2 * (1 - ‖z‖) ^ (-4 : ℝ) := by
{
  have hr : ‖z‖ < 1 := by simpa [disk, Brennan.Koebe.disk] using hz
  have hd : 0 < 1 - ‖z‖ := by linarith
  have hg := schlicht_growth_upper hf hz
  have hb : ‖f z‖ ≤ 1 / (1 - ‖z‖)^2 := hg.trans (div_le_div_of_nonneg_right hr.le (sq_nonneg _))
  have hs := pow_le_pow_left₀ (norm_nonneg _) hb 2
  have hδ : (1 - ‖z‖)^4 ≤ 1 := pow_le_one₀ hd.le (by nlinarith [norm_nonneg z])
  rw [bracketSq_eq, Real.rpow_neg hd.le]
  norm_num only [Real.rpow_ofNat]
  rw [inv_eq_one_div]
  have hdiv : (1 / (1 - ‖z‖)^2)^2 = 1 / (1 - ‖z‖)^4 := by field_simp
  rw [hdiv] at hs
  have hh : 1 ≤ 1 / (1 - ‖z‖)^4 := (le_div_iff₀ (pow_pos hd _)).mpr (by simpa using hδ)
  linarith
}

lemma continuousOn_smoothPower_comp {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) (a : ℝ) :
    ContinuousOn (fun z => smoothPower a (f z)) disk := by
{
  exact (smoothPower_contDiff a 0).continuous.comp_continuousOn hf.1.continuousOn
}

lemma schlicht_circle_power_mono_gt {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f)
    {a q r : ℝ} (haqp : 0 < a - q) (hr : 0 < r) (hr1 : r < 1) :
    (∫ θ in -Real.pi..Real.pi, bracketSq (f (circlePoint r θ)) ^ a) ≤
      ((2 : ℝ) ^ (a - q) * (1 - r) ^ (-4 * (a - q))) *
        ∫ θ in -Real.pi..Real.pi, smoothPower q (f (circlePoint r θ)) := by
{
  have hd : 0 < 1 - r := by linarith
  have hm : IntervalIntegrable (fun θ => bracketSq (f (circlePoint r θ)) ^ a) volume (-Real.pi) Real.pi :=
    (continuous_circle_smoothPower hf a r hr.le hr1).intervalIntegrable _ _
  have hqn : IntervalIntegrable (fun θ => smoothPower q (f (circlePoint r θ))) volume (-Real.pi) Real.pi :=
    (continuous_circle_smoothPower hf q r hr.le hr1).intervalIntegrable _ _
  rw [← intervalIntegral.integral_const_mul]
  refine intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi)
    (by linarith [Real.pi_pos]) hm (hqn.const_mul _) (fun θ _ => ?_)
  have hz : circlePoint r θ ∈ disk := by
  {
    simpa [disk, Brennan.Koebe.disk, circlePoint_norm, abs_of_pos hr] using hr1
  }
  have hg := schlicht_bracketSq_growth hf hz
  rw [circlePoint_norm, abs_of_pos hr] at hg
  have hp := Real.rpow_le_rpow (bracketSq_pos _).le hg haqp.le
  rw [Real.mul_rpow (by norm_num) (Real.rpow_nonneg hd.le _), ← Real.rpow_mul hd.le] at hp
  calc
    _ = bracketSq (f (circlePoint r θ)) ^ (a - q) * bracketSq (f (circlePoint r θ)) ^ q := by
      rw [← Real.rpow_add (bracketSq_pos _), sub_add_cancel]
    _ ≤ _ := mul_le_mul_of_nonneg_right hp (Real.rpow_nonneg (bracketSq_pos _).le _)
}

lemma schlicht_function_area {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {a : ℝ} (ha : a < 1 / 2) :
    IntegrableOn (fun z => bracketSq (f z) ^ a) disk := by
{
  obtain ⟨q, hq0, hq4⟩ := exists_between (show max (0 : ℝ) (a - 1 / 4) < 1 / 4 by
    exact max_lt (by norm_num) (by linarith))
  have hq : 0 < q := (le_max_left _ _).trans_lt hq0
  have haq : a - q < 1 / 4 := by have hh := (le_max_right _ _).trans_lt hq0; linarith
  obtain ⟨C, hC, hmean⟩ := schlicht_smooth_means hf hq hq4
  have hc : ContinuousOn (fun z => bracketSq (f z) ^ a) disk := continuousOn_smoothPower_comp hf a
  by_cases haq0 : a ≤ q
  · apply integrableOn_disk_of_power_circle_bound hc (fun z _ => Real.rpow_nonneg (bracketSq_pos _).le _)
      (C := C) (a := 0) hC.le (by norm_num)
    intro r hr hr1
    rw [circle_lintegral_eq (F := fun z => bracketSq (f z) ^ a)
      (continuous_circle_smoothPower hf a r hr.le hr1)
      (fun θ => Real.rpow_nonneg (bracketSq_pos _).le _), Real.rpow_zero, mul_one]
    apply ENNReal.ofReal_le_ofReal
    refine (intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi) (by linarith [Real.pi_pos])
      ((continuous_circle_smoothPower hf a r hr.le hr1).intervalIntegrable _ _)
      ((continuous_circle_smoothPower hf q r hr.le hr1).intervalIntegrable _ _) ?_).trans (hmean r hr hr1)
    intro θ _
    exact Real.rpow_le_rpow_of_exponent_le (by rw [bracketSq_eq]; nlinarith [sq_nonneg ‖f (circlePoint r θ)‖]) haq0
  · have haqp : 0 < a - q := by linarith
    apply integrableOn_disk_of_power_circle_bound hc (fun z _ => Real.rpow_nonneg (bracketSq_pos _).le _)
      (C := (2 : ℝ) ^ (a - q) * C) (a := -4 * (a - q)) (by positivity) (by linarith)
    intro r hr hr1
    rw [circle_lintegral_eq (F := fun z => bracketSq (f z) ^ a)
      (continuous_circle_smoothPower hf a r hr.le hr1)
      (fun θ => Real.rpow_nonneg (bracketSq_pos _).le _)]
    apply ENNReal.ofReal_le_ofReal
    calc
      _ ≤ ((2 : ℝ) ^ (a - q) * (1 - r) ^ (-4 * (a - q))) *
          ∫ θ in -Real.pi..Real.pi, smoothPower q (f (circlePoint r θ)) :=
        schlicht_circle_power_mono_gt hf haqp hr hr1
      _ ≤ ((2 : ℝ) ^ (a - q) * (1 - r) ^ (-4 * (a - q))) * C :=
        mul_le_mul_of_nonneg_left (hmean r hr hr1) (by positivity)
      _ = _ := by ring
}

lemma bracketSq_negative_integrable {η : ℝ} (hη : 0 < η) :
    Integrable (fun z : ℂ => bracketSq z ^ (-1 - η)) := by
{
  have h := integrable_rpow_neg_one_add_norm_sq (E := ℂ) (μ := volume) (r := 2 + 2 * η)
    (by norm_num [Complex.finrank_real_complex]; linarith)
  convert! h using 1
  ext z
  rw [bracketSq_eq]
  congr 1
  ring
}

lemma schlicht_weighted_derivative_integrable {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {η : ℝ} (hη : 0 < η) :
    IntegrableOn (fun z => ‖deriv f z‖^2 * bracketSq (f z) ^ (-1 - η)) disk := by
{
  have hc : ContinuousOn (fun z => ‖deriv f z‖^2 * bracketSq (f z) ^ (-1 - η)) disk :=
    ((continuousOn_deriv_univalent ⟨hf.1, hf.2.1⟩).norm.pow 2).mul (continuousOn_smoothPower_comp hf _)
  have hn : ∀ z : ℂ, 0 ≤ ‖deriv f z‖^2 * bracketSq (f z) ^ (-1 - η) :=
    fun z => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bracketSq_pos _).le _)
  refine ⟨hc.aestronglyMeasurable Metric.isOpen_ball.measurableSet, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall hn)).mpr
  have hh := conformal_lintegral_le Metric.isOpen_ball.measurableSet
    (fun z hz => hf.1.differentiableAt (Metric.isOpen_ball.mem_nhds hz)) hf.2.1
    (fun w => ENNReal.ofReal (bracketSq w ^ (-1 - η)))
  simp_rw [← ENNReal.ofReal_mul (sq_nonneg _)] at hh
  refine lt_of_le_of_lt hh ?_
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun z : ℂ => Real.rpow_nonneg (bracketSq_pos z).le (-1 - η)))).mp
      (bracketSq_negative_integrable hη).hasFiniteIntegral
}

lemma schlicht_positive_area {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {t : ℝ}
    (ht : 0 < t) (ht2 : t < 2 / 3) : IntegrableOn (fun z => ‖deriv f z‖ ^ t) disk := by
{
  let q := t / 2
  let η := (1 - 3 * q) / (4 * q)
  let a := (1 + η) * q / (1 - q)
  have hq : 0 < q := by dsimp [q]; linarith
  have hq3 : q < 1 / 3 := by dsimp [q]; linarith
  have hq1 : q < 1 := by linarith
  have hη : 0 < η := div_pos (by linarith) (by positivity)
  have ha : a < 1 / 2 := by
  {
    dsimp [a]
    apply (div_lt_iff₀ (by linarith : 0 < 1 - q)).mpr
    have he : (1 + η) * q = (1 + q) / 4 := by dsimp [η]; field_simp; ring
    rw [he]
    linarith
  }
  let A : ℂ → ℝ := fun z => ‖deriv f z‖^2 * bracketSq (f z) ^ (-1 - η)
  let B : ℂ → ℝ := fun z => bracketSq (f z) ^ a
  apply integrableOn_geometric_product Metric.isOpen_ball.measurableSet
    (A := A) (B := B) (schlicht_weighted_derivative_integrable hf hη)
    (schlicht_function_area hf ha)
    ((continuousOn_deriv_norm_rpow ⟨hf.1, hf.2.1⟩ t).aestronglyMeasurable Metric.isOpen_ball.measurableSet)
    hq.le hq1.le
  · intro z _hz
    exact mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (bracketSq_pos _).le _)
  · intro z _hz
    exact Real.rpow_nonneg (bracketSq_pos _).le _
  · intro z _hz
    dsimp [A, B]
    rw [Real.mul_rpow (sq_nonneg _) (Real.rpow_nonneg (bracketSq_pos _).le _),
      ← Real.rpow_natCast ‖deriv f z‖ 2, ← Real.rpow_mul (norm_nonneg _),
      ← Real.rpow_mul (bracketSq_pos _).le, ← Real.rpow_mul (bracketSq_pos _).le]
    have he : (-1 - η) * q + a * (1 - q) = 0 := by
    {
      dsimp [a]
      rw [div_mul_cancel₀ _ (by linarith : 1 - q ≠ 0)]
      ring
    }
    have htq : (2 : ℝ) * q = t := by dsimp [q]; ring
    norm_num only [Nat.cast_ofNat] at *
    rw [htq]
    calc
      _ = ‖deriv f z‖ ^ t * 1 := by ring
      _ = ‖deriv f z‖ ^ t * (bracketSq (f z) ^ ((-1 - η) * q) * bracketSq (f z) ^ (a * (1 - q))) := by
        rw [← Real.rpow_add (bracketSq_pos _), he, Real.rpow_zero]
      _ = _ := by ring
}

theorem lemma_7_3_positive_powers (f : ℂ → ℂ) (hf : Brennan.Koebe.IsClassS f)
    (t : ℝ) (ht : 0 < t ∧ t < 2/3) :
  IntegrableOn (fun z => ‖deriv f z‖ ^ t) (Metric.ball 0 1) volume := by
{
  exact schlicht_positive_area hf ht.1 ht.2
}

/-!
PAPER: 7.3 Domains, equivalence, and endpoint sharpness
PAPER: Proof of the area assertion in Theorem 1.1. Equations (7.4) and Lemma 7.3, together with
PAPER: t = 0, prove the disk integral for f ∈ S throughout −2 < t < 2/3.
PAPER: ...
PAPER: This change of variables is valid for nonnegative integrands, whether or not the integrals
PAPER: are finite. Since 4/3 < s < 4 is equivalent to −2 < 2 − s < 2/3, the desired domain integral
PAPER: is finite.
-/

lemma schlicht_inverse_bound_small {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {z : ℂ}
    (hz : ‖z‖ ≤ 1 / 2) : ‖deriv f z‖ ^ (-2 : ℝ) ≤ 256 := by
{
  have hm : z ∈ disk := by simp only [disk, Brennan.Koebe.disk, Metric.mem_ball, dist_zero_right]; linarith
  have hb := schlicht_deriv_lower hf hm
  have hp : (1 + ‖z‖)^3 ≤ (2 : ℝ)^3 := pow_le_pow_left₀ (by positivity) (by linarith) _
  have hl : (1 / 16 : ℝ) ≤ (1 - ‖z‖) / (1 + ‖z‖)^3 := by
  {
    apply (le_div_iff₀ (by positivity)).mpr
    nlinarith
  }
  have h16 : (1 / 16 : ℝ) ^ (-2 : ℝ) = 256 := by norm_num
  exact (Real.rpow_le_rpow_of_nonpos (by norm_num : (0 : ℝ) < 1 / 16)
    (hl.trans hb) (by norm_num : (-2 : ℝ) ≤ 0)).trans_eq h16
}

lemma inverse_square_bound_all
    (h_means : ∀ ε > (0 : ℝ), ∃ C_ε : ℝ, ∀ (f : ℂ → ℂ) (_hf : Brennan.Koebe.IsClassS f) (r : ℝ),
      (1 / 2 : ℝ) ≤ r ∧ r < 1 →
      integralMean f (-2) r ≤ C_ε * (1 - r) ^ ((-1 : ℝ) - ε))
    (ε : ℝ) (hε : 0 < ε) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : ℂ → ℂ, Brennan.Koebe.IsClassS f → ∀ r : ℝ, 0 ≤ r → r < 1 →
      integralMean f (-2) r ≤ C * (1 - r) ^ (-1 - ε) := by
{
  obtain ⟨C, hbound⟩ := h_means ε hε
  refine ⟨max C 0 + 256, by positivity, fun f hf r hr hr1 => ?_⟩
  have hd : 0 < 1 - r := by linarith
  have hp : 1 ≤ (1 - r) ^ (-1 - ε) :=
    Real.one_le_rpow_of_pos_of_le_one_of_nonpos hd (by linarith) (by linarith)
  by_cases hrh : 1 / 2 ≤ r
  · exact (hbound f hf r ⟨hrh, hr1⟩).trans (mul_le_mul_of_nonneg_right
      (by linarith [le_max_left C 0]) (Real.rpow_nonneg hd.le _))
  · have hn (θ : ℝ) : ‖deriv f (circlePoint r θ)‖ ^ (-2 : ℝ) ≤ 256 :=
      schlicht_inverse_bound_small hf (by rw [circlePoint_norm, abs_of_nonneg hr]; linarith)
    have hi := intervalIntegral.integral_mono_on (a := -Real.pi) (b := Real.pi)
      (f := fun θ => ‖deriv f (circlePoint r θ)‖ ^ (-2 : ℝ))
      (g := fun _ => (256 : ℝ)) (by linarith [Real.pi_pos])
      ((continuous_circle_deriv_rpow ⟨hf.1, hf.2.1⟩ hr hr1 (-2)).intervalIntegrable _ _)
      (intervalIntegrable_const (μ := volume)) (fun θ _ => hn θ)
    have hm : integralMean f (-2) r ≤ 256 := by
    {
      change (2 * Real.pi)⁻¹ * (∫ θ in -Real.pi..Real.pi, ‖deriv f (circlePoint r θ)‖ ^ (-2 : ℝ)) ≤ _
      have hh := mul_le_mul_of_nonneg_left hi (inv_nonneg.mpr (by positivity : (0 : ℝ) ≤ 2 * Real.pi))
      refine hh.trans_eq ?_
      simp only [intervalIntegral.integral_const, smul_eq_mul]
      field_simp
      ring
    }
    nlinarith [le_max_right C 0]
}

lemma weighted_inverse_integrable
    (h_means : ∀ ε > (0 : ℝ), ∃ C_ε : ℝ, ∀ (f : ℂ → ℂ) (_hf : Brennan.Koebe.IsClassS f) (r : ℝ),
      (1 / 2 : ℝ) ≤ r ∧ r < 1 →
      integralMean f (-2) r ≤ C_ε * (1 - r) ^ ((-1 : ℝ) - ε))
    {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {α : ℝ} (hα : 0 < α) :
    IntegrableOn (fun z => (1 - ‖z‖) ^ α * ‖deriv f z‖ ^ (-2 : ℝ)) disk := by
{
  obtain ⟨C, hC, hbound⟩ := inverse_square_bound_all h_means (α / 2) (by linarith)
  have hδ (z : ℂ) (hz : z ∈ disk) : 0 < 1 - ‖z‖ :=
    sub_pos.mpr (by simpa [disk, Brennan.Koebe.disk] using hz)
  have hc : ContinuousOn (fun z : ℂ => (1 - ‖z‖) ^ α * ‖deriv f z‖ ^ (-2 : ℝ)) disk :=
    ((continuous_const.sub continuous_norm).continuousOn.rpow_const (fun z hz => Or.inl (hδ z hz).ne')).mul
      (continuousOn_deriv_norm_rpow ⟨hf.1, hf.2.1⟩ _)
  apply integrableOn_disk_of_power_circle_bound hc
    (fun z hz => mul_nonneg (Real.rpow_nonneg (hδ z hz).le _) (Real.rpow_nonneg (norm_nonneg _) _))
    (C := 2 * Real.pi * C) (a := α / 2 - 1) (by positivity) (by linarith)
  intro r hr hr1
  have hd : 0 < 1 - r := by linarith
  have he : (fun θ => (1 - ‖circlePoint r θ‖) ^ α * ‖deriv f (circlePoint r θ)‖ ^ (-2 : ℝ)) =
      fun θ => (1 - r) ^ α * ‖deriv f (circlePoint r θ)‖ ^ (-2 : ℝ) := by
  {
    ext θ
    rw [circlePoint_norm, abs_of_pos hr]
  }
  rw [circle_lintegral_eq (F := fun z => (1 - ‖z‖) ^ α * ‖deriv f z‖ ^ (-2 : ℝ)) (r := r)
    (by rw [he]; exact continuous_const.mul (continuous_circle_deriv_rpow ⟨hf.1, hf.2.1⟩ hr.le hr1 _))
    (fun θ => by rw [circlePoint_norm, abs_of_pos hr]; positivity), he, intervalIntegral.integral_const_mul]
  apply ENNReal.ofReal_le_ofReal
  have hmean : (∫ θ in -Real.pi..Real.pi, ‖deriv f (circlePoint r θ)‖ ^ (-2 : ℝ)) =
      2 * Real.pi * integralMean f (-2) r := by
  {
    unfold integralMean circlePoint
    field_simp
    simp only [mul_comm I]
  }
  rw [hmean]
  calc
    _ ≤ (1 - r) ^ α * (2 * Real.pi * (C * (1 - r) ^ (-1 - α / 2))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hbound f hf r hr.le hr1) (by positivity)) (by positivity)
    _ = (2 * Real.pi * C) * ((1 - r) ^ α * (1 - r) ^ (-1 - α / 2)) := by ring
    _ = 2 * Real.pi * C * (1 - r) ^ (α / 2 - 1) := by
      rw [← Real.rpow_add hd]
      congr 2
      ring
}

lemma schlicht_negative_area
    (h_means : ∀ ε > (0 : ℝ), ∃ C_ε : ℝ, ∀ (f : ℂ → ℂ) (_hf : Brennan.Koebe.IsClassS f) (r : ℝ),
      (1 / 2 : ℝ) ≤ r ∧ r < 1 →
      integralMean f (-2) r ≤ C_ε * (1 - r) ^ ((-1 : ℝ) - ε))
    {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {t : ℝ}
    (ht : -2 < t) (ht0 : t < 0) : IntegrableOn (fun z => ‖deriv f z‖ ^ t) disk := by
{
  let q : ℝ := -t / 2
  let α : ℝ := (1 - q) / (2 * q)
  have hq : 0 < q := by dsimp [q]; linarith
  have hq1 : q < 1 := by dsimp [q]; linarith
  have hα : 0 < α := div_pos (by linarith) (by positivity)
  let A : ℂ → ℝ := fun z => (1 - ‖z‖) ^ α * ‖deriv f z‖ ^ (-2 : ℝ)
  let B : ℂ → ℝ := fun z => (1 - ‖z‖) ^ (-1 / 2 : ℝ)
  apply integrableOn_geometric_product Metric.isOpen_ball.measurableSet
    (A := A) (B := B) (weighted_inverse_integrable h_means hf hα)
    (integrableOn_disk_boundary_power (by norm_num))
    ((continuousOn_deriv_norm_rpow ⟨hf.1, hf.2.1⟩ t).aestronglyMeasurable Metric.isOpen_ball.measurableSet)
    hq.le hq1.le
  · intro z hz
    have hn : ‖z‖ < 1 := by simpa [disk, Brennan.Koebe.disk] using hz
    exact mul_nonneg (Real.rpow_nonneg (by linarith) _) (Real.rpow_nonneg (norm_nonneg _) _)
  · intro z hz
    have hn : ‖z‖ < 1 := by simpa [disk, Brennan.Koebe.disk] using hz
    exact Real.rpow_nonneg (by linarith) _
  · intro z hz
    have hn : ‖z‖ < 1 := by simpa [disk, Brennan.Koebe.disk] using hz
    have hd : 0 < 1 - ‖z‖ := by linarith
    dsimp [A, B]
    rw [Real.mul_rpow (Real.rpow_nonneg hd.le _) (Real.rpow_nonneg (norm_nonneg _) _),
      ← Real.rpow_mul hd.le, ← Real.rpow_mul (norm_nonneg _), ← Real.rpow_mul hd.le]
    have he : α * q + (-1 / 2) * (1 - q) = 0 := by dsimp [α]; field_simp; ring
    have htq : (-2 : ℝ) * q = t := by dsimp [q]; ring
    rw [htq]
    calc
      _ = ‖deriv f z‖ ^ t * 1 := by ring
      _ = ‖deriv f z‖ ^ t * ((1 - ‖z‖) ^ (α * q) * (1 - ‖z‖) ^ ((-1 / 2) * (1 - q))) := by
        rw [← Real.rpow_add hd, he, Real.rpow_zero]
      _ = _ := by ring
}

lemma schlicht_area
    (h_means : ∀ ε > (0 : ℝ), ∃ C_ε : ℝ, ∀ (f : ℂ → ℂ) (_hf : Brennan.Koebe.IsClassS f) (r : ℝ),
      (1 / 2 : ℝ) ≤ r ∧ r < 1 →
      integralMean f (-2) r ≤ C_ε * (1 - r) ^ ((-1 : ℝ) - ε))
    {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {t : ℝ}
    (ht : -2 < t) (ht2 : t < 2 / 3) : IntegrableOn (fun z => ‖deriv f z‖ ^ t) disk := by
{
  rcases lt_trichotomy t 0 with h | h | h
  · exact schlicht_negative_area h_means hf ht h
  · subst t
    simp only [Real.rpow_zero]
    exact integrableOn_const (ne_of_lt Metric.isBounded_ball.measure_lt_top)
  · exact schlicht_positive_area hf h ht2
}

def normalizeDisk (f : ℂ → ℂ) (z : ℂ) : ℂ := (f z - f 0) / deriv f 0

lemma normalizeDisk_hasDeriv {f : ℂ → ℂ} (hf : UnivalentOn f disk) {z : ℂ} (hz : z ∈ disk) :
    HasDerivAt (normalizeDisk f) (deriv f z / deriv f 0) z := by
{
  exact ((hf.1.differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt.sub_const (f 0)).div_const _
}

lemma normalizeDisk_isClassS {f : ℂ → ℂ} (hf : UnivalentOn f disk) :
    Brennan.Koebe.IsClassS (normalizeDisk f) := by
{
  have h0 : (0 : ℂ) ∈ disk := by simp [disk, Brennan.Koebe.disk]
  have hn := deriv_ne_zero_of_univalentOn Metric.isOpen_ball hf h0
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (normalizeDisk_hasDeriv hf hz).differentiableAt.differentiableWithinAt
  · intro z hz w hw he
    have hh : f z - f 0 = f w - f 0 := (div_left_inj' hn).mp he
    exact hf.2 hz hw (sub_left_inj.mp hh)
  · simp [normalizeDisk]
  · rw [(normalizeDisk_hasDeriv hf h0).deriv, div_self hn]
}

lemma univalent_disk_area
    (h_means : ∀ ε > (0 : ℝ), ∃ C_ε : ℝ, ∀ (f : ℂ → ℂ) (_hf : Brennan.Koebe.IsClassS f) (r : ℝ),
      (1 / 2 : ℝ) ≤ r ∧ r < 1 →
      integralMean f (-2) r ≤ C_ε * (1 - r) ^ ((-1 : ℝ) - ε))
    {f : ℂ → ℂ} (hf : UnivalentOn f disk) {t : ℝ}
    (ht : -2 < t) (ht2 : t < 2 / 3) : IntegrableOn (fun z => ‖deriv f z‖ ^ t) disk := by
{
  have h0 : (0 : ℂ) ∈ disk := by simp [disk, Brennan.Koebe.disk]
  have hn := deriv_ne_zero_of_univalentOn Metric.isOpen_ball hf h0
  have hg := schlicht_area h_means (normalizeDisk_isClassS hf) ht ht2
  apply IntegrableOn.congr_fun (hg.const_mul (‖deriv f 0‖ ^ t)) _ Metric.isOpen_ball.measurableSet
  intro z hz
  have he : deriv f z = deriv f 0 * deriv (normalizeDisk f) z := by
  {
    rw [(normalizeDisk_hasDeriv hf hz).deriv]
    field_simp
  }
  dsimp only
  rw [he, norm_mul, Real.mul_rpow (norm_nonneg _) (norm_nonneg _)]
}

lemma univalent_inverse_hasDerivAt {U : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : UnivalentOn φ U) {z : ℂ} (hz : z ∈ U) :
    HasDerivAt (Function.invFunOn φ U) (deriv φ z)⁻¹ (φ z) := by
{
  have ha := hφ.1.analyticOnNhd hU z hz
  apply (ha.hasStrictDerivAt.to_local_left_inverse (deriv_ne_zero_of_univalentOn hU hφ hz) ?_).hasDerivAt
  filter_upwards [hU.mem_nhds hz] with w hw
  exact hφ.2.leftInvOn_invFunOn hw
}

lemma bijOn_inverse_univalent {U V : Set ℂ} (hU : IsOpen U) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ U) (hb : BijOn φ U V) :
    UnivalentOn (Function.invFunOn φ U) V := by
{
  constructor
  · intro w hw
    obtain ⟨z, hz, rfl⟩ := hb.surjOn hw
    exact (univalent_inverse_hasDerivAt hU ⟨hφ, hb.injOn⟩ hz).differentiableAt.differentiableWithinAt
  · exact (Function.invFunOn_injOn_image φ U).mono hb.surjOn
}

lemma bijOn_inverse_image {U V : Set ℂ} {φ : ℂ → ℂ} (hb : BijOn φ U V) :
    Function.invFunOn φ U '' V = U := by
{
  rw [← hb.image_eq]
  exact hb.injOn.invFunOn_image (Subset.refl _)
}

lemma conformal_lintegral_eq {F : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hF : ∀ z ∈ s, DifferentiableAt ℂ F z) (hi : InjOn F s) (b : ℂ → ℝ≥0∞) :
    (∫⁻ w in F '' s, b w) = ∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖^2) * b (F z) := by
{
  rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (hF z hz).hasFDerivAt.restrictScalars ℝ |>.hasFDerivWithinAt) hi b]
  refine setLIntegral_congr_fun hs (fun z hz => ?_)
  have hd := (hF z hz).hasFDerivAt.restrictScalars ℝ
  have hf : (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F z)) = fderiv ℝ F z := hd.fderiv.symm
  have hd' : (fderiv ℝ F z).det = ‖deriv F z‖^2 := Brennan.Koebe.det_fderiv_complex_at (hF z hz)
  rw [hf, hd', abs_of_nonneg (sq_nonneg _)]
}

lemma conformal_domain_area
    (h_means : ∀ ε > (0 : ℝ), ∃ C_ε : ℝ, ∀ (f : ℂ → ℂ) (_hf : Brennan.Koebe.IsClassS f) (r : ℝ),
      (1 / 2 : ℝ) ≤ r ∧ r < 1 →
      integralMean f (-2) r ≤ C_ε * (1 - r) ^ ((-1 : ℝ) - ε))
    {W : Set ℂ} (hW : IsOpen W) {φ : ℂ → ℂ}
    (hφ : DifferentiableOn ℂ φ W) (hb : BijOn φ W disk) {s : ℝ}
    (hs : 4 / 3 < s) (hs4 : s < 4) : IntegrableOn (fun z => ‖deriv φ z‖ ^ s) W := by
{
  let f := Function.invFunOn φ W
  have hf : UnivalentOn f disk := bijOn_inverse_univalent hW hφ hb
  have himage : f '' disk = W := bijOn_inverse_image hb
  have hfi : IntegrableOn (fun w => ‖deriv f w‖ ^ (2 - s)) disk :=
    univalent_disk_area h_means hf (by linarith) (by linarith)
  have hderiv (w : ℂ) (hw : w ∈ disk) : deriv φ (f w) = (deriv f w)⁻¹ := by
  {
    have hz : f w ∈ W := hb.surjOn.mapsTo_invFunOn hw
    have hv : φ (f w) = w := hb.surjOn.rightInvOn_invFunOn hw
    have hd := (univalent_inverse_hasDerivAt hW ⟨hφ, hb.injOn⟩ hz).deriv
    change deriv f (φ (f w)) = (deriv φ (f w))⁻¹ at hd
    rw [hv] at hd
    rw [hd, inv_inv]
  }
  have hc : ContinuousOn (fun z => ‖deriv φ z‖ ^ s) W := by
  {
    refine (hφ.deriv hW).continuousOn.norm.rpow_const (fun z hz => ?_)
    exact Or.inl (norm_ne_zero_iff.mpr (deriv_ne_zero_of_univalentOn hW ⟨hφ, hb.injOn⟩ hz))
  }
  refine ⟨hc.aestronglyMeasurable hW.measurableSet, ?_⟩
  apply (hasFiniteIntegral_iff_ofReal (Eventually.of_forall (fun z : ℂ => Real.rpow_nonneg (norm_nonneg _) s))).mpr
  have he := conformal_lintegral_eq Metric.isOpen_ball.measurableSet
    (fun z hz => hf.1.differentiableAt (Metric.isOpen_ball.mem_nhds hz)) hf.2
    (fun z => ENNReal.ofReal (‖deriv φ z‖ ^ s))
  change (∫⁻ z in f '' disk, ENNReal.ofReal (‖deriv φ z‖ ^ s)) =
    ∫⁻ z in disk, ENNReal.ofReal (‖deriv f z‖^2) * ENNReal.ofReal (‖deriv φ (f z)‖ ^ s) at he
  rw [himage] at he
  rw [he]
  have hp : (∫⁻ w in disk, ENNReal.ofReal (‖deriv f w‖^2) * ENNReal.ofReal (‖deriv φ (f w)‖ ^ s)) =
      ∫⁻ w in disk, ENNReal.ofReal (‖deriv f w‖ ^ (2 - s)) := by
  {
    refine setLIntegral_congr_fun Metric.isOpen_ball.measurableSet (fun w hw => ?_)
    rw [hderiv w hw, norm_inv, Real.inv_rpow (norm_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _)]
    congr 1
    have hn : 0 < ‖deriv f w‖ := norm_pos_iff.mpr (deriv_ne_zero_of_univalentOn Metric.isOpen_ball hf hw)
    rw [← Real.rpow_natCast ‖deriv f w‖ 2, ← Real.rpow_neg hn.le, ← Real.rpow_add hn]
    rfl
  }
  rw [hp]
  exact (hasFiniteIntegral_iff_ofReal (Eventually.of_forall
    (fun w : ℂ => Real.rpow_nonneg (norm_nonneg (deriv f w)) (2 - s)))).mp hfi.hasFiniteIntegral
}

theorem brennan_conjecture_from_disk_means :
    (∀ ε > (0 : ℝ), ∃ C_ε : ℝ, ∀ (f : ℂ → ℂ) (_hf : Brennan.Koebe.IsClassS f) (r : ℝ),
      (1 / 2 : ℝ) ≤ r ∧ r < 1 →
      integralMean f (-2) r ≤ C_ε * (1 - r) ^ ((-1 : ℝ) - ε)) →
    BrennansConjectureStatement := by
{
  intro h_means W f p hW _hW_ne _hW_univ hf_diff hf_inj hf_im hp
  have hb : BijOn f W disk := by
  {
    change BijOn f W (Metric.ball (0 : ℂ) 1)
    rw [← hf_im]
    exact ⟨mapsTo_image f W, hf_inj, surjOn_image f W⟩
  }
  exact conformal_domain_area h_means hW hf_diff hb hp.1 hp.2
}

-- This proves your exact BrennansConjectureStatement from `BrennanConjecture.lean`!
theorem brennan_area_assertion : BrennansConjectureStatement := by
{
  exact brennan_conjecture_from_disk_means main_theorem_inverse_square
}

end Brennan.Sections6and7
