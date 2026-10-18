import Mathlib
import brennan.Section3

open Complex Set MeasureTheory Topology Filter Classical Function
open scoped ComplexConjugate Topology ENNReal NNReal CompactlySupported

noncomputable section

namespace Brennan.Sections4and5

open Brennan.Section2
open Brennan.Section2_Dyadic
open Brennan.Section3

variable (beta : ℝ)

/-!
# 4 Escape estimates and compact superlevels

PAPER: The geometric argument will compare critical points above a fixed positive level. We first
PAPER: show that such points cannot escape to the boundary or to infinity for almost every target
PAPER: value. The main step near the real axis is a bound on the total length of a horizontal line
PAPER: that maps into a compact target set.
PAPER: Throughout this section assume ρ > 2, let β = log2 ρ > 1, and let P be the probability
PAPER: from Lemma 3.1. Thus, for z = x + iy ∈ H and every nonnegative Borel function Φ on K,
PAPER: E[|QF (z)|^2Φ(TzF)] = y^{−β}EΦ(F). (4.1)
PAPER: Set
PAPER: k = (β + 3)/4 > 1, V^F_ξ(x + iy) = y^k / |F(x + iy) - ξ| (4.2)
PAPER: with value +∞ at the unique possible point where F(z) = ξ.
-/

-- The critical scale factor k
def k_val (beta : ℝ) := (beta + 3) / 4

-- The target potential function V^F_ξ(z), taking value +∞ (⊤) at F(z) = ξ in H
def V_target (beta : ℝ) (F : KClass) (xi : ℂ) (z : ℂ) : ℝ≥0∞ :=
  if z ∈ H then ENNReal.ofReal ((z.im : ℝ) ^ (k_val beta)) / ENNReal.ofReal ‖F.F z - xi‖ else 0

/-!
PAPER: 4.1 A weighted area integral
PAPER: Recall m(z) = (z − i)/(z + i) and the affine inverse z# = (−x + i)/y of z = x + iy. Define
PAPER: S0 = {z ∈ H : |m(z)| ≥ 1/2}, I(F) = ∫_S0 y^{β+1}|F(x + iy)|^{−4} dA(x + iy). (4.3)
PAPER: The complement of S0 has compact closure in H and contains the unique zero i of every F ∈ K.

PAPER: Lemma 4.2 (Weighted inverse area). The function I : K → [0, ∞] is Borel and satisfies
PAPER: EI(F) ≤ 256π. In particular, I(F) < ∞ almost surely.
-/
def S0 : Set ℂ := {z | z.im > 0 ∧ ‖(z - I) / (z + I)‖ ≥ 1/2}

def I_integrable (beta : ℝ) (F : KClass) : Prop :=
  IntegrableOn (fun z : ℂ => (z.im : ℝ) ^ (beta + 1) * ‖F.F z‖ ^ (-4 : ℝ)) S0 volume

def I_func (beta : ℝ) (F : KClass) : ℝ :=
  ∫ z in S0, (z.im : ℝ) ^ (beta + 1) * ‖F.F z‖ ^ (-4 : ℝ) ∂volume

lemma determinant_complex_real (A : ℂ →ₗ[ℝ] ℂ) :
    LinearMap.det A = (A 1).re * (A I).im - (A I).re * (A 1).im := by
{
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]
}

lemma aff_inv_re (z : ℂ) : (aff_inv z).re = -z.re / z.im := by
{
  simp [aff_inv, Complex.div_ofReal_re]
}

lemma aff_inv_im (z : ℂ) : (aff_inv z).im = z.im⁻¹ := by
{
  simp [aff_inv, Complex.div_ofReal_im]
}

lemma aff_inv_mem {z : ℂ} (hz : z ∈ H) : aff_inv z ∈ H := by
{
  simpa only [H, mem_setOf_eq, aff_inv_im] using inv_pos.mpr hz
}

lemma aff_inv_invol {z : ℂ} (hz : z ∈ H) : aff_inv (aff_inv z) = z := by
{
  have hn : z.im ≠ 0 := ne_of_gt hz
  apply Complex.ext
  · simp only [aff_inv_re, aff_inv_im, neg_div, neg_neg, div_inv_eq_mul]
    exact div_mul_cancel₀ _ hn
  · simp only [aff_inv_im, inv_inv]
}

lemma aff_inv_injOn : InjOn aff_inv H := by
{
  intro z hz w hw he
  simpa only [aff_inv_invol hz, aff_inv_invol hw] using congrArg aff_inv he
}

lemma aff_inv_aff {z : ℂ} (hz : z ∈ H) : aff z (aff_inv z) = I := by
{
  have hn : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  rw [aff, aff_inv, mul_div_cancel₀ _ hn]
  ring
}

lemma hasFDerivAt_aff_inv {z : ℂ} (hz : z ∈ H) :
    HasFDerivAt aff_inv
      (((z.im : ℂ)⁻¹) • (-(Complex.ofRealCLM.comp Complex.reCLM)) +
        (-(z.re : ℂ) + I) •
          ((-((z.im : ℂ)^2)⁻¹) • (Complex.ofRealCLM.comp Complex.imCLM))) z := by
{
  have hn : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hi := (hasFDerivAt_inv' (𝕜 := ℝ) hn).comp z
    (Complex.ofRealCLM.comp Complex.imCLM).hasFDerivAt
  have h := ((Complex.ofRealCLM.comp Complex.reCLM).hasFDerivAt.neg.add_const I).mul hi
  convert! h using 1
  ext v
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, Pi.neg_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply,
    ContinuousLinearMap.mulLeftRight_apply, Function.comp_apply, smul_eq_mul]
  ring
}

lemma differentiableAt_aff_inv {z : ℂ} (hz : z ∈ H) : DifferentiableAt ℝ aff_inv z := by
{
  exact (hasFDerivAt_aff_inv hz).differentiableAt
}

lemma fderiv_aff_inv_apply {z : ℂ} (hz : z ∈ H) (v : ℂ) :
    fderiv ℝ aff_inv z v =
      (-(v.re : ℂ) * (z.im : ℂ) - (-(z.re : ℂ) + I) * (v.im : ℂ)) / (z.im : ℂ)^2 := by
{
  have hn : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  rw [(hasFDerivAt_aff_inv hz).fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, Complex.reCLM_apply, Complex.imCLM_apply, smul_eq_mul]
  field_simp
  ring
}

lemma det_aff_inv {z : ℂ} (hz : z ∈ H) :
    (fderiv ℝ aff_inv z).det = z.im⁻¹ ^ 3 := by
{
  change LinearMap.det (fderiv ℝ aff_inv z).toLinearMap = _
  rw [determinant_complex_real]
  change (fderiv ℝ aff_inv z 1).re * (fderiv ℝ aff_inv z I).im -
    (fderiv ℝ aff_inv z I).re * (fderiv ℝ aff_inv z 1).im = _
  rw [fderiv_aff_inv_apply hz, fderiv_aff_inv_apply hz]
  simp only [Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, Complex.ofReal_one,
    Complex.ofReal_zero, neg_zero, zero_mul, mul_zero, mul_one, sub_zero, zero_sub, neg_mul,
    ← Complex.ofReal_pow, Complex.div_ofReal_re, Complex.div_ofReal_im,
    Complex.neg_re, Complex.neg_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im]
  field_simp [ne_of_gt (show 0 < z.im from hz)]
  ring
}

lemma aff_inv_change_variables {s : Set ℂ} (hs : MeasurableSet s) (hsub : s ⊆ H)
    (hInv : aff_inv '' s = s) (f : ℂ → ℝ≥0∞) :
    (∫⁻ z in s, f z ∂volume) = ∫⁻ z in s, ENNReal.ofReal (z.im⁻¹ ^ 3) * f (aff_inv z) ∂volume := by
{
  have h := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (differentiableAt_aff_inv (hsub hz)).hasFDerivAt.hasFDerivWithinAt)
    (aff_inv_injOn.mono hsub) f
  rw [hInv] at h
  refine h.trans (setLIntegral_congr_fun hs (fun z hz => ?_))
  rw [det_aff_inv (hsub hz), abs_of_nonneg (pow_nonneg (inv_nonneg.mpr (hsub hz).le) _)]
}

lemma measurable_inv_cayley : Measurable inv_cayley := by
{
  exact (measurable_id.sub_const _).div (measurable_id.add_const _)
}

lemma measurableSet_S0 : MeasurableSet S0 := by
{
  exact isOpen_H.measurableSet.inter (measurableSet_le measurable_const measurable_inv_cayley.norm)
}

lemma inv_cayley_aff_inv {z : ℂ} (hz : z ∈ H) :
    inv_cayley (aff_inv z) = (z - I) / (star (z + I)) := by
{
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have h₁ : aff_inv z - I = -(z - I) / (z.im : ℂ) := by
  {
    rw [aff_inv, div_sub' hy]
    congr 1
    apply Complex.ext <;> simp
  }
  have h₂ : aff_inv z + I = -star (z + I) / (z.im : ℂ) := by
  {
    rw [aff_inv, div_add' _ _ _ hy]
    congr 1
    apply Complex.ext <;> simp
  }
  rw [inv_cayley, h₁, h₂, div_div_div_cancel_right₀ hy, neg_div_neg_eq]
}

lemma inv_cayley_aff_inv_norm {z : ℂ} (hz : z ∈ H) :
    ‖inv_cayley (aff_inv z)‖ = ‖inv_cayley z‖ := by
{
  rw [inv_cayley_aff_inv hz, inv_cayley, norm_div, norm_div, norm_star]
}

lemma aff_inv_mem_S0 {z : ℂ} (hz : z ∈ S0) : aff_inv z ∈ S0 := by
{
  exact ⟨aff_inv_mem hz.1, (inv_cayley_aff_inv_norm hz.1).symm ▸ hz.2⟩
}

lemma aff_inv_image_S0 : aff_inv '' S0 = S0 := by
{
  ext z
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact aff_inv_mem_S0 hw
  · intro hz
    exact ⟨aff_inv z, aff_inv_mem_S0 hz, aff_inv_invol hz.1⟩
}

lemma F_lower_S0 (F : KClass) {z : ℂ} (hz : z ∈ S0) :
    (1 / 16 : ℝ) ≤ ‖F.F z‖ := by
{
  have hl := Brennan.Koebe.schlicht_lower_growth (lemma_2_2_bounds_S F) (inv_cayley_maps hz.1)
  have he : ‖F.F z‖ = 2 * ‖K_to_S F (inv_cayley z)‖ := by
  {
    rw [← S_to_K_K_to_S F hz.1]
    simp [S_to_K]
  }
  rw [he]
  have hm : (1 / 2 : ℝ) ≤ ‖inv_cayley z‖ := hz.2
  linarith
}

lemma F_ne_zero_S0 (F : KClass) {z : ℂ} (hz : z ∈ S0) : F.F z ≠ 0 := by
{
  exact norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by norm_num) (F_lower_S0 F hz)))
}

lemma T_at_aff_inv (F : KClass) {z : ℂ} (hz : z ∈ H) :
    T z F.F (aff_inv z) = -F.F z / ((z.im : ℂ) * deriv F.F z) := by
{
  simp only [T, aff_inv_aff hz, F.norm_zero, zero_sub]
}

lemma A_weight_inverse_value (F : KClass) {z : ℂ} (hz : z ∈ S0) :
    A_weight z F.F * ‖T z F.F (aff_inv z)‖⁻¹ ^ 4 =
      z.im ^ 4 * (‖deriv F.F z‖^2 * ‖F.F z‖⁻¹ ^ 4) := by
{
  have hn := F_ne_zero_S0 F hz
  have hd := deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz.1
  have hy : 0 < z.im := hz.1
  rw [A_weight, Q, T_at_aff_inv F hz.1]
  simp only [one_div, norm_inv, norm_div, norm_neg, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hy]
  field_simp
}

lemma inv_jacobian_det {f : ℂ → ℂ} {z : ℂ} (hf : DifferentiableAt ℂ f z) (hn : f z ≠ 0) :
    |(fderiv ℝ (fun w => (f w)⁻¹) z).det| = ‖deriv f z‖^2 * ‖f z‖⁻¹ ^ 4 := by
{
  have hd : HasDerivAt (fun w => (f w)⁻¹) (-deriv f z / f z ^ 2) z := hf.hasDerivAt.inv hn
  have hdet : (fderiv ℝ (fun w => (f w)⁻¹) z).det = ‖deriv (fun w => (f w)⁻¹) z‖^2 :=
    Brennan.Koebe.det_fderiv_complex_at hd.differentiableAt
  rw [hdet, abs_of_nonneg (sq_nonneg _), hd.deriv]
  change ‖(-deriv f z / f z ^ 2 : ℂ)‖^2 = ‖deriv f z‖^2 * ‖f z‖⁻¹ ^ 4
  rw [Complex.norm_div, norm_neg, Complex.norm_pow]
  simp only [div_eq_mul_inv, inv_pow]
  ring
}

lemma inverse_area_bound {f : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hf : ∀ z ∈ s, DifferentiableAt ℂ f z) (hi : InjOn f s)
    (hmin : ∀ z ∈ s, (1 / 16 : ℝ) ≤ ‖f z‖) :
    (∫⁻ z in s, ENNReal.ofReal (‖deriv f z‖^2 * ‖f z‖⁻¹ ^ 4)) ≤
      ENNReal.ofReal (256 * Real.pi) := by
{
  have hn (z : ℂ) (hz : z ∈ s) : f z ≠ 0 :=
    norm_ne_zero_iff.mp (ne_of_gt (lt_of_lt_of_le (by norm_num) (hmin z hz)))
  have hd (z : ℂ) (hz : z ∈ s) : HasDerivAt (fun w => (f w)⁻¹) (-deriv f z / f z ^ 2) z :=
    (hf z hz).hasDerivAt.inv (hn z hz)
  have hhi : InjOn (fun z => (f z)⁻¹) s := fun z hz w hw he => hi hz hw (inv_inj.mp he)
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => ((hd z hz).hasFDerivAt.restrictScalars ℝ).hasFDerivWithinAt) hhi (fun _ => (1 : ℝ≥0∞))
  simp only [lintegral_const, one_mul, Measure.restrict_apply_univ] at he
  have he' : (∫⁻ z in s, ENNReal.ofReal (‖deriv f z‖^2 * ‖f z‖⁻¹ ^ 4)) =
      volume ((fun z => (f z)⁻¹) '' s) := by
  {
    rw [he]
    refine setLIntegral_congr_fun hs (fun z hz => ?_)
    rw [mul_one, ((hd z hz).hasFDerivAt.restrictScalars ℝ).fderiv.symm,
      inv_jacobian_det (hf z hz) (hn z hz)]
  }
  rw [he']
  have hsub : (fun z => (f z)⁻¹) '' s ⊆ Metric.closedBall 0 16 := by
  {
    rintro _ ⟨z, hz, rfl⟩
    simp only [Metric.mem_closedBall, dist_zero_right, norm_inv]
    exact (inv_le_comm₀ (norm_pos_iff.mpr (hn z hz)) (by norm_num)).mpr (by simpa using hmin z hz)
  }
  refine (measure_mono hsub).trans_eq ?_
  rw [Complex.volume_closedBall]
  have hp : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
  {
    rw [ENNReal.ofReal, ENNReal.coe_inj]
    exact Subtype.ext (Real.coe_toNNReal Real.pi Real.pi_pos.le).symm
  }
  rw [hp, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 256)]
  norm_num [mul_comm]
}

lemma continuous_KClass_iteratedDeriv_eval (n : ℕ) :
    Continuous (fun p : KClass × H => iteratedDeriv n p.1.F p.2) := by
{
  have heq : (fun p : KClass × H => iteratedDeriv n p.1.F p.2) =
      (fun p : DiskClass × H => iteratedDeriv n (toKClass p.1).F p.2) ∘
        (Prod.map ofKClass id) := by
  {
    funext p
    exact (eqOn_iteratedDeriv_of_eqOn (toKClass_ofKClass_eqOn p.1) n p.2.2).symm
  }
  rw [heq]
  exact (continuous_halfClassJet_eval n).comp (continuous_ofKClass.prodMap continuous_id)
}

lemma continuous_KClass_eval : Continuous (fun p : KClass × H => p.1.F p.2) := by
{
  simpa only [iteratedDeriv_zero] using continuous_KClass_iteratedDeriv_eval 0
}

lemma continuous_KClass_deriv_eval : Continuous (fun p : KClass × H => deriv p.1.F p.2) := by
{
  simpa only [iteratedDeriv_one] using continuous_KClass_iteratedDeriv_eval 1
}

def planeKClassValue (F : KClass) (z : ℂ) : ℂ :=
  if z ∈ H then F.F z else 0

def planeKClassDeriv (F : KClass) (z : ℂ) : ℂ :=
  if z ∈ H then deriv F.F z else 0

lemma measurable_planeKClassValue :
    Measurable (fun p : KClass × ℂ => planeKClassValue p.1 p.2) := by
{
  let s : Set (KClass × ℂ) := Prod.snd ⁻¹' H
  have hc : Continuous (fun p : s => p.val.1.F p.val.2) :=
    continuous_KClass_eval.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => p.2)))
  simpa only [planeKClassValue, s, Set.mem_preimage, dite_eq_ite] using
    hc.measurable.dite (measurable_const (a := (0 : ℂ)))
      (isOpen_H.measurableSet.preimage measurable_snd)
}

lemma measurable_planeKClassDeriv :
    Measurable (fun p : KClass × ℂ => planeKClassDeriv p.1 p.2) := by
{
  let s : Set (KClass × ℂ) := Prod.snd ⁻¹' H
  have hc : Continuous (fun p : s => deriv p.val.1.F p.val.2) :=
    continuous_KClass_deriv_eval.comp
      ((continuous_fst.comp continuous_subtype_val).prodMk
        ((continuous_snd.comp continuous_subtype_val).subtype_mk (fun p => p.2)))
  simpa only [planeKClassDeriv, s, Set.mem_preimage, dite_eq_ite] using
    hc.measurable.dite (measurable_const (a := (0 : ℂ)))
      (isOpen_H.measurableSet.preimage measurable_snd)
}

lemma planeKClassValue_eq (F : KClass) {z : ℂ} (hz : z ∈ H) :
    planeKClassValue F z = F.F z := by
{
  simp [planeKClassValue, hz]
}

lemma planeKClassDeriv_eq (F : KClass) {z : ℂ} (hz : z ∈ H) :
    planeKClassDeriv F z = deriv F.F z := by
{
  simp [planeKClassDeriv, hz]
}

def inverseDensity (F : KClass) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖planeKClassValue F z‖⁻¹ ^ 4)

def inverseJacDensity (F : KClass) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (‖planeKClassDeriv F z‖^2 * ‖planeKClassValue F z‖⁻¹ ^ 4)

def weightedInverseArea (beta : ℝ) (F : KClass) : ℝ≥0∞ :=
  ∫⁻ z in S0, ENNReal.ofReal (z.im ^ (beta + 1)) * inverseDensity F z

lemma measurable_inverseDensity : Measurable (Function.uncurry inverseDensity) := by
{
  exact (measurable_planeKClassValue.norm.inv.pow_const 4).ennreal_ofReal
}

lemma measurable_inverseJacDensity : Measurable (Function.uncurry inverseJacDensity) := by
{
  exact ((measurable_planeKClassDeriv.norm.pow_const 2).mul
    (measurable_planeKClassValue.norm.inv.pow_const 4)).ennreal_ofReal
}

lemma measurable_weightedInverseArea (beta : ℝ) : Measurable (weightedInverseArea beta) := by
{
  apply Measurable.lintegral_prod_right
  exact (((Complex.continuous_im.comp continuous_snd).measurable.pow measurable_const).ennreal_ofReal).mul
    measurable_inverseDensity
}

lemma inverseJacDensity_integral_le (F : KClass) :
    (∫⁻ z in S0, inverseJacDensity F z) ≤ ENNReal.ofReal (256 * Real.pi) := by
{
  have he : (∫⁻ z in S0, inverseJacDensity F z) =
      ∫⁻ z in S0, ENNReal.ofReal (‖deriv F.F z‖^2 * ‖F.F z‖⁻¹ ^ 4) := by
  {
    refine setLIntegral_congr_fun measurableSet_S0 (fun z hz => ?_)
    simp only [inverseJacDensity, planeKClassValue_eq F hz.1, planeKClassDeriv_eq F hz.1]
  }
  rw [he]
  exact inverse_area_bound measurableSet_S0
    (fun _ hz => (F.univalent.1 _ hz.1).differentiableAt (isOpen_H.mem_nhds hz.1))
    (F.univalent.2.mono (fun _ h => h.1))
    (fun _ hz => F_lower_S0 F hz)
}

lemma inv_pow_four_eq_rpow_neg_four (x : ℝ) (hx : 0 ≤ x) :
    x⁻¹ ^ 4 = x ^ (-4 : ℝ) := by
{
  rw [show (-4 : ℝ) = -((4 : ℕ) : ℝ) by norm_num, Real.rpow_neg hx, Real.rpow_natCast, inv_pow]
}

lemma weightedInverseArea_eq_lintegral (beta : ℝ) (F : KClass) :
    weightedInverseArea beta F =
      ∫⁻ z in S0, ENNReal.ofReal ((z.im : ℝ) ^ (beta + 1) * ‖F.F z‖ ^ (-4 : ℝ)) ∂volume := by
{
  unfold weightedInverseArea
  refine setLIntegral_congr_fun measurableSet_S0 (fun z hz => ?_)
  have hy : 0 < z.im := hz.1
  simp only [inverseDensity, planeKClassValue_eq F hz.1]
  rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _),
    inv_pow_four_eq_rpow_neg_four ‖F.F z‖ (norm_nonneg _)]
}

attribute [local irreducible] inverseDensity inverseJacDensity

lemma weighted_inverse_identity (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) {z : ℂ} (hz : z ∈ S0) :
    (∫⁻ F, inverseJacDensity F z ∂P_eigenmeasure) =
      ENNReal.ofReal (z.im ^ (-beta - 4)) *
        (∫⁻ F, inverseDensity F (aff_inv z) ∂P_eigenmeasure) := by
{
  have hy : 0 < z.im := hz.1
  have hden : Measurable (fun F : KClass => inverseDensity F (aff_inv z)) :=
    measurable_inverseDensity.comp (measurable_id.prodMk measurable_const)
  have he := (lemma_3_1_weighted_covariance_lintegral h_rho).2 z hz.1 _ hden
  rw [← h_beta] at he
  have hid (F : KClass) :
      ENNReal.ofReal (A_weight z F.F) *
        inverseDensity ⟨T z F.F, (T_KClass F z hz.1).1, (T_KClass F z hz.1).2.1, (T_KClass F z hz.1).2.2⟩ (aff_inv z) =
        ENNReal.ofReal (z.im ^ 4) * inverseJacDensity F z := by
  {
    unfold inverseDensity inverseJacDensity
    simp only [planeKClassValue_eq _ (aff_inv_mem hz.1),
      planeKClassValue_eq _ hz.1, planeKClassDeriv_eq _ hz.1]
    have hA_nonneg : 0 ≤ A_weight z F.F := by unfold A_weight; positivity
    rw [← ENNReal.ofReal_mul hA_nonneg,
      A_weight_inverse_value F hz, ENNReal.ofReal_mul (pow_nonneg hy.le 4)]
  }
  simp_rw [hid] at he
  have hJac : Measurable (fun F : KClass => inverseJacDensity F z) :=
    measurable_inverseJacDensity.comp (measurable_id.prodMk measurable_const)
  rw [lintegral_const_mul _ hJac] at he
  have hpow : ENNReal.ofReal (z.im ^ 4) * ENNReal.ofReal (z.im ^ (-beta - 4)) =
      ENNReal.ofReal (z.im ^ (-beta)) := by
  {
    rw [← ENNReal.ofReal_mul (pow_nonneg hy.le 4), ← Real.rpow_natCast, ← Real.rpow_add hy]
    congr 2
    ring
  }
  apply (ENNReal.mul_right_inj (by positivity : ENNReal.ofReal (z.im ^ 4) ≠ 0) ENNReal.ofReal_ne_top).mp
  rw [← mul_assoc, hpow]
  exact he
}

lemma weightedInverseArea_pointwise_swap (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) {z : ℂ} (hz : z ∈ S0) :
    ENNReal.ofReal (z.im ^ (beta + 1)) * (∫⁻ F, inverseDensity F z ∂P_eigenmeasure) =
      ENNReal.ofReal (z.im⁻¹ ^ 3) * (∫⁻ F, inverseJacDensity F (aff_inv z) ∂P_eigenmeasure) := by
{
  have hy : 0 < z.im := hz.1
  rw [weighted_inverse_identity h_rho beta h_beta (aff_inv_mem_S0 hz),
    aff_inv_invol hz.1, aff_inv_im, ← mul_assoc]
  congr 1
  rw [← ENNReal.ofReal_mul (pow_nonneg (inv_nonneg.mpr hy.le) 3)]
  congr 1
  rw [Real.inv_rpow hy.le]
  have he : (z.im⁻¹ ^ 3 : ℝ) = z.im ^ (-3 : ℝ) := by
  {
    rw [Real.rpow_neg hy.le]
    norm_cast
    simp
  }
  rw [he, ← Real.rpow_neg hy.le, ← Real.rpow_add hy]
  congr 1
  ring
}

lemma weightedInverseArea_expectation_le (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) :
    (∫⁻ F, weightedInverseArea beta F ∂P_eigenmeasure) ≤ ENNReal.ofReal (256 * Real.pi) := by
{
  haveI : IsProbabilityMeasure P_eigenmeasure := (lemma_3_1_weighted_covariance h_rho).1
  let A (z : ℂ) := ∫⁻ F, inverseJacDensity F z ∂P_eigenmeasure
  let B (z : ℂ) := ∫⁻ F, inverseDensity F z ∂P_eigenmeasure
  have hswap : (∫⁻ F, weightedInverseArea beta F ∂P_eigenmeasure) =
      ∫⁻ z in S0, ENNReal.ofReal (z.im ^ (beta + 1)) * B z := by
  {
    unfold weightedInverseArea
    rw [lintegral_lintegral_swap]
    · refine lintegral_congr (fun z => lintegral_const_mul _ ?_)
      exact measurable_inverseDensity.comp (measurable_id.prodMk measurable_const)
    · exact ((((Complex.continuous_im.comp continuous_snd).measurable.pow measurable_const).ennreal_ofReal).mul
        measurable_inverseDensity).aemeasurable
  }
  rw [hswap, setLIntegral_congr_fun measurableSet_S0
    (fun z hz => weightedInverseArea_pointwise_swap h_rho beta h_beta hz),
    ← aff_inv_change_variables measurableSet_S0 (fun _ h => h.1) aff_inv_image_S0 A]
  have hswap₂ : (∫⁻ z in S0, A z) =
      ∫⁻ F, (∫⁻ z in S0, inverseJacDensity F z) ∂P_eigenmeasure :=
    (lintegral_lintegral_swap measurable_inverseJacDensity.aemeasurable).symm
  rw [hswap₂]
  calc
    _ ≤ ∫⁻ _ : KClass, ENNReal.ofReal (256 * Real.pi) ∂P_eigenmeasure :=
      lintegral_mono inverseJacDensity_integral_le
    _ = _ := by simp
}

lemma continuousOn_I_integrand (beta : ℝ) (F : KClass) :
    ContinuousOn (fun z : ℂ => (z.im : ℝ) ^ (beta + 1) * ‖F.F z‖ ^ (-4 : ℝ)) S0 := by
{
  have hc1 : ContinuousOn (fun z : ℂ => (z.im : ℝ) ^ (beta + 1)) S0 :=
    Complex.continuous_im.continuousOn.rpow_const (fun z hz => Or.inl (ne_of_gt hz.1))
  have hc2 : ContinuousOn (fun z : ℂ => ‖F.F z‖ ^ (-4 : ℝ)) S0 :=
    ((F.univalent.1.continuousOn.mono (fun _ hz => hz.1)).norm).rpow_const
      (fun z hz => Or.inl (norm_ne_zero_iff.mpr (F_ne_zero_S0 F hz)))
  exact hc1.mul hc2
}

lemma I_integrable_iff_weightedInverseArea_lt_top (beta : ℝ) (F : KClass) :
    I_integrable beta F ↔ weightedInverseArea beta F < ∞ := by
{
  have hnonneg : ∀ᵐ z ∂(volume.restrict S0),
      0 ≤ (z.im : ℝ) ^ (beta + 1) * ‖F.F z‖ ^ (-4 : ℝ) :=
    ae_restrict_of_forall_mem measurableSet_S0 (fun z hz =>
      mul_nonneg (Real.rpow_nonneg hz.1.le _) (Real.rpow_nonneg (norm_nonneg _) _))
  rw [I_integrable, IntegrableOn, Integrable,
    and_iff_right ((continuousOn_I_integrand beta F).aestronglyMeasurable measurableSet_S0),
    hasFiniteIntegral_iff_ofReal hnonneg, weightedInverseArea_eq_lintegral]
}

lemma ofReal_I_func_le_weightedInverseArea (beta : ℝ) (F : KClass) :
    ENNReal.ofReal (I_func beta F) ≤ weightedInverseArea beta F := by
{
  by_cases hI : I_integrable beta F
  · have hnonneg : 0 ≤ᵐ[volume.restrict S0]
        (fun z : ℂ => (z.im : ℝ) ^ (beta + 1) * ‖F.F z‖ ^ (-4 : ℝ)) :=
      ae_restrict_of_forall_mem measurableSet_S0 (fun z hz =>
        mul_nonneg (Real.rpow_nonneg hz.1.le _) (Real.rpow_nonneg (norm_nonneg _) _))
    rw [I_func, ofReal_integral_eq_lintegral_ofReal hI hnonneg, weightedInverseArea_eq_lintegral]
  · have hzero : I_func beta F = 0 := integral_undef hI
    rw [hzero, ENNReal.ofReal_zero]
    exact zero_le
}

theorem lemma_4_2_weighted_inverse_area (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) :
  (∀ᵐ F ∂P_eigenmeasure, I_integrable beta F) ∧
  ∫ F, I_func beta F ∂P_eigenmeasure ≤ 256 * Real.pi := by
{
  have hexp := weightedInverseArea_expectation_le h_rho beta h_beta
  have hae : ∀ᵐ F ∂P_eigenmeasure, weightedInverseArea beta F < ∞ :=
    ae_lt_top (measurable_weightedInverseArea beta)
      (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hexp)
  have hae_int : ∀ᵐ F ∂P_eigenmeasure, I_integrable beta F := by
  {
    filter_upwards [hae] with F hF
    exact (I_integrable_iff_weightedInverseArea_lt_top beta F).mpr hF
  }
  refine ⟨hae_int, ?_⟩
  by_cases hint : Integrable (I_func beta) P_eigenmeasure
  · have hnonneg : 0 ≤ᵐ[P_eigenmeasure] I_func beta :=
      Eventually.of_forall (fun F => setIntegral_nonneg measurableSet_S0
        (fun z hz => mul_nonneg (Real.rpow_nonneg hz.1.le _) (Real.rpow_nonneg (norm_nonneg _) _)))
    have hle : ENNReal.ofReal (∫ F, I_func beta F ∂P_eigenmeasure) ≤ ENNReal.ofReal (256 * Real.pi) := by
    {
      rw [ofReal_integral_eq_lintegral_ofReal hint hnonneg]
      exact (lintegral_mono (ofReal_I_func_le_weightedInverseArea beta)).trans hexp
    }
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hle
  · rw [integral_undef hint]
    positivity
}

/-!
PAPER: 4.2 Escape and horizontal preimage length
PAPER: Lemma 4.3 (Escape and trace bounds). Let F ∈ K satisfy I(F) < ∞. Then
PAPER: y^k / |F(x + iy)| → 0 as |x| + y → ∞. (4.6)
-/

lemma integral_closedBall_translate {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : ℂ → E) (z : ℂ) (r : ℝ) :
    (∫ w in Metric.closedBall (0 : ℂ) r, f (w + z)) = ∫ w in Metric.closedBall z r, f w := by
{
  have he : (fun w : ℂ => w + z) ⁻¹' Metric.closedBall z r = Metric.closedBall 0 r := by
  {
    ext w
    simp [Metric.mem_closedBall, dist_eq_norm]
  }
  rw [← he]
  exact (measurePreserving_add_right volume z).setIntegral_preimage_emb
    (Homeomorph.addRight z).measurableEmbedding f _
}

lemma volume_real_closedBall_complex (z : ℂ) {r : ℝ} (hr : 0 ≤ r) :
    volume.real (Metric.closedBall z r) = Real.pi * r ^ 2 := by
{
  rw [measureReal_def, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
    ENNReal.toReal_ofReal hr]
  simp only [ENNReal.coe_toReal, NNReal.coe_real_pi]
  ring
}

lemma holomorphic_sq_submean_center {f : ℂ → ℂ} {z : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball z R)) (hr : 0 < r) (hrR : r < R) :
    Real.pi * r ^ 2 * ‖f z‖^2 ≤ ∫ w in Metric.closedBall z r, ‖f w‖^2 := by
{
  have hfd : DifferentiableOn ℂ (fun w => f (w + z)) (Metric.ball 0 R) := by
  {
    apply hf.comp (differentiable_id.add_const z).differentiableOn
    intro w hw
    simpa [Metric.mem_ball, dist_eq_norm] using hw
  }
  have hh := Brennan.Koebe.holomorphic_sq_submean hfd hr hrR
  rw [integral_closedBall_translate (fun w => ‖f w‖^2) z r] at hh
  simpa only [volume_real_closedBall_complex 0 hr.le, zero_add] using hh
}

lemma holomorphic_sq_submean_lintegral {f : ℂ → ℂ} {z : ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball z R)) (hr : 0 < r) (hrR : r < R) :
    ENNReal.ofReal (Real.pi * r ^ 2 * ‖f z‖^2) ≤
      ∫⁻ w in Metric.closedBall z r, ENNReal.ofReal (‖f w‖^2) := by
{
  have hi : IntegrableOn (fun w => ‖f w‖^2) (Metric.closedBall z r) volume :=
    ((hf.continuousOn.mono (Metric.closedBall_subset_ball hrR)).norm.pow 2).integrableOn_compact
      (isCompact_closedBall z r)
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun _ => sq_nonneg _))]
  exact ENNReal.ofReal_le_ofReal (holomorphic_sq_submean_center hf hr hrR)
}

lemma finite_density_compact_tail (s : Set ℂ) (b : ℂ → ℝ≥0∞)
    (hf : (∫⁻ z in s, b z) < ∞) {ε : ℝ≥0∞} (hε : 0 < ε) :
    ∃ K : Set ℂ, IsCompact K ∧ (∫⁻ z in s \ K, b z) < ε := by
{
  let ν : Measure ℂ := (volume.restrict s).withDensity b
  haveI : IsFiniteMeasure ν := isFiniteMeasure_withDensity hf.ne
  let A (n : ℕ) : Set ℂ := (Metric.closedBall (0 : ℂ) n)ᶜ
  have hanti : Antitone A := fun m n hmn =>
    compl_subset_compl.mpr (Metric.closedBall_subset_closedBall (Nat.cast_le.mpr hmn))
  have hmeas (n : ℕ) : NullMeasurableSet (A n) ν :=
    (isCompact_closedBall (0 : ℂ) n).isClosed.measurableSet.compl.nullMeasurableSet
  have hempty : (⋂ n : ℕ, A n) = ∅ := by
  {
    ext z
    simp only [A, mem_iInter, mem_compl_iff, Metric.mem_closedBall, dist_zero_right,
      not_le, mem_empty_iff_false, iff_false, not_forall, not_lt]
    exact exists_nat_ge ‖z‖
  }
  have htend := tendsto_measure_iInter_atTop hmeas hanti ⟨0, measure_ne_top ν (A 0)⟩
  rw [hempty, measure_empty] at htend
  obtain ⟨n, hn⟩ := (htend.eventually (gt_mem_nhds hε)).exists
  refine ⟨Metric.closedBall (0 : ℂ) n, isCompact_closedBall (0 : ℂ) n, ?_⟩
  have he : ν (A n) = ∫⁻ z in s \ Metric.closedBall (0 : ℂ) n, b z := by
  {
    have hsK : A n ∩ s = s \ Metric.closedBall (0 : ℂ) n := by ext z; simp [A, and_comm]
    rw [withDensity_apply _ (isCompact_closedBall (0 : ℂ) n).isClosed.measurableSet.compl,
      Measure.restrict_restrict (isCompact_closedBall (0 : ℂ) n).isClosed.measurableSet.compl, hsK]
  }
  rw [Function.comp_apply, he] at hn
  exact hn
}

lemma tail_ball_disjoint {R₀ M : ℝ} {K : Set ℂ}
    (hM : K ⊆ Metric.closedBall 0 M) {z w : ℂ} (hy : 0 < z.im)
    (hz : 2 * (max R₀ M + 1) ≤ ‖z‖) (hw : w ∈ Metric.ball z (z.im / 2)) :
    0 < w.im ∧ R₀ < ‖w‖ ∧ w ∉ K := by
{
  have hd : ‖w - z‖ < z.im / 2 := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hi := Complex.abs_im_le_norm (w - z)
  rw [Complex.sub_im] at hi
  have him : z.im / 2 < w.im := by linarith [neg_le_of_abs_le hi]
  have himz : z.im ≤ ‖z‖ := (le_abs_self _).trans (Complex.abs_im_le_norm z)
  have hnw := norm_sub_norm_le z w
  rw [norm_sub_rev z w] at hnw
  have hnw' : max R₀ M < ‖w‖ := by nlinarith [le_max_left R₀ M]
  refine ⟨by linarith, lt_of_le_of_lt (le_max_left _ _) hnw', fun hwK => ?_⟩
  have hm : ‖w‖ ≤ M := by simpa [Metric.mem_closedBall, dist_zero_right] using hM hwK
  exact (not_lt_of_ge (hm.trans (le_max_right _ _))) hnw'
}

lemma weighted_submean_ball_le {q : ℂ → ℂ} {s K : Set ℂ} {a : ℝ} (ha : 0 ≤ a)
    {z : ℂ} (hy : 0 < z.im) (hhol : DifferentiableOn ℂ q (Metric.ball z (z.im / 2)))
    (hsub : Metric.closedBall z (z.im / 4) ⊆ s \ K)
    (hwi : ∀ w ∈ Metric.closedBall z (z.im / 4), 0 < w.im) :
    ENNReal.ofReal (z.im ^ (a + 2) * ‖q z‖^2) ≤
      ENNReal.ofReal (16 * (2 : ℝ) ^ a / Real.pi) *
        (∫⁻ w in s \ K, ENNReal.ofReal (w.im ^ a * ‖q w‖^2)) := by
{
  have hcomp (w : ℂ) (hw : w ∈ Metric.closedBall z (z.im / 4)) :
      z.im ^ a * ‖q w‖^2 ≤ (2 : ℝ) ^ a * (w.im ^ a * ‖q w‖^2) := by
  {
    have hd : ‖w - z‖ ≤ z.im / 4 := by simpa only [Metric.mem_closedBall, dist_eq_norm] using hw
    have hi := Complex.abs_im_le_norm (w - z)
    rw [Complex.sub_im] at hi
    have hle : z.im ≤ 2 * w.im := by linarith [neg_le_of_abs_le hi]
    have hh := Real.rpow_le_rpow hy.le hle ha
    rw [Real.mul_rpow (by norm_num) (hwi w hw).le] at hh
    nlinarith [sq_nonneg ‖q w‖]
  }
  have hweighted : ENNReal.ofReal (z.im ^ a) *
      (∫⁻ w in Metric.closedBall z (z.im / 4), ENNReal.ofReal (‖q w‖^2)) ≤
      ENNReal.ofReal ((2 : ℝ) ^ a) * (∫⁻ w in s \ K, ENNReal.ofReal (w.im ^ a * ‖q w‖^2)) := by
  {
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
      ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine le_trans (setLIntegral_mono' measurableSet_closedBall (fun w hw => ?_))
      (lintegral_mono_set hsub)
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _),
      ← ENNReal.ofReal_mul (Real.rpow_nonneg (by norm_num) _)]
    exact ENNReal.ofReal_le_ofReal (hcomp w hw)
  }
  have hmean := holomorphic_sq_submean_lintegral hhol (by linarith : 0 < z.im / 4) (by linarith)
  have hh := (mul_le_mul' (le_refl (ENNReal.ofReal (z.im ^ a))) hmean).trans hweighted
  have hmul : ENNReal.ofReal (z.im ^ a) * ENNReal.ofReal (Real.pi * (z.im / 4) ^ 2 * ‖q z‖^2) =
      ENNReal.ofReal (Real.pi / 16) * ENNReal.ofReal (z.im ^ (a + 2) * ‖q z‖^2) := by
  {
    rw [← ENNReal.ofReal_mul (Real.rpow_nonneg hy.le _),
      ← ENNReal.ofReal_mul (by positivity), Real.rpow_add hy, Real.rpow_two]
    congr 1; ring
  }
  rw [hmul] at hh
  apply (ENNReal.mul_le_mul_iff_right (by positivity : ENNReal.ofReal (Real.pi / 16) ≠ 0)
    ENNReal.ofReal_ne_top).mp
  have he : ENNReal.ofReal (Real.pi / 16) * ENNReal.ofReal (16 * (2 : ℝ) ^ a / Real.pi) =
      ENNReal.ofReal ((2 : ℝ) ^ a) := by
  {
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1; field_simp
  }
  rwa [← mul_assoc, he]
}

lemma weighted_holomorphic_tail {q : ℂ → ℂ} {s : Set ℂ} {a R₀ : ℝ}
    (ha : 0 ≤ a)
    (hs : ∀ z : ℂ, 0 < z.im → R₀ < ‖z‖ → z ∈ s)
    (hq : ∀ z ∈ s, DifferentiableAt ℂ q z)
    (hfin : (∫⁻ z in s, ENNReal.ofReal (z.im ^ a * ‖q z‖^2)) < ∞) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ →
      z.im ^ (a + 2) * ‖q z‖^2 < ε := by
{
  intro ε hε
  let C : ℝ := 16 * (2 : ℝ) ^ a / Real.pi
  have hC : 0 < C := by dsimp [C]; positivity
  obtain ⟨K, hK, hKε⟩ := finite_density_compact_tail s
    (fun z => ENNReal.ofReal (z.im ^ a * ‖q z‖^2)) hfin
    (ENNReal.ofReal_pos.mpr (div_pos hε hC))
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨2 * (max R₀ M + 1), fun z hy hz => ?_⟩
  have hball (w : ℂ) (hw : w ∈ Metric.ball z (z.im / 2)) :=
    tail_ball_disjoint hM hy hz hw
  have hhol : DifferentiableOn ℂ q (Metric.ball z (z.im / 2)) := fun w hw =>
    (hq w (hs w (hball w hw).1 (hball w hw).2.1)).differentiableWithinAt
  have hsmall : Metric.closedBall z (z.im / 4) ⊆ Metric.ball z (z.im / 2) :=
    Metric.closedBall_subset_ball (by linarith)
  have hsub : Metric.closedBall z (z.im / 4) ⊆ s \ K := fun w hw =>
    ⟨hs w (hball w (hsmall hw)).1 (hball w (hsmall hw)).2.1, (hball w (hsmall hw)).2.2⟩
  have hineq := weighted_submean_ball_le ha hy hhol hsub (fun w hw => (hball w (hsmall hw)).1)
  have hh := hineq.trans_lt ((ENNReal.mul_lt_mul_iff_right (ENNReal.ofReal_pos.mpr hC).ne'
    ENNReal.ofReal_ne_top).mpr hKε)
  have he : ENNReal.ofReal C * ENNReal.ofReal (ε / C) = ENNReal.ofReal ε := by
  {
    rw [← ENNReal.ofReal_mul hC.le, mul_div_cancel₀ ε (ne_of_gt hC)]
  }
  dsimp only [C] at he hh
  rw [he] at hh
  exact (ENNReal.ofReal_lt_ofReal_iff hε).mp hh
}

def HasQuarticTail (F : ℂ → ℂ) (a : ℝ) : Prop :=
  ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ →
    z.im ^ a * ‖F z‖⁻¹ ^ 4 < ε

lemma quartic_tail_iff_power {F : ℂ → ℂ} {k : ℝ} (ht : HasQuarticTail F (4 * k)) :
    ∀ ε : ℝ, 0 < ε → ∃ R : ℝ, ∀ z : ℂ, 0 < z.im → R ≤ ‖z‖ →
      z.im ^ k * ‖F z‖⁻¹ < ε := by
{
  intro ε hε
  obtain ⟨R, hR⟩ := ht (ε ^ 4) (pow_pos hε _)
  refine ⟨R, fun z hz hzr => ?_⟩
  have hh := hR z hz hzr
  have he : z.im ^ (4 * k) * ‖F z‖⁻¹ ^ 4 = (z.im ^ k * ‖F z‖⁻¹) ^ 4 := by
  {
    rw [mul_comm (4 : ℝ) k, Real.rpow_mul hz.le, Real.rpow_ofNat, mul_pow]
  }
  rw [he] at hh
  by_contra! hle
  exact (not_lt_of_ge (pow_le_pow_left₀ hε.le hle 4)) hh
}

lemma S0_of_norm {z : ℂ} (hz : z ∈ H) (hn : 3 < ‖z‖) : z ∈ S0 := by
{
  refine ⟨hz, ?_⟩
  change (1 / 2 : ℝ) ≤ ‖(z - I) / (z + I)‖
  rw [norm_div, le_div_iff₀ (norm_pos_iff.mpr (inv_cayley_den_ne_zero hz))]
  have h₁ : ‖z‖ ≤ ‖z - I‖ + 1 := by
  {
    simpa only [sub_add_cancel, Complex.norm_I] using norm_add_le (z - I) I
  }
  have h₂ : ‖z + I‖ ≤ ‖z‖ + 1 := by
  {
    simpa only [Complex.norm_I] using norm_add_le z I
  }
  linarith
}

lemma KClass_quartic_tail (F : KClass) {beta : ℝ} (h_beta : beta > 1)
    (hI : I_integrable beta F) :
    HasQuarticTail F.F (beta + 3) := by
{
  let q : ℂ → ℂ := fun z => (F.F z)⁻¹ ^ 2
  have hnorm (z : ℂ) : ‖q z‖^2 = ‖F.F z‖⁻¹ ^ 4 := by
  {
    simp only [q, norm_pow, norm_inv, ← pow_mul]
  }
  have hhol (z : ℂ) (hz : z ∈ S0) : DifferentiableAt ℂ q z :=
    (((F.univalent.1 _ hz.1).differentiableAt (isOpen_H.mem_nhds hz.1)).inv
      (F_ne_zero_S0 F hz)).pow 2
  have hfin := (I_integrable_iff_weightedInverseArea_lt_top beta F).mp hI
  rw [weightedInverseArea_eq_lintegral] at hfin
  have hfq : (∫⁻ z in S0, ENNReal.ofReal (z.im ^ (beta + 1) * ‖q z‖^2)) < ∞ := by
  {
    convert hfin using 1
    refine setLIntegral_congr_fun measurableSet_S0 (fun z _ => ?_)
    rw [hnorm, inv_pow_four_eq_rpow_neg_four ‖F.F z‖ (norm_nonneg _)]
  }
  have hh := weighted_holomorphic_tail (R₀ := 3) (by linarith : 0 ≤ beta + 1)
    (fun z hz hn => S0_of_norm hz hn) hhol hfq
  intro ε hε
  obtain ⟨R, hR⟩ := hh ε hε
  refine ⟨R, fun z hz hzr => ?_⟩
  have he : beta + 1 + 2 = beta + 3 := by ring
  simpa only [he, hnorm] using hR z hz hzr
}

theorem lemma_4_3_escape (beta : ℝ) (h_beta : beta > 1) (F : KClass) (hI : I_integrable beta F) :
  Filter.Tendsto (fun z : ℂ => V_target beta F 0 z)
    (Filter.comap (fun z : ℂ => abs z.re + z.im) Filter.atTop) (𝓝 0) := by
{
  have ht : HasQuarticTail F.F (4 * k_val beta) := by
  {
    convert KClass_quartic_tail F h_beta hI using 1
    unfold k_val; ring
  }
  rw [ENNReal.tendsto_nhds_zero]
  intro ε hε
  obtain ⟨δ, hδ, hδ_le⟩ : ∃ δ : ℝ, 0 < δ ∧ ENNReal.ofReal δ ≤ ε := by
  {
    rcases eq_or_ne ε ⊤ with rfl | htop
    · exact ⟨1, zero_lt_one, le_top⟩
    · exact ⟨ε.toReal, ENNReal.toReal_pos hε.ne' htop, by simp [htop]⟩
  }
  obtain ⟨R, hR⟩ := quartic_tail_iff_power ht δ hδ
  rw [Filter.Eventually, Filter.mem_comap]
  refine ⟨Ici (2 * max R 4), Filter.mem_atTop _, fun z hz => ?_⟩
  by_cases hzH : z ∈ H
  · have hy : 0 < z.im := hzH
    have hnorm : max R 4 ≤ ‖z‖ := by
    {
      have hre : |z.re| ≤ ‖z‖ := Complex.abs_re_le_norm z
      have him : z.im ≤ ‖z‖ := (le_abs_self _).trans (Complex.abs_im_le_norm z)
      change 2 * max R 4 ≤ |z.re| + z.im at hz
      linarith
    }
    have hFz : F.F z ≠ 0 := F_ne_zero_S0 F (S0_of_norm hzH (by linarith [le_max_right R 4]))
    have hpow := hR z hy ((le_max_left R 4).trans hnorm)
    have hV : V_target beta F 0 z = ENNReal.ofReal (z.im ^ k_val beta * ‖F.F z‖⁻¹) := by
    {
      simp only [V_target, hzH, ite_true, sub_zero]
      rw [← ENNReal.ofReal_div_of_pos (norm_pos_iff.mpr hFz), div_eq_mul_inv]
    }
    rw [Set.mem_setOf_eq, hV]
    exact (ENNReal.ofReal_le_ofReal hpow.le).trans hδ_le
  · simp [V_target, hzH]
}

lemma quartic_tail_proper {F : ℂ → ℂ} {a R₀ : ℝ}
    (ha : 0 ≤ a) (ht : HasQuarticTail F a)
    (hzero : ∀ z : ℂ, 0 < z.im → R₀ < ‖z‖ → F z ≠ 0)
    (hc : ContinuousOn F {z | 0 < z.im}) {K : Set ℂ} (hK : IsCompact K)
    {η : ℝ} (hη : 0 < η) : IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' K) := by
{
  obtain ⟨M₀, hM₀⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let M := max M₀ 1
  have hM : 0 < M := lt_of_lt_of_le (by norm_num) (le_max_right M₀ 1)
  have hδ : 0 < η ^ a * M⁻¹ ^ 4 := mul_pos (Real.rpow_pos_of_pos hη _) (pow_pos (inv_pos.mpr hM) _)
  obtain ⟨R, hR⟩ := ht (η ^ a * M⁻¹ ^ 4) hδ
  have hb : {z : ℂ | η ≤ z.im} ∩ F ⁻¹' K ⊆ Metric.closedBall 0 (max R (R₀ + 1)) := by
  {
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra! hzn
    have hy : 0 < z.im := hη.trans_le hz.1
    have hznR : R ≤ ‖z‖ := (le_max_left _ _).trans hzn.le
    have hzn₀ : R₀ < ‖z‖ := by linarith [le_max_right R (R₀ + 1)]
    have hFn : 0 < ‖F z‖ := norm_pos_iff.mpr (hzero z hy hzn₀)
    have hFle : ‖F z‖ ≤ M := (show ‖F z‖ ≤ M₀ by simpa using hM₀ hz.2).trans (le_max_left _ _)
    have hpow : M⁻¹ ^ 4 ≤ ‖F z‖⁻¹ ^ 4 :=
      pow_le_pow_left₀ (inv_nonneg.mpr hM.le) ((inv_le_inv₀ hM hFn).mpr hFle) 4
    have hheight := Real.rpow_le_rpow hη.le hz.1 ha
    have hle := mul_le_mul hheight hpow (by positivity) (Real.rpow_nonneg hy.le _)
    exact (not_lt_of_ge hle) (hR z hy hznR)
  }
  refine (isCompact_closedBall (0 : ℂ) (max R (R₀ + 1))).of_isClosed_subset ?_ hb
  exact (hc.mono (fun _ hz => hη.trans_le hz)).preimage_isClosed_of_isClosed
    (isClosed_le continuous_const Complex.continuous_im) hK.isClosed
}

lemma quartic_tail_height_bound {F : ℂ → ℂ} {a R₀ : ℝ}
    (ha : 0 ≤ a) (ht : HasQuarticTail F a)
    (hzero : ∀ z : ℂ, 0 < z.im → R₀ < ‖z‖ → F z ≠ 0)
    (hc : ContinuousOn F {z | 0 < z.im}) {K : Set ℂ} (hK : IsCompact K) :
    ∃ H_max : ℝ, 0 < H_max ∧ ∀ z : ℂ, 0 < z.im → F z ∈ K → z.im ≤ H_max := by
{
  have hk := quartic_tail_proper ha ht hzero hc hK (by norm_num : (0 : ℝ) < 1)
  obtain ⟨M, hM⟩ := hk.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨max M 1, lt_of_lt_of_le (by norm_num) (le_max_right M 1), fun z _ hz => ?_⟩
  by_cases hy : 1 ≤ z.im
  · have hh : ‖z‖ ≤ M := by simpa using hM ⟨hy, hz⟩
    exact ((le_abs_self z.im).trans (Complex.abs_im_le_norm z)).trans (hh.trans (le_max_left _ _))
  · exact (le_of_lt (lt_of_not_ge hy)).trans (le_max_right _ _)
}

lemma KClass_proper_preimage (F : KClass) {beta : ℝ} (h_beta : beta > 1)
    (hI : I_integrable beta F) {K : Set ℂ} (hK : IsCompact K) {η : ℝ} (hη : 0 < η) :
    IsCompact ({z : ℂ | η ≤ z.im} ∩ F.F ⁻¹' K) := by
{
  exact quartic_tail_proper (by linarith : 0 ≤ beta + 3) (KClass_quartic_tail F h_beta hI)
    (fun _ hz hn => F_ne_zero_S0 F (S0_of_norm hz hn))
    F.univalent.1.continuousOn hK hη
}

lemma KClass_preimage_height_bound (F : KClass) {beta : ℝ} (h_beta : beta > 1)
    (hI : I_integrable beta F) {K : Set ℂ} (hK : IsCompact K) :
    ∃ H_max : ℝ, 0 < H_max ∧ ∀ z : ℂ, 0 < z.im → F.F z ∈ K → z.im ≤ H_max := by
{
  exact quartic_tail_height_bound (by linarith : 0 ≤ beta + 3) (KClass_quartic_tail F h_beta hI)
    (fun _ hz hn => F_ne_zero_S0 F (S0_of_norm hz hn))
    F.univalent.1.continuousOn hK
}

def pairLaplacian (g : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  fderiv ℝ (fderiv ℝ g) p (1, 0) (1, 0) + fderiv ℝ (fderiv ℝ g) p (0, 1) (0, 1)

def traceFluxX (g : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.2 - ε) * fderiv ℝ g p (1, 0)

def traceFluxY (g : ℝ × ℝ → ℝ) (ε : ℝ) (p : ℝ × ℝ) : ℝ :=
  (p.2 - ε) * fderiv ℝ g p (0, 1) - g p

lemma traceFlux_contDiffAt {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 g p) (ε : ℝ) :
    ContDiffAt ℝ 1 (traceFluxX g ε) p ∧ ContDiffAt ℝ 1 (traceFluxY g ε) p := by
{
  have hd : ContDiffAt ℝ 1 (fderiv ℝ g) p := hg.fderiv_right (by norm_num)
  have htr : ContDiffAt ℝ 1 g p := hg.of_le (by norm_num)
  refine ⟨by unfold traceFluxX; fun_prop, by unfold traceFluxY; fun_prop⟩
}

lemma divergence_traceFlux {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 g p) (ε : ℝ) :
    fderiv ℝ (traceFluxX g ε) p (1, 0) + fderiv ℝ (traceFluxY g ε) p (0, 1) =
      (p.2 - ε) * pairLaplacian g p := by
{
  have hdg := hg.differentiableAt (by norm_num)
  have hddg := (hg.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hx := hddg.hasFDerivAt.clm_apply (hasFDerivAt_const ((1, 0) : ℝ × ℝ) p)
  have hy := hddg.hasFDerivAt.clm_apply (hasFDerivAt_const ((0, 1) : ℝ × ℝ) p)
  have hs : HasFDerivAt (fun p : ℝ × ℝ => p.2 - ε) (ContinuousLinearMap.snd ℝ ℝ ℝ) p :=
    (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt.sub_const ε
  unfold traceFluxX traceFluxY
  have hfx := (hs.mul hx).fderiv
  have hfy := ((hs.mul hy).sub hdg.hasFDerivAt).fderiv
  change fderiv ℝ (fun p => (p.2 - ε) * fderiv ℝ g p (1, 0)) p = _ at hfx
  change fderiv ℝ (fun p => (p.2 - ε) * fderiv ℝ g p (0, 1) - g p) p = _ at hfy
  rw [hfx, hfy]
  simp [pairLaplacian, ContinuousLinearMap.flip_apply, mul_add]
}

lemma continuousAt_pairLaplacian {g : ℝ × ℝ → ℝ} {p : ℝ × ℝ}
    (hg : ContDiffAt ℝ 2 g p) : ContinuousAt (pairLaplacian g) p := by
{
  have hh : ContDiffAt ℝ 0 (fderiv ℝ (fderiv ℝ g)) p :=
    (hg.fderiv_right (m := 1) (by norm_num)).fderiv_right (by norm_num)
  have hc := hh.continuousAt
  unfold pairLaplacian
  fun_prop
}

lemma rectangle_divergence_integral {g : ℝ × ℝ → ℝ} {R ε Y : ℝ}
    (hR : 0 ≤ R) (hεY : ε ≤ Y)
    (hg : ∀ p ∈ Icc (-R, ε) (R, Y), ContDiffAt ℝ 2 g p) :
    (∫ p in Icc (-R, ε) (R, Y), (p.2 - ε) * pairLaplacian g p) =
      ((∫ x in -R..R, traceFluxY g ε (x, Y)) - ∫ x in -R..R, traceFluxY g ε (x, ε)) +
      (∫ y in ε..Y, traceFluxX g ε (R, y)) - ∫ y in ε..Y, traceFluxX g ε (-R, y) := by
{
  have hf : ContinuousOn (traceFluxX g ε) (Icc (-R, ε) (R, Y)) :=
    fun p hp => ((traceFlux_contDiffAt (hg p hp) ε).1.continuousAt).continuousWithinAt
  have hh : ContinuousOn (traceFluxY g ε) (Icc (-R, ε) (R, Y)) :=
    fun p hp => ((traceFlux_contDiffAt (hg p hp) ε).2.continuousAt).continuousWithinAt
  have hint : IntegrableOn (fun p : ℝ × ℝ => (p.2 - ε) * pairLaplacian g p)
      (Icc (-R, ε) (R, Y)) volume := by
  {
    refine ContinuousOn.integrableOn_compact isCompact_Icc (fun p hp => ?_)
    have hc : ContinuousAt (fun p : ℝ × ℝ => (p.2 - ε) * pairLaplacian g p) p :=
      (continuous_snd.continuousAt.sub continuousAt_const).mul (continuousAt_pairLaplacian (hg p hp))
    exact hc.continuousWithinAt
  }
  have heq (p : ℝ × ℝ) (hp : p ∈ Icc (-R, ε) (R, Y)) := divergence_traceFlux (hg p hp) ε
  have hi : IntegrableOn (fun p => fderiv ℝ (traceFluxX g ε) p (1, 0) +
      fderiv ℝ (traceFluxY g ε) p (0, 1)) (Icc (-R, ε) (R, Y)) volume :=
    hint.congr (ae_restrict_of_forall_mem measurableSet_Icc (fun p hp => (heq p hp).symm))
  have hb := integral_divergence_prod_Icc_of_hasFDerivAt_of_le
    (traceFluxX g ε) (traceFluxY g ε) (fderiv ℝ (traceFluxX g ε))
    (fderiv ℝ (traceFluxY g ε)) (-R, ε) (R, Y) ⟨by linarith, hεY⟩ hf hh
    (fun p hp => ((traceFlux_contDiffAt (hg p ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩) ε).1.differentiableAt (by norm_num)).hasFDerivAt)
    (fun p hp => ((traceFlux_contDiffAt (hg p ⟨⟨hp.1.1.le, hp.2.1.le⟩, ⟨hp.1.2.le, hp.2.2.le⟩⟩) ε).2.differentiableAt (by norm_num)).hasFDerivAt) hi
  rw [setIntegral_congr_fun measurableSet_Icc heq] at hb
  exact hb
}

lemma rectangle_trace_identity {g : ℝ × ℝ → ℝ} {R ε Y : ℝ}
    (hR : 0 ≤ R) (hεY : ε ≤ Y)
    (hg : ∀ p ∈ Icc (-R, ε) (R, Y), ContDiffAt ℝ 2 g p)
    (htop : ∀ x ∈ Icc (-R) R, g (x, Y) = 0 ∧ fderiv ℝ g (x, Y) (0, 1) = 0)
    (hside : ∀ y ∈ Icc ε Y,
      fderiv ℝ g (-R, y) (1, 0) = 0 ∧ fderiv ℝ g (R, y) (1, 0) = 0) :
    (∫ p in Icc (-R, ε) (R, Y), (p.2 - ε) * pairLaplacian g p) =
      ∫ x in -R..R, g (x, ε) := by
{
  have hb := rectangle_divergence_integral hR hεY hg
  have ht : (∫ x in -R..R, traceFluxY g ε (x, Y)) = 0 := by
  {
    rw [← intervalIntegral.integral_zero]
    refine intervalIntegral.integral_congr (fun x hx => ?_)
    have hx' : x ∈ Icc (-R) R := by simpa only [uIcc_of_le (by linarith : -R ≤ R)] using hx
    simp [traceFluxY, (htop x hx').1, (htop x hx').2]
  }
  have hl : (∫ y in ε..Y, traceFluxX g ε (-R, y)) = 0 := by
  {
    rw [← intervalIntegral.integral_zero]
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    simp [traceFluxX, (hside y (by simpa only [uIcc_of_le hεY] using hy)).1]
  }
  have hr : (∫ y in ε..Y, traceFluxX g ε (R, y)) = 0 := by
  {
    rw [← intervalIntegral.integral_zero]
    refine intervalIntegral.integral_congr (fun y hy => ?_)
    simp [traceFluxX, (hside y (by simpa only [uIcc_of_le hεY] using hy)).2]
  }
  rw [ht, hl, hr] at hb
  simpa only [traceFluxY, sub_self, zero_mul, zero_sub,
    intervalIntegral.integral_neg, sub_neg_eq_add, zero_add, add_zero, sub_zero] using hb
}

lemma half_trace_zero_outside_ball {g : ℝ × ℝ → ℝ} {ε M : ℝ} {K : Set (ℝ × ℝ)}
    (hM : K ⊆ Metric.closedBall (0 : ℝ × ℝ) M)
    (hs : ∀ p : ℝ × ℝ, ε / 2 ≤ p.2 → g p ≠ 0 → p ∈ K) :
    (∀ p : ℝ × ℝ, ε / 2 ≤ p.2 → M < ‖p‖ → g p = 0) ∧
    (∀ p : ℝ × ℝ, ε / 2 < p.2 → M < ‖p‖ → fderiv ℝ g p = 0) := by
{
  have hz (p : ℝ × ℝ) (hy : ε / 2 ≤ p.2) (hn : M < ‖p‖) : g p = 0 := by
  {
    by_contra hg
    have hh : ‖p‖ ≤ M := by simpa using hM (hs p hy hg)
    exact (not_lt_of_ge hh) hn
  }
  refine ⟨hz, fun p hy hn => ?_⟩
  have hznhd : g =ᶠ[𝓝 p] (0 : ℝ × ℝ → ℝ) := by
  {
    filter_upwards [(isOpen_lt continuous_const continuous_snd).mem_nhds hy,
      (isOpen_lt continuous_const continuous_norm).mem_nhds hn] with q hq₁ hq₂
    exact hz q hq₁.le hq₂
  }
  rw [hznhd.fderiv_eq, fderiv_zero]
  rfl
}

lemma half_trace_rectangle {g : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hc : ∀ p : ℝ × ℝ, 0 < p.2 → ContDiffAt ℝ 2 g p)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hs : ∀ p : ℝ × ℝ, ε / 2 ≤ p.2 → g p ≠ 0 → p ∈ K) :
    ∃ R : ℝ, 0 < R ∧ ε ≤ R ∧ Integrable (fun x : ℝ => g (x, ε)) ∧
      (∫ x : ℝ, g (x, ε)) =
        ∫ p in Icc (-R, ε) (R, R), (p.2 - ε) * pairLaplacian g p := by
{
  obtain ⟨M, hM⟩ := hK.isBounded.subset_closedBall (0 : ℝ × ℝ)
  obtain ⟨hz, hd⟩ := half_trace_zero_outside_ball hM hs
  let R := max M ε + 1
  have hR : 0 < R := by dsimp only [R]; linarith [le_max_right M ε]
  have hεR : ε ≤ R := by dsimp only [R]; linarith [le_max_right M ε]
  have hMR : M < R := by dsimp only [R]; linarith [le_max_left M ε]
  have htop (x : ℝ) (_ : x ∈ Icc (-R) R) : g (x, R) = 0 ∧ fderiv ℝ g (x, R) (0, 1) = 0 := by
  {
    have hn : M < ‖(x, R)‖ := hMR.trans_le (by simp [abs_of_pos hR])
    exact ⟨hz (x, R) (by linarith) hn, by rw [hd (x, R) (by linarith) hn]; rfl⟩
  }
  have hside (y : ℝ) (hy : y ∈ Icc ε R) :
      fderiv ℝ g (-R, y) (1, 0) = 0 ∧ fderiv ℝ g (R, y) (1, 0) = 0 := by
  {
    have h₁ : M < ‖(-R, y)‖ := hMR.trans_le (by simp [abs_of_pos hR])
    have h₂ : M < ‖(R, y)‖ := hMR.trans_le (by simp [abs_of_pos hR])
    rw [hd (-R, y) (by linarith [hy.1]) h₁, hd (R, y) (by linarith [hy.1]) h₂]; simp
  }
  have hb := rectangle_trace_identity hR.le hεR (fun p hp => hc p (hε.trans_le hp.1.2)) htop hside
  have hzero (x : ℝ) (hx : x ∉ Icc (-R) R) : g (x, ε) = 0 := by
  {
    have hh : R < |x| := by
    {
      rcases (by simpa only [mem_Icc, not_and_or, not_le] using hx : x < -R ∨ R < x) with h | h
      · exact (lt_neg_of_lt_neg h).trans_le (neg_le_abs x)
      · exact h.trans_le (le_abs_self x)
    }
    exact hz (x, ε) (by linarith) (hMR.trans (hh.trans_le (norm_fst_le (x, ε))))
  }
  have hcont : Continuous (fun x : ℝ => g (x, ε)) :=
    continuous_iff_continuousAt.mpr (fun x => (hc (x, ε) hε).continuousAt.comp
      (f := fun x : ℝ => (x, ε)) (continuous_id.prodMk continuous_const).continuousAt)
  have hint := hcont.continuousOn.integrableOn_compact (μ := volume) (isCompact_Icc (a := -R) (b := R))
  have hline : (∫ x in -R..R, g (x, ε)) = ∫ x : ℝ, g (x, ε) := by
  {
    rw [intervalIntegral.integral_of_le (by linarith : -R ≤ R), setIntegral_congr_set Ioc_ae_eq_Icc]
    exact setIntegral_eq_integral_of_forall_compl_eq_zero hzero
  }
  exact ⟨R, hR, hεR, hint.integrable_of_forall_notMem_eq_zero hzero, hline.symm.trans hb.symm⟩
}

lemma ofReal_integral_le_lintegral_abs {α : Type*} [MeasurableSpace α]
    {μ : Measure α} {f : α → ℝ} (hf : Integrable f μ) :
    ENNReal.ofReal (∫ x, f x ∂μ) ≤ ∫⁻ x, ENNReal.ofReal |f x| ∂μ := by
{
  rw [← ofReal_integral_eq_lintegral_ofReal hf.abs (Eventually.of_forall (fun x => abs_nonneg (f x)))]
  exact ENNReal.ofReal_le_ofReal (integral_mono hf hf.abs (fun _ => le_abs_self _))
}

lemma half_trace_lintegral_le {g : ℝ × ℝ → ℝ} {ε : ℝ} (hε : 0 < ε)
    (hc : ∀ p : ℝ × ℝ, 0 < p.2 → ContDiffAt ℝ 2 g p)
    (hn : ∀ p : ℝ × ℝ, 0 ≤ g p)
    {K : Set (ℝ × ℝ)} (hK : IsCompact K)
    (hs : ∀ p : ℝ × ℝ, ε / 2 ≤ p.2 → g p ≠ 0 → p ∈ K) :
    (∫⁻ x : ℝ, ENNReal.ofReal (g (x, ε))) ≤
      ∫⁻ p in {p : ℝ × ℝ | ε ≤ p.2}, ENNReal.ofReal ((p.2 - ε) * |pairLaplacian g p|) := by
{
  obtain ⟨R, _, _, hi, he⟩ := half_trace_rectangle hε hc hK hs
  rw [← ofReal_integral_eq_lintegral_ofReal hi (Eventually.of_forall (fun x => hn (x, ε))), he]
  have hi₂ : IntegrableOn (fun p : ℝ × ℝ => (p.2 - ε) * pairLaplacian g p)
      (Icc (-R, ε) (R, R)) volume := by
  {
    refine ContinuousOn.integrableOn_compact isCompact_Icc (fun p hp => ?_)
    have hcAt : ContinuousAt (fun p : ℝ × ℝ => (p.2 - ε) * pairLaplacian g p) p :=
      (continuous_snd.continuousAt.sub continuousAt_const).mul
        (continuousAt_pairLaplacian (hc p (hε.trans_le hp.1.2)))
    exact hcAt.continuousWithinAt
  }
  refine (ofReal_integral_le_lintegral_abs hi₂).trans ?_
  calc
    (∫⁻ p in Icc (-R, ε) (R, R), ENNReal.ofReal |(p.2 - ε) * pairLaplacian g p|) =
        ∫⁻ p in Icc (-R, ε) (R, R), ENNReal.ofReal ((p.2 - ε) * |pairLaplacian g p|) := by
    {
      refine setLIntegral_congr_fun measurableSet_Icc (fun p hp => ?_)
      simp only [abs_mul, abs_of_nonneg (sub_nonneg.mpr hp.1.2)]
    }
    _ ≤ _ := lintegral_mono_set (fun _ hp => hp.1.2)
}

def secondReal (f : ℂ → ℝ) (z u v : ℂ) : ℝ := fderiv ℝ (fderiv ℝ f) z u v

def complexSecondReal (f : ℂ → ℂ) (z u v : ℂ) : ℂ := fderiv ℝ (fderiv ℝ f) z u v

def complexLaplacian (f : ℂ → ℝ) (z : ℂ) : ℝ :=
  secondReal f z 1 1 + secondReal f z I I

lemma secondReal_comp {ψ : ℂ → ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hψ : ContDiffAt ℝ 2 ψ (F z)) (hF : ContDiffAt ℝ 2 F z) (u v : ℂ) :
    secondReal (ψ ∘ F) z u v =
      fderiv ℝ ψ (F z) (complexSecondReal F z u v) +
      secondReal ψ (F z) (fderiv ℝ F z u) (fderiv ℝ F z v) := by
{
  have hdψ := hψ.differentiableAt (by norm_num)
  have hdF := hF.differentiableAt (by norm_num)
  have hddψ := (hψ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hddF := (hF.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have he : fderiv ℝ (ψ ∘ F) =ᶠ[𝓝 z] fun w =>
      (fderiv ℝ ψ (F w)).comp (fderiv ℝ F w) := by
  {
    filter_upwards [hF.eventually (by simp), hdF.continuousAt.eventually (hψ.eventually (by simp))] with w hFw hψw
    exact fderiv_comp w (hψw.differentiableAt (by norm_num)) (hFw.differentiableAt (by norm_num))
  }
  have hh := ((hddψ.hasFDerivAt.comp z hdF.hasFDerivAt).clm_comp hddF.hasFDerivAt).congr_of_eventuallyEq he
  rw [secondReal, hh.fderiv]
  simp [secondReal, complexSecondReal, ContinuousLinearMap.compL_apply]
}

lemma bilinear_complex_rotation (B : ℂ →L[ℝ] ℂ →L[ℝ] ℝ) (c : ℂ) :
    B c c + B (c * I) (c * I) = ‖c‖^2 * (B 1 1 + B I I) := by
{
  have hc : c = c.re • (1 : ℂ) + c.im • I := by simp
  have hci : c * I = (-c.im) • (1 : ℂ) + c.re • I := by
  {
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im]
  }
  have hn : ‖c‖^2 = c.re ^ 2 + c.im ^ 2 := by
  {
    rw [Complex.sq_norm]
    simp [Complex.normSq_apply, pow_two]
  }
  rw [hci, hc]
  simp only [map_add, map_smul, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, smul_eq_mul]
  rw [← hc, hn]
  ring
}

lemma fderiv_real_complex_apply {F : ℂ → ℂ} {z : ℂ}
    (hF : DifferentiableAt ℂ F z) (v : ℂ) : fderiv ℝ F z v = deriv F z * v := by
{
  rw [(hF.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv]
  simp [smul_eq_mul, mul_comm]
}

lemma complexSecondReal_holomorphic {F : ℂ → ℂ} {z : ℂ}
    (hF : AnalyticAt ℂ F z) (u v : ℂ) :
    complexSecondReal F z u v = deriv (deriv F) z * u * v := by
{
  have hF2 : ContDiffAt ℝ 2 F z := hF.contDiffAt.restrict_scalars ℝ
  have hddF := (hF2.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hclm : fderiv ℝ (fun y => (fderiv ℝ F y) v) z = (fderiv ℝ (fderiv ℝ F) z).flip v := by
  {
    simpa using (hddF.hasFDerivAt.clm_apply (hasFDerivAt_const v z)).fderiv
  }
  have hev : (fun w => fderiv ℝ F w v) =ᶠ[𝓝 z] (fun w => deriv F w * v) := by
  {
    filter_upwards [hF.eventually_analyticAt] with w hw
    exact fderiv_real_complex_apply hw.differentiableAt v
  }
  have hd := ((hF.deriv.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ).mul_const v).fderiv
  change (fderiv ℝ (fderiv ℝ F) z).flip v u = _
  rw [← hclm, hev.fderiv_eq, hd]
  change v * (u * deriv (deriv F) z) = _
  ring
}

lemma complexSecondReal_trace_zero {F : ℂ → ℂ} {z : ℂ} (hF : AnalyticAt ℂ F z) :
    complexSecondReal F z 1 1 + complexSecondReal F z I I = 0 := by
{
  rw [complexSecondReal_holomorphic hF 1 1, complexSecondReal_holomorphic hF I I]
  have hI : (I : ℂ) * I = -1 := Complex.I_mul_I
  linear_combination deriv (deriv F) z * hI
}

lemma laplacian_holomorphic_comp {ψ : ℂ → ℝ} {F : ℂ → ℂ} {z : ℂ}
    (hψ : ContDiffAt ℝ 2 ψ (F z)) (hF : AnalyticAt ℂ F z) :
    complexLaplacian (ψ ∘ F) z = ‖deriv F z‖^2 * complexLaplacian ψ (F z) := by
{
  rw [complexLaplacian, secondReal_comp hψ (hF.contDiffAt.restrict_scalars ℝ),
    secondReal_comp hψ (hF.contDiffAt.restrict_scalars ℝ)]
  have hz := complexSecondReal_trace_zero hF
  have he : fderiv ℝ ψ (F z) (complexSecondReal F z 1 1) +
      fderiv ℝ ψ (F z) (complexSecondReal F z I I) = 0 := by
  {
    rw [← map_add, hz, map_zero]
  }
  simp only [fderiv_real_complex_apply hF.differentiableAt, mul_one]
  have hb := bilinear_complex_rotation (fderiv ℝ (fderiv ℝ ψ) (F z)) (deriv F z)
  rw [complexLaplacian]
  dsimp only [secondReal] at *
  linarith
}

lemma pairLaplacian_complex (f : ℂ → ℝ) (p : ℝ × ℝ) :
    pairLaplacian (f ∘ Complex.equivRealProdCLM.symm) p =
      complexLaplacian f (Complex.equivRealProdCLM.symm p) := by
{
  have he := Complex.equivRealProdCLM.symm.iteratedFDerivWithin_comp_right
    f (s := univ) uniqueDiffOn_univ (mem_univ (Complex.equivRealProdCLM.symm p)) 2
  simp only [preimage_univ, iteratedFDerivWithin_univ] at he
  have h₁ := congrArg (fun B => B ![((1, 0) : ℝ × ℝ), (1, 0)]) he
  have h₂ := congrArg (fun B => B ![((0, 1) : ℝ × ℝ), (0, 1)]) he
  simp only [iteratedFDeriv_two_apply, ContinuousMultilinearMap.compContinuousLinearMap_apply,
    Matrix.cons_val_zero, Matrix.cons_val_one, ContinuousLinearEquiv.coe_coe] at h₁ h₂
  have hc₁ : Complex.equivRealProdCLM.symm (1, 0) = 1 := by simp [Complex.equivRealProdCLM_symm_apply]
  have hc₂ : Complex.equivRealProdCLM.symm (0, 1) = I := by simp [Complex.equivRealProdCLM_symm_apply]
  rw [hc₁] at h₁
  rw [hc₂] at h₂
  rw [pairLaplacian, h₁, h₂, complexLaplacian]
  rfl
}

lemma laplacian_eq_zero_outside_tsupport {ψ : ℂ → ℝ} {z : ℂ}
    (hz : z ∉ tsupport ψ) : complexLaplacian ψ z = 0 := by
{
  have he : ψ =ᶠ[𝓝 z] (fun _ => (0 : ℝ)) := notMem_tsupport_iff_eventuallyEq.mp hz
  have he1 : fderiv ℝ ψ =ᶠ[𝓝 z] (fun _ => (0 : ℂ →L[ℝ] ℝ)) := by
  {
    filter_upwards [he.eventually_nhds] with w hw
    have hw' : ψ =ᶠ[𝓝 w] (fun _ => (0 : ℝ)) := hw
    rw [hw'.fderiv_eq, fderiv_const_apply]
  }
  have he2 : fderiv ℝ (fderiv ℝ ψ) z = 0 := by
  {
    rw [he1.fderiv_eq, fderiv_const_apply]
  }
  simp [complexLaplacian, secondReal, he2]
}

lemma continuous_laplacian {ψ : ℂ → ℝ} (hψ : ContDiff ℝ 2 ψ) :
    Continuous (complexLaplacian ψ) := by
{
  have hh : ContDiff ℝ 0 (fderiv ℝ (fderiv ℝ ψ)) :=
    (hψ.fderiv_right (m := 1) (by norm_num)).fderiv_right (by norm_num)
  have hc := hh.continuous
  unfold complexLaplacian secondReal
  fun_prop
}

lemma compactSupport_laplacian {ψ : ℂ → ℝ} (hψ : HasCompactSupport ψ) :
    HasCompactSupport (complexLaplacian ψ) := by
{
  refine hψ.mono' (fun z hz => ?_)
  by_contra hn
  exact hz (laplacian_eq_zero_outside_tsupport hn)
}

lemma conformal_lintegral_le {F : ℂ → ℂ} {s : Set ℂ} (hs : MeasurableSet s)
    (hF : ∀ z ∈ s, DifferentiableAt ℂ F z) (hi : InjOn F s) (b : ℂ → ℝ≥0∞) :
    (∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖^2) * b (F z)) ≤ ∫⁻ w, b w := by
{
  have he := lintegral_image_eq_lintegral_abs_det_fderiv_mul volume hs
    (fun z hz => (hF z hz).hasFDerivAt.restrictScalars ℝ |>.hasFDerivWithinAt) hi b
  have hh : (∫⁻ z in s, ENNReal.ofReal (‖deriv F z‖^2) * b (F z)) = ∫⁻ w in F '' s, b w := by
  {
    rw [he]
    refine setLIntegral_congr_fun hs (fun z hz => ?_)
    have hd := (hF z hz).hasFDerivAt.restrictScalars ℝ
    have hf : (ContinuousLinearMap.restrictScalars ℝ (fderiv ℂ F z)) = fderiv ℝ F z := hd.fderiv.symm
    have hdet : (fderiv ℝ F z).det = ‖deriv F z‖^2 :=
      Brennan.Koebe.det_fderiv_complex_at (hF z hz)
    rw [hf, hdet, abs_of_nonneg (sq_nonneg _)]
  }
  rw [hh]
  exact lintegral_mono' Measure.restrict_le_self le_rfl
}

lemma conformal_cutoff_trace_le_strip {F : ℂ → ℂ} {ψ : ℂ → ℝ}
    (hF : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ F z)
    (hψ : ContDiff ℝ 2 ψ) (hn : ∀ w, 0 ≤ ψ w)
    (hproper : ∀ η : ℝ, 0 < η → IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' tsupport ψ))
    {ε : ℝ} (hε : 0 < ε) :
    (∫⁻ x : ℝ, ENNReal.ofReal (ψ (F (x + ε * I)))) ≤
      ∫⁻ z in {z : ℂ | ε ≤ z.im}, ENNReal.ofReal ((z.im - ε) * |complexLaplacian (ψ ∘ F) z|) := by
{
  let C := Complex.equivRealProdCLM.symm
  let g : ℝ × ℝ → ℝ := (ψ ∘ F) ∘ C
  have hc (p : ℝ × ℝ) (hp : 0 < p.2) : ContDiffAt ℝ 2 g p :=
    (hψ.contDiffAt.comp _ ((hF (C p) hp).contDiffAt.restrict_scalars ℝ)).comp _ C.contDiff.contDiffAt
  have hK := (hproper (ε / 2) (by linarith)).image Complex.equivRealProdCLM.continuous
  have hs (p : ℝ × ℝ) (hp : ε / 2 ≤ p.2) (hg : g p ≠ 0) :
      p ∈ Complex.equivRealProdCLM '' ({z : ℂ | ε / 2 ≤ z.im} ∩ F ⁻¹' tsupport ψ) :=
    ⟨C p, ⟨hp, subset_closure hg⟩, Complex.equivRealProdCLM.apply_symm_apply p⟩
  have ht := half_trace_lintegral_le hε hc (fun _ => hn _) hK hs
  have he := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding
    (fun p : ℝ × ℝ => ENNReal.ofReal ((p.2 - ε) * |pairLaplacian g p|)) {p : ℝ × ℝ | ε ≤ p.2}
  have hh : (∫⁻ p in {p : ℝ × ℝ | ε ≤ p.2}, ENNReal.ofReal ((p.2 - ε) * |pairLaplacian g p|)) =
      ∫⁻ z in {z : ℂ | ε ≤ z.im}, ENNReal.ofReal ((z.im - ε) * |complexLaplacian (ψ ∘ F) z|) := by
  {
    rw [← he]
    refine lintegral_congr (fun z => ?_)
    dsimp only [g, C]
    rw [pairLaplacian_complex]
    rfl
  }
  rw [hh] at ht
  simpa only [g, C, Function.comp_apply, Complex.equivRealProdCLM_symm_apply] using ht
}

lemma conformal_cutoff_trace_bound {F : ℂ → ℂ} {ψ : ℂ → ℝ}
    (hF : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ F z)
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hψ : ContDiff ℝ 2 ψ) (hn : ∀ w, 0 ≤ ψ w) (_hψK : HasCompactSupport ψ)
    (hproper : ∀ η : ℝ, 0 < η → IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' tsupport ψ))
    {H_max : ℝ} (hH : 0 ≤ H_max)
    (hheight : ∀ z : ℂ, 0 < z.im → F z ∈ tsupport ψ → z.im ≤ H_max) :
    ∀ ε : ℝ, 0 < ε → (∫⁻ x : ℝ, ENNReal.ofReal (ψ (F (x + ε * I)))) ≤
      ENNReal.ofReal H_max * ∫⁻ w : ℂ, ENNReal.ofReal |complexLaplacian ψ w| := by
{
  intro ε hε
  refine (conformal_cutoff_trace_le_strip hF hψ hn hproper hε).trans ?_
  have hmeas : MeasurableSet {z : ℂ | ε ≤ z.im} :=
    isClosed_le continuous_const Complex.continuous_im |>.measurableSet
  calc
    (∫⁻ z in {z : ℂ | ε ≤ z.im}, ENNReal.ofReal ((z.im - ε) * |complexLaplacian (ψ ∘ F) z|)) ≤
        ∫⁻ z in {z : ℂ | ε ≤ z.im}, ENNReal.ofReal H_max *
          (ENNReal.ofReal (‖deriv F z‖^2) * ENNReal.ofReal |complexLaplacian ψ (F z)|) := by
    {
      refine setLIntegral_mono' hmeas (fun z hz => ?_)
      rw [laplacian_holomorphic_comp hψ.contDiffAt (hF z (hε.trans_le hz)),
        abs_mul, abs_of_nonneg (sq_nonneg _), ← ENNReal.ofReal_mul (sq_nonneg _),
        ← ENNReal.ofReal_mul hH]
      apply ENNReal.ofReal_le_ofReal
      by_cases hd : complexLaplacian ψ (F z) = 0
      · simp [hd]
      have hm : F z ∈ tsupport ψ := by
      {
        by_contra hh
        exact hd (laplacian_eq_zero_outside_tsupport hh)
      }
      nlinarith [sq_nonneg ‖deriv F z‖, abs_nonneg (complexLaplacian ψ (F z)),
        hheight z (hε.trans_le hz) hm,
        mul_nonneg (sq_nonneg ‖deriv F z‖) (abs_nonneg (complexLaplacian ψ (F z)))]
    }
    _ = ENNReal.ofReal H_max * ∫⁻ z in {z : ℂ | ε ≤ z.im},
        ENNReal.ofReal (‖deriv F z‖^2) * ENNReal.ofReal |complexLaplacian ψ (F z)| :=
      lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := mul_le_mul' le_rfl (conformal_lintegral_le hmeas
      (fun z hz => (hF z (hε.trans_le hz)).differentiableAt)
      (hi.mono (fun _ hz => hε.trans_le hz))
      (fun w => ENNReal.ofReal |complexLaplacian ψ w|))
}

lemma exists_trace_smooth_cutoff (K : Set ℂ) (hK : IsCompact K) :
    ∃ ψ : ℂ → ℝ, ContDiff ℝ 2 ψ ∧ (∀ w, 0 ≤ ψ w) ∧ HasCompactSupport ψ ∧
      ∀ w ∈ K, ψ w = 1 := by
{
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : ℂ)
  let b : ContDiffBump (0 : ℂ) := ⟨max R 0 + 1, max R 0 + 2, by positivity, by linarith⟩
  refine ⟨b, b.contDiff, b.nonneg', b.hasCompactSupport, fun w hw => ?_⟩
  apply b.one_of_mem_closedBall
  exact Metric.closedBall_subset_closedBall (by dsimp [b]; linarith [le_max_left R 0]) (hR hw)
}

lemma conformal_trace_bound {F : ℂ → ℂ}
    (hF : ∀ z : ℂ, 0 < z.im → AnalyticAt ℂ F z)
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hproper : ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η →
      IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' K))
    (hheight : ∀ K : Set ℂ, IsCompact K → ∃ H_max : ℝ, 0 < H_max ∧
      ∀ z : ℂ, 0 < z.im → F z ∈ K → z.im ≤ H_max)
    {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x + ε * I) ∈ K} ≤ C := by
{
  obtain ⟨ψ, hψ, hn, hψK, hψone⟩ := exists_trace_smooth_cutoff K hK
  obtain ⟨H_max, hH, hHb⟩ := hheight (tsupport ψ) hψK
  let C := ENNReal.ofReal H_max * ∫⁻ w : ℂ, ENNReal.ofReal |complexLaplacian ψ w|
  have hfin : C < ∞ := by
  {
    apply ENNReal.mul_lt_top ENNReal.ofReal_lt_top
    have hi := (continuous_laplacian hψ).integrable_of_hasCompactSupport
      (μ := volume) (compactSupport_laplacian hψK)
    simpa only [HasFiniteIntegral, ← ofReal_norm, Real.norm_eq_abs] using hi.hasFiniteIntegral
  }
  refine ⟨C, hfin, fun ε hε => ?_⟩
  refine le_trans ?_ (conformal_cutoff_trace_bound hF hi hψ hn hψK
    (hproper (tsupport ψ) hψK) hH.le hHb ε hε)
  have hcont : Continuous (fun x : ℝ => F (x + ε * I)) :=
    continuous_iff_continuousAt.mpr (fun x => (hF _ (by simpa using hε)).continuousAt.comp
      (f := fun x : ℝ => (x + ε * I : ℂ)) (by fun_prop))
  have hm : MeasurableSet {x : ℝ | F (x + ε * I) ∈ K} :=
    hK.isClosed.measurableSet.preimage hcont.measurable
  rw [← lintegral_indicator_one hm]
  refine lintegral_mono (fun x => ?_)
  by_cases hx : F (x + ε * I) ∈ K <;> simp [hx, hψone]
}

lemma KClass_trace_bound (F : KClass) {beta : ℝ} (h_beta : beta > 1)
    (hI : I_integrable beta F) {K : Set ℂ} (hK : IsCompact K) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F.F (x + ε * I) ∈ K} ≤ C := by
{
  exact conformal_trace_bound
    (fun z hz => F.univalent.1.analyticAt (isOpen_H.mem_nhds hz))
    F.univalent.2
    (fun _ hK η hη => KClass_proper_preimage F h_beta hI hK hη)
    (fun _ hK => KClass_preimage_height_bound F h_beta hI hK) hK
}

theorem lemma_4_3_trace_bounds (beta : ℝ) (h_beta : beta > 1) (F : KClass) (hI : I_integrable beta F)
    (K : Set ℂ) (hK : IsCompact K) (eps : ℝ) (heps : eps > 0) :
  IsCompact ({z : ℂ | F.F z ∈ K} ∩ {z : ℂ | z.im ≥ eps}) ∧
  ∃ C_F_K : ℝ, ∀ e > 0, ∫ x : ℝ, (if F.F (x + e • I) ∈ K then (1 : ℝ) else 0) ∂volume ≤ C_F_K := by
{
  refine ⟨?_, ?_⟩
  · rw [Set.inter_comm]
    exact KClass_proper_preimage F h_beta hI hK heps
  · obtain ⟨C, hCfin, hC⟩ := KClass_trace_bound F h_beta hI hK
    refine ⟨C.toReal, fun e he => ?_⟩
    by_cases hint : Integrable (fun x : ℝ => if F.F (x + e • I) ∈ K then (1 : ℝ) else 0) volume
    · have hnonneg : 0 ≤ᵐ[volume] (fun x : ℝ => if F.F (x + e • I) ∈ K then (1 : ℝ) else 0) :=
        Eventually.of_forall (fun x => by
          change 0 ≤ if F.F (x + e • I) ∈ K then (1 : ℝ) else 0
          split_ifs <;> positivity)
      apply (ENNReal.ofReal_le_iff_le_toReal hCfin.ne).mp
      rw [ofReal_integral_eq_lintegral_ofReal hint hnonneg]
      let ε : ℝ := e
      have her : 0 < ε := Nat.cast_pos.mpr he
      have hcont : Continuous (fun x : ℝ => F.F (x + (ε : ℂ) * I)) :=
        continuous_iff_continuousAt.mpr (fun x =>
          (F.univalent.1.analyticAt (isOpen_H.mem_nhds (by simpa [H] using her))).continuousAt.comp
            (f := fun x : ℝ => (x + (ε : ℂ) * I)) (by fun_prop))
      have hm : MeasurableSet {x : ℝ | F.F (x + (ε : ℂ) * I) ∈ K} :=
        hK.isClosed.measurableSet.preimage hcont.measurable
      refine le_trans ?_ (hC ε her)
      rw [← lintegral_indicator_one hm]
      refine lintegral_mono (fun x => ?_)
      have hsmul : (e • I : ℂ) = (ε : ℂ) * I := by simp [ε]
      rw [hsmul]
      by_cases hx : F.F (x + (ε : ℂ) * I) ∈ K
      · simp [hx]
      · simp [hx]
    · rw [integral_undef hint]
      exact ENNReal.toReal_nonneg
}

lemma uniform_relative_KClass_bound :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (F : KClass) (w : ℂ), |w.re| ≤ 1 →
      (1 / 2 : ℝ) ≤ w.im → w.im ≤ 1 → ‖F.F w‖ ≤ M := by
{
  let B : Set (ℝ × ℝ) := Icc (-1, 1 / 2) (1, 1)
  let K : Set ℂ := Complex.equivRealProdCLM.symm '' B
  have hK : IsCompact K := isCompact_Icc.image Complex.equivRealProdCLM.symm.continuous
  have hKsub : K ⊆ Set.range (fun w : H => (w : ℂ)) := by
  {
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨⟨Complex.equivRealProdCLM.symm p, by change 0 < p.2; linarith [hp.1.2]⟩, rfl⟩
  }
  have hKs : IsCompact ((fun w : H => (w : ℂ)) ⁻¹' K) :=
    Topology.IsEmbedding.subtypeVal.isInducing.isCompact_preimage' hK hKsub
  have hprod := (isCompact_univ (X := DiskClass)).prod hKs
  obtain ⟨M, hM⟩ := hprod.exists_bound_of_continuousOn continuous_toKClass_eval.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun F w hx hy hyy => ?_⟩
  have hw : w ∈ H := by change 0 < w.im; linarith
  have hmem : (ofKClass F, ⟨w, hw⟩) ∈ (univ : Set DiskClass) ×ˢ ((fun w : H => (w : ℂ)) ⁻¹' K) := by
  {
    refine ⟨mem_univ _, ⟨(w.re, w.im), ⟨⟨(abs_le.mp hx).1, hy⟩, ⟨(abs_le.mp hx).2, hyy⟩⟩, ?_⟩⟩
    exact Complex.equivRealProdCLM.symm_apply_apply w
  }
  rw [← toKClass_ofKClass_eqOn F hw]
  exact (hM _ hmem).trans (le_max_left _ _)
}

lemma H_ball_subset {z : ℂ} (_hz : z ∈ H) : Metric.ball z z.im ⊆ H := by
{
  intro w hw
  have hh : ‖w - z‖ < z.im := by simpa only [Metric.mem_ball, dist_eq_norm] using hw
  have hb := Complex.abs_im_le_norm (w - z)
  change 0 < w.im
  simp only [Complex.sub_im] at hb
  linarith [neg_le_abs (w.im - z.im)]
}

lemma omitted_quarter_bound {F : ℂ → ℂ} (hf : UnivalentOn F H)
    {z ξ : ℂ} (hz : z ∈ H) (hξ : ξ ∉ F '' H) :
    z.im * ‖deriv F z‖ ≤ 4 * ‖F z - ξ‖ := by
{
  have hr : 0 < z.im := hz
  have hb := Brennan.Koebe.local_koebe_quarter F z z.im hr
    (hf.1.mono (H_ball_subset hz)) (hf.2.mono (H_ball_subset hz))
    (deriv_ne_zero_of_univalentOn isOpen_H hf hz)
  have hn : ξ ∉ Metric.ball (F z) (z.im * ‖deriv F z‖ / 4) :=
    fun hh => hξ ((image_mono (H_ball_subset hz)) (hb hh))
  have hn' : z.im * ‖deriv F z‖ / 4 ≤ ‖F z - ξ‖ := by
  {
    simpa only [Metric.mem_ball, dist_eq_norm, not_lt, norm_sub_rev] using hn
  }
  linarith
}

lemma KClass_omitted_cell_bound {M : ℝ} (hM : 0 ≤ M)
    (hb : ∀ (F : KClass) (w : ℂ), |w.re| ≤ 1 → (1 / 2 : ℝ) ≤ w.im → w.im ≤ 1 → ‖F.F w‖ ≤ M)
    (F : KClass) {h x y x' : ℝ} {ξ : ℂ} (hh : 0 < h)
    (hy : h ≤ y) (hyy : y ≤ 2 * h) (hxx : |x' - x| ≤ h)
    (hξ : ξ ∉ F.F '' H) :
    ‖F.F (x' + h * I) - ξ‖ ≤ (1 + 4 * M) * ‖F.F (x + y * I) - ξ‖ := by
{
  let z : ℂ := x + y * I
  let w : ℂ := ((x' - x) / y : ℝ) + (h / y : ℝ) * I
  have hy0 : 0 < y := hh.trans_le hy
  have hz : z ∈ H := by simpa [z, H] using hy0
  have hwy : w.im = h / y := by simp [w]
  have hwx : w.re = (x' - x) / y := by simp [w]
  have hwr : |w.re| ≤ 1 := by rw [hwx, abs_div, abs_of_pos hy0]; exact (div_le_one hy0).mpr (hxx.trans hy)
  have hwl : (1 / 2 : ℝ) ≤ w.im := by rw [hwy, le_div_iff₀ hy0]; linarith
  have hwu : w.im ≤ 1 := by rw [hwy]; exact (div_le_one hy0).mpr hy
  have hwa : aff z w = x' + h * I := by
  {
    apply Complex.ext
    · simp [aff, z, w, Complex.mul_re, Complex.mul_im]
      field_simp
      ring
    · simp [aff, z, w, Complex.mul_re, Complex.mul_im]
      field_simp
  }
  have hd : 0 < ‖deriv F.F z‖ := norm_pos_iff.mpr (deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz)
  have hm := hb ⟨T z F.F, (T_KClass F z hz).1, (T_KClass F z hz).2.1, (T_KClass F z hz).2.2⟩ w hwr hwl hwu
  have hzim : z.im = y := by simp [z]
  simp only [T, hwa, norm_div, norm_mul, Complex.norm_real, hzim, Real.norm_eq_abs, abs_of_pos hy0] at hm
  have hm' := (div_le_iff₀ (mul_pos hy0 hd)).mp hm
  have hq := omitted_quarter_bound F.univalent hz hξ
  rw [hzim] at hq
  have hsum := norm_add_le (F.F (x' + h * I) - F.F z) (F.F z - ξ)
  simp only [sub_add_sub_cancel] at hsum
  have hhq := mul_le_mul_of_nonneg_left hq hM
  dsimp only [z] at *
  nlinarith
}

def closedPositiveSuperlevel (F : ℂ → ℂ) (k δ : ℝ) (ξ : ℂ) : Set ℂ :=
  {z | 0 < z.im ∧ ‖F z - ξ‖ ≤ z.im ^ k / δ}

lemma superlevel_V_target_eq_closedPositiveSuperlevel (beta : ℝ) (F : KClass) (xi : ℂ)
    {delta : ℝ} (hdelta : 0 < delta) :
    {z ∈ H | V_target beta F xi z ≥ ENNReal.ofReal delta} =
      closedPositiveSuperlevel F.F (k_val beta) delta xi := by
{
  ext z
  simp only [Set.mem_setOf_eq, closedPositiveSuperlevel, H]
  constructor
  · rintro ⟨hz, hV⟩
    refine ⟨hz, ?_⟩
    have hzH : z ∈ H := hz
    simp only [V_target, hzH, ite_true, ge_iff_le] at hV
    by_cases h0 : ‖F.F z - xi‖ = 0
    · rw [h0]
      exact div_nonneg (Real.rpow_nonneg hz.le _) hdelta.le
    · have hpos : 0 < ‖F.F z - xi‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      rw [← ENNReal.ofReal_div_of_pos hpos, ENNReal.ofReal_le_ofReal_iff (by positivity)] at hV
      exact (le_div_iff₀ hdelta).mpr (by linarith [(le_div_iff₀ hpos).mp hV])
  · rintro ⟨hz, hle⟩
    refine ⟨hz, ?_⟩
    have hzH : z ∈ H := hz
    simp only [V_target, hzH, ite_true, ge_iff_le]
    by_cases h0 : ‖F.F z - xi‖ = 0
    · rw [h0, ENNReal.ofReal_zero,
        ENNReal.div_zero (ENNReal.ofReal_pos.mpr (Real.rpow_pos_of_pos hz _)).ne']
      exact le_top
    · have hpos : 0 < ‖F.F z - xi‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
      rw [← ENNReal.ofReal_div_of_pos hpos]
      exact ENNReal.ofReal_le_ofReal ((le_div_iff₀ hpos).mpr (by linarith [(le_div_iff₀ hdelta).mp hle]))
}

lemma interior_positive_superlevel_height {F : ℂ → ℂ} {k δ : ℝ}
    (hk : 0 < k) (_hδ : 0 < δ)
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hopen : ∀ z : ℂ, 0 < z.im → map F (𝓝 z) = 𝓝 (F z))
    {ξ : ℂ} (hξ : ξ ∈ F '' {z : ℂ | 0 < z.im}) :
    ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
      ‖F z - ξ‖ ≤ z.im ^ k / δ → η ≤ z.im := by
{
  obtain ⟨z₀, hz₀, rfl⟩ := hξ
  change 0 < z₀.im at hz₀
  have hn : {z : ℂ | z₀.im / 2 < z.im} ∈ 𝓝 z₀ :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds (by change z₀.im / 2 < z₀.im; linarith)
  have hn' := image_mem_map (m := F) hn
  rw [hopen z₀ hz₀] at hn'
  obtain ⟨r, hr, hrB⟩ := Metric.mem_nhds_iff.mp hn'
  have hc : ContinuousAt (fun y : ℝ => y ^ k / δ) 0 :=
    (Real.continuous_rpow_const hk.le).continuousAt.div_const δ
  have he : (0 : ℝ) ^ k / δ = 0 := by rw [Real.zero_rpow (ne_of_gt hk), zero_div]
  have hevent : ∀ᶠ y : ℝ in 𝓝 0, y ^ k / δ < r :=
    hc.eventually (gt_mem_nhds (show (0 : ℝ) ^ k / δ < r by rwa [he]))
  obtain ⟨a, ha, haB⟩ := Metric.mem_nhds_iff.mp hevent
  refine ⟨min a (z₀.im / 2), lt_min ha (by linarith), fun z hz hzw => ?_⟩
  by_contra! hsmall
  have hza : z.im < a := hsmall.trans_le (min_le_left _ _)
  have hm : F z ∈ Metric.ball (F z₀) r := by
  {
    rw [Metric.mem_ball, dist_eq_norm]
    exact hzw.trans_lt (haB (by simpa [abs_of_pos hz] using hza))
  }
  obtain ⟨w, hw, hwe⟩ := hrB hm
  have hwH : 0 < w.im := by change z₀.im / 2 < w.im at hw; linarith
  have hwz : w = z := hi hwH hz hwe
  subst w
  change z₀.im / 2 < z.im at hw
  exact (not_lt_of_ge hw.le) (hsmall.trans_le (min_le_right _ _))
}

lemma positive_superlevel_compact {F : ℂ → ℂ} {k δ : ℝ} {ξ : ℂ}
    (hk : 0 ≤ k) (hδ : 0 < δ)
    (hc : ContinuousOn F {z : ℂ | 0 < z.im})
    (ht : HasQuarticTail F (4 * k))
    (hp : ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η →
      IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' K))
    (hheight : ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
      ‖F z - ξ‖ ≤ z.im ^ k / δ → η ≤ z.im) :
    IsCompact (closedPositiveSuperlevel F k δ ξ) := by
{
  obtain ⟨η, hη, hηb⟩ := hheight
  obtain ⟨R₀, hR₀⟩ := (hp (Metric.closedBall (0 : ℂ) (2 * ‖ξ‖ + 1))
    (isCompact_closedBall _ _) η hη).isBounded.subset_closedBall (0 : ℂ)
  obtain ⟨R₁, hR₁⟩ := quartic_tail_iff_power ht (δ / 2) (by linarith)
  have hb : closedPositiveSuperlevel F k δ ξ ⊆ Metric.closedBall 0 (max R₀ R₁) := by
  {
    intro z hz
    rw [Metric.mem_closedBall, dist_zero_right]
    by_contra! hn
    have hno : 2 * ‖ξ‖ + 1 < ‖F z‖ := by
    {
      by_contra! hle
      have hh' : ‖z‖ ≤ R₀ := by simpa using hR₀ ⟨hηb z hz.1 hz.2, by simpa using hle⟩
      linarith [le_max_left R₀ R₁]
    }
    have hFn : 0 < ‖F z‖ := by nlinarith [norm_nonneg ξ]
    have ht' := hR₁ z hz.1 ((le_max_right _ _).trans hn.le)
    rw [← div_eq_mul_inv, div_lt_iff₀ hFn] at ht'
    have hpot := (le_div_iff₀ hδ).mp hz.2
    have hnorm : ‖F z‖ ≤ ‖F z - ξ‖ + ‖ξ‖ := by
    {
      simpa only [sub_add_cancel] using norm_add_le (F z - ξ) ξ
    }
    nlinarith
  }
  have he : closedPositiveSuperlevel F k δ ξ =
      {z : ℂ | η ≤ z.im} ∩ (fun z => ‖F z - ξ‖ - z.im ^ k / δ) ⁻¹' Iic 0 := by
  {
    ext z
    exact ⟨fun hz => ⟨hηb z hz.1 hz.2, sub_nonpos.mpr hz.2⟩,
      fun hz => ⟨hη.trans_le hz.1, sub_nonpos.mp hz.2⟩⟩
  }
  have hcc : ContinuousOn (fun z : ℂ => ‖F z - ξ‖ - z.im ^ k / δ) {z : ℂ | η ≤ z.im} :=
    (((hc.mono (fun _ hz => hη.trans_le hz)).sub continuousOn_const).norm).sub
      (((Real.continuous_rpow_const hk).comp Complex.continuous_im).continuousOn.div_const δ)
  refine (isCompact_closedBall (0 : ℂ) (max R₀ R₁)).of_isClosed_subset ?_ hb
  rw [he]
  exact hcc.preimage_isClosed_of_isClosed (isClosed_le continuous_const Complex.continuous_im) isClosed_Iic
}

def realCell (h : ℝ) (j : ℤ) : Set ℝ := Ico ((j : ℝ) * h) (((j : ℝ) + 1) * h)

lemma realCell_disjoint {h : ℝ} (hh : 0 < h) : Pairwise (Function.onFun Disjoint (realCell h)) := by
{
  intro i j hij
  apply Set.disjoint_left.mpr
  intro x hx hy
  rcases lt_or_gt_of_ne hij with hij | hji
  · have hhij : (i : ℝ) + 1 ≤ j := by exact_mod_cast Int.add_one_le_iff.mpr hij
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hhij hh.le).trans hy.1)) hx.2
  · have hhji : (j : ℝ) + 1 ≤ i := by exact_mod_cast Int.add_one_le_iff.mpr hji
    exact (not_lt_of_ge ((mul_le_mul_of_nonneg_right hhji hh.le).trans hx.1)) hy.2
}

lemma measure_realCell {h : ℝ} (_hh : 0 ≤ h) (j : ℤ) :
    volume (realCell h j) = ENNReal.ofReal h := by
{
  rw [realCell, Real.volume_Ico]
  congr 1; ring
}

lemma mem_realCell_floor {h : ℝ} (hh : 0 < h) (x : ℝ) : x ∈ realCell h ⌊x / h⌋ := by
{
  exact ⟨(le_div_iff₀ hh).mp (Int.floor_le _), (div_lt_iff₀ hh).mp (Int.lt_floor_add_one _)⟩
}

lemma realCell_length_bound {h : ℝ} (_hh : 0 < h) {j : ℤ} {x x' : ℝ}
    (hx : x ∈ realCell h j) (hx' : x' ∈ realCell h j) : |x' - x| ≤ h := by
{
  rw [abs_le]
  constructor <;> dsimp [realCell] at hx hx' <;> nlinarith [hx.1, hx.2, hx'.1, hx'.2]
}

lemma cell_target_cover_bound {h r : ℝ} (hh : 0 < h) (hr : 0 ≤ r)
    (W : Set ℤ) (centers : ℤ → ℂ) {S : Set ℝ} {C : ℝ≥0∞}
    (hsub : ∀ j ∈ W, realCell h j ⊆ S) (hS : volume S ≤ C) :
    volume (⋃ j : W, Metric.closedBall (centers j) r) ≤
      (ENNReal.ofReal (Real.pi * r ^ 2) / ENNReal.ofReal h) * C := by
{
  have hlen : (∑' j : W, ENNReal.ofReal h) ≤ C := by
  {
    have hd : Pairwise (Function.onFun Disjoint (fun j : W => realCell h j)) :=
      fun i j hij => realCell_disjoint hh (fun he => hij (Subtype.ext he))
    have he := measure_iUnion (μ := volume) hd (fun _ => measurableSet_Ico)
    simp only [measure_realCell hh.le] at he
    rw [← he]
    exact (measure_mono (iUnion_subset (fun (j : W) => hsub j.val j.property))).trans hS
  }
  have harea (j : W) : volume (Metric.closedBall (centers j) r) = ENNReal.ofReal (Real.pi * r ^ 2) := by
  {
    rw [Complex.volume_closedBall]
    have hpi : (NNReal.pi : ℝ≥0∞) = ENNReal.ofReal Real.pi := by
    {
      rw [ENNReal.ofReal, ENNReal.coe_inj]
      exact Subtype.ext (Real.coe_toNNReal Real.pi Real.pi_pos.le).symm
    }
    rw [hpi, ENNReal.ofReal_mul Real.pi_pos.le, ENNReal.ofReal_pow hr, mul_comm]
  }
  calc
    _ ≤ ∑' j : W, volume (Metric.closedBall (centers j) r) := measure_iUnion_le _
    _ = ∑' _ : W, (ENNReal.ofReal (Real.pi * r ^ 2) / ENNReal.ofReal h) * ENNReal.ofReal h := by
    {
      refine tsum_congr (fun j => ?_)
      rw [harea j]
      exact (ENNReal.div_mul_cancel (ne_of_gt (ENNReal.ofReal_pos.mpr hh)) ENNReal.ofReal_ne_top).symm
    }
    _ = (ENNReal.ofReal (Real.pi * r ^ 2) / ENNReal.ofReal h) * (∑' _ : W, ENNReal.ofReal h) :=
      ENNReal.tsum_mul_left
    _ ≤ _ := mul_le_mul' le_rfl hlen
}

lemma summable_geometric_ofReal {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) :
    (∑' n : ℕ, ENNReal.ofReal (r ^ n)) < ∞ := by
{
  have hs : Summable (fun n : ℕ => (⟨r ^ n, pow_nonneg hr0 n⟩ : ℝ≥0)) :=
    NNReal.summable_coe.mp (summable_geometric_of_lt_one hr0 hr1)
  have ht := ENNReal.tsum_coe_ne_top_iff_summable.mpr hs
  apply lt_top_iff_ne_top.mpr
  convert ht using 1
  congr 1; ext n
  exact ENNReal.ofReal_eq_coe_nnreal (pow_nonneg hr0 n)
}

lemma ae_eventually_outside_geometric_covers {E : ℕ → Set ℂ} {C : ℝ≥0∞} (hC : C < ∞)
    {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1)
    (hE : ∀ n, volume (E n) ≤ C * ENNReal.ofReal (r ^ n)) :
    ∀ᵐ ξ : ℂ, ∀ᶠ n : ℕ in atTop, ξ ∉ E n := by
{
  apply ae_eventually_notMem
  refine ne_top_of_le_ne_top ?_ (ENNReal.tsum_le_tsum hE)
  rw [ENNReal.tsum_mul_left]
  exact ne_of_lt (ENNReal.mul_lt_top hC (summable_geometric_ofReal hr0 hr1))
}

def dyadicHeight (n : ℕ) : ℝ := (1 / 2) ^ n

lemma dyadicHeight_pos (n : ℕ) : 0 < dyadicHeight n := by
{
  exact pow_pos (by norm_num) n
}

lemma dyadicHeight_le_one (n : ℕ) : dyadicHeight n ≤ 1 := by
{
  exact pow_le_one₀ (by norm_num) (by norm_num)
}

lemma exists_dyadic_slab {y : ℝ} (hy : 0 < y) (hy1 : y ≤ 1) :
    ∃ n : ℕ, dyadicHeight n ≤ y ∧ y ≤ 2 * dyadicHeight n := by
{
  obtain ⟨n, hn, hn'⟩ := exists_nat_pow_near_of_lt_one hy hy1
    (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  refine ⟨n + 1, hn.le, ?_⟩
  dsimp [dyadicHeight]
  rw [pow_succ]
  nlinarith
}

lemma dyadicHeight_antitone : Antitone dyadicHeight := by
{
  intro m n hmn
  exact pow_le_pow_of_le_one (by norm_num) (by norm_num) hmn
}

lemma small_height_dyadic_slab (N : ℕ) {y : ℝ} (hy : 0 < y) (hyN : y < dyadicHeight N) :
    ∃ n ≥ N, dyadicHeight n ≤ y ∧ y ≤ 2 * dyadicHeight n := by
{
  obtain ⟨n, hn, hn'⟩ := exists_dyadic_slab hy (hyN.le.trans (dyadicHeight_le_one N))
  refine ⟨n, ?_, hn, hn'⟩
  by_contra! h
  exact (not_lt_of_ge ((dyadicHeight_antitone h.le).trans hn)) hyN
}

lemma slab_power_bound {k h y : ℝ} (hk : 1 ≤ k) (hh : 0 < h) (hh1 : h ≤ 1)
    (hy : 0 ≤ y) (hyh : y ≤ 2 * h) : y ^ k ≤ (2 : ℝ) ^ k * h := by
{
  calc
    y ^ k ≤ (2 * h) ^ k := Real.rpow_le_rpow hy hyh (by linarith)
    _ = (2 : ℝ) ^ k * h ^ k := Real.mul_rpow (by norm_num) hh.le
    _ ≤ _ := mul_le_mul_of_nonneg_left (Real.rpow_le_self_of_le_one hh.le hh1 hk) (by positivity)
}

def omittedTargets (F : ℂ → ℂ) (k R δ h : ℝ) : Set ℂ :=
  {ξ | ξ ∉ F '' {z : ℂ | 0 < z.im} ∧ ‖ξ‖ ≤ R ∧
    ∃ x y : ℝ, h ≤ y ∧ y ≤ 2 * h ∧ ‖F (x + y * I) - ξ‖ ≤ y ^ k / δ}

lemma omittedTargets_cell_bound {F : ℂ → ℂ} {k L R δ h : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L) (hδ : 0 < δ) (hh : 0 < h) (hh1 : h ≤ 1)
    (hcell : ∀ h x y x' : ℝ, ∀ ξ : ℂ, 0 < h → h ≤ y → y ≤ 2 * h → |x' - x| ≤ h →
      ξ ∉ F '' {z : ℂ | 0 < z.im} →
      ‖F (x' + h * I) - ξ‖ ≤ L * ‖F (x + y * I) - ξ‖)
    {j : ℤ} {ξ : ℂ} (hξ : ξ ∈ omittedTargets F k R δ h)
    {x y x' : ℝ} (hx : x ∈ realCell h j) (hy : h ≤ y) (hyy : y ≤ 2 * h)
    (hFw : ‖F (x + y * I) - ξ‖ ≤ y ^ k / δ) (hx' : x' ∈ realCell h j) :
    ‖F (x' + h * I) - ξ‖ ≤ (L * (2 : ℝ) ^ k / δ) * h := by
{
  have ht := hcell h x y x' ξ hh hy hyy (realCell_length_bound hh hx hx') hξ.1
  have hp := div_le_div_of_nonneg_right (slab_power_bound hk hh hh1 (hh.le.trans hy) hyy) hδ.le
  have hp' := mul_le_mul_of_nonneg_left (hFw.trans hp) hL
  calc
    _ ≤ L * ((2 : ℝ) ^ k * h / δ) := ht.trans hp'
    _ = _ := by ring
}

lemma omitted_targets_cover {F : ℂ → ℂ} {k L R δ : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hcell : ∀ h x y x' : ℝ, ∀ ξ : ℂ, 0 < h → h ≤ y → y ≤ 2 * h → |x' - x| ≤ h →
      ξ ∉ F '' {z : ℂ | 0 < z.im} →
      ‖F (x' + h * I) - ξ‖ ≤ L * ‖F (x + y * I) - ξ‖)
    (htrace : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x + ε * I) ∈ K} ≤ C) :
    ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ h : ℝ, 0 < h → h ≤ 1 →
      volume (omittedTargets F k R δ h) ≤ C * ENNReal.ofReal h := by
{
  let D := L * (2 : ℝ) ^ k / δ
  have hD : 0 ≤ D := div_nonneg (mul_nonneg hL (by positivity)) hδ.le
  let K := Metric.closedBall (0 : ℂ) (R + D)
  obtain ⟨C, hC, hCt⟩ := htrace K (isCompact_closedBall _ _)
  refine ⟨ENNReal.ofReal (Real.pi * D ^ 2) * C, ENNReal.mul_lt_top ENNReal.ofReal_lt_top hC, fun h hh hh1 => ?_⟩
  let W : Set ℤ := {j | ∃ ξ ∈ omittedTargets F k R δ h,
    ∃ x y : ℝ, x ∈ realCell h j ∧ h ≤ y ∧ y ≤ 2 * h ∧ ‖F (x + y * I) - ξ‖ ≤ y ^ k / δ}
  let center (j : ℤ) := F ((((j : ℝ) + 1 / 2) * h : ℝ) + h * I)
  have hsub (j : ℤ) (hj : j ∈ W) : realCell h j ⊆ {x : ℝ | F (x + h * I) ∈ K} := by
  {
    rcases hj with ⟨ξ, hξ, x, y, hx, hy, hyy, hFw⟩
    intro x' hx'
    have hhB := omittedTargets_cell_bound hk hL hδ hh hh1 hcell hξ hx hy hyy hFw hx'
    have hn := norm_add_le (F (x' + h * I) - ξ) ξ
    simp only [sub_add_cancel] at hn
    change F (x' + h * I) ∈ Metric.closedBall (0 : ℂ) (R + D)
    rw [Metric.mem_closedBall, dist_zero_right]
    dsimp only [D] at hhB ⊢
    nlinarith [hξ.2.1, mul_le_of_le_one_right hD hh1]
  }
  have hcovered : omittedTargets F k R δ h ⊆ ⋃ j : W, Metric.closedBall (center j) (D * h) := by
  {
    intro ξ hξ
    obtain ⟨x, y, hy, hyy, hFw⟩ := hξ.2.2
    let j : ℤ := ⌊x / h⌋
    have hx : x ∈ realCell h j := mem_realCell_floor hh _
    refine mem_iUnion.mpr ⟨⟨j, ⟨ξ, hξ, x, y, hx, hy, hyy, hFw⟩⟩, ?_⟩
    rw [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev]
    exact omittedTargets_cell_bound (x' := ((j : ℝ) + 1 / 2) * h) hk hL hδ hh hh1 hcell
      hξ hx hy hyy hFw (by constructor <;> nlinarith)
  }
  calc
    _ ≤ volume (⋃ j : W, Metric.closedBall (center j) (D * h)) := measure_mono hcovered
    _ ≤ (ENNReal.ofReal (Real.pi * (D * h) ^ 2) / ENNReal.ofReal h) * C :=
      cell_target_cover_bound hh (mul_nonneg hD hh.le) W center hsub (hCt h hh)
    _ = _ := by
    {
      rw [← ENNReal.ofReal_div_of_pos hh]
      have he : Real.pi * (D * h) ^ 2 / h = (Real.pi * D ^ 2) * h := by field_simp
      rw [he, ENNReal.ofReal_mul (by positivity)]
      ring
    }
}

lemma ae_omitted_positive_superlevel_height {F : ℂ → ℂ} {k L R δ : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L) (hδ : 0 < δ)
    (hcell : ∀ h x y x' : ℝ, ∀ ξ : ℂ, 0 < h → h ≤ y → y ≤ 2 * h → |x' - x| ≤ h →
      ξ ∉ F '' {z : ℂ | 0 < z.im} →
      ‖F (x' + h * I) - ξ‖ ≤ L * ‖F (x + y * I) - ξ‖)
    (htrace : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x + ε * I) ∈ K} ≤ C) :
    ∀ᵐ ξ : ℂ, ξ ∉ F '' {z : ℂ | 0 < z.im} → ‖ξ‖ ≤ R →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
        ‖F z - ξ‖ ≤ z.im ^ k / δ → η ≤ z.im := by
{
  obtain ⟨C, hC, hCb⟩ := omitted_targets_cover hk hL hδ hcell htrace (R := R)
  have hae := ae_eventually_outside_geometric_covers hC
    (by norm_num : (0 : ℝ) ≤ 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
    (E := fun n => omittedTargets F k R δ (dyadicHeight n))
    (fun n => hCb _ (dyadicHeight_pos n) (dyadicHeight_le_one n))
  filter_upwards [hae] with ξ hξ ho hR
  obtain ⟨N, hN⟩ := eventually_atTop.mp hξ
  refine ⟨dyadicHeight N, dyadicHeight_pos N, fun z hz hzw => ?_⟩
  by_contra! hh
  obtain ⟨n, hn, hy, hyy⟩ := small_height_dyadic_slab N hz hh
  refine hN n hn ⟨ho, hR, z.re, z.im, hy, hyy, ?_⟩
  simpa only [Complex.re_add_im] using hzw
}

lemma ae_positive_superlevel_height {F : ℂ → ℂ} {k L : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L)
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hopen : ∀ z : ℂ, 0 < z.im → map F (𝓝 z) = 𝓝 (F z))
    (hcell : ∀ h x y x' : ℝ, ∀ ξ : ℂ, 0 < h → h ≤ y → y ≤ 2 * h → |x' - x| ≤ h →
      ξ ∉ F '' {z : ℂ | 0 < z.im} →
      ‖F (x' + h * I) - ξ‖ ≤ L * ‖F (x + y * I) - ξ‖)
    (htrace : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x + ε * I) ∈ K} ≤ C) :
    ∀ᵐ ξ : ℂ, ∀ δ : ℝ, 0 < δ →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
        ‖F z - ξ‖ ≤ z.im ^ k / δ → η ≤ z.im := by
{
  have hae : ∀ᵐ ξ : ℂ, ∀ R n : ℕ,
      ξ ∉ F '' {z : ℂ | 0 < z.im} → ‖ξ‖ ≤ R →
      ∃ η : ℝ, 0 < η ∧ ∀ z : ℂ, 0 < z.im →
        ‖F z - ξ‖ ≤ z.im ^ k / (1 / (n + 1 : ℝ)) → η ≤ z.im :=
    ae_all_iff.mpr (fun _ => ae_all_iff.mpr (fun _ =>
      ae_omitted_positive_superlevel_height hk hL (by positivity) hcell htrace))
  filter_upwards [hae] with ξ hξ δ hδ
  by_cases ho : ξ ∈ F '' {z : ℂ | 0 < z.im}
  · exact interior_positive_superlevel_height (by linarith) hδ hi hopen ho
  obtain ⟨R, hR⟩ := exists_nat_ge ‖ξ‖
  obtain ⟨n, hn⟩ := exists_nat_gt (1 / δ)
  have hn0 : 0 < (n + 1 : ℝ) := by positivity
  have hnδ : 1 / (n + 1 : ℝ) ≤ δ := by
  {
    apply (div_le_iff₀ hn0).mpr
    have hh := (div_lt_iff₀ hδ).mp hn
    nlinarith
  }
  obtain ⟨η, hη, hηb⟩ := hξ R n ho hR
  exact ⟨η, hη, fun z hz hzw =>
    hηb z hz (hzw.trans (div_le_div_of_nonneg_left (Real.rpow_nonneg hz.le _) (by positivity) hnδ))⟩
}

lemma ae_positive_superlevel_compact {F : ℂ → ℂ} {k L : ℝ}
    (hk : 1 ≤ k) (hL : 0 ≤ L)
    (hc : ContinuousOn F {z : ℂ | 0 < z.im})
    (hi : InjOn F {z : ℂ | 0 < z.im})
    (hopen : ∀ z : ℂ, 0 < z.im → map F (𝓝 z) = 𝓝 (F z))
    (ht : HasQuarticTail F (4 * k))
    (hp : ∀ K : Set ℂ, IsCompact K → ∀ η : ℝ, 0 < η →
      IsCompact ({z : ℂ | η ≤ z.im} ∩ F ⁻¹' K))
    (hcell : ∀ h x y x' : ℝ, ∀ ξ : ℂ, 0 < h → h ≤ y → y ≤ 2 * h → |x' - x| ≤ h →
      ξ ∉ F '' {z : ℂ | 0 < z.im} →
      ‖F (x' + h * I) - ξ‖ ≤ L * ‖F (x + y * I) - ξ‖)
    (htrace : ∀ K : Set ℂ, IsCompact K → ∃ C : ℝ≥0∞, C < ∞ ∧ ∀ ε : ℝ, 0 < ε →
      volume {x : ℝ | F (x + ε * I) ∈ K} ≤ C) :
    ∀ᵐ ξ : ℂ, ∀ δ : ℝ, 0 < δ → IsCompact (closedPositiveSuperlevel F k δ ξ) := by
{
  filter_upwards [ae_positive_superlevel_height hk hL hi hopen hcell htrace] with ξ hξ δ hδ
  exact positive_superlevel_compact (by linarith) hδ hc ht hp (hξ δ hδ)
}

lemma KClass_ae_compact_superlevels (F : KClass) {beta : ℝ} (h_beta : beta > 1)
    (hI : I_integrable beta F) :
    ∀ᵐ xi : ℂ, ∀ delta > 0,
      IsCompact {z ∈ H | V_target beta F xi z ≥ ENNReal.ofReal delta} := by
{
  obtain ⟨M, hM, hMb⟩ := uniform_relative_KClass_bound
  have ht : HasQuarticTail F.F (4 * k_val beta) := by
  {
    convert KClass_quartic_tail F h_beta hI using 1
    unfold k_val; ring
  }
  have hk : 1 ≤ k_val beta := by unfold k_val; linarith
  have hae := ae_positive_superlevel_compact hk (by linarith : 0 ≤ 1 + 4 * M)
    F.univalent.1.continuousOn F.univalent.2
    (fun z hz => ((F.univalent.1.analyticAt (isOpen_H.mem_nhds hz)).contDiffAt (n := 1)
      |>.hasStrictDerivAt (by norm_num)).map_nhds_eq
      (deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz))
    ht
    (fun _ hK _ hη => KClass_proper_preimage F h_beta hI hK hη)
    (fun _ _ _ _ _ hh hy hyy hxx hξ => KClass_omitted_cell_bound hM hMb F hh hy hyy hxx hξ)
    (fun _ hK => KClass_trace_bound F h_beta hI hK)
  filter_upwards [hae] with xi hxi delta hdelta
  rw [superlevel_V_target_eq_closedPositiveSuperlevel beta F xi hdelta]
  exact hxi delta hdelta
}

theorem prop_4_1_compact_superlevels (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) :
  ∀ᵐ F ∂P_eigenmeasure, ∀ᵐ xi ∂volume, ∀ delta > 0,
    IsCompact {z ∈ H | V_target beta F xi z ≥ ENNReal.ofReal delta} := by
{
  have h_beta_gt : beta > 1 := by
  {
    rw [h_beta]
    exact (one_lt_div (Real.log_pos (by norm_num))).mpr (Real.log_lt_log (by norm_num) h_rho)
  }
  filter_upwards [(lemma_4_2_weighted_inverse_area h_rho beta h_beta).1] with F hI
  exact KClass_ae_compact_superlevels F h_beta_gt hI
}

lemma compact_sublevels_iff_exhaustion {X : Type*} [TopologicalSpace X] [T2Space X]
    (K : CompactExhaustion X) {f : X → ℝ} (hf : Continuous f) :
    (∀ r : ℝ, IsCompact {x | f x ≤ r}) ↔
      ∀ n : ℕ, ∃ m : ℕ, ∀ x : X, x ∉ K m → (n : ℝ) ≤ f x := by
{
  constructor
  · intro h n
    obtain ⟨m, hm⟩ := K.exists_superset_of_isCompact (h n)
    refine ⟨m, fun x hx => ?_⟩
    by_contra! hh
    exact hx (hm hh.le)
  · intro h r
    obtain ⟨n, hn⟩ := exists_nat_gt r
    obtain ⟨m, hm⟩ := h n
    refine (K.isCompact m).of_isClosed_subset (isClosed_le hf continuous_const) (fun x hx => ?_)
    by_contra hh
    exact (not_lt_of_ge ((hm x hh).trans hx)) hn
}

lemma measurableSet_compact_sublevels {P X : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    [TopologicalSpace X] [T2Space X] [WeaklyLocallyCompactSpace X] [SigmaCompactSpace X]
    {f : P → X → ℝ} (hp : ∀ x, Continuous (fun p => f p x))
    (hx : ∀ p, Continuous (f p)) :
    MeasurableSet {p | ∀ r : ℝ, IsCompact {x | f p x ≤ r}} := by
{
  let K := CompactExhaustion.choice X
  have he : {p | ∀ r : ℝ, IsCompact {x | f p x ≤ r}} =
      ⋂ n : ℕ, ⋃ m : ℕ, ⋂ x : X, ⋂ (_ : x ∉ K m), {p | (n : ℝ) ≤ f p x} := by
  {
    ext p
    simp only [Set.mem_setOf_eq, mem_iInter, mem_iUnion]
    exact compact_sublevels_iff_exhaustion K (hx p)
  }
  rw [he]
  refine MeasurableSet.iInter (fun _ => MeasurableSet.iUnion (fun _ => IsClosed.measurableSet ?_))
  refine isClosed_iInter (fun x => isClosed_iInter (fun _ => ?_))
  exact isClosed_le continuous_const (hp x)
}

lemma compact_sublevels_iff_positive {X : Type*} [TopologicalSpace X] [T2Space X]
    {f : X → ℝ} (hf : Continuous f) :
    (∀ r : ℝ, IsCompact {x | f x ≤ r}) ↔ ∀ r : ℝ, 0 < r → IsCompact {x | f x ≤ r} := by
{
  refine ⟨fun h r _ => h r, fun h r => ?_⟩
  exact (h (max r 1) (lt_of_lt_of_le (by norm_num) (le_max_right _ _))).of_isClosed_subset
    (isClosed_le hf continuous_const) (fun _ hx => (show f _ ≤ r from hx).trans (le_max_left _ _))
}

lemma compact_positive_superlevels_iff {F : ℂ → ℂ} (k : ℝ) (ξ : ℂ)
    (hc : ContinuousOn F H) :
    (∀ δ : ℝ, 0 < δ → IsCompact (closedPositiveSuperlevel F k δ ξ)) ↔
      ∀ r : ℝ, IsCompact {z : H | ‖F z - ξ‖ / z.val.im ^ k ≤ r} := by
{
  have hy (z : H) : 0 < z.val.im ^ k := Real.rpow_pos_of_pos z.property k
  have hcont : Continuous (fun z : H => ‖F z - ξ‖ / z.val.im ^ k) :=
    ((hc.restrict.sub continuous_const).norm).div
      ((Complex.continuous_im.comp continuous_subtype_val).rpow_const
        (fun z => Or.inl (ne_of_gt z.property)))
      (fun z => ne_of_gt (hy z))
  rw [compact_sublevels_iff_positive hcont]
  have he (r : ℝ) (hr : 0 < r) :
      Subtype.val '' {z : H | ‖F z - ξ‖ / z.val.im ^ k ≤ r} =
        closedPositiveSuperlevel F k (1 / r) ξ := by
  {
    ext z
    simp only [mem_image, Set.mem_setOf_eq, closedPositiveSuperlevel]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [div_le_iff₀ (hy w)] at hw
      exact ⟨w.property, by simpa only [one_div, div_inv_eq_mul, mul_comm r] using hw⟩
    · rintro ⟨hz, hzv⟩
      refine ⟨⟨z, hz⟩, ?_, rfl⟩
      rw [div_le_iff₀ (hy ⟨z, hz⟩)]
      simpa only [one_div, div_inv_eq_mul, mul_comm r] using hzv
  }
  constructor
  · intro h r hr
    rw [Topology.IsEmbedding.subtypeVal.isCompact_iff, he r hr]
    exact h (1 / r) (by positivity)
  · intro h δ hδ
    have hh := (h (1 / δ) (by positivity)).image continuous_subtype_val
    rw [he (1 / δ) (by positivity)] at hh
    simpa only [one_div_one_div] using hh
}

lemma measurableSet_compact_positive_superlevels {P : Type*}
    [TopologicalSpace P] [MeasurableSpace P] [BorelSpace P]
    {F : P → ℂ → ℂ} (hF : Continuous (fun p : P × H => F p.1 p.2)) (k : ℝ) :
    MeasurableSet {p : P × ℂ | ∀ δ : ℝ, 0 < δ →
      IsCompact (closedPositiveSuperlevel (F p.1) k δ p.2)} := by
{
  let f : (P × ℂ) → H → ℝ := fun p z => ‖F p.1 z - p.2‖ / z.val.im ^ k
  have hc (p : P × ℂ) : ContinuousOn (F p.1) H :=
    continuousOn_iff_continuous_restrict.mpr (hF.comp (continuous_const.prodMk continuous_id))
  have he : {p : P × ℂ | ∀ δ : ℝ, 0 < δ →
      IsCompact (closedPositiveSuperlevel (F p.1) k δ p.2)} =
      {p | ∀ r : ℝ, IsCompact {z : H | f p z ≤ r}} :=
    Set.ext (fun p => compact_positive_superlevels_iff k p.2 (hc p))
  rw [he]
  apply measurableSet_compact_sublevels
  · intro z
    exact (((hF.comp (continuous_fst.prodMk continuous_const)).sub continuous_snd).norm).div_const _
  · intro p
    exact (((hc p).restrict.sub continuous_const).norm).div
      ((Complex.continuous_im.comp continuous_subtype_val).rpow_const
        (fun z => Or.inl (ne_of_gt z.property)))
      (fun z => ne_of_gt (Real.rpow_pos_of_pos z.property k))
}

theorem lemma_4_4_measurability (beta : ℝ) :
  MeasurableSet {p : KClass × ℂ | ∀ delta > 0, IsCompact {z ∈ H | V_target beta p.1 p.2 z ≥ ENNReal.ofReal delta}} := by
{
  have he : {p : KClass × ℂ | ∀ delta > 0, IsCompact {z ∈ H | V_target beta p.1 p.2 z ≥ ENNReal.ofReal delta}} =
      {p : KClass × ℂ | ∀ δ : ℝ, 0 < δ →
        IsCompact (closedPositiveSuperlevel p.1.F (k_val beta) δ p.2)} := by
  {
    ext p
    exact forall₂_congr (fun delta hdelta => by
      rw [superlevel_V_target_eq_closedPositiveSuperlevel beta p.1 p.2 hdelta])
  }
  rw [he]
  exact measurableSet_compact_positive_superlevels continuous_KClass_eval (k_val beta)
}

/-!
# 5 Critical points and an equivariant pairing

PAPER: For targets with the compact superlevels obtained in the preceding section, we can compare
PAPER: the critical points of V^F_ξ. We will assign every saddle to a distinct maximum whose value is
PAPER: at least as large. The assignment must depend measurably on F and respect affine changes
PAPER: of the source, because the next section will average this comparison using the weighted law.
-/

/-!
PAPER: 5.1 The critical map and good targets
PAPER: Throughout this section, P is the law of Lemma 3.1, β > 1, and k = (β + 3)/4 > 1. Recall
PAPER: that QF = 1/F' and qF(x + iy) = iyQ'F(x + iy)/QF(x + iy) = aF + ibF. Define the smooth
PAPER: real map GF : H → C by
PAPER: GF(z) = F(z) − (iy/k) F'(z), z = x + iy. (5.1)
PAPER: The normalization gives GF(i) = −i/k for every F ∈ K. We define its normalized signed
PAPER: Jacobian by
PAPER: JF(z) = det DGF(z) / |F'(z)|^2. (5.2)
-/
-- The critical map G_F whose roots define the saddles and maxima
def G (beta : ℝ) (F : KClass) (z : ℂ) : ℂ :=
  F.F z - I / (k_val beta : ℂ) * (z.im : ℂ) * deriv F.F z

-- The normalized signed Jacobian: 2x2 real determinant of dG_F divided by |F'(z)|^2
def J (beta : ℝ) (F : KClass) (z : ℂ) : ℝ :=
  (((fderiv ℝ (G beta F) z 1).re * (fderiv ℝ (G beta F) z I).im -
    (fderiv ℝ (G beta F) z I).re * (fderiv ℝ (G beta F) z 1).im) / ‖deriv F.F z‖^2)

lemma fderiv_G_apply (beta : ℝ) (F : KClass) {z : ℂ} (hz : z ∈ H) (v : ℂ) :
    fderiv ℝ (G beta F) z v = deriv F.F z * v -
      I / (k_val beta : ℂ) * ((v.im : ℂ) * deriv F.F z +
        (z.im : ℂ) * (deriv (deriv F.F) z * v)) := by
{
  have han : AnalyticAt ℂ F.F z := F.univalent.1.analyticOnNhd isOpen_H z hz
  have ha := han.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hb := han.deriv.differentiableAt.hasDerivAt.hasFDerivAt.restrictScalars ℝ
  have hc := Complex.ofRealCLM.hasFDerivAt.comp z Complex.imCLM.hasFDerivAt
  have hG := ha.sub ((hc.const_mul (I / (k_val beta : ℂ))).mul hb)
  have hG' : HasFDerivAt (G beta F)
      (ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ (deriv F.F z)) -
        ((I / (k_val beta : ℂ) * (z.im : ℂ)) •
          ContinuousLinearMap.restrictScalars ℝ (ContinuousLinearMap.toSpanSingleton ℂ (deriv (deriv F.F) z)) +
        deriv F.F z • (I / (k_val beta : ℂ)) •
          (Complex.ofRealCLM.comp Complex.imCLM))) z := hG
  rw [hG'.fderiv]
  change v * deriv F.F z -
    ((I / (k_val beta : ℂ) * (z.im : ℂ)) * (v * deriv (deriv F.F) z) +
      deriv F.F z * (I / (k_val beta : ℂ) * (v.im : ℂ))) = _
  ring
}

lemma G_columns (beta : ℝ) (hk : k_val beta ≠ 0) (F : KClass) {z : ℂ} (hz : z ∈ H) :
    fderiv ℝ (G beta F) z 1 = deriv F.F z / (k_val beta : ℂ) * ((k_val beta : ℂ) + q F z) ∧
    fderiv ℝ (G beta F) z I =
      I * (deriv F.F z / (k_val beta : ℂ)) * ((k_val beta : ℂ) - 1 + q F z) := by
{
  have han : AnalyticAt ℂ F.F z := F.univalent.1.analyticOnNhd isOpen_H z hz
  have hd : deriv F.F z ≠ 0 := deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz
  have hq : q F z = -I * (z.im : ℂ) * (deriv (deriv F.F) z) / (deriv F.F z) :=
    q_eq_F_deriv2 F z hd han.deriv.differentiableAt
  have hk' : (k_val beta : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  constructor <;> rw [fderiv_G_apply beta F hz, hq] <;>
    simp only [Complex.one_im, Complex.I_im, Complex.ofReal_zero, Complex.ofReal_one,
      zero_mul, one_mul, mul_one, zero_add] <;> field_simp <;> ring
}

lemma critical_columns_det (u q_val : ℂ) (k : ℝ) :
    (u * ((k : ℂ) + q_val)).re * (I * u * ((k : ℂ) - 1 + q_val)).im -
      (I * u * ((k : ℂ) - 1 + q_val)).re * (u * ((k : ℂ) + q_val)).im =
    ‖u‖^2 * (k * (k - 1) + (2 * k - 1) * q_val.re + ‖q_val‖^2) := by
{
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im, Complex.one_re, Complex.one_im,
    Complex.sq_norm, Complex.normSq_apply]
  ring
}

/-!
PAPER: Lemma 5.1 (Jacobian and its expectation). For every F ∈ K and z ∈ H,
PAPER: k^2 JF(z) = k(k − 1) + (2k − 1)aF(z) + |qF(z)|^2. (5.3)
PAPER: The function F ↦ JF(i) is bounded and continuous on K, and
PAPER: k^2 EJF(i) = k(k − 1) > 0. (5.4)
-/
-- The exact algebraic identity relating the Jacobian to the logarithmic derivative
lemma J_identity (beta : ℝ) (hk : k_val beta ≠ 0) (F : KClass) {z : ℂ} (hz : z ∈ H) :
    (k_val beta)^2 * J beta F z =
      (k_val beta) * ((k_val beta) - 1) + (2 * (k_val beta) - 1) * a F z + ‖q F z‖^2 := by
{
  have hd : ‖deriv F.F z‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz)
  obtain ⟨hc₁, hc₂⟩ := G_columns beta hk F hz
  unfold J a
  rw [hc₁, hc₂, critical_columns_det, norm_div, Complex.norm_real,
    Real.norm_eq_abs, div_pow, sq_abs]
  field_simp
}

-- Crucially, the expectation of the Jacobian is STRICTLY POSITIVE at the root i
-- We prove this algebraically by integrating the Jacobian identity and substituting the moments
lemma E_J_positive (beta : ℝ) (h_beta : beta > 1) (P : Measure KClass)
    (h_J_integral : ∫ F, (k_val beta)^2 * J beta F I ∂P =
      (k_val beta) * ((k_val beta) - 1) +
      (2 * (k_val beta) - 1) * (∫ F, a F I ∂P) + (∫ F, ‖q F I‖^2 ∂P))
    (h_E_a : ∫ F, a F I ∂P = -beta / 2)
    (h_E_q_sq : ∫ F, ‖q F I‖^2 ∂P = beta * (beta + 1) / 4) :
    ∫ F, (k_val beta)^2 * J beta F I ∂P > 0 := by
{
  have hk : k_val beta = (beta + 3) / 4 := rfl
  rw [h_J_integral, h_E_a, h_E_q_sq, hk]
  have h1 : (beta + 3) / 4 > 0 := by linarith
  have h2 : (beta + 3) / 4 - 1 > 0 := by linarith
  have h_eq : (beta + 3) / 4 * ((beta + 3) / 4 - 1) +
      (2 * ((beta + 3) / 4) - 1) * (-beta / 2) + beta * (beta + 1) / 4 =
      (beta + 3) / 4 * ((beta + 3) / 4 - 1) := by ring
  rw [h_eq]
  positivity
}

/-!
PAPER: Lemma 5.2 (Critical points and their signs). Fix F ∈ K and ξ ∈ C. Away from the
PAPER: unique possible pole of V^F_ξ, put ℓ = log V^F_ξ. Then
PAPER: ∆ℓ = −k/y^2, (5.5)
PAPER: and its critical points are exactly the solutions of GF(z) = ξ. At such a point,
PAPER: V^F_ξ(z) = ky^{k−1}|QF(z)|, (5.6)
PAPER: Hess ℓ(z) = (k/y^2) * [−(k + aF(z)) bF(z) ; bF(z) k − 1 + aF(z)], (5.7)
PAPER: det Hess ℓ(z) = −(k^4/y^4) JF(z). (5.8)
PAPER: Consequently a solution with JF(z) > 0 is a nondegenerate saddle, and one with JF(z) < 0
PAPER: is a nondegenerate maximum.
-/
def is_saddle (beta : ℝ) (F : KClass) (xi : ℂ) (z : ℂ) : Prop := G beta F z = xi ∧ J beta F z > 0
def is_max (beta : ℝ) (F : KClass) (xi : ℂ) (z : ℂ) : Prop := G beta F z = xi ∧ J beta F z < 0

/-!
PAPER: Definition 5.3. A pair (F, ξ) ∈ K × C is good if every closed positive superlevel of V^F_ξ is
PAPER: compact in H, and ξ is a regular value of GF. Thus every solution GF(z) = ξ must satisfy
PAPER: JF(z) ̸= 0; a target with no such solution is regular. Write G for the set of good pairs.

PAPER: Lemma 5.4 (Good pairs and affine changes of source). The set G is Borel. For P-almost
PAPER: every F, its section {ξ : (F, ξ) ∈ G} has full planar area measure.
(Verified in `brennanOAI/lean/OAI/Analysis/IntegralMeans/GoodPairs.lean`)
-/
def is_good_pair (beta : ℝ) (F : KClass) (xi : ℂ) : Prop :=
  (∀ delta > 0, IsCompact {z ∈ H | V_target beta F xi z ≥ ENNReal.ofReal delta}) ∧
  (∀ z ∈ H, G beta F z = xi → J beta F z ≠ 0)

instance diskClassSecondCountable : SecondCountableTopology DiskClass :=
  inferInstanceAs (SecondCountableTopology diskSchlichtSet)

lemma measurableSet_regular_parameters {P X Y : Type*}
    [TopologicalSpace P] [SigmaCompactSpace P]
    [TopologicalSpace X] [SigmaCompactSpace X]
    [TopologicalSpace Y] [T2Space Y] [T2Space P]
    [MeasurableSpace P] [BorelSpace P] [MeasurableSpace Y] [BorelSpace Y]
    [SecondCountableTopology P] [SecondCountableTopology Y]
    {F : P → X → Y} {J : P → X → ℝ}
    (hF : Continuous (fun q : P × X => F q.1 q.2))
    (hJ : Continuous (fun q : P × X => J q.1 q.2)) :
    MeasurableSet {q : P × Y | ∀ x, F q.1 x = q.2 → J q.1 x ≠ 0} := by
{
  let Z : Set (P × X) := {q | J q.1 q.2 = 0}
  let M : P × X → P × Y := fun q => (q.1, F q.1 q.2)
  have hZ : IsSigmaCompact Z := isSigmaCompact_univ.of_isClosed_subset
    (isClosed_eq hJ continuous_const) (subset_univ _)
  have hM : Continuous M := continuous_fst.prodMk hF
  have him : MeasurableSet (M '' Z) := by
  {
    obtain ⟨K, hK, he⟩ := hZ.image hM
    rw [← he]
    exact MeasurableSet.iUnion (fun n => (hK n).isClosed.measurableSet)
  }
  have he : {q : P × Y | ∀ x, F q.1 x = q.2 → J q.1 x ≠ 0} = (M '' Z)ᶜ := by
  {
    ext q
    constructor
    · intro h ⟨⟨p, x⟩, hx, hq⟩
      exact h x (congrArg Prod.fst hq ▸ congrArg Prod.snd hq) (congrArg Prod.fst hq ▸ hx)
    · intro h x hx hJx
      exact h ⟨(q.1, x), hJx, Prod.ext rfl hx⟩
  }
  rw [he]
  exact him.compl
}

lemma continuous_diskClass_deriv :
    Continuous (fun p : DiskClass × H => deriv (toKClass p.1).F p.2) := by
{
  simpa only [iteratedDeriv_one] using continuous_halfClassJet_eval 1
}

lemma continuous_diskClass_deriv2 :
    Continuous (fun p : DiskClass × H => deriv (deriv (toKClass p.1).F) p.2) := by
{
  simpa only [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero]
    using continuous_halfClassJet_eval 2
}

lemma continuous_diskClass_G (beta : ℝ) :
    Continuous (fun p : DiskClass × H => G beta (toKClass p.1) p.2) := by
{
  exact continuous_toKClass_eval.sub ((continuous_const.mul
    (Complex.continuous_ofReal.comp (Complex.continuous_im.comp
      (continuous_subtype_val.comp continuous_snd)))).mul continuous_diskClass_deriv)
}

lemma continuous_diskClass_fderiv_G (beta : ℝ) (v : ℂ) :
    Continuous (fun p : DiskClass × H => fderiv ℝ (G beta (toKClass p.1)) p.2 v) := by
{
  have he (p : DiskClass × H) := fderiv_G_apply beta (toKClass p.1) p.2.2 v
  simp_rw [he]
  have hy : Continuous (fun p : DiskClass × H => (p.2.val.im : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd))
  exact (continuous_diskClass_deriv.mul continuous_const).sub
    (continuous_const.mul ((continuous_const.mul continuous_diskClass_deriv).add
      (hy.mul (continuous_diskClass_deriv2.mul continuous_const))))
}

lemma continuous_diskClass_J (beta : ℝ) :
    Continuous (fun p : DiskClass × H => J beta (toKClass p.1) p.2) := by
{
  unfold J
  refine ((((Complex.continuous_re.comp (continuous_diskClass_fderiv_G beta 1)).mul
    (Complex.continuous_im.comp (continuous_diskClass_fderiv_G beta I))).sub
    ((Complex.continuous_re.comp (continuous_diskClass_fderiv_G beta I)).mul
      (Complex.continuous_im.comp (continuous_diskClass_fderiv_G beta 1)))).div
    (continuous_diskClass_deriv.norm.pow 2)) (fun p => ?_)
  exact pow_ne_zero _ (norm_ne_zero_iff.mpr
    (deriv_ne_zero_of_univalentOn isOpen_H (toKClass p.1).univalent p.2.2))
}

lemma G_J_congr_ofKClass (beta : ℝ) (F : KClass) {z : ℂ} (hz : z ∈ H) :
    G beta F z = G beta (toKClass (ofKClass F)) z ∧
    J beta F z = J beta (toKClass (ofKClass F)) z := by
{
  have heq := toKClass_ofKClass_eqOn F
  have h0 : (toKClass (ofKClass F)).F z = F.F z := heq hz
  have h1 : deriv (toKClass (ofKClass F)).F z = deriv F.F z := by
  {
    simpa only [iteratedDeriv_one] using eqOn_iteratedDeriv_of_eqOn heq 1 hz
  }
  have h2 : deriv (deriv (toKClass (ofKClass F)).F) z = deriv (deriv F.F) z := by
  {
    simpa only [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero]
      using eqOn_iteratedDeriv_of_eqOn heq 2 hz
  }
  have hG : G beta F z = G beta (toKClass (ofKClass F)) z := by simp only [G, h0, h1]
  have hf (v : ℂ) : fderiv ℝ (G beta F) z v = fderiv ℝ (G beta (toKClass (ofKClass F))) z v := by
  {
    rw [fderiv_G_apply beta F hz, fderiv_G_apply beta (toKClass (ofKClass F)) hz, h1, h2]
  }
  refine ⟨hG, ?_⟩
  simp only [J, hf 1, hf I, h1]
}

lemma measurableSet_regular_KClass (beta : ℝ) :
    MeasurableSet {p : KClass × ℂ | ∀ z ∈ H, G beta p.1 z = p.2 → J beta p.1 z ≠ 0} := by
{
  have hreg := measurableSet_regular_parameters
    (F := fun (g : DiskClass) (z : H) => G beta (toKClass g) z)
    (J := fun (g : DiskClass) (z : H) => J beta (toKClass g) z)
    (continuous_diskClass_G beta) (continuous_diskClass_J beta)
  have he : {p : KClass × ℂ | ∀ z ∈ H, G beta p.1 z = p.2 → J beta p.1 z ≠ 0} =
      (Prod.map ofKClass id) ⁻¹'
        {q : DiskClass × ℂ | ∀ z : H, G beta (toKClass q.1) z = q.2 → J beta (toKClass q.1) z ≠ 0} := by
  {
    ext ⟨F, xi⟩
    simp only [Set.mem_setOf_eq, Set.mem_preimage, Prod.map_apply, id_eq]
    constructor
    · intro h z
      rw [← (G_J_congr_ofKClass beta F z.2).1, ← (G_J_congr_ofKClass beta F z.2).2]
      exact h z.1 z.2
    · intro h z hz
      rw [(G_J_congr_ofKClass beta F hz).1, (G_J_congr_ofKClass beta F hz).2]
      exact h ⟨z, hz⟩
  }
  rw [he]
  exact hreg.preimage (continuous_ofKClass.prodMap continuous_id).measurable
}

lemma differentiableAt_G (beta : ℝ) (F : KClass) {z : ℂ} (hz : z ∈ H) :
    DifferentiableAt ℝ (G beta F) z := by
{
  have han : AnalyticAt ℂ F.F z := F.univalent.1.analyticOnNhd isOpen_H z hz
  exact (han.differentiableAt.restrictScalars ℝ).sub
    (((Complex.ofRealCLM.differentiableAt.comp z Complex.imCLM.differentiableAt).const_mul
      (I / (k_val beta : ℂ))).mul (han.deriv.differentiableAt.restrictScalars ℝ))
}

lemma ae_regular_values {f : ℂ → ℂ} {s : Set ℂ}
    (hf : ∀ z ∈ s, DifferentiableAt ℝ f z) :
    ∀ᵐ ξ ∂volume, ∀ z ∈ s, f z = ξ → LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0 := by
{
  let t : Set ℂ := {z | z ∈ s ∧ LinearMap.det (fderiv ℝ f z).toLinearMap = 0}
  have hz : volume (f '' t) = 0 :=
    addHaar_image_eq_zero_of_det_fderivWithin_eq_zero volume
      (fun z hz => (hf z hz.1).hasFDerivAt.hasFDerivWithinAt) (fun _ hz => hz.2)
  have hae : ∀ᵐ ξ ∂volume, ξ ∉ f '' t := by
  {
    rw [ae_iff]
    simpa only [not_not, Set.setOf_mem_eq] using hz
  }
  filter_upwards [hae] with ξ hξ z hzs hfz hdet
  exact hξ ⟨z, ⟨hzs, hdet⟩, hfz⟩
}

lemma ae_regular_G (beta : ℝ) (F : KClass) :
    ∀ᵐ xi ∂volume, ∀ z ∈ H, G beta F z = xi → J beta F z ≠ 0 := by
{
  filter_upwards [ae_regular_values (s := H) (fun z hz => differentiableAt_G beta F hz)] with xi hxi z hz hG
  have hdet : ((fderiv ℝ (G beta F) z 1).re * (fderiv ℝ (G beta F) z I).im -
      (fderiv ℝ (G beta F) z I).re * (fderiv ℝ (G beta F) z 1).im) =
      LinearMap.det (fderiv ℝ (G beta F) z).toLinearMap :=
    (determinant_complex_real (fderiv ℝ (G beta F) z).toLinearMap).symm
  rw [J, hdet]
  exact div_ne_zero (hxi z hz hG)
    (pow_ne_zero _ (norm_ne_zero_iff.mpr (deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz)))
}

theorem lemma_5_4_good_pairs (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) :
  MeasurableSet {p : KClass × ℂ | is_good_pair beta p.1 p.2} ∧
  ∀ᵐ F ∂P_eigenmeasure, volume {xi : ℂ | ¬ is_good_pair beta F xi} = 0 := by
{
  refine ⟨?_, ?_⟩
  · have he : {p : KClass × ℂ | is_good_pair beta p.1 p.2} =
        {p : KClass × ℂ | ∀ delta > 0, IsCompact {z ∈ H | V_target beta p.1 p.2 z ≥ ENNReal.ofReal delta}} ∩
        {p : KClass × ℂ | ∀ z ∈ H, G beta p.1 z = p.2 → J beta p.1 z ≠ 0} := rfl
    rw [he]
    exact (lemma_4_4_measurability beta).inter (measurableSet_regular_KClass beta)
  · filter_upwards [prop_4_1_compact_superlevels h_rho beta h_beta] with F hcomp
    rw [← ae_iff]
    filter_upwards [hcomp, ae_regular_G beta F] with xi h1 h2
    exact ⟨h1, h2⟩
}

/-!
PAPER: 5.2 The superlevel count
PAPER: Lemma 5.5 (Counting critical points above a level). Fix a good pair (F, ξ). There are
PAPER: only finitely many critical points of V^F_ξ with value at least h, for every h > 0. For every
PAPER: such h,
PAPER: #{maxima with V^F_ξ ≥ h} ≥ #{saddles with V^F_ξ ≥ h}. (5.12)
PAPER: The possible pole is excluded from the maximum count.
(Verified in `brennanOAI/lean/OAI/Analysis/IntegralMeans/CriticalCount.lean`)
-/
axiom lemma_5_5_count (beta : ℝ) (h_beta : beta > 1) (F : KClass) (xi : ℂ)
    (h_good : is_good_pair beta F xi) (h : ℝ) (hh : h > 0) :
  {z ∈ H | V_target beta F xi z ≥ ENNReal.ofReal h ∧ G beta F z = xi}.Finite ∧
  Nat.card {z ∈ H | is_max beta F xi z ∧ V_target beta F xi z ≥ ENNReal.ofReal h} ≥
  Nat.card {z ∈ H | is_saddle beta F xi z ∧ V_target beta F xi z ≥ ENNReal.ofReal h}

/-!
PAPER: 5.3 Equal-rank pairing
PAPER: Proposition 5.6 (Measurable equivariant pairing). Let
PAPER: D = {(F, z) ∈ K × H : JF(z) > 0, (F, GF(z)) ∈ G}.
PAPER: There is a Borel map R : D → H, written RF(z) = R(F, z), such that, for every (F, z) ∈ D,
PAPER: with z' = RF(z) and ξ = GF(z),
PAPER: GF(z') = ξ, JF(z') < 0, V^F_ξ(z') ≥ V^F_ξ(z). (5.15)
PAPER: For each fixed F, the map RF is injective on its domain. It is affine equivariant: if t ∈ H
PAPER: and (F, t · w) ∈ D, then
PAPER: (TtF, w) ∈ D, RTtF(w) = t# · RF(t · w). (5.16)
(Verified in `brennanOAI/lean/OAI/Analysis/IntegralMeans/BorelPairing.lean` and `RankPairing.lean`)
-/
axiom R_pair (beta : ℝ) (F : KClass) (z : ℂ) : ℂ

axiom prop_5_6_equivariant_pairing (beta : ℝ) (h_beta : beta > 1) (F : KClass) (z : ℂ)
    (hz : z ∈ H) (hz_saddle : J beta F z > 0) (h_good : is_good_pair beta F (G beta F z)) :
  R_pair beta F z ∈ H ∧
  is_max beta F (G beta F z) (R_pair beta F z) ∧
  V_target beta F (G beta F z) (R_pair beta F z) ≥ V_target beta F (G beta F z) z

end Brennan.Sections4and5
