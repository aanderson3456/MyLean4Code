import Mathlib
import brennan.Section4_5

open Complex Set MeasureTheory Topology Filter Classical Function
open scoped ComplexConjugate Topology ENNReal NNReal

noncomputable section

namespace Brennan.Sections6and7

open Brennan.Section2
open Brennan.Section2_Dyadic
open Brennan.Section3
open Brennan.Sections4and5

/-!
# Section 6 Transport Helpers: Affine Equivariance, Borel Pairing, and Area Transport
-/

lemma G_J_congr_eqOn (beta : ℝ) {F₁ F₂ : KClass} (heq : EqOn F₁.F F₂.F H)
    {z : ℂ} (hz : z ∈ H) :
    G beta F₁ z = G beta F₂ z ∧ J beta F₁ z = J beta F₂ z := by
{
  have h0 : F₁.F z = F₂.F z := heq hz
  have h1 : deriv F₁.F z = deriv F₂.F z := by
  {
    simpa only [iteratedDeriv_one] using eqOn_iteratedDeriv_of_eqOn heq 1 hz
  }
  have h2 : deriv (deriv F₁.F) z = deriv (deriv F₂.F) z := by
  {
    simpa only [show 2 = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one, iteratedDeriv_zero]
      using eqOn_iteratedDeriv_of_eqOn heq 2 hz
  }
  have hG : G beta F₁ z = G beta F₂ z := by simp only [G, h0, h1]
  have hf (v : ℂ) : fderiv ℝ (G beta F₁) z v = fderiv ℝ (G beta F₂) z v := by
  {
    rw [fderiv_G_apply beta F₁ hz, fderiv_G_apply beta F₂ hz, h1, h2]
  }
  refine ⟨hG, ?_⟩
  simp only [J, hf 1, hf I, h1]
}

lemma criticalHeight_congr_eqOn (beta : ℝ) {F₁ F₂ : KClass} (heq : EqOn F₁.F F₂.F H) :
    EqOn (criticalHeight beta F₁) (criticalHeight beta F₂) H := by
{
  intro z hz
  simp only [criticalHeight, Q, heq.deriv isOpen_H hz]
}

lemma is_good_pair_congr_eqOn (beta : ℝ) {F₁ F₂ : KClass} (heq : EqOn F₁.F F₂.F H) (xi : ℂ) :
    is_good_pair beta F₁ xi ↔ is_good_pair beta F₂ xi := by
{
  have hs (delta : ℝ) : {z ∈ H | V_target beta F₁ xi z ≥ ENNReal.ofReal delta} =
      {z ∈ H | V_target beta F₂ xi z ≥ ENNReal.ofReal delta} := by
  {
    ext z
    by_cases hz : z ∈ H
    · simp only [mem_setOf_eq, hz, true_and, V_target, heq hz]
    · simp only [mem_setOf_eq, hz, false_and]
  }
  simp only [is_good_pair, hs]
  apply and_congr_right
  intro _
  constructor <;> intro h z hz hG
  · rw [← (G_J_congr_eqOn beta heq hz).2]
    exact h z hz ((G_J_congr_eqOn beta heq hz).1.trans hG)
  · rw [(G_J_congr_eqOn beta heq hz).2]
    exact h z hz ((G_J_congr_eqOn beta heq hz).1.symm.trans hG)
}

def signedFiber (beta : ℝ) (F : KClass) (xi : ℂ) (σ : ℝ) : Set ℂ :=
  {z ∈ H | G beta F z = xi ∧ 0 < σ * J beta F z}

lemma signedFiber_one (beta : ℝ) (F : KClass) (xi : ℂ) :
    signedFiber beta F xi 1 = positiveFiber beta F xi := by
{
  ext z
  simp [signedFiber, positiveFiber, is_saddle]
}

lemma signedFiber_neg_one (beta : ℝ) (F : KClass) (xi : ℂ) :
    signedFiber beta F xi (-1) = negativeFiber beta F xi := by
{
  ext z
  simp [signedFiber, negativeFiber, is_max]
}

lemma signedFiber_congr_eqOn (beta : ℝ) {F₁ F₂ : KClass} (heq : EqOn F₁.F F₂.F H)
    (xi : ℂ) (σ : ℝ) :
    signedFiber beta F₁ xi σ = signedFiber beta F₂ xi σ := by
{
  ext z
  simp only [signedFiber, mem_setOf_eq]
  apply and_congr_right
  intro hz
  rw [(G_J_congr_eqOn beta heq hz).1, (G_J_congr_eqOn beta heq hz).2]
}

lemma heightRank_congr_on {h₁ h₂ : ℂ → ℝ} {S : Set ℂ} (hS : S ⊆ H)
    (heq : EqOn h₁ h₂ H) {z : ℂ} (hz : z ∈ H) :
    heightRank h₁ S z = heightRank h₂ S z := by
{
  rw [heightRank_eq_ncard, heightRank_eq_ncard]
  congr 1
  ext w
  apply and_congr_right
  intro hw
  simp only [heightPrecedes, heq hz, heq (hS hw)]
}

lemma R_pair_congr_eqOn (beta : ℝ) (h_beta : beta > 1) {F₁ F₂ : KClass}
    (heq : EqOn F₁.F F₂.F H) {z : ℂ} (hz : z ∈ H)
    (hJ : J beta F₁ z > 0) (hgood : is_good_pair beta F₁ (G beta F₁ z)) :
    R_pair beta F₁ z = R_pair beta F₂ z := by
{
  have hG := (G_J_congr_eqOn beta heq hz).1
  have hgood' : is_good_pair beta F₂ (G beta F₂ z) := by
  {
    rw [← hG]
    exact (is_good_pair_congr_eqOn beta heq _).mp hgood
  }
  have hs := R_pair_spec_height beta h_beta F₁ hz hJ hgood
  obtain ⟨w, hw, _, hr_ex⟩ := exists_critical_equalRank beta h_beta F₁ (G beta F₁ z) hgood ⟨hz, rfl, hJ⟩
  have hr := rankPartner_spec ⟨w, hw, hr_ex⟩
  have hneg : negativeFiber beta F₁ (G beta F₁ z) = negativeFiber beta F₂ (G beta F₂ z) := by
  {
    rw [← signedFiber_neg_one, ← signedFiber_neg_one, signedFiber_congr_eqOn beta heq, hG]
  }
  have hpos : positiveFiber beta F₁ (G beta F₁ z) = positiveFiber beta F₂ (G beta F₂ z) := by
  {
    rw [← signedFiber_one, ← signedFiber_one, signedFiber_congr_eqOn beta heq, hG]
  }
  have hr' := hr.2
  change heightRank (criticalHeight beta F₁) (negativeFiber beta F₁ (G beta F₁ z)) (R_pair beta F₁ z) = _ at hr'
  rw [heightRank_congr_on (fun u hu => hu.1) (criticalHeight_congr_eqOn beta heq) hs.1,
    heightRank_congr_on (fun u hu => hu.1) (criticalHeight_congr_eqOn beta heq) hz, hneg, hpos] at hr'
  exact (rankPartner_eq (criticalHeight_rank_inj beta h_beta F₂ _ hgood').2 (hneg ▸ hr.1) hr').symm
}

def affineHome (t : ℂ) (ht : t ∈ H) : ℂ ≃ₜ ℂ :=
  (Homeomorph.mulLeft₀ (t.im : ℂ) (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))).trans
    (Homeomorph.addLeft (t.re : ℂ))

lemma affineHome_apply (t : ℂ) (ht : t ∈ H) (z : ℂ) :
    affineHome t ht z = aff t z := by
{
  rfl
}

lemma aff_mem_H_iff {t : ℂ} (ht : t ∈ H) (z : ℂ) :
    aff t z ∈ H ↔ z ∈ H := by
{
  change 0 < (aff t z).im ↔ 0 < z.im
  simp only [aff, Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.ofReal_re,
    zero_mul, zero_add, add_zero]
  exact mul_pos_iff_of_pos_left ht
}

def rerootTarget (F : KClass) (t xi : ℂ) : ℂ :=
  (xi - F.F t) / ((t.im : ℂ) * deriv F.F t)

def heightScaleInverse (beta : ℝ) (F : KClass) (t : ℂ) : ℝ :=
  t.im ^ (k_val beta - 1) / ‖deriv F.F t‖

lemma heightScaleInverse_pos (beta : ℝ) (F : KClass) {t : ℂ} (ht : t ∈ H) :
    0 < heightScaleInverse beta F t := by
{
  exact div_pos (Real.rpow_pos_of_pos ht _)
    (norm_pos_iff.mpr (deriv_ne_zero_of_univalentOn isOpen_H F.univalent ht))
}

lemma G_T_elem (beta : ℝ) (F : KClass) {t w : ℂ} (ht : t ∈ H) (hw : w ∈ H) :
    G beta (T_elem F t ht) w = rerootTarget F t (G beta F (aff t w)) := by
{
  have hy : (t.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hd : deriv F.F t ≠ 0 := deriv_ne_zero_of_univalentOn isOpen_H F.univalent ht
  have hF_aff : DifferentiableAt ℂ F.F (aff t w) :=
    (F.univalent.1 _ (aff_mem_H ht hw)).differentiableAt (isOpen_H.mem_nhds (aff_mem_H ht hw))
  have him : ((aff t w).im : ℂ) = (t.im : ℂ) * (w.im : ℂ) := by simp [aff]
  change G beta (T_elem F t ht) w = _
  unfold G rerootTarget
  change T t F.F w - I / (k_val beta : ℂ) * (w.im : ℂ) * deriv (T t F.F) w = _
  rw [deriv_T F.F t w hF_aff hy]
  simp only [T, him]
  field_simp
  ring
}

lemma G_T_elem_fiber (beta : ℝ) (F : KClass) {t w : ℂ} (ht : t ∈ H) (hw : w ∈ H) (xi : ℂ) :
    G beta (T_elem F t ht) w = rerootTarget F t xi ↔ G beta F (aff t w) = xi := by
{
  rw [G_T_elem beta F ht hw, rerootTarget, rerootTarget,
    div_left_inj' (mul_ne_zero (Complex.ofReal_ne_zero.mpr (ne_of_gt ht))
      (deriv_ne_zero_of_univalentOn isOpen_H F.univalent ht)), sub_left_inj]
}

lemma J_T_elem (beta : ℝ) (hk : k_val beta ≠ 0) (F : KClass) {t w : ℂ}
    (ht : t ∈ H) (hw : w ∈ H) :
    J beta (T_elem F t ht) w = J beta F (aff t w) := by
{
  apply mul_left_cancel₀ (pow_ne_zero 2 hk)
  rw [J_identity beta hk (T_elem F t ht) hw, J_identity beta hk F (aff_mem_H ht hw)]
  have hq : q (T_elem F t ht) w = q F (aff t w) := q_T_eq F t w ht hw
  simp only [a, hq]
}

lemma criticalHeight_T_elem (beta : ℝ) (F : KClass) {t w : ℂ} (ht : t ∈ H) (hw : w ∈ H) :
    criticalHeight beta (T_elem F t ht) w =
      criticalHeight beta F (aff t w) / heightScaleInverse beta F t := by
{
  have hy : (t.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt ht)
  have hF_aff : DifferentiableAt ℂ F.F (aff t w) :=
    (F.univalent.1 _ (aff_mem_H ht hw)).differentiableAt (isOpen_H.mem_nhds (aff_mem_H ht hw))
  have him : (aff t w).im = t.im * w.im := by simp [aff]
  have hn : ‖deriv F.F t‖ ≠ 0 :=
    norm_ne_zero_iff.mpr (deriv_ne_zero_of_univalentOn isOpen_H F.univalent ht)
  have hp : t.im ^ (k_val beta - 1) ≠ 0 := ne_of_gt (Real.rpow_pos_of_pos ht _)
  unfold criticalHeight heightScaleInverse
  change k_val beta * w.im ^ (k_val beta - 1) * ‖Q (T t F.F) w‖ = _
  rw [lemma_2_3_Q F.F t w hF_aff hy, norm_div, him, Real.mul_rpow ht.le hw.le]
  simp only [Q, norm_div, norm_one]
  field_simp
}

lemma superlevel_V_target_T_elem (beta : ℝ) (F : KClass) {t : ℂ} (ht : t ∈ H) (xi : ℂ)
    {delta : ℝ} (hdelta : 0 < delta) :
    {z ∈ H | V_target beta (T_elem F t ht) (rerootTarget F t xi) z ≥ ENNReal.ofReal delta} =
      (affineHome t ht) ⁻¹' {w ∈ H |
        V_target beta F xi w ≥ ENNReal.ofReal (delta * heightScaleInverse beta F t)} := by
{
  have hc := heightScaleInverse_pos beta F ht
  rw [superlevel_V_target_eq_closedPositiveSuperlevel beta (T_elem F t ht) _ hdelta,
    superlevel_V_target_eq_closedPositiveSuperlevel beta F xi (mul_pos hdelta hc)]
  ext z
  simp only [mem_preimage, affineHome_apply, closedPositiveSuperlevel, mem_setOf_eq]
  have him : (aff t z).im = t.im * z.im := by simp [aff]
  have h0 : 0 < z.im ↔ 0 < (aff t z).im := (aff_mem_H_iff ht z).symm
  rw [h0]
  refine and_congr_right (fun hz => ?_)
  have hz0 : 0 < z.im := h0.mpr hz
  have he : (T_elem F t ht).F z - rerootTarget F t xi =
      (F.F (aff t z) - xi) / ((t.im : ℂ) * deriv F.F t) := by
  {
    change T t F.F z - rerootTarget F t xi = _
    simp only [T, rerootTarget, ← sub_div]
    congr 1; ring
  }
  have hn : 0 < ‖deriv F.F t‖ :=
    norm_pos_iff.mpr (deriv_ne_zero_of_univalentOn isOpen_H F.univalent ht)
  have ht_pos : 0 < t.im := ht
  have hscale : t.im * ‖deriv F.F t‖ * (z.im ^ k_val beta / delta) =
      (aff t z).im ^ k_val beta / (delta * heightScaleInverse beta F t) := by
  {
    rw [him, Real.mul_rpow ht_pos.le hz0.le, heightScaleInverse, Real.rpow_sub_one ht_pos.ne']
    field_simp
  }
  rw [he, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg ht_pos.le,
    div_le_iff₀ (mul_pos ht_pos hn), mul_comm _ (t.im * ‖deriv F.F t‖), hscale]
}

lemma is_good_pair_T_elem (beta : ℝ) (hk : 0 < k_val beta) (F : KClass)
    {t : ℂ} (ht : t ∈ H) (xi : ℂ) :
    is_good_pair beta (T_elem F t ht) (rerootTarget F t xi) ↔ is_good_pair beta F xi := by
{
  have hc := heightScaleInverse_pos beta F ht
  constructor
  · rintro ⟨hcompact, hregular⟩
    refine ⟨fun delta hdelta => ?_, fun w hw hG => ?_⟩
    · have h := hcompact (delta / heightScaleInverse beta F t) (div_pos hdelta hc)
      rw [superlevel_V_target_T_elem beta F ht xi (div_pos hdelta hc),
        div_mul_cancel₀ _ hc.ne'] at h
      exact (affineHome t ht).isCompact_preimage.mp h
    · let z := (affineHome t ht).symm w
      have he : aff t z = w := (affineHome t ht).apply_symm_apply w
      have hz : z ∈ H := (aff_mem_H_iff ht z).mp (he.symm ▸ hw)
      have hr := hregular z hz ((G_T_elem_fiber beta F ht hz xi).mpr (he.symm ▸ hG))
      rwa [J_T_elem beta hk.ne' F ht hz, he] at hr
  · rintro ⟨hcompact, hregular⟩
    refine ⟨fun delta hdelta => ?_, fun z hz hG => ?_⟩
    · rw [superlevel_V_target_T_elem beta F ht xi hdelta]
      exact (affineHome t ht).isCompact_preimage.mpr (hcompact _ (mul_pos hdelta hc))
    · rw [J_T_elem beta hk.ne' F ht hz]
      exact hregular _ (aff_mem_H ht hz) ((G_T_elem_fiber beta F ht hz xi).mp hG)
}

lemma heightRank_transport_on {h₁ h₂ : ℂ → ℝ} {S S' : Set ℂ} (e : ℂ ≃ ℂ)
    (hS : ∀ w, w ∈ S' ↔ e w ∈ S) (z : ℂ)
    (hord : ∀ w ∈ S', heightPrecedes h₂ w z ↔ heightPrecedes h₁ (e w) (e z)) :
    heightRank h₂ S' z = heightRank h₁ S (e z) := by
{
  rw [heightRank_eq_ncard, heightRank_eq_ncard]
  apply Set.ncard_congr (fun w _ => e w)
  · intro w hw
    exact ⟨(hS w).mp hw.1, (hord w hw.1).mp hw.2⟩
  · intro a b _ _ hab
    exact e.injective hab
  · intro w hw
    have hm : e.symm w ∈ S' := (hS _).mpr (by simpa using hw.1)
    exact ⟨e.symm w, ⟨hm, (hord _ hm).mpr (by simpa using hw.2)⟩, e.apply_symm_apply w⟩
}

lemma heightPrecedes_T_elem (beta : ℝ) (F : KClass) {t z w : ℂ}
    (ht : t ∈ H) (hz : z ∈ H) (hw : w ∈ H) :
    heightPrecedes (criticalHeight beta (T_elem F t ht)) z w ↔
      heightPrecedes (criticalHeight beta F) (aff t z) (aff t w) := by
{
  have hc := heightScaleInverse_pos beta F ht
  have hre (v : ℂ) : (aff t v).re = t.re + t.im * v.re := by simp [aff]
  have him (v : ℂ) : (aff t v).im = t.im * v.im := by simp [aff]
  simp only [heightPrecedes, criticalHeight_T_elem beta F ht hz, criticalHeight_T_elem beta F ht hw,
    div_lt_div_iff_of_pos_right hc, div_left_inj' hc.ne', hre, him,
    add_lt_add_iff_left, add_right_inj, mul_lt_mul_iff_right₀ (show 0 < t.im from ht),
    mul_right_inj' (ne_of_gt (show 0 < t.im from ht))]
}

lemma signedFiber_T_elem (beta : ℝ) (hk : 0 < k_val beta) (F : KClass)
    {t : ℂ} (ht : t ∈ H) (xi : ℂ) (σ : ℝ) (w : ℂ) :
    w ∈ signedFiber beta (T_elem F t ht) (rerootTarget F t xi) σ ↔
      aff t w ∈ signedFiber beta F xi σ := by
{
  simp only [signedFiber, mem_setOf_eq, aff_mem_H_iff ht]
  apply and_congr_right
  intro hw
  rw [G_T_elem_fiber beta F ht hw xi, J_T_elem beta hk.ne' F ht hw]
}

lemma heightRank_T_elem (beta : ℝ) (hk : 0 < k_val beta) (F : KClass)
    {t z : ℂ} (ht : t ∈ H) (hz : z ∈ H) (xi : ℂ) (σ : ℝ) :
    heightRank (criticalHeight beta (T_elem F t ht))
      (signedFiber beta (T_elem F t ht) (rerootTarget F t xi) σ) z =
      heightRank (criticalHeight beta F) (signedFiber beta F xi σ) (aff t z) := by
{
  apply heightRank_transport_on (affineHome t ht).toEquiv
    (signedFiber_T_elem beta hk F ht xi σ) z
  intro w hw
  exact heightPrecedes_T_elem beta F ht hw.1 hz
}

lemma R_pair_T_elem (beta : ℝ) (h_beta : beta > 1) (F : KClass)
    {t z : ℂ} (ht : t ∈ H) (hz : z ∈ H)
    (hJ : J beta F (aff t z) > 0)
    (hg : is_good_pair beta F (G beta F (aff t z))) :
    aff t (R_pair beta (T_elem F t ht) z) = R_pair beta F (aff t z) := by
{
  have hk : 0 < k_val beta := by unfold k_val; linarith
  let F' := T_elem F t ht
  have hG : G beta F' z = rerootTarget F t (G beta F (aff t z)) := G_T_elem beta F ht hz
  have hg' : is_good_pair beta F' (G beta F' z) := by
  {
    rw [hG]
    exact (is_good_pair_T_elem beta hk F ht _).mpr hg
  }
  have hJ' : J beta F' z > 0 := by
  {
    rw [J_T_elem beta hk.ne' F ht hz]
    exact hJ
  }
  have hs := R_pair_spec_height beta h_beta F' hz hJ' hg'
  obtain ⟨w, hw, _, he_rk⟩ := exists_critical_equalRank beta h_beta F' (G beta F' z) hg' ⟨hz, rfl, hJ'⟩
  have hr := rankPartner_spec ⟨w, hw, he_rk⟩
  have hr' : heightRank (criticalHeight beta F)
      (negativeFiber beta F (G beta F (aff t z))) (aff t (R_pair beta F' z)) =
      heightRank (criticalHeight beta F)
      (positiveFiber beta F (G beta F (aff t z))) (aff t z) := by
  {
    have h := hr.2
    change heightRank (criticalHeight beta F') (negativeFiber beta F' (G beta F' z))
      (R_pair beta F' z) = _ at h
    rw [← signedFiber_neg_one, ← signedFiber_one, hG,
      heightRank_T_elem beta hk F ht hs.1 _ (-1), heightRank_T_elem beta hk F ht hz _ 1,
      signedFiber_neg_one, signedFiber_one] at h
    exact h
  }
  have hm : aff t (R_pair beta F' z) ∈ negativeFiber beta F (G beta F (aff t z)) := by
  {
    rw [← signedFiber_neg_one, ← signedFiber_T_elem beta hk F ht _ (-1), ← hG, signedFiber_neg_one]
    exact ⟨hs.1, hs.2.1⟩
  }
  exact (rankPartner_eq (criticalHeight_rank_inj beta h_beta F _ hg).2 hm hr').symm
}

lemma J_T_elem_root (beta : ℝ) (hk : k_val beta ≠ 0) (F : KClass) {z : ℂ} (hz : z ∈ H) :
    J beta (T_elem F z hz) I = J beta F z := by
{
  have hI : I ∈ H := by dsimp [H]; simp
  simpa only [aff_I] using J_T_elem beta hk F hz hI
}

lemma is_good_pair_T_elem_root (beta : ℝ) (hk : 0 < k_val beta) (F : KClass) {z : ℂ} (hz : z ∈ H) :
    is_good_pair beta (T_elem F z hz) (G beta (T_elem F z hz) I) ↔
      is_good_pair beta F (G beta F z) := by
{
  have hI : I ∈ H := by dsimp [H]; simp
  rw [G_T_elem beta F hz hI, aff_I]
  exact is_good_pair_T_elem beta hk F hz (G beta F z)
}

lemma R_pair_T_elem_root (beta : ℝ) (h_beta : beta > 1) (F : KClass) {z : ℂ} (hz : z ∈ H)
    (hJ : J beta F z > 0) (hg : is_good_pair beta F (G beta F z)) :
    aff z (R_pair beta (T_elem F z hz) I) = R_pair beta F z := by
{
  have hI : I ∈ H := by dsimp [H]; simp
  simpa only [aff_I] using R_pair_T_elem beta h_beta F hz hI
    (by simpa only [aff_I] using hJ) (by simpa only [aff_I] using hg)
}

/-!
## Part 2: Borel Branches and Measurability of `R_pair`
-/

lemma joint_locally_injective {P : Type*} [TopologicalSpace P]
    {F : P → ℂ → ℂ} {DF : P → ℂ → ℂ →L[ℝ] ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hder : ∀ p z, z ∈ s → HasFDerivAt (F p) (DF p z) z)
    (hc : ContinuousOn (fun q : P × ℂ => DF q.1 q.2) (univ ×ˢ s))
    {p : P} {z : ℂ} (hz : z ∈ s) (he : LinearMap.det (DF p z).toLinearMap ≠ 0) :
    ∃ U : Set (P × ℂ), IsOpen U ∧ (p, z) ∈ U ∧
      InjOn (fun q : P × ℂ => (q.1, F q.1 q.2)) U := by
{
  let e : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr he)).toContinuousLinearEquiv
  have heq : (e : ℂ →L[ℝ] ℂ) = DF p z := by
  {
    ext v
    exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr he) v
  }
  let c : ℝ≥0 := ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ / 2
  have hn : 0 < ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊ := by exact_mod_cast e.symm.norm_pos
  have hcpos : 0 < c := by dsimp [c]; positivity
  have hclt : c < ‖(e.symm : ℂ →L[ℝ] ℂ)‖₊⁻¹ := half_lt_self (inv_pos.mpr hn)
  have hcAt : ContinuousAt (fun q : P × ℂ => DF q.1 q.2) (p, z) :=
    hc.continuousAt ((isOpen_univ.prod hs).mem_nhds ⟨mem_univ p, hz⟩)
  have hnb : {q : P × ℂ | q.2 ∈ s ∧ ‖DF q.1 q.2 - (e : ℂ →L[ℝ] ℂ)‖₊ < c} ∈ 𝓝 (p, z) := by
  {
    apply Filter.inter_mem
    · exact continuous_snd.continuousAt.preimage_mem_nhds (hs.mem_nhds hz)
    · exact ((hcAt.sub continuousAt_const).nnnorm).eventually
        (gt_mem_nhds (by simpa only [Pi.sub_apply, heq, sub_self, nnnorm_zero] using hcpos))
  }
  obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hnb
  obtain ⟨u', hu'u, hu'o, hpu⟩ := mem_nhds_iff.mp hu
  obtain ⟨r, hr, hvr⟩ := Metric.mem_nhds_iff.mp hv
  refine ⟨u' ×ˢ Metric.ball z r, hu'o.prod Metric.isOpen_ball, ⟨hpu, Metric.mem_ball_self hr⟩, ?_⟩
  rintro ⟨p1, z1⟩ h1 ⟨p2, z2⟩ h2 hh
  have hp : p1 = p2 := congrArg Prod.fst hh
  subst p2
  have hbound (w : ℂ) (hw : w ∈ Metric.ball z r) :
      w ∈ s ∧ ‖DF p1 w - (e : ℂ →L[ℝ] ℂ)‖₊ < c :=
    huv (show (p1, w) ∈ u ×ˢ v from ⟨hu'u h1.1, hvr hw⟩)
  have hLip : LipschitzOnWith c (fun w => F p1 w - e w) (Metric.ball z r) :=
    (convex_ball z r).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun w hw => ((hder p1 w (hbound w hw).1).sub e.hasFDerivAt).hasFDerivWithinAt)
      (fun w hw => (hbound w hw).2.le)
  exact Prod.ext rfl (hLip.approximatesLinearOn.injOn (Or.inr hclt) h1.2 h2.2 (congrArg Prod.snd hh))
}

lemma countable_joint_injective_partition {P : Type*} [TopologicalSpace P]
    [SecondCountableTopology P] [MeasurableSpace P] [BorelSpace P]
    {F : P → ℂ → ℂ} {DF : P → ℂ → ℂ →L[ℝ] ℂ} {s : Set ℂ}
    (hs : IsOpen s) (hder : ∀ p z, z ∈ s → HasFDerivAt (F p) (DF p z) z)
    (hc : ContinuousOn (fun q : P × ℂ => DF q.1 q.2) (univ ×ˢ s)) :
    ∃ p : ℕ → Set (P × ℂ), (∀ n, MeasurableSet (p n)) ∧
      Pairwise (Disjoint on p) ∧
      (⋃ n, p n) = {q | q.2 ∈ s ∧ LinearMap.det (DF q.1 q.2).toLinearMap ≠ 0} ∧
      ∀ n, InjOn (fun q : P × ℂ => (q.1, F q.1 q.2)) (p n) := by
{
  let t : Set (P × ℂ) := {q | q.2 ∈ s ∧ LinearMap.det (DF q.1 q.2).toLinearMap ≠ 0}
  have htopen : IsOpen t := by
  {
    have h : IsOpen ((univ ×ˢ s) ∩ (fun q : P × ℂ => DF q.1 q.2) ⁻¹' {d | d.det ≠ 0}) :=
      hc.isOpen_inter_preimage (isOpen_univ.prod hs)
        (isClosed_eq ContinuousLinearMap.continuous_det continuous_const).isOpen_compl
    convert h using 1
    ext q
    simp [t]
  }
  have hlocal (q : t) : ∃ U : Set (P × ℂ), IsOpen U ∧ q.val ∈ U ∧
      InjOn (fun q : P × ℂ => (q.1, F q.1 q.2)) U :=
    joint_locally_injective hs hder hc q.property.1 q.property.2
  choose U hUo hUq hUi using hlocal
  by_cases he : t = ∅
  · refine ⟨fun _ => ∅, by simp, by simp [Pairwise], ?_, by simp⟩
    simpa using he.symm
  · have : Nonempty t := Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr he)
    obtain ⟨j, hj⟩ := (HereditarilyLindelofSpace.isLindelof t).indexed_countable_subcover
      U hUo (fun q hq => mem_iUnion.mpr ⟨⟨q, hq⟩, hUq ⟨q, hq⟩⟩)
    let q : ℕ → Set (P × ℂ) := fun n => t ∩ U (j n)
    refine ⟨disjointed q, ?_, disjoint_disjointed q, ?_, ?_⟩
    · intro n
      exact MeasurableSet.disjointed (fun n => htopen.measurableSet.inter (hUo (j n)).measurableSet) n
    · rw [iUnion_disjointed]
      ext z
      simp only [mem_iUnion, mem_inter_iff, q]
      exact ⟨fun ⟨_, hz, _⟩ => hz, fun hz => by obtain ⟨n, hn⟩ := mem_iUnion.mp (hj hz); exact ⟨n, hz, hn⟩⟩
    · intro n
      exact (hUi (j n)).mono ((disjointed_subset q n).trans inter_subset_right)
}

lemma exists_borel_partial_inverse {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {s : Set X} (hs : MeasurableSet s) (hf : ContinuousOn f s) (hi : InjOn f s) :
    ∃ b : Y → X, Measurable b ∧ MeasurableSet (f '' s) ∧
      (∀ y ∈ f '' s, b y ∈ s ∧ f (b y) = y) ∧ ∀ x ∈ s, b (f x) = x := by
{
  have hm := hf.measurableEmbedding hs hi
  by_cases hne : s.Nonempty
  · let : Nonempty s := Set.nonempty_coe_sort.mpr hne
    let b : Y → X := fun y => (hm.invFun y).val
    refine ⟨b, measurable_subtype_coe.comp hm.measurable_invFun, ?_, ?_, ?_⟩
    · simpa only [Set.range_restrict] using hm.measurableSet_range
    · rintro y ⟨x, hx, rfl⟩
      have hb : b (f x) = x := congrArg Subtype.val (hm.leftInverse_invFun ⟨x, hx⟩)
      exact ⟨hb.symm ▸ hx, congrArg f hb⟩
    · intro x hx
      exact congrArg Subtype.val (hm.leftInverse_invFun ⟨x, hx⟩)
  · have he : s = ∅ := not_nonempty_iff_eq_empty.mp hne
    refine ⟨fun _ => Classical.arbitrary X, measurable_const, ?_, ?_, ?_⟩ <;> simp [he]
}

lemma fiber_count_eq_tsum_branches {X Y : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    {f : X → Y} {s : Set X} {p : ℕ → Set X} {b : ℕ → Y → X}
    (hp : Pairwise (Disjoint on p)) (hu : (⋃ n, p n) = s)
    (hi : ∀ n, InjOn f (p n))
    (hb : ∀ n y, y ∈ f '' p n → b n y ∈ p n ∧ f (b n y) = y)
    (hinv : ∀ n x, x ∈ p n → b n (f x) = x)
    (R : X → Prop) (y : Y) :
    Measure.count {x | x ∈ s ∧ f x = y ∧ R x} =
      ∑' n, if y ∈ f '' p n ∧ R (b n y) then (1 : ℝ≥0∞) else 0 := by
{
  have he : {x | x ∈ s ∧ f x = y ∧ R x} = ⋃ n, {x | x ∈ p n ∧ f x = y ∧ R x} := by
  {
    rw [← hu]
    ext x
    simp only [mem_setOf_eq, mem_iUnion]
    aesop
  }
  have hsub (n) : ({x | x ∈ p n ∧ f x = y ∧ R x} : Set X).Subsingleton := by
  {
    intro x hx z hz
    exact hi n hx.1 hz.1 (hx.2.1.trans hz.2.1.symm)
  }
  rw [he, measure_iUnion]
  · apply tsum_congr
    intro n
    by_cases hy : y ∈ f '' p n ∧ R (b n y)
    · rw [if_pos hy]
      have hx : {x | x ∈ p n ∧ f x = y ∧ R x} = {b n y} := by
      {
        apply Set.Subsingleton.eq_singleton_of_mem (hsub n)
        exact ⟨(hb n y hy.1).1, (hb n y hy.1).2, hy.2⟩
      }
      rw [hx, Measure.count_singleton]
    · rw [if_neg hy]
      have hx : {x | x ∈ p n ∧ f x = y ∧ R x} = ∅ := by
      {
        apply eq_empty_iff_forall_notMem.mpr
        intro x hx
        apply hy
        refine ⟨⟨x, hx.1, hx.2.1⟩, ?_⟩
        rw [← hx.2.1, hinv n x hx.1]
        exact hx.2.2
      }
      rw [hx, measure_empty]
  · exact pairwise_disjoint_mono hp (fun n => fun x hx => hx.1)
  · intro n
    exact (hsub n).countable.measurableSet
}

lemma measurable_fiber_count_branches {X Y Q_t : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSpace Q_t]
    {f : X → Y} {s : Set X} {p : ℕ → Set X} {b : ℕ → Y → X}
    (hp : Pairwise (Disjoint on p)) (hu : (⋃ n, p n) = s)
    (hi : ∀ n, InjOn f (p n)) (hbm : ∀ n, Measurable (b n))
    (hdm : ∀ n, MeasurableSet (f '' p n))
    (hb : ∀ n y, y ∈ f '' p n → b n y ∈ p n ∧ f (b n y) = y)
    (hinv : ∀ n x, x ∈ p n → b n (f x) = x)
    {R : Q_t → X → Prop} (hR : MeasurableSet {q : Q_t × X | R q.1 q.2})
    {y : Q_t → Y} (hy : Measurable y) :
    Measurable (fun q => Measure.count {x | x ∈ s ∧ f x = y q ∧ R q x}) := by
{
  have he : (fun q => Measure.count {x | x ∈ s ∧ f x = y q ∧ R q x}) =
      fun q => ∑' n, if y q ∈ f '' p n ∧ R q (b n (y q)) then (1 : ℝ≥0∞) else 0 := by
  {
    funext q
    exact fiber_count_eq_tsum_branches hp hu hi hb hinv (R q) (y q)
  }
  rw [he]
  apply Measurable.tsum
  intro n
  exact Measurable.ite ((hdm n |>.preimage hy).inter
    (hR.preimage (measurable_id.prodMk ((hbm n).comp hy)))) measurable_const measurable_const
}

lemma measurable_branch_selection {Q_t X : Type*} [MeasurableSpace Q_t] [MeasurableSpace X]
    {b : ℕ → Q_t → X} {M : ℕ → Set Q_t} {f : Q_t → X}
    (hb : ∀ n, Measurable (b n)) (hM : ∀ n, MeasurableSet (M n))
    (he : ∀ q, ∃ n, q ∈ M n) (hf : ∀ n q, q ∈ M n → f q = b n q) : Measurable f := by
{
  intro T hT
  have hset : f ⁻¹' T = ⋃ n, M n ∩ (b n) ⁻¹' T := by
  {
    ext q
    constructor
    · intro hq
      obtain ⟨n, hn⟩ := he q
      exact mem_iUnion.mpr ⟨n, hn, by simpa only [mem_preimage, ← hf n q hn] using hq⟩
    · intro hq
      obtain ⟨n, hn, ht⟩ := mem_iUnion.mp hq
      simpa only [mem_preimage, hf n q hn] using ht
  }
  rw [hset]
  exact MeasurableSet.iUnion (fun n => (hM n).inter (hT.preimage (hb n)))
}

structure BorelBranches {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    (f : X → Y) (s : Set X) where
  part : ℕ → Set X
  branch : ℕ → Y → X
  measurable_part : ∀ n, MeasurableSet (part n)
  disjoint : Pairwise (Disjoint on part)
  cover : (⋃ n, part n) = s
  injective : ∀ n, InjOn f (part n)
  measurable_branch : ∀ n, Measurable (branch n)
  measurable_image : ∀ n, MeasurableSet (f '' part n)
  right_inv : ∀ n y, y ∈ f '' part n → branch n y ∈ part n ∧ f (branch n y) = y
  left_inv : ∀ n x, x ∈ part n → branch n (f x) = x

lemma exists_borelBranches {X Y : Type*}
    [TopologicalSpace X] [PolishSpace X] [MeasurableSpace X] [BorelSpace X] [Nonempty X]
    [TopologicalSpace Y] [T2Space Y] [MeasurableSpace Y] [BorelSpace Y]
    {f : X → Y} {s : Set X} (hf : ContinuousOn f s)
    (hp : ∃ p : ℕ → Set X, (∀ n, MeasurableSet (p n)) ∧ Pairwise (Disjoint on p) ∧
      (⋃ n, p n) = s ∧ ∀ n, InjOn f (p n)) : Nonempty (BorelBranches f s) := by
{
  obtain ⟨p, hpm, hpd, hpc, hpi⟩ := hp
  have hb (n) := exists_borel_partial_inverse (hpm n)
    (hf.mono (show p n ⊆ s from hpc ▸ subset_iUnion p n)) (hpi n)
  choose b hbm him hbr hbl using hb
  exact ⟨⟨p, b, hpm, hpd, hpc, hpi, hbm, him, hbr, hbl⟩⟩
}

lemma BorelBranches.measurable_count {X Y Q_t : Type*}
    [MeasurableSpace X] [MeasurableSingletonClass X] [MeasurableSpace Y] [MeasurableSpace Q_t]
    {f : X → Y} {s : Set X} (B : BorelBranches f s)
    {R : Q_t → X → Prop} (hR : MeasurableSet {q : Q_t × X | R q.1 q.2})
    {y : Q_t → Y} (hy : Measurable y) :
    Measurable (fun q => Measure.count {x | x ∈ s ∧ f x = y q ∧ R q x}) := by
{
  exact measurable_fiber_count_branches B.disjoint B.cover B.injective B.measurable_branch
    B.measurable_image B.right_inv B.left_inv hR hy
}

lemma count_product_fiber {P X Y : Type*} [MeasurableSpace P] [MeasurableSingletonClass P]
    [MeasurableSpace X] [MeasurableSingletonClass X] (F : P → X → Y)
    (R : P × X → Prop) (p : P) (y : Y) :
    Measure.count {q : P × X | (q.1, F q.1 q.2) = (p, y) ∧ R q} =
      Measure.count {x | F p x = y ∧ R (p, x)} := by
{
  have he : {q : P × X | (q.1, F q.1 q.2) = (p, y) ∧ R q} =
      (fun x => (p, x)) '' {x | F p x = y ∧ R (p, x)} := by
  {
    ext q
    constructor
    · rintro ⟨hq, hR⟩
      obtain rfl : q.1 = p := congrArg Prod.fst hq
      exact ⟨q.2, ⟨congrArg Prod.snd hq, hR⟩, rfl⟩
    · rintro ⟨x, ⟨hx, hR⟩, rfl⟩
      exact ⟨Prod.ext rfl hx, hR⟩
  }
  rw [he]
  exact Measure.count_injective_image (fun _ _ h => congrArg Prod.snd h) _
}

lemma count_subtype_set {X : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    (s : Set X) (R : X → Prop) :
    Measure.count {x : s | R x} = Measure.count {x : X | x ∈ s ∧ R x} := by
{
  rw [← Measure.count_injective_image (f := (Subtype.val : s → X)) Subtype.val_injective]
  congr 1
  ext x
  simp only [mem_image, mem_setOf_eq, Subtype.exists, exists_prop]
  aesop
}

instance : PolishSpace DiskClass := by
{
  let := TopologicalSpace.metrizableSpaceMetric DiskClass
  infer_instance
}

instance : PolishSpace H := isOpen_H.polishSpace

instance : Nonempty H := ⟨⟨I, by dsimp [H]; simp⟩⟩

def jointCriticalMap (beta : ℝ) (q : DiskClass × H) : DiskClass × ℂ :=
  (q.1, G beta (toKClass q.1) q.2)

def nonsingularClass (beta : ℝ) : Set (DiskClass × H) :=
  {q | J beta (toKClass q.1) q.2 ≠ 0}

lemma continuous_jointCriticalMap (beta : ℝ) : Continuous (jointCriticalMap beta) := by
{
  exact continuous_fst.prodMk (continuous_diskClass_G beta)
}

lemma continuous_diskClass_fderiv_G_CLM (beta : ℝ) :
    Continuous (fun p : DiskClass × H => fderiv ℝ (G beta (toKClass p.1)) p.2) := by
{
  let A : ℂ →L[ℝ] ℂ := 1
  let B : ℂ →L[ℝ] ℂ := Complex.ofRealCLM.comp Complex.imCLM
  have he (p : DiskClass × H) : fderiv ℝ (G beta (toKClass p.1)) p.2 =
      deriv (toKClass p.1).F p.2 • A -
      (I / (k_val beta : ℂ) * (p.2.val.im : ℂ) * deriv (deriv (toKClass p.1).F) p.2) • A -
      (I / (k_val beta : ℂ) * deriv (toKClass p.1).F p.2) • B := by
  {
    ext v
    rw [fderiv_G_apply beta (toKClass p.1) p.2.2]
    change _ = deriv (toKClass p.1).F p.2 * v -
      (I / (k_val beta : ℂ) * (p.2.val.im : ℂ) * deriv (deriv (toKClass p.1).F) p.2) * v -
      (I / (k_val beta : ℂ) * deriv (toKClass p.1).F p.2) * (v.im : ℂ)
    ring
  }
  simp_rw [he]
  have hy : Continuous (fun p : DiskClass × H => (p.2.val.im : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd))
  exact ((continuous_diskClass_deriv.smul continuous_const).sub
    (((continuous_const.mul hy).mul continuous_diskClass_deriv2).smul continuous_const)).sub
    ((continuous_const.mul continuous_diskClass_deriv).smul continuous_const)
}

lemma continuous_diskClass_criticalHeight (beta : ℝ) :
    Continuous (fun p : DiskClass × H => criticalHeight beta (toKClass p.1) p.2) := by
{
  have hy : Continuous (fun p : DiskClass × H => p.2.val.im ^ (k_val beta - 1)) :=
    (Complex.continuous_im.comp (continuous_subtype_val.comp continuous_snd)).rpow_const
      (fun p => Or.inl (ne_of_gt p.2.2))
  have hh : Continuous (fun p : DiskClass × H =>
      k_val beta * p.2.val.im ^ (k_val beta - 1) * ‖deriv (toKClass p.1).F p.2‖⁻¹) :=
    (continuous_const.mul hy).mul (continuous_diskClass_deriv.norm.inv₀
      (fun p => norm_ne_zero_iff.mpr (deriv_ne_zero_of_univalentOn isOpen_H
        (toKClass p.1).univalent p.2.2)))
  exact hh.congr (fun p => by simp only [criticalHeight, Q, one_div, norm_inv])
}

lemma continuousOn_prod_of_continuous_subtype {P X Y : Type*}
    [TopologicalSpace P] [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {F : P → X → Y}
    (hF : Continuous (fun q : P × s => F q.1 q.2)) :
    ContinuousOn (fun q : P × X => F q.1 q.2) (univ ×ˢ s) := by
{
  apply continuousOn_iff_continuous_restrict.mpr
  exact hF.comp (continuous_subtype_val.fst.prodMk
    (continuous_subtype_val.snd.subtype_mk (fun q => q.property.2)))
}

lemma exists_class_branches (beta : ℝ) :
    Nonempty (BorelBranches (jointCriticalMap beta) (nonsingularClass beta)) := by
{
  apply exists_borelBranches (continuous_jointCriticalMap beta).continuousOn
  obtain ⟨p, hpm, hpd, hpc, hpi⟩ := countable_joint_injective_partition isOpen_H
    (fun g z hz => (differentiableAt_G beta (toKClass g) hz).hasFDerivAt)
    (continuousOn_prod_of_continuous_subtype
      (F := fun g z => fderiv ℝ (G beta (toKClass g)) z) (continuous_diskClass_fderiv_G_CLM beta))
  let e : DiskClass × H → DiskClass × ℂ := fun q => (q.1, q.2)
  have hem : Measurable e := measurable_fst.prodMk (measurable_subtype_coe.comp measurable_snd)
  let u : ℕ → Set (DiskClass × H) := fun n => e ⁻¹' p n
  refine ⟨u, fun n => (hpm n).preimage hem, ?_, ?_, ?_⟩
  · intro n m hnm
    exact (hpd hnm).preimage e
  · ext q
    have hc : (∃ n, e q ∈ p n) ↔ (e q).2 ∈ H ∧
        LinearMap.det (fderiv ℝ (G beta (toKClass q.1)) q.2).toLinearMap ≠ 0 := by
    {
      rw [← mem_iUnion, hpc]
      rfl
    }
    simp only [mem_iUnion, mem_preimage, u]
    rw [hc]
    have hdet : ((fderiv ℝ (G beta (toKClass q.1)) q.2 1).re *
        (fderiv ℝ (G beta (toKClass q.1)) q.2 I).im -
        (fderiv ℝ (G beta (toKClass q.1)) q.2 I).re *
        (fderiv ℝ (G beta (toKClass q.1)) q.2 1).im) =
        LinearMap.det (fderiv ℝ (G beta (toKClass q.1)) q.2).toLinearMap :=
      (determinant_complex_real (fderiv ℝ (G beta (toKClass q.1)) q.2).toLinearMap).symm
    simp only [e, q.2.2, true_and, nonsingularClass, mem_setOf_eq, J, hdet]
    exact (div_ne_zero_iff.trans (and_iff_left
      (pow_ne_zero _ (norm_ne_zero_iff.mpr (deriv_ne_zero_of_univalentOn isOpen_H
        (toKClass q.1).univalent q.2.2))))).symm
  · intro n q hq r hr he
    have hz : e q = e r := hpi n hq hr he
    have hfst : q.1 = r.1 := congrArg (fun x : DiskClass × ℂ => x.1) hz
    have hsnd : q.2.val = r.2.val := congrArg (fun x : DiskClass × ℂ => x.2) hz
    exact Prod.ext hfst (Subtype.ext hsnd)
}

def classPrecedes (beta : ℝ) (q r : DiskClass × H) : Prop :=
  criticalHeight beta (toKClass r.1) r.2 < criticalHeight beta (toKClass q.1) q.2 ∨
  criticalHeight beta (toKClass q.1) q.2 = criticalHeight beta (toKClass r.1) r.2 ∧
    (q.2.val.re < r.2.val.re ∨ q.2.val.re = r.2.val.re ∧ q.2.val.im < r.2.val.im)

lemma measurableSet_classPrecedes (beta : ℝ) :
    MeasurableSet {p : (DiskClass × H) × (DiskClass × H) | classPrecedes beta p.1 p.2} := by
{
  have hH := (continuous_diskClass_criticalHeight beta).measurable
  have hr : Measurable (fun q : DiskClass × H => q.2.val.re) :=
    Complex.continuous_re.measurable.comp (measurable_subtype_coe.comp measurable_snd)
  have hi : Measurable (fun q : DiskClass × H => q.2.val.im) :=
    Complex.continuous_im.measurable.comp (measurable_subtype_coe.comp measurable_snd)
  exact (measurableSet_lt (hH.comp measurable_snd) (hH.comp measurable_fst)).union
    ((measurableSet_eq_fun (hH.comp measurable_fst) (hH.comp measurable_snd)).inter
      ((measurableSet_lt (hr.comp measurable_fst) (hr.comp measurable_snd)).union
        ((measurableSet_eq_fun (hr.comp measurable_fst) (hr.comp measurable_snd)).inter
          (measurableSet_lt (hi.comp measurable_fst) (hi.comp measurable_snd)))))
}

def classRankCount (beta σ : ℝ) (q : DiskClass × H) : ℝ≥0∞ :=
  Measure.count {r | r ∈ nonsingularClass beta ∧ jointCriticalMap beta r = jointCriticalMap beta q ∧
    0 < σ * J beta (toKClass r.1) r.2 ∧ classPrecedes beta r q}

lemma measurable_classRankCount (beta σ : ℝ) : Measurable (classRankCount beta σ) := by
{
  let B := Classical.choice (exists_class_branches beta)
  apply B.measurable_count _ (continuous_jointCriticalMap beta).measurable
  exact (measurableSet_lt measurable_const
    (measurable_const.mul ((continuous_diskClass_J beta).measurable.comp measurable_snd))).inter
    ((measurableSet_classPrecedes beta).preimage measurable_swap)
}

lemma classRankCount_eq_count (beta σ : ℝ) (q : DiskClass × H) :
    classRankCount beta σ q = Measure.count {w | w ∈ signedFiber beta (toKClass q.1)
      (G beta (toKClass q.1) q.2) σ ∧ heightPrecedes (criticalHeight beta (toKClass q.1)) w q.2} := by
{
  let R : DiskClass × H → Prop := fun r =>
    0 < σ * J beta (toKClass r.1) r.2 ∧ classPrecedes beta r q
  have he : {r | r ∈ nonsingularClass beta ∧ jointCriticalMap beta r = jointCriticalMap beta q ∧ R r} =
      {r : DiskClass × H | jointCriticalMap beta r = jointCriticalMap beta q ∧ R r} := by
  {
    ext r
    refine ⟨fun h => h.2, fun h => ⟨fun hz => ?_, h⟩⟩
    have hp := h.2.1
    rw [hz, mul_zero] at hp
    exact lt_irrefl 0 hp
  }
  change Measure.count {r | r ∈ nonsingularClass beta ∧ jointCriticalMap beta r = jointCriticalMap beta q ∧ R r} = _
  rw [he]
  simp only [jointCriticalMap]
  rw [count_product_fiber (fun g (z : H) => G beta (toKClass g) z) R]
  change Measure.count {w : H | G beta (toKClass q.1) w = G beta (toKClass q.1) q.2 ∧
    0 < σ * J beta (toKClass q.1) w ∧ heightPrecedes (criticalHeight beta (toKClass q.1)) w q.2} = _
  rw [count_subtype_set H (fun w : ℂ => G beta (toKClass q.1) w = G beta (toKClass q.1) q.2 ∧
    0 < σ * J beta (toKClass q.1) w ∧ heightPrecedes (criticalHeight beta (toKClass q.1)) w q.2)]
  congr 1
  ext w
  simp only [mem_setOf_eq, signedFiber]
  tauto
}

lemma classRankCount_eq_heightRank {beta : ℝ} (h_beta : beta > 1) (σ : ℝ) (q : DiskClass × H)
    (hg : is_good_pair beta (toKClass q.1) (G beta (toKClass q.1) q.2)) :
    classRankCount beta σ q =
      (heightRank (criticalHeight beta (toKClass q.1))
        (signedFiber beta (toKClass q.1) (G beta (toKClass q.1) q.2) σ) q.2 : ℝ≥0∞) := by
{
  have hk : 0 < k_val beta := by unfold k_val; linarith
  rw [classRankCount_eq_count, heightRank_eq_ncard]
  have hpos := criticalHeight_pos beta hk (toKClass q.1) q.2.2
  have hc := finite_critical_superlevel_KClass beta (toKClass q.1) _ hg _ hpos
  have hf : {w | w ∈ signedFiber beta (toKClass q.1) (G beta (toKClass q.1) q.2) σ ∧
      heightPrecedes (criticalHeight beta (toKClass q.1)) w q.2}.Finite := by
  {
    apply hc.subset
    intro w hw
    refine ⟨hw.1.1, ?_, hw.1.2.1⟩
    rw [V_target_eq_criticalHeight beta hk (toKClass q.1) hw.1.1 hw.1.2.1]
    exact ENNReal.ofReal_le_ofReal
      (heightOrder_height_le ((heightOrder_lt_iff _ _ _).mpr hw.2))
  }
  rw [Measure.count_apply_finite _ hf, ← Set.ncard_eq_toFinset_card _ hf]
}

def pairingDomainDisk (beta : ℝ) : Set (DiskClass × H) :=
  {q | 0 < J beta (toKClass q.1) q.2 ∧
    is_good_pair beta (toKClass q.1) (G beta (toKClass q.1) q.2)}

def pairingDomain (beta : ℝ) : Set (KClass × H) :=
  {q | 0 < J beta q.1 q.2 ∧ is_good_pair beta q.1 (G beta q.1 q.2)}

lemma A_weight_ofKClass (F : KClass) (z : H) :
    A_weight z.1 F.F = diskWeight (ofKClass F) z := by
{
  dsimp [A_weight, diskWeight, Q]
  rw [(toKClass_ofKClass_eqOn F).deriv isOpen_H z.2]
}

lemma ofKClass_T_elem (F : KClass) (z : H) :
    ofKClass (T_elem F z.1 z.2) = rerootDisk (ofKClass F) z := by
{
  exact ofKClass_eq_of_eqOn (T_congr (toKClass_ofKClass_eqOn F) z.2).symm
}

instance kClassSecondCountable : SecondCountableTopology KClass :=
  (Topology.IsInducing.induced ofKClass).secondCountableTopology

attribute [local irreducible] toKClass ofKClass

lemma measurableSet_pairingDomain (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) :
    MeasurableSet (pairingDomain beta) := by
{
  have hmap : Measurable (fun q : KClass × H => (ofKClass q.1, q.2)) :=
    ((continuous_ofKClass.comp continuous_fst).prodMk continuous_snd).measurable
  have hJ : Measurable (fun q : KClass × H => J beta q.1 q.2) := by
  {
    have he : (fun q : KClass × H => J beta q.1 q.2) =
        (fun p : DiskClass × H => J beta (toKClass p.1) p.2) ∘ (fun q : KClass × H => (ofKClass q.1, q.2)) :=
      funext (fun q => (G_J_congr_ofKClass beta q.1 q.2.2).2)
    rw [he]
    exact (continuous_diskClass_J beta).measurable.comp hmap
  }
  have hG : Measurable (fun q : KClass × H => (q.1, G beta q.1 q.2)) := by
  {
    refine measurable_fst.prodMk ?_
    have he : (fun q : KClass × H => G beta q.1 q.2) =
        (fun p : DiskClass × H => G beta (toKClass p.1) p.2) ∘ (fun q : KClass × H => (ofKClass q.1, q.2)) :=
      funext (fun q => (G_J_congr_ofKClass beta q.1 q.2.2).1)
    rw [he]
    exact (continuous_diskClass_G beta).measurable.comp hmap
  }
  have hgp := (lemma_5_4_good_pairs h_rho beta h_beta).1.preimage hG
  exact (measurableSet_lt measurable_const hJ).inter hgp
}

lemma R_pair_eq_of_classRanks {beta : ℝ} (h_beta : beta > 1) (q r : DiskClass × H)
    (hg : is_good_pair beta (toKClass q.1) (G beta (toKClass q.1) q.2))
    (he : jointCriticalMap beta r = jointCriticalMap beta q)
    (hJ : J beta (toKClass r.1) r.2 < 0)
    (hr : classRankCount beta (-1) r = classRankCount beta 1 q) :
    R_pair beta (toKClass q.1) q.2 = r.2 := by
{
  rcases q with ⟨g, z⟩
  rcases r with ⟨h, w⟩
  have hp : h = g := congrArg Prod.fst he
  subst h
  have hG : G beta (toKClass g) w = G beta (toKClass g) z := congrArg Prod.snd he
  have hgw : is_good_pair beta (toKClass g) (G beta (toKClass g) w) := hG ▸ hg
  rw [classRankCount_eq_heightRank h_beta (-1) (g, w) hgw,
    classRankCount_eq_heightRank h_beta 1 (g, z) hg, signedFiber_neg_one, signedFiber_one, hG] at hr
  have heq : heightRank (criticalHeight beta (toKClass g))
      (negativeFiber beta (toKClass g) (G beta (toKClass g) z)) w =
      heightRank (criticalHeight beta (toKClass g))
      (positiveFiber beta (toKClass g) (G beta (toKClass g) z)) z := by
    exact_mod_cast hr
  exact rankPartner_eq (criticalHeight_rank_inj beta h_beta (toKClass g) _ hg).2
    ⟨w.2, hG, hJ⟩ heq
}

lemma measurable_R_pair_diskClass {beta : ℝ} (h_beta : beta > 1) :
    Measurable (fun q : pairingDomainDisk beta => R_pair beta (toKClass q.val.1) q.val.2) := by
{
  let B := Classical.choice (exists_class_branches beta)
  let y : pairingDomainDisk beta → DiskClass × ℂ := fun q => jointCriticalMap beta q.val
  let b : ℕ → pairingDomainDisk beta → DiskClass × H := fun n q => B.branch n (y q)
  let M : ℕ → Set (pairingDomainDisk beta) := fun n => {q | y q ∈ jointCriticalMap beta '' B.part n ∧
    J beta (toKClass (b n q).1) (b n q).2 < 0 ∧
    classRankCount beta (-1) (b n q) = classRankCount beta 1 q.val}
  have hym : Measurable y := (continuous_jointCriticalMap beta).measurable.comp measurable_subtype_coe
  have hbm (n) : Measurable (b n) := (B.measurable_branch n).comp hym
  apply measurable_branch_selection (b := fun n q => (b n q).2.val) (M := M)
  · intro n
    exact measurable_subtype_coe.comp ((hbm n).snd)
  · intro n
    exact ((B.measurable_image n).preimage hym).inter
      ((measurableSet_lt ((continuous_diskClass_J beta).measurable.comp (hbm n)) measurable_const).inter
        (measurableSet_eq_fun ((measurable_classRankCount beta (-1)).comp (hbm n))
          ((measurable_classRankCount beta 1).comp measurable_subtype_coe)))
  · intro q
    obtain ⟨w, hw, _, hr⟩ := exists_critical_equalRank beta h_beta (toKClass q.val.1) _ q.2.2
      ⟨q.val.2.2, rfl, q.2.1⟩
    let r : DiskClass × H := (q.val.1, ⟨w, hw.1⟩)
    have hG : jointCriticalMap beta r = y q := Prod.ext rfl hw.2.1
    have hns : r ∈ nonsingularClass beta := ne_of_lt hw.2.2
    obtain ⟨n, hn⟩ := mem_iUnion.mp (B.cover.symm ▸ hns)
    have hb : b n q = r := by
    {
      dsimp [b]
      rw [← hG]
      exact B.left_inv n r hn
    }
    refine ⟨n, ⟨⟨r, hn, hG⟩, ?_, ?_⟩⟩
    · simpa only [hb] using hw.2.2
    · rw [hb, classRankCount_eq_heightRank h_beta (-1) r (by simpa only [r, hw.2.1] using q.2.2),
        classRankCount_eq_heightRank h_beta 1 q.val q.2.2, signedFiber_neg_one, signedFiber_one]
      simpa only [r, hw.2.1] using congrArg (fun n : ℕ => (n : ℝ≥0∞)) hr
  · intro n q hq
    exact R_pair_eq_of_classRanks h_beta q.val (b n q) q.2.2
      (B.right_inv n (y q) hq.1).2 hq.2.1 hq.2.2
}

lemma measurable_R_pair {beta : ℝ} (h_beta : beta > 1) :
    Measurable (fun q : pairingDomain beta => R_pair beta q.val.1 q.val.2) := by
{
  let phi : pairingDomain beta → pairingDomainDisk beta := fun q =>
    ⟨(ofKClass q.val.1, q.val.2), by
      have heq := (toKClass_ofKClass_eqOn q.val.1).symm
      refine ⟨?_, ?_⟩
      · rw [← (G_J_congr_eqOn beta heq q.val.2.2).2]
        exact q.2.1
      · rw [← (G_J_congr_eqOn beta heq q.val.2.2).1]
        exact (is_good_pair_congr_eqOn beta heq _).mp q.2.2⟩
  have hphi : Measurable phi :=
    ((continuous_ofKClass.comp (continuous_fst.comp continuous_subtype_val)).prodMk
      (continuous_snd.comp continuous_subtype_val)).measurable.subtype_mk
  have heq : (fun q : pairingDomain beta => R_pair beta q.val.1 q.val.2) =
      (fun r : pairingDomainDisk beta => R_pair beta (toKClass r.val.1) r.val.2) ∘ phi := by
  {
    funext q
    exact R_pair_congr_eqOn beta h_beta (toKClass_ofKClass_eqOn q.val.1).symm
      q.val.2.2 q.2.1 q.2.2
  }
  rw [heq]
  exact (measurable_R_pair_diskClass h_beta).comp hphi
}

/-!
## Part 3: Area Transport Formula (`weighted_area_formula_regular` and `transport_area`)
-/

lemma exists_countable_injective_partition {f : ℂ → ℂ} {s : Set ℂ}
    (hs : MeasurableSet s) (hf : ∀ z ∈ s, ContDiffAt ℝ 1 f z)
    (hreg : ∀ z ∈ s, LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0) :
    ∃ p : ℕ → Set ℂ, (∀ n, MeasurableSet (p n)) ∧
      Pairwise (Disjoint on p) ∧ (⋃ n, p n) = s ∧ ∀ n, InjOn f (p n) := by
{
  have hlocal (z : s) : ∃ U : Set ℂ, IsOpen U ∧ (z : ℂ) ∈ U ∧ InjOn f U := by
  {
    let e : ℂ ≃L[ℝ] ℂ :=
      (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr (hreg z z.2))).toContinuousLinearEquiv
    have he : (e : ℂ →L[ℝ] ℂ) = fderiv ℝ f z := by
    {
      ext v
      exact LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr (hreg z z.2)) v
    }
    have hd := (hf z z.2).hasStrictFDerivAt (by norm_num)
    rw [← he] at hd
    let e' := hd.toOpenPartialHomeomorph f
    exact ⟨e'.source, e'.open_source, hd.mem_toOpenPartialHomeomorph_source, e'.injOn⟩
  }
  choose U hUo hUz hUi using hlocal
  by_cases he : s = ∅
  · subst s
    exact ⟨fun _ => ∅, by simp, by simp [Pairwise], by simp, by simp⟩
  · have : Nonempty s := Set.nonempty_coe_sort.mpr (Set.nonempty_iff_ne_empty.mpr he)
    obtain ⟨j, hj⟩ := (HereditarilyLindelofSpace.isLindelof s).indexed_countable_subcover
      U hUo (fun z hz => mem_iUnion.mpr ⟨⟨z, hz⟩, hUz ⟨z, hz⟩⟩)
    let q : ℕ → Set ℂ := fun n => s ∩ U (j n)
    refine ⟨disjointed q, ?_, disjoint_disjointed q, ?_, ?_⟩
    · intro n
      exact MeasurableSet.disjointed (fun n => hs.inter (hUo (j n)).measurableSet) n
    · rw [iUnion_disjointed]
      ext z
      simp only [mem_iUnion, mem_inter_iff, q]
      exact ⟨fun ⟨_, hz, _⟩ => hz, fun hz => by obtain ⟨n, hn⟩ := mem_iUnion.mp (hj hz); exact ⟨n, hz, hn⟩⟩
    · intro n
      exact (hUi (j n)).mono ((disjointed_subset q n).trans inter_subset_right)
}

def fiberSum {X Y : Type*} (f : X → Y) (s : Set X) (u : X → ℝ≥0∞) (y : Y) : ℝ≥0∞ :=
  ∑' x : {x | x ∈ s ∧ f x = y}, u x

lemma BorelBranches.fiberSum_eq {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} {s : Set X} (B : BorelBranches f s) (u : X → ℝ≥0∞) (y : Y) :
    fiberSum f s u y = ∑' n, (f '' B.part n).indicator (fun y => u (B.branch n y)) y := by
{
  have he : {x | x ∈ s ∧ f x = y} = ⋃ n, {x | x ∈ B.part n ∧ f x = y} := by
  {
    ext x
    simp only [mem_setOf_eq]
    rw [show x ∈ s ↔ x ∈ ⋃ n, B.part n from by rw [B.cover]]
    simp only [mem_iUnion]
    aesop
  }
  rw [fiberSum, he, ENNReal.tsum_biUnion]
  · apply tsum_congr
    intro n
    by_cases hy : y ∈ f '' B.part n
    · have hx : {x | x ∈ B.part n ∧ f x = y} = {B.branch n y} := by
      {
        ext x
        constructor
        · intro hx
          exact mem_singleton_iff.mpr (B.injective n hx.1 (B.right_inv n y hy).1
            (hx.2.trans (B.right_inv n y hy).2.symm))
        · rintro rfl
          exact B.right_inv n y hy
      }
      rw [hx, tsum_singleton, indicator_of_mem hy]
    · rw [indicator_of_notMem hy, ENNReal.tsum_eq_zero]
      rintro ⟨x, hx⟩
      exact False.elim (hy ⟨x, hx.1, hx.2⟩)
  · intro n _ m _ hnm
    exact (B.disjoint hnm).mono (fun _ h => h.1) (fun _ h => h.1)
}

lemma BorelBranches.measurable_fiberSum {X Y : Type*} [MeasurableSpace X] [MeasurableSpace Y]
    {f : X → Y} {s : Set X} (B : BorelBranches f s) {u : X → ℝ≥0∞} (hu : Measurable u) :
    Measurable (fiberSum f s u) := by
{
  have he := funext (B.fiberSum_eq u)
  rw [he]
  exact Measurable.tsum (fun n => (hu.comp (B.measurable_branch n)).indicator (B.measurable_image n))
}

lemma weighted_area_formula_regular {f : ℂ → ℂ} {s : Set ℂ}
    (hs : MeasurableSet s) (hf : ∀ z ∈ s, ContDiffAt ℝ 1 f z)
    (hreg : ∀ z ∈ s, LinearMap.det (fderiv ℝ f z).toLinearMap ≠ 0)
    {u : ℂ → ℝ≥0∞} (hu : Measurable u) :
    Measurable (fiberSum f s u) ∧
    (∫⁻ z in s, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| * u z) =
      ∫⁻ y, fiberSum f s u y := by
{
  let B := Classical.choice (exists_borelBranches
    (fun z hz => (hf z hz).continuousAt.continuousWithinAt)
    (exists_countable_injective_partition hs hf hreg))
  have hsub (n : ℕ) : B.part n ⊆ s := fun z hz => by rw [← B.cover]; exact mem_iUnion.mpr ⟨n, hz⟩
  have hder (n : ℕ) (z : ℂ) (hz : z ∈ B.part n) :
      HasFDerivWithinAt f (fderiv ℝ f z) (B.part n) z :=
    ((hf z (hsub n hz)).differentiableAt (by norm_num)).hasFDerivAt.hasFDerivWithinAt
  refine ⟨B.measurable_fiberSum hu, ?_⟩
  calc
    (∫⁻ z in s, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| * u z) =
        ∑' n, ∫⁻ z in B.part n, ENNReal.ofReal |LinearMap.det (fderiv ℝ f z).toLinearMap| * u z := by
    {
      conv_lhs => rw [← B.cover]
      exact lintegral_iUnion B.measurable_part B.disjoint _
    }
    _ = ∑' n, ∫⁻ y in f '' B.part n, u (B.branch n y) := by
    {
      apply tsum_congr
      intro n
      rw [lintegral_image_eq_lintegral_abs_det_fderiv_mul volume (B.measurable_part n) (hder n) (B.injective n)]
      apply setLIntegral_congr_fun (B.measurable_part n)
      intro z hz
      dsimp only
      rw [B.left_inv n z hz]
    }
    _ = ∫⁻ y, fiberSum f s u y := by
    {
      rw [funext (B.fiberSum_eq u), lintegral_tsum]
      · exact tsum_congr (fun n => (lintegral_indicator (B.measurable_image n) _).symm)
      · exact fun n => ((hu.comp (B.measurable_branch n)).indicator (B.measurable_image n)).aemeasurable
    }
}

lemma fiberSum_mono_injective {X Y : Type*} {f : X → Y} {s t : Set X} {u v : X → ℝ≥0∞}
    (R : X → X) (y : Y)
    (hR : ∀ x ∈ s, f x = y → R x ∈ t ∧ f (R x) = y)
    (hinj : InjOn R {x | x ∈ s ∧ f x = y})
    (hle : ∀ x ∈ s, f x = y → u x ≤ v (R x)) :
    fiberSum f s u y ≤ fiberSum f t v y := by
{
  let e : {x | x ∈ s ∧ f x = y} → {x | x ∈ t ∧ f x = y} := fun x =>
    ⟨R x, hR x x.property.1 x.property.2⟩
  have hi : Injective e := fun a b h => Subtype.ext
    (hinj a.property b.property (congrArg Subtype.val h))
  exact ENNReal.summable.tsum_le_tsum_of_inj e hi (fun _ _ => zero_le)
    (fun x => hle x x.property.1 x.property.2) ENNReal.summable
}

lemma contDiffAt_G (beta : ℝ) (F : KClass) {z : ℂ} (hz : z ∈ H) :
    ContDiffAt ℝ 1 (G beta F) z := by
{
  have han : AnalyticAt ℂ F.F z := F.univalent.1.analyticOnNhd isOpen_H z hz
  have hc : ContDiffAt ℝ 1 (fun w : ℂ => (w.im : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z Complex.imCLM.contDiff.contDiffAt
  exact (han.contDiffAt.restrict_scalars ℝ).sub
    ((contDiffAt_const.mul hc).mul (han.deriv.contDiffAt.restrict_scalars ℝ))
}

lemma measurableSet_H_pred (P : ℂ → Prop)
    (hP : MeasurableSet {z : H | P z}) :
    MeasurableSet {z : ℂ | z ∈ H ∧ P z} := by
{
  have h := isOpen_H.measurableSet.subtype_image hP
  convert h using 1
  ext z
  simp only [mem_setOf_eq, mem_image, Subtype.exists, exists_prop]
  aesop
}

def jacobianRegion (beta : ℝ) (F : KClass) (σ : ℝ) : Set ℂ :=
  {z | z ∈ H ∧ 0 < σ * J beta F z}

lemma continuous_J_H (beta : ℝ) (F : KClass) :
    Continuous (fun z : H => J beta F z) := by
{
  have he : (fun z : H => J beta F z) =
      (fun p : DiskClass × H => J beta (toKClass p.1) p.2) ∘ (fun z : H => (ofKClass F, z)) :=
    funext (fun z => (G_J_congr_ofKClass beta F z.2).2)
  rw [he]
  exact (continuous_diskClass_J beta).comp (continuous_const.prodMk continuous_id)
}

lemma continuous_G_H (beta : ℝ) (F : KClass) :
    Continuous (fun z : H => G beta F z) := by
{
  have he : (fun z : H => G beta F z) =
      (fun p : DiskClass × H => G beta (toKClass p.1) p.2) ∘ (fun z : H => (ofKClass F, z)) :=
    funext (fun z => (G_J_congr_ofKClass beta F z.2).1)
  rw [he]
  exact (continuous_diskClass_G beta).comp (continuous_const.prodMk continuous_id)
}

lemma measurableSet_jacobianRegion (beta : ℝ) (F : KClass) (σ : ℝ) :
    MeasurableSet (jacobianRegion beta F σ) := by
{
  apply measurableSet_H_pred
  exact measurableSet_lt measurable_const (measurable_const.mul (continuous_J_H beta F).measurable)
}

lemma jacobianRegion_regular (beta : ℝ) (F : KClass) (σ : ℝ) {z : ℂ}
    (hz : z ∈ jacobianRegion beta F σ) :
    LinearMap.det (fderiv ℝ (G beta F) z).toLinearMap ≠ 0 := by
{
  intro hzero
  have hdet : ((fderiv ℝ (G beta F) z 1).re * (fderiv ℝ (G beta F) z I).im -
      (fderiv ℝ (G beta F) z I).re * (fderiv ℝ (G beta F) z 1).im) =
      LinearMap.det (fderiv ℝ (G beta F) z).toLinearMap :=
    (determinant_complex_real (fderiv ℝ (G beta F) z).toLinearMap).symm
  have h := hz.2
  rw [J, hdet, hzero, zero_div, mul_zero] at h
  exact lt_irrefl 0 h
}

def transportDensity (beta : ℝ) (F : KClass) (z : ℂ) : ℝ≥0∞ :=
  ENNReal.ofReal (z.im ^ (beta - 1) * ‖Q F.F z‖^2)

def targetDensity (beta : ℝ) (F : KClass) : ℂ → ℝ≥0∞ :=
  H.indicator (fun z => ENNReal.ofReal (z.im ^ (beta - 1) * ‖Q F.F z‖^4))

lemma measurable_targetDensity (beta : ℝ) (F : KClass) :
    Measurable (targetDensity beta F) := by
{
  have hc : ContinuousOn (fun z : ℂ => ENNReal.ofReal (z.im ^ (beta - 1) * ‖Q F.F z‖^4)) H := by
  {
    apply continuousOn_iff_continuous_restrict.mpr
    have hp : Continuous (fun z : H => z.val.im ^ (beta - 1)) :=
      (Complex.continuous_im.comp continuous_subtype_val).rpow_const
        (fun z => Or.inl (ne_of_gt z.2))
    have hq : Continuous (fun z : H => ‖Q F.F z‖^4) :=
      ((differentiableOn_KClass_Q F).continuousOn.restrict.norm).pow 4
    exact ENNReal.continuous_ofReal.comp (hp.mul hq)
  }
  exact hc.measurable_piecewise continuousOn_const isOpen_H.measurableSet
}

lemma transportDensity_jacobian (beta σ : ℝ) (F : KClass) (hσ : |σ| = 1)
    {z : ℂ} (hz : z ∈ jacobianRegion beta F σ) :
    transportDensity beta F z * ENNReal.ofReal (σ * J beta F z) =
      ENNReal.ofReal |LinearMap.det (fderiv ℝ (G beta F) z).toLinearMap| * targetDensity beta F z := by
{
  have hD : 0 < ‖deriv F.F z‖ := norm_pos_iff.mpr
    (deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz.1)
  have habs : |J beta F z| = σ * J beta F z := by
  {
    rw [← one_mul |J beta F z|, ← hσ, ← abs_mul, abs_of_pos hz.2]
  }
  have hdet_eq : ((fderiv ℝ (G beta F) z 1).re * (fderiv ℝ (G beta F) z I).im -
      (fderiv ℝ (G beta F) z I).re * (fderiv ℝ (G beta F) z 1).im) =
      LinearMap.det (fderiv ℝ (G beta F) z).toLinearMap :=
    (determinant_complex_real (fderiv ℝ (G beta F) z).toLinearMap).symm
  have hdet : |LinearMap.det (fderiv ℝ (G beta F) z).toLinearMap| =
      ‖deriv F.F z‖^2 * (σ * J beta F z) := by
  {
    rw [← habs, J, hdet_eq, abs_div, abs_pow, abs_norm]
    field_simp
  }
  rw [transportDensity, targetDensity, indicator_of_mem hz.1, hdet]
  simp only [Q, one_div, norm_inv]
  rw [← ENNReal.ofReal_mul (mul_nonneg (Real.rpow_nonneg hz.1.le _) (sq_nonneg _)),
    ← ENNReal.ofReal_mul (mul_nonneg (sq_nonneg _) hz.2.le)]
  congr 1
  field_simp
}

lemma transport_area (beta σ : ℝ) (F : KClass) (hσ : |σ| = 1)
    {h : ℂ → ℝ≥0∞} (hm : Measurable h) :
    (∫⁻ z in H, transportDensity beta F z * ENNReal.ofReal (σ * J beta F z) * h z) =
    ∫⁻ xi, fiberSum (G beta F) (jacobianRegion beta F σ)
      (fun z => targetDensity beta F z * h z) xi := by
{
  have hs := measurableSet_jacobianRegion beta F σ
  have he := (weighted_area_formula_regular hs
    (fun z hz => contDiffAt_G beta F hz.1)
    (fun z hz => jacobianRegion_regular beta F σ hz)
    ((measurable_targetDensity beta F).mul hm)).2
  refine Eq.trans ?_ he
  have hzero : (fun z => transportDensity beta F z * ENNReal.ofReal (σ * J beta F z) * h z) =ᶠ[ae (volume.restrict H)]
      (jacobianRegion beta F σ).indicator (fun z => transportDensity beta F z *
        ENNReal.ofReal (σ * J beta F z) * h z) := by
  {
    filter_upwards [ae_restrict_mem isOpen_H.measurableSet] with z hz
    by_cases hj : 0 < σ * J beta F z
    · rw [indicator_of_mem (show z ∈ jacobianRegion beta F σ from ⟨hz, hj⟩)]
    · rw [indicator_of_notMem (show z ∉ jacobianRegion beta F σ from fun h => hj h.2),
        ENNReal.ofReal_eq_zero.mpr (le_of_not_gt hj), mul_zero, zero_mul]
  }
  rw [lintegral_congr_ae hzero, lintegral_indicator hs, Measure.restrict_restrict hs]
  have hinter : jacobianRegion beta F σ ∩ H = jacobianRegion beta F σ :=
    inter_eq_left.mpr (fun z hz => hz.1)
  rw [hinter]
  apply setLIntegral_congr_fun hs
  intro z hz
  dsimp only
  rw [transportDensity_jacobian beta σ F hσ hz, mul_assoc]
}

lemma targetDensity_eq_height (beta : ℝ) (hk : 0 < k_val beta) (F : KClass)
    {z : ℂ} (hz : z ∈ H) :
    targetDensity beta F z = ENNReal.ofReal ((criticalHeight beta F z / k_val beta) ^ 4) := by
{
  have hb : beta - 1 = (k_val beta - 1) * 4 := by unfold k_val; ring
  rw [targetDensity, indicator_of_mem hz, criticalHeight, hb, Real.rpow_mul hz.le]
  congr 1
  simp only [Real.rpow_ofNat]
  field_simp
}

lemma targetDensity_le_pair {beta : ℝ} (h_beta : beta > 1) (F : KClass)
    {z : ℂ} (hz : z ∈ H) (hJ : 0 < J beta F z)
    (hg : is_good_pair beta F (G beta F z)) :
    targetDensity beta F z ≤ targetDensity beta F (R_pair beta F z) := by
{
  have hk : 0 < k_val beta := by unfold k_val; linarith
  have hs := R_pair_spec_height beta h_beta F hz hJ hg
  rw [targetDensity_eq_height beta hk F hz, targetDensity_eq_height beta hk F hs.1]
  apply ENNReal.ofReal_le_ofReal
  gcongr
  · exact div_nonneg (criticalHeight_pos beta hk F hz).le hk.le
  · exact hs.2.2
}

/-!
## Part 4: Transport Boxes (`transport_box` and `exceptional_transport_zero`)
-/

def displacementWindow (N : ℝ) (z w : ℂ) : Prop :=
  z.im ≤ N * w.im ∧ w.im ≤ N * z.im ∧ |w.re - z.re| ≤ N * z.im

def transportWindow (beta N : ℝ) : Set (KClass × H) :=
  {q | q ∈ pairingDomain beta ∧ displacementWindow N q.2 (R_pair beta q.1 q.2)}

lemma measurableSet_transportWindow (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) (N : ℝ) :
    MeasurableSet (transportWindow beta N) := by
{
  have h_beta_gt : beta > 1 := by
  {
    rw [h_beta]
    exact (one_lt_div (Real.log_pos (by norm_num))).mpr (Real.log_lt_log (by norm_num) h_rho)
  }
  have hr := measurable_R_pair h_beta_gt
  have hz : Measurable (fun q : pairingDomain beta => (q.val.2 : ℂ)) :=
    measurable_subtype_coe.comp (measurable_subtype_coe.snd)
  have hm : MeasurableSet {q : pairingDomain beta |
      displacementWindow N q.val.2 (R_pair beta q.val.1 q.val.2)} :=
    (measurableSet_le (Complex.measurable_im.comp hz)
      (measurable_const.mul (Complex.measurable_im.comp hr))).inter
    ((measurableSet_le (Complex.measurable_im.comp hr)
      (measurable_const.mul (Complex.measurable_im.comp hz))).inter
    (measurableSet_le (((Complex.measurable_re.comp hr).sub (Complex.measurable_re.comp hz)).abs)
      (measurable_const.mul (Complex.measurable_im.comp hz))))
  have h := (measurableSet_pairingDomain h_rho beta h_beta).subtype_image hm
  convert h using 1
  ext q
  simp only [transportWindow, mem_setOf_eq, mem_image, Subtype.exists, exists_prop]
  aesop
}

lemma displacementWindow_affine (N : ℝ) {t : ℂ} (ht : t ∈ H) (z w : ℂ) :
    displacementWindow N (aff t z) (aff t w) ↔ displacementWindow N z w := by
{
  have him (v : ℂ) : (aff t v).im = t.im * v.im := by simp [aff]
  have hre : (aff t w).re - (aff t z).re = t.im * (w.re - z.re) := by simp [aff]; ring
  simp only [displacementWindow, him, hre, abs_mul, abs_of_pos (show 0 < t.im from ht)]
  simp only [show N * (t.im * w.im) = t.im * (N * w.im) from by ring,
    show N * (t.im * z.im) = t.im * (N * z.im) from by ring,
    mul_le_mul_iff_right₀ (show 0 < t.im from ht)]
}

lemma transportWindow_root {beta : ℝ} (h_beta : beta > 1) (N : ℝ) (F : KClass) (z : H) :
    (T_elem F z.1 z.2, ⟨I, by dsimp [H]; simp⟩) ∈ transportWindow beta N ↔
      (F, z) ∈ transportWindow beta N := by
{
  have hk : 0 < k_val beta := by unfold k_val; linarith
  have hJ := J_T_elem_root beta hk.ne' F z.2
  have hG := is_good_pair_T_elem_root beta hk F z.2
  change (0 < J beta (T_elem F z.1 z.2) I ∧
    is_good_pair beta (T_elem F z.1 z.2) (G beta (T_elem F z.1 z.2) I)) ∧ _ ↔
    (0 < J beta F z ∧ is_good_pair beta F (G beta F z)) ∧ _
  rw [hJ, hG]
  apply and_congr_right
  intro h
  have he := R_pair_T_elem_root beta h_beta F z.2 h.1 h.2
  change displacementWindow N I (R_pair beta (T_elem F z.1 z.2) I) ↔
    displacementWindow N z (R_pair beta F z)
  rw [← displacementWindow_affine N z.2 I, aff_I, he]
}

lemma displacementWindow_mono {N M : ℝ} (hNM : N ≤ M) {z w : ℂ}
    (hz : z ∈ H) (hw : w ∈ H) (h : displacementWindow N z w) :
    displacementWindow M z w := by
{
  exact ⟨h.1.trans (mul_le_mul_of_nonneg_right hNM hw.le),
    h.2.1.trans (mul_le_mul_of_nonneg_right hNM hz.le),
    h.2.2.trans (mul_le_mul_of_nonneg_right hNM hz.le)⟩
}

lemma exists_displacementWindow {z w : ℂ} (hz : z ∈ H) (hw : w ∈ H) :
    ∃ n : ℕ, displacementWindow (n + 1) z w := by
{
  obtain ⟨n, hn⟩ := exists_nat_gt (max (z.im / w.im) (max (w.im / z.im) (|w.re - z.re| / z.im)))
  refine ⟨n, ?_, ?_, ?_⟩
  · exact (div_le_iff₀ hw).mp ((le_max_left _ _).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))
  · exact (div_le_iff₀ hz).mp (((le_max_left _ _).trans (le_max_right _ _)).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))
  · exact (div_le_iff₀ hz).mp (((le_max_right _ _).trans (le_max_right _ _)).trans (by exact_mod_cast hn.le.trans (le_add_of_nonneg_right zero_le_one)))
}

lemma transportWindow_mono {beta : ℝ} (h_beta : beta > 1) {N M : ℝ} (hNM : N ≤ M) :
    transportWindow beta N ⊆ transportWindow beta M := by
{
  rintro ⟨F, z⟩ ⟨hp, hw⟩
  exact ⟨hp, displacementWindow_mono hNM z.2
    (R_pair_spec_height beta h_beta F z.2 hp.1 hp.2).1 hw⟩
}

lemma iUnion_transportWindow {beta : ℝ} (h_beta : beta > 1) :
    (⋃ n : ℕ, transportWindow beta (n + 1)) = pairingDomain beta := by
{
  ext q
  constructor
  · rintro ⟨_, ⟨n, rfl⟩, hq⟩
    exact hq.1
  · intro hq
    obtain ⟨n, hn⟩ := exists_displacementWindow q.2.2
      (R_pair_spec_height beta h_beta q.1 q.2.2 hq.1 hq.2).1
    exact mem_iUnion.mpr ⟨n, hq, hn⟩
}

def transportSlice (beta N : ℝ) (F : KClass) : Set ℂ :=
  {z | z ∈ H ∧ 0 < J beta F z ∧
    is_good_pair beta F (G beta F z) ∧
    displacementWindow N z (R_pair beta F z)}

lemma transportSlice_iff (beta N : ℝ) (F : KClass) (z : H) :
    z.val ∈ transportSlice beta N F ↔ (F, z) ∈ transportWindow beta N := by
{
  simp only [transportSlice, transportWindow, pairingDomain, mem_setOf_eq, z.2, true_and, and_assoc]
}

lemma measurableSet_transportSlice (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) (N : ℝ) (F : KClass) :
    MeasurableSet (transportSlice beta N F) := by
{
  apply measurableSet_H_pred
  have hm : Measurable (fun z : H => (F, z)) := measurable_const.prodMk measurable_id
  have h := (measurableSet_transportWindow h_rho beta h_beta N).preimage hm
  convert h using 1
  ext z
  exact and_assoc.symm
}

def transportBox (R a b : ℝ) : Set ℂ := {z | |z.re| ≤ R ∧ a ≤ z.im ∧ z.im ≤ b}

lemma measurableSet_transportBox (R a b : ℝ) : MeasurableSet (transportBox R a b) := by
{
  exact (measurableSet_le Complex.measurable_re.abs measurable_const).inter
    ((measurableSet_le measurable_const Complex.measurable_im).inter
      (measurableSet_le Complex.measurable_im measurable_const))
}

lemma pair_mem_enlargedBox {N R Y : ℝ} (hN : 1 ≤ N) {z w : ℂ}
    (hz : z ∈ transportBox R 1 Y) (hw : displacementWindow N z w) :
    w ∈ transportBox (R + N * Y) (1 / N) (N * Y) := by
{
  have hn : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hab : |w.re| ≤ |z.re| + |w.re - z.re| := by
  {
    calc |w.re| = |z.re + (w.re - z.re)| := by congr 1; ring
         _ ≤ |z.re| + |w.re - z.re| := abs_add_le _ _
  }
  refine ⟨hab.trans (add_le_add hz.1 (hw.2.2.trans (mul_le_mul_of_nonneg_left hz.2.2 hn.le))), ?_,
    hw.2.1.trans (mul_le_mul_of_nonneg_left hz.2.2 hn.le)⟩
  rw [div_le_iff₀ hn]
  nlinarith [hw.1, hz.2.1]
}

lemma fiberSum_mul_indicator {X Y : Type*} (f : X → Y) (s t : Set X)
    (u : X → ℝ≥0∞) (y : Y) :
    fiberSum f s (fun x => u x * t.indicator 1 x) y = fiberSum f (s ∩ t) u y := by
{
  rw [fiberSum, fiberSum, tsum_subtype {x | x ∈ s ∧ f x = y} (fun x => u x * t.indicator 1 x),
    tsum_subtype {x | x ∈ s ∩ t ∧ f x = y} u]
  apply tsum_congr
  intro x
  by_cases hs : x ∈ s <;> by_cases ht : x ∈ t <;> by_cases hy : f x = y <;>
    simp [hs, ht, hy]
}

lemma transport_box (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) {N R Y : ℝ} (hN : 1 ≤ N) (F : KClass) :
    (∫⁻ z in H, transportDensity beta F z * ENNReal.ofReal (J beta F z) *
      (transportSlice beta N F ∩ transportBox R 1 Y).indicator 1 z) ≤
    ∫⁻ z in H, transportDensity beta F z * ENNReal.ofReal (-J beta F z) *
      (transportBox (R + N * Y) (1 / N) (N * Y)).indicator 1 z := by
{
  have h_beta_gt : beta > 1 := by
  {
    rw [h_beta]
    exact (one_lt_div (Real.log_pos (by norm_num))).mpr (Real.log_lt_log (by norm_num) h_rho)
  }
  let S := transportSlice beta N F ∩ transportBox R 1 Y
  let T := transportBox (R + N * Y) (1 / N) (N * Y)
  have hs : MeasurableSet S :=
    (measurableSet_transportSlice h_rho beta h_beta N F).inter (measurableSet_transportBox R 1 Y)
  have ht : MeasurableSet T := measurableSet_transportBox _ _ _
  have hp := transport_area beta 1 F (by norm_num) (measurable_const.indicator hs : Measurable (S.indicator (1 : ℂ → ℝ≥0∞)))
  have hn := transport_area beta (-1) F (by norm_num) (measurable_const.indicator ht : Measurable (T.indicator (1 : ℂ → ℝ≥0∞)))
  simp only [one_mul] at hp
  simp only [neg_one_mul] at hn
  apply le_trans hp.le
  apply le_trans ?_ hn.symm.le
  apply lintegral_mono
  intro xi
  apply le_trans (fiberSum_mul_indicator (G beta F) (jacobianRegion beta F 1) S (targetDensity beta F) xi).le
  apply le_trans ?_ (fiberSum_mul_indicator (G beta F) (jacobianRegion beta F (-1)) T (targetDensity beta F) xi).symm.le
  apply fiberSum_mono_injective (R_pair beta F) xi
  · intro z hz hG
    have hsz := hz.2.1
    have hpair := R_pair_spec_height beta h_beta_gt F hsz.1 hsz.2.1 hsz.2.2.1
    exact ⟨⟨⟨hpair.1, by simpa only [neg_one_mul] using neg_pos.mpr hpair.2.1.2⟩,
      pair_mem_enlargedBox hN hz.2.2 hsz.2.2.2⟩, hpair.2.1.1.trans hG⟩
  · apply (R_pair_injective beta h_beta_gt F).mono
    intro z hz
    exact ⟨hz.1.2.1.1, hz.1.2.1.2.1, hz.1.2.1.2.2.1⟩
  · intro z hz _
    exact targetDensity_le_pair h_beta_gt F hz.2.1.1 hz.2.1.2.1 hz.2.1.2.2.1
}

lemma measurableSet_exceptionSlice (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) (F : KClass) :
    MeasurableSet {z : ℂ | z ∈ H ∧ ¬is_good_pair beta F (G beta F z)} := by
{
  apply measurableSet_H_pred
  have hm : Measurable (fun z : H => (F, G beta F z)) :=
    measurable_const.prodMk (continuous_G_H beta F).measurable
  exact (((lemma_5_4_good_pairs h_rho beta h_beta).1.preimage hm).compl)
}

lemma exceptional_transport_zero (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) (F : KClass)
    (hg : ∀ᵐ xi : ℂ, is_good_pair beta F xi) :
    (∫⁻ z in H, transportDensity beta F z * ENNReal.ofReal (J beta F z) *
      {z : ℂ | z ∈ H ∧ ¬is_good_pair beta F (G beta F z)}.indicator 1 z) = 0 := by
{
  have hs := measurableSet_exceptionSlice h_rho beta h_beta F
  have he := transport_area beta 1 F (by norm_num)
    (measurable_const.indicator hs : Measurable ({z : ℂ | z ∈ H ∧ ¬is_good_pair beta F (G beta F z)}.indicator (1 : ℂ → ℝ≥0∞)))
  simp only [one_mul] at he
  refine he.trans ?_
  apply lintegral_eq_zero_of_ae_eq_zero
  filter_upwards [hg] with xi hxi
  unfold fiberSum
  apply ENNReal.tsum_eq_zero.mpr
  intro z
  have hn : z.val ∉ {z : ℂ | z ∈ H ∧ ¬is_good_pair beta F (G beta F z)} := by
  {
    rintro ⟨_, hbad⟩
    exact hbad (z.property.2.symm ▸ hxi)
  }
  exact (congrArg (targetDensity beta F z * ·) (indicator_of_notMem (f := (1 : ℂ → ℝ≥0∞)) hn)).trans (mul_zero _)
}

/-!
## Part 5: Expected Density and Expected Transport (`E_J_nonpositive_proof`)
-/

def halfRetract (z : ℂ) : H := if h : z ∈ H then ⟨z, h⟩ else ⟨I, by dsimp [H]; simp⟩

lemma halfRetract_of_mem {z : ℂ} (hz : z ∈ H) : halfRetract z = ⟨z, hz⟩ := by
{
  simp only [halfRetract, dif_pos hz]
}

lemma measurable_halfRetract : Measurable halfRetract := by
{
  have hm : Measurable (fun z : ℂ => (halfRetract z : ℂ)) := by
  {
    have he : (fun z : ℂ => (halfRetract z : ℂ)) = (fun z => if z ∈ H then z else I) := by
    {
      funext z
      by_cases hz : z ∈ H <;> simp [halfRetract, hz]
    }
    rw [he]
    exact measurable_id.piecewise isOpen_H.measurableSet measurable_const
  }
  exact hm.subtype_mk
}

lemma continuous_A_weight_joint :
    Continuous (fun p : KClass × H => A_weight p.2.1 p.1.F) := by
{
  have he : (fun p : KClass × H => A_weight p.2.1 p.1.F) =
      (fun q : DiskClass × H => diskWeight q.1 q.2) ∘ (fun p : KClass × H => (ofKClass p.1, p.2)) :=
    funext (fun p => A_weight_ofKClass p.1 p.2)
  rw [he]
  exact continuous_diskWeight.comp ((continuous_ofKClass.comp continuous_fst).prodMk continuous_snd)
}

lemma continuous_T_elem_joint :
    Continuous (fun p : KClass × H => T_elem p.1 p.2.1 p.2.2) := by
{
  rw [continuous_induced_rng]
  have he : ofKClass ∘ (fun p : KClass × H => T_elem p.1 p.2.1 p.2.2) =
      (fun q : DiskClass × H => rerootDisk q.1 q.2) ∘ (fun p : KClass × H => (ofKClass p.1, p.2)) :=
    funext (fun p => ofKClass_T_elem p.1 p.2)
  rw [he]
  exact continuous_rerootDisk.comp ((continuous_ofKClass.comp continuous_fst).prodMk continuous_snd)
}

def averagedDensity (beta : ℝ) (Phi : KClass → ℝ≥0∞) (p : KClass × ℂ) : ℝ≥0∞ :=
  {p : KClass × ℂ | p.2 ∈ H}.indicator
    (fun p => ENNReal.ofReal (p.2.im ^ (beta - 1)) *
      ENNReal.ofReal (A_weight (halfRetract p.2).1 p.1.F) *
      Phi (T_elem p.1 (halfRetract p.2).1 (halfRetract p.2).2)) p

lemma measurable_averagedDensity (beta : ℝ) {Phi : KClass → ℝ≥0∞} (hPhi : Measurable Phi) :
    Measurable (averagedDensity beta Phi) := by
{
  have hm : Measurable (fun p : KClass × ℂ => (p.1, halfRetract p.2)) :=
    measurable_fst.prodMk (measurable_halfRetract.comp measurable_snd)
  exact ((((Complex.measurable_im.comp measurable_snd).pow_const (beta - 1)).ennreal_ofReal.mul
    (continuous_A_weight_joint.measurable.comp hm).ennreal_ofReal).mul
    (hPhi.comp (continuous_T_elem_joint.measurable.comp hm))).indicator
      (isOpen_H.measurableSet.preimage measurable_snd)
}

lemma averagedDensity_of_mem (beta : ℝ) (Phi : KClass → ℝ≥0∞) (F : KClass) (z : H) :
    averagedDensity beta Phi (F, z) = transportDensity beta F z * Phi (T_elem F z.1 z.2) := by
{
  rw [averagedDensity, indicator_of_mem (show (F, (z : ℂ)) ∈ {p : KClass × ℂ | p.2 ∈ H} from z.2)]
  simp only [halfRetract_of_mem z.2]
  rw [transportDensity, ENNReal.ofReal_mul (Real.rpow_nonneg z.2.le _)]
  simp only [A_weight]
}

lemma weighted_averagedDensity (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2)
    {Phi : KClass → ℝ≥0∞} (hPhi : Measurable Phi) (z : H) :
    (∫⁻ F, averagedDensity beta Phi (F, z) ∂P_eigenmeasure) =
      ENNReal.ofReal (z.1.im⁻¹) * ∫⁻ F, Phi F ∂P_eigenmeasure := by
{
  have hm : Measurable (fun F : KClass => ENNReal.ofReal (A_weight z.1 F.F) * Phi (T_elem F z.1 z.2)) :=
    (continuous_A_weight z.2).measurable.ennreal_ofReal.mul
      (hPhi.comp (continuous_T_elem z.2).measurable)
  have he : (fun F : KClass => averagedDensity beta Phi (F, z)) =
      fun F => ENNReal.ofReal (z.1.im ^ (beta - 1)) *
        (ENNReal.ofReal (A_weight z.1 F.F) * Phi (T_elem F z.1 z.2)) := by
  {
    funext F
    rw [averagedDensity, indicator_of_mem (show (F, (z : ℂ)) ∈ {p : KClass × ℂ | p.2 ∈ H} from z.2)]
    simp only [halfRetract_of_mem z.2, mul_assoc]
  }
  have hcov := (lemma_3_1_weighted_covariance_lintegral h_rho).2 z.1 z.2 Phi hPhi
  rw [he, lintegral_const_mul _ hm]
  change ENNReal.ofReal (z.1.im ^ (beta - 1)) *
    (∫⁻ F, ENNReal.ofReal (A_weight z.1 F.F) *
      Phi ⟨T z.1 F.F, (T_KClass F z.1 z.2).1, (T_KClass F z.1 z.2).2.1, (T_KClass F z.1 z.2).2.2⟩ ∂P_eigenmeasure) = _
  rw [hcov, ← h_beta, ← mul_assoc,
    ← ENNReal.ofReal_mul (Real.rpow_nonneg z.2.le _), ← Real.rpow_add z.2]
  congr 2
  rw [show beta - 1 + -beta = (-1 : ℝ) from by ring, Real.rpow_neg_one]
}

lemma root_test_zero_of_averaging (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2)
    {Phi : KClass → ℝ≥0∞} (hPhi : Measurable Phi)
    (hzero : ∀ᵐ F ∂P_eigenmeasure, (∫⁻ z in H, averagedDensity beta Phi (F, z)) = 0) :
    (∫⁻ F, Phi F ∂P_eigenmeasure) = 0 := by
{
  haveI : IsProbabilityMeasure P_eigenmeasure := (lemma_3_1_weighted_covariance h_rho).1
  have hm := measurable_averagedDensity beta hPhi
  have hz : (∫⁻ z in H, ∫⁻ F, averagedDensity beta Phi (F, z) ∂P_eigenmeasure) = 0 :=
    (lintegral_lintegral_swap (f := fun F z => averagedDensity beta Phi (F, z))
      (μ := P_eigenmeasure) (ν := volume.restrict H) hm.aemeasurable).symm.trans
      (lintegral_eq_zero_of_ae_eq_zero hzero)
  have ha := (lintegral_eq_zero_iff hm.lintegral_prod_left').mp hz
  have : (ae (volume.restrict H)).NeBot := ae_restrict_neBot.mpr
    (ne_of_gt (isOpen_H.measure_pos volume ⟨I, by dsimp [H]; simp⟩))
  obtain ⟨z, hz, hz0⟩ := ((ae_restrict_mem isOpen_H.measurableSet).and ha).exists
  have he := weighted_averagedDensity h_rho beta h_beta hPhi ⟨z, hz⟩
  change (∫⁻ F, averagedDensity beta Phi (F, z) ∂P_eigenmeasure) = 0 at hz0
  exact (mul_eq_zero.mp (he.symm.trans hz0)).resolve_left
    (ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hz)))
}

lemma lintegral_Icc_inv {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ y in Icc a b, ENNReal.ofReal y⁻¹) = ENNReal.ofReal (Real.log (b / a)) := by
{
  have hc : ContinuousOn (fun y : ℝ => y⁻¹) (Icc a b) :=
    continuousOn_id.inv₀ (fun y hy => ne_of_gt (ha.trans_le hy.1))
  have hi : IntegrableOn (fun y : ℝ => y⁻¹) (Icc a b) volume := hc.integrableOn_Icc
  rw [← ofReal_integral_eq_lintegral_ofReal hi]
  · rw [integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hab,
      integral_inv_of_pos ha (ha.trans_le hab)]
  · filter_upwards [ae_restrict_mem measurableSet_Icc] with y hy
    exact inv_nonneg.mpr (ha.le.trans hy.1)
}

lemma lintegral_transportBox_inv {R a b : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ z in transportBox R a b, ENNReal.ofReal z.im⁻¹) =
      ENNReal.ofReal (2 * R * Real.log (b / a)) := by
{
  have he : Complex.measurableEquivRealProd ⁻¹' (Icc (-R) R ×ˢ Icc a b) = transportBox R a b := by
  {
    ext z
    simp only [Complex.measurableEquivRealProd_apply, mem_preimage, mem_prod, mem_Icc,
      transportBox, mem_setOf_eq, abs_le]
  }
  have hprod := Complex.volume_preserving_equiv_real_prod.setLIntegral_comp_preimage_emb
    Complex.measurableEquivRealProd.measurableEmbedding (fun p : ℝ × ℝ => ENNReal.ofReal p.2⁻¹)
    (Icc (-R) R ×ˢ Icc a b)
  rw [he] at hprod
  change (∫⁻ z in transportBox R a b, ENNReal.ofReal z.im⁻¹) = _ at hprod
  rw [hprod, show (volume : Measure (ℝ × ℝ)) = volume.prod volume from rfl,
    setLIntegral_prod _ (by fun_prop)]
  dsimp only
  rw [lintegral_Icc_inv ha hab, lintegral_const, Measure.restrict_apply_univ, Real.volume_Icc]
  rw [show R - -R = 2 * R from by ring, mul_comm, ← ENNReal.ofReal_mul (by positivity : 0 ≤ 2 * R)]
}

def rootJac (beta σ : ℝ) (F : KClass) : ℝ≥0∞ :=
  ENNReal.ofReal (σ * J beta F I)

lemma continuous_J_root (beta : ℝ) : Continuous (fun F : KClass => J beta F I) := by
{
  let hI : H := ⟨I, by dsimp [H]; simp⟩
  have he : (fun F : KClass => J beta F I) =
      (fun g : DiskClass => J beta (toKClass g) hI) ∘ ofKClass :=
    funext (fun F => (G_J_congr_ofKClass beta F hI.2).2)
  rw [he]
  exact ((continuous_diskClass_J beta).comp (continuous_id.prodMk continuous_const)).comp continuous_ofKClass
}

lemma measurable_rootJac (beta σ : ℝ) : Measurable (rootJac beta σ) := by
{
  exact (measurable_const.mul (continuous_J_root beta).measurable).ennreal_ofReal
}

lemma rootJac_T_elem (beta : ℝ) (hk : k_val beta ≠ 0) (σ : ℝ) (F : KClass) (z : H) :
    rootJac beta σ (T_elem F z.1 z.2) = ENNReal.ofReal (σ * J beta F z) := by
{
  rw [rootJac, J_T_elem_root beta hk F z.2]
}

def rootWindow (beta N : ℝ) : Set KClass :=
  {F | (F, ⟨I, by dsimp [H]; simp⟩) ∈ transportWindow beta N}

def windowTest (beta N : ℝ) : KClass → ℝ≥0∞ := (rootWindow beta N).indicator (rootJac beta 1)

lemma measurableSet_rootWindow (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) (N : ℝ) :
    MeasurableSet (rootWindow beta N) := by
{
  exact (measurableSet_transportWindow h_rho beta h_beta N).preimage (measurable_id.prodMk measurable_const)
}

lemma measurable_windowTest (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) (N : ℝ) :
    Measurable (windowTest beta N) := by
{
  exact (measurable_rootJac beta 1).indicator (measurableSet_rootWindow h_rho beta h_beta N)
}

lemma averagedDensity_window {beta : ℝ} (h_beta : beta > 1) (N : ℝ) (F : KClass) (z : H) :
    averagedDensity beta (windowTest beta N) (F, z) =
      transportDensity beta F z * ENNReal.ofReal (J beta F z) *
        (transportSlice beta N F).indicator 1 z := by
{
  have hk : k_val beta ≠ 0 := by unfold k_val; linarith
  rw [averagedDensity_of_mem, windowTest]
  have he : T_elem F z.1 z.2 ∈ rootWindow beta N ↔ z.val ∈ transportSlice beta N F :=
    (transportWindow_root h_beta N F z).trans (transportSlice_iff beta N F z).symm
  by_cases hz : z.val ∈ transportSlice beta N F
  · rw [indicator_of_mem (he.mpr hz), rootJac_T_elem beta hk 1 F z, one_mul, indicator_of_mem hz]
    simp
  · rw [indicator_of_notMem (fun h => hz (he.mp h)), indicator_of_notMem hz]
    simp
}

def rootException (beta : ℝ) : Set KClass :=
  {F | ¬is_good_pair beta F (G beta F I)}

def exceptionTest (beta : ℝ) : KClass → ℝ≥0∞ := (rootException beta).indicator (rootJac beta 1)

lemma measurableSet_rootException (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) :
    MeasurableSet (rootException beta) := by
{
  let hI : H := ⟨I, by dsimp [H]; simp⟩
  have hG : Continuous (fun F : KClass => G beta F I) := by
  {
    have he : (fun F : KClass => G beta F I) =
        (fun g : DiskClass => G beta (toKClass g) hI) ∘ ofKClass :=
      funext (fun F => (G_J_congr_ofKClass beta F hI.2).1)
    rw [he]
    exact ((continuous_diskClass_G beta).comp (continuous_id.prodMk continuous_const)).comp continuous_ofKClass
  }
  have hm : Measurable (fun F : KClass => (F, G beta F I)) :=
    measurable_id.prodMk hG.measurable
  exact ((lemma_5_4_good_pairs h_rho beta h_beta).1.preimage hm).compl
}

lemma measurable_exceptionTest (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) :
    Measurable (exceptionTest beta) := by
{
  exact (measurable_rootJac beta 1).indicator (measurableSet_rootException h_rho beta h_beta)
}

lemma averagedDensity_exception {beta : ℝ} (h_beta : beta > 1) (F : KClass) (z : H) :
    averagedDensity beta (exceptionTest beta) (F, z) =
      transportDensity beta F z * ENNReal.ofReal (J beta F z) *
        {z : ℂ | z ∈ H ∧ ¬is_good_pair beta F (G beta F z)}.indicator 1 z := by
{
  have hk : 0 < k_val beta := by unfold k_val; linarith
  rw [averagedDensity_of_mem, exceptionTest]
  have he := is_good_pair_T_elem_root beta hk F z.2
  by_cases hg : is_good_pair beta F (G beta F z)
  · rw [indicator_of_notMem (show T_elem F z.1 z.2 ∉ rootException beta from fun h => h (he.mpr hg)),
      indicator_of_notMem (show z.val ∉ {z : ℂ | z ∈ H ∧ ¬is_good_pair beta F (G beta F z)} from fun h => h.2 hg)]
    simp
  · rw [indicator_of_mem (show T_elem F z.1 z.2 ∈ rootException beta from fun h => hg (he.mp h)),
      rootJac_T_elem beta hk.ne' 1 F z, one_mul,
      indicator_of_mem (show z.val ∈ {z : ℂ | z ∈ H ∧ ¬is_good_pair beta F (G beta F z)} from ⟨z.2, hg⟩)]
    simp
}

lemma exceptionTest_integral_zero (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) :
    (∫⁻ F, exceptionTest beta F ∂P_eigenmeasure) = 0 := by
{
  have h_beta_gt : beta > 1 := by
  {
    rw [h_beta]
    exact (one_lt_div (Real.log_pos (by norm_num))).mpr (Real.log_lt_log (by norm_num) h_rho)
  }
  apply root_test_zero_of_averaging h_rho beta h_beta (measurable_exceptionTest h_rho beta h_beta)
  filter_upwards [(lemma_5_4_good_pairs h_rho beta h_beta).2] with F hF
  have hg : ∀ᵐ xi : ℂ, is_good_pair beta F xi := by
  {
    rw [ae_iff]
    simpa only [not_not] using hF
  }
  refine Eq.trans ?_ (exceptional_transport_zero h_rho beta h_beta F hg)
  apply setLIntegral_congr_fun isOpen_H.measurableSet
  intro z hz
  exact averagedDensity_exception h_beta_gt F ⟨z, hz⟩
}

lemma averagedDensity_box (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2)
    {Phi : KClass → ℝ≥0∞} (hPhi : Measurable Phi)
    {R a b : ℝ} (hR : 0 ≤ R) (ha : 0 < a) (hab : a ≤ b) :
    (∫⁻ F, ∫⁻ z in transportBox R a b, averagedDensity beta Phi (F, z) ∂volume ∂P_eigenmeasure) =
      ENNReal.ofReal (2 * R * Real.log (b / a)) * ∫⁻ F, Phi F ∂P_eigenmeasure := by
{
  haveI : IsProbabilityMeasure P_eigenmeasure := (lemma_3_1_weighted_covariance h_rho).1
  rw [lintegral_lintegral_swap (f := fun F z => averagedDensity beta Phi (F, z))
    (μ := P_eigenmeasure) (ν := volume.restrict (transportBox R a b))
    (measurable_averagedDensity beta hPhi).aemeasurable]
  have he : (∫⁻ z in transportBox R a b, ∫⁻ F, averagedDensity beta Phi (F, z) ∂P_eigenmeasure) =
      ∫⁻ z in transportBox R a b, ENNReal.ofReal z.im⁻¹ * ∫⁻ F, Phi F ∂P_eigenmeasure := by
  {
    apply setLIntegral_congr_fun (measurableSet_transportBox R a b)
    intro z hz
    exact weighted_averagedDensity h_rho beta h_beta hPhi ⟨z, ha.trans_le hz.2.1⟩
  }
  rw [he, lintegral_mul_const _ (by fun_prop), lintegral_transportBox_inv hR ha hab]
}

lemma setLIntegral_mul_indicator_one {S T : Set ℂ} (hS : MeasurableSet S) (hST : S ⊆ T)
    (f : ℂ → ℝ≥0∞) :
    (∫⁻ z in T, f z * S.indicator 1 z) = ∫⁻ z in S, f z := by
{
  have he : (fun z => f z * S.indicator 1 z) = S.indicator f := by
  {
    funext z
    by_cases hz : z ∈ S <;> simp [hz]
  }
  rw [he, setLIntegral_indicator hS, inter_eq_left.mpr hST]
}

lemma transport_box_averaged (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) {N R Y : ℝ} (hN : 1 ≤ N) (F : KClass) :
    (∫⁻ z in transportBox R 1 Y, averagedDensity beta (windowTest beta N) (F, z)) ≤
      ∫⁻ z in transportBox (R + N * Y) (1 / N) (N * Y), averagedDensity beta (rootJac beta (-1)) (F, z) := by
{
  have h_beta_gt : beta > 1 := by
  {
    rw [h_beta]
    exact (one_lt_div (Real.log_pos (by norm_num))).mpr (Real.log_lt_log (by norm_num) h_rho)
  }
  have hk : k_val beta ≠ 0 := by unfold k_val; linarith
  have hn : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hB : transportBox R 1 Y ⊆ H := fun z hz => lt_of_lt_of_le zero_lt_one hz.2.1
  have hB' : transportBox (R + N * Y) (1 / N) (N * Y) ⊆ H := fun z hz =>
    lt_of_lt_of_le (one_div_pos.mpr hn) hz.2.1
  have he := transport_box h_rho beta h_beta hN F (R := R) (Y := Y)
  have hp : (∫⁻ z in H, transportDensity beta F z * ENNReal.ofReal (J beta F z) *
      (transportSlice beta N F ∩ transportBox R 1 Y).indicator 1 z) =
      ∫⁻ z in transportBox R 1 Y, averagedDensity beta (windowTest beta N) (F, z) := by
  {
    have hid : (fun z => transportDensity beta F z * ENNReal.ofReal (J beta F z) *
      (transportSlice beta N F ∩ transportBox R 1 Y).indicator 1 z) =
      fun z => (transportDensity beta F z * ENNReal.ofReal (J beta F z) *
        (transportSlice beta N F).indicator 1 z) * (transportBox R 1 Y).indicator 1 z := by
    {
      funext z
      rw [inter_indicator_one]
      simp only [Pi.mul_apply, mul_assoc]
    }
    rw [hid, setLIntegral_mul_indicator_one (measurableSet_transportBox _ _ _) hB]
    apply setLIntegral_congr_fun (measurableSet_transportBox _ _ _)
    intro z hz
    exact (averagedDensity_window h_beta_gt N F ⟨z, hB hz⟩).symm
  }
  have hm : (∫⁻ z in H, transportDensity beta F z * ENNReal.ofReal (-J beta F z) *
      (transportBox (R + N * Y) (1 / N) (N * Y)).indicator 1 z) =
      ∫⁻ z in transportBox (R + N * Y) (1 / N) (N * Y), averagedDensity beta (rootJac beta (-1)) (F, z) := by
  {
    rw [setLIntegral_mul_indicator_one (measurableSet_transportBox _ _ _) hB']
    apply setLIntegral_congr_fun (measurableSet_transportBox _ _ _)
    intro z hz
    symm
    exact (averagedDensity_of_mem beta (rootJac beta (-1)) F ⟨z, hB' hz⟩).trans
      (congrArg (transportDensity beta F z * ·) (by simpa only [neg_one_mul] using rootJac_T_elem beta hk (-1) F ⟨z, hB' hz⟩))
  }
  exact hp.symm.trans_le (he.trans_eq hm)
}

lemma expected_transport_box (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) {N R Y : ℝ}
    (hN : 1 ≤ N) (hR : 0 ≤ R) (hY : 1 ≤ Y) :
    ENNReal.ofReal (2 * R * Real.log Y) * (∫⁻ F, windowTest beta N F ∂P_eigenmeasure) ≤
      ENNReal.ofReal (2 * (R + N * Y) * Real.log (N ^ 2 * Y)) *
        (∫⁻ F, rootJac beta (-1) F ∂P_eigenmeasure) := by
{
  have hn : 0 < N := lt_of_lt_of_le zero_lt_one hN
  have hny : 1 / N ≤ N * Y := by
  {
    rw [div_le_iff₀ hn]
    have hc := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hY hn.le) hn.le
    nlinarith [sq_nonneg (N - 1)]
  }
  have hp := averagedDensity_box h_rho beta h_beta (measurable_windowTest h_rho beta h_beta N) hR zero_lt_one hY
  have hm := averagedDensity_box h_rho beta h_beta (measurable_rootJac beta (-1))
    (add_nonneg hR (mul_nonneg hn.le (zero_le_one.trans hY))) (one_div_pos.mpr hn) hny
  simp only [div_one] at hp
  rw [show N * Y / (1 / N) = N ^ 2 * Y from by field_simp] at hm
  rw [← hp, ← hm]
  exact lintegral_mono (fun F => transport_box_averaged h_rho beta h_beta hN F)
}

lemma transport_ratio_tendsto (N : ℝ) :
    Tendsto (fun Y : ℝ => (1 + N / Y) * (1 + 2 * Real.log N / Real.log Y)) atTop (𝓝 1) := by
{
  have h1 : Tendsto (fun Y : ℝ => N / Y) atTop (𝓝 0) := tendsto_const_nhds.div_atTop tendsto_id
  have h2 : Tendsto (fun Y : ℝ => 2 * Real.log N / Real.log Y) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop Real.tendsto_log_atTop
  simpa using ((tendsto_const_nhds (x := (1 : ℝ))).add h1).mul ((tendsto_const_nhds (x := (1 : ℝ))).add h2)
}

lemma transport_box_limit {A B : ℝ≥0∞} (hA : A ≠ ∞) (hB : B ≠ ∞)
    {N : ℝ} (hN : 1 ≤ N)
    (h : ∀ Y : ℝ, 1 < Y →
      ENNReal.ofReal (2 * Y ^ 2 * Real.log Y) * A ≤
        ENNReal.ofReal (2 * (Y ^ 2 + N * Y) * Real.log (N ^ 2 * Y)) * B) : A ≤ B := by
{
  have hn : 0 < N := zero_lt_one.trans_le hN
  have hineq : ∀ Y : ℝ, 1 < Y → A.toReal ≤ (1 + N / Y) * (1 + 2 * Real.log N / Real.log Y) * B.toReal := by
  {
    intro Y hY
    have hy : 0 < Y := zero_lt_one.trans hY
    have hl : 0 < Real.log Y := Real.log_pos hY
    have hny : 1 < N ^ 2 * Y := by nlinarith [sq_nonneg (N - 1)]
    have hlny : 0 ≤ Real.log (N ^ 2 * Y) := Real.log_nonneg hny.le
    have hb := ENNReal.toReal_mono (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hB) (h Y hY)
    rw [ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * Y ^ 2 * Real.log Y),
      ENNReal.toReal_ofReal (by positivity : 0 ≤ 2 * (Y ^ 2 + N * Y) * Real.log (N ^ 2 * Y))] at hb
    have hlog : Real.log (N ^ 2 * Y) = 2 * Real.log N + Real.log Y := by
    {
      rw [Real.log_mul (by positivity) (ne_of_gt hy), Real.log_pow]
      norm_num
    }
    rw [hlog] at hb
    apply (mul_le_mul_iff_right₀ (show 0 < 2 * Y ^ 2 * Real.log Y by positivity)).mp
    calc
      _ ≤ 2 * (Y ^ 2 + N * Y) * (2 * Real.log N + Real.log Y) * B.toReal := hb
      _ = _ := by field_simp; ring
  }
  apply (ENNReal.toReal_le_toReal hA hB).mp
  have ht := (transport_ratio_tendsto N).mul_const B.toReal
  simp only [one_mul] at ht
  apply ge_of_tendsto ht
  filter_upwards [eventually_gt_atTop (1 : ℝ)] with Y hY
  exact hineq Y hY
}

lemma integrable_J_at_I (beta σ : ℝ) (P : Measure KClass) [IsFiniteMeasure P] :
    Integrable (fun F : KClass => σ * J beta F I) P := by
{
  let hI : H := ⟨I, by dsimp [H]; simp⟩
  have hc_disk : Continuous (fun g : DiskClass => σ * J beta (toKClass g) hI) :=
    continuous_const.mul ((continuous_diskClass_J beta).comp (continuous_id.prodMk continuous_const))
  obtain ⟨M, hM⟩ := isCompact_univ.exists_bound_of_continuousOn hc_disk.continuousOn
  have he : (fun F : KClass => σ * J beta F I) =
      (fun g : DiskClass => σ * J beta (toKClass g) hI) ∘ ofKClass :=
    funext (fun F => congrArg (σ * ·) (G_J_congr_ofKClass beta F hI.2).2)
  have hc : Continuous (fun F : KClass => σ * J beta F I) := he ▸ hc_disk.comp continuous_ofKClass
  refine (integrable_const M).mono' hc.aestronglyMeasurable (Eventually.of_forall (fun F => ?_))
  rw [(G_J_congr_ofKClass beta F hI.2).2]
  exact hM (ofKClass F) (mem_univ _)
}

lemma rootJac_integral_lt_top (beta σ : ℝ) (P : Measure KClass) [IsFiniteMeasure P] :
    (∫⁻ F, rootJac beta σ F ∂P) < ∞ := by
{
  have hi := integrable_J_at_I beta σ P
  apply lt_of_le_of_lt (lintegral_mono (fun F => ENNReal.ofReal_le_ofReal (le_abs_self _)))
  exact (hasFiniteIntegral_iff_norm _).mp hi.2
}

lemma windowTest_le (beta N : ℝ) (F : KClass) : windowTest beta N F ≤ rootJac beta 1 F := by
{
  by_cases hF : F ∈ rootWindow beta N <;> simp [windowTest, indicator_of_mem, indicator_of_notMem, hF]
}

lemma windowTest_integral_lt_top (beta N : ℝ) (P : Measure KClass) [IsFiniteMeasure P] :
    (∫⁻ F, windowTest beta N F ∂P) < ∞ := by
{
  exact (lintegral_mono (windowTest_le beta N)).trans_lt (rootJac_integral_lt_top beta 1 P)
}

lemma windowTest_mono {beta : ℝ} (h_beta : beta > 1) :
    Monotone (fun n : ℕ => windowTest beta (n + 1)) := by
{
  intro n m hnm F
  have hs : rootWindow beta (n + 1) ⊆ rootWindow beta (m + 1) :=
    fun F hF => transportWindow_mono h_beta (by exact_mod_cast Nat.add_le_add_right hnm 1) hF
  by_cases hF : F ∈ rootWindow beta (n + 1)
  · simp only [windowTest, indicator_of_mem hF, indicator_of_mem (hs hF), le_refl]
  · simp only [windowTest, indicator_of_notMem hF]
    exact bot_le
}

lemma iSup_windowTest {beta : ℝ} (h_beta : beta > 1) (F : KClass) :
    (⨆ n : ℕ, windowTest beta (n + 1) F) =
      {F : KClass | (F, ⟨I, by dsimp [H]; simp⟩) ∈ pairingDomain beta}.indicator (rootJac beta 1) F := by
{
  let hI : H := ⟨I, by dsimp [H]; simp⟩
  by_cases hF : (F, hI) ∈ pairingDomain beta
  · rw [indicator_of_mem (show F ∈ {F : KClass | (F, hI) ∈ pairingDomain beta} from hF)]
    apply le_antisymm (iSup_le (fun n : ℕ => windowTest_le beta (n + 1) F))
    have hu : (F, hI) ∈ ⋃ n : ℕ, transportWindow beta (n + 1) :=
      (iUnion_transportWindow h_beta).symm ▸ hF
    obtain ⟨n, hn⟩ := mem_iUnion.mp hu
    have he : windowTest beta (n + 1) F = rootJac beta 1 F :=
      indicator_of_mem (show F ∈ rootWindow beta (n + 1) from hn) _
    exact he ▸ le_iSup (fun n : ℕ => windowTest beta (n + 1) F) n
  · rw [indicator_of_notMem (show F ∉ {F : KClass | (F, hI) ∈ pairingDomain beta} from hF)]
    apply le_antisymm _ bot_le
    apply iSup_le
    intro n
    apply le_of_eq
    apply indicator_of_notMem
    intro hn
    exact hF hn.1
}

lemma rootJac_eq_window_exception {beta : ℝ} (h_beta : beta > 1) (F : KClass) :
    rootJac beta 1 F = (⨆ n : ℕ, windowTest beta (n + 1) F) + exceptionTest beta F := by
{
  let hI : H := ⟨I, by dsimp [H]; simp⟩
  rw [iSup_windowTest h_beta F, exceptionTest]
  by_cases hG : is_good_pair beta F (G beta F I)
  · rw [indicator_of_notMem (show F ∉ rootException beta from fun h => h hG), add_zero]
    by_cases hJ : 0 < J beta F I
    · exact (indicator_of_mem (show F ∈ {F : KClass | (F, hI) ∈ pairingDomain beta} from ⟨hJ, hG⟩) _).symm
    · rw [indicator_of_notMem (show F ∉ {F : KClass | (F, hI) ∈ pairingDomain beta} from fun h => hJ h.1)]
      exact ENNReal.ofReal_eq_zero.mpr (by simpa only [one_mul] using le_of_not_gt hJ)
  · rw [indicator_of_mem (show F ∈ rootException beta from hG),
      indicator_of_notMem (show F ∉ {F : KClass | (F, hI) ∈ pairingDomain beta} from fun h => hG h.2), zero_add]
}

lemma jacobian_positive_le_negative (h_rho : rho > 2) (beta : ℝ)
    (h_beta : beta = Real.log rho / Real.log 2) :
    (∫⁻ F, rootJac beta 1 F ∂P_eigenmeasure) ≤ ∫⁻ F, rootJac beta (-1) F ∂P_eigenmeasure := by
{
  haveI : IsProbabilityMeasure P_eigenmeasure := (lemma_3_1_weighted_covariance h_rho).1
  have h_beta_gt : beta > 1 := by
  {
    rw [h_beta]
    exact (one_lt_div (Real.log_pos (by norm_num))).mpr (Real.log_lt_log (by norm_num) h_rho)
  }
  have hw (n : ℕ) : (∫⁻ F, windowTest beta (n + 1) F ∂P_eigenmeasure) ≤
      ∫⁻ F, rootJac beta (-1) F ∂P_eigenmeasure := by
  {
    apply transport_box_limit (N := (n : ℝ) + 1)
      (windowTest_integral_lt_top beta (n + 1) P_eigenmeasure).ne
      (rootJac_integral_lt_top beta (-1) P_eigenmeasure).ne
      (by have h := Nat.cast_nonneg (α := ℝ) n; linarith : (1 : ℝ) ≤ n + 1)
    intro Y hY
    exact expected_transport_box h_rho beta h_beta
      (by have h := Nat.cast_nonneg (α := ℝ) n; linarith) (sq_nonneg Y) hY.le
  }
  have he (F : KClass) := rootJac_eq_window_exception h_beta_gt F
  simp_rw [he]
  rw [lintegral_add_left (Measurable.iSup (fun n : ℕ => measurable_windowTest h_rho beta h_beta (n + 1))),
    exceptionTest_integral_zero h_rho beta h_beta, add_zero,
    lintegral_iSup (fun n : ℕ => measurable_windowTest h_rho beta h_beta (n + 1)) (windowTest_mono h_beta_gt)]
  exact iSup_le hw
}

theorem E_J_nonpositive_proof (h_rho : rho > 2) :
    ∫ F, J (Real.log rho / Real.log 2) F I ∂P_eigenmeasure ≤ 0 := by
{
  haveI : IsProbabilityMeasure P_eigenmeasure := (lemma_3_1_weighted_covariance h_rho).1
  set beta := Real.log rho / Real.log 2
  have hi := jacobian_positive_le_negative h_rho beta rfl
  have hInt : Integrable (fun F : KClass => J beta F I) P_eigenmeasure := by
  {
    simpa only [one_mul] using integrable_J_at_I beta 1 P_eigenmeasure
  }
  rw [integral_eq_lintegral_pos_part_sub_lintegral_neg_part hInt]
  have ht := ENNReal.toReal_mono (rootJac_integral_lt_top beta (-1) P_eigenmeasure).ne hi
  simpa only [rootJac, one_mul, neg_one_mul, sub_nonpos] using ht
}

end Brennan.Sections6and7
