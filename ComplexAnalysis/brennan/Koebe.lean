import Mathlib

open Complex Set MeasureTheory Topology Filter Classical InnerProductSpace
open scoped ComplexConjugate Topology

noncomputable section

namespace Brennan.Koebe

/-!
# Classical Koebe Distortion, Growth, and Quarter-Disk Theorems

This file proves the classical univalence estimates for the normalized disk class `IsClassS`
(Lemma 2.1 of the paper):
1. Bieberbach's second coefficient bound `‖deriv (deriv f) 0‖ ≤ 4` (`|a₂| ≤ 2`) from
   Gronwall's meromorphic area inequality (`meromorphic_univalent_area`).
2. Koebe Quarter Theorem (`koebe_quarter_theorem` and `local_koebe_quarter`).
3. Pre-Schwarzian inequality `‖(1 - ‖a‖²) f''(a)/f'(a) - 2 conj a‖ ≤ 4`.
4. Koebe Derivative Distortion (`(1 - r)/(1 + r)³ ≤ ‖f'(z)‖ ≤ (1 + r)/(1 - r)³`).
5. Koebe Growth Bounds (`‖z‖ / 4 ≤ ‖f(z)‖ ≤ ‖z‖ / (1 - ‖z‖)²`).
-/

/-- The open unit disk `𝔻 = B(0, 1)`. -/
def disk : Set ℂ := Metric.ball 0 1

/-- Univalent maps on a domain `U`. -/
def UnivalentOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ InjOn f U

/-- The normalized schlicht class `S` on the unit disk. -/
def IsClassS (f : ℂ → ℂ) : Prop :=
  DifferentiableOn ℂ f (Metric.ball 0 1) ∧ InjOn f (Metric.ball 0 1) ∧ f 0 = 0 ∧ deriv f 0 = 1

lemma isClassS_univalent {f : ℂ → ℂ} (hf : IsClassS f) : UnivalentOn f disk := by
{
  exact ⟨hf.1, hf.2.1⟩
}

/-! ### 1. Non-vanishing derivative of univalent maps -/

lemma nonconstant_germ_of_injOn {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : Set.InjOn f U) {a : ℂ} (ha : a ∈ U) :
    ¬ ∀ᶠ z in 𝓝 a, f z = f a := by
{
  intro hc
  have heq : ∀ᶠ z in 𝓝 a, z = a := by
  {
    filter_upwards [hc, hU.mem_nhds ha] with z hz hzU
    exact hf hzU ha hz
  }
  have heq' : ∀ᶠ z in 𝓝[≠] a, z = a := heq.filter_mono nhdsWithin_le_nhds
  have hne' : ∀ᶠ z in 𝓝[≠] a, z ≠ a := self_mem_nhdsWithin
  obtain ⟨z, hz, hne⟩ := (heq'.and hne').exists
  exact hne hz
}

lemma univalent_inverse_continuousAt {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : UnivalentOn f U) {a : ℂ} (ha : a ∈ U) :
    ContinuousAt (Function.invFunOn f U) (f a) := by
{
  have haan : AnalyticAt ℂ f a := (hf.1.analyticOnNhd hU) a ha
  have hopen : 𝓝 (f a) ≤ Filter.map f (𝓝 a) :=
    haan.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (nonconstant_germ_of_injOn hU hf.2 ha)
  have hl : ∀ᶠ z in 𝓝 a, Function.invFunOn f U (f z) = z := by
  {
    filter_upwards [hU.mem_nhds ha] with z hz
    exact hf.2.leftInvOn_invFunOn hz
  }
  have ht : Tendsto (Function.invFunOn f U ∘ f) (𝓝 a) (𝓝 a) :=
    tendsto_id.congr' (Filter.EventuallyEq.symm hl)
  rw [ContinuousAt, hf.2.leftInvOn_invFunOn ha]
  exact (tendsto_map'_iff.mpr ht).mono_left hopen
}

lemma univalent_deriv_eventually_ne_zero {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : UnivalentOn f U) {a : ℂ} (ha : a ∈ U) :
    ∀ᶠ z in 𝓝[≠] a, deriv f z ≠ 0 := by
{
  have han : AnalyticAt ℂ f a := hf.1.analyticOnNhd hU a ha
  have hd_nonconst : ¬ ∀ᶠ z in 𝓝 a, deriv f z = 0 := by
  {
    intro hc
    obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (hc.and (hU.mem_nhds ha))
    have hfball : DifferentiableOn ℂ f (Metric.ball a r) :=
      hf.1.mono (fun z hz => (hball hz).2)
    have hcball : ∀ z ∈ Metric.ball a r, f z = f a := by
    {
      intro z hz
      exact Metric.isOpen_ball.is_const_of_deriv_eq_zero (convex_ball a r).isPreconnected
        hfball (fun w hw => (hball hw).1) hz (Metric.mem_ball_self hr)
    }
    apply nonconstant_germ_of_injOn hU hf.2 ha
    filter_upwards [Metric.ball_mem_nhds a hr] with z hz
    exact hcball z hz
  }
  exact han.deriv.eventually_eq_zero_or_eventually_ne_zero.resolve_left hd_nonconst
}

lemma univalent_deriv_ne_zero {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : UnivalentOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
{
  have han : AnalyticAt ℂ f a := hf.1.analyticOnNhd hU a ha
  have hd := univalent_deriv_eventually_ne_zero hU hf ha
  let g := Function.invFunOn f U
  have hgc : ContinuousAt g (f a) := univalent_inverse_continuousAt hU hf ha
  have hga : g (f a) = a := hf.2.leftInvOn_invFunOn ha
  have hopen : 𝓝 (f a) ≤ Filter.map f (𝓝 a) :=
    han.eventually_constant_or_nhds_le_map_nhds.resolve_left
      (nonconstant_germ_of_injOn hU hf.2 ha)
  have hright : ∀ᶠ w in 𝓝 (f a), g w ∈ U ∧ f (g w) = w := by
  {
    apply hopen (Filter.mem_map.mpr ?_)
    filter_upwards [hU.mem_nhds ha] with z hz
    exact ⟨Function.invFunOn_apply_mem hz, Function.invFunOn_apply_eq hz⟩
  }
  have hgne : ∀ᶠ w in 𝓝[≠] (f a), g w ≠ a := by
  {
    filter_upwards [hright.filter_mono nhdsWithin_le_nhds, self_mem_nhdsWithin] with w hw hwne
    exact fun heq => hwne (hw.2.symm.trans (congrArg f heq))
  }
  have hgt : Tendsto g (𝓝[≠] (f a)) (𝓝[≠] a) :=
    tendsto_nhdsWithin_iff.mpr ⟨by simpa only [hga] using hgc.tendsto.mono_left nhdsWithin_le_nhds, hgne⟩
  have hgd : ∀ᶠ w in 𝓝[≠] (f a), DifferentiableAt ℂ g w := by
  {
    filter_upwards [hgt.eventually hd, hright.filter_mono nhdsWithin_le_nhds] with w hwder hw
    have hws : HasStrictDerivAt f (deriv f (g w)) (g w) :=
      ((hf.1.analyticOnNhd hU (g w) hw.1).contDiffAt (n := 1)).hasStrictDerivAt (by norm_num)
    have hl : ∀ᶠ z in 𝓝 (g w), g (f z) = z := by
      filter_upwards [hU.mem_nhds hw.1] with z hz using hf.2.leftInvOn_invFunOn hz
    simpa [hw.2] using (hws.to_local_left_inverse hwder hl).hasDerivAt.differentiableAt
  }
  have hgan := Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt hgd hgc
  have hcomp := hgan.differentiableAt.hasDerivAt.comp a han.differentiableAt.hasDerivAt
  have hid : (fun z => g (f z)) =ᶠ[𝓝 a] id := by
    filter_upwards [hU.mem_nhds ha] with z hz using hf.2.leftInvOn_invFunOn hz
  have hprod : deriv g (f a) * deriv f a = 1 := by
    simpa using (hcomp.congr_of_eventuallyEq hid.symm).unique (hasDerivAt_id a)
  intro hzero
  simp [hzero] at hprod
}

/-! ### 2. Submean inequality and Gronwall's Area Inequality -/

lemma polar_symm_eq_circleMap (r θ : ℝ) :
    Complex.polarCoord.symm (r, θ) = circleMap 0 r θ := by
{
  rw [Complex.polarCoord_symm_apply, circleMap, zero_add]
  congr 1
  rw [Complex.exp_mul_I]
  simp
}

lemma circleAverage_eq_integral_neg_pi (f : ℂ → ℂ) (c : ℂ) (r : ℝ) :
    Real.circleAverage f c r =
      (2 * Real.pi)⁻¹ • ∫ θ in -Real.pi..Real.pi, f (circleMap c r θ) := by
{
  rw [Real.circleAverage_eq_integral_add (-Real.pi)]
  rw [intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c r θ))]
  congr 2 <;> ring
}

lemma integral_ball_polar_step1 {f : ℂ → ℂ} {R : ℝ}
    (hf : ContinuousOn f (Metric.closedBall 0 R)) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi) := by
{
  let g : ℝ × ℝ → ℂ := fun p => p.1 • f (Complex.polarCoord.symm p)
  refine (show IntegrableOn g (Icc (0 : ℝ) R ×ˢ Icc (-Real.pi) Real.pi) from ?_).mono_set
    (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hpolar : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  {
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  }
  apply continuousOn_fst.smul (hf.comp hpolar.continuousOn ?_)
  intro p hp
  simp only [Metric.mem_closedBall, dist_zero_right, Complex.norm_polarCoord_symm]
  exact (abs_of_nonneg hp.1.1).trans_le hp.1.2
}

lemma integral_ball_polar_step2 {f : ℂ → ℂ} {R : ℝ} :
    ∫ z in Metric.ball (0 : ℂ) R, f z =
      ∫ p in Ioo (0 : ℝ) R ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • f (Complex.polarCoord.symm p) := by
{
  let g : ℝ × ℝ → ℂ := fun p => p.1 • f (Complex.polarCoord.symm p)
  rw [← integral_indicator Metric.isOpen_ball.measurableSet,
    ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have heq : (fun p : ℝ × ℝ => p.1 •
      (Metric.ball (0 : ℂ) R).indicator f (Complex.polarCoord.symm p)) =ᶠ[
      ae (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi))]
    (Iio R ×ˢ (univ : Set ℝ)).indicator g := by
  {
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
    have hp1 : 0 < p.1 := hp.1
    by_cases hr : p.1 < R
    · rw [indicator_of_mem (by simpa [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp1] using hr),
        indicator_of_mem (show p ∈ Iio R ×ˢ (univ : Set ℝ) from ⟨hr, mem_univ _⟩)]
    · rw [indicator_of_notMem (by simpa [Metric.mem_ball, dist_zero_right, Complex.norm_polarCoord_symm, abs_of_pos hp1] using hr),
        indicator_of_notMem (show p ∉ Iio R ×ˢ (univ : Set ℝ) from fun h => hr h.1), smul_zero]
  }
  rw [integral_congr_ae heq, integral_indicator (measurableSet_Iio.prod MeasurableSet.univ),
    Measure.restrict_restrict (measurableSet_Iio.prod MeasurableSet.univ)]
  congr 2
  ext p
  simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Iio, mem_Ioo, mem_univ, and_true]
  tauto
}

lemma integral_ball_polar {f : ℂ → ℂ} {R : ℝ} (hR : 0 < R)
    (hf : ContinuousOn f (Metric.closedBall 0 R)) :
    ∫ z in Metric.ball (0 : ℂ) R, f z =
      ∫ r in (0 : ℝ)..R, (2 * Real.pi * r) • Real.circleAverage f 0 r := by
{
  have hg := integral_ball_polar_step1 hf
  rw [integral_ball_polar_step2, Measure.volume_eq_prod, setIntegral_prod _ hg]
  rw [intervalIntegral.integral_of_le hR.le, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r _hr
  dsimp only
  rw [circleAverage_eq_integral_neg_pi,
    intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    integral_Ioc_eq_integral_Ioo, ← smul_assoc]
  have he : (2 * Real.pi * r) * (2 * Real.pi)⁻¹ = r := by field_simp
  rw [smul_eq_mul, he, ← integral_smul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ _hθ
  simp only [polar_symm_eq_circleMap]
}

lemma ball_closedBall_ae_eq (r : ℝ) :
    Metric.ball (0 : ℂ) r =ᵐ[volume] Metric.closedBall 0 r := by
{
  apply ae_eq_set.mpr
  constructor
  · rw [diff_eq_empty.mpr Metric.ball_subset_closedBall, measure_empty]
  · rw [Metric.closedBall_diff_ball]
    exact Measure.addHaar_sphere volume 0 r
}

lemma integral_ball_holomorphic {f : ℂ → ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R))
    (hr : 0 < r) (hrR : r < R) :
    ∫ z in Metric.ball (0 : ℂ) r, f z = volume.real (Metric.ball (0 : ℂ) r) • f 0 := by
{
  have hfc : ContinuousOn f (Metric.closedBall 0 r) :=
    hf.continuousOn.mono (Metric.closedBall_subset_ball hrR)
  rw [integral_ball_polar hr hfc]
  have hc := integral_ball_polar (f := fun _ : ℂ => f 0) hr continuousOn_const
  rw [setIntegral_const] at hc
  rw [hc]
  apply intervalIntegral.integral_congr
  intro t ht
  rw [uIcc_of_le hr.le] at ht
  by_cases ht0 : t = 0
  · simp [ht0]
  have htpos : 0 < t := lt_of_le_of_ne ht.1 (Ne.symm ht0)
  have hmf : Real.circleAverage f 0 t = f 0 := by
  {
    apply DiffContOnCl.circleAverage
    rw [abs_of_pos htpos]
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball 0 htpos.ne']
    exact hf.mono (Metric.closedBall_subset_ball (lt_of_le_of_lt ht.2 hrR))
  }
  simp only [hmf, Real.circleAverage_const]
}

lemma integral_closedBall_holomorphic {f : ℂ → ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R))
    (hr : 0 < r) (hrR : r < R) :
    ∫ z in Metric.closedBall (0 : ℂ) r, f z =
      volume.real (Metric.closedBall (0 : ℂ) r) • f 0 := by
{
  rw [← setIntegral_congr_set (ball_closedBall_ae_eq r),
    integral_ball_holomorphic hf hr hrR]
  congr 1
  exact congrArg ENNReal.toReal (measure_congr (ball_closedBall_ae_eq r))
}

lemma holomorphic_sq_submean {f : ℂ → ℂ} {R r : ℝ}
    (hf : DifferentiableOn ℂ f (Metric.ball (0 : ℂ) R))
    (hr : 0 < r) (hrR : r < R) :
    volume.real (Metric.closedBall (0 : ℂ) r) * ‖f 0‖^2 ≤
      ∫ z in Metric.closedBall (0 : ℂ) r, ‖f z‖^2 := by
{
  let K : Set ℂ := Metric.closedBall 0 r
  have hfc : ContinuousOn f K := hf.continuousOn.mono (Metric.closedBall_subset_ball hrR)
  have hfi : IntegrableOn f K := hfc.integrableOn_compact (isCompact_closedBall 0 r)
  have hf2i : IntegrableOn (fun z => ‖f z‖^2) K :=
    (hfc.norm.pow 2).integrableOn_compact (isCompact_closedBall 0 r)
  have hconst : IntegrableOn (fun _ : ℂ => ‖f 0‖^2) K :=
    integrableOn_const (isCompact_closedBall 0 r).measure_ne_top
  have hnonneg : 0 ≤ ∫ z in K, ‖f z - f 0‖^2 := integral_nonneg (fun _ => sq_nonneg _)
  have he : (fun z => ‖f z - f 0‖^2) =
      (fun z => ‖f z‖^2 - 2 * inner ℝ (f 0) (f z) + ‖f 0‖^2) := by
  {
    funext z
    rw [norm_sub_sq_real, real_inner_comm]
  }
  have hsub : IntegrableOn (fun z => ‖f z‖^2 - 2 * inner ℝ (f 0) (f z)) K :=
    hf2i.sub ((hfi.const_inner (f 0)).const_mul 2)
  have hinner : IntegrableOn (fun z => 2 * inner ℝ (f 0) (f z)) K :=
    (hfi.const_inner (f 0)).const_mul 2
  rw [he, integral_add hsub hconst, integral_sub hf2i hinner,
    integral_const_mul, integral_inner hfi, setIntegral_const,
    integral_closedBall_holomorphic hf hr hrR, real_inner_smul_right,
    real_inner_self_eq_norm_sq, smul_eq_mul] at hnonneg
  dsimp only [K] at hnonneg ⊢
  linarith
}

lemma integral_annulus_polar_step1 {f : ℂ → ℝ} {ε R : ℝ} (hε : 0 < ε)
    (hf : ContinuousOn f (Metric.closedBall 0 R \ Metric.ball 0 ε)) :
    IntegrableOn (fun p : ℝ × ℝ => p.1 • f (Complex.polarCoord.symm p))
      (Ioo ε R ×ˢ Ioo (-Real.pi) Real.pi) := by
{
  let g : ℝ × ℝ → ℝ := fun p => p.1 • f (Complex.polarCoord.symm p)
  refine (show IntegrableOn g (Icc ε R ×ˢ Icc (-Real.pi) Real.pi) from ?_).mono_set
    (prod_mono Ioo_subset_Icc_self Ioo_subset_Icc_self)
  apply ContinuousOn.integrableOn_compact (isCompact_Icc.prod isCompact_Icc)
  have hpolar : Continuous (fun p : ℝ × ℝ => Complex.polarCoord.symm p) := by
  {
    simp only [Complex.polarCoord_symm_apply]
    fun_prop
  }
  apply continuousOn_fst.smul (hf.comp hpolar.continuousOn ?_)
  intro p hp
  have hp0 : 0 ≤ p.1 := hε.le.trans hp.1.1
  simp only [mem_diff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right,
    Complex.norm_polarCoord_symm, abs_of_nonneg hp0, not_lt]
  exact ⟨hp.1.2, hp.1.1⟩
}

lemma integral_annulus_polar_step2 {f : ℂ → ℝ} {ε R : ℝ} (hε : 0 < ε) :
    ∫ z in Metric.ball (0 : ℂ) R \ Metric.closedBall 0 ε, f z =
      ∫ p in Ioo ε R ×ˢ Ioo (-Real.pi) Real.pi,
        p.1 • f (Complex.polarCoord.symm p) := by
{
  let s : Set ℂ := Metric.ball (0 : ℂ) R \ Metric.closedBall 0 ε
  have hs : MeasurableSet s :=
    (Metric.isOpen_ball.sdiff Metric.isClosed_closedBall).measurableSet
  let g : ℝ × ℝ → ℝ := fun p => p.1 • f (Complex.polarCoord.symm p)
  rw [← integral_indicator hs, ← Complex.integral_comp_polarCoord_symm, polarCoord_target]
  have heq : (fun p : ℝ × ℝ => p.1 • s.indicator f (Complex.polarCoord.symm p)) =ᶠ[
      ae (volume.restrict (Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi))]
    (Ioo ε R ×ˢ (univ : Set ℝ)).indicator g := by
  {
    filter_upwards [ae_restrict_mem (measurableSet_Ioi.prod measurableSet_Ioo)] with p hp
    have hp1 : 0 < p.1 := hp.1
    have hmem : Complex.polarCoord.symm p ∈ s ↔ p.1 ∈ Ioo ε R := by
    {
      simp only [s, mem_diff, Metric.mem_ball, Metric.mem_closedBall, dist_zero_right,
        Complex.norm_polarCoord_symm, abs_of_pos hp1, not_le, mem_Ioo, and_comm]
    }
    by_cases hr : p.1 ∈ Ioo ε R
    · rw [indicator_of_mem (hmem.mpr hr),
        indicator_of_mem (show p ∈ Ioo ε R ×ˢ (univ : Set ℝ) from ⟨hr, mem_univ _⟩)]
    · rw [indicator_of_notMem (mt hmem.mp hr),
        indicator_of_notMem (show p ∉ Ioo ε R ×ˢ (univ : Set ℝ) from fun h => hr h.1), smul_zero]
  }
  rw [integral_congr_ae heq, integral_indicator (measurableSet_Ioo.prod MeasurableSet.univ),
    Measure.restrict_restrict (measurableSet_Ioo.prod MeasurableSet.univ)]
  congr 2
  ext p
  simp only [mem_inter_iff, mem_prod, mem_Ioi, mem_Ioo, mem_univ, and_true]
  exact ⟨fun h => ⟨h.1, h.2.2⟩, fun h => ⟨h.1, hε.trans h.1.1, h.2⟩⟩
}

lemma circleAverage_real_eq_integral_neg_pi (f : ℂ → ℝ) (c : ℂ) (r : ℝ) :
    Real.circleAverage f c r =
      (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi, f (circleMap c r θ) := by
{
  rw [Real.circleAverage_eq_integral_add (-Real.pi)]
  rw [intervalIntegral.integral_comp_add_right (fun θ => f (circleMap c r θ)), smul_eq_mul]
  congr 2 <;> ring
}

lemma integral_annulus_polar {f : ℂ → ℝ} {ε R : ℝ} (hε : 0 < ε) (hεR : ε < R)
    (hf : ContinuousOn f (Metric.closedBall 0 R \ Metric.ball 0 ε)) :
    ∫ z in Metric.ball (0 : ℂ) R \ Metric.closedBall 0 ε, f z =
      ∫ r in ε..R, (2 * Real.pi * r) * Real.circleAverage f 0 r := by
{
  have hg := integral_annulus_polar_step1 hε hf
  rw [integral_annulus_polar_step2 hε, Measure.volume_eq_prod, setIntegral_prod _ hg]
  rw [intervalIntegral.integral_of_le hεR.le, integral_Ioc_eq_integral_Ioo]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro r _hr
  dsimp only
  rw [circleAverage_real_eq_integral_neg_pi,
    intervalIntegral.integral_of_le (neg_le_self Real.pi_pos.le),
    integral_Ioc_eq_integral_Ioo, ← mul_assoc]
  have he : (2 * Real.pi * r) * (2 * Real.pi)⁻¹ = r := by field_simp
  rw [he, ← integral_const_mul]
  apply setIntegral_congr_fun measurableSet_Ioo
  intro θ _hθ
  simp only [polar_symm_eq_circleMap, smul_eq_mul]
}

lemma circleAverage_re_sq_mul_deriv {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Real.circleAverage (fun z : ℂ => (z^2 * deriv h z).re) 0 ρ = 0 := by
{
  let g : ℂ → ℂ := fun z => z^2 * deriv h z
  have hg : DifferentiableOn ℂ g (Metric.ball 0 1) :=
    (differentiableOn_id.pow 2).mul (hh.deriv Metric.isOpen_ball)
  have hgi : IntervalIntegrable (fun θ => g (circleMap 0 ρ θ)) volume 0 (2 * Real.pi) := by
  {
    apply Continuous.intervalIntegrable
    apply hg.continuousOn.comp_continuous (continuous_circleMap 0 ρ)
    intro θ
    simp [circleMap, abs_of_pos hρ, hρ1]
  }
  have havg : Real.circleAverage g 0 ρ = 0 := by
  {
    have hm : Real.circleAverage g 0 ρ = g 0 := by
    {
      apply DiffContOnCl.circleAverage
      rw [abs_of_pos hρ]
      apply DifferentiableOn.diffContOnCl
      rw [closure_ball 0 hρ.ne']
      exact hg.mono (Metric.closedBall_subset_ball hρ1)
    }
    simpa [g] using hm
  }
  have hcomm : Real.circleAverage (fun z => Complex.reCLM (g z)) 0 ρ =
      Complex.reCLM (Real.circleAverage g 0 ρ) := by
  {
    simp only [Real.circleAverage_def, smul_eq_mul, map_smul]
    congr 1
    exact Complex.reCLM.intervalIntegral_comp_comm hgi
  }
  simpa [g, havg] using hcomm
}

lemma sphere_singular_cross_eq {h : ℂ → ℂ} {ρ : ℝ} {z : ℂ}
    (hz : z ∈ Metric.sphere (0 : ℂ) ρ) :
    ‖(z^2)⁻¹‖^2 - 2 * inner ℝ ((z^2)⁻¹) (deriv h z) =
      (ρ^4)⁻¹ - 2 * (ρ^4)⁻¹ * (z^2 * deriv h z).re := by
{
  have hn : ‖z‖ = ρ := by simpa using hz
  have hnsq : Complex.normSq z = ρ^2 := by rw [Complex.normSq_eq_norm_sq, hn]
  have hinv2 : (z^2)⁻¹ = ((ρ^4)⁻¹ : ℝ) • conj (z^2) := by
  {
    rw [Complex.inv_def, map_pow, map_pow, hnsq, Complex.real_smul]
    push_cast
    ring
  }
  have hnorm : ‖(z^2)⁻¹‖^2 = (ρ^4)⁻¹ := by
  {
    rw [norm_inv, norm_pow, hn, ← inv_pow]
    ring
  }
  have hinner : inner ℝ ((z^2)⁻¹) (deriv h z) = (ρ^4)⁻¹ * (z^2 * deriv h z).re := by
  {
    rw [hinv2, real_inner_smul_left]
    congr 1
    simp only [Complex.inner, RingHomCompTriple.comp_apply, RingHom.id_apply]
    rw [mul_comm]
  }
  rw [hnorm, hinner]
  ring
}

lemma circleAverage_singular_cross {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1)) {ρ : ℝ} (hρ : 0 < ρ) (hρ1 : ρ < 1) :
    Real.circleAverage (fun z : ℂ => ‖(z^2)⁻¹‖^2 - 2 * inner ℝ ((z^2)⁻¹) (deriv h z)) 0 ρ =
      (ρ^4)⁻¹ := by
{
  have hcongr : Real.circleAverage (fun z : ℂ => ‖(z^2)⁻¹‖^2 - 2 * inner ℝ ((z^2)⁻¹) (deriv h z)) 0 ρ =
      Real.circleAverage (fun z : ℂ => (ρ^4)⁻¹ - 2 * (ρ^4)⁻¹ * (z^2 * deriv h z).re) 0 ρ := by
  {
    apply Real.circleAverage_congr_sphere
    intro z hz
    rw [abs_of_pos hρ] at hz
    exact sphere_singular_cross_eq hz
  }
  rw [hcongr]
  have hg : Continuous (fun θ : ℝ => ((circleMap 0 ρ θ)^2 * deriv h (circleMap 0 ρ θ)).re) := by
  {
    apply Complex.continuous_re.comp
    apply (((differentiableOn_id.pow 2).mul (hh.deriv Metric.isOpen_ball)).continuousOn).comp_continuous
      (continuous_circleMap 0 ρ)
    intro θ
    simp [circleMap, abs_of_pos hρ, hρ1]
  }
  have hzero := circleAverage_re_sq_mul_deriv hh hρ hρ1
  simp only [Real.circleAverage_def, smul_eq_mul] at hzero ⊢
  rw [intervalIntegral.integral_sub intervalIntegrable_const
    ((hg.intervalIntegrable _ _).const_mul _),
    intervalIntegral.integral_const, intervalIntegral.integral_const_mul]
  have hint0 : ∫ x in 0..2 * Real.pi, ((circleMap 0 ρ x)^2 * deriv h (circleMap 0 ρ x)).re = 0 := by
  {
    have h2pi : (2 * Real.pi)⁻¹ ≠ 0 := inv_ne_zero (mul_ne_zero two_ne_zero Real.pi_ne_zero)
    exact (mul_eq_zero.mp hzero).resolve_left h2pi
  }
  rw [hint0, mul_zero, sub_zero, sub_zero, smul_eq_mul]
  have h2pi : 2 * Real.pi ≠ 0 := mul_ne_zero two_ne_zero Real.pi_ne_zero
  field_simp
}

lemma integral_inv_cube_eq_sub {ε r : ℝ} (hε : 0 < ε) (hεr : ε < r) :
    ∫ ρ in ε..r, 2 * Real.pi * (ρ^3)⁻¹ =
      (-Real.pi * (r^2)⁻¹) - (-Real.pi * (ε^2)⁻¹) := by
{
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
  · intro ρ hρ
    rw [uIcc_of_le hεr.le] at hρ
    have hρ0 : ρ ≠ 0 := (lt_of_lt_of_le hε hρ.1).ne'
    have hd := ((hasDerivAt_pow 2 ρ).inv (pow_ne_zero 2 hρ0)).const_mul (-Real.pi)
    have heq : 2 * Real.pi * (ρ ^ 3)⁻¹ = -Real.pi * (-(↑2 * ρ ^ (2 - 1)) / (ρ ^ 2) ^ 2) := by
    {
      have h1 : (ρ ^ 3)⁻¹ * ρ ^ 4 = ρ := by
        rw [show ρ ^ 4 = ρ ^ 3 * ρ by ring, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero 3 hρ0), one_mul]
      have h2 : (ρ ^ 2) ^ 2 = ρ ^ 4 := by ring
      norm_num
      rw [h2, div_eq_mul_inv]
      apply mul_right_cancel₀ (pow_ne_zero 4 hρ0)
      linear_combination (2 * Real.pi) * h1 - (2 * Real.pi * ρ) * inv_mul_cancel₀ (pow_ne_zero 4 hρ0)
    }
    exact heq ▸ hd
  · apply ContinuousOn.intervalIntegrable
    rw [uIcc_of_le hεr.le]
    exact continuousOn_const.mul ((continuousOn_id.pow 3).inv₀
      (fun ρ hρ => pow_ne_zero 3 (lt_of_lt_of_le hε hρ.1).ne'))
}

lemma integral_annulus_singular_cross {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    {ε r : ℝ} (hε : 0 < ε) (hεr : ε < r) (hr1 : r < 1) :
    ∫ z in Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε,
      (‖(z^2)⁻¹‖^2 - 2 * inner ℝ ((z^2)⁻¹) (deriv h z)) =
      Real.pi * ((ε^2)⁻¹ - (r^2)⁻¹) := by
{
  let K : Set ℂ := Metric.closedBall 0 r \ Metric.ball 0 ε
  have hK0 : ∀ z ∈ K, z ≠ 0 := by
  {
    intro z hz he
    simp [K, he, hε] at hz
  }
  have hf : ContinuousOn (fun z : ℂ => ‖(z^2)⁻¹‖^2 - 2 * inner ℝ ((z^2)⁻¹) (deriv h z)) K := by
  {
    have hd : ContinuousOn (deriv h) K :=
      (hh.deriv Metric.isOpen_ball).continuousOn.mono
        (diff_subset.trans (Metric.closedBall_subset_ball hr1))
    have hi : ContinuousOn (fun z : ℂ => (z^2)⁻¹) K :=
      (continuousOn_id.pow 2).inv₀ (fun z hz => pow_ne_zero 2 (hK0 z hz))
    exact (hi.norm.pow 2).sub (continuousOn_const.mul (hi.inner hd))
  }
  rw [integral_annulus_polar hε hεr hf]
  have hcongr : ∫ ρ in ε..r, (2 * Real.pi * ρ) *
      Real.circleAverage (fun z : ℂ => ‖(z^2)⁻¹‖^2 - 2 * inner ℝ ((z^2)⁻¹) (deriv h z)) 0 ρ =
      ∫ ρ in ε..r, 2 * Real.pi * (ρ^3)⁻¹ := by
  {
    apply intervalIntegral.integral_congr
    intro ρ hρ
    rw [uIcc_of_le hεr.le] at hρ
    have hρ0 : 0 < ρ := lt_of_lt_of_le hε hρ.1
    dsimp only
    rw [circleAverage_singular_cross hh hρ0 (lt_of_le_of_lt hρ.2 hr1)]
    have hne : ρ ≠ 0 := hρ0.ne'
    field_simp
  }
  rw [hcongr, integral_inv_cube_eq_sub hε hεr]
  ring
}

lemma hasDerivAt_H_punctured {h H : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹ + h z)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) 1 \ {0}) :
    HasDerivAt H (deriv h z - (z^2)⁻¹) z := by
{
  have hopen : IsOpen (Metric.ball (0 : ℂ) 1 \ {0}) :=
    Metric.isOpen_ball.sdiff isClosed_singleton
  have heq : H =ᶠ[𝓝 z] fun w => w⁻¹ + h w := by
  {
    filter_upwards [hopen.mem_nhds hz] with w hw
    exact hdef w hw.1 hw.2
  }
  have hdh := ((hh z hz.1).differentiableAt (Metric.isOpen_ball.mem_nhds hz.1)).hasDerivAt
  have hd := (hasDerivAt_inv (show z ≠ 0 from hz.2)).add hdh
  rw [ neg_add_eq_sub] at hd
  exact hd.congr_of_eventuallyEq heq
}

lemma integral_annulus_norm_deriv_H_sq {h H : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹ + h z)
    {ε r : ℝ} (hε : 0 < ε) (hεr : ε < r) (hr1 : r < 1) :
    ∫ z in Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε, ‖deriv H z‖^2 =
      (∫ z in Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε, ‖deriv h z‖^2) +
        Real.pi * ((ε^2)⁻¹ - (r^2)⁻¹) := by
{
  let A : Set ℂ := Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε
  let K : Set ℂ := Metric.closedBall 0 r \ Metric.ball 0 ε
  have hAK : A ⊆ K := diff_subset_diff Metric.ball_subset_closedBall Metric.ball_subset_closedBall
  have hK0 : ∀ z ∈ K, z ≠ 0 := by
  {
    intro z hz he
    simp [K, he, hε] at hz
  }
  have hd : ContinuousOn (deriv h) K :=
    (hh.deriv Metric.isOpen_ball).continuousOn.mono
      (diff_subset.trans (Metric.closedBall_subset_ball hr1))
  have hi : ContinuousOn (fun z : ℂ => (z^2)⁻¹) K :=
    (continuousOn_id.pow 2).inv₀ (fun z hz => pow_ne_zero 2 (hK0 z hz))
  have hint1 : IntegrableOn (fun z => ‖deriv h z‖^2) A :=
    ((hd.norm.pow 2).integrableOn_compact
      (isCompact_closedBall 0 r |>.diff Metric.isOpen_ball)).mono_set hAK
  have hint2 : IntegrableOn (fun z => ‖(z^2)⁻¹‖^2 - 2 * inner ℝ ((z^2)⁻¹) (deriv h z)) A :=
    (((hi.norm.pow 2).sub (continuousOn_const.mul (hi.inner hd))).integrableOn_compact
      (isCompact_closedBall 0 r |>.diff Metric.isOpen_ball)).mono_set hAK
  have hcongr : ∫ z in A, ‖deriv H z‖^2 =
      ∫ z in A, (‖deriv h z‖^2 + (‖(z^2)⁻¹‖^2 - 2 * inner ℝ ((z^2)⁻¹) (deriv h z))) := by
  {
    apply setIntegral_congr_fun (Metric.isOpen_ball.sdiff Metric.isClosed_closedBall).measurableSet
    intro z hz
    have hz' : z ∈ Metric.ball (0 : ℂ) 1 \ {0} :=
      ⟨Metric.ball_subset_ball hr1.le hz.1, hK0 z (hAK hz)⟩
    dsimp only
    rw [(hasDerivAt_H_punctured hh hdef hz').deriv, norm_sub_sq_real, real_inner_comm]
    ring
  }
  rw [hcongr, integral_add hint1 hint2, integral_annulus_singular_cross hh hε hεr hr1]
}

lemma frontier_annulus_subset {ε r : ℝ} :
    frontier (Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε) ⊆
      Metric.sphere 0 ε ∪ Metric.sphere 0 r := by
{
  intro z hz
  have hopen : IsOpen (Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε) :=
    Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  rw [hopen.frontier_eq] at hz
  have hcl : closure (Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε) ⊆
      Metric.closedBall 0 r \ Metric.ball 0 ε :=
    closure_minimal (diff_subset_diff Metric.ball_subset_closedBall Metric.ball_subset_closedBall)
      (Metric.isClosed_closedBall.sdiff Metric.isOpen_ball)
  have hz1 := hcl hz.1
  have hz2 := hz.2
  simp only [mem_diff, Metric.mem_closedBall, Metric.mem_ball, dist_zero_right,
    not_lt, not_and_or, not_le] at hz1 hz2
  simp only [mem_union, Metric.mem_sphere, dist_zero_right]
  rcases hz2 with hge | hle
  · exact Or.inr (le_antisymm hz1.1 hge)
  · exact Or.inl (le_antisymm hle hz1.2)
}

lemma closure_annulus_subset_punctured_ball {ε r : ℝ} (hε : 0 < ε) (hr1 : r < 1) :
    closure (Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε) ⊆ Metric.ball 0 1 \ {0} := by
{
  refine (closure_minimal (diff_subset_diff Metric.ball_subset_closedBall Metric.ball_subset_closedBall)
    (Metric.isClosed_closedBall.sdiff Metric.isOpen_ball)).trans
    (fun w hw => ⟨Metric.closedBall_subset_ball hr1 hw.1, ?_⟩)
  intro hw0
  rw [mem_singleton_iff] at hw0
  simp [hw0, hε] at hw
}

lemma exp_norm_harmonic_aux (c a b : ℂ) :
    (c * a + conj c * b).re = (c * (a + conj b)).re := by
{
  rw [mul_add, Complex.add_re, Complex.add_re]
  congr 1
  have hconj : conj (conj c * b) = c * conj b := by simp
  rw [← hconj, Complex.conj_re]
}

lemma harmonic_max_principle_annulus {f g : ℂ → ℂ} {ε r M : ℝ}
    (hε : 0 < ε) (hr1 : r < 1)
    (hf : DifferentiableOn ℂ f (Metric.ball 0 1 \ {0}))
    (hg : DifferentiableOn ℂ g (Metric.ball 0 1 \ {0}))
    (hM : ∀ w ∈ Metric.sphere (0 : ℂ) ε ∪ Metric.sphere 0 r, ‖f w + conj (g w)‖ ≤ M)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε) :
    ‖f z + conj (g z)‖ ≤ M := by
{
  let U : Set ℂ := Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε
  let u₀ : ℂ := f z + conj (g z)
  let c : ℂ := if u₀ = 0 then 1 else conj u₀ / ‖u₀‖
  have hc_norm : ‖c‖ = 1 := by
  {
    dsimp only [c]
    split_ifs with h0
    · simp
    · rw [norm_div, RCLike.norm_conj, Complex.norm_real, Real.norm_of_nonneg (norm_nonneg _),
        div_self (norm_ne_zero_iff.mpr h0)]
  }
  have hc_re : (c * u₀).re = ‖u₀‖ := by
  {
    dsimp only [c]
    split_ifs with h0
    · simp [h0]
    · have hn : (‖u₀‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr h0)
      have he : conj u₀ / (‖u₀‖ : ℂ) * u₀ = (‖u₀‖ : ℂ) := by
        rw [div_mul_eq_mul_div, Complex.conj_mul']; field_simp [hn]
      rw [he, Complex.ofReal_re]
  }
  let Φ : ℂ → ℂ := fun w => Complex.exp (c * f w + conj c * g w)
  have hΦ_norm (w : ℂ) : ‖Φ w‖ ≤ Real.exp ‖f w + conj (g w)‖ := by
  {
    simp only [Φ, Complex.norm_exp, exp_norm_harmonic_aux]
    exact Real.exp_le_exp.mpr ((Complex.re_le_norm _).trans (by rw [norm_mul, hc_norm, one_mul]))
  }
  have hΦd : DiffContOnCl ℂ Φ U :=
    ((((hf.const_mul c).add (hg.const_mul (conj c))).cexp).mono
      (closure_annulus_subset_punctured_ball hε hr1)).diffContOnCl
  have hbound := Complex.norm_le_of_forall_mem_frontier_norm_le
    (Metric.isBounded_ball.subset diff_subset) hΦd
    (fun w hw => (hΦ_norm w).trans (Real.exp_le_exp.mpr (hM w (frontier_annulus_subset hw))))
    (subset_closure hz)
  have hΦz : ‖Φ z‖ = Real.exp ‖u₀‖ := by
    simp only [Φ, Complex.norm_exp, exp_norm_harmonic_aux, u₀, hc_re]
  exact Real.exp_le_exp.mp (hΦz ▸ hbound)
}

def shearCLM (b : ℂ) : ℂ →L[ℝ] ℂ :=
  ContinuousLinearMap.id ℝ ℂ -
    (ContinuousLinearMap.mulLeftRight ℝ ℂ b 1).comp Complex.conjCLE.toContinuousLinearMap

@[simp] lemma shearCLM_apply (b w : ℂ) : shearCLM b w = w - b * conj w := by
{
  simp [shearCLM]
}

lemma det_shearCLM (b : ℂ) :
    LinearMap.det (shearCLM b).toLinearMap = 1 - ‖b‖^2 := by
{
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [shearCLM, LinearMap.toMatrix_apply, Complex.coe_basisOneI,
    Complex.coe_basisOneI_repr, ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
  ring
}

lemma shearCLM_injective {b : ℂ} (hb : ‖b‖ < 1) : Function.Injective (shearCLM b) := by
{
  intro w₁ w₂ he
  have hsub : shearCLM b (w₁ - w₂) = 0 := by rw [map_sub, he, sub_self]
  rw [shearCLM_apply, sub_eq_zero] at hsub
  have hn : ‖w₁ - w₂‖ = ‖b‖ * ‖w₁ - w₂‖ := by
    simpa only [norm_mul, ← map_sub, RCLike.norm_conj] using congrArg norm hsub
  have hzero : ‖w₁ - w₂‖ = 0 := by nlinarith [norm_nonneg (w₁ - w₂)]
  exact sub_eq_zero.mp (norm_eq_zero.mp hzero)
}

lemma det_fderiv_complex_at {f : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℂ f z) :
    LinearMap.det (fderiv ℝ f z).toLinearMap = ‖deriv f z‖^2 := by
{
  rw [(hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv,
    ← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr,
    ← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
}

lemma det_fderiv_shearCLM_comp {f : ℂ → ℂ} {b z : ℂ} (hd : DifferentiableAt ℂ f z) :
    LinearMap.det (fderiv ℝ (fun w => shearCLM b (f w)) z).toLinearMap =
      (1 - ‖b‖^2) * ‖deriv f z‖^2 := by
{
  have hfD : HasFDerivAt (fun w => shearCLM b (f w))
      ((shearCLM b).comp (fderiv ℝ f z)) z :=
    (shearCLM b).hasFDerivAt.comp z (hd.restrictScalars ℝ).hasFDerivAt
  rw [hfD.fderiv, ContinuousLinearMap.coe_comp, LinearMap.det_comp,
    det_shearCLM, det_fderiv_complex_at hd]
}

def dslope2 (h : ℂ → ℂ) : ℂ → ℂ := dslope (dslope h 0) 0

lemma differentiableOn_dslope2 {h : ℂ → ℂ} (hh : DifferentiableOn ℂ h (Metric.ball 0 1)) :
    DifferentiableOn ℂ (dslope2 h) (Metric.ball 0 1) := by
{
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hd1 : DifferentiableOn ℂ (dslope h 0) (Metric.ball 0 1) :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds h0)).mpr hh
  exact (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds h0)).mpr hd1
}

lemma h_sub_eq_linear_add_sq_dslope2 (h : ℂ → ℂ) (z : ℂ) :
    h z - h 0 = deriv h 0 * z + z^2 * dslope2 h z := by
{
  have h1 : z * dslope h 0 z = h z - h 0 := by
    simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope h 0 z
  have h2 : z * dslope2 h z = dslope h 0 z - deriv h 0 := by
    simpa only [dslope2, sub_zero, smul_eq_mul, dslope_same] using sub_smul_dslope (dslope h 0) 0 z
  linear_combination -h1 - z * h2
}

lemma shearCLM_H_sphere_inner {h H : ℂ → ℂ}
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹ + h z)
    {ε : ℝ} (hε : 0 < ε) (hε1 : ε < 1) {w : ℂ} (hw : w ∈ Metric.sphere (0 : ℂ) ε) :
    shearCLM ((ε^2 : ℂ) * deriv h 0) (H w - h 0) =
      w⁻¹ + w^2 * dslope2 h w - ((ε^2 : ℂ) * deriv h 0) * conj (h w - h 0) := by
{
  have hw_norm : ‖w‖ = ε := by simpa using hw
  have hw0 : w ≠ 0 := norm_pos_iff.mp (hw_norm.symm ▸ hε)
  have hw_ball : w ∈ Metric.ball (0 : ℂ) 1 := by simpa [hw_norm] using hε1
  have hinv : (ε^2 : ℂ) * conj (w⁻¹) = w := by
  {
    have hmul : w * conj w = (ε^2 : ℂ) := by rw [Complex.mul_conj', hw_norm]
    rw [← hmul, map_inv₀, mul_inv_cancel_right₀ (by simpa using hw0)]
  }
  have h1 := h_sub_eq_linear_add_sq_dslope2 h w
  rw [shearCLM_apply, hdef w hw_ball hw0, add_sub_assoc, map_add]
  linear_combination h1 - deriv h 0 * hinv
}

lemma shearCLM_eq_add_conj (b w : ℂ) :
    shearCLM b w = w + conj (-conj b * w) := by
{
  simp [shearCLM_apply, sub_eq_add_neg]
}

lemma norm_shearCLM_H_sphere_inner_le {h H : ℂ → ℂ}
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹ + h z)
    {ε r C₁ C₂ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hr1 : r < 1) (hC₁ : 0 ≤ C₁)
    (h1 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖dslope h 0 w‖ ≤ C₁)
    (h2 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖dslope2 h w‖ ≤ C₂)
    {w : ℂ} (hw : w ∈ Metric.sphere (0 : ℂ) ε) :
    ‖shearCLM ((ε^2 : ℂ) * deriv h 0) (H w - h 0)‖ ≤
      ε⁻¹ + (C₂ + ‖deriv h 0‖ * C₁) * ε^2 := by
{
  have hw_norm : ‖w‖ = ε := by simpa using hw
  have hw_cb : w ∈ Metric.closedBall (0 : ℂ) r := by simp [hw_norm, hεr.le]
  rw [shearCLM_H_sphere_inner hdef hε (hεr.trans hr1) hw]
  have ht1 := norm_sub_le (w⁻¹ + w^2 * dslope2 h w) (((ε^2 : ℂ) * deriv h 0) * conj (h w - h 0))
  have ht2 := norm_add_le (w⁻¹) (w^2 * dslope2 h w)
  have hn1 : ‖w⁻¹‖ = ε⁻¹ := by rw [norm_inv, hw_norm]
  have hn2 : ‖w^2 * dslope2 h w‖ ≤ C₂ * ε^2 := by
  {
    rw [norm_mul, norm_pow, hw_norm, mul_comm]
    exact mul_le_mul_of_nonneg_right (h2 w hw_cb) (sq_nonneg ε)
  }
  have hsub : ‖h w - h 0‖ ≤ C₁ := by
  {
    have hf : h w - h 0 = w * dslope h 0 w := by
      simpa only [sub_zero, smul_eq_mul] using (sub_smul_dslope h 0 w).symm
    rw [hf, norm_mul, hw_norm]
    have hle1 : ε ≤ 1 := (hεr.trans hr1).le
    nlinarith [h1 w hw_cb]
  }
  have hn3 : ‖((ε^2 : ℂ) * deriv h 0) * conj (h w - h 0)‖ ≤ ‖deriv h 0‖ * C₁ * ε^2 := by
  {
    rw [norm_mul, norm_mul, Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg hε.le,
      RCLike.norm_conj]
    have hmul := mul_le_mul_of_nonneg_left hsub (mul_nonneg (sq_nonneg ε) (norm_nonneg (deriv h 0)))
    linarith
  }
  linarith
}

lemma norm_shearCLM_H_sphere_outer_le {h H : ℂ → ℂ}
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹ + h z)
    {ε r C₁ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hr1 : r < 1) (hC₁ : 0 ≤ C₁)
    (h1 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖dslope h 0 w‖ ≤ C₁)
    {w : ℂ} (hw : w ∈ Metric.sphere (0 : ℂ) r) :
    ‖shearCLM ((ε^2 : ℂ) * deriv h 0) (H w - h 0)‖ ≤
      (1 + ‖deriv h 0‖) * (r⁻¹ + C₁) := by
{
  have hr : 0 < r := hε.trans hεr
  have hw_norm : ‖w‖ = r := by simpa using hw
  have hw0 : w ≠ 0 := norm_pos_iff.mp (hw_norm.symm ▸ hr)
  have hw_ball : w ∈ Metric.ball (0 : ℂ) 1 := by simpa [hw_norm] using hr1
  have hw_cb : w ∈ Metric.closedBall (0 : ℂ) r := Metric.sphere_subset_closedBall hw
  have hHw : H w - h 0 = w⁻¹ + w * dslope h 0 w := by
  {
    rw [hdef w hw_ball hw0, add_sub_assoc]
    congr 1
    simpa only [sub_zero, smul_eq_mul] using (sub_smul_dslope h 0 w).symm
  }
  have hnH : ‖H w - h 0‖ ≤ r⁻¹ + C₁ := by
  {
    rw [hHw]
    refine (norm_add_le _ _).trans ?_
    rw [norm_inv, norm_mul, hw_norm]
    have hle1 : r ≤ 1 := hr1.le
    nlinarith [h1 w hw_cb]
  }
  rw [shearCLM_apply]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_mul, norm_mul, Complex.norm_pow, Complex.norm_real, Real.norm_of_nonneg hε.le,
    RCLike.norm_conj]
  have hε2 : ε^2 ≤ 1 := by nlinarith [hεr.trans hr1]
  have hm1 : ε^2 * ‖deriv h 0‖ * ‖H w - h 0‖ ≤ 1 * ‖deriv h 0‖ * ‖H w - h 0‖ :=
    mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hε2 (norm_nonneg _)) (norm_nonneg _)
  have hm2 : (1 + ‖deriv h 0‖) * ‖H w - h 0‖ ≤ (1 + ‖deriv h 0‖) * (r⁻¹ + C₁) :=
    mul_le_mul_of_nonneg_left hnH (by positivity)
  linarith
}

lemma norm_shearCLM_H_annulus_le {h H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹ + h z)
    {ε r C₁ C₂ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hr1 : r < 1)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h1 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖dslope h 0 w‖ ≤ C₁)
    (h2 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖dslope2 h w‖ ≤ C₂)
    (hout : (1 + ‖deriv h 0‖) * (r⁻¹ + C₁) ≤ ε⁻¹)
    {z : ℂ} (hz : z ∈ Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε) :
    ‖shearCLM ((ε^2 : ℂ) * deriv h 0) (H z - h 0)‖ ≤
      ε⁻¹ + (C₂ + ‖deriv h 0‖ * C₁) * ε^2 := by
{
  let b : ℂ := (ε^2 : ℂ) * deriv h 0
  let f : ℂ → ℂ := fun w => H w - h 0
  let g : ℂ → ℂ := fun w => -conj b * f w
  have hf : DifferentiableOn ℂ f (Metric.ball 0 1 \ {0}) := hH.sub_const (h 0)
  have hg : DifferentiableOn ℂ g (Metric.ball 0 1 \ {0}) := hf.const_mul (-conj b)
  have hnonneg : 0 ≤ (C₂ + ‖deriv h 0‖ * C₁) * ε^2 := by positivity
  rw [shearCLM_eq_add_conj]
  apply harmonic_max_principle_annulus hε hr1 hf hg ?_ hz
  intro w hw
  rw [← shearCLM_eq_add_conj]
  rcases hw with hw | hw
  · exact norm_shearCLM_H_sphere_inner_le hdef hε hεr hr1 hC₁ h1 h2 hw
  · exact (norm_shearCLM_H_sphere_outer_le hdef hε hεr hr1 hC₁ h1 hw).trans (by linarith)
}

lemma annulus_subset_punctured_unit_ball {ε r : ℝ} (hε : 0 < ε) (hr1 : r < 1) :
    Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε ⊆ Metric.ball (0 : ℂ) 1 \ {0} := by
{
  intro z hz
  refine ⟨Metric.ball_subset_ball hr1.le hz.1, fun hz0 => ?_⟩
  rw [mem_singleton_iff] at hz0
  simp [hz0, hε.le] at hz
}

lemma lintegral_shearCLM_H_annulus_le {h H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹ + h z)
    (hHi : InjOn H (Metric.ball 0 1 \ {0}))
    {ε r C₁ C₂ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hr1 : r < 1)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h1 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖dslope h 0 w‖ ≤ C₁)
    (h2 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖dslope2 h w‖ ≤ C₂)
    (hout : (1 + ‖deriv h 0‖) * (r⁻¹ + C₁) ≤ ε⁻¹)
    (hb1 : ε^2 * ‖deriv h 0‖ < 1) :
    (∫⁻ z in Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε,
      ENNReal.ofReal ((1 - (ε^2 * ‖deriv h 0‖)^2) * ‖deriv H z‖^2)) ≤
      volume (Metric.closedBall (0 : ℂ) (ε⁻¹ + (C₂ + ‖deriv h 0‖ * C₁) * ε^2)) := by
{
  let A : Set ℂ := Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε
  let b : ℂ := (ε^2 : ℂ) * deriv h 0
  let u : ℂ → ℂ := fun z => shearCLM b (H z - h 0)
  have hb_norm : ‖b‖ = ε^2 * ‖deriv h 0‖ := by
  {
    simp [b, Complex.norm_real, Real.norm_of_nonneg hε.le]
  }
  have hb_lt : ‖b‖ < 1 := hb_norm.symm ▸ hb1
  have hA_open : IsOpen A := Metric.isOpen_ball.sdiff Metric.isClosed_closedBall
  have hA_sub := annulus_subset_punctured_unit_ball hε hr1
  have hu_inj : InjOn u A := fun z₁ hz₁ z₂ hz₂ he =>
    hHi (hA_sub hz₁) (hA_sub hz₂) (sub_left_inj.mp (shearCLM_injective hb_lt he))
  have hdH (z : ℂ) (hz : z ∈ A) : DifferentiableAt ℂ (fun w => H w - h 0) z :=
    ((hH z (hA_sub hz)).differentiableAt
      ((Metric.isOpen_ball.sdiff isClosed_singleton).mem_nhds (hA_sub hz))).sub_const (h 0)
  have hu_fderiv (z : ℂ) (hz : z ∈ A) : HasFDerivWithinAt u (fderiv ℝ u z) A z :=
    ((shearCLM b).hasFDerivAt.comp z ((hdH z hz).restrictScalars ℝ).hasFDerivAt).differentiableAt.hasFDerivAt.hasFDerivWithinAt
  have harea := lintegral_abs_det_fderiv_eq_addHaar_image volume hA_open.measurableSet hu_fderiv hu_inj
  have hdet : ∀ z ∈ A, ENNReal.ofReal ((1 - (ε^2 * ‖deriv h 0‖)^2) * ‖deriv H z‖^2) =
      ENNReal.ofReal |LinearMap.det (fderiv ℝ u z).toLinearMap| := by
  {
    intro z hz
    have h1m : 0 ≤ 1 - ‖b‖^2 := by nlinarith [norm_nonneg b]
    rw [det_fderiv_shearCLM_comp (hdH z hz), deriv_sub_const, abs_of_nonneg (mul_nonneg h1m (sq_nonneg _)), hb_norm]
  }
  rw [setLIntegral_congr_fun hA_open.measurableSet hdet, harea]
  exact measure_mono (fun _ ⟨z, hz, hw⟩ => hw ▸ (Metric.mem_closedBall.mpr
    ((dist_zero_right _).trans_le (norm_shearCLM_H_annulus_le hH hdef hε hεr hr1 hC₁ hC₂ h1 h2 hout hz))))
}

lemma annulus_area_ineq {h H : ℂ → ℂ}
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹ + h z)
    (hHi : InjOn H (Metric.ball 0 1 \ {0}))
    {ε r C₁ C₂ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hr1 : r < 1)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h1 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖dslope h 0 w‖ ≤ C₁)
    (h2 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖dslope2 h w‖ ≤ C₂)
    (hout : (1 + ‖deriv h 0‖) * (r⁻¹ + C₁) ≤ ε⁻¹)
    (hb1 : ε^2 * ‖deriv h 0‖ < 1) :
    (1 - (ε^2 * ‖deriv h 0‖)^2) *
      ∫ z in Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε, ‖deriv H z‖^2 ≤
      Real.pi * (ε⁻¹ + (C₂ + ‖deriv h 0‖ * C₁) * ε^2)^2 := by
{
  let A : Set ℂ := Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε
  let R_ε : ℝ := ε⁻¹ + (C₂ + ‖deriv h 0‖ * C₁) * ε^2
  have hR_pos : 0 < R_ε := by positivity
  have h1m : 0 ≤ 1 - (ε^2 * ‖deriv h 0‖)^2 := by
    nlinarith [mul_nonneg (sq_nonneg ε) (norm_nonneg (deriv h 0))]
  have hintH : IntegrableOn (fun z => (1 - (ε^2 * ‖deriv h 0‖)^2) * ‖deriv H z‖^2) A := by
  {
    let K : Set ℂ := Metric.closedBall 0 r \ Metric.ball 0 ε
    have hAK : A ⊆ K := diff_subset_diff Metric.ball_subset_closedBall Metric.ball_subset_closedBall
    have hKsub : K ⊆ Metric.ball (0 : ℂ) 1 \ {0} := fun z hz =>
      ⟨Metric.closedBall_subset_ball hr1 hz.1, fun hz0 => by
        rw [mem_singleton_iff] at hz0; simp [K, hz0, hε] at hz⟩
    have hd : ContinuousOn (fun z => ‖deriv H z‖^2) K :=
      (((hH.deriv (Metric.isOpen_ball.sdiff isClosed_singleton)).continuousOn.mono hKsub).norm.pow 2)
    exact ((hd.const_mul _).integrableOn_compact ((isCompact_closedBall 0 r).diff Metric.isOpen_ball)).mono_set hAK
  }
  have hle : ENNReal.ofReal ((1 - (ε^2 * ‖deriv h 0‖)^2) * ∫ z in A, ‖deriv H z‖^2) ≤
      volume (Metric.closedBall (0 : ℂ) R_ε) := by
  {
    rw [← integral_const_mul, ofReal_integral_eq_lintegral_ofReal hintH
      (ae_of_all _ (fun z => mul_nonneg h1m (sq_nonneg _)))]
    exact lintegral_shearCLM_H_annulus_le hH hdef hHi hε hεr hr1 hC₁ hC₂ h1 h2 hout hb1
  }
  have hvol : (volume (Metric.closedBall (0 : ℂ) R_ε)).toReal = Real.pi * R_ε^2 := by
  {
    rw [Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hR_pos.le, ENNReal.coe_toReal]
    exact mul_comm _ _
  }
  have htoReal := ENNReal.toReal_mono (isCompact_closedBall (0 : ℂ) R_ε).measure_ne_top hle
  rwa [ENNReal.toReal_ofReal (mul_nonneg h1m (integral_nonneg (fun _ => sq_nonneg _))), hvol] at htoReal
}

lemma integral_closedBall_le_annulus_add_small {h : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    {ε r D₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hr1 : r < 1)
    (hD : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖deriv h w‖^2 ≤ D₀) :
    (∫ z in Metric.closedBall 0 r, ‖deriv h z‖^2) - Real.pi * ε^2 * D₀ ≤
      ∫ z in Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε, ‖deriv h z‖^2 := by
{
  let A : Set ℂ := Metric.ball (0 : ℂ) r \ Metric.closedBall 0 ε
  let E : Set ℂ := Metric.closedBall (0 : ℂ) ε
  have hcont : ContinuousOn (fun z => ‖deriv h z‖^2) (Metric.closedBall 0 r) :=
    ((hh.deriv Metric.isOpen_ball).continuousOn.mono (Metric.closedBall_subset_ball hr1)).norm.pow 2
  have hintR : IntegrableOn (fun z => ‖deriv h z‖^2) (Metric.closedBall 0 r) :=
    hcont.integrableOn_compact (isCompact_closedBall 0 r)
  have hintA : IntegrableOn (fun z => ‖deriv h z‖^2) A :=
    hintR.mono_set (diff_subset.trans Metric.ball_subset_closedBall)
  have hintE : IntegrableOn (fun z => ‖deriv h z‖^2) E :=
    hintR.mono_set (Metric.closedBall_subset_closedBall hεr.le)
  have hunion : A ∪ E = Metric.ball (0 : ℂ) r :=
    diff_union_of_subset (Metric.closedBall_subset_ball hεr)
  have hsplit : ∫ z in Metric.closedBall (0 : ℂ) r, ‖deriv h z‖^2 =
      (∫ z in A, ‖deriv h z‖^2) + ∫ z in E, ‖deriv h z‖^2 := by
  {
    rw [← setIntegral_congr_set (ball_closedBall_ae_eq r), ← hunion,
      setIntegral_union disjoint_sdiff_self_left measurableSet_closedBall hintA hintE]
  }
  have hE_le : ∫ z in E, ‖deriv h z‖^2 ≤ Real.pi * ε^2 * D₀ := by
  {
    have hm := setIntegral_mono_on hintE (integrableOn_const (isCompact_closedBall 0 ε).measure_ne_top)
      measurableSet_closedBall (fun z hz => hD z (Metric.closedBall_subset_closedBall hεr.le hz))
    rw [setIntegral_const, smul_eq_mul, measureReal_def, Complex.volume_closedBall,
      ENNReal.toReal_mul, ENNReal.toReal_pow, ENNReal.toReal_ofReal hε.le,
      ENNReal.coe_toReal] at hm
    change ∫ z in E, ‖deriv h z‖^2 ≤ (ε^2 * Real.pi) * D₀ at hm
    linarith
  }
  linarith
}

lemma meromorphic_area_eps_poly_ineq {h H : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹ + h z)
    (hHi : InjOn H (Metric.ball 0 1 \ {0}))
    {ε r C₁ C₂ D₀ : ℝ} (hε : 0 < ε) (hεr : ε < r) (hr1 : r < 1)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂)
    (h1 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖dslope h 0 w‖ ≤ C₁)
    (h2 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖dslope2 h w‖ ≤ C₂)
    (hD : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖deriv h w‖^2 ≤ D₀)
    (hout : (1 + ‖deriv h 0‖) * (r⁻¹ + C₁) ≤ ε⁻¹)
    (hb1 : ε^2 * ‖deriv h 0‖ < 1) :
    (1 - (ε^2 * ‖deriv h 0‖)^2) *
      ((∫ z in Metric.closedBall 0 r, ‖deriv h z‖^2) - Real.pi * (r^2)⁻¹ - Real.pi * ε^2 * D₀) ≤
      Real.pi * (2 * (C₂ + ‖deriv h 0‖ * C₁) * ε +
        (C₂ + ‖deriv h 0‖ * C₁)^2 * ε^4 + ε^2 * ‖deriv h 0‖^2) := by
{
  let a : ℝ := ‖deriv h 0‖
  let K : ℝ := C₂ + a * C₁
  have h1m : 0 ≤ 1 - (ε^2 * a)^2 := by nlinarith [mul_nonneg (sq_nonneg ε) (norm_nonneg (deriv h 0))]
  have hsub := integral_closedBall_le_annulus_add_small hh hε hεr hr1 hD
  have hH_eq := integral_annulus_norm_deriv_H_sq hh hdef hε hεr hr1
  have harea := annulus_area_ineq hH hdef hHi hε hεr hr1 hC₁ hC₂ h1 h2 hout hb1
  have hm := mul_le_mul_of_nonneg_left
    (add_le_add_left hsub (Real.pi * ((ε^2)⁻¹ - (r^2)⁻¹))) h1m
  rw [← hH_eq] at hm
  have hcomb := hm.trans harea
  have hi1 : ε * ε⁻¹ = 1 := mul_inv_cancel₀ hε.ne'
  have hi2 : ε^2 * (ε^2)⁻¹ = 1 := mul_inv_cancel₀ (pow_ne_zero 2 hε.ne')
  have hi3 : (ε⁻¹)^2 = (ε^2)⁻¹ := inv_pow ε 2
  have halg : Real.pi * (ε⁻¹ + K * ε^2)^2 - (1 - (ε^2 * a)^2) * Real.pi * (ε^2)⁻¹ =
      Real.pi * (2 * K * ε + K^2 * ε^4 + ε^2 * a^2) := by
  {
    linear_combination Real.pi * hi3 + 2 * Real.pi * K * ε * hi1 + Real.pi * a^2 * ε^2 * hi2
  }
  dsimp only [a, K] at hcomb halg ⊢
  linarith
}

lemma meromorphic_area_small_eps_conds {ε r a C₁ : ℝ}
    (hr : 0 < r) (hr1 : r < 1) (ha : 0 ≤ a) (hC₁ : 0 ≤ C₁) (hε0 : 0 < ε)
    (hεr : ε < r) (hεM : ε < ((1 + a) * (r⁻¹ + C₁) + 1)⁻¹) (hεa : ε < (a + 1)⁻¹) :
    (1 + a) * (r⁻¹ + C₁) ≤ ε⁻¹ ∧ ε^2 * a < 1 := by
{
  have hM_pos : 0 < (1 + a) * (r⁻¹ + C₁) + 1 := by positivity
  have hltM : (1 + a) * (r⁻¹ + C₁) + 1 < ε⁻¹ := (lt_inv_comm₀ hε0 hM_pos).mp hεM
  have h1le : ε ≤ 1 := hεr.le.trans hr1.le
  have hlta : a + 1 < ε⁻¹ := (lt_inv_comm₀ hε0 (by positivity)).mp hεa
  have hm := mul_lt_mul_of_pos_left hlta hε0
  rw [mul_inv_cancel₀ hε0.ne'] at hm
  exact ⟨by linarith, by nlinarith⟩
}

lemma meromorphic_area_limit_step {h H : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹ + h z)
    (hHi : InjOn H (Metric.ball 0 1 \ {0}))
    {r C₁ C₂ D₀ : ℝ} (hr : 0 < r) (hr1 : r < 1)
    (hC₁ : 0 ≤ C₁) (hC₂ : 0 ≤ C₂) (_hD₀ : 0 ≤ D₀)
    (h1 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖dslope h 0 w‖ ≤ C₁)
    (h2 : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖dslope2 h w‖ ≤ C₂)
    (hD : ∀ w ∈ Metric.closedBall (0 : ℂ) r, ‖deriv h w‖^2 ≤ D₀) :
    ∫ z in Metric.closedBall 0 r, ‖deriv h z‖^2 ≤ Real.pi * (r^2)⁻¹ := by
{
  let a : ℝ := ‖deriv h 0‖
  let K : ℝ := C₂ + a * C₁
  let I_r : ℝ := ∫ z in Metric.closedBall 0 r, ‖deriv h z‖^2
  let M_out : ℝ := (1 + a) * (r⁻¹ + C₁) + 1
  have hε₀ : 0 < min r (min M_out⁻¹ (a + 1)⁻¹) :=
    lt_min hr (lt_min (inv_pos.mpr (by positivity)) (inv_pos.mpr (by positivity)))
  have hev : ∀ᶠ ε in 𝓝[>] (0 : ℝ),
      (1 - (ε^2 * a)^2) * (I_r - Real.pi * (r^2)⁻¹ - Real.pi * ε^2 * D₀) ≤
        Real.pi * (2 * K * ε + K^2 * ε^4 + ε^2 * a^2) := by
  {
    filter_upwards [Ioo_mem_nhdsGT hε₀] with ε hε
    have hεr : ε < r := hε.2.trans_le (min_le_left _ _)
    have hcond := meromorphic_area_small_eps_conds hr hr1 (norm_nonneg _) hC₁ hε.1 hεr
      (hε.2.trans_le ((min_le_right _ _).trans (min_le_left _ _)))
      (hε.2.trans_le ((min_le_right _ _).trans (min_le_right _ _)))
    exact meromorphic_area_eps_poly_ineq hh hH hdef hHi hε.1 hεr hr1 hC₁ hC₂ h1 h2 hD hcond.1 hcond.2
  }
  have htL : Tendsto (fun ε : ℝ => (1 - (ε^2 * a)^2) * (I_r - Real.pi * (r^2)⁻¹ - Real.pi * ε^2 * D₀))
      (𝓝[>] 0) (𝓝 (I_r - Real.pi * (r^2)⁻¹)) := by
  {
    have hc : Continuous (fun ε : ℝ => (1 - (ε^2 * a)^2) * (I_r - Real.pi * (r^2)⁻¹ - Real.pi * ε^2 * D₀)) := by fun_prop
    simpa using hc.tendsto 0 |>.mono_left nhdsWithin_le_nhds
  }
  have htR : Tendsto (fun ε : ℝ => Real.pi * (2 * K * ε + K^2 * ε^4 + ε^2 * a^2))
      (𝓝[>] 0) (𝓝 0) := by
  {
    have hc : Continuous (fun ε : ℝ => Real.pi * (2 * K * ε + K^2 * ε^4 + ε^2 * a^2)) := by fun_prop
    simpa using hc.tendsto 0 |>.mono_left nhdsWithin_le_nhds
  }
  have hle0 : I_r - Real.pi * (r^2)⁻¹ ≤ 0 := le_of_tendsto_of_tendsto htL htR hev
  dsimp only [I_r] at hle0
  linarith
}

/-- Gronwall's Area Theorem for meromorphic univalent maps `H(z) = z⁻¹ + h(z)` on `𝔻 \ {0}`. -/
lemma meromorphic_univalent_area {h H : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹ + h z)
    (_hHd : ∀ z ∈ Metric.ball (0 : ℂ) 1 \ {0}, deriv H z ≠ 0)
    (hHi : InjOn H (Metric.ball 0 1 \ {0}))
    {r : ℝ} (hr : 0 < r) (hr1 : r < 1) :
    ∫ z in Metric.closedBall 0 r, ‖deriv h z‖^2 ∂volume ≤
      volume.real (Metric.closedBall (0 : ℂ) r) * (r^2)⁻¹^2 := by
{
  let B : Set ℂ := Metric.closedBall 0 r
  have hBc : IsCompact B := isCompact_closedBall 0 r
  have hBsub : B ⊆ Metric.ball 0 1 := Metric.closedBall_subset_ball hr1
  have h0B : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  have hd1 : DifferentiableOn ℂ (dslope h 0) (Metric.ball 0 1) :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds h0B)).mpr hh
  obtain ⟨C₁', hC₁'⟩ := hBc.exists_bound_of_continuousOn (hd1.continuousOn.mono hBsub)
  obtain ⟨C₂', hC₂'⟩ := hBc.exists_bound_of_continuousOn
    ((differentiableOn_dslope2 hh).continuousOn.mono hBsub)
  obtain ⟨D₀', hD₀'⟩ := hBc.exists_bound_of_continuousOn
    (((hh.deriv Metric.isOpen_ball).continuousOn.mono hBsub).norm.pow 2)
  have hD' (w : ℂ) (hw : w ∈ B) : ‖deriv h w‖^2 ≤ D₀' := by
    simpa only [Real.norm_eq_abs, abs_sq] using hD₀' w hw
  have hle := meromorphic_area_limit_step hh hH hdef hHi hr hr1
    (le_max_right C₁' 0) (le_max_right C₂' 0) (le_max_right D₀' 0)
    (fun w hw => (hC₁' w hw).trans (le_max_left _ _))
    (fun w hw => (hC₂' w hw).trans (le_max_left _ _))
    (fun w hw => (hD' w hw).trans (le_max_left _ _))
  have hvol : volume.real (Metric.closedBall (0 : ℂ) r) * (r^2)⁻¹^2 = Real.pi * (r^2)⁻¹ := by
  {
    rw [measureReal_def, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
      ENNReal.toReal_ofReal hr.le, ENNReal.coe_toReal]
    change (r^2 * Real.pi) * (r^2)⁻¹^2 = Real.pi * (r^2)⁻¹
    have hr2 : r^2 ≠ 0 := pow_ne_zero 2 hr.ne'
    field_simp [hr2]
  }
  linarith
}

lemma meromorphic_univalent_coefficient {h H : ℂ → ℂ}
    (hh : DifferentiableOn ℂ h (Metric.ball 0 1))
    (hH : DifferentiableOn ℂ H (Metric.ball 0 1 \ {0}))
    (hdef : ∀ z ∈ Metric.ball (0 : ℂ) 1, z ≠ 0 → H z = z⁻¹ + h z)
    (hHd : ∀ z ∈ Metric.ball (0 : ℂ) 1 \ {0}, deriv H z ≠ 0)
    (hHi : InjOn H (Metric.ball 0 1 \ {0})) : ‖deriv h 0‖ ≤ 1 := by
{
  have hb (r : ℝ) (hr : 0 < r) (hr1 : r < 1) : ‖deriv h 0‖^2 ≤ (r^2)⁻¹^2 := by
  {
    have hM : 0 < volume.real (Metric.closedBall (0 : ℂ) r) := by
    {
      rw [measureReal_def, Complex.volume_closedBall, ENNReal.toReal_mul, ENNReal.toReal_pow,
        ENNReal.toReal_ofReal hr.le, ENNReal.coe_toReal]
      exact mul_pos (sq_pos_of_pos hr) Real.pi_pos
    }
    have hle := (holomorphic_sq_submean (hh.deriv Metric.isOpen_ball) hr hr1).trans
      (meromorphic_univalent_area hh hH hdef hHd hHi hr hr1)
    nlinarith
  }
  have ht : Tendsto (fun r : ℝ => (r^2)⁻¹^2) (𝓝[<] (1 : ℝ)) (𝓝 1) := by
  {
    have hc : ContinuousAt (fun r : ℝ => (r^2)⁻¹^2) 1 :=
      ((continuousAt_id.pow 2).inv₀ (by norm_num)).pow 2
    simpa using hc.tendsto.mono_left nhdsWithin_le_nhds
  }
  have hsq : ‖deriv h 0‖^2 ≤ 1 := by
  {
    apply ge_of_tendsto ht
    filter_upwards [self_mem_nhdsWithin,
      (show ∀ᶠ r : ℝ in 𝓝[<] (1 : ℝ), 0 < r from
        nhdsWithin_le_nhds (Ioi_mem_nhds (by norm_num : (0 : ℝ) < 1)))] with r hr1 hr
    exact hb r hr hr1
  }
  nlinarith [norm_nonneg (deriv h 0)]
}

/-! ### 3. Odd Square-Root Transform and Bieberbach's `|a₂| ≤ 2` (`‖f''(0)‖ ≤ 4`) -/

lemma differentiableAt_of_continuous_root {q F : ℂ → ℂ} {z : ℂ}
    (hq : ContinuousAt q z) (hF : DifferentiableAt ℂ F z)
    (hroot : (fun w => q w^2) =ᶠ[𝓝 z] F) (hq0 : q z ≠ 0) :
    DifferentiableAt ℂ q z := by
{
  have hp : HasStrictDerivAt (fun w : ℂ => w^2) (2 * q z) (q z) := by
  {
    have hp := (hasStrictDerivAt_id (q z)).pow 2
    change HasStrictDerivAt (fun w : ℂ => w^2) _ (q z) at hp
    simpa only [id_eq, Nat.reduceSub, pow_one, Nat.cast_ofNat, mul_one] using hp
  }
  have hn : 2 * q z ≠ 0 := mul_ne_zero (by norm_num) hq0
  let p := hp.localInverse _ _ _ hn
  have hpD : DifferentiableAt ℂ p (F z) := by
  {
    rw [← hroot.self_of_nhds]
    exact (hp.to_localInverse hn).hasDerivAt.differentiableAt
  }
  have he : q =ᶠ[𝓝 z] fun w => p (F w) := by
  {
    filter_upwards [hq.tendsto.eventually (hp.eventually_left_inverse hn), hroot] with w hw hwF
    exact (hwF ▸ hw).symm
  }
  exact (hpD.comp z hF).congr_of_eventuallyEq he
}

lemma exists_holomorphic_sqrt_disk {F : ℂ → ℂ}
    (hF : DifferentiableOn ℂ F disk) (hF0 : ∀ z ∈ disk, F z ≠ 0)
    (hFone : F 0 = 1) :
    ∃ q : ℂ → ℂ, DifferentiableOn ℂ q disk ∧ q 0 = 1 ∧
      (∀ z ∈ disk, q z^2 = F z) ∧ ∀ z ∈ disk, q z ≠ 0 := by
{
  have hdz : (0 : ℂ) ∈ disk := by simp [disk]
  have hsim : IsSimplyConnected disk := by
  {
    have : ContractibleSpace disk := (convex_ball (0 : ℂ) (1 : ℝ)).contractibleSpace ⟨0, hdz⟩
    change SimplyConnectedSpace disk
    exact inferInstance
  }
  obtain ⟨q, hqc, hq⟩ := Complex.exists_continuousOn_pow_eq hsim Metric.isOpen_ball hF.continuousOn
    (by rintro ⟨z, hz, he⟩; exact hF0 z hz he) (n := 2) (by norm_num)
  have hqn (z) (hz : z ∈ disk) : q z ≠ 0 := by
  {
    intro he
    have := hq z
    rw [he, zero_pow (by norm_num)] at this
    exact hF0 z hz this.symm
  }
  have hqd : DifferentiableOn ℂ q disk := by
  {
    intro z hz
    apply DifferentiableAt.differentiableWithinAt
    exact differentiableAt_of_continuous_root
      (hqc.continuousAt (Metric.isOpen_ball.mem_nhds hz))
      ((hF z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz))
      (Filter.Eventually.of_forall hq) (hqn z hz)
  }
  let Q : ℂ → ℂ := fun z => q z / q 0
  refine ⟨Q, hqd.div_const _, by simp [Q, hqn 0 hdz], ?_, ?_⟩
  · intro z _hz
    simp only [Q, div_pow, hq, hFone, div_one]
  · intro z hz
    exact div_ne_zero (hqn z hz) (hqn 0 hdz)
}

lemma dslope_factor (f : ℂ → ℂ) (z : ℂ) :
    z * dslope f 0 z = f z - f 0 := by
{
  simpa only [sub_zero, smul_eq_mul] using sub_smul_dslope f 0 z
}

lemma sq_mem_disk {z : ℂ} (hz : z ∈ disk) : z^2 ∈ disk := by
{
  have hn : ‖z‖ < 1 := by simpa [disk] using hz
  simpa [disk] using pow_lt_one₀ (norm_nonneg z) hn (by norm_num : 2 ≠ 0)
}

lemma dslope_zero_ne_zero {f : ℂ → ℂ} (hf : IsClassS f) {z : ℂ} (hz : z ∈ disk) :
    dslope f 0 z ≠ 0 := by
{
  have hdz : (0 : ℂ) ∈ disk := by simp [disk]
  by_cases hz0 : z = 0
  · simpa [hz0] using (show deriv f 0 ≠ 0 by rw [hf.2.2.2]; norm_num)
  · intro he
    have hfact := dslope_factor f z
    rw [he, mul_zero] at hfact
    exact hz0 (hf.2.1 hz hdz (sub_eq_zero.mp hfact.symm))
}

lemma odd_sqrt_univalent {f q : ℂ → ℂ} (hf : IsClassS f)
    (hqd : DifferentiableOn ℂ q disk) (hqn : ∀ z ∈ disk, q z ≠ 0)
    (hqs : ∀ z ∈ disk, q z^2 = dslope f 0 z) :
    UnivalentOn (fun z => z * q (z^2)) disk := by
{
  let g : ℂ → ℂ := fun z => z * q (z^2)
  have hgd : DifferentiableOn ℂ g disk :=
    differentiableOn_id.mul (hqd.comp (differentiableOn_id.pow 2) (fun _ hz => sq_mem_disk hz))
  have hgs (z) (hz : z ∈ disk) : g z^2 = f (z^2) := by
  {
    dsimp only [g]
    rw [mul_pow, hqs _ (sq_mem_disk hz)]
    simpa [hf.2.2.1] using dslope_factor f (z^2)
  }
  have hgn (z) (hz : z ∈ disk) (hz0 : z ≠ 0) : g z ≠ 0 :=
    mul_ne_zero hz0 (hqn _ (sq_mem_disk hz))
  refine ⟨hgd, ?_⟩
  intro z hz w hw he
  have hsq : z^2 = w^2 := hf.2.1 (sq_mem_disk hz) (sq_mem_disk hw)
    ((hgs z hz).symm.trans ((congrArg (fun t => t^2) he).trans (hgs w hw)))
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp hsq with heq | heq
  · exact heq
  · have hgneg : g z = -g w := by simp [g, heq]
    have hw0 : w = 0 := by
    {
      by_contra hn
      exact hgn w hw hn (by linear_combination (he.symm + hgneg) / 2)
    }
    simpa [hw0] using heq
}

lemma odd_recip_remainder_deriv {q : ℂ → ℂ} (hqd : DifferentiableOn ℂ q disk)
    (hq0 : q 0 = 1) (hqn : ∀ z ∈ disk, q z ≠ 0) :
    DifferentiableOn ℂ (fun z => -z * dslope q 0 (z^2) / q (z^2)) disk ∧
    deriv (fun z => -z * dslope q 0 (z^2) / q (z^2)) 0 = -deriv q 0 ∧
    ∀ z ∈ disk, z ≠ 0 → (z * q (z^2))⁻¹ = z⁻¹ + (-z * dslope q 0 (z^2) / q (z^2)) := by
{
  have hdz : (0 : ℂ) ∈ disk := by simp [disk]
  let Q := dslope q 0
  have hQd : DifferentiableOn ℂ Q disk :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds hdz)).mpr hqd
  let h : ℂ → ℂ := fun z => -z * Q (z^2) / q (z^2)
  refine ⟨?_, ?_, ?_⟩
  · exact (differentiableOn_id.neg.mul
      (hQd.comp (differentiableOn_id.pow 2) (fun _ hz => sq_mem_disk hz))).div
      (hqd.comp (differentiableOn_id.pow 2) (fun _ hz => sq_mem_disk hz))
      (fun _ hz => hqn _ (sq_mem_disk hz))
  · have hqd0 := ((hqd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt
    have hQd0 := ((hQd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt
    have hp : HasDerivAt (fun z : ℂ => z^2) 0 0 := by
      simpa using hasDerivAt_pow 2 (0 : ℂ)
    have hQcomp : HasDerivAt (fun z : ℂ => Q (z^2)) 0 0 := by
      convert (show HasDerivAt Q (deriv Q 0) ((0 : ℂ)^2) by simpa using hQd0).comp 0 hp using 1 <;> first | rfl | simp
    have hqcomp : HasDerivAt (fun z : ℂ => q (z^2)) 0 0 := by
      convert (show HasDerivAt q (deriv q 0) ((0 : ℂ)^2) by simpa using hqd0).comp 0 hp using 1 <;> first | rfl | simp
    have hD : HasDerivAt (fun z => -z * dslope q 0 (z^2) / q (z^2)) _ 0 :=
      ((hasDerivAt_id' (0 : ℂ)).neg.mul hQcomp).div hqcomp (by simpa using hqn 0 hdz)
    simpa [Q, hq0] using hD.deriv
  · intro z hz hz0
    have hfact : z^2 * Q (z^2) = q (z^2) - 1 := by simpa [Q, hq0] using dslope_factor q (z^2)
    field_simp [hz0, hqn _ (sq_mem_disk hz)]
    linear_combination hfact
}

lemma second_deriv_from_sqrt {f q : ℂ → ℂ} (hf : IsClassS f)
    (hqd : DifferentiableOn ℂ q disk) (hq0 : q 0 = 1)
    (hqs : ∀ z ∈ disk, q z^2 = dslope f 0 z) :
    deriv (deriv f) 0 = 4 * deriv q 0 := by
{
  have hdz : (0 : ℂ) ∈ disk := by simp [disk]
  let F := dslope f 0
  have hFd : DifferentiableOn ℂ F disk :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds hdz)).mpr hf.1
  have hFq : deriv F 0 = 2 * deriv q 0 := by
  {
    have hD := (((hqd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt).pow 2
    have he : (fun z => q z^2) =ᶠ[𝓝 (0 : ℂ)] F := by
      filter_upwards [Metric.isOpen_ball.mem_nhds hdz] with z hz using hqs z hz
    simpa [hq0] using (hD.congr_of_eventuallyEq he.symm).deriv
  }
  have hff : deriv (deriv f) 0 = 2 * deriv F 0 := by
  {
    have hidentity : f = fun z => z * F z := by
      funext z; simpa [hf.2.2.1, F] using (dslope_factor f z).symm
    have he : deriv f =ᶠ[𝓝 (0 : ℂ)] fun z => F z + z * deriv F z := by
    {
      filter_upwards [Metric.isOpen_ball.mem_nhds hdz] with z hz
      have hD := (hasDerivAt_id z).mul (((hFd z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt)
      rw [hidentity]
      change HasDerivAt (fun w => w * F w) _ z at hD
      simpa using hD.deriv
    }
    have hD := (((hFd 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt).add
      ((hasDerivAt_id (0 : ℂ)).mul
        (((hFd.deriv Metric.isOpen_ball 0 hdz).differentiableAt (Metric.isOpen_ball.mem_nhds hdz)).hasDerivAt))
    simpa [two_mul] using (hD.congr_of_eventuallyEq he).deriv
  }
  rw [hff, hFq]
  ring
}

/-- Bieberbach's second coefficient bound `|a₂| ≤ 2`, i.e., `‖f''(0)‖ ≤ 4`. -/
lemma schlicht_second_deriv_bound {f : ℂ → ℂ} (hf : IsClassS f) :
    ‖deriv (deriv f) 0‖ ≤ 4 := by
{
  have hdz : (0 : ℂ) ∈ disk := by simp [disk]
  have hFd : DifferentiableOn ℂ (dslope f 0) disk :=
    (Complex.differentiableOn_dslope (Metric.isOpen_ball.mem_nhds hdz)).mpr hf.1
  obtain ⟨q, hqd, hq0, hqs, hqn⟩ := exists_holomorphic_sqrt_disk hFd
    (fun _ hz => dslope_zero_ne_zero hf hz) (by simpa using hf.2.2.2)
  have hgu := odd_sqrt_univalent hf hqd hqn hqs
  obtain ⟨hhd, hderh, hdef⟩ := odd_recip_remainder_deriv hqd hq0 hqn
  let H : ℂ → ℂ := fun z => (z * q (z^2))⁻¹
  have hHu : UnivalentOn H (disk \ {0}) :=
    ⟨(hgu.1.mono diff_subset).inv (fun z hz => mul_ne_zero hz.2 (hqn _ (sq_mem_disk hz.1))),
      fun _ hz _ hw he => hgu.2 hz.1 hw.1 (inv_inj.mp he)⟩
  have hbound : ‖deriv (fun z => -z * dslope q 0 (z^2) / q (z^2)) 0‖ ≤ 1 :=
    meromorphic_univalent_coefficient hhd hHu.1 hdef
      (fun _ hz => univalent_deriv_ne_zero (Metric.isOpen_ball.sdiff isClosed_singleton) hHu hz) hHu.2
  rw [hderh, norm_neg] at hbound
  rw [second_deriv_from_sqrt hf hqd hq0 hqs, norm_mul]
  norm_num
  linarith
}

/-! ### 4. Omitted-Value Transformation & Koebe Quarter Theorem -/

def omittedTransform (f : ℂ → ℂ) (w z : ℂ) : ℂ := w * f z / (w - f z)

lemma omittedTransform_univalent {f : ℂ → ℂ} {w : ℂ}
    (hf : UnivalentOn f disk) (hw : w ∉ f '' disk) (hw0 : w ≠ 0) :
    UnivalentOn (omittedTransform f w) disk := by
{
  have hn (z) (hz : z ∈ disk) : w - f z ≠ 0 := fun he => hw ⟨z, hz, (sub_eq_zero.mp he).symm⟩
  refine ⟨(hf.1.const_mul w).div (hf.1.const_sub w) hn, ?_⟩
  intro z hz v hv he
  apply hf.2 hz hv
  apply mul_left_cancel₀ (pow_ne_zero 2 hw0)
  have he' := (div_eq_div_iff (hn z hz) (hn v hv)).mp he
  linear_combination he'
}

lemma omittedTransform_deriv {f : ℂ → ℂ} {w z : ℂ}
    (hf : DifferentiableOn ℂ f disk) (hw : w ∉ f '' disk) (hz : z ∈ disk) :
    HasDerivAt (omittedTransform f w) (w^2 * deriv f z / (w - f z)^2) z := by
{
  have hn : w - f z ≠ 0 := fun he => hw ⟨z, hz, (sub_eq_zero.mp he).symm⟩
  have hd := ((hf z hz).differentiableAt (Metric.isOpen_ball.mem_nhds hz)).hasDerivAt
  convert (hd.const_mul w).div (hd.const_sub w) hn using 1 <;> try rfl
  ring
}

lemma omittedTransform_isClassS {f : ℂ → ℂ} {w : ℂ}
    (hf : IsClassS f) (hw : w ∉ f '' disk) : IsClassS (omittedTransform f w) := by
{
  have hzero : (0 : ℂ) ∈ disk := by simp [disk]
  have hw0 : w ≠ 0 := fun h => hw ⟨0, hzero, hf.2.2.1.trans h.symm⟩
  have huniv := omittedTransform_univalent (isClassS_univalent hf) hw hw0
  refine ⟨huniv.1, huniv.2, ?_, ?_⟩
  · simp [omittedTransform, hf.2.2.1]
  · rw [(omittedTransform_deriv hf.1 hw hzero).deriv, hf.2.2.1, hf.2.2.2]
    simp [hw0]
}

lemma omittedTransform_second_deriv {f : ℂ → ℂ} {w : ℂ}
    (hf : IsClassS f) (hw : w ∉ f '' disk) :
    deriv (deriv (omittedTransform f w)) 0 = deriv (deriv f) 0 + 2 / w := by
{
  have hzero : (0 : ℂ) ∈ disk := by simp [disk]
  have hw0 : w ≠ 0 := fun h => hw ⟨0, hzero, hf.2.2.1.trans h.symm⟩
  have he : deriv (omittedTransform f w) =ᶠ[𝓝 (0 : ℂ)]
      fun z => w^2 * deriv f z / (w - f z)^2 := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzero] with z hz using
      (omittedTransform_deriv hf.1 hw hz).deriv
  have hfd := ((hf.1 0 hzero).differentiableAt (Metric.isOpen_ball.mem_nhds hzero)).hasDerivAt
  have hfdd := ((hf.1.deriv Metric.isOpen_ball 0 hzero).differentiableAt
    (Metric.isOpen_ball.mem_nhds hzero)).hasDerivAt
  have hd := ((hfdd.const_mul (w^2)).div ((hfd.const_sub w).pow 2)
    (by simpa [hf.2.2.1] using pow_ne_zero 2 hw0)).congr_of_eventuallyEq he
  rw [hd.deriv]
  simp only [Pi.pow_apply, hf.2.2.1, hf.2.2.2, sub_zero, mul_one]
  field_simp [hw0]
  ring
}

/-- Koebe Quarter Theorem: every value omitted by `f ∈ S` has modulus at least `1/4`. -/
theorem koebe_quarter_theorem (f : ℂ → ℂ) (hf : IsClassS f) (w : ℂ)
    (hw : w ∉ f '' (Metric.ball 0 1)) : 1 / 4 ≤ ‖w‖ := by
{
  have hz : (0 : ℂ) ∈ disk := by simp [disk]
  have hw0 : w ≠ 0 := fun h => hw ⟨0, hz, hf.2.2.1.trans h.symm⟩
  have hb := schlicht_second_deriv_bound (omittedTransform_isClassS hf hw)
  rw [omittedTransform_second_deriv hf hw] at hb
  have hdiff : ‖(2 : ℂ) / w‖ ≤ 8 := by
  {
    have ht := norm_sub_le (deriv (deriv f) 0 + 2 / w) (deriv (deriv f) 0)
    have hf2 := schlicht_second_deriv_bound hf
    simp only [add_sub_cancel_left] at ht
    linarith
  }
  rw [norm_div] at hdiff
  norm_num at hdiff
  have hle := (div_le_iff₀ (norm_pos_iff.mpr hw0)).mp hdiff
  linarith
}

lemma schlicht_quarter {f : ℂ → ℂ} (hf : IsClassS f) :
    Metric.ball (0 : ℂ) (1 / 4) ⊆ f '' disk := by
{
  intro w hw
  by_contra hnot
  have hge := koebe_quarter_theorem f hf w hnot
  have hlt : ‖w‖ < 1 / 4 := by simpa using hw
  linarith
}

def ballNormalize (f : ℂ → ℂ) (a : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  (f (a + (R : ℂ) * z) - f a) / ((R : ℂ) * deriv f a)

lemma affine_disk_maps_ball (a : ℂ) {R : ℝ} (hR : 0 < R) :
    MapsTo (fun z : ℂ => a + (R : ℂ) * z) disk (Metric.ball a R) := by
{
  intro z hz
  have hz' : ‖z‖ < 1 := by simpa [disk] using hz
  simp only [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left, norm_mul,
    Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
  nlinarith
}

lemma ballNormalize_deriv {f : ℂ → ℂ} {a z : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : DifferentiableOn ℂ f (Metric.ball a R)) (hz : z ∈ disk) :
    HasDerivAt (ballNormalize f a R)
      (deriv f (a + (R : ℂ) * z) / deriv f a) z := by
{
  have hmap := affine_disk_maps_ball a hR hz
  have hd := ((hf _ hmap).differentiableAt (Metric.isOpen_ball.mem_nhds hmap)).hasDerivAt
  have hdz := (((hd.comp z (((hasDerivAt_id z).const_mul (R : ℂ)).const_add a)).sub_const (f a)).div_const
    ((R : ℂ) * deriv f a))
  convert hdz using 1 <;> try rfl
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  simp only [mul_one]
  field_simp
}

lemma ballNormalize_isClassS {f : ℂ → ℂ} {a : ℂ} {R : ℝ} (hR : 0 < R)
    (hf : UnivalentOn f (Metric.ball a R)) (hn : deriv f a ≠ 0) :
    IsClassS (ballNormalize f a R) := by
{
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hmap := affine_disk_maps_ball a hR
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro z hz
    exact (ballNormalize_deriv hR hf.1 hz).differentiableAt.differentiableWithinAt
  · intro z hz w hw he
    apply mul_left_cancel₀ hRc
    apply add_left_cancel (a := a)
    apply hf.2 (hmap hz) (hmap hw)
    have he' := (div_left_inj' (mul_ne_zero hRc hn)).mp he
    exact sub_left_inj.mp he'
  · simp [ballNormalize]
  · rw [(ballNormalize_deriv hR hf.1 (show (0 : ℂ) ∈ disk by simp [disk])).deriv]
    simp [hn]
}

/-- Local Koebe Quarter Theorem on an arbitrary open disk `B(z₀, R)`. -/
theorem local_koebe_quarter (g : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hg_diff : DifferentiableOn ℂ g (Metric.ball z₀ R))
    (hg_inj : InjOn g (Metric.ball z₀ R))
    (hn : deriv g z₀ ≠ 0) :
    Metric.ball (g z₀) (R * ‖deriv g z₀‖ / 4) ⊆ g '' Metric.ball z₀ R := by
{
  have hRc : (R : ℂ) ≠ 0 := by exact_mod_cast hR.ne'
  have hden := mul_ne_zero hRc hn
  intro w hw
  have hu : (w - g z₀) / ((R : ℂ) * deriv g z₀) ∈ Metric.ball (0 : ℂ) (1 / 4) := by
  {
    simp only [Metric.mem_ball, dist_zero_right, norm_div, norm_mul,
      Complex.norm_real, Real.norm_eq_abs, abs_of_pos hR]
    rw [div_lt_iff₀ (mul_pos hR (norm_pos_iff.mpr hn))]
    have hw' : ‖w - g z₀‖ < R * ‖deriv g z₀‖ / 4 := by simpa [dist_eq_norm] using hw
    linarith
  }
  obtain ⟨z, hz, he⟩ := schlicht_quarter (ballNormalize_isClassS hR ⟨hg_diff, hg_inj⟩ hn) hu
  refine ⟨z₀ + (R : ℂ) * z, affine_disk_maps_ball z₀ hR hz, ?_⟩
  have hes := (div_left_inj' hden).mp he
  exact sub_left_inj.mp hes
}

lemma schlicht_separation {f : ℂ → ℂ} (hf : IsClassS f)
    {z w : ℂ} (_hz : z ∈ disk) (hw : w ∈ disk) {R : ℝ} (hR : 0 < R)
    (hsub : Metric.ball z R ⊆ disk) (hdist : R ≤ ‖w - z‖) :
    R * ‖deriv f z‖ / 4 ≤ ‖f w - f z‖ := by
{
  by_contra! hlt
  have hm : f w ∈ Metric.ball (f z) (R * ‖deriv f z‖ / 4) := by
    simpa [dist_eq_norm] using hlt
  have h_univ_sub : UnivalentOn f (Metric.ball z R) := ⟨hf.1.mono hsub, hf.2.1.mono hsub⟩
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball h_univ_sub (Metric.mem_ball_self hR)
  obtain ⟨v, hv, he⟩ := local_koebe_quarter f z R hR h_univ_sub.1 h_univ_sub.2 hn hm
  have hvw := hf.2.1 (hsub hv) hw he
  subst v
  have : ‖w - z‖ < R := by simpa [dist_eq_norm] using hv
  exact (not_lt_of_ge hdist) this
}

lemma schlicht_lower_growth {f : ℂ → ℂ} (hf : IsClassS f) {z : ℂ} (hz : z ∈ disk) :
    ‖z‖ / 4 ≤ ‖f z‖ := by
{
  by_cases hzero : z = 0
  · simp [hzero, hf.2.2.1]
  have h := schlicht_separation hf (show (0 : ℂ) ∈ disk by simp [disk]) hz
    (norm_pos_iff.mpr hzero)
    (Metric.ball_subset_ball (show ‖z‖ ≤ 1 by exact le_of_lt (by simpa [disk] using hz)))
    (show ‖z‖ ≤ ‖z - (0 : ℂ)‖ by simp)
  simpa [hf.2.2.1, hf.2.2.2] using h
}

/-! ### 5. Disk Automorphisms, Pre-Schwarzian Bound, and Derivative Distortion -/

def diskAutomorphism (a z : ℂ) : ℂ := (z + a) / (1 + starRingEnd ℂ a * z)

lemma diskAutomorphism_den_ne_zero {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) :
    1 + starRingEnd ℂ a * z ≠ 0 := by
{
  have hna : ‖a‖ < 1 := by simpa [disk] using ha
  have hnz : ‖z‖ < 1 := by simpa [disk] using hz
  intro he
  have hb : ‖starRingEnd ℂ a * z‖ < 1 := by
  {
    rw [norm_mul, Complex.norm_conj]
    nlinarith [norm_nonneg a, norm_nonneg z]
  }
  have he' : starRingEnd ℂ a * z = -1 := by linear_combination he
  rw [he'] at hb
  norm_num at hb
}

lemma diskAutomorphism_normSq_identity (a z : ℂ) :
    Complex.normSq (1 + starRingEnd ℂ a * z) - Complex.normSq (z + a) =
      (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
{
  simp [Complex.normSq, Complex.mul_re, Complex.mul_im]
  ring
}

lemma diskAutomorphism_mem {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) :
    diskAutomorphism a z ∈ disk := by
{
  have hna : ‖a‖ < 1 := by simpa [disk] using ha
  have hnz : ‖z‖ < 1 := by simpa [disk] using hz
  have hpos : 0 < (1 - Complex.normSq a) * (1 - Complex.normSq z) := by
  {
    rw [← Complex.sq_norm, ← Complex.sq_norm]
    apply mul_pos <;> nlinarith [norm_nonneg a, norm_nonneg z]
  }
  have hineq := diskAutomorphism_normSq_identity a z
  have hd := diskAutomorphism_den_ne_zero ha hz
  rw [disk, Metric.mem_ball, dist_zero_right, diskAutomorphism, norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  rw [← Complex.sq_norm, ← Complex.sq_norm] at hineq
  nlinarith [norm_nonneg (z + a), norm_nonneg (1 + starRingEnd ℂ a * z)]
}

lemma diskAutomorphism_deriv {a z : ℂ} (ha : a ∈ disk) (hz : z ∈ disk) :
    HasDerivAt (diskAutomorphism a)
      ((1 - (‖a‖^2 : ℝ)) / (1 + starRingEnd ℂ a * z)^2) z := by
{
  have hd := ((hasDerivAt_id z).add_const a).div
    (((hasDerivAt_id z).const_mul (starRingEnd ℂ a)).const_add 1)
    (diskAutomorphism_den_ne_zero ha hz)
  convert hd using 1 <;> try rfl
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]
  simp only [id_eq]
  ring
}

lemma diskAutomorphism_injOn {a : ℂ} (ha : a ∈ disk) : InjOn (diskAutomorphism a) disk := by
{
  intro z hz w hw he
  have he' := (div_eq_div_iff (diskAutomorphism_den_ne_zero ha hz)
    (diskAutomorphism_den_ne_zero ha hw)).mp he
  have hna : ‖a‖ < 1 := by simpa [disk] using ha
  have hd : (1 - starRingEnd ℂ a * a) ≠ 0 := by
  {
    rw [← Complex.normSq_eq_conj_mul_self, ← Complex.ofReal_one, ← Complex.ofReal_sub]
    apply Complex.ofReal_ne_zero.mpr
    rw [← Complex.sq_norm]
    nlinarith [norm_nonneg a]
  }
  apply mul_left_cancel₀ hd
  linear_combination he'
}

lemma diskAutomorphism_zero (a : ℂ) : diskAutomorphism a 0 = a := by
{
  simp [diskAutomorphism]
}

lemma diskAutomorphism_differentiableOn {a : ℂ} (ha : a ∈ disk) :
    DifferentiableOn ℂ (diskAutomorphism a) disk := by
{
  exact fun _ hz => (diskAutomorphism_deriv ha hz).differentiableAt.differentiableWithinAt
}

def diskKoebe (f : ℂ → ℂ) (a z : ℂ) : ℂ :=
  (f (diskAutomorphism a z) - f a) / ((1 - ((‖a‖^2 : ℝ) : ℂ)) * deriv f a)

lemma disk_coeff_ne_zero {a : ℂ} (ha : a ∈ disk) : 1 - ((‖a‖^2 : ℝ) : ℂ) ≠ 0 := by
{
  have hn : ‖a‖ < 1 := by simpa [disk] using ha
  rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.ofReal_ne_zero]
  nlinarith [norm_nonneg a]
}

lemma diskKoebe_univalent {f : ℂ → ℂ} {a : ℂ} (hf : UnivalentOn f disk)
    (ha : a ∈ disk) (hfd : deriv f a ≠ 0) : UnivalentOn (diskKoebe f a) disk := by
{
  refine ⟨?_, ?_⟩
  · exact ((hf.1.comp (diskAutomorphism_differentiableOn ha)
      (fun _ hz => diskAutomorphism_mem ha hz)).sub_const (f a)).div_const _
  · intro z hz w hw he
    have he' := (div_left_inj' (mul_ne_zero (disk_coeff_ne_zero ha) hfd)).mp he
    exact diskAutomorphism_injOn ha hz hw
      (hf.2 (diskAutomorphism_mem ha hz) (diskAutomorphism_mem ha hw) (sub_left_inj.mp he'))
}

lemma diskKoebe_deriv {f : ℂ → ℂ} {a z : ℂ} (hf : DifferentiableOn ℂ f disk)
    (ha : a ∈ disk) (hz : z ∈ disk) :
    HasDerivAt (diskKoebe f a)
      ((deriv f (diskAutomorphism a z) * ((1 - ((‖a‖^2 : ℝ) : ℂ)) / (1 + starRingEnd ℂ a * z)^2)) /
        ((1 - ((‖a‖^2 : ℝ) : ℂ)) * deriv f a)) z := by
{
  exact ((((hf _ (diskAutomorphism_mem ha hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (diskAutomorphism_mem ha hz))).hasDerivAt.comp z
    (diskAutomorphism_deriv ha hz)).sub_const (f a)).div_const _
}

lemma diskKoebe_isClassS {f : ℂ → ℂ} {a : ℂ} (hf : UnivalentOn f disk)
    (ha : a ∈ disk) (hfd : deriv f a ≠ 0) : IsClassS (diskKoebe f a) := by
{
  have huniv := diskKoebe_univalent hf ha hfd
  refine ⟨huniv.1, huniv.2, ?_, ?_⟩
  · simp [diskKoebe, diskAutomorphism_zero]
  · have hd := (diskKoebe_deriv hf.1 ha (by simp [disk] : (0 : ℂ) ∈ disk)).deriv
    rw [hd]
    simp only [diskAutomorphism_zero, mul_zero, add_zero, one_pow, div_one]
    rw [mul_comm (deriv f a), div_self (mul_ne_zero (disk_coeff_ne_zero ha) hfd)]
}

lemma diskKoebe_second_deriv {f : ℂ → ℂ} {a : ℂ} (hf : DifferentiableOn ℂ f disk)
    (ha : a ∈ disk) (hfd : deriv f a ≠ 0) :
    deriv (deriv (diskKoebe f a)) 0 =
      (1 - ((‖a‖^2 : ℝ) : ℂ)) * deriv (deriv f) a / deriv f a - 2 * starRingEnd ℂ a := by
{
  have hzero : (0 : ℂ) ∈ disk := by simp [disk]
  have he : deriv (diskKoebe f a) =ᶠ[𝓝 (0 : ℂ)]
      fun z => (deriv f (diskAutomorphism a z) *
        ((1 - ((‖a‖^2 : ℝ) : ℂ)) / (1 + starRingEnd ℂ a * z)^2)) /
        ((1 - ((‖a‖^2 : ℝ) : ℂ)) * deriv f a) := by
    filter_upwards [Metric.isOpen_ball.mem_nhds hzero] with z hz using
      (diskKoebe_deriv hf ha hz).deriv
  have hda := ((hf.deriv Metric.isOpen_ball a ha).differentiableAt
    (Metric.isOpen_ball.mem_nhds ha)).hasDerivAt
  have hda' : HasDerivAt (deriv f) (deriv (deriv f) a) (diskAutomorphism a 0) := by
    simpa [diskAutomorphism_zero] using hda
  have hcomp := hda'.comp 0 (diskAutomorphism_deriv ha hzero)
  have hrat := (hasDerivAt_const (0 : ℂ) (1 - ((‖a‖^2 : ℝ) : ℂ))).div
    ((((hasDerivAt_id (0 : ℂ)).const_mul (starRingEnd ℂ a)).const_add 1).pow 2)
    (by simp)
  have hd := ((hcomp.mul hrat).div_const
    ((1 - ((‖a‖^2 : ℝ) : ℂ)) * deriv f a)).congr_of_eventuallyEq he
  rw [hd.deriv]
  simp only [Pi.div_apply, Pi.pow_apply, Function.comp_apply, diskAutomorphism_zero,
    mul_zero, add_zero, one_pow, div_one, zero_sub, id_eq, mul_one]
  have halg (A B C D : ℂ) (hB : B ≠ 0) (hC : C ≠ 0) :
      (A * C * C + B * (-(C * (2 * D)))) / (C * B) = C * A / B - 2 * D := by
  {
    field_simp
    ring
  }
  exact halg (deriv (deriv f) a) (deriv f a)
    (1 - ((‖a‖^2 : ℝ) : ℂ)) (starRingEnd ℂ a) hfd (disk_coeff_ne_zero ha)
}

lemma schlicht_preSchwarzian_bound {f : ℂ → ℂ} (hf : IsClassS f) {a : ℂ} (ha : a ∈ disk) :
    ‖(1 - ((‖a‖^2 : ℝ) : ℂ)) * deriv (deriv f) a / deriv f a - 2 * starRingEnd ℂ a‖ ≤ 4 := by
{
  have hn := univalent_deriv_ne_zero Metric.isOpen_ball (isClassS_univalent hf) ha
  have hb := schlicht_second_deriv_bound (diskKoebe_isClassS (isClassS_univalent hf) ha hn)
  rwa [diskKoebe_second_deriv hf.1 ha hn] at hb
}

lemma hasDerivAt_log_norm_real {g : ℝ → ℂ} {d : ℂ} {x : ℝ}
    (hg : HasDerivAt g d x) (hn : g x ≠ 0) :
    HasDerivAt (fun t => Real.log ‖g t‖) (d / g x).re x := by
{
  have heq : (fun t => Real.log ‖g t‖) =
      (fun t => (1 / 2 : ℝ) * Real.log (‖g t‖^2)) := by
  {
    funext t
    rw [Real.log_pow]
    ring
  }
  have hd := ((hg.norm_sq).log (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))).const_mul (1 / 2 : ℝ)
  rw [heq]
  apply hd.congr_deriv
  simp only [Complex.inner, Complex.conj_re, Complex.conj_im, Complex.mul_re,
    Complex.div_re, Complex.normSq_eq_norm_sq]
  ring
}

lemma logarithmic_distortion_alg {x : ℝ} (h1 : 0 < 1 - x) (h2 : 0 < 1 + x) (h3 : 0 < 1 - x^2) :
    1 / (1 + x) + 3 / (1 - x) = (2 * x + 4) / (1 - x^2) ∧
    -(1 / (1 - x) + 3 / (1 + x)) = (2 * x - 4) / (1 - x^2) := by
{
  constructor <;> field_simp [h1.ne', h2.ne', h3.ne'] <;> ring
}

lemma hasDerivAt_log_distortion_aux {L : ℝ → ℝ} {d x : ℝ}
    (hL : HasDerivAt L d x) (h1 : 0 < 1 - x) (h2 : 0 < 1 + x) :
    HasDerivAt (fun y => L y - Real.log (1 + y) + 3 * Real.log (1 - y))
      (d - 1 / (1 + x) - 3 / (1 - x)) x ∧
    HasDerivAt (fun y => L y - Real.log (1 - y) + 3 * Real.log (1 + y))
      (d + 1 / (1 - x) + 3 / (1 + x)) x := by
{
  have hlogp := ((hasDerivAt_id x).const_add 1).log (ne_of_gt h2)
  have hlogm := ((hasDerivAt_id x).const_sub 1).log (ne_of_gt h1)
  constructor
  · convert (hL.sub hlogp).add (hlogm.const_mul 3) using 1 <;> try rfl
    simp; ring
  · convert (hL.sub hlogm).add (hlogp.const_mul 3) using 1 <;> try rfl
    simp; ring
}

lemma logarithmic_distortion {L D : ℝ → ℝ} {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    (hL : ∀ x ∈ Icc 0 r, HasDerivAt L (D x) x) (hL0 : L 0 = 0)
    (hbound : ∀ x ∈ Icc 0 r,
      (2 * x - 4) / (1 - x^2) ≤ D x ∧ D x ≤ (2 * x + 4) / (1 - x^2)) :
    Real.log (1 - r) - 3 * Real.log (1 + r) ≤ L r ∧
      L r ≤ Real.log (1 + r) - 3 * Real.log (1 - r) := by
{
  have hp (x : ℝ) (hx : x ∈ Icc 0 r) : 0 < 1 - x ∧ 0 < 1 + x ∧ 0 < 1 - x^2 :=
    ⟨by linarith [hx.2], by linarith [hx.1], by nlinarith [hx.1, hx.2]⟩
  let U := fun x => L x - Real.log (1 + x) + 3 * Real.log (1 - x)
  let V := fun x => L x - Real.log (1 - x) + 3 * Real.log (1 + x)
  have hU (x) (hx : x ∈ Icc 0 r) := (hasDerivAt_log_distortion_aux (hL x hx) (hp x hx).1 (hp x hx).2.1).1
  have hV (x) (hx : x ∈ Icc 0 r) := (hasDerivAt_log_distortion_aux (hL x hx) (hp x hx).1 (hp x hx).2.1).2
  have hUa : AntitoneOn U (Icc 0 r) :=
    antitoneOn_of_deriv_nonpos (convex_Icc 0 r)
      (fun x hx => (hU x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hU x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [(hU x (interior_subset hx)).deriv]
        have hb := (hbound x (interior_subset hx)).2
        have halg := (logarithmic_distortion_alg (hp x (interior_subset hx)).1 (hp x (interior_subset hx)).2.1 (hp x (interior_subset hx)).2.2).1
        linarith)
  have hVm : MonotoneOn V (Icc 0 r) :=
    monotoneOn_of_deriv_nonneg (convex_Icc 0 r)
      (fun x hx => (hV x hx).continuousAt.continuousWithinAt)
      (fun x hx => (hV x (interior_subset hx)).differentiableAt.differentiableWithinAt)
      (fun x hx => by
        rw [(hV x (interior_subset hx)).deriv]
        have hb := (hbound x (interior_subset hx)).1
        have halg := (logarithmic_distortion_alg (hp x (interior_subset hx)).1 (hp x (interior_subset hx)).2.1 (hp x (interior_subset hx)).2.2).2
        linarith)
  have hu := hUa (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  have hv := hVm (left_mem_Icc.mpr hr) (right_mem_Icc.mpr hr) hr
  dsimp [U, V] at hu hv
  simp only [hL0, add_zero, sub_zero, Real.log_one, mul_zero] at hu hv
  constructor <;> linarith
}

lemma radialDistortion_deriv_bounds {f : ℂ → ℂ}
    (hps : ∀ a ∈ disk,
      ‖(1 - ((‖a‖^2 : ℝ) : ℂ)) * deriv (deriv f) a / deriv f a - 2 * starRingEnd ℂ a‖ ≤ 4)
    {r : ℝ} (hr1 : r < 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) (x : ℝ) (hx : x ∈ Icc 0 r) :
    (2 * x - 4) / (1 - x^2) ≤ (deriv (deriv f) ((x : ℂ) * ζ) * ζ / deriv f ((x : ℂ) * ζ)).re ∧
    (deriv (deriv f) ((x : ℂ) * ζ) * ζ / deriv f ((x : ℂ) * ζ)).re ≤ (2 * x + 4) / (1 - x^2) := by
{
  let D : ℝ := (deriv (deriv f) ((x : ℂ) * ζ) * ζ / deriv f ((x : ℂ) * ζ)).re
  have hn : ‖(x : ℂ) * ζ‖ = x := by
    rw [norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
  have hm : (x : ℂ) * ζ ∈ disk := by
    simp only [disk, Metric.mem_ball, dist_zero_right, hn]; exact hx.2.trans_lt hr1
  let A : ℂ := (1 - ((x^2 : ℝ) : ℂ)) * deriv (deriv f) ((x : ℂ) * ζ) / deriv f ((x : ℂ) * ζ)
    - 2 * starRingEnd ℂ ((x : ℂ) * ζ)
  have hA : ‖A * ζ‖ ≤ 4 := by
    rw [norm_mul, hζ, mul_one]; simpa only [A, hn] using hps _ hm
  have he : (A * ζ).re = (1 - x^2) * D - 2 * x := by
  {
    have hzz : starRingEnd ℂ ζ * ζ = 1 := by
      rw [← Complex.normSq_eq_conj_mul_self, ← Complex.sq_norm, hζ]; norm_num
    have heq : A * ζ = ((1 - x^2 : ℝ) : ℂ) *
        (deriv (deriv f) ((x : ℂ) * ζ) * ζ / deriv f ((x : ℂ) * ζ)) - 2 * (x : ℂ) := by
    {
      dsimp only [A]
      rw [map_mul, Complex.conj_ofReal, Complex.ofReal_sub, Complex.ofReal_one]
      linear_combination -2 * (x : ℂ) * hzz
    }
    rw [heq]
    simp only [D, Complex.sub_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
    norm_num
  }
  have hreal := (Complex.abs_re_le_norm (A * ζ)).trans hA
  rw [he, abs_le] at hreal
  have hpos : 0 < 1 - x^2 := by nlinarith [hx.1, hx.2]
  exact ⟨(div_le_iff₀ hpos).mpr (by nlinarith [hreal.1]), (le_div_iff₀ hpos).mpr (by nlinarith [hreal.2])⟩
}

lemma radialDistortion_of_preSchwarzian {f : ℂ → ℂ}
    (hf : DifferentiableOn ℂ f disk) (hf0 : deriv f 0 = 1)
    (hfn : ∀ a ∈ disk, deriv f a ≠ 0)
    (hps : ∀ a ∈ disk,
      ‖(1 - ((‖a‖^2 : ℝ) : ℂ)) * deriv (deriv f) a / deriv f a - 2 * starRingEnd ℂ a‖ ≤ 4)
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    (1 - r) / (1 + r)^3 ≤ ‖deriv f ((r : ℂ) * ζ)‖ ∧
      ‖deriv f ((r : ℂ) * ζ)‖ ≤ (1 + r) / (1 - r)^3 := by
{
  let L : ℝ → ℝ := fun x => Real.log ‖deriv f ((x : ℂ) * ζ)‖
  let D : ℝ → ℝ := fun x => (deriv (deriv f) ((x : ℂ) * ζ) * ζ / deriv f ((x : ℂ) * ζ)).re
  have hm (x) (hx : x ∈ Icc 0 r) : (x : ℂ) * ζ ∈ disk := by
  {
    simp only [disk, Metric.mem_ball, dist_zero_right, norm_mul, hζ, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx.1]
    exact hx.2.trans_lt hr1
  }
  have hD (x) (hx : x ∈ Icc 0 r) : HasDerivAt L (D x) x := by
  {
    have hd := ((hf.deriv Metric.isOpen_ball _ (hm x hx)).differentiableAt
      (Metric.isOpen_ball.mem_nhds (hm x hx))).hasDerivAt
    have hx' : HasDerivAt (fun t : ℝ => (t : ℂ) * ζ) ζ x := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const ζ :
        HasDerivAt (fun t : ℝ => Complex.ofRealCLM t * ζ) ((Complex.ofRealCLM (1 : ℝ)) * ζ) x)
    have hdc : HasDerivAt (fun t : ℝ => deriv f ((t : ℂ) * ζ))
        (deriv (deriv f) ((x : ℂ) * ζ) * ζ) x := by
      convert HasDerivAt.comp (𝕜 := ℝ) x hd hx' using 1 <;> rfl
    exact hasDerivAt_log_norm_real hdc (hfn _ (hm x hx))
  }
  have hbnd := logarithmic_distortion hr hr1 hD (by simp [L, hf0])
    (radialDistortion_deriv_bounds hps hr1 hζ)
  have hposm : 0 < 1 - r := sub_pos.mpr hr1
  have hposp : 0 < 1 + r := by linarith
  have hnorm : 0 < ‖deriv f ((r : ℂ) * ζ)‖ := norm_pos_iff.mpr (hfn _ (hm r (right_mem_Icc.mpr hr)))
  constructor
  · apply (Real.log_le_log_iff (div_pos hposm (pow_pos hposp 3)) hnorm).mp
    simpa only [Real.log_div hposm.ne' (pow_ne_zero 3 hposp.ne'), Real.log_pow, Nat.cast_ofNat] using hbnd.1
  · apply (Real.log_le_log_iff hnorm (div_pos hposp (pow_pos hposm 3))).mp
    simpa only [Real.log_div hposp.ne' (pow_ne_zero 3 hposm.ne'), Real.log_pow, Nat.cast_ofNat] using hbnd.2
}

lemma schlicht_deriv_bounds {f : ℂ → ℂ} (hf : IsClassS f) {z : ℂ} (hz : z ∈ disk) :
    (1 - ‖z‖) / (1 + ‖z‖)^3 ≤ ‖deriv f z‖ ∧
      ‖deriv f z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖)^3 := by
{
  by_cases hzero : z = 0
  · simp [hzero, hf.2.2.2]
  have hn := norm_pos_iff.mpr hzero
  have hζ : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), div_self hn.ne']
  have heq : (‖z‖ : ℂ) * (z / (‖z‖ : ℂ)) = z := by
    field_simp [show (‖z‖ : ℂ) ≠ 0 by exact_mod_cast hn.ne']
  have hb := radialDistortion_of_preSchwarzian hf.1 hf.2.2.2
    (fun _ ha => univalent_deriv_ne_zero Metric.isOpen_ball (isClassS_univalent hf) ha)
    (fun _ ha => schlicht_preSchwarzian_bound hf ha) (norm_nonneg z)
    (show ‖z‖ < 1 by simpa [disk] using hz) hζ
  rwa [heq] at hb
}

/-! ### 6. Upper Growth Bound `‖f(z)‖ ≤ ‖z‖ / (1 - ‖z‖)²` and Full Koebe Theorem -/

lemma hasDerivAt_koebe_growth_real {x : ℝ} (hx1 : x < 1) :
    HasDerivAt (fun t : ℝ => t / (1 - t)^2) ((1 + x) / (1 - x)^3) x := by
{
  have hne : 1 - x ≠ 0 := by linarith
  have hd : HasDerivAt (fun t : ℝ => t / (1 - t)^2) _ x :=
    (hasDerivAt_id' x).div (((hasDerivAt_id' x).const_sub 1).pow 2) (pow_ne_zero 2 hne)
  apply hd.congr_deriv
  field_simp [hne]
  ring
}

lemma radial_upper_growth {f : ℂ → ℂ} (hf : IsClassS f) {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1)
    {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    ‖f ((r : ℂ) * ζ)‖ ≤ r / (1 - r)^2 := by
{
  let g : ℝ → ℂ := fun t => f ((t : ℂ) * ζ)
  let g' : ℝ → ℂ := fun t => deriv f ((t : ℂ) * ζ) * ζ
  let B : ℝ → ℝ := fun t => t / (1 - t)^2
  let B' : ℝ → ℝ := fun t => (1 + t) / (1 - t)^3
  have hm (t) (ht : t ∈ Icc 0 r) : (t : ℂ) * ζ ∈ disk := by
  {
    simp only [disk, Metric.mem_ball, dist_zero_right, norm_mul, hζ, mul_one,
      Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
    exact ht.2.trans_lt hr1
  }
  have hg_deriv (t) (ht : t ∈ Icc 0 r) : HasDerivAt g (g' t) t := by
  {
    have hd := ((hf.1 _ (hm t ht)).differentiableAt (Metric.isOpen_ball.mem_nhds (hm t ht))).hasDerivAt
    have ht' : HasDerivAt (fun s : ℝ => (s : ℂ) * ζ) ζ t := by
      simpa using (Complex.ofRealCLM.hasDerivAt.mul_const ζ :
        HasDerivAt (fun s : ℝ => Complex.ofRealCLM s * ζ) ((Complex.ofRealCLM (1 : ℝ)) * ζ) t)
    convert HasDerivAt.comp (𝕜 := ℝ) t hd ht' using 1 <;> rfl
  }
  have hB_deriv (t) (ht : t ∈ Icc 0 r) : HasDerivAt B (B' t) t :=
    hasDerivAt_koebe_growth_real (ht.2.trans_lt hr1)
  have h_le := image_norm_le_of_norm_deriv_right_le_deriv_boundary'
    (fun t ht => (hg_deriv t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hg_deriv t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (by simp [g, B, hf.2.2.1])
    (fun t ht => (hB_deriv t ht).continuousAt.continuousWithinAt)
    (fun t ht => (hB_deriv t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    (fun t ht => by
      dsimp [g', B']
      rw [norm_mul, hζ, mul_one]
      have h_t := (schlicht_deriv_bounds hf (hm t (Ico_subset_Icc_self ht))).2
      have h_norm : ‖(t : ℂ) * ζ‖ = t := by
        rw [norm_mul, hζ, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg ht.1]
      rwa [h_norm] at h_t)
  exact h_le (right_mem_Icc.mpr hr)
}

lemma schlicht_upper_growth {f : ℂ → ℂ} (hf : IsClassS f) {z : ℂ} (hz : z ∈ disk) :
    ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖)^2 := by
{
  by_cases hzero : z = 0
  · simp [hzero, hf.2.2.1]
  have hn := norm_pos_iff.mpr hzero
  have hζ : ‖z / (‖z‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg z), div_self hn.ne']
  have heq : (‖z‖ : ℂ) * (z / (‖z‖ : ℂ)) = z := by
    field_simp [show (‖z‖ : ℂ) ≠ 0 by exact_mod_cast hn.ne']
  have hb := radial_upper_growth hf (norm_nonneg z) (by simpa [disk] using hz) hζ
  rwa [heq] at hb
}

/-- Classical univalence estimates for the normalized disk class `S` (Lemma 2.1 of the paper). -/
theorem koebe_distortion_theorem (f : ℂ → ℂ) (hf : IsClassS f) (z : ℂ) (hz : ‖z‖ < 1) :
    (1 - ‖z‖) / (1 + ‖z‖)^3 ≤ ‖deriv f z‖ ∧
    ‖deriv f z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖)^3 ∧
    ‖z‖ / 4 ≤ ‖f z‖ ∧
    ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖)^2 := by
{
  have hzd : z ∈ disk := by simpa [disk] using hz
  have hd := schlicht_deriv_bounds hf hzd
  exact ⟨hd.1, hd.2, schlicht_lower_growth hf hzd, schlicht_upper_growth hf hzd⟩
}

lemma schlicht_deriv_compact_bound {f : ℂ → ℂ} (hf : IsClassS f)
    {R : ℝ} (hR : R < 1) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖deriv f z‖ ≤ 2 / (1 - R)^3 := by
{
  have hzm : z ∈ disk := by simpa [disk] using hz.trans_lt hR
  apply (schlicht_deriv_bounds hf hzm).2.trans
  have hd : 0 < 1 - R := sub_pos.mpr hR
  apply div_le_div₀ (by positivity) (by linarith [norm_nonneg z]) (by positivity)
  exact pow_le_pow_left₀ hd.le (by linarith) 3
}

lemma schlicht_lipschitz_bound {f : ℂ → ℂ} (hf : IsClassS f)
    {R : ℝ} (hR : R < 1) {z w : ℂ} (hz : ‖z‖ ≤ R) (hw : ‖w‖ ≤ R) :
    ‖f z - f w‖ ≤ (2 / (1 - R)^3) * ‖z - w‖ := by
{
  apply Convex.norm_image_sub_le_of_norm_deriv_le (s := Metric.closedBall 0 R)
    (𝕜 := ℂ) _ _ (convex_closedBall 0 R)
    (by simpa using hw) (by simpa using hz)
  · intro x hx
    apply (hf.1 x _).differentiableAt
      (Metric.isOpen_ball.mem_nhds (show x ∈ disk from ?_))
    all_goals simpa [disk] using (show ‖x‖ ≤ R by simpa using hx).trans_lt hR
  · intro x hx
    exact schlicht_deriv_compact_bound hf hR (by simpa using hx)
}

lemma schlicht_local_bound {f : ℂ → ℂ} (hf : IsClassS f)
    {R : ℝ} (hR : R < 1) {z : ℂ} (hz : ‖z‖ ≤ R) :
    ‖f z‖ ≤ (2 / (1 - R)^3) * R := by
{
  have h := schlicht_lipschitz_bound hf hR hz
    (show ‖(0 : ℂ)‖ ≤ R by simpa using (norm_nonneg z).trans hz)
  simp only [hf.2.2.1, sub_zero] at h
  exact h.trans (mul_le_mul_of_nonneg_left hz (by positivity))
}

lemma schlicht_uniform_separation {z w : ℂ} (hz : z ∈ disk) (hw : w ∈ disk)
    (hne : z ≠ w) : ∃ c : ℝ, 0 < c ∧ ∀ f : ℂ → ℂ, IsClassS f → c ≤ ‖f w - f z‖ := by
{
  have hz1 : ‖z‖ < 1 := by simpa [disk] using hz
  let R := min ((1 - ‖z‖) / 2) (‖w - z‖ / 2)
  have hR : 0 < R := lt_min (by linarith)
    (div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hne.symm)) (by norm_num))
  have hR1 : R ≤ (1 - ‖z‖) / 2 := min_le_left _ _
  have hR2 : R ≤ ‖w - z‖ / 2 := min_le_right _ _
  have hsub : Metric.ball z R ⊆ disk := by
  {
    intro v hv
    have hvR : ‖v - z‖ < R := by simpa [dist_eq_norm] using hv
    have ht := norm_add_le (v - z) z
    rw [sub_add_cancel] at ht
    simp only [disk, Metric.mem_ball, dist_zero_right]
    linarith
  }
  refine ⟨R * ((1 - ‖z‖) / (1 + ‖z‖)^3) / 4, by positivity, ?_⟩
  intro f hf
  have h := schlicht_separation hf hz hw hR hsub (by linarith [norm_nonneg (w - z)])
  apply le_trans _ h
  exact div_le_div_of_nonneg_right
    (mul_le_mul_of_nonneg_left (schlicht_deriv_bounds hf hz).1 hR.le) (by norm_num)
}

end Brennan.Koebe
