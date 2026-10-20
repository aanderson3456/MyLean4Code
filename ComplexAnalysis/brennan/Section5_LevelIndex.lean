import Mathlib
import brennan.Section5_Winding
import brennan.Section3

noncomputable section

open Set MeasureTheory Filter Function InnerProductSpace TopologicalSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical CompactlySupported Matrix

namespace Brennan.Sections4and5

open Brennan.Section2
open Brennan.Section2_Dyadic
open Brennan.Section3

/-!
# Section 5 Hopf Tangent Turning, Level Index Sum, and Critical Point Count
-/

def secantTriangle : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ 1}

lemma convex_secantTriangle : Convex ℝ secantTriangle := by
{
  intro p hp q hq a b ha hb hab
  change 0 ≤ a * p.1 + b * q.1 ∧ a * p.1 + b * q.1 ≤ a * p.2 + b * q.2 ∧ a * p.2 + b * q.2 ≤ 1
  rcases hp with ⟨hp0, hpst, hp1⟩
  rcases hq with ⟨hq0, hqst, hq1⟩
  refine ⟨add_nonneg (mul_nonneg ha hp0) (mul_nonneg hb hq0),
    add_le_add (mul_le_mul_of_nonneg_left hpst ha) (mul_le_mul_of_nonneg_left hqst hb), ?_⟩
  calc
    _ ≤ a * 1 + b * 1 := add_le_add (mul_le_mul_of_nonneg_left hp1 ha) (mul_le_mul_of_nonneg_left hq1 hb)
    _ = 1 := by simpa using hab
}

lemma nonempty_secantTriangle : secantTriangle.Nonempty := by
{
  exact ⟨(0, 0), by simp [secantTriangle]⟩
}

def averagedDerivative (γ : ℝ → ℂ) (s t : ℝ) : ℂ :=
  ∫ u in (0 : ℝ)..1, deriv γ (s + u * (t - s))

lemma continuous_averagedDerivative {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) :
    Continuous (fun p : ℝ × ℝ => averagedDerivative γ p.1 p.2) := by
{
  have hd : Continuous (deriv γ) := hγ.continuous_deriv (by norm_num)
  have hi : Continuous (fun p : ℝ × ℝ => ∫ u in Icc (0 : ℝ) 1, deriv γ (p.1 + u * (p.2 - p.1))) :=
    continuous_parametric_integral_of_continuous (by fun_prop) isCompact_Icc
  simpa [averagedDerivative, intervalIntegral.integral_of_le zero_le_one,
    integral_Icc_eq_integral_Ioc] using hi
}

lemma sub_smul_averagedDerivative {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) (s t : ℝ) :
    (t - s) • averagedDerivative γ s t = γ t - γ s := by
{
  have hd : Continuous (deriv γ) := hγ.continuous_deriv (by norm_num)
  have hD (u : ℝ) : HasDerivAt (fun v : ℝ => γ (s + v * (t - s)))
      ((t - s) • deriv γ (s + u * (t - s))) u := by
  {
    simpa only [Function.comp_def, Pi.add_apply, id_eq, zero_add, one_mul] using
      ((hγ.differentiable (by norm_num) (s + u * (t - s))).hasDerivAt.scomp u
        ((hasDerivAt_const u s).add ((hasDerivAt_id u).mul_const (t - s))))
  }
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt (fun u _ => hD u)
    (((hd.comp (show Continuous (fun u : ℝ => s + u * (t - s)) by fun_prop)).const_smul (t - s)).intervalIntegrable 0 1)
  simpa [averagedDerivative, intervalIntegral.integral_smul, sub_eq_add_neg] using hFTC
}

@[simp] lemma averagedDerivative_diag (γ : ℝ → ℂ) (s : ℝ) :
    averagedDerivative γ s s = deriv γ s := by
{
  simp [averagedDerivative]
}

def extendedSecant (γ : ℝ → ℂ) (p : ℝ × ℝ) : ℂ :=
  (1 - (p.2 - p.1)) • averagedDerivative γ p.1 p.2 -
    (p.2 - p.1) • averagedDerivative γ p.1 (p.2 - 1)

lemma continuous_extendedSecant {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ) :
    Continuous (extendedSecant γ) := by
{
  have hc := continuous_averagedDerivative hγ
  exact ((continuous_const.sub (continuous_snd.sub continuous_fst)).smul hc).sub
    ((continuous_snd.sub continuous_fst).smul
      (hc.comp (show Continuous (fun p : ℝ × ℝ => (p.1, p.2 - 1)) by fun_prop)))
}

@[simp] lemma extendedSecant_diag (γ : ℝ → ℂ) (s : ℝ) :
    extendedSecant γ (s, s) = deriv γ s := by
{
  simp [extendedSecant]
}

@[simp] lemma extendedSecant_corner (γ : ℝ → ℂ) :
    extendedSecant γ (0, 1) = -deriv γ 0 := by
{
  simp [extendedSecant]
}

lemma extendedSecant_scale {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (s t : ℝ) :
    ((t - s) * (1 - (t - s))) • extendedSecant γ (s, t) =
      ((1 - (t - s))^2 + (t - s)^2) • (γ t - γ s) := by
{
  have h₁ := sub_smul_averagedDerivative hγ s t
  have h₂ := sub_smul_averagedDerivative hγ s (t - 1)
  rw [hp.sub_eq] at h₂
  change ((t - s) * (1 - (t - s))) • ((1 - (t - s)) • averagedDerivative γ s t -
    (t - s) • averagedDerivative γ s (t - 1)) = _
  calc
    _ = (1 - (t - s))^2 • ((t - s) • averagedDerivative γ s t) +
      (t - s)^2 • ((t - 1 - s) • averagedDerivative γ s (t - 1)) := by
        simp only [smul_sub, smul_smul]; module
    _ = _ := by rw [h₁, h₂, ← add_smul]
}

lemma extendedSecant_ne_zero {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico 0 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0) {p : ℝ × ℝ}
    (hpt : p ∈ secantTriangle) : extendedSecant γ p ≠ 0 := by
{
  rcases p with ⟨s, t⟩
  rcases hpt with ⟨hs, hst, ht⟩
  by_cases heq : s = t
  · subst t; simpa using hd s ⟨hs, ht⟩
  by_cases hc : s = 0 ∧ t = 1
  · rcases hc with ⟨rfl, rfl⟩; simpa using hd 0 (by simp)
  have hst' : s < t := lt_of_le_of_ne hst heq
  have hneq : γ t ≠ γ s := by
  {
    by_cases ht1 : t = 1
    · subst t; rw [hp.eq]
      have hs0 : s ≠ 0 := fun h => hc ⟨h, rfl⟩
      exact fun h => hs0 ((hinj ⟨by norm_num, by norm_num⟩ ⟨hs, hst'⟩ h).symm)
    · exact fun h => (ne_of_gt hst') (hinj ⟨hs.trans hst, lt_of_le_of_ne ht ht1⟩
        ⟨hs, hst'.trans_le ht⟩ h)
  }
  have hpos : 0 < (1 - (t - s))^2 + (t - s)^2 := by nlinarith [sq_nonneg (1 - (t - s))]
  intro he
  have hscale := extendedSecant_scale hγ hp s t
  rw [he, smul_zero] at hscale
  exact hneq (sub_eq_zero.mp ((smul_eq_zero.mp hscale.symm).resolve_left hpos.ne'))
}

lemma periodic_deriv {γ : ℝ → ℂ} (hp : Function.Periodic γ 1) :
    Function.Periodic (deriv γ) 1 := by
{
  intro t
  rw [← deriv_comp_add_const γ 1 t]
  congr 1
  exact funext hp
}

lemma extendedSecant_edges {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    extendedSecant γ (t, 1) = -extendedSecant γ (0, t) := by
{
  by_cases h0 : t = 0
  · subst t; simp
  by_cases h1 : t = 1
  · subst t; simpa using (periodic_deriv hp).eq
  have hd : t * (1 - t) ≠ 0 := mul_ne_zero h0 (sub_ne_zero.mpr (Ne.symm h1))
  apply (smul_right_injective ℂ hd)
  have ha := extendedSecant_scale hγ hp 0 t
  have hb := extendedSecant_scale hγ hp t 1
  simp only [sub_zero] at ha
  rw [hp.eq, show (1 - t) * (1 - (1 - t)) = t * (1 - t) by ring,
    show (1 - (1 - t))^2 + (1 - t)^2 = (1 - t)^2 + t^2 by ring] at hb
  change (t * (1 - t)) • extendedSecant γ (t, 1) = (t * (1 - t)) • (-extendedSecant γ (0, t))
  rw [smul_neg, ha, hb, ← smul_neg]
  congr 1
  module
}

lemma extendedSecant_left_re_nonneg {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hm : ∀ t ∈ Icc (0 : ℝ) 1, (γ 0).re ≤ (γ t).re)
    (hd : (deriv γ 0).re = 0) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) 1) :
    0 ≤ (extendedSecant γ (0, t)).re := by
{
  by_cases h0 : t = 0
  · subst t; simp [hd]
  by_cases h1 : t = 1
  · subst t; simp [hd]
  have hpos : 0 < t * (1 - t) := mul_pos (lt_of_le_of_ne ht.1 (Ne.symm h0))
    (sub_pos.mpr (lt_of_le_of_ne ht.2 h1))
  have hs := congrArg Complex.re (extendedSecant_scale hγ hp 0 t)
  simp only [sub_zero, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
    Complex.ofReal_im, zero_mul, sub_zero, Complex.sub_re] at hs
  have hnonneg : 0 ≤ ((1 - t)^2 + t^2) * ((γ t).re - (γ 0).re) :=
    mul_nonneg (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sub_nonneg.mpr (hm t ht))
  nlinarith
}

def triangleOrigin : secantTriangle := ⟨(0, 0), by simp [secantTriangle]⟩
def triangleCorner : secantTriangle := ⟨(0, 1), by simp [secantTriangle]⟩
def triangleEnd : secantTriangle := ⟨(1, 1), by simp [secantTriangle]⟩

lemma exists_secant_log {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico 0 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0) :
    ∃ A : C(secantTriangle, ℂ), A triangleOrigin = Complex.log (deriv γ 0) ∧
      ∀ p, Complex.exp (A p) = extendedSecant γ p := by
{
  let := convex_secantTriangle.contractibleSpace nonempty_secantTriangle
  let := convex_secantTriangle.locPathConnectedSpace
  let S : C(secantTriangle, ℂ) :=
    ⟨fun p => extendedSecant γ p, (continuous_extendedSecant hγ).comp continuous_subtype_val⟩
  have he : Complex.exp (Complex.log (deriv γ 0)) = S triangleOrigin := by
    simpa [S, triangleOrigin] using Complex.exp_log (hd 0 (by simp))
  obtain ⟨A, ⟨hA0, hA⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts S he
    (fun p => extendedSecant_ne_zero hγ hp hinj hd p.property)
  exact ⟨A, hA0, fun p => congrFun hA p⟩
}

lemma continuous_log_unique.{u_1} {X : Type u_1} [TopologicalSpace X] [PreconnectedSpace X]
    {A B : X → ℂ} (hA : Continuous A) (hB : Continuous B)
    (h : ∀ x, Complex.exp (A x) = Complex.exp (B x)) {x : X} (hx : A x = B x) : A = B := by
{
  exact Complex.isCoveringMap_exp.eq_of_comp_eq hA hB
    (by funext y; exact Subtype.ext (h y)) x hx
}

def triangleLeft (t : unitInterval) : secantTriangle :=
  ⟨(0, t), ⟨le_rfl, t.property.1, t.property.2⟩⟩

def triangleTop (t : unitInterval) : secantTriangle :=
  ⟨(t, 1), ⟨t.property.1, t.property.2, le_rfl⟩⟩

def triangleDiag (t : unitInterval) : secantTriangle :=
  ⟨(t, t), ⟨t.property.1, le_rfl, t.property.2⟩⟩

lemma continuous_triangleLeft : Continuous triangleLeft := by
{
  unfold triangleLeft; fun_prop
}

lemma continuous_triangleTop : Continuous triangleTop := by
{
  unfold triangleTop; fun_prop
}

lemma continuous_triangleDiag : Continuous triangleDiag := by
{
  unfold triangleDiag; fun_prop
}

lemma mem_slitPlane_of_re_nonneg {z : ℂ} (hz : z ≠ 0) (hr : 0 ≤ z.re) :
    z ∈ Complex.slitPlane := by
{
  by_cases hi : z.im = 0
  · exact Or.inl (lt_of_le_of_ne hr (fun he => hz (Complex.ext he.symm hi)))
  · exact Or.inr hi
}

lemma log_neg_of_downward {z : ℂ} (hr : z.re = 0) (hi : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * Complex.I := by
{
  apply Complex.ext
  · simp [Complex.log_re, norm_neg]
  · have ha := Complex.arg_eq_neg_pi_div_two_iff.mpr ⟨hr, hi⟩
    have hb : Complex.arg (-z) = Real.pi / 2 :=
      Complex.arg_eq_pi_div_two_iff.mpr ⟨by simpa using hr, by simpa using hi⟩
    simp only [Complex.log_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.I_im, mul_one, Complex.ofReal_im, Complex.I_re, mul_zero, add_zero, ha, hb]
    ring
}

lemma tangent_turning_log {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico 0 1))
    (hd : ∀ t ∈ Icc (0 : ℝ) 1, deriv γ t ≠ 0)
    (hm : ∀ t ∈ Icc (0 : ℝ) 1, (γ 0).re ≤ (γ t).re)
    (hr : (deriv γ 0).re = 0) (hi : (deriv γ 0).im < 0) :
    ∃ T : C(unitInterval, ℂ), (∀ t, Complex.exp (T t) = deriv γ t) ∧
      T 1 = T 0 + (2 * Real.pi : ℝ) * Complex.I := by
{
  obtain ⟨A, hA0, hA⟩ := exists_secant_log hγ hp hinj hd
  have hleftc : Continuous (fun t : unitInterval =>
      Complex.log (extendedSecant γ (triangleLeft t))) :=
    continuous_iff_continuousAt.mpr (fun t =>
      (continuousAt_clog (mem_slitPlane_of_re_nonneg
        (extendedSecant_ne_zero hγ hp hinj hd (triangleLeft t).property)
        (extendedSecant_left_re_nonneg hγ hp hm hr t.property))).comp
        (f := fun u : unitInterval => extendedSecant γ (triangleLeft u))
        ((continuous_extendedSecant hγ).comp
          (continuous_subtype_val.comp continuous_triangleLeft)).continuousAt)
  have hleft : (fun t : unitInterval => A (triangleLeft t)) =
      (fun t : unitInterval => Complex.log (extendedSecant γ (triangleLeft t))) := by
  {
    apply continuous_log_unique (x := (0 : unitInterval))
      (A.continuous.comp continuous_triangleLeft) hleftc
    · intro t; dsimp only [Function.comp_def]
      rw [hA, Complex.exp_log (extendedSecant_ne_zero hγ hp hinj hd (triangleLeft t).property)]
    · simpa [Function.comp_def, triangleLeft, triangleOrigin] using hA0
  }
  have hcorner : A triangleCorner = A triangleOrigin + (Real.pi : ℂ) * Complex.I := by
  {
    have hcl' : A triangleCorner = Complex.log (-deriv γ 0) := by
      simpa [triangleLeft, triangleCorner] using congrFun hleft 1
    rw [hcl', hA0, log_neg_of_downward hr hi]
  }
  have htop : (fun t : unitInterval => A (triangleTop t)) =
      (fun t : unitInterval => A (triangleLeft t) + (Real.pi : ℂ) * Complex.I) := by
  {
    apply continuous_log_unique (x := (0 : unitInterval)) (A.continuous.comp continuous_triangleTop)
      ((A.continuous.comp continuous_triangleLeft).add continuous_const)
    · intro t; dsimp only [Function.comp_def, Pi.add_apply]
      rw [Complex.exp_add, hA, hA, Complex.exp_pi_mul_I, mul_neg_one]
      exact extendedSecant_edges hγ hp t.property
    · exact hcorner
  }
  refine ⟨⟨fun t => A (triangleDiag t), A.continuous.comp continuous_triangleDiag⟩,
    fun t => (hA (triangleDiag t)).trans (extendedSecant_diag γ t), ?_⟩
  have hpt : A triangleEnd = A triangleCorner + (Real.pi : ℂ) * Complex.I := congrFun htop 1
  change A triangleEnd = A triangleOrigin + (↑(2 * Real.pi) : ℂ) * Complex.I
  rw [hpt, hcorner]; push_cast; ring
}

lemma regular_level_sublevel_nhds {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0)
    {W : Set ℂ} (hW : W ∈ 𝓝 z) :
    ∃ U : Set ℂ, IsOpen U ∧ z ∈ U ∧ U ⊆ W ∧
      IsPreconnected (U ∩ {w | f w < f z}) ∧
      (U ∩ {w | f w < f z}).Nonempty := by
{
  obtain ⟨e, hz, her, _⟩ := exists_regular_level_chart hf hp
  have het : e z ∈ e.target := e.map_source hz
  have hn : e.target ∩ e.symm ⁻¹' W ∈ 𝓝 (e z) :=
    inter_mem (e.open_target.mem_nhds het) ((e.continuousAt_symm het).preimage_mem_nhds
      (show W ∈ 𝓝 (e.symm (e z)) by rwa [e.left_inv hz]))
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hn
  let B := Metric.ball (e z) r
  let U := e.source ∩ e ⁻¹' B
  have hBU (b : ℂ) (hb : b ∈ B) : b ∈ e.target ∧ e.symm b ∈ U :=
    ⟨(hball hb).1, e.map_target (hball hb).1, by simpa only [mem_preimage, e.right_inv (hball hb).1] using hb⟩
  have he : U ∩ {w | f w < f z} = e.symm '' (B ∩ {b | b.re < f z}) := by
  {
    ext w
    refine ⟨fun ⟨hw, hfw⟩ => ⟨e w, ⟨hw.2, by simpa only [mem_setOf_eq, her] using hfw⟩, e.left_inv hw.1⟩, ?_⟩
    rintro ⟨b, ⟨hb, hbr⟩, rfl⟩
    refine ⟨(hBU b hb).2, ?_⟩
    have hh := her (e.symm b)
    rw [e.right_inv (hBU b hb).1] at hh
    change f (e.symm b) < f z
    rw [← hh]; exact hbr
  }
  have hconv : Convex ℝ (B ∩ {b : ℂ | b.re < f z}) :=
    (convex_ball (e z) r).inter ((convex_Iio (f z)).linear_preimage Complex.reCLM.toLinearMap)
  refine ⟨U, e.isOpen_inter_preimage Metric.isOpen_ball, ⟨hz, by simpa [B] using hr⟩,
    fun w hw => by simpa only [mem_preimage, e.left_inv hw.1] using (hball hw.2).2,
    he ▸ hconv.isPreconnected.image e.symm (e.continuousOn_symm.mono (fun b hb => (hBU b hb.1).1)), ?_⟩
  rw [he]
  refine Nonempty.image _ ⟨e z - (r / 2 : ℝ), ?_, ?_⟩
  · change dist (e z - (r / 2 : ℝ)) (e z) < r
    rw [dist_eq_norm, sub_sub_cancel_left, norm_neg, Complex.norm_real, Real.norm_eq_abs,
      abs_of_pos (by linarith : (0 : ℝ) < r / 2)]; linarith
  · change (e z - (r / 2 : ℝ)).re < f z
    rw [Complex.sub_re, Complex.ofReal_re, her]; linarith
}

lemma regular_level_frequently_below {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0) :
    ∃ᶠ w in 𝓝 z, f w < f z := by
{
  rw [frequently_iff]
  intro P hP
  obtain ⟨U, _, _, hUP, _, w, hwU, hwf⟩ := regular_level_sublevel_nhds hf hp hP
  exact ⟨w, hUP hwU, hwf⟩
}

lemma regular_level_local_integer {f : ℂ → ℝ} {j : ℂ → ℤ} {c : ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0) (hz : f z = c)
    (hj : ContinuousOn j {w | f w ≠ c}) (hj0 : ∀ w, c < f w → j w = 0) :
    ∃ n : ℤ, ∀ᶠ w in 𝓝 z, f w ≠ c → j w = if f w < c then n else 0 := by
{
  obtain ⟨U, hUo, hzU, _, hpc, w₀, hw₀, hfw₀⟩ := regular_level_sublevel_nhds hf hp
    (show (univ : Set ℂ) ∈ 𝓝 z from univ_mem)
  refine ⟨j w₀, ?_⟩
  filter_upwards [hUo.mem_nhds hzU] with w hw hne
  by_cases hlt : f w < c
  · rw [ite_eq_left hlt]
    have hdisc := (hpc.image j (hj.mono (fun v hv =>
      ne_of_lt (by simpa only [hz] using (show f v < f z from hv.2))))).subsingleton
    exact hdisc ⟨w, ⟨hw, by change f w < f z; simpa only [hz] using hlt⟩, rfl⟩ ⟨w₀, ⟨hw₀, hfw₀⟩, rfl⟩
  · rw [ite_eq_right hlt]
    exact hj0 w (lt_of_le_of_ne (not_lt.mp hlt) hne.symm)
}

lemma regular_level_local_integer_unique {f : ℂ → ℝ} {j : ℂ → ℤ} {c : ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0) (hz : f z = c)
    {m n : ℤ}
    (hm : ∀ᶠ w in 𝓝 z, f w ≠ c → j w = if f w < c then m else 0)
    (hn : ∀ᶠ w in 𝓝 z, f w ≠ c → j w = if f w < c then n else 0) : m = n := by
{
  obtain ⟨w, hw, hmw, hnw⟩ := ((regular_level_frequently_below hf hp).and_eventually
    (hm.and hn)).exists
  have hlt : f w < c := by simpa only [hz] using hw
  simpa only [ite_eq_left hlt] using (hmw hlt.ne).symm.trans (hnw hlt.ne)
}

lemma regular_level_integer_constant_along {f : ℂ → ℝ} {j : ℂ → ℤ}
    {c : ℝ} {γ : ℝ → ℂ} (hc : Continuous γ)
    (hf : ∀ t, ContDiffAt ℝ 1 f (γ t)) (hp : ∀ t, fderiv ℝ f (γ t) ≠ 0)
    (hz : ∀ t, f (γ t) = c) (hj : ContinuousOn j {w | f w ≠ c})
    (hj0 : ∀ w, c < f w → j w = 0) :
    ∃ n : ℤ, ∀ t, ∀ᶠ w in 𝓝 (γ t),
      f w ≠ c → j w = if f w < c then n else 0 := by
{
  choose n hn using fun t => regular_level_local_integer (hf t) (hp t) (hz t) hj hj0
  have hnc : Continuous n := by
  {
    apply continuous_iff_continuousAt.mpr
    intro t
    have he : ∀ᶠ s in 𝓝 t, n s = n t := by
    {
      filter_upwards [(hc.tendsto t).eventually (hn t).eventually_nhds] with s hs
      exact (regular_level_local_integer_unique (hf s) (hp s) (hz s) hs (hn s)).symm
    }
    exact continuousAt_const.congr (he.mono fun _ h => h.symm)
  }
  refine ⟨n 0, fun t => ?_⟩
  have he : n t = n 0 := TotallyDisconnectedSpace.eq_of_continuous n hnc t 0
  simpa only [he] using hn t
}

lemma regular_level_loop_local_index {f : ℂ → ℝ} {c : ℝ} {γ : ℝ → ℂ}
    (hc : Continuous γ) (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {d : ℂ}
    (hd : HasDerivAt γ d 0) (hdi : d.im < 0)
    (hmin : ∀ t, (γ 0).re ≤ (γ t).re)
    (hf : ∀ t, ContDiffAt ℝ 1 f (γ t))
    (hreg : ∀ t, fderiv ℝ f (γ t) ≠ 0) (hz : ∀ t, f (γ t) = c)
    (hbelow : ∀ w, w ∉ range γ → loopIndex (periodicLoop hc 0) w ≠ 0 → f w < c) :
    ∀ t, ∀ᶠ w in 𝓝 (γ t), f w ≠ c →
      loopIndex (periodicLoop hc 0) w = if f w < c then 1 else 0 := by
{
  have hj : ContinuousOn (loopIndex (periodicLoop hc 0)) {w | f w ≠ c} :=
    (continuousOn_loopIndex _ (periodicLoop_closed hc hp 0)).mono
      (fun w hw ⟨t, ht⟩ => hw (ht ▸ hz ((t : ℝ) + 0)))
  have hj0 : ∀ w, c < f w → loopIndex (periodicLoop hc 0) w = 0 := by
  {
    intro w hw; by_contra hn
    exact (hbelow w (by rintro ⟨t, rfl⟩; linarith [hz t]) hn).not_gt hw
  }
  obtain ⟨n, hn⟩ := regular_level_integer_constant_along hc hf hreg hz hj hj0
  obtain ⟨δ, hδ, hjump⟩ := winding_leftmost_normal hc hp hinj hd hdi hmin
  have ht : Tendsto (fun r : ℝ => γ 0 + r • (Complex.I * d)) (𝓝 0) (𝓝 (γ 0)) := by
  {
    have h : Continuous (fun r : ℝ => γ 0 + r • (Complex.I * d)) := by fun_prop
    simpa only [zero_smul, add_zero] using h.tendsto 0
  }
  obtain ⟨ε, hε, he⟩ := Metric.mem_nhds_iff.mp (ht.eventually (hn 0))
  let r := min δ ε / 2
  have hr : 0 < r := half_pos (lt_min hδ hε)
  obtain ⟨hoff, hi⟩ := hjump r hr (by dsimp [r]; linarith [min_le_left δ ε])
  have hlt := hbelow _ hoff (by rw [hi]; norm_num)
  have hh := he (show r ∈ Metric.ball (0 : ℝ) ε by
    simpa only [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hr] using
      (show r < ε by dsimp [r]; linarith [min_le_right δ ε])) hlt.ne
  have hne : n = 1 := by simpa only [ite_eq_left hlt, hi] using hh.symm
  simpa only [hne] using hn
}

/-!
## Part 2: Global Level Curve Orientation and Index Sum (`LevelIndex.lean`)
-/

lemma continuous_loopIndex_sublevel_diff.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι]
    (γ : ι → C(unitInterval, ℂ)) (hclosed : ∀ i, γ i 1 = γ i 0) {f : ℂ → ℝ} {c : ℝ}
    (hf : Continuous f) (hcover : ∀ z, f z = c ↔ ∃ i, z ∈ range (γ i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (range (γ i)) (range (γ j)))
    (hlocal : ∀ i z, z ∈ range (γ i) → ∀ᶠ w in 𝓝 z, f w ≠ c →
      loopIndex (γ i) w = if f w < c then 1 else 0)
    (hbelow : ∀ i w, w ∉ range (γ i) → loopIndex (γ i) w ≠ 0 → f w < c) :
    Continuous (fun z => if f z = c then (0 : ℤ) else
      ∑ i, loopIndex (γ i) z - if f z < c then 1 else 0) := by
{
  let J : ℂ → ℤ := fun z => if f z = c then 0 else ∑ i, loopIndex (γ i) z - if f z < c then 1 else 0
  have hzero (i : ι) (z : ℂ) (hz : c ≤ f z) (hoff : z ∉ range (γ i)) : loopIndex (γ i) z = 0 := by
    { by_contra hn; exact (hbelow i z hoff hn).not_ge hz }
  refine continuous_iff_continuousAt.mpr fun z => ?_
  by_cases hz : f z = c
  · obtain ⟨i, hiz⟩ := (hcover z).mp hz
    have hj : ∀ᶠ w in 𝓝 z, ∀ j, j ≠ i → loopIndex (γ j) w = 0 := Filter.eventually_all.mpr fun j => by
    {
      by_cases hji : j = i
      · exact Filter.Eventually.of_forall (fun _ h => (h hji).elim)
      · have hoff : z ∉ range (γ j) := fun hjz =>
          Set.disjoint_left.mp (hdisjoint i j (Ne.symm hji)) hiz hjz
        exact (loopIndex_eventually_eq (γ j) (hclosed j) hoff).mono fun w hw _ =>
          hw.trans (hzero j z hz.ge hoff)
    }
    refine continuousAt_const.congr ((hlocal i z hiz).and hj |>.mono fun w ⟨hw, hjw⟩ => (?_ : J w = 0).symm)
    dsimp only [J]; by_cases hwe : f w = c
    · rw [ite_eq_left hwe]
    · rw [ite_eq_right hwe, Finset.sum_eq_single i (fun j _ hji => hjw j hji) (by simp), hw hwe, sub_self]
  · have hgood (i) : z ∉ range (γ i) := fun hi => hz ((hcover z).mpr ⟨i, hi⟩)
    have hj : ∀ᶠ w in 𝓝 z, ∀ i, loopIndex (γ i) w = loopIndex (γ i) z :=
      Filter.eventually_all.mpr fun i => loopIndex_eventually_eq (γ i) (hclosed i) (hgood i)
    have hsign : ∀ᶠ w in 𝓝 z, f w ≠ c ∧ (f w < c ↔ f z < c) := by
    {
      by_cases hlt : f z < c
      · filter_upwards [(isOpen_lt hf continuous_const).mem_nhds hlt] with w hw; exact ⟨hw.ne, iff_of_true hw hlt⟩
      · filter_upwards [(isOpen_lt continuous_const hf).mem_nhds
          (lt_of_le_of_ne (not_lt.mp hlt) (Ne.symm hz))] with w hw; exact ⟨hw.ne', iff_of_false hw.not_gt hlt⟩
    }
    refine continuousAt_const.congr (hj.and hsign |>.mono fun w ⟨hjw, hw⟩ => (?_ : J w = J z).symm)
    simp only [J, ite_eq_right hz, ite_eq_right hw.1, Finset.sum_congr rfl (fun i _ => hjw i), hw.2]
}

lemma sum_loopIndex_sublevel.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι]
    (γ : ι → C(unitInterval, ℂ)) (hclosed : ∀ i, γ i 1 = γ i 0)
    {f : ℂ → ℝ} {c : ℝ} (hf : Continuous f)
    (hcover : ∀ z, f z = c ↔ ∃ i, z ∈ range (γ i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (range (γ i)) (range (γ j)))
    (hlocal : ∀ i z, z ∈ range (γ i) → ∀ᶠ w in 𝓝 z, f w ≠ c →
      loopIndex (γ i) w = if f w < c then 1 else 0)
    (hbelow : ∀ i w, w ∉ range (γ i) → loopIndex (γ i) w ≠ 0 → f w < c)
    (habove : ∃ z, c < f z) :
    ∀ z, f z ≠ c → ∑ i, loopIndex (γ i) z = if f z < c then 1 else 0 := by
{
  let J : ℂ → ℤ := fun z => if f z = c then 0 else
    ∑ i, loopIndex (γ i) z - if f z < c then 1 else 0
  have hcont : Continuous J :=
    continuous_loopIndex_sublevel_diff γ hclosed hf hcover hdisjoint hlocal hbelow
  obtain ⟨a, ha⟩ := habove
  have hJa : J a = 0 := by
  {
    have hs (i : ι) : loopIndex (γ i) a = 0 := by
    {
      by_contra hn
      exact (hbelow i a (fun hi => ha.ne ((hcover a).mpr ⟨i, hi⟩).symm) hn).not_ge ha.le
    }
    simp only [J, ite_eq_right ha.ne', ite_eq_right ha.not_gt, hs, Finset.sum_const_zero, sub_zero]
  }
  intro z hz
  have he := (TotallyDisconnectedSpace.eq_of_continuous J hcont z a).trans hJa
  change (if f z = c then (0 : ℤ) else _) = 0 at he
  rw [ite_eq_right hz, sub_eq_zero] at he
  exact he
}

lemma windingNumber_normal_field {γ : ℝ → ℂ} (hγ : ContDiff ℝ 1 γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hd : ∀ t, deriv γ t ≠ 0)
    (hm : ∀ t, (γ 0).re ≤ (γ t).re)
    (hr : (deriv γ 0).re = 0) (hi : (deriv γ 0).im < 0)
    (X : C(ℂ, ℂ)) (hX : ∀ t, X (γ t) ≠ 0)
    (horth : ∀ t, (X (γ t) * (conj (deriv γ t))).re = 0) :
    windingNumber (X.comp (periodicLoop hγ.continuous 0)) = 1 := by
{
  let T : C(unitInterval, ℂ) := ⟨fun t => deriv γ t,
    (hγ.continuous_deriv (by simp)).comp continuous_subtype_val⟩
  let R : C(unitInterval, ℂ) := ⟨fun t => X (γ t) / deriv γ t,
    (X.continuous.comp (hγ.continuous.comp continuous_subtype_val)).div T.continuous (fun t => hd t)⟩
  have hTloop : T 1 = T 0 := (periodic_deriv hp).eq
  have hRloop : R 1 = R 0 := by
  {
    change X (γ 1) / deriv γ 1 = X (γ 0) / deriv γ 0
    rw [hp.eq, (periodic_deriv hp).eq]
  }
  have hRn (t) : R t ≠ 0 := div_ne_zero (hX t) (hd t)
  have hRslit (t) : R t ∈ Complex.slitPlane := by
  {
    refine Or.inr (fun him => hRn t (Complex.ext ?_ him))
    change (X (γ t) / deriv γ t).re = 0
    rw [Complex.div_re, ← add_div]
    have hh := horth t
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, mul_neg, sub_neg_eq_add] at hh
    rw [hh, zero_div]
  }
  have hwindR : windingNumber R = 0 := by
  {
    apply windingNumber_eq_of_logIncrement hRloop
    simpa only [hRloop, sub_self, Int.cast_zero, zero_mul] using HasLogIncrement.of_slit R hRslit
  }
  have hwindT : windingNumber T = 1 := by
  {
    apply windingNumber_eq_of_logIncrement hTloop
    obtain ⟨A, hA, hinc⟩ := tangent_turning_log hγ hp hinj (fun t _ => hd t) (fun t _ => hm t) hr hi
    refine ⟨A, hA, ?_⟩
    rw [hinc, add_sub_cancel_left]; simp only [Int.cast_one, one_mul]; push_cast; ring
  }
  have he : X.comp (periodicLoop hγ.continuous 0) = T * R := by
  {
    ext t; change X (γ ((t : ℝ) + 0)) = deriv γ t * (X (γ t) / deriv γ t)
    rw [add_zero, mul_div_cancel₀ _ (hd t)]
  }
  rw [he, windingNumber_mul T R hTloop hRloop (fun t => hd t) hRn, hwindT, hwindR, add_zero]
}

lemma periodic_simple_eq_of_near {γ : ℝ → ℂ} (hp : Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {a b : ℝ}
    (he : γ a = γ b) (hab : |a - b| < 1) : a = b := by
{
  have hh (t : ℝ) : γ (Int.fract t) = γ t := by
  {
    simpa only [Int.fract, mul_one] using hp.sub_int_mul_eq (x := t) ⌊t⌋
  }
  have hfr : Int.fract a = Int.fract b := hinj
    ⟨Int.fract_nonneg a, Int.fract_lt_one a⟩ ⟨Int.fract_nonneg b, Int.fract_lt_one b⟩
    ((hh a).trans (he.trans (hh b).symm))
  obtain ⟨n, hn⟩ := Int.fract_eq_fract.mp hfr
  rw [hn] at hab
  have hnlo : (-1 : ℤ) < n := by exact_mod_cast (abs_lt.mp hab).1
  have hnhi : n < (1 : ℤ) := by exact_mod_cast (abs_lt.mp hab).2
  have hn0 : n = 0 := by linarith
  rw [hn0, Int.cast_zero] at hn
  exact sub_eq_zero.mp hn
}

lemma periodic_simple_shift {γ : ℝ → ℂ} (hp : Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) (s : ℝ) :
    InjOn (fun t => γ (t + s)) (Ico (0 : ℝ) 1) := by
{
  intro a ha b hb he
  have hh : |(a + s) - (b + s)| < 1 := by
  {
    rw [abs_lt]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  }
  have heq := periodic_simple_eq_of_near hp hinj he hh
  linarith
}

lemma periodic_simple_reverse {γ : ℝ → ℂ} (hp : Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) :
    InjOn (fun t => γ (-t)) (Ico (0 : ℝ) 1) := by
{
  intro a ha b hb he
  have hh : |(-a) - (-b)| < 1 := by
  {
    rw [abs_lt]; constructor <;> linarith [ha.1, ha.2, hb.1, hb.2]
  }
  have heq := periodic_simple_eq_of_near hp hinj he hh
  linarith
}

lemma orient_reverse_curve {η : ℝ → ℂ} (hηc : ContDiff ℝ 1 η)
    (hηp : Periodic η 1) (hηinj : InjOn η (Ico (0 : ℝ) 1))
    (hηd : ∀ t, deriv η t ≠ 0) (hηmin : ∀ t, (η 0).re ≤ (η t).re)
    (hηre : (deriv η 0).re = 0) (him : 0 < (deriv η 0).im) :
    let κ : ℝ → ℂ := fun t => η (-t)
    range κ = range η ∧ ContDiff ℝ 1 κ ∧
      Periodic κ 1 ∧ InjOn κ (Ico (0 : ℝ) 1) ∧ (∀ t, deriv κ t ≠ 0) ∧
      (∀ t, (κ 0).re ≤ (κ t).re) ∧ (deriv κ 0).re = 0 ∧ (deriv κ 0).im < 0 := by
{
  let κ : ℝ → ℂ := fun t => η (-t)
  have hκr : range κ = range η := Subset.antisymm
    (by rintro _ ⟨t, rfl⟩; exact ⟨-t, rfl⟩)
    (by rintro _ ⟨t, rfl⟩; exact ⟨-t, by simp [κ]⟩)
  refine ⟨hκr, hηc.comp contDiff_id.neg, fun t => ?_,
    periodic_simple_reverse hηp hηinj, fun t => ?_,
    fun t => by simpa only [κ, neg_zero] using hηmin (-t), ?_, ?_⟩
  · change η (-(t + 1)) = η (-t)
    rw [show -(t + 1) = -t - 1 by ring, hηp.sub_eq]
  · rw [deriv_comp_neg]; exact neg_ne_zero.mpr (hηd (-t))
  · rw [deriv_comp_neg, neg_zero, Complex.neg_re, hηre, neg_zero]
  · rw [deriv_comp_neg, neg_zero, Complex.neg_im]; exact neg_neg_of_pos him
}

lemma orient_unit_curve {γ : ℝ → ℂ} (hc : ContDiff ℝ 1 γ)
    (hp : Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    (hd : ∀ t, deriv γ t ≠ 0) :
    ∃ η : ℝ → ℂ, range η = range γ ∧ ContDiff ℝ 1 η ∧
      Periodic η 1 ∧ InjOn η (Ico (0 : ℝ) 1) ∧ (∀ t, deriv η t ≠ 0) ∧
      (∀ t, (η 0).re ≤ (η t).re) ∧ (deriv η 0).re = 0 ∧ (deriv η 0).im < 0 := by
{
  have hk : IsCompact (range γ) := by
  {
    rw [← periodicLoop_range hc.continuous hp 0]
    exact isCompact_range (periodicLoop hc.continuous 0).continuous
  }
  obtain ⟨z, ⟨s, rfl⟩, hmin⟩ := hk.exists_isMinOn ⟨γ 0, ⟨0, rfl⟩⟩ Complex.continuous_re.continuousOn
  let η : ℝ → ℂ := fun t => γ (t + s)
  have hηr : range η = range γ := Subset.antisymm
    (by rintro _ ⟨t, rfl⟩; exact ⟨t + s, rfl⟩)
    (by rintro _ ⟨t, rfl⟩; exact ⟨t - s, by simp only [η, sub_add_cancel]⟩)
  have hηc : ContDiff ℝ 1 η := hc.comp (contDiff_id.add contDiff_const)
  have hηp : Periodic η 1 := hp.add_const s
  have hηinj : InjOn η (Ico (0 : ℝ) 1) := periodic_simple_shift hp hinj s
  have hηd (t) : deriv η t ≠ 0 := by dsimp only [η]; rw [deriv_comp_add_const]; exact hd (t + s)
  have hηmin (t) : (η 0).re ≤ (η t).re := by
  {
    simpa only [η, zero_add] using (show (γ s).re ≤ (γ (t + s)).re from hmin ⟨t + s, rfl⟩)
  }
  have hlocal : IsLocalMin (fun t => (η t).re) 0 := Filter.Eventually.of_forall hηmin
  have hηre : (deriv η 0).re = 0 := hlocal.hasDerivAt_eq_zero
    (Complex.reCLM.hasFDerivAt.comp_hasDerivAt 0 ((hηc.differentiable (by simp)) 0).hasDerivAt)
  by_cases hi : (deriv η 0).im < 0
  · exact ⟨η, hηr, hηc, hηp, hηinj, hηd, hηmin, hηre, hi⟩
  · have him : 0 < (deriv η 0).im :=
      lt_of_le_of_ne (not_lt.mp hi) (fun he => hηd 0 (Complex.ext hηre he.symm))
    have hrev := orient_reverse_curve hηc hηp hηinj hηd hηmin hηre him
    exact ⟨fun t => η (-t), hrev.1.trans hηr, hrev.2⟩
}

lemma orient_periodic_curve {γ : ℝ → ℂ} {P : ℝ} (hP : 0 < P)
    (hc : ContDiff ℝ 1 γ) (hp : Periodic γ P) (hinj : InjOn γ (Ico (0 : ℝ) P))
    (hd : ∀ t, deriv γ t ≠ 0) :
    ∃ η : ℝ → ℂ, range η = range γ ∧ ContDiff ℝ 1 η ∧
      Periodic η 1 ∧ InjOn η (Ico (0 : ℝ) 1) ∧ (∀ t, deriv η t ≠ 0) ∧
      (∀ t, (η 0).re ≤ (η t).re) ∧ (deriv η 0).re = 0 ∧ (deriv η 0).im < 0 := by
{
  let κ : ℝ → ℂ := fun t => γ (P * t)
  have hκr : range κ = range γ := Subset.antisymm
    (by rintro _ ⟨t, rfl⟩; exact ⟨P * t, rfl⟩)
    (by rintro _ ⟨t, rfl⟩; exact ⟨t / P, by simp [κ, mul_div_cancel₀ _ hP.ne']⟩)
  have hκc : ContDiff ℝ 1 κ := hc.comp (contDiff_const.mul contDiff_id)
  have hκp : Periodic κ 1 := fun t => by change γ (P * (t + 1)) = γ (P * t); rw [mul_add, mul_one, hp]
  have hκinj : InjOn κ (Ico (0 : ℝ) 1) := fun a ha b hb he =>
    (mul_left_cancel₀ hP.ne') (hinj ⟨mul_nonneg hP.le ha.1, by nlinarith [ha.2]⟩
      ⟨mul_nonneg hP.le hb.1, by nlinarith [hb.2]⟩ he)
  have hκd (t) : deriv κ t ≠ 0 := by
  {
    dsimp only [κ]; rw [deriv_comp_mul_left]; exact smul_ne_zero hP.ne' (hd (P * t))
  }
  obtain ⟨η, hηr, hh⟩ := orient_unit_curve hκc hκp hκinj hκd
  exact ⟨η, hηr.trans hκr, hh⟩
}

lemma regular_level_index_sum.{u_1} {ι : Type u_1} [Fintype ι] [DecidableEq ι]
    {f : ℂ → ℝ} {c : ℝ} (hf : Continuous f) (γ : ι → ℝ → ℂ) (hc : ∀ i, ContDiff ℝ 1 (γ i))
    (hp : ∀ i, Periodic (γ i) 1) (hi : ∀ i, InjOn (γ i) (Ico (0 : ℝ) 1))
    (hd : ∀ i t, deriv (γ i) t ≠ 0) (hm : ∀ i t, (γ i 0).re ≤ (γ i t).re)
    (hr : ∀ i, (deriv (γ i) 0).re = 0) (hdown : ∀ i, (deriv (γ i) 0).im < 0)
    (hlevel : ∀ i t, f (γ i t) = c)
    (hfreg : ∀ z, f z = c → ContDiffAt ℝ 1 f z ∧ fderiv ℝ f z ≠ 0)
    (hcover : ∀ z, f z = c ↔ ∃ i, z ∈ range (γ i))
    (hdisjoint : ∀ i j, i ≠ j → Disjoint (range (γ i)) (range (γ j)))
    (hbelow : ∀ i w, w ∉ range (γ i) → loopIndex (periodicLoop (hc i).continuous 0) w ≠ 0 → f w < c)
    (habove : ∃ z, c < f z) {K : Set ℂ} (hK : Convex ℝ K) (hγK : ∀ i t, γ i t ∈ K)
    (s : Finset ℂ) (X : C(ℂ, ℂ)) (A : ℂ → ℂ →L[ℝ] ℂ)
    (hsK : ∀ z ∈ s, z ∈ K) (hzero : ∀ z ∈ K, X z = 0 ↔ z ∈ s)
    (hD : ∀ z ∈ s, HasFDerivAt X (A z) z ∧ LinearMap.det (A z).toLinearMap ≠ 0)
    (hX : ∀ i t, X (γ i t) ≠ 0) (horth : ∀ i t, (X (γ i t) * conj (deriv (γ i) t)).re = 0) :
    ∑ a ∈ s, (if f a < c then planeIndex (A a) else 0) = (Fintype.card ι : ℤ) := by
{
  let Γ (i : ι) := periodicLoop (hc i).continuous 0
  have hΓclosed (i) : Γ i 1 = Γ i 0 := periodicLoop_closed _ (hp i) 0
  have hΓrange (i) : range (Γ i) = range (γ i) := periodicLoop_range _ (hp i) 0
  have hΓlocal (i) (z) (hz : z ∈ range (Γ i)) :
      ∀ᶠ w in 𝓝 z, f w ≠ c → loopIndex (Γ i) w = if f w < c then 1 else 0 := by
  {
    obtain ⟨t, rfl⟩ := (hΓrange i) ▸ hz
    exact regular_level_loop_local_index (hc i).continuous (hp i) (hi i)
      (((hc i).differentiable (by simp)) 0).hasDerivAt (hdown i) (hm i)
      (fun t => (hfreg _ (hlevel i t)).1) (fun t => (hfreg _ (hlevel i t)).2) (hlevel i) (hbelow i) t
  }
  have hsum := sum_loopIndex_sublevel Γ hΓclosed hf (fun z => by simp only [hΓrange]; exact hcover z)
    (fun i j hij => by rw [hΓrange, hΓrange]; exact hdisjoint i j hij)
    hΓlocal (fun i w hw => by rw [hΓrange] at hw; exact hbelow i w hw) habove
  have hnotlevel (a) (ha : a ∈ s) : f a ≠ c := fun hal =>
    let ⟨i, t, ht⟩ := (hcover a).mp hal; hX i t (ht ▸ (hzero a (hsK a ha)).mpr ha)
  have hindex (i) : (1 : ℤ) = ∑ a ∈ s, planeIndex (A a) * loopIndex (Γ i) a := by
  {
    have h := windingNumber_finite_regular_zeros hK s X A hsK hzero hD (Γ i) (hΓclosed i)
      (fun t => hγK i ((t : ℝ) + 0)) (fun t => hX i ((t : ℝ) + 0))
    rwa [windingNumber_normal_field (hc i) (hp i) (hi i) (hd i) (hm i) (hr i) (hdown i) X (hX i) (horth i)] at h
  }
  calc
    ∑ a ∈ s, (if f a < c then planeIndex (A a) else 0) =
        ∑ a ∈ s, planeIndex (A a) * (∑ i, loopIndex (Γ i) a) :=
      Finset.sum_congr rfl (fun a ha => by rw [hsum a (hnotlevel a ha)]; split_ifs <;> simp)
    _ = ∑ i, ∑ a ∈ s, planeIndex (A a) * loopIndex (Γ i) a := by simp only [Finset.mul_sum]; exact Finset.sum_comm
    _ = ∑ _i : ι, (1 : ℤ) := Finset.sum_congr rfl (fun i _ => (hindex i).symm)
    _ = (Fintype.card ι : ℤ) := by simp
}

def tangentGradient (f : ℂ → ℝ) (z : ℂ) : ℂ :=
  (-(fderiv ℝ f z Complex.I) : ℂ) + Complex.I * (fderiv ℝ f z 1 : ℂ)

lemma tangentGradient_orthogonal (f : ℂ → ℝ) (z : ℂ) :
    fderiv ℝ f z (tangentGradient f z) = 0 := by
{
  rw [realFunctional_decomposition]
  simp only [tangentGradient, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im]
  ring
}

lemma tangentGradient_ne_zero {f : ℂ → ℝ} {z : ℂ} (h : fderiv ℝ f z ≠ 0) :
    tangentGradient f z ≠ 0 := by
{
  intro he
  have hre := congrArg Complex.re he
  have him := congrArg Complex.im he
  simp only [tangentGradient, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.zero_re, Complex.zero_im] at hre him
  apply h
  ext w
  rw [realFunctional_decomposition]
  simp only [zero_mul, one_mul, sub_zero, neg_zero, zero_add, add_zero, neg_eq_zero] at hre him
  simp only [him, hre, mul_zero, add_zero, ContinuousLinearMap.zero_apply]
}

lemma tangentGradient_contDiff {f : ℂ → ℝ} (hf : ContDiff ℝ 2 f) :
    ContDiff ℝ 1 (tangentGradient f) := by
{
  have hd := hf.fderiv_right (show (1 : WithTop ℕ∞) + 1 ≤ 2 by norm_num)
  exact ((Complex.ofRealCLM.contDiff.comp (hd.clm_apply contDiff_const)).neg).add
    (contDiff_const.mul (Complex.ofRealCLM.contDiff.comp (hd.clm_apply contDiff_const)))
}

lemma tangentGradient_hasCompactSupport {f : ℂ → ℝ} {d : ℝ}
    (hs : HasCompactSupport (fun z => f z - d)) : HasCompactSupport (tangentGradient f) := by
{
  have hD := hs.fderiv ℝ
  apply hD.mono'
  intro z hz
  by_contra hn
  have hzer : fderiv ℝ (fun z => f z - d) z = 0 := notMem_support.mp
    (fun h => hn (subset_tsupport _ h))
  have hfzero : fderiv ℝ f z = 0 := by simpa only [fderiv_sub_const] using hzer
  exact hz (by simp only [tangentGradient, hfzero, ContinuousLinearMap.zero_apply,
    Complex.ofReal_zero, neg_zero, mul_zero, add_zero])
}

lemma compact_regular_level_oriented_curves {f : ℂ → ℝ} {c d : ℝ}
    (hf : ContDiff ℝ 2 f) (hs : HasCompactSupport (fun z => f z - d))
    (hreg : ∀ z, f z = c → fderiv ℝ f z ≠ 0)
    (hK : IsCompact {z | f z = c}) :
    ∃ C : Finset (Set ℂ), (⋃ S ∈ C, S) = {z | f z = c} ∧
      (∀ S ∈ C, ∀ T ∈ C, S ≠ T → Disjoint S T) ∧
      ∀ S ∈ C, ∃ γ : ℝ → ℂ, range γ = S ∧ ContDiff ℝ 1 γ ∧
        Periodic γ 1 ∧ InjOn γ (Ico (0 : ℝ) 1) ∧ (∀ t, deriv γ t ≠ 0) ∧
        (∀ t, (γ 0).re ≤ (γ t).re) ∧ (deriv γ 0).re = 0 ∧ (deriv γ 0).im < 0 := by
{
  obtain ⟨C, hC, hdis, hcurves⟩ := compact_regular_level_finite_curves
    (hf.of_le (by norm_num)) (tangentGradient_contDiff hf) (tangentGradient_hasCompactSupport hs)
    (tangentGradient_orthogonal f) hreg (fun z hz => tangentGradient_ne_zero (hreg z hz)) hK
  refine ⟨C, hC, hdis, fun S hS => ?_⟩
  obtain ⟨γ, P, hP, hrange, hD, hper, hinj⟩ := hcurves S hS
  have hlevel (t) : f (γ t) = c := by
  {
    have hm : γ t ∈ ⋃ S ∈ C, S := mem_iUnion₂.mpr ⟨S, hS, hrange ▸ mem_range_self t⟩
    rwa [hC] at hm
  }
  obtain ⟨η, hηrange, hη⟩ := orient_periodic_curve hP
    (integral_curve_contDiff_one (tangentGradient_contDiff hf).continuous hD)
    hper hinj (fun t => by rw [(hD t).deriv]; exact tangentGradient_ne_zero (hreg _ (hlevel t)))
  exact ⟨η, hηrange.trans hrange, hη⟩
}

lemma loopIndex_zero_of_im_lt (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    {a : ℂ} (ha : ∀ t, a.im < (γ t).im) : loopIndex γ a = 0 := by
{
  have hslit (t) : γ t - a ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (ne_of_gt (sub_pos.mpr (ha t))))
  apply windingNumber_eq_of_logIncrement (by simp [hloop])
  refine ⟨⟨fun t => Complex.log (γ t - a), Continuous.clog (by fun_prop) hslit⟩,
    fun t => Complex.exp_log (Complex.slitPlane_ne_zero (hslit t)), by simp [hloop]⟩
}

lemma closure_windingInterior_subset_H (γ : C(unitInterval, ℂ))
    (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ∈ H) :
    closure (windingInterior γ) ⊆ H := by
{
  obtain ⟨d, hd, hdist⟩ := isCompact_univ.exists_forall_le'
    (show ContinuousOn (fun t : unitInterval => (γ t).im) univ by fun_prop)
    (a := 0) (fun t _ => hγ t)
  have hsub : windingInterior γ ⊆ {a : ℂ | d ≤ a.im} := by
  {
    intro a ha; by_contra hn
    exact ha.2 (loopIndex_zero_of_im_lt γ hloop
      (fun t => (lt_of_not_ge hn).trans_le (hdist t (mem_univ t))))
  }
  have hc := closure_minimal hsub (isClosed_le continuous_const Complex.continuous_im)
  exact fun a ha => hd.trans_le (hc ha)
}

lemma extend_compact_sublevel_smooth {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ}
    (hf : ∀ z ∈ U, ContDiffAt ℝ 2 f z) {d : ℝ}
    (hK : IsCompact {z | z ∈ U ∧ f z ≤ d}) :
    ∃ F : ℂ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport (fun z => F z - d) ∧
      (∀ z, z ∈ U → f z ≤ d → F =ᶠ[𝓝 z] f) ∧
      (∀ z ∉ U, F z = d) ∧
      (∀ z ∈ U, d ≤ f z → d ≤ F z) := by
{
  obtain ⟨χ, hχc, hχK, hχU, hχ1, hχrange⟩ := exists_smooth_cutoff hK hU (fun _ h => h.1)
  let F := fun z => χ z * (f z - d) + d
  have heq (z) (hz : z ∈ U) (hzd : f z ≤ d) : F =ᶠ[𝓝 z] f := by
  {
    filter_upwards [hχ1 z ⟨hz, hzd⟩] with w hw
    simp only [F, hw, one_mul, sub_add_cancel]
  }
  have hzero (z) (hz : z ∉ tsupport χ) : F =ᶠ[𝓝 z] fun _ => d := by
  {
    filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hz] with w hw
    have hh : χ w = 0 := notMem_support.mp (fun h => hw (subset_tsupport χ h))
    simp only [F, hh, zero_mul, zero_add]
  }
  have hFc : ContDiff ℝ 2 F := by
  {
    rw [contDiff_iff_contDiffAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact (hχc.contDiffAt.mul ((hf z (hχU hz)).sub contDiffAt_const)).add contDiffAt_const
    · exact contDiffAt_const.congr_of_eventuallyEq (hzero z hz)
  }
  have hFK : HasCompactSupport (fun z => F z - d) := by
  {
    apply hχK.mono'
    intro z hz; by_contra hn
    exact hz (sub_eq_zero.mpr (hzero z hn).self_of_nhds)
  }
  exact ⟨F, hFc, hFK, heq, fun z hz => (hzero z (fun h => hz (hχU h))).self_of_nhds,
    fun z _ hdz => le_add_of_nonneg_left (mul_nonneg (hχrange z).1 (sub_nonneg.mpr hdz))⟩
}

lemma extend_compact_sublevel {U : Set ℂ} (hU : IsOpen U) {f : ℂ → ℝ}
    (hf : ∀ z ∈ U, ContDiffAt ℝ 2 f z) {d : ℝ}
    (hK : IsCompact {z | z ∈ U ∧ f z ≤ d}) :
    ∃ F : ℂ → ℝ, ContDiff ℝ 2 F ∧ HasCompactSupport (fun z => F z - d) ∧
      (∀ z, z ∈ U → f z ≤ d → F =ᶠ[𝓝 z] f) ∧
      (∀ z ∉ U, F z = d) ∧
      (∀ z c, c < d → (F z ≤ c ↔ z ∈ U ∧ f z ≤ c)) ∧
      (∀ z c, c < d → (F z < c ↔ z ∈ U ∧ f z < c)) := by
{
  obtain ⟨F, hFc, hFK, heq, hFd, hlarge⟩ := extend_compact_sublevel_smooth hU hf hK
  refine ⟨F, hFc, hFK, heq, hFd, fun z c hc => ?_, fun z c hc => ?_⟩
  · refine ⟨fun hz => ?_, fun ⟨hzU, hz⟩ => by rwa [(heq z hzU (hz.trans hc.le)).self_of_nhds]⟩
    have hzU : z ∈ U := by by_contra hn; rw [hFd z hn] at hz; exact hc.not_ge hz
    have hzd : f z ≤ d := by by_contra hn; exact hc.not_ge ((hlarge z hzU (not_le.mp hn).le).trans hz)
    exact ⟨hzU, (heq z hzU hzd).self_of_nhds ▸ hz⟩
  · refine ⟨fun hz => ?_, fun ⟨hzU, hz⟩ => by rwa [(heq z hzU (hz.le.trans hc.le)).self_of_nhds]⟩
    have hzU : z ∈ U := by by_contra hn; rw [hFd z hn] at hz; exact hc.not_gt hz
    have hzd : f z ≤ d := by by_contra hn; exact hc.not_gt ((hlarge z hzU (not_le.mp hn).le).trans_lt hz)
    exact ⟨hzU, (heq z hzU hzd).self_of_nhds ▸ hz⟩
}

/-!
## Part 3: Subharmonic Potential, Regularized Gradient, and Critical Count
-/

def criticalMap (f : ℂ → ℂ) (k : ℝ) (z : ℂ) : ℂ :=
  f z - Complex.I / (k : ℂ) * (z.im : ℂ) * deriv f z

def normalizedJacobian (f : ℂ → ℂ) (k : ℝ) (z : ℂ) : ℝ :=
  LinearMap.det (fderiv ℝ (criticalMap f k) z).toLinearMap / ‖deriv f z‖^2

def potential (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℝ≥0∞ :=
  (ENNReal.ofReal z.im) ^ k / ENNReal.ofReal ‖f z - ξ‖

def GoodPair (f : ℂ → ℂ) (k : ℝ) (ξ : ℂ) : Prop :=
  (∀ δ : ℝ, 0 < δ → IsCompact {z | z ∈ H ∧ ENNReal.ofReal δ ≤ potential f k ξ z}) ∧
  (∀ z ∈ H, criticalMap f k z = ξ → normalizedJacobian f k z ≠ 0)

lemma differentiableAt_criticalMap {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {z : ℂ} (hz : z ∈ H) (k : ℝ) :
    DifferentiableAt ℝ (criticalMap f k) z := by
{
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_H z hz
  exact ((han.differentiableAt.restrictScalars ℝ).sub
    (((Complex.ofRealCLM.differentiableAt.comp z Complex.imCLM.differentiableAt).const_mul
      (Complex.I / (k : ℂ))).mul (han.deriv.differentiableAt.restrictScalars ℝ)))
}

lemma critical_fiber_discrete_H {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} {ξ : ℂ} (hreg : ∀ z ∈ H, criticalMap f k z = ξ → normalizedJacobian f k z ≠ 0) :
    IsDiscrete {z | z ∈ H ∧ criticalMap f k z = ξ} := by
{
  rw [isDiscrete_iff_nhdsNE]
  intro z hz
  have hd : LinearMap.det (fderiv ℝ (criticalMap f k) z).toLinearMap ≠ 0 :=
    (div_ne_zero_iff.mp (hreg z hz.1 hz.2)).1
  let e : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hd)).toContinuousLinearEquiv
  have he : (e : ℂ → ℂ) = fderiv ℝ (criticalMap f k) z :=
    funext (fun w => LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr hd) w)
  have ha : ∃ C, AntilipschitzWith C (fderiv ℝ (criticalMap f k) z) := by
  {
    rw [← he]; exact ⟨_, e.antilipschitz⟩
  }
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [(differentiableAt_criticalMap hf hz.1 k).hasFDerivAt.eventually_ne (c := ξ) ha] with w hw
  exact fun h => hw h.2
}

lemma finite_critical_superlevel {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} {ξ : ℂ} (hg : GoodPair f k ξ) {h : ℝ} (hh : 0 < h) :
    {z | z ∈ H ∧ criticalMap f k z = ξ ∧ ENNReal.ofReal h ≤ potential f k ξ z}.Finite := by
{
  let P := {z | z ∈ H ∧ ENNReal.ofReal h ≤ potential f k ξ z}
  have hP : IsCompact P := hg.1 h hh
  have hc : ContinuousOn (criticalMap f k) P :=
    fun z hz => (differentiableAt_criticalMap hf hz.1 k).continuousAt.continuousWithinAt
  have hclosed := hc.preimage_isClosed_of_isClosed hP.isClosed (isClosed_singleton (x := ξ))
  have hcompact : IsCompact (P ∩ (criticalMap f k) ⁻¹' {ξ}) :=
    hP.of_isClosed_subset hclosed inter_subset_left
  have hdiscrete := (critical_fiber_discrete_H hf hg.2).mono
    (show P ∩ (criticalMap f k) ⁻¹' {ξ} ⊆ {z | z ∈ H ∧ criticalMap f k z = ξ} from fun _ hz => ⟨hz.1.1, hz.2⟩)
  convert hcompact.finite hdiscrete using 1
  ext z
  simp only [P, mem_setOf_eq, mem_inter_iff, mem_preimage, mem_singleton_iff]
  tauto
}

def logPotential (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℝ :=
  k * Real.log z.im - Real.log ‖f z - ξ‖

lemma differentiableAt_log_norm {g : ℂ → ℂ} {z : ℂ}
    (hg : DifferentiableAt ℂ g z) (hn : g z ≠ 0) :
    DifferentiableAt ℝ (fun w => Real.log ‖g w‖) z := by
{
  exact ((hg.restrictScalars ℝ).norm ℂ hn).log (norm_ne_zero_iff.mpr hn)
}

lemma fderiv_log_norm_apply {g : ℂ → ℂ} {d z : ℂ} (hg : HasDerivAt g d z)
    (hn : g z ≠ 0) (v : ℂ) :
    fderiv ℝ (fun w => Real.log ‖g w‖) z v = (d * v / g z).re := by
{
  have heq : (fun w => Real.log ‖g w‖) = (fun w => (1 / 2 : ℝ) * Real.log (‖g w‖ ^ 2)) := by
  {
    funext w; rw [Real.log_pow]; ring
  }
  have hh := (((hg.hasFDerivAt.restrictScalars ℝ).norm_sq).log
    (pow_ne_zero 2 (norm_ne_zero_iff.mpr hn))).const_mul (1 / 2 : ℝ)
  rw [heq, hh.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, innerSL_apply_apply, Complex.inner, Complex.mul_re, Complex.conj_re,
    Complex.conj_im, Complex.mul_im, Complex.div_re, Complex.normSq_eq_norm_sq]
  ring
}

lemma differentiableAt_logPotential {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {z ξ : ℂ} (hz : z ∈ H) (hp : f z ≠ ξ) (k : ℝ) :
    DifferentiableAt ℝ (logPotential f k ξ) z := by
{
  have hd := (hf.1 z hz).differentiableAt (isOpen_H.mem_nhds hz)
  exact ((Complex.imCLM.differentiableAt.log (ne_of_gt hz)).const_mul k).sub
    (differentiableAt_log_norm (hd.sub_const ξ) (sub_ne_zero.mpr hp))
}

lemma fderiv_logPotential_apply {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {z ξ : ℂ} (hz : z ∈ H) (hp : f z ≠ ξ) (k : ℝ) (v : ℂ) :
    fderiv ℝ (logPotential f k ξ) z v =
      k / z.im * v.im - (deriv f z * v / (f z - ξ)).re := by
{
  have hd := (hf.1 z hz).differentiableAt (isOpen_H.mem_nhds hz)
  have ha := (Complex.imCLM.hasFDerivAt.log (ne_of_gt hz)).const_mul k
  simp only [Complex.imCLM_apply] at ha
  have hb := differentiableAt_log_norm (hd.sub_const ξ) (sub_ne_zero.mpr hp)
  change fderiv ℝ (fun w => k * Real.log w.im - Real.log ‖f w - ξ‖) z v = _
  rw [fderiv_fun_sub ha.differentiableAt hb, ContinuousLinearMap.sub_apply, ha.fderiv,
    fderiv_log_norm_apply (hd.hasDerivAt.sub_const ξ) (sub_ne_zero.mpr hp)]
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul, Complex.imCLM_apply, div_eq_mul_inv]
  ring
}

lemma criticalMap_ne_pole {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} (hk : k ≠ 0) {z ξ : ℂ} (hz : z ∈ H)
    (hc : criticalMap f k z = ξ) : f z ≠ ξ := by
{
  intro hp
  have hn := mul_ne_zero (mul_ne_zero (div_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr hk)) (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
    (deriv_ne_zero_of_univalentOn isOpen_H hf hz)
  apply hn
  simpa [criticalMap, hp] using hc
}

def targetRatio (f : ℂ → ℂ) (ξ z : ℂ) : ℂ := deriv f z / (f z - ξ)

lemma hasDerivAt_targetRatio {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {z ξ : ℂ} (hz : z ∈ H) (hp : f z ≠ ξ) :
    HasDerivAt (targetRatio f ξ)
      ((deriv (deriv f) z * (f z - ξ) - deriv f z * deriv f z) / (f z - ξ)^2) z := by
{
  have han : AnalyticAt ℂ f z := hf.1.analyticOnNhd isOpen_H z hz
  exact han.deriv.differentiableAt.hasDerivAt.div
    (han.differentiableAt.hasDerivAt.sub_const ξ) (sub_ne_zero.mpr hp)
}

def secondDirectional (u : ℂ → ℝ) (z v w : ℂ) : ℝ :=
  fderiv ℝ (fun t => fderiv ℝ u t v) z w

def realHessian (u : ℂ → ℝ) (z : ℂ) : Matrix (Fin 2) (Fin 2) ℝ :=
  !![secondDirectional u z 1 1, secondDirectional u z 1 Complex.I;
    secondDirectional u z Complex.I 1, secondDirectional u z Complex.I Complex.I]

lemma secondDirectional_logPotential_one {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {z ξ : ℂ} (hz : z ∈ H) (hp : f z ≠ ξ) (k : ℝ) (v : ℂ) :
    secondDirectional (logPotential f k ξ) z 1 v =
      -(deriv (targetRatio f ξ) z * v).re := by
{
  have hd := (hf.1 z hz).differentiableAt (isOpen_H.mem_nhds hz)
  have hn := hd.continuousAt.eventually_ne hp
  have heq : (fun w => fderiv ℝ (logPotential f k ξ) w 1) =ᶠ[𝓝 z]
      (fun w => -(targetRatio f ξ w).re) := by
  {
    filter_upwards [isOpen_H.mem_nhds hz, hn] with w hw hne
    simp only [fderiv_logPotential_apply hf hw hne, Complex.one_im, mul_zero,
      mul_one, zero_sub, targetRatio]
  }
  have hr := (hasDerivAt_targetRatio hf hz hp).differentiableAt.hasDerivAt
  have hh := (Complex.reCLM.hasFDerivAt.comp z (hr.hasFDerivAt.restrictScalars ℝ)).neg
  change HasFDerivAt (fun w => -(targetRatio f ξ w).re) _ z at hh
  rw [secondDirectional, heq.fderiv_eq, hh.fderiv]
  simp only [ContinuousLinearMap.neg_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, Complex.reCLM_apply, mul_comm v]
}

lemma secondDirectional_logPotential_I {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {z ξ : ℂ} (hz : z ∈ H) (hp : f z ≠ ξ) (k : ℝ) (v : ℂ) :
    secondDirectional (logPotential f k ξ) z Complex.I v =
      -k / z.im^2 * v.im + (deriv (targetRatio f ξ) z * v).im := by
{
  have hd := (hf.1 z hz).differentiableAt (isOpen_H.mem_nhds hz)
  have hn := hd.continuousAt.eventually_ne hp
  have heq : (fun w => fderiv ℝ (logPotential f k ξ) w Complex.I) =ᶠ[𝓝 z]
      (fun w => k / w.im + (targetRatio f ξ w).im) := by
  {
    filter_upwards [isOpen_H.mem_nhds hz, hn] with w hw hne
    rw [fderiv_logPotential_apply hf hw hne,
      show deriv f w * Complex.I / (f w - ξ) = (deriv f w / (f w - ξ)) * Complex.I by ring]
    simp only [Complex.I_im, mul_one, Complex.mul_I_re, sub_neg_eq_add, targetRatio]
  }
  have hr := (hasDerivAt_targetRatio hf hz hp).differentiableAt.hasDerivAt
  have ha := (((hasDerivAt_inv (ne_of_gt hz)).hasFDerivAt).comp z
    Complex.imCLM.hasFDerivAt).const_mul k
  have hb := Complex.imCLM.hasFDerivAt.comp z (hr.hasFDerivAt.restrictScalars ℝ)
  have hh := ha.add hb
  change HasFDerivAt (fun w => k * w.im⁻¹ + (targetRatio f ξ w).im) _ z at hh
  simp only [← div_eq_mul_inv] at hh
  rw [secondDirectional, heq.fderiv_eq, hh.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    Complex.imCLM_apply, mul_comm v]
  ring
}

lemma realHessian_logPotential {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {z ξ : ℂ} (hz : z ∈ H) (hp : f z ≠ ξ) (k : ℝ) :
    realHessian (logPotential f k ξ) z =
      !![-(deriv (targetRatio f ξ) z).re, (deriv (targetRatio f ξ) z).im;
        (deriv (targetRatio f ξ) z).im, -k / z.im^2 + (deriv (targetRatio f ξ) z).re] := by
{
  simp only [realHessian, secondDirectional_logPotential_one hf hz hp,
    secondDirectional_logPotential_I hf hz hp, mul_one, Complex.mul_I_re,
    Complex.mul_I_im, Complex.one_im, Complex.I_im, mul_zero, mul_one, zero_add, neg_neg]
}

lemma trace_realHessian_negative {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} (hk : 0 < k) {z ξ : ℂ} (hz : z ∈ H) (hp : f z ≠ ξ) :
    Matrix.trace (realHessian (logPotential f k ξ) z) < 0 := by
{
  have ht : Matrix.trace (realHessian (logPotential f k ξ) z) = -k / z.im^2 := by
  {
    rw [realHessian_logPotential hf hz hp]
    simp [Matrix.trace, Matrix.diag, Fin.sum_univ_two]
  }
  rw [ht]
  exact div_neg_of_neg_of_pos (neg_neg_of_pos hk) (sq_pos_of_pos hz)
}

lemma second_derivative_nonneg_at_min_zero {f f' : ℝ → ℝ} {b : ℝ}
    (hmin : IsLocalMin f 0) (hf : ∀ᶠ x in 𝓝 0, HasDerivAt f (f' x) x)
    (hf' : HasDerivAt f' b 0) : 0 ≤ b := by
{
  by_contra hb
  have hb' : b < 0 := lt_of_not_ge hb
  have hzero : f' 0 = 0 := hmin.hasDerivAt_eq_zero hf.self_of_nhds
  have hrem := (hasDerivAt_iff_isLittleO_nhds_zero.mp hf').bound (by linarith : 0 < -b / 2)
  have he : ∀ᶠ x in 𝓝 (0 : ℝ),
      HasDerivAt f (f' x) x ∧ f 0 ≤ f x ∧ |f' x - x * b| ≤ (-b / 2) * |x| := by
  {
    filter_upwards [hf, hmin, hrem] with x hdx hmx hrx
    exact ⟨hdx, hmx, by simpa [hzero, Real.norm_eq_abs] using hrx⟩
  }
  obtain ⟨δ, hδ, hall⟩ := Metric.eventually_nhds_iff.mp he
  have hball {x : ℝ} (hx : x ∈ Icc 0 (δ / 2)) : dist x 0 < δ := by
  {
    rw [Real.dist_eq, sub_zero, abs_of_nonneg hx.1]; linarith [hx.2]
  }
  obtain ⟨c, hcint, hceq⟩ := exists_deriv_eq_slope f (by linarith : 0 < δ / 2)
    (fun x hx => (hall (hball hx)).1.continuousAt.continuousWithinAt)
    (fun x hx => (hall (hball (Ioo_subset_Icc_self hx))).1.differentiableAt.differentiableWithinAt)
  have hcl := hall (hball (Ioo_subset_Icc_self hcint))
  rw [hcl.1.deriv] at hceq
  have hend := (hall (hball (show δ / 2 ∈ Icc 0 (δ / 2) by constructor <;> linarith))).2.1
  have hf'c : 0 ≤ f' c := hceq ▸ div_nonneg (sub_nonneg.mpr hend) (by linarith)
  have hupper := (le_abs_self (f' c - c * b)).trans hcl.2.2
  rw [abs_of_pos hcint.1] at hupper
  nlinarith [mul_neg_of_pos_of_neg hcint.1 hb']
}

lemma second_directional_nonneg_at_min {u : ℂ → ℝ} {z v : ℂ}
    (hmin : IsLocalMin u z)
    (hu : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ u w)
    (hv : DifferentiableAt ℝ (fun w => fderiv ℝ u w v) z) :
    0 ≤ fderiv ℝ (fun w => fderiv ℝ u w v) z v := by
{
  let g : ℝ → ℂ := fun t => z + t • v
  have hg (t : ℝ) : HasDerivAt g v t := by
  {
    simpa [g] using (hasDerivAt_id t).smul_const v |>.const_add z
  }
  have hgz : g 0 = z := by simp [g]
  have hmin' : IsLocalMin (u ∘ g) 0 := (hgz ▸ hmin).comp_continuous (hg 0).continuousAt
  have hu' : ∀ᶠ t in 𝓝 (0 : ℝ), HasDerivAt (u ∘ g) (fderiv ℝ u (g t) v) t := by
  {
    have ht : Tendsto g (𝓝 0) (𝓝 z) := hgz ▸ (hg 0).continuousAt
    filter_upwards [ht.eventually hu] with t ht
    exact ht.hasFDerivAt.comp_hasDerivAt t (hg t)
  }
  have hv' : HasDerivAt (fun t => fderiv ℝ u (g t) v)
      (fderiv ℝ (fun w => fderiv ℝ u w v) z v) 0 :=
    hv.hasFDerivAt.comp_hasDerivAt_of_eq 0 (hg 0) hgz.symm
  exact second_derivative_nonneg_at_min_zero hmin' hu' hv'
}

lemma differentiableAt_fderiv_logPotential_apply {f : ℂ → ℂ}
    (hf : UnivalentOn f H) {z ξ : ℂ} (hz : z ∈ H)
    (hp : f z ≠ ξ) (k : ℝ) (v : ℂ) :
    DifferentiableAt ℝ (fun w => fderiv ℝ (logPotential f k ξ) w v) z := by
{
  have hd := (hf.1 z hz).differentiableAt (isOpen_H.mem_nhds hz)
  have hn := hd.continuousAt.eventually_ne hp
  have heq : (fun w => fderiv ℝ (logPotential f k ξ) w v) =ᶠ[𝓝 z]
      (fun w => k / w.im * v.im - (targetRatio f ξ w * v).re) := by
  {
    filter_upwards [isOpen_H.mem_nhds hz, hn] with w hw hne
    rw [fderiv_logPotential_apply hf hw hne]; unfold targetRatio; congr 2; ring
  }
  have ha : DifferentiableAt ℝ (fun w : ℂ => k / w.im * v.im) z := by
  {
    have hi := (hasDerivAt_inv (ne_of_gt hz)).differentiableAt.comp z Complex.imCLM.differentiableAt
    simpa only [div_eq_mul_inv, Function.comp_def, Complex.imCLM_apply] using
      (hi.const_mul k).mul_const v.im
  }
  have hb : DifferentiableAt ℝ (fun w => (targetRatio f ξ w * v).re) z :=
    Complex.reCLM.differentiableAt.comp z
      (((hasDerivAt_targetRatio hf hz hp).differentiableAt.restrictScalars ℝ).mul_const v)
  exact (ha.sub hb).congr_of_eventuallyEq heq
}

lemma not_isLocalMin_logPotential {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} (hk : 0 < k) {z ξ : ℂ} (hz : z ∈ H) (hp : f z ≠ ξ) :
    ¬ IsLocalMin (logPotential f k ξ) z := by
{
  intro hmin
  have hd := (hf.1 z hz).differentiableAt (isOpen_H.mem_nhds hz)
  have hu : ∀ᶠ w in 𝓝 z, DifferentiableAt ℝ (logPotential f k ξ) w := by
  {
    filter_upwards [isOpen_H.mem_nhds hz, hd.continuousAt.eventually_ne hp] with w hw hne
    exact differentiableAt_logPotential hf hw hne k
  }
  have h1 := second_directional_nonneg_at_min hmin hu
    (differentiableAt_fderiv_logPotential_apply hf hz hp k 1)
  have hI := second_directional_nonneg_at_min hmin hu
    (differentiableAt_fderiv_logPotential_apply hf hz hp k Complex.I)
  have ht := trace_realHessian_negative hf hk hz hp
  simp only [realHessian, Matrix.trace, Matrix.diag, Fin.sum_univ_two,
    Matrix.of_apply, Matrix.cons_val_zero, Matrix.cons_val_one] at ht
  change secondDirectional _ z 1 1 + secondDirectional _ z Complex.I Complex.I < 0 at ht
  unfold secondDirectional at ht
  linarith
}

def reciprocalPotential (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℝ :=
  ‖f z - ξ‖ / z.im ^ k

lemma continuousOn_reciprocalPotential {f : ℂ → ℂ} (hf : UnivalentOn f H)
    (k : ℝ) (ξ : ℂ) : ContinuousOn (reciprocalPotential f k ξ) H := by
{
  apply ((hf.1.continuousOn.sub continuousOn_const).norm).div
    (Complex.continuous_im.continuousOn.rpow_const (fun z hz => Or.inl (ne_of_gt hz)))
  exact fun z hz => ne_of_gt (Real.rpow_pos_of_pos hz k)
}

lemma reciprocalPotential_pos {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ}
    (hz : z ∈ H) (hp : f z ≠ ξ) : 0 < reciprocalPotential f k ξ z := by
{
  exact div_pos (norm_pos_iff.mpr (sub_ne_zero.mpr hp)) (Real.rpow_pos_of_pos hz k)
}

lemma log_reciprocalPotential {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ}
    (hz : z ∈ H) (hp : f z ≠ ξ) :
    Real.log (reciprocalPotential f k ξ z) = -logPotential f k ξ z := by
{
  rw [reciprocalPotential, Real.log_div (norm_ne_zero_iff.mpr (sub_ne_zero.mpr hp))
    (ne_of_gt (Real.rpow_pos_of_pos hz k)), Real.log_rpow hz, logPotential]
  ring
}

lemma not_isLocalMax_reciprocalPotential {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} (hk : 0 < k) {z ξ : ℂ} (hz : z ∈ H) (hp : f z ≠ ξ) :
    ¬ IsLocalMax (reciprocalPotential f k ξ) z := by
{
  intro hmax
  apply not_isLocalMin_logPotential hf hk hz hp
  have hd := (hf.1 z hz).differentiableAt (isOpen_H.mem_nhds hz)
  filter_upwards [hmax, isOpen_H.mem_nhds hz, hd.continuousAt.eventually_ne hp]
    with w hw hwH hwne
  have hl := Real.log_le_log (reciprocalPotential_pos hwH hwne) hw
  rw [log_reciprocalPotential hwH hwne, log_reciprocalPotential hz hp] at hl
  linarith
}

lemma reciprocalPotential_lt_boundary {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k b : ℝ} (hk : 0 < k) (hb : 0 < b) (ξ : ℂ) {U : Set ℂ}
    (ho : IsOpen U) (hcompact : IsCompact (closure U))
    (hH : closure U ⊆ H)
    (hboundary : ∀ z ∈ frontier U, reciprocalPotential f k ξ z ≤ b)
    {z : ℂ} (hz : z ∈ U) : reciprocalPotential f k ξ z < b := by
{
  have hcont := (continuousOn_reciprocalPotential hf k ξ).mono hH
  obtain ⟨a, ha, hmax⟩ := hcompact.exists_isMaxOn ⟨z, subset_closure hz⟩ hcont
  have hmaxle : reciprocalPotential f k ξ a ≤ b := by
  {
    by_contra hn
    have hab : b < reciprocalPotential f k ξ a := lt_of_not_ge hn
    have haU : a ∈ U := by
    {
      by_contra hau
      exact (not_lt_of_ge (hboundary a ⟨ha, by simpa only [ho.interior_eq] using hau⟩)) hab
    }
    have hane : f a ≠ ξ := fun he => by
      have he0 : reciprocalPotential f k ξ a = 0 := by simp [reciprocalPotential, he]
      linarith
    exact not_isLocalMax_reciprocalPotential hf hk (hH ha) hane
      (hmax.isLocalMax (mem_of_superset (ho.mem_nhds haU) subset_closure))
  }
  have hwhole : ∀ w ∈ closure U, reciprocalPotential f k ξ w ≤ b :=
    fun w hw => (hmax hw).trans hmaxle
  apply lt_of_le_of_ne (hwhole z (subset_closure hz))
  intro he
  have hzne : f z ≠ ξ := fun hze => by
    have he0 : reciprocalPotential f k ξ z = 0 := by simp [reciprocalPotential, hze]
    linarith
  apply not_isLocalMax_reciprocalPotential hf hk (hH (subset_closure hz)) hzne
  filter_upwards [ho.mem_nhds hz] with w hw
  exact (hwhole w (subset_closure hw)).trans_eq he.symm
}

lemma reciprocalPotential_lt_on_windingInterior {f : ℂ → ℂ}
    (hf : UnivalentOn f H) {k b : ℝ} (hk : 0 < k) (hb : 0 < b) (ξ : ℂ)
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ∈ H)
    (hlevel : ∀ t, reciprocalPotential f k ξ (γ t) = b)
    {z : ℂ} (hz : z ∈ windingInterior γ) : reciprocalPotential f k ξ z < b := by
{
  apply reciprocalPotential_lt_boundary hf hk hb ξ (isOpen_windingInterior γ hloop)
    ((isBounded_windingInterior γ hloop).isCompact_closure)
    (closure_windingInterior_subset_H γ hloop hγ) _ hz
  intro w hw
  obtain ⟨t, rfl⟩ := frontier_windingInterior_subset γ hloop hw
  exact (hlevel t).le
}

def regularizedGradient (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℂ :=
  ((k : ℂ) * Complex.I / (z.im : ℂ)) * (f z - ξ) * conj (criticalMap f k z - ξ)

lemma regularizedGradient_eq_zero_iff {f : ℂ → ℂ} {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ H) :
    regularizedGradient f k ξ z = 0 ↔ f z = ξ ∨ criticalMap f k z = ξ := by
{
  have hc : ((k : ℂ) * Complex.I / (z.im : ℂ)) ≠ 0 := div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk) Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hz))
  simp only [regularizedGradient, mul_eq_zero, hc, false_or, sub_eq_zero, map_eq_zero]
}

lemma differentiableAt_gradientCoefficient {z : ℂ} (hz : z ∈ H) (k : ℝ) :
    DifferentiableAt ℝ (fun w : ℂ => (k : ℂ) * Complex.I / (w.im : ℂ)) z := by
{
  have hn : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hi := ((hasDerivAt_inv hn).differentiableAt.restrictScalars ℝ).comp z
    ((Complex.ofRealCLM.comp Complex.imCLM).differentiableAt)
  simpa only [div_eq_mul_inv, Function.comp_def, ContinuousLinearMap.comp_apply,
    Complex.ofRealCLM_apply, Complex.imCLM_apply] using hi.const_mul ((k : ℂ) * Complex.I)
}

lemma differentiableAt_regularizedGradient {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {z : ℂ} (hz : z ∈ H) (k : ℝ) (ξ : ℂ) :
    DifferentiableAt ℝ (regularizedGradient f k ξ) z := by
{
  have hd := ((hf.1 z hz).differentiableAt (isOpen_H.mem_nhds hz)).restrictScalars ℝ
  exact ((differentiableAt_gradientCoefficient hz k).mul (hd.sub_const ξ)).mul
    (Complex.conjCLE.differentiableAt.comp z ((differentiableAt_criticalMap hf hz k).sub_const ξ))
}

lemma hasFDerivAt_regularizedGradient_at_critical {f : ℂ → ℂ}
    (hf : UnivalentOn f H) {k : ℝ} {ξ z : ℂ} (hz : z ∈ H)
    (hc : criticalMap f k z = ξ) :
    HasFDerivAt (regularizedGradient f k ξ)
      ((((k : ℂ) * Complex.I / (z.im : ℂ)) * (f z - ξ)) •
        (Complex.conjCLE.toContinuousLinearMap.comp (fderiv ℝ (criticalMap f k) z))) z := by
{
  have hd := ((hf.1 z hz).differentiableAt (isOpen_H.mem_nhds hz)).restrictScalars ℝ
  have hG := (differentiableAt_criticalMap hf hz k).hasFDerivAt.sub_const ξ
  have hh := ((differentiableAt_gradientCoefficient hz k).hasFDerivAt.fun_mul
    (hd.hasFDerivAt.sub_const ξ)).fun_mul (Complex.conjCLE.hasFDerivAt.comp z hG)
  convert hh using 1 <;>
    first | rfl | simp only [Function.comp_def, hc, sub_self, map_zero, zero_smul, add_zero]
}

lemma hasFDerivAt_regularizedGradient_at_pole {f : ℂ → ℂ}
    (hf : UnivalentOn f H) {k : ℝ} {ξ z : ℂ} (hz : z ∈ H)
    (hp : f z = ξ) :
    HasFDerivAt (regularizedGradient f k ξ)
      ((((k : ℂ) * Complex.I / (z.im : ℂ)) * conj (criticalMap f k z - ξ)) •
        (fderiv ℝ f z)) z := by
{
  have hd := ((hf.1 z hz).differentiableAt (isOpen_H.mem_nhds hz)).restrictScalars ℝ
  have hG := (differentiableAt_criticalMap hf hz k).hasFDerivAt.sub_const ξ
  have hh := ((differentiableAt_gradientCoefficient hz k).hasFDerivAt.fun_mul
    (hd.hasFDerivAt.sub_const ξ)).fun_mul (Complex.conjCLE.hasFDerivAt.comp z hG)
  convert hh using 1 <;>
    first | rfl | simp only [Function.comp_def, hp, sub_self, mul_zero, zero_smul,
      zero_add, add_zero, smul_smul, Complex.conjCLE_apply, mul_comm]
}

lemma det_conj_comp (A : ℂ →L[ℝ] ℂ) :
    LinearMap.det (Complex.conjCLE.toContinuousLinearMap.comp A).toLinearMap =
      -LinearMap.det A.toLinearMap := by
{
  rw [det_complex_real_eq, det_complex_real_eq]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.comp_apply,
    ContinuousLinearEquiv.coe_coe, Complex.conjCLE_apply, Complex.conj_re, Complex.conj_im]
  ring
}

lemma det_regularizedGradient_at_critical {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} {ξ z : ℂ} (hz : z ∈ H) (hc : criticalMap f k z = ξ) :
    LinearMap.det (fderiv ℝ (regularizedGradient f k ξ) z).toLinearMap =
      -‖((k : ℂ) * Complex.I / (z.im : ℂ)) * (f z - ξ)‖^2 * ‖deriv f z‖^2 *
        normalizedJacobian f k z := by
{
  rw [(hasFDerivAt_regularizedGradient_at_critical hf hz hc).fderiv,
    det_complex_smul, det_conj_comp, normalizedJacobian]
  have hd : ‖deriv f z‖ ≠ 0 := norm_ne_zero_iff.mpr (deriv_ne_zero_of_univalentOn isOpen_H hf hz)
  field_simp
}

lemma det_regularizedGradient_at_pole_pos {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} (hk : k ≠ 0) {ξ z : ℂ} (hz : z ∈ H) (hp : f z = ξ) :
    0 < LinearMap.det (fderiv ℝ (regularizedGradient f k ξ) z).toLinearMap := by
{
  have hG : criticalMap f k z ≠ ξ := fun hc => criticalMap_ne_pole hf hk hz hc hp
  rw [(hasFDerivAt_regularizedGradient_at_pole hf hz hp).fderiv, det_complex_smul,
    det_fderiv_complex ((hf.1 z hz).differentiableAt (isOpen_H.mem_nhds hz))]
  refine mul_pos (sq_pos_of_pos (norm_pos_iff.mpr ?_))
    (sq_pos_of_pos (norm_pos_iff.mpr (deriv_ne_zero_of_univalentOn isOpen_H hf hz)))
  exact mul_ne_zero (div_ne_zero
    (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk) Complex.I_ne_zero)
    (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
    ((map_ne_zero (starRingEnd ℂ)).mpr (sub_ne_zero.mpr hG))
}

/-!
## Part 4: Squared Reciprocal Potential and `critical_count` (`CriticalCount.lean`)
-/

def squaredReciprocalPotential (f : ℂ → ℂ) (k : ℝ) (ξ z : ℂ) : ℝ :=
  ‖f z - ξ‖^2 * z.im ^ (-2 * k)

lemma squaredReciprocalPotential_eq_sq {f : ℂ → ℂ} {k : ℝ} {ξ z : ℂ}
    (hz : z ∈ H) :
    squaredReciprocalPotential f k ξ z = (reciprocalPotential f k ξ z)^2 := by
{
  rw [squaredReciprocalPotential, reciprocalPotential, div_pow]
  have he : z.im ^ (-2 * k) = ((z.im ^ k)^2)⁻¹ := by
  {
    rw [show -2 * k = -(k * 2) by ring, Real.rpow_neg hz.le, Real.rpow_mul hz.le, Real.rpow_two]
  }
  rw [he, div_eq_mul_inv]
}

lemma contDiffAt_squaredReciprocalPotential {f : ℂ → ℂ}
    (hf : UnivalentOn f H) {z : ℂ} (hz : z ∈ H) (k : ℝ) (ξ : ℂ) :
    ContDiffAt ℝ 2 (squaredReciprocalPotential f k ξ) z := by
{
  have hc : ContDiffAt ℝ 2 f z :=
    (hf.1.analyticOnNhd isOpen_H z hz).contDiffAt.restrict_scalars ℝ
  exact ((hc.sub contDiffAt_const).norm_sq ℂ).mul
    (Complex.imCLM.contDiff.contDiffAt.rpow_const_of_ne (ne_of_gt hz))
}

lemma potential_ge_iff_reciprocalPotential_le {f : ℂ → ℂ} {k h : ℝ}
    (hk : 0 ≤ k) (hh : 0 < h) {ξ z : ℂ} (hz : z ∈ H) :
    ENNReal.ofReal h ≤ potential f k ξ z ↔ reciprocalPotential f k ξ z ≤ h⁻¹ := by
{
  have hy := Real.rpow_pos_of_pos hz k
  rw [potential, ENNReal.ofReal_rpow_of_nonneg hz.le hk,
    ENNReal.le_div_iff_mul_le
      (Or.inr (ne_of_gt (ENNReal.ofReal_pos.mpr hy))) (Or.inl ENNReal.ofReal_ne_top),
    ← ENNReal.ofReal_mul hh.le, ENNReal.ofReal_le_ofReal_iff hy.le, reciprocalPotential,
    div_le_iff₀ hy, inv_mul_eq_div, le_div_iff₀ hh]
  exact mul_comm h ‖f z - ξ‖ ▸ Iff.rfl
}

lemma compact_squaredReciprocal_sublevel {f : ℂ → ℂ} {k : ℝ} (hk : 0 ≤ k)
    {ξ : ℂ} (hg : GoodPair f k ξ) {d : ℝ} (hd : 0 < d) :
    IsCompact {z | z ∈ H ∧ squaredReciprocalPotential f k ξ z ≤ d} := by
{
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  have he : {z | z ∈ H ∧ squaredReciprocalPotential f k ξ z ≤ d} =
      {z | z ∈ H ∧ ENNReal.ofReal ((Real.sqrt d)⁻¹) ≤ potential f k ξ z} := by
  {
    ext z
    constructor
    · rintro ⟨hz, hzval⟩
      refine ⟨hz, (potential_ge_iff_reciprocalPotential_le hk (inv_pos.mpr hs) hz).mpr ?_⟩
      rw [inv_inv]; rw [squaredReciprocalPotential_eq_sq hz] at hzval
      nlinarith [Real.sq_sqrt hd.le]
    · rintro ⟨hz, hzval⟩
      have hv := (potential_ge_iff_reciprocalPotential_le hk (inv_pos.mpr hs) hz).mp hzval
      rw [inv_inv] at hv
      refine ⟨hz, ?_⟩
      rw [squaredReciprocalPotential_eq_sq hz]
      have hn : 0 ≤ reciprocalPotential f k ξ z := div_nonneg (norm_nonneg _) (Real.rpow_nonneg hz.le _)
      nlinarith [Real.sq_sqrt hd.le]
  }
  rw [he]
  exact hg.1 _ (inv_pos.mpr hs)
}

lemma regularizedGradient_formula {f : ℂ → ℂ} {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ H) :
    regularizedGradient f k ξ z =
      ((k : ℂ) * Complex.I / (z.im : ℂ)) * ((‖f z - ξ‖^2 : ℝ) : ℂ) -
        (f z - ξ) * conj (deriv f z) := by
{
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hkc : (k : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hk
  have he : conj (criticalMap f k z - ξ) = conj (f z - ξ) +
      Complex.I / (k : ℂ) * (z.im : ℂ) * conj (deriv f z) := by
  {
    simp only [criticalMap, div_eq_mul_inv, map_sub, map_mul, map_inv₀, Complex.conj_I, Complex.conj_ofReal]
    ring
  }
  rw [regularizedGradient, he, mul_add, mul_assoc _ (f z - ξ), Complex.mul_conj',
    ← Complex.ofReal_pow]
  field_simp
  ring_nf
  simp only [Complex.I_sq]
  ring
}

lemma fderiv_squaredReciprocalPotential_apply {f : ℂ → ℂ}
    (hf : UnivalentOn f H) {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ H) (v : ℂ) :
    fderiv ℝ (squaredReciprocalPotential f k ξ) z v =
      -2 * z.im ^ (-2 * k) * (regularizedGradient f k ξ z * conj v).re := by
{
  have hd := (((hf.1 z hz).differentiableAt (isOpen_H.mem_nhds hz)).hasDerivAt.sub_const ξ).hasFDerivAt.restrictScalars ℝ
  have hy := Complex.imCLM.hasFDerivAt.rpow_const (p := -2 * k) (Or.inl (ne_of_gt hz))
  have hu := hd.norm_sq.fun_mul hy
  simp only [Complex.imCLM_apply] at hu
  change (fderiv ℝ (fun w => ‖f w - ξ‖ ^ 2 * w.im ^ (-2 * k)) z) v = _
  rw [hu.fderiv]
  simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul, innerSL_apply_apply, Complex.imCLM_apply]
  rw [regularizedGradient_formula hk hz, Real.rpow_sub hz, Real.rpow_one]
  simp only [Complex.inner, Complex.mul_re, Complex.mul_im, Complex.conj_re, Complex.conj_im,
    Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.normSq_ofReal]
  field_simp [ne_of_gt (show 0 < z.im from hz)]
  ring
}

lemma fderiv_squaredReciprocalPotential_eq_zero_iff {f : ℂ → ℂ}
    (hf : UnivalentOn f H) {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ H) :
    fderiv ℝ (squaredReciprocalPotential f k ξ) z = 0 ↔
      regularizedGradient f k ξ z = 0 := by
{
  constructor
  · intro hzero
    have hh := fderiv_squaredReciprocalPotential_apply hf hk (ξ := ξ) hz
      (regularizedGradient f k ξ z)
    rw [hzero, ContinuousLinearMap.zero_apply, Complex.mul_conj', ← Complex.ofReal_pow, Complex.ofReal_re] at hh
    have hp := Real.rpow_pos_of_pos hz (-2 * k)
    apply norm_eq_zero.mp
    have hsq : ‖regularizedGradient f k ξ z‖^2 = 0 :=
      (mul_eq_zero.mp hh.symm).resolve_left (mul_ne_zero (by norm_num) (ne_of_gt hp))
    nlinarith [norm_nonneg (regularizedGradient f k ξ z)]
  · intro hzero
    ext v
    rw [fderiv_squaredReciprocalPotential_apply hf hk hz v, hzero]
    simp
}

lemma det_regularizedGradient_ne_zero {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} (hk : k ≠ 0) {ξ : ℂ} (hg : GoodPair f k ξ)
    {z : ℂ} (hz : z ∈ H) (hzero : regularizedGradient f k ξ z = 0) :
    LinearMap.det (fderiv ℝ (regularizedGradient f k ξ) z).toLinearMap ≠ 0 := by
{
  rcases (regularizedGradient_eq_zero_iff hk hz).mp hzero with hp | hc
  · exact ne_of_gt (det_regularizedGradient_at_pole_pos hf hk hz hp)
  · rw [det_regularizedGradient_at_critical hf hz hc]
    refine mul_ne_zero (mul_ne_zero ?_ ?_) (hg.2 z hz hc)
    · exact neg_ne_zero.mpr (pow_ne_zero 2 (norm_ne_zero_iff.mpr
        (mul_ne_zero (div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk)
          Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
          (sub_ne_zero.mpr (criticalMap_ne_pole hf hk hz hc)))))
    · exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (deriv_ne_zero_of_univalentOn isOpen_H hf hz))
}

lemma compact_convex_H_envelope {P : Set ℂ} (hP : IsCompact P) (hPH : P ⊆ H) :
    ∃ K : Set ℂ, IsCompact K ∧ Convex ℝ K ∧ P ⊆ K ∧ K ⊆ H := by
{
  obtain ⟨η, hη, hheight⟩ := hP.exists_forall_le' Complex.continuous_im.continuousOn hPH
  obtain ⟨R, hR⟩ := hP.isBounded.subset_closedBall (0 : ℂ)
  refine ⟨Metric.closedBall 0 R ∩ {z : ℂ | η ≤ z.im},
    (isCompact_closedBall 0 R).inter_right (isClosed_le continuous_const Complex.continuous_im),
    (convex_closedBall (0 : ℂ) R).inter (convex_halfSpace_im_ge η),
    fun z hz => ⟨hR hz, hheight z hz⟩, fun z hz => hη.trans_le hz.2⟩
}

lemma continuous_extension_near_compact {K U : Set ℂ} (hK : IsCompact K)
    (hU : IsOpen U) (hKU : K ⊆ U) {x : ℂ → ℂ}
    (hx : ∀ z ∈ U, ContinuousAt x z) :
    ∃ X : C(ℂ, ℂ), ∀ z ∈ K, (X : ℂ → ℂ) =ᶠ[𝓝 z] x := by
{
  obtain ⟨χ, hχc, _hχK, hχU, hχ1, _hχrange⟩ := exists_smooth_cutoff hK hU hKU
  let X := fun z => (χ z : ℂ) * x z
  have hX : Continuous X := by
  {
    rw [continuous_iff_continuousAt]
    intro z
    by_cases hz : z ∈ tsupport χ
    · exact (Complex.continuous_ofReal.continuousAt.comp hχc.continuous.continuousAt).mul
        (hx z (hχU hz))
    · have he : X =ᶠ[𝓝 z] fun _ => 0 := by
      {
        filter_upwards [isClosed_tsupport χ |>.isOpen_compl.mem_nhds hz] with w hw
        have hzero : χ w = 0 := notMem_support.mp (fun h => hw (subset_tsupport χ h))
        simp only [X, hzero, Complex.ofReal_zero, zero_mul]
      }
      exact continuousAt_const.congr he.symm
  }
  refine ⟨⟨X, hX⟩, fun z hz => ?_⟩
  filter_upwards [hχ1 z hz] with w hw
  simp only [ContinuousMap.coe_mk, X, hw, Complex.ofReal_one, one_mul]
}

lemma squaredReciprocalPotential_lt_windingInterior {f : ℂ → ℂ}
    (hf : UnivalentOn f H) {k c : ℝ} (hk : 0 < k) (hc : 0 < c) (ξ : ℂ)
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ∈ H)
    (hlevel : ∀ t, squaredReciprocalPotential f k ξ (γ t) = c)
    {z : ℂ} (hz : z ∈ windingInterior γ) :
    z ∈ H ∧ squaredReciprocalPotential f k ξ z < c := by
{
  have hzH := closure_windingInterior_subset_H γ hloop hγ (subset_closure hz)
  have hb : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have hl (t) : reciprocalPotential f k ξ (γ t) = Real.sqrt c := by
  {
    have hsq := hlevel t
    rw [squaredReciprocalPotential_eq_sq (hγ t)] at hsq
    have hn : 0 ≤ reciprocalPotential f k ξ (γ t) :=
      div_nonneg (norm_nonneg _) (Real.rpow_nonneg (hγ t).le _)
    nlinarith [Real.sq_sqrt hc.le]
  }
  have hh := reciprocalPotential_lt_on_windingInterior hf hk hb ξ γ hloop hγ hl hz
  have hn : 0 ≤ reciprocalPotential f k ξ z :=
    div_nonneg (norm_nonneg _) (Real.rpow_nonneg hzH.le _)
  refine ⟨hzH, ?_⟩
  rw [squaredReciprocalPotential_eq_sq hzH]
  nlinarith [Real.sq_sqrt hc.le]
}

lemma extend_potential_sublevel {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} (hk : 0 < k) {ξ : ℂ} (hg : GoodPair f k ξ) {c : ℝ} (hc : 0 < c)
    (hreg : ∀ z ∈ H, squaredReciprocalPotential f k ξ z = c → regularizedGradient f k ξ z ≠ 0) :
    ∃ (K : Set ℂ) (F : ℂ → ℝ),
      IsCompact K ∧ Convex ℝ K ∧ K ⊆ H ∧
      ({z | z ∈ H ∧ squaredReciprocalPotential f k ξ z ≤ c + 1} ⊆ K) ∧
      ContDiff ℝ 2 F ∧ HasCompactSupport (fun z => F z - (c + 1)) ∧
      (∀ z ∈ H, squaredReciprocalPotential f k ξ z ≤ c + 1 → F =ᶠ[𝓝 z] squaredReciprocalPotential f k ξ) ∧
      F 0 = c + 1 ∧
      (∀ z, (F z < c ↔ z ∈ H ∧ squaredReciprocalPotential f k ξ z < c)) ∧
      (∀ z, F z = c → z ∈ H ∧ squaredReciprocalPotential f k ξ z = c) ∧
      (∀ z, F z = c → fderiv ℝ F z ≠ 0) ∧
      IsCompact {z | F z = c} := by
{
  let u := squaredReciprocalPotential f k ξ
  let d := c + 1
  have hcd : c < d := by dsimp [d]; linarith
  have hP := compact_squaredReciprocal_sublevel hk.le hg (hc.trans hcd)
  obtain ⟨K, hK, hKcv, hPK, hKH⟩ := compact_convex_H_envelope hP (fun _ h => h.1)
  obtain ⟨F, hFc, hFs, hFeq, hFout, hFle, hFlt⟩ := extend_compact_sublevel isOpen_H
    (fun z hz => contDiffAt_squaredReciprocalPotential hf hz k ξ) hP
  have hlevel (z) (hz : F z = c) : z ∈ H ∧ u z = c := by
  {
    have hh := (hFle z c hcd).mp hz.le
    exact ⟨hh.1, ((hFeq z hh.1 (hh.2.trans hcd.le)).self_of_nhds).symm.trans hz⟩
  }
  have hFreg (z) (hz : F z = c) : fderiv ℝ F z ≠ 0 := by
  {
    obtain ⟨hzH, huz⟩ := hlevel z hz
    rw [(hFeq z hzH (huz.le.trans hcd.le)).fderiv_eq]
    exact fun hh => hreg z hzH huz ((fderiv_squaredReciprocalPotential_eq_zero_iff
      hf (ne_of_gt hk) hzH).mp hh)
  }
  have hL : IsCompact {z | F z = c} := hP.of_isClosed_subset
    (isClosed_eq hFc.continuous continuous_const)
    (fun z hz => ⟨(hlevel z hz).1, (hlevel z hz).2.le.trans hcd.le⟩)
  exact ⟨K, F, hK, hKcv, hKH, hPK, hFc, hFs, hFeq, hFout 0 (by simp [H]),
    fun z => hFlt z c hcd, hlevel, hFreg, hL⟩
}

lemma regularizedGradient_cutoff {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} (hk : 0 < k) {ξ : ℂ} (hg : GoodPair f k ξ)
    {K : Set ℂ} (hK : IsCompact K) (hKH : K ⊆ H) :
    ∃ (s : Finset ℂ) (X : C(ℂ, ℂ)),
      (∀ z, z ∈ s ↔ z ∈ K ∧ regularizedGradient f k ξ z = 0) ∧
      (∀ z ∈ K, (X : ℂ → ℂ) =ᶠ[𝓝 z] regularizedGradient f k ξ) ∧
      (∀ z ∈ K, X z = 0 ↔ z ∈ s) ∧
      (∀ z ∈ s, HasFDerivAt X (fderiv ℝ (regularizedGradient f k ξ) z) z ∧
        LinearMap.det (fderiv ℝ (regularizedGradient f k ξ) z).toLinearMap ≠ 0) := by
{
  let x := regularizedGradient f k ξ
  obtain ⟨X, hXeq⟩ := continuous_extension_near_compact hK isOpen_H hKH
    (fun z hz => (differentiableAt_regularizedGradient hf hz k ξ).continuousAt)
  have hfinite : {z | z ∈ K ∧ x z = 0}.Finite := finite_regular_zeros_on_compact hK
    (fun z hz => (differentiableAt_regularizedGradient hf (hKH hz) k ξ).continuousAt.continuousWithinAt)
    (fun z hz hzero => ⟨differentiableAt_regularizedGradient hf (hKH hz) k ξ,
      det_regularizedGradient_ne_zero hf (ne_of_gt hk) hg (hKH hz) hzero⟩)
  let s := hfinite.toFinset
  have hs (z) : z ∈ s ↔ z ∈ K ∧ x z = 0 := hfinite.mem_toFinset
  refine ⟨s, X, hs, hXeq, fun z hz => ?_, fun z hz => ?_⟩
  · rw [(hXeq z hz).self_of_nhds, hs]
    exact ⟨fun h => ⟨hz, h⟩, fun h => h.2⟩
  · have hsK : z ∈ K := ((hs z).mp hz).1
    exact ⟨(differentiableAt_regularizedGradient hf (hKH hsK) k ξ).hasFDerivAt.congr_of_eventuallyEq
      (hXeq z hsK), det_regularizedGradient_ne_zero hf (ne_of_gt hk) hg (hKH hsK) ((hs z).mp hz).2⟩
}

lemma regular_potential_level_index_sum {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} (hk : 0 < k) {ξ : ℂ} (hg : GoodPair f k ξ) {c : ℝ} (hc : 0 < c)
    (hreg : ∀ z ∈ H, squaredReciprocalPotential f k ξ z = c → regularizedGradient f k ξ z ≠ 0) :
    ∃ (s : Finset ℂ) (N : ℕ), (∀ z ∈ s, z ∈ H ∧ regularizedGradient f k ξ z = 0) ∧
      (∀ z ∈ H, squaredReciprocalPotential f k ξ z < c → (z ∈ s ↔ regularizedGradient f k ξ z = 0)) ∧
      (∑ z ∈ s, if squaredReciprocalPotential f k ξ z < c then
        planeIndex (fderiv ℝ (regularizedGradient f k ξ) z) else 0) = (N : ℤ) ∧
      ((∃ z ∈ H, f z = ξ) → 1 ≤ N) := by
{
  let u := squaredReciprocalPotential f k ξ
  have hcd : c < c + 1 := by linarith
  obtain ⟨K, F, hK, hKcv, hKH, hPK, hFc, hFs, hFeq, hFzero, hFlt, hlevel, hFreg, hL⟩ :=
    extend_potential_sublevel hf hk hg hc hreg
  obtain ⟨C, hC, hdis, hcurves⟩ := compact_regular_level_oriented_curves hFc hFs hFreg hL
  let ι := {S : Set ℂ // S ∈ C}
  choose γ hγrange hγc hγp hγi hγd hγm hγr hγdown using (fun S : ι => hcurves S.1 S.2)
  have hγlevel (i : ι) (t : ℝ) : F (γ i t) = c := by
    have hh : γ i t ∈ ⋃ S ∈ C, S := mem_iUnion₂.mpr ⟨i.1, i.2, hγrange i ▸ mem_range_self t⟩; rwa [hC] at hh
  have hcover (z) : F z = c ↔ ∃ i : ι, z ∈ range (γ i) :=
    ⟨fun hz => by obtain ⟨S, hS, hzS⟩ := mem_iUnion₂.mp (hC.symm ▸ (show z ∈ {z | F z = c} from hz)); exact ⟨⟨S, hS⟩, (hγrange ⟨S, hS⟩).symm ▸ hzS⟩,
      by rintro ⟨i, t, rfl⟩; exact hγlevel i t⟩
  have hbelow (i : ι) (w : ℂ) (hw : w ∉ range (γ i)) (hind : loopIndex (periodicLoop (hγc i).continuous 0) w ≠ 0) : F w < c :=
    (hFlt w).mpr (squaredReciprocalPotential_lt_windingInterior hf hk hc ξ (periodicLoop (hγc i).continuous 0)
      (periodicLoop_closed _ (hγp i) 0) (fun t => (hlevel _ (hγlevel i ((t : ℝ) + 0))).1)
      (fun t => (hlevel _ (hγlevel i ((t : ℝ) + 0))).2) ⟨by rwa [periodicLoop_range _ (hγp i) 0], hind⟩)
  obtain ⟨s, X, hs, hXeq, hXzero, hD⟩ := regularizedGradient_cutoff hf hk hg hK hKH
  have hγK (i : ι) (t : ℝ) : γ i t ∈ K := hPK ⟨(hlevel _ (hγlevel i t)).1, (hlevel _ (hγlevel i t)).2.le.trans hcd.le⟩
  have horth (i : ι) (t : ℝ) : (X (γ i t) * conj (deriv (γ i) t)).re = 0 := by
    have he0 : fderiv ℝ F (γ i t) (deriv (γ i) t) = 0 :=
      ((((hFc.differentiable (by norm_num)) _).hasFDerivAt.comp_hasDerivAt t (((hγc i).differentiable (by norm_num)) t).hasDerivAt).congr_of_eventuallyEq
        (Filter.Eventually.of_forall (fun q => (hγlevel i q).symm))).unique (hasDerivAt_const t c)
    rw [(hFeq _ (hlevel _ (hγlevel i t)).1 ((hlevel _ (hγlevel i t)).2.le.trans hcd.le)).fderiv_eq,
      fderiv_squaredReciprocalPotential_apply hf (ne_of_gt hk) (hlevel _ (hγlevel i t)).1, ← (hXeq _ (hγK i t)).self_of_nhds] at he0
    exact (mul_eq_zero.mp he0).resolve_left (mul_ne_zero (by norm_num) (ne_of_gt (Real.rpow_pos_of_pos (hlevel _ (hγlevel i t)).1 (-2 * k))))
  have hsum := regular_level_index_sum hFc.continuous γ hγc hγp hγi hγd hγm hγr hγdown hγlevel
    (fun z hz => ⟨hFc.contDiffAt.of_le (by norm_num), hFreg z hz⟩) hcover
    (fun i j hij => by rw [hγrange, hγrange]; exact hdis i.1 i.2 j.1 j.2 (Subtype.val_injective.ne hij))
    hbelow ⟨0, hFzero ▸ hcd⟩ hKcv hγK s X (fderiv ℝ (regularizedGradient f k ξ)) (fun z hz => ((hs z).mp hz).1) hXzero hD
    (fun i t => by rw [(hXeq _ (hγK i t)).self_of_nhds]; exact hreg _ (hlevel _ (hγlevel i t)).1 (hlevel _ (hγlevel i t)).2) horth
  refine ⟨s, Fintype.card ι, fun z hz => ⟨hKH ((hs z).mp hz).1, ((hs z).mp hz).2⟩,
    fun z hzH hzu => (hs z).trans ⟨fun h => h.2, fun hx => ⟨hPK ⟨hzH, hzu.le.trans hcd.le⟩, hx⟩⟩, ?_, ?_⟩
  · refine Eq.trans (Finset.sum_congr rfl (fun z hz => ?_)) hsum
    simp only [show (F z < c) ↔ u z < c from (hFlt z).trans (and_iff_right (hKH ((hs z).mp hz).1)), u]
  · rintro ⟨z, hzH, hpole⟩
    have huz : u z = 0 := by simp [u, squaredReciprocalPotential, hpole]
    have hFz : F z = 0 := (hFeq z hzH (huz.le.trans (hc.trans hcd).le)).self_of_nhds.trans huz
    obtain ⟨w, hw⟩ := intermediate_value_univ z 0 hFc.continuous (show c ∈ Icc (F z) (F 0) by rw [hFz, hFzero]; exact ⟨hc.le, hcd.le⟩)
    obtain ⟨i, _⟩ := (hcover w).mp hw
    exact Nat.succ_le_iff.mpr (Fintype.card_pos_iff.mpr ⟨i⟩)
}

lemma planeIndex_regularizedGradient_at_critical {f : ℂ → ℂ}
    (hf : UnivalentOn f H) {k : ℝ} (hk : k ≠ 0)
    {ξ z : ℂ} (hz : z ∈ H) (hcrit : criticalMap f k z = ξ) :
    planeIndex (fderiv ℝ (regularizedGradient f k ξ) z) =
      if normalizedJacobian f k z < 0 then 1 else -1 := by
{
  have hp : 0 < ‖((k : ℂ) * Complex.I / (z.im : ℂ)) * (f z - ξ)‖^2 * ‖deriv f z‖^2 := by
  {
    refine mul_pos (sq_pos_of_pos (norm_pos_iff.mpr ?_))
      (sq_pos_of_pos (norm_pos_iff.mpr (deriv_ne_zero_of_univalentOn isOpen_H hf hz)))
    exact mul_ne_zero (div_ne_zero (mul_ne_zero (Complex.ofReal_ne_zero.mpr hk)
      Complex.I_ne_zero) (Complex.ofReal_ne_zero.mpr (ne_of_gt hz)))
      (sub_ne_zero.mpr (criticalMap_ne_pole hf hk hz hcrit))
  }
  rw [planeIndex, det_regularizedGradient_at_critical hf hz hcrit]
  congr 1
  apply propext
  rw [neg_mul, neg_mul, neg_pos]
  exact ⟨fun h => by by_contra hn; exact (not_lt_of_ge (mul_nonneg hp.le (le_of_not_gt hn))) h,
    mul_neg_of_pos_of_neg hp⟩
}

lemma regularizedGradient_index_term {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} (hk : 0 < k) {ξ : ℂ} (hg : GoodPair f k ξ) {c : ℝ} {z : ℂ}
    (hzH : z ∈ H) (hz0 : regularizedGradient f k ξ z = 0) :
    let u := squaredReciprocalPotential f k ξ
    (if u z < c then planeIndex (fderiv ℝ (regularizedGradient f k ξ) z) else 0) =
      (if u z < c ∧ f z = ξ then (1 : ℤ) else 0) +
      (if u z < c ∧ criticalMap f k z = ξ ∧ normalizedJacobian f k z < 0 then 1 else 0) -
      (if u z < c ∧ criticalMap f k z = ξ ∧ 0 < normalizedJacobian f k z then 1 else 0) := by
{
  dsimp only
  by_cases hu : squaredReciprocalPotential f k ξ z < c
  · simp only [hu, true_and, ↓reduceIte]
    rcases (regularizedGradient_eq_zero_iff (ne_of_gt hk) hzH).mp hz0 with hpz | hG
    · have hGn : criticalMap f k z ≠ ξ := fun h => criticalMap_ne_pole hf (ne_of_gt hk) hzH h hpz
      simp [hpz, hGn, planeIndex, det_regularizedGradient_at_pole_pos hf (ne_of_gt hk) hzH hpz]
    · have hpn := criticalMap_ne_pole hf (ne_of_gt hk) hzH hG
      rw [planeIndex_regularizedGradient_at_critical hf (ne_of_gt hk) hzH hG]
      rcases lt_or_gt_of_ne (hg.2 z hzH hG) with hJ | hJ <;>
        simp [hpn, hG, hJ, not_lt_of_ge hJ.le]
  · simp [hu]
}

lemma critical_count_strict_sublevel {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} (hk : 0 < k) {ξ : ℂ} (hg : GoodPair f k ξ) {c : ℝ} (hc : 0 < c)
    (hreg : ∀ z ∈ H, squaredReciprocalPotential f k ξ z = c → regularizedGradient f k ξ z ≠ 0) :
    let critical := {z | z ∈ H ∧ criticalMap f k z = ξ ∧ squaredReciprocalPotential f k ξ z < c}
    critical.Finite ∧ ({z ∈ critical | 0 < normalizedJacobian f k z}).ncard ≤
      ({z ∈ critical | normalizedJacobian f k z < 0}).ncard := by
{
  dsimp only
  obtain ⟨s, N, hs, hsall, hsum, hpole⟩ := regular_potential_level_index_sum hf hk hg hc hreg
  let u := squaredReciprocalPotential f k ξ
  let p := s.filter (fun z => u z < c ∧ f z = ξ)
  let m := s.filter (fun z => u z < c ∧ criticalMap f k z = ξ ∧ normalizedJacobian f k z < 0)
  let a := s.filter (fun z => u z < c ∧ criticalMap f k z = ξ ∧ 0 < normalizedJacobian f k z)
  have hcritmem (z) (hz : z ∈ H) (hG : criticalMap f k z = ξ) (hu : u z < c) : z ∈ s :=
    (hsall z hz hu).mpr ((regularizedGradient_eq_zero_iff (ne_of_gt hk) hz).mpr (Or.inr hG))
  have hfinite : {z | z ∈ H ∧ criticalMap f k z = ξ ∧ u z < c}.Finite :=
    s.finite_toSet.subset (fun z hz => hcritmem z hz.1 hz.2.1 hz.2.2)
  have hmset : {z | (z ∈ H ∧ criticalMap f k z = ξ ∧ u z < c) ∧ normalizedJacobian f k z < 0} = (m : Set ℂ) := by
    ext z; simp only [m, Finset.mem_coe, Finset.mem_filter, mem_setOf_eq]
    exact ⟨fun ⟨⟨hz, hG, hu⟩, hJ⟩ => ⟨hcritmem z hz hG hu, hu, hG, hJ⟩, fun ⟨hz, hu, hG, hJ⟩ => ⟨⟨(hs z hz).1, hG, hu⟩, hJ⟩⟩
  have haset : {z | (z ∈ H ∧ criticalMap f k z = ξ ∧ u z < c) ∧ 0 < normalizedJacobian f k z} = (a : Set ℂ) := by
    ext z; simp only [a, Finset.mem_coe, Finset.mem_filter, mem_setOf_eq]
    exact ⟨fun ⟨⟨hz, hG, hu⟩, hJ⟩ => ⟨hcritmem z hz hG hu, hu, hG, hJ⟩, fun ⟨hz, hu, hG, hJ⟩ => ⟨⟨(hs z hz).1, hG, hu⟩, hJ⟩⟩
  have hpcard : p.card ≤ 1 := Finset.card_le_one.mpr (fun z hz w hw =>
    hf.2 (hs z (Finset.mem_filter.mp hz).1).1 (hs w (Finset.mem_filter.mp hw).1).1
      ((Finset.mem_filter.mp hz).2.2.trans (Finset.mem_filter.mp hw).2.2.symm))
  have hpN : p.card ≤ N := by
    by_cases hpe : p = ∅
    · simp [hpe]
    · obtain ⟨z, hz⟩ := Finset.nonempty_iff_ne_empty.mpr hpe
      exact hpcard.trans (hpole ⟨z, (hs z (Finset.mem_filter.mp hz).1).1, (Finset.mem_filter.mp hz).2.2⟩)
  have heuler : (p.card : ℤ) + m.card - a.card = N := by
    rw [← hsum]
    refine Eq.trans ?_ (Finset.sum_congr rfl (fun z hz => (regularizedGradient_index_term hf hk hg (c := c) (hs z hz).1 (hs z hz).2).symm))
    simp only [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_boole, p, m, a, u]
  refine ⟨hfinite, ?_⟩
  change ({z | (z ∈ H ∧ criticalMap f k z = ξ ∧ u z < c) ∧ 0 < normalizedJacobian f k z}).ncard ≤
    ({z | (z ∈ H ∧ criticalMap f k z = ξ ∧ u z < c) ∧ normalizedJacobian f k z < 0}).ncard
  rw [haset, hmset, Set.ncard_coe_finset, Set.ncard_coe_finset]
  have hpN_int : (p.card : ℤ) ≤ N := by exact_mod_cast hpN
  exact_mod_cast (by linarith : (a.card : ℤ) ≤ m.card)
}

lemma finite_critical_squared_sublevel {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} (hk : 0 ≤ k) {ξ : ℂ} (hg : GoodPair f k ξ) {d : ℝ} (hd : 0 < d) :
    {z | z ∈ H ∧ criticalMap f k z = ξ ∧
      squaredReciprocalPotential f k ξ z ≤ d}.Finite := by
{
  have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hd
  apply (finite_critical_superlevel hf hg (h := (Real.sqrt d)⁻¹) (inv_pos.mpr hs)).subset
  intro z hz
  refine ⟨hz.1, hz.2.1, (potential_ge_iff_reciprocalPotential_le hk (inv_pos.mpr hs) hz.1).mpr ?_⟩
  rw [inv_inv]
  have hh := hz.2.2
  rw [squaredReciprocalPotential_eq_sq hz.1] at hh
  nlinarith [Real.sq_sqrt hd.le]
}

lemma potential_ge_iff_squaredReciprocal_le {f : ℂ → ℂ} {k h : ℝ}
    (hk : 0 ≤ k) (hh : 0 < h) {ξ z : ℂ} (hz : z ∈ H) :
    ENNReal.ofReal h ≤ potential f k ξ z ↔
      squaredReciprocalPotential f k ξ z ≤ (h⁻¹)^2 := by
{
  rw [potential_ge_iff_reciprocalPotential_le hk hh hz, squaredReciprocalPotential_eq_sq hz]
  exact (sq_le_sq₀ (div_nonneg (norm_nonneg _) (Real.rpow_nonneg hz.le _))
    (inv_nonneg.mpr hh.le)).symm
}

lemma finset_gap_above (s : Finset ℝ) (r d : ℝ) (hrd : r < d) :
    ∃ c, r < c ∧ c < d ∧ ∀ a ∈ s, r < a → c < a := by
{
  induction s using Finset.induction_on generalizing d with
  | empty =>
      obtain ⟨c, hrc, hcd⟩ := exists_between hrd
      exact ⟨c, hrc, hcd, by simp⟩
  | @insert a s ha ih =>
      by_cases hra : r < a
      · obtain ⟨c, hrc, hcd, hcs⟩ := ih (min d a) (lt_min hrd hra)
        refine ⟨c, hrc, hcd.trans_le (min_le_left _ _), fun b hb hrb => ?_⟩
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact hcd.trans_le (min_le_right _ _)
        · exact hcs b hb hrb
      · obtain ⟨c, hrc, hcd, hcs⟩ := ih d hrd
        refine ⟨c, hrc, hcd, fun b hb hrb => ?_⟩
        rcases Finset.mem_insert.mp hb with rfl | hb
        · exact (hra hrb).elim
        · exact hcs b hb hrb
}

theorem critical_count {f : ℂ → ℂ} (hf : UnivalentOn f H)
    {k : ℝ} (hk : 0 < k) {ξ : ℂ} (hg : GoodPair f k ξ) {h : ℝ} (hh : 0 < h) :
    let critical := {z | z ∈ H ∧ criticalMap f k z = ξ ∧
      ENNReal.ofReal h ≤ potential f k ξ z}
    critical.Finite ∧ ({z ∈ critical | 0 < normalizedJacobian f k z}).ncard ≤
      ({z ∈ critical | normalizedJacobian f k z < 0}).ncard := by
{
  let u := squaredReciprocalPotential f k ξ
  let r := (h⁻¹)^2
  have hr : 0 < r := sq_pos_of_pos (inv_pos.mpr hh)
  have hd : 0 < r + 1 := by linarith
  have hfinite := finite_critical_squared_sublevel hf hk.le hg hd
  let s := hfinite.toFinset.image u
  obtain ⟨c, hrc, hcd, hcs⟩ := finset_gap_above s r (r + 1) (by linarith)
  have hcmem (z) (hz : z ∈ H) (hG : criticalMap f k z = ξ)
      (hu : u z ≤ r + 1) : u z ∈ s :=
    Finset.mem_image.mpr ⟨z, hfinite.mem_toFinset.mpr ⟨hz, hG, hu⟩, rfl⟩
  have hcut (z) (hz : z ∈ H) (hG : criticalMap f k z = ξ) : u z < c ↔ u z ≤ r := by
    refine ⟨fun huc => ?_, fun h => h.trans_lt hrc⟩
    by_contra hn
    exact (hcs (u z) (hcmem z hz hG (huc.trans hcd).le) (lt_of_not_ge hn)).not_gt huc
  have hreg (z) (hz : z ∈ H) (huc : u z = c) : regularizedGradient f k ξ z ≠ 0 := by
  {
    intro hzero
    rcases (regularizedGradient_eq_zero_iff (ne_of_gt hk) hz).mp hzero with hp | hG
    · have huz : u z = 0 := by simp [u, squaredReciprocalPotential, hp]
      linarith
    · have hcc := hcs (u z) (hcmem z hz hG (huc.le.trans hcd.le)) (hrc.trans_eq huc.symm)
      linarith
  }
  have hc := critical_count_strict_sublevel hf hk hg (hr.trans hrc) hreg
  have he : {z | z ∈ H ∧ criticalMap f k z = ξ ∧ ENNReal.ofReal h ≤ potential f k ξ z} =
      {z | z ∈ H ∧ criticalMap f k z = ξ ∧ u z < c} := by
    ext z
    exact ⟨fun ⟨hz, hG, hV⟩ => ⟨hz, hG, (hcut z hz hG).mpr ((potential_ge_iff_squaredReciprocal_le hk.le hh hz).mp hV)⟩,
      fun ⟨hz, hG, hu⟩ => ⟨hz, hG, (potential_ge_iff_squaredReciprocal_le hk.le hh hz).mpr ((hcut z hz hG).mp hu)⟩⟩
  dsimp only
  rw [he]
  exact hc
}

end Brennan.Sections4and5
