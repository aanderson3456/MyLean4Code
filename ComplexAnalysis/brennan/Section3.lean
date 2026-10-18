import Mathlib
import brennan.Section2
import brennan.Section2_Dyadic

open Complex Set MeasureTheory Topology Filter BigOperators
open scoped Classical ComplexConjugate Topology CompactlySupported ENNReal NNReal

noncomputable section

namespace Brennan.Section3

open Brennan.Section2
open Brennan.Section2_Dyadic

/-!
# 3 A probability law from transfer growth

PAPER: Lemma 3.1 (Weighted affine covariance). Suppose that ρ > 2, and put β = \log_2 ρ > 1.
PAPER: There is a Borel probability measure P on K such that, for every z = x + iy ∈ H and every
PAPER: nonnegative Borel function Φ : K → [0, ∞],
PAPER: E[ |QF (z)|^2 Φ(TzF) ] = y^{-β} EΦ(F), (3.1)
PAPER: where E denotes expectation with respect to P.
-/

lemma differentiableOn_iteratedDeriv_open {U : Set ℂ} (hU : IsOpen U)
    {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f U) (n : ℕ) :
    DifferentiableOn ℂ (iteratedDeriv n f) U := by
{
  induction n with
  | zero => simpa using hf
  | succ n ih => simpa only [iteratedDeriv_succ] using ih.deriv hU
}

lemma tendstoLocallyUniformlyOn_iteratedDeriv_open {U : Set ℂ} (hU : IsOpen U)
    {ι : Type*} {l : Filter ι} {f : ι → ℂ → ℂ} {g : ℂ → ℂ}
    (h : TendstoLocallyUniformlyOn f g l U)
    (hf : ∀ᶠ i in l, DifferentiableOn ℂ (f i) U) (n : ℕ) :
    TendstoLocallyUniformlyOn (fun i => iteratedDeriv n (f i)) (iteratedDeriv n g) l U := by
{
  induction n with
  | zero => simpa using h
  | succ n ih =>
    simpa only [iteratedDeriv_succ, Function.comp_def] using ih.deriv
      (hf.mono (fun i h => differentiableOn_iteratedDeriv_open hU h n)) hU
}

def diskClassJet (n : ℕ) (g : DiskClass) : C(disk, ℂ) :=
  ⟨fun z => iteratedDeriv n (diskExtend g.1) z,
    continuousOn_iff_continuous_restrict.mp
      (differentiableOn_iteratedDeriv_open Metric.isOpen_ball g.2.1 n).continuousOn⟩

lemma continuous_diskClassJet (n : ℕ) : Continuous (diskClassJet n) := by
{
  rw [continuous_iff_continuousAt]
  intro g
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  have h := tendstoLocallyUniformlyOn_iteratedDeriv_open Metric.isOpen_ball
    (diskExtend_convergence (continuous_subtype_val.tendsto g))
    (Eventually.of_forall (fun f : DiskClass => f.2.1)) n
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp h
}

lemma continuous_diskClassJet_eval (n : ℕ) :
    Continuous (fun p : DiskClass × disk => iteratedDeriv n (diskExtend p.1.1) p.2) := by
{
  exact continuous_eval.comp ((continuous_diskClassJet n).prodMap continuous_id)
}

def toKClass (g : DiskClass) : KClass := S_to_KClass (diskExtend g.1) g.2

lemma S_to_K_K_to_S (F : KClass) {z : ℂ} (hz : z ∈ H) :
    S_to_K (K_to_S F) z = F.F z := by
{
  dsimp [S_to_K, K_to_S]
  rw [cayley_inv_cayley hz]
  field_simp
}

lemma K_to_S_S_to_K {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {w : ℂ} (hw : w ∈ disk) :
    K_to_S (S_to_KClass f hf) w = f w := by
{
  dsimp [K_to_S, S_to_KClass, S_to_K]
  rw [inv_cayley_cayley hw]
  field_simp
}

lemma toKClass_ofKClass_eqOn (F : KClass) :
    EqOn (toKClass (ofKClass F)).F F.F H := by
{
  intro z hz
  dsimp [toKClass, S_to_KClass, S_to_K, ofKClass]
  rw [diskExtend_apply _ (⟨inv_cayley z, inv_cayley_maps hz⟩ : disk)]
  exact S_to_K_K_to_S F hz
}

lemma diskClass_ext {g h : DiskClass} (he : EqOn (toKClass g).F (toKClass h).F H) : g = h := by
{
  apply Subtype.ext
  apply ContinuousMap.ext
  intro z
  have hx := congrArg (fun q : ℂ => q / (2 * I)) (he (cayley_maps z.2))
  have hg : (toKClass g).F (cayley z) / (2 * I) = g.1 z :=
    (K_to_S_S_to_K g.2 z.2).trans (diskExtend_apply _ z)
  have hh : (toKClass h).F (cayley z) / (2 * I) = h.1 z :=
    (K_to_S_S_to_K h.2 z.2).trans (diskExtend_apply _ z)
  rwa [hg, hh] at hx
}

lemma ofKClass_toKClass (g : DiskClass) : ofKClass (toKClass g) = g := by
{
  exact diskClass_ext (toKClass_ofKClass_eqOn (toKClass g))
}

lemma ofKClass_eq_of_eqOn {F₁ F₂ : KClass} (h : EqOn F₁.F F₂.F H) :
    ofKClass F₁ = ofKClass F₂ := by
{
  apply diskClass_ext
  exact (toKClass_ofKClass_eqOn F₁).trans (h.trans (toKClass_ofKClass_eqOn F₂).symm)
}

lemma continuous_toKClass : Continuous toKClass := by
{
  rw [continuous_induced_rng]
  have heq : ofKClass ∘ toKClass = id := funext ofKClass_toKClass
  rw [heq]
  exact continuous_id
}

lemma continuous_ofKClass : Continuous ofKClass := by
{
  exact continuous_induced_dom
}

lemma continuous_toKClass_eval : Continuous (fun p : DiskClass × H => (toKClass p.1).F p.2) := by
{
  have hm : Continuous (fun z : H => inv_cayley z) := by
  {
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (hasDerivAt_inv_cayley z.2).continuousAt.comp continuous_subtype_val.continuousAt
  }
  have h := (continuous_diskClassJet_eval 0).comp
    (continuous_id.prodMap (hm.subtype_mk (fun z => inv_cayley_maps z.2)))
  simpa only [iteratedDeriv_zero, toKClass, S_to_KClass, S_to_K, Function.comp_def, Prod.map, id_eq]
    using h.const_mul (2 * I)
}

def halfClassJet (n : ℕ) (g : DiskClass) : C(H, ℂ) :=
  ⟨fun z => iteratedDeriv n (toKClass g).F z, continuousOn_iff_continuous_restrict.mp
    (differentiableOn_iteratedDeriv_open isOpen_H (toKClass g).univalent.1 n).continuousOn⟩

lemma continuous_halfClassJet (n : ℕ) : Continuous (halfClassJet n) := by
{
  have hc : Continuous (halfClassJet 0) :=
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_toKClass_eval
  rw [continuous_iff_continuousAt]
  intro g
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  have hv := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hc.tendsto g)
  have h : TendstoLocallyUniformlyOn (fun a : DiskClass => (toKClass a).F)
      (toKClass g).F (𝓝 g) H :=
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr hv
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp
    (tendstoLocallyUniformlyOn_iteratedDeriv_open isOpen_H h
      (Eventually.of_forall (fun f : DiskClass => (toKClass f).univalent.1)) n)
}

lemma continuous_halfClassJet_eval (n : ℕ) :
    Continuous (fun p : DiskClass × H => iteratedDeriv n (toKClass p.1).F p.2) := by
{
  exact continuous_eval.comp ((continuous_halfClassJet n).prodMap continuous_id)
}

lemma differentiableOn_KClass_Q (F : KClass) : DifferentiableOn ℂ (Q F.F) H := by
{
  have h_eq : Q F.F = fun u => (deriv F.F u)⁻¹ := by
  {
    ext u
    simp [Q]
  }
  rw [h_eq]
  exact (F.univalent.1.deriv isOpen_H).inv
    (fun z hz => deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz)
}

lemma continuous_toKClass_Q_eval :
    Continuous (fun p : DiskClass × H => Q (toKClass p.1).F p.2) := by
{
  have hd : Continuous (fun p : DiskClass × H => deriv (toKClass p.1).F p.2) := by
  {
    simpa only [iteratedDeriv_one] using continuous_halfClassJet_eval 1
  }
  have h_eq : (fun p : DiskClass × H => Q (toKClass p.1).F p.2) =
      fun p : DiskClass × H => (deriv (toKClass p.1).F p.2)⁻¹ := by
  {
    ext p
    simp [Q]
  }
  rw [h_eq]
  exact hd.inv₀ (fun p => deriv_ne_zero_of_univalentOn isOpen_H (toKClass p.1).univalent p.2.2)
}

def reciprocalJet (n : ℕ) (g : DiskClass) : C(H, ℂ) :=
  ⟨fun z => iteratedDeriv n (Q (toKClass g).F) z, continuousOn_iff_continuous_restrict.mp
    (differentiableOn_iteratedDeriv_open isOpen_H (differentiableOn_KClass_Q (toKClass g)) n).continuousOn⟩

lemma continuous_reciprocalJet (n : ℕ) : Continuous (reciprocalJet n) := by
{
  have hc : Continuous (reciprocalJet 0) :=
    ContinuousMap.continuous_of_continuous_uncurry _ continuous_toKClass_Q_eval
  rw [continuous_iff_continuousAt]
  intro g
  apply ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mpr
  have hv := ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp (hc.tendsto g)
  have h : TendstoLocallyUniformlyOn (fun a : DiskClass => Q (toKClass a).F)
      (Q (toKClass g).F) (𝓝 g) H :=
    tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mpr hv
  exact tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe.mp
    (tendstoLocallyUniformlyOn_iteratedDeriv_open isOpen_H h
      (Eventually.of_forall (fun a : DiskClass => differentiableOn_KClass_Q (toKClass a))) n)
}

lemma continuous_reciprocalJet_eval (n : ℕ) :
    Continuous (fun p : DiskClass × H => iteratedDeriv n (Q (toKClass p.1).F) p.2) := by
{
  exact continuous_eval.comp ((continuous_reciprocalJet n).prodMap continuous_id)
}

lemma eqOn_iteratedDeriv_of_eqOn {f g : ℂ → ℂ} (h : EqOn f g H) (n : ℕ) :
    EqOn (iteratedDeriv n f) (iteratedDeriv n g) H := by
{
  induction n with
  | zero => simpa using h
  | succ n ih =>
    intro z hz
    rw [iteratedDeriv_succ, iteratedDeriv_succ]
    exact ih.deriv isOpen_H hz
}

lemma continuous_comp₂ {X Y Z W : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [TopologicalSpace Z] [TopologicalSpace W] {F : Y → Z → W} {g : X → Y} {h : X → Z}
    (hF : Continuous (fun p : Y × Z => F p.1 p.2)) (hg : Continuous g) (hh : Continuous h) :
    Continuous (fun x => F (g x) (h x)) := by
{
  exact hF.comp (hg.prodMk hh)
}

lemma continuous_iteratedDeriv_Q_eval (n : ℕ) {w : ℂ} (hw : w ∈ H) :
    Continuous (fun F : KClass => iteratedDeriv n (Q F.F) w) := by
{
  have heq : (fun F : KClass => iteratedDeriv n (Q F.F) w) =
      fun F : KClass => iteratedDeriv n (Q (toKClass (ofKClass F)).F) (⟨w, hw⟩ : H) := by
  {
    ext F
    have hF := toKClass_ofKClass_eqOn F
    have hQ : EqOn (Q F.F) (Q (toKClass (ofKClass F)).F) H := by
    {
      intro z hz
      simp [Q, hF.deriv isOpen_H hz]
    }
    exact eqOn_iteratedDeriv_of_eqOn hQ n hw
  }
  rw [heq]
  exact continuous_comp₂ (F := fun (g : DiskClass) (z : H) => iteratedDeriv n (Q (toKClass g).F) z)
    (continuous_reciprocalJet_eval n) continuous_ofKClass continuous_const
}

def rerootDisk (g : DiskClass) (z : H) : DiskClass :=
  ofKClass (T_elem (toKClass g) z.1 z.2)

lemma toKClass_rerootDisk (g : DiskClass) (z : H) :
    EqOn (toKClass (rerootDisk g z)).F (T z.1 (toKClass g).F) H := by
{
  exact toKClass_ofKClass_eqOn (T_elem (toKClass g) z.1 z.2)
}

lemma continuous_cayley_to_H :
    Continuous (fun p : (DiskClass × H) × disk => (⟨cayley p.2, cayley_maps p.2.2⟩ : H)) := by
{
  apply Continuous.subtype_mk
  have hm : Continuous (fun z : disk => cayley z) := by
  {
    apply continuous_iff_continuousAt.mpr
    intro z
    exact (hasDerivAt_cayley z.2).continuousAt.comp continuous_subtype_val.continuousAt
  }
  exact hm.comp continuous_snd
}

lemma continuous_rerootDisk : Continuous (fun p : DiskClass × H => rerootDisk p.1 p.2) := by
{
  apply Continuous.subtype_mk
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hc := continuous_cayley_to_H
  have ha : Continuous (fun p : (DiskClass × H) × disk =>
      (⟨aff p.1.2.1 (cayley p.2), aff_mem_H p.1.2.2 (cayley_maps p.2.2)⟩ : H)) := by
  {
    apply Continuous.subtype_mk
    have hre : Continuous (fun p : (DiskClass × H) × disk => p.1.2.1.re) :=
      Complex.continuous_re.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    have him : Continuous (fun p : (DiskClass × H) × disk => p.1.2.1.im) :=
      Complex.continuous_im.comp (continuous_subtype_val.comp (continuous_snd.comp continuous_fst))
    exact (Complex.continuous_ofReal.comp hre).add
      ((Complex.continuous_ofReal.comp him).mul (continuous_subtype_val.comp hc))
  }
  have hvalue := continuous_toKClass_eval.comp ((continuous_fst.comp continuous_fst).prodMk ha)
  have hroot : Continuous (fun p : (DiskClass × H) × disk => (toKClass p.1.1).F p.1.2) :=
    continuous_toKClass_eval.comp continuous_fst
  have hder : Continuous (fun p : (DiskClass × H) × disk => deriv (toKClass p.1.1).F p.1.2) := by
  {
    simpa only [iteratedDeriv_one, Function.comp_def] using
      ((continuous_halfClassJet_eval 1).comp
        (continuous_fst : Continuous (Prod.fst : (DiskClass × H) × disk → DiskClass × H)))
  }
  have him : Continuous (fun p : (DiskClass × H) × disk => (p.1.2.1.im : ℂ)) :=
    Complex.continuous_ofReal.comp (Complex.continuous_im.comp
      (continuous_subtype_val.comp (continuous_snd.comp continuous_fst)))
  have hdiv := (hvalue.sub hroot).div (him.mul hder) (fun p => mul_ne_zero
    (Complex.ofReal_ne_zero.mpr (ne_of_gt p.1.2.2))
    (deriv_ne_zero_of_univalentOn isOpen_H (toKClass p.1.1).univalent p.1.2.2))
  exact hdiv.div_const (2 * I)
}

lemma T_congr {f g : ℂ → ℂ} (h : EqOn f g H) {z : ℂ} (hz : z ∈ H) :
    EqOn (T z f) (T z g) H := by
{
  intro w hw
  dsimp [T]
  rw [h (aff_mem_H hz hw), h hz, h.deriv isOpen_H hz]
}

lemma A_weight_congr {f g : ℂ → ℂ} (h : EqOn f g H) {z : ℂ} (hz : z ∈ H) :
    A_weight z f = A_weight z g := by
{
  dsimp [A_weight, Q]
  rw [h.deriv isOpen_H hz]
}

lemma rerootDisk_comp (g : DiskClass) (z w : H) :
    rerootDisk (rerootDisk g z) w = rerootDisk g ⟨aff z.1 w.1, aff_mem_H z.2 w.2⟩ := by
{
  apply diskClass_ext
  intro u hu
  rw [toKClass_rerootDisk _ _ hu, T_congr (toKClass_rerootDisk g z) w.2 hu,
    lemma_2_3_KClass (toKClass g) z.1 w.1 z.2 w.2, toKClass_rerootDisk _ _ hu]
}

def diskWeight (g : DiskClass) (z : H) : ℝ := A_weight z.1 (toKClass g).F

lemma diskWeight_pos (g : DiskClass) (z : H) : 0 < diskWeight g z := by
{
  dsimp [diskWeight, A_weight, Q]
  apply sq_pos_of_ne_zero
  exact norm_ne_zero_iff.mpr (one_div_ne_zero
    (deriv_ne_zero_of_univalentOn isOpen_H (toKClass g).univalent z.2))
}

lemma continuous_diskWeight : Continuous (fun p : DiskClass × H => diskWeight p.1 p.2) := by
{
  have hQ : Continuous (fun p : DiskClass × H => Q (toKClass p.1).F p.2) :=
    continuous_toKClass_Q_eval
  exact hQ.norm.pow 2
}

lemma diskWeight_cocycle (g : DiskClass) (z w : H) :
    diskWeight g z * diskWeight (rerootDisk g z) w =
      diskWeight g ⟨aff z.1 w.1, aff_mem_H z.2 w.2⟩ := by
{
  dsimp [diskWeight]
  rw [A_weight_congr (toKClass_rerootDisk g z) w.2]
  exact A_weight_cocycle (toKClass g) z.1 w.1 z.2 w.2
}

def halfMul (z w : H) : H := ⟨aff z.1 w.1, aff_mem_H z.2 w.2⟩

def halfPoint (x y : ℝ) (hy : 0 < y) : H :=
  ⟨(x : ℂ) + (y : ℂ) * I, by dsimp [H]; simp [hy]⟩

def halfOne : H := ⟨I, by dsimp [H]; simp⟩

def horizontal (x : ℝ) : H := halfPoint x 1 zero_lt_one

lemma halfPoint_mul (x y u v : ℝ) (hy : 0 < y) (hv : 0 < v) :
    halfMul (halfPoint x y hy) (halfPoint u v hv) = halfPoint (x + y * u) (y * v) (mul_pos hy hv) := by
{
  apply Subtype.ext
  apply Complex.ext <;> simp [halfMul, halfPoint, aff]
}

lemma continuous_halfPoint {Y : Type*} [TopologicalSpace Y] {x y : Y → ℝ}
    (hx : Continuous x) (hy : Continuous y) (hp : ∀ a, 0 < y a) :
    Continuous (fun a => halfPoint (x a) (y a) (hp a)) := by
{
  exact ((Complex.continuous_ofReal.comp hx).add
    ((Complex.continuous_ofReal.comp hy).mul continuous_const)).subtype_mk _
}

lemma rerootDisk_one (g : DiskClass) : rerootDisk g halfOne = g := by
{
  apply diskClass_ext
  intro z hz
  rw [toKClass_rerootDisk _ _ hz]
  dsimp [T, halfOne, aff]
  simp [(toKClass g).norm_zero, (toKClass g).norm_deriv]
}

lemma diskWeight_one (g : DiskClass) : diskWeight g halfOne = 1 := by
{
  dsimp [diskWeight, halfOne, A_weight, Q]
  simp [(toKClass g).norm_deriv]
}

def idDiskClass : DiskClass := ofKClass idKClass

instance : Nonempty DiskClass := ⟨idDiskClass⟩

def weightAt (z : H) : C(DiskClass, ℝ) :=
  ⟨fun g => diskWeight g z, continuous_comp₂ continuous_diskWeight continuous_id continuous_const⟩

def actionAt (z : H) : C(DiskClass, DiskClass) :=
  ⟨fun g => rerootDisk g z, continuous_comp₂ continuous_rerootDisk continuous_id continuous_const⟩

def affineOperator (z : H) : C(DiskClass, ℝ) →L[ℝ] C(DiskClass, ℝ) :=
  (ContinuousLinearMap.mul ℝ C(DiskClass, ℝ) (weightAt z)).comp
    (ContinuousMap.compCLM ℝ ℝ (actionAt z))

lemma affineOperator_apply (z : H) (f : C(DiskClass, ℝ)) (g : DiskClass) :
    affineOperator z f g = diskWeight g z * f (rerootDisk g z) := by
{
  rfl
}

lemma affineOperator_pos (z : H) (f : C(DiskClass, ℝ)) (hf : 0 ≤ f) :
    0 ≤ affineOperator z f := by
{
  intro g
  exact mul_nonneg (diskWeight_pos g z).le (hf _)
}

lemma affineOperator_mul (z w : H) :
    affineOperator z * affineOperator w = affineOperator (halfMul z w) := by
{
  ext f g
  change diskWeight g z * (diskWeight (rerootDisk g z) w * f (rerootDisk (rerootDisk g z) w)) = _
  rw [← mul_assoc, diskWeight_cocycle, rerootDisk_comp]
  rfl
}

lemma affineOperator_one : affineOperator halfOne = 1 := by
{
  ext f g
  simp only [affineOperator_apply, diskWeight_one, rerootDisk_one, one_mul]
  rfl
}

lemma continuous_affineOperator_apply (f : C(DiskClass, ℝ)) :
    Continuous (fun z : H => affineOperator z f) := by
{
  apply ContinuousMap.continuous_of_continuous_uncurry
  have hw : Continuous (fun p : H × DiskClass => diskWeight p.2 p.1) :=
    continuous_comp₂ continuous_diskWeight continuous_snd continuous_fst
  have ht : Continuous (fun p : H × DiskClass => rerootDisk p.2 p.1) :=
    continuous_comp₂ continuous_rerootDisk continuous_snd continuous_fst
  exact hw.mul (f.continuous.comp ht)
}

lemma affineOperator_norm_le {z : H} {B : ℝ} (hB : 0 ≤ B)
    (hw : ∀ g : DiskClass, diskWeight g z ≤ B) : ‖affineOperator z‖ ≤ B := by
{
  apply (affineOperator z).opNorm_le_bound hB
  intro f
  apply (ContinuousMap.norm_le _ (mul_nonneg hB (norm_nonneg f))).mpr
  intro g
  rw [affineOperator_apply, norm_mul, Real.norm_of_nonneg (diskWeight_pos g z).le]
  exact mul_le_mul (hw g) (ContinuousMap.norm_coe_le_norm f _) (norm_nonneg _) hB
}

def dyadicLeft : H := halfPoint (-1/2) (1/2) (by norm_num)

def dyadicRight : H := halfPoint (1/2) (1/2) (by norm_num)

def transferOperator : C(DiskClass, ℝ) →L[ℝ] C(DiskClass, ℝ) :=
  (1 / 2 : ℝ) • (affineOperator dyadicLeft + affineOperator dyadicRight)

lemma transferOperator_pos (f : C(DiskClass, ℝ)) (hf : 0 ≤ f) : 0 ≤ transferOperator f := by
{
  intro g
  change 0 ≤ (1 / 2 : ℝ) * (affineOperator dyadicLeft f g + affineOperator dyadicRight f g)
  exact mul_nonneg (by norm_num) (add_nonneg (affineOperator_pos _ f hf g) (affineOperator_pos _ f hf g))
}

lemma positive_operator_mono {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f) : Monotone L := by
{
  intro f g h
  have := hp (g - f) (sub_nonneg.mpr h)
  simpa only [map_sub, sub_nonneg] using this
}

lemma positive_operator_abs_bound {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f) (f : C(X, ℝ)) (x : X) :
    |L f x| ≤ ‖f‖ * L 1 x := by
{
  have hlo : (-‖f‖) • (1 : C(X, ℝ)) ≤ f := by
  {
    intro y
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f y)).1
  }
  have hhi : f ≤ ‖f‖ • (1 : C(X, ℝ)) := by
  {
    intro y
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f y)).2
  }
  have h1 := positive_operator_mono L hp hlo x
  have h2 := positive_operator_mono L hp hhi x
  simp only [map_smul, ContinuousMap.toFun_eq_coe, ContinuousMap.smul_apply, smul_eq_mul, neg_mul] at h1 h2
  exact abs_le.mpr ⟨h1, h2⟩
}

lemma positive_operator_norm {X : Type*} [TopologicalSpace X] [CompactSpace X] [Nonempty X]
    (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f) : ‖L‖ = ‖L 1‖ := by
{
  apply le_antisymm
  · apply L.opNorm_le_bound (norm_nonneg _)
    intro f
    apply (ContinuousMap.norm_le (L f) (by positivity)).mpr
    intro x
    calc
      ‖L f x‖ = |L f x| := Real.norm_eq_abs _
      _ ≤ ‖f‖ * L 1 x := positive_operator_abs_bound L hp f x
      _ ≤ ‖f‖ * ‖L 1‖ := mul_le_mul_of_nonneg_left
        (le_trans (le_abs_self _) (ContinuousMap.norm_coe_le_norm (L 1) x)) (norm_nonneg _)
      _ = ‖L 1‖ * ‖f‖ := mul_comm _ _
  · simpa using L.le_opNorm (1 : C(X, ℝ))
}

lemma positive_operator_pow {X : Type*} [TopologicalSpace X] [CompactSpace X]
    (L : C(X, ℝ) →L[ℝ] C(X, ℝ)) (hp : ∀ f, 0 ≤ f → 0 ≤ L f) (n : ℕ) :
    ∀ f, 0 ≤ f → 0 ≤ (L ^ n) f := by
{
  induction n with
  | zero => simp
  | succ n ih =>
    intro f hf
    simpa only [pow_succ', ContinuousLinearMap.mul_apply] using hp ((L ^ n) f) (ih f hf)
}

lemma L_one_congr (n : ℕ) {F₁ F₂ : KClass} (h : EqOn F₁.F F₂.F H) :
    L_one n F₁ = L_one n F₂ := by
{
  dsimp [L_one, L_pow_real]
  congr 1
  apply Finset.sum_congr rfl
  intro j _
  rw [A_weight_congr h (dyadic_cell_H n j)]
}

lemma dyadicLeft_val : dyadicLeft.1 = -1/2 + I/2 := by
{
  dsimp [dyadicLeft, halfPoint]
  push_cast
  ring
}

lemma dyadicRight_val : dyadicRight.1 = 1/2 + I/2 := by
{
  dsimp [dyadicRight, halfPoint]
  push_cast
  ring
}

lemma transferOperator_pow_one_apply (n : ℕ) (g : DiskClass) :
    (transferOperator ^ n) 1 g = L_one n (toKClass g) := by
{
  induction n generalizing g with
  | zero =>
    rw [L_one, L_pow_real_zero]
    rfl
  | succ n ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply]
    change (1 / 2 : ℝ) * (diskWeight g dyadicLeft * (transferOperator ^ n) 1 (rerootDisk g dyadicLeft) +
      diskWeight g dyadicRight * (transferOperator ^ n) 1 (rerootDisk g dyadicRight)) = _
    rw [L_one, L_pow_real_succ, ih, ih]
    have hl : EqOn (toKClass (rerootDisk g dyadicLeft)).F
        (T_elem (toKClass g) (-1/2 + I/2) L_op_left_H).F H := by
    {
      simpa only [T_elem, dyadicLeft_val] using toKClass_rerootDisk g dyadicLeft
    }
    have hr : EqOn (toKClass (rerootDisk g dyadicRight)).F
        (T_elem (toKClass g) (1/2 + I/2) L_op_right_H).F H := by
    {
      simpa only [T_elem, dyadicRight_val] using toKClass_rerootDisk g dyadicRight
    }
    rw [L_one_congr n hl, L_one_congr n hr]
    dsimp [diskWeight]
    rw [dyadicLeft_val, dyadicRight_val]
    rfl
}

lemma norm_transferOperator_pow_one (n : ℕ) :
    ‖(transferOperator ^ n) 1‖ = L_norm n := by
{
  apply le_antisymm
  · apply (ContinuousMap.norm_le _ (L_norm_pos n).le).mpr
    intro g
    have hn : 0 ≤ (transferOperator ^ n) 1 g :=
      positive_operator_pow transferOperator transferOperator_pos n 1 (fun _ => zero_le_one) g
    rw [Real.norm_of_nonneg hn, transferOperator_pow_one_apply]
    exact le_L_norm n (toKClass g)
  · haveI : Nonempty KClass := ⟨idKClass⟩
    apply ciSup_le
    intro F
    rw [← L_one_congr n (toKClass_ofKClass_eqOn F), ← transferOperator_pow_one_apply]
    exact (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm ((transferOperator ^ n) 1) (ofKClass F))
}

lemma norm_transferOperator_pow (n : ℕ) :
    ‖transferOperator ^ n‖ = L_norm n := by
{
  rw [positive_operator_norm (transferOperator ^ n)
    (positive_operator_pow transferOperator transferOperator_pos n),
    norm_transferOperator_pow_one]
}

lemma summable_scaled_pow {A : Type*} [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (a : A) {r τ : ℝ} (hr0 : 0 < r) (hrτ : r < τ)
    (he : ∀ᶠ n : ℕ in atTop, ‖a ^ n‖ ≤ r ^ n) :
    Summable (fun n : ℕ => (τ⁻¹) ^ n • a ^ n) := by
{
  have hτ0 : 0 < τ := hr0.trans hrτ
  apply Summable.of_norm_bounded_eventually_nat
    (summable_geometric_of_lt_one (by positivity) ((div_lt_one hτ0).mpr hrτ))
  filter_upwards [he] with n hn
  rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ (τ⁻¹) ^ n)]
  calc
    (τ⁻¹) ^ n * ‖a ^ n‖ ≤ (τ⁻¹) ^ n * r ^ n := mul_le_mul_of_nonneg_left hn (by positivity)
    _ = (r / τ) ^ n := by rw [← mul_pow]; congr 1; ring
}

lemma summable_scaled_transferOperator_pow {τ : ℝ} (hτ : rho < τ) :
    Summable (fun n : ℕ => (τ⁻¹) ^ n • transferOperator ^ n) := by
{
  obtain ⟨r, hr, hrτ⟩ := exists_between hτ
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one (rho_ge_one.trans hr.le)
  apply summable_scaled_pow transferOperator hr0 hrτ
  filter_upwards [L_norm_eventually_le hr] with n hn
  rwa [norm_transferOperator_pow]
}

lemma rho_le_of_pow_bound {M c : ℝ} (hM : 0 < M) (_hc : 0 ≤ c)
    (hb : ∀ n : ℕ, L_norm n ≤ M * c ^ n) : rho ≤ c := by
{
  have hc0 : 0 < c := by
  {
    have h1 := hb 1
    have h2 := one_le_L_norm 1
    simp only [pow_one] at *
    nlinarith
  }
  have ht : Tendsto (fun n : ℕ => Real.log M / (n : ℝ) + Real.log c) atTop (𝓝 (Real.log c)) := by
  {
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add_const (Real.log c)
  }
  have hl : rho_log ≤ Real.log c := by
  {
    apply le_of_tendsto_of_tendsto tendsto_log_L_norm ht
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog := Real.log_le_log (L_norm_pos n) (hb n)
    rw [Real.log_mul hM.ne' (pow_pos hc0 n).ne', Real.log_pow] at hlog
    calc
      Real.log (L_norm n) / (n : ℝ) ≤ (Real.log M + (n : ℝ) * Real.log c) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog hnR.le
      _ = Real.log M / (n : ℝ) + Real.log c := by field_simp
  }
  simpa [rho, Real.exp_log hc0] using Real.exp_le_exp.mpr hl
}

def positiveResolvent (τ : ℝ) : C(DiskClass, ℝ) →L[ℝ] C(DiskClass, ℝ) :=
  ∑' n : ℕ, (τ⁻¹) ^ n • transferOperator ^ n

lemma summable_resolvent_eval {τ : ℝ} (hτ : rho < τ) (f : C(DiskClass, ℝ)) (x : DiskClass) :
    Summable (fun n : ℕ => (τ⁻¹) ^ n * (transferOperator ^ n) f x) := by
{
  let e : (C(DiskClass, ℝ) →L[ℝ] C(DiskClass, ℝ)) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM (R := ℝ) x).comp (ContinuousLinearMap.apply ℝ C(DiskClass, ℝ) f)
  have hs := e.summable (summable_scaled_transferOperator_pow hτ)
  simpa only [e, ContinuousLinearMap.comp_apply, ContinuousLinearMap.apply_apply,
    ContinuousLinearMap.smul_apply, ContinuousMap.evalCLM_apply,
    ContinuousMap.smul_apply, smul_eq_mul] using hs
}

lemma positiveResolvent_eval {τ : ℝ} (hτ : rho < τ) (f : C(DiskClass, ℝ)) (x : DiskClass) :
    positiveResolvent τ f x = ∑' n : ℕ, (τ⁻¹) ^ n * (transferOperator ^ n) f x := by
{
  let e : (C(DiskClass, ℝ) →L[ℝ] C(DiskClass, ℝ)) →L[ℝ] ℝ :=
    (ContinuousMap.evalCLM (R := ℝ) x).comp (ContinuousLinearMap.apply ℝ C(DiskClass, ℝ) f)
  exact e.map_tsum (summable_scaled_transferOperator_pow hτ)
}

lemma positiveResolvent_nonneg {τ : ℝ} (hτ : rho < τ) :
    ∀ f, 0 ≤ f → 0 ≤ positiveResolvent τ f := by
{
  have ht : 0 < τ := lt_of_lt_of_le zero_lt_one (rho_ge_one.trans hτ.le)
  intro f hf x
  change 0 ≤ positiveResolvent τ f x
  rw [positiveResolvent_eval hτ]
  exact tsum_nonneg (fun n => mul_nonneg (pow_nonneg (inv_nonneg.mpr ht.le) n)
    (positive_operator_pow transferOperator transferOperator_pos n f hf x))
}

lemma positiveResolvent_ge_one {τ : ℝ} (hτ : rho < τ) :
    1 ≤ positiveResolvent τ 1 := by
{
  have ht : 0 < τ := lt_of_lt_of_le zero_lt_one (rho_ge_one.trans hτ.le)
  intro x
  change 1 ≤ positiveResolvent τ 1 x
  rw [positiveResolvent_eval hτ]
  have hn (n : ℕ) : 0 ≤ (τ⁻¹) ^ n * (transferOperator ^ n) (1 : C(DiskClass, ℝ)) x :=
    mul_nonneg (pow_nonneg (inv_nonneg.mpr ht.le) n)
      (positive_operator_pow transferOperator transferOperator_pos n 1 (by intro; simp) x)
  simpa using (summable_resolvent_eval hτ 1 x).le_tsum 0 (fun n _ => hn n)
}

lemma positiveResolvent_tail {τ : ℝ} (hτ : rho < τ) :
    ∑' n : ℕ, (τ⁻¹) ^ (n + 1) • transferOperator ^ (n + 1) = positiveResolvent τ - 1 := by
{
  have he := (summable_scaled_transferOperator_pow hτ).sum_add_tsum_nat_add 1
  simpa [positiveResolvent] using eq_sub_iff_add_eq.mpr (by simpa [add_comm] using he)
}

lemma positiveResolvent_mul {τ : ℝ} (hτ : rho < τ) :
    positiveResolvent τ * transferOperator = τ • (positiveResolvent τ - 1) ∧
    transferOperator * positiveResolvent τ = τ • (positiveResolvent τ - 1) := by
{
  have ht : τ ≠ 0 := ne_of_gt (lt_of_lt_of_le zero_lt_one (rho_ge_one.trans hτ.le))
  have hs := summable_scaled_transferOperator_pow hτ
  have htail := positiveResolvent_tail hτ
  have he (n : ℕ) : τ • ((τ⁻¹) ^ (n + 1) • transferOperator ^ (n + 1)) =
      (τ⁻¹) ^ n • (transferOperator ^ n * transferOperator) := by
  {
    rw [smul_smul, pow_succ, pow_succ]
    congr 1
    field_simp
  }
  constructor
  · change (∑' n : ℕ, (τ⁻¹) ^ n • transferOperator ^ n) * transferOperator = _
    rw [show (∑' n : ℕ, (τ⁻¹) ^ n • transferOperator ^ n) * transferOperator =
      ∑' n : ℕ, ((τ⁻¹) ^ n • transferOperator ^ n) * transferOperator from
      ((ContinuousLinearMap.compL ℝ C(DiskClass, ℝ) C(DiskClass, ℝ) C(DiskClass, ℝ)).flip
        transferOperator).map_tsum hs, ← htail, ← tsum_const_smul'']
    exact tsum_congr (fun n => by rw [he]; exact ContinuousLinearMap.smul_comp _ _ _)
  · change transferOperator * (∑' n : ℕ, (τ⁻¹) ^ n • transferOperator ^ n) = _
    rw [show transferOperator * (∑' n : ℕ, (τ⁻¹) ^ n • transferOperator ^ n) =
      ∑' n : ℕ, transferOperator * ((τ⁻¹) ^ n • transferOperator ^ n) from
      ((ContinuousLinearMap.compL ℝ C(DiskClass, ℝ) C(DiskClass, ℝ) C(DiskClass, ℝ))
        transferOperator).map_tsum hs, ← htail, ← tsum_const_smul'']
    apply tsum_congr
    intro n
    rw [he]
    change transferOperator.comp ((τ⁻¹) ^ n • transferOperator ^ n) =
      (τ⁻¹) ^ n • ((transferOperator ^ n).comp transferOperator)
    rw [ContinuousLinearMap.comp_smul]
    congr 1
    change transferOperator * transferOperator ^ n = transferOperator ^ n * transferOperator
    rw [← pow_succ', ← pow_succ]
}

lemma positive_operator_pow_bound {g : C(DiskClass, ℝ)} (hg : 1 ≤ g)
    {c : ℝ} (hc : 0 ≤ c) (hLg : transferOperator g ≤ c • g) (n : ℕ) :
    L_norm n ≤ ‖g‖ * c ^ n := by
{
  have hiter : ∀ n : ℕ, (transferOperator ^ n) g ≤ c ^ n • g := by
  {
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h1 := positive_operator_mono transferOperator transferOperator_pos ih
      have h2 : c ^ m • transferOperator g ≤ c ^ m • (c • g) :=
        smul_le_smul_of_nonneg_left hLg (pow_nonneg hc m)
      rw [map_smul] at h1
      have h3 := h1.trans h2
      simpa only [pow_succ', ContinuousLinearMap.mul_apply, smul_smul, mul_comm] using h3
  }
  rw [← norm_transferOperator_pow_one]
  apply (ContinuousMap.norm_le _ (mul_nonneg (norm_nonneg _) (pow_nonneg hc n))).mpr
  intro x
  have hn := positive_operator_pow transferOperator transferOperator_pos n 1 (by intro; simp) x
  have h1 := positive_operator_mono (transferOperator ^ n)
    (positive_operator_pow transferOperator transferOperator_pos n) hg x
  have h2 := hiter n x
  change (transferOperator ^ n) g x ≤ c ^ n * g x at h2
  calc
    ‖(transferOperator ^ n) 1 x‖ = (transferOperator ^ n) 1 x := Real.norm_of_nonneg hn
    _ ≤ c ^ n * g x := h1.trans h2
    _ ≤ c ^ n * ‖g‖ := mul_le_mul_of_nonneg_left
      ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm g x)) (pow_nonneg hc n)
    _ = ‖g‖ * c ^ n := mul_comm _ _
}

lemma positiveResolvent_norm_bound {τ : ℝ} (hτ : rho < τ) :
    1 ≤ ‖positiveResolvent τ 1‖ ∧
    τ / ‖positiveResolvent τ 1‖ ≤ τ - rho := by
{
  let g := positiveResolvent τ 1
  have hg : 1 ≤ g := positiveResolvent_ge_one hτ
  have hM : 1 ≤ ‖g‖ :=
    (hg idDiskClass).trans ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm g idDiskClass))
  have hM0 : 0 < ‖g‖ := zero_lt_one.trans_le hM
  have ht : 0 < τ := lt_of_lt_of_le zero_lt_one (rho_ge_one.trans hτ.le)
  let c := τ * (1 - 1 / ‖g‖)
  have hc : 0 ≤ c := mul_nonneg ht.le (sub_nonneg.mpr ((div_le_one hM0).mpr hM))
  have he : transferOperator g = τ • (g - 1) := by
  {
    have hv := congrArg (fun A : C(DiskClass, ℝ) →L[ℝ] C(DiskClass, ℝ) => A 1)
      (positiveResolvent_mul hτ).2
    simpa only [ContinuousLinearMap.mul_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply] using hv
  }
  have hLg : transferOperator g ≤ c • g := by
  {
    rw [he]
    intro x
    change τ * (g x - 1) ≤ c * g x
    have hgx : g x ≤ ‖g‖ := (le_abs_self _).trans (ContinuousMap.norm_coe_le_norm g x)
    have hdiv : g x / ‖g‖ ≤ 1 := (div_le_one hM0).mpr hgx
    dsimp [c]
    have hh := mul_le_mul_of_nonneg_left hdiv ht.le
    simp only [div_eq_mul_inv, one_mul] at hh ⊢
    nlinarith
  }
  have hr := rho_le_of_pow_bound hM0 hc (positive_operator_pow_bound hg hc hLg)
  refine ⟨hM, ?_⟩
  dsimp [c] at hr
  change τ / ‖g‖ ≤ τ - rho
  simp only [div_eq_mul_inv, one_mul] at hr ⊢
  nlinarith
}

lemma probability_of_positive_functional
    (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (h1 : Λ 1 = 1) :
    ∃ μ : ProbabilityMeasure DiskClass, ∀ f : C(DiskClass, ℝ),
      ∫ x, f x ∂(μ : Measure DiskClass) = Λ f := by
{
  let Λ' : C_c(DiskClass, ℝ) →ₚ[ℝ] ℝ :=
    { toFun := fun f => Λ f.toContinuousMap
      map_add' := fun f g => map_add Λ f.toContinuousMap g.toContinuousMap
      map_smul' := fun c f => map_smul Λ c f.toContinuousMap
      monotone' := by
      {
        intro f g hfg
        have hn : 0 ≤ Λ (g.toContinuousMap - f.toContinuousMap) := hp _ (sub_nonneg.mpr hfg)
        simpa only [map_sub, sub_nonneg] using hn
      } }
  let μ := RealRMK.rieszMeasure Λ'
  have hi (f : C(DiskClass, ℝ)) : ∫ x, f x ∂μ = Λ f := by
  {
    let f' : C_c(DiskClass, ℝ) := ⟨f, HasCompactSupport.of_compactSpace f⟩
    exact RealRMK.integral_rieszMeasure Λ' f'
  }
  have hμ : IsProbabilityMeasure μ := isProbabilityMeasure_iff_real.mpr (by
  {
    have hh := hi 1
    simpa [h1] using hh
  })
  exact ⟨⟨μ, hμ⟩, hi⟩
}

lemma exists_max_of_nonneg_continuous (f : C(DiskClass, ℝ)) (hf : 0 ≤ f) :
    ∃ x : DiskClass, f x = ‖f‖ := by
{
  obtain ⟨x, _, hx⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty f.continuous.continuousOn
  refine ⟨x, le_antisymm ((le_abs_self _).trans (ContinuousMap.norm_coe_le_norm f x)) ?_⟩
  apply (ContinuousMap.norm_le f (hf x)).mpr
  intro y
  calc
    ‖f y‖ = f y := Real.norm_of_nonneg (hf y)
    _ ≤ f x := hx (mem_univ y)
}

lemma exists_resolvent_probability {τ : ℝ} (hτ : rho < τ) :
    ∃ μ : ProbabilityMeasure DiskClass, ∀ f : C(DiskClass, ℝ),
      |(∫ x, transferOperator f x ∂(μ : Measure DiskClass)) -
        τ * (∫ x, f x ∂(μ : Measure DiskClass))| ≤ (τ - rho) * ‖f‖ := by
{
  let R := positiveResolvent τ
  let g := R 1
  have hg : 1 ≤ g := positiveResolvent_ge_one hτ
  have hg0 : 0 ≤ g := le_trans (by intro; simp) hg
  obtain ⟨x, hx⟩ := exists_max_of_nonneg_continuous g hg0
  have hM := positiveResolvent_norm_bound hτ
  have hM0 : 0 < ‖g‖ := zero_lt_one.trans_le hM.1
  let Λ : C(DiskClass, ℝ) →L[ℝ] ℝ := (‖g‖⁻¹ • ContinuousMap.evalCLM (R := ℝ) x).comp R
  have hΛ (f : C(DiskClass, ℝ)) : Λ f = R f x / ‖g‖ := by
  {
    change ‖g‖⁻¹ * R f x = R f x / ‖g‖
    ring
  }
  have hpΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f := by
  {
    intro f hf
    rw [hΛ]
    exact div_nonneg (positiveResolvent_nonneg hτ f hf x) hM0.le
  }
  have h1 : Λ 1 = 1 := by
  {
    rw [hΛ]
    change g x / ‖g‖ = 1
    rw [hx, div_self hM0.ne']
  }
  obtain ⟨μ, hμ⟩ := probability_of_positive_functional Λ hpΛ h1
  refine ⟨μ, fun f => ?_⟩
  rw [hμ (transferOperator f), hμ f, hΛ, hΛ]
  have he : R (transferOperator f) x = τ * (R f x - f x) :=
    congrArg (fun A : C(DiskClass, ℝ) →L[ℝ] C(DiskClass, ℝ) => A f x) (positiveResolvent_mul hτ).1
  rw [he]
  have hτ0 : 0 ≤ τ := (lt_of_lt_of_le zero_lt_one (rho_ge_one.trans hτ.le)).le
  calc
    |τ * (R f x - f x) / ‖g‖ - τ * (R f x / ‖g‖)| = (τ / ‖g‖) * |f x| := by
    {
      rw [show τ * (R f x - f x) / ‖g‖ - τ * (R f x / ‖g‖) = -(τ / ‖g‖) * f x by ring,
        abs_mul, abs_neg, abs_of_nonneg (div_nonneg hτ0 hM0.le)]
    }
    _ ≤ (τ / ‖g‖) * ‖f‖ := mul_le_mul_of_nonneg_left (ContinuousMap.norm_coe_le_norm f x)
      (div_nonneg hτ0 hM0.le)
    _ ≤ (τ - rho) * ‖f‖ := mul_le_mul_of_nonneg_right hM.2 (norm_nonneg f)
}

lemma exists_growth_eigenmeasure :
    ∃ μ : ProbabilityMeasure DiskClass, ∀ f : C(DiskClass, ℝ),
      (∫ x, transferOperator f x ∂(μ : Measure DiskClass)) =
        rho * (∫ x, f x ∂(μ : Measure DiskClass)) := by
{
  let τ : ℕ → ℝ := fun n => rho + 1 / ((n : ℝ) + 1)
  have hτ (n : ℕ) : rho < τ n := lt_add_of_pos_right _ (by positivity)
  choose μ hμ using fun n : ℕ => exists_resolvent_probability (hτ n)
  let U := Ultrafilter.of (atTop : Filter ℕ)
  let V := U.map μ
  let ν := V.lim
  have hν : Tendsto μ (U : Filter ℕ) (𝓝 ν) := V.le_nhds_lim
  have ht : Tendsto τ (U : Filter ℕ) (𝓝 rho) := by
  {
    have hh : Tendsto τ atTop (𝓝 rho) := by
    {
      simpa [τ] using tendsto_one_div_add_atTop_nhds_zero_nat.const_add rho
    }
    exact hh.mono_left (Ultrafilter.of_le atTop)
  }
  refine ⟨ν, fun f => ?_⟩
  have hi := (ProbabilityMeasure.continuous_integral_continuousMap f).tendsto ν |>.comp hν
  have hLi := (ProbabilityMeasure.continuous_integral_continuousMap (transferOperator f)).tendsto ν |>.comp hν
  have hb := le_of_tendsto_of_tendsto ((hLi.sub (ht.mul hi)).abs)
    ((ht.sub_const rho).mul_const ‖f‖) (Eventually.of_forall (hμ · f))
  simp only [sub_self, zero_mul] at hb
  exact sub_eq_zero.mp (abs_nonpos_iff.mp hb)
}

lemma positive_functional_bound (Λ : C(DiskClass, ℝ) →ₗ[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (f : C(DiskClass, ℝ)) :
    ‖Λ f‖ ≤ Λ 1 * ‖f‖ := by
{
  have hlo : (-‖f‖) • (1 : C(DiskClass, ℝ)) ≤ f := by
  {
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).1
  }
  have hhi : f ≤ ‖f‖ • (1 : C(DiskClass, ℝ)) := by
  {
    intro x
    simpa using (abs_le.mp (ContinuousMap.norm_coe_le_norm f x)).2
  }
  have h1 := hp (f - (-‖f‖) • 1) (sub_nonneg.mpr hlo)
  have h2 := hp (‖f‖ • 1 - f) (sub_nonneg.mpr hhi)
  simp only [map_sub, map_smul, smul_eq_mul, neg_mul] at h1 h2
  rw [Real.norm_eq_abs]
  apply abs_le.mpr
  constructor <;> nlinarith
}

def positiveFunctionalCLM (Λ : C(DiskClass, ℝ) →ₗ[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) : C(DiskClass, ℝ) →L[ℝ] ℝ :=
  Λ.mkContinuous (Λ 1) (positive_functional_bound Λ hp)

def intervalFunctional (A : ℝ → C(DiskClass, ℝ) →L[ℝ] C(DiskClass, ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (a b : ℝ) (hab : a ≤ b) : C(DiskClass, ℝ) →L[ℝ] ℝ :=
  positiveFunctionalCLM
    { toFun := fun f => ∫ t in a..b, Λ (A t f)
      map_add' := fun f g => by
      {
        simp only [map_add]
        exact intervalIntegral.integral_add ((Λ.continuous.comp (hc f)).intervalIntegrable a b)
          ((Λ.continuous.comp (hc g)).intervalIntegrable a b)
      }
      map_smul' := fun c f => by
      {
        simp only [map_smul, smul_eq_mul]
        exact intervalIntegral.integral_const_mul c _
      } }
    (fun f hf => intervalIntegral.integral_nonneg hab (fun t _ => hΛ _ (hp t f hf)))

lemma intervalFunctional_apply (A : ℝ → C(DiskClass, ℝ) →L[ℝ] C(DiskClass, ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (a b : ℝ) (hab : a ≤ b) (f : C(DiskClass, ℝ)) :
    intervalFunctional A hc hp Λ hΛ a b hab f = ∫ t in a..b, Λ (A t f) := by
{
  rfl
}

lemma intervalFunctional_nonneg (A : ℝ → C(DiskClass, ℝ) →L[ℝ] C(DiskClass, ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (a b : ℝ) (hab : a ≤ b) (f : C(DiskClass, ℝ)) (hf : 0 ≤ f) :
    0 ≤ intervalFunctional A hc hp Λ hΛ a b hab f := by
{
  exact intervalIntegral.integral_nonneg hab (fun t _ => hΛ _ (hp t f hf))
}

def pointOperator (x y : ℝ) (hy : 0 < y) := affineOperator (halfPoint x y hy)

lemma pointOperator_mul (x y u v : ℝ) (hy : 0 < y) (hv : 0 < v) :
    pointOperator x y hy * pointOperator u v hv = pointOperator (x + y * u) (y * v) (mul_pos hy hv) := by
{
  simp only [pointOperator, affineOperator_mul, halfPoint_mul]
}

lemma pointOperator_zero_one : pointOperator 0 1 zero_lt_one = 1 := by
{
  have h : halfPoint 0 1 zero_lt_one = halfOne := by
  {
    apply Subtype.ext
    simp [halfPoint, halfOne]
  }
  rw [pointOperator, h, affineOperator_one]
}

lemma pointOperator_horizontal (x : ℝ) :
    pointOperator x 1 zero_lt_one = affineOperator (horizontal x) := by
{
  rfl
}

lemma transfer_endpoint_step (v : ℝ) (hv : 0 < v) :
    transferOperator * (pointOperator (1 + v) v hv - pointOperator (-1 + v) v hv) =
      (1 / 2 : ℝ) • (pointOperator (1 + v / 2) (v / 2) (by positivity) -
        pointOperator (-1 + v / 2) (v / 2) (by positivity)) := by
{
  change ((1 / 2 : ℝ) • (pointOperator (-1 / 2) (1 / 2) (by norm_num) +
    pointOperator (1 / 2) (1 / 2) (by norm_num))) * _ = _
  rw [smul_mul_assoc, add_mul, mul_sub, mul_sub]
  simp only [pointOperator_mul]
  have h1 : -1 / 2 + 1 / 2 * (1 + v) = v / 2 := by ring
  have h2 : -1 / 2 + 1 / 2 * (-1 + v) = -1 + v / 2 := by ring
  have h3 : 1 / 2 + 1 / 2 * (1 + v) = 1 + v / 2 := by ring
  have h4 : 1 / 2 + 1 / 2 * (-1 + v) = v / 2 := by ring
  simp only [h1, h2, h3, h4, show (1 / 2 : ℝ) * v = v / 2 by ring]
  congr 1
  abel
}

lemma transfer_endpoint (n : ℕ) :
    transferOperator ^ n * (affineOperator (horizontal 2) - 1) =
      ((1 / 2 : ℝ) ^ n) • (pointOperator (1 + (1 / 2 : ℝ) ^ n) ((1 / 2 : ℝ) ^ n) (by positivity) -
        pointOperator (-1 + (1 / 2 : ℝ) ^ n) ((1 / 2 : ℝ) ^ n) (by positivity)) := by
{
  induction n with
  | zero =>
    simp only [pow_zero, one_mul, one_smul]
    norm_num only [show (1 + (1 : ℝ)) = 2 by norm_num, show (-1 + (1 : ℝ)) = 0 by norm_num]
    rw [pointOperator_zero_one, pointOperator_horizontal]
  | succ n ih =>
    rw [pow_succ', mul_assoc, ih, mul_smul_comm, transfer_endpoint_step, smul_smul]
    simp only [pow_succ, div_eq_mul_inv, one_mul]
}

lemma endpoint_norm_bound (n : ℕ) :
    ‖pointOperator (1 + (1 / 2 : ℝ) ^ n) ((1 / 2 : ℝ) ^ n) (by positivity) -
      pointOperator (-1 + (1 / 2 : ℝ) ^ n) ((1 / 2 : ℝ) ^ n) (by positivity)‖ ≤
      8192 / ((1 / 2 : ℝ) ^ n) ^ 2 := by
{
  let v := (1 / 2 : ℝ) ^ n
  have hv : 0 < v := by positivity
  have hv1 : v ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hb (x : ℝ) (hx : |x| ≤ 2) : ‖pointOperator x v hv‖ ≤ 4096 / v ^ 2 := by
  {
    apply affineOperator_norm_le (by positivity)
    intro g
    have hq := lemma_2_2_bounds (toKClass g) x v 2 hv hv1 hx
    have h64 : ((2 : ℝ) ^ 2 + 4) ^ 2 / v = 64 / v := by ring
    rw [h64] at hq
    dsimp [diskWeight, halfPoint, A_weight]
    have hh := (sq_le_sq₀ (norm_nonneg _) (by positivity : 0 ≤ 64 / v)).mpr hq
    simpa only [div_pow, show (64 : ℝ) ^ 2 = 4096 by norm_num] using hh
  }
  have hp := hb (1 + v) (by rw [abs_le]; constructor <;> linarith)
  have hm := hb (-1 + v) (by rw [abs_le]; constructor <;> linarith)
  calc
    _ ≤ ‖pointOperator (1 + v) v hv‖ + ‖pointOperator (-1 + v) v hv‖ :=
      norm_sub_le (pointOperator (1 + v) v hv) (pointOperator (-1 + v) v hv)
    _ ≤ 4096 / v ^ 2 + 4096 / v ^ 2 := add_le_add hp hm
    _ = 8192 / v ^ 2 := by ring
}

lemma eigenfunctional_pow (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (ρ : ℝ)
    (hΛ : ∀ f, Λ (transferOperator f) = ρ * Λ f) (n : ℕ) (f : C(DiskClass, ℝ)) :
    Λ ((transferOperator ^ n) f) = ρ ^ n * Λ f := by
{
  induction n with
  | zero => simp
  | succ n ih => simp only [pow_succ', ContinuousLinearMap.mul_apply, hΛ, ih]; ring
}

lemma eigenfunctional_horizontal_period_step (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (ρ : ℝ)
    (hρ0 : 0 < ρ) (hΛ : ∀ f, Λ (transferOperator f) = ρ * Λ f) (f : C(DiskClass, ℝ)) (n : ℕ) :
    ‖Λ (affineOperator (horizontal 2) f) - Λ f‖ ≤ (8192 * ‖Λ‖ * ‖f‖) * (2 / ρ) ^ n := by
{
  let v := (1 / 2 : ℝ) ^ n
  let B := pointOperator (1 + v) v (by positivity) - pointOperator (-1 + v) v (by positivity)
  have he : ρ ^ n * (Λ (affineOperator (horizontal 2) f) - Λ f) = v * Λ (B f) := by
  {
    rw [← map_sub, ← eigenfunctional_pow Λ ρ hΛ]
    change Λ ((transferOperator ^ n * (affineOperator (horizontal 2) - 1)) f) = _
    rw [transfer_endpoint]
    change Λ (v • B f) = _
    exact map_smul Λ v (B f)
  }
  have hb : ‖B‖ ≤ 8192 / v ^ 2 := endpoint_norm_bound n
  have hh : ρ ^ n * ‖Λ (affineOperator (horizontal 2) f) - Λ f‖ ≤
      v * (‖Λ‖ * (8192 / v ^ 2 * ‖f‖)) := by
  {
    calc
      _ = ‖v * Λ (B f)‖ := by rw [← he, norm_mul, Real.norm_of_nonneg (pow_nonneg hρ0.le n)]
      _ ≤ v * (‖Λ‖ * (‖B‖ * ‖f‖)) := by
      {
        rw [norm_mul, Real.norm_of_nonneg (by positivity : 0 ≤ v)]
        exact mul_le_mul_of_nonneg_left ((Λ.le_opNorm _).trans
          (mul_le_mul_of_nonneg_left (B.le_opNorm f) (norm_nonneg Λ))) (by positivity)
      }
      _ ≤ _ := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_right hb (norm_nonneg f)) (norm_nonneg Λ)) (by positivity)
  }
  calc
    _ ≤ (v * (‖Λ‖ * (8192 / v ^ 2 * ‖f‖))) / ρ ^ n :=
      (le_div_iff₀ (pow_pos hρ0 n)).mpr (by simpa only [mul_comm] using hh)
    _ = _ := by dsimp [v]; simp only [div_pow, one_pow]; field_simp
}

lemma eigenfunctional_horizontal_period (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (ρ : ℝ)
    (hρ : 2 < ρ) (hΛ : ∀ f, Λ (transferOperator f) = ρ * Λ f) (f : C(DiskClass, ℝ)) :
    Λ (affineOperator (horizontal 2) f) = Λ f := by
{
  have hρ0 : 0 < ρ := by linarith
  have hn := eigenfunctional_horizontal_period_step Λ ρ hρ0 hΛ f
  have ht : Tendsto (fun n : ℕ => (8192 * ‖Λ‖ * ‖f‖) * (2 / ρ) ^ n) atTop (𝓝 0) := by
  {
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity : 0 ≤ 2 / ρ)
      ((div_lt_one hρ0).mpr hρ)).const_mul (8192 * ‖Λ‖ * ‖f‖)
  }
  exact sub_eq_zero.mp (norm_eq_zero.mp
    (le_antisymm (ge_of_tendsto ht (Eventually.of_forall hn)) (norm_nonneg _)))
}

def probabilityFunctional (μ : ProbabilityMeasure DiskClass) : C(DiskClass, ℝ) →L[ℝ] ℝ :=
  positiveFunctionalCLM
    { toFun := fun f => ∫ x, f x ∂(μ : Measure DiskClass)
      map_add' := fun f g => integral_add
        (f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
        (g.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
      map_smul' := fun c f => integral_smul c f }
    (fun _ hf => integral_nonneg hf)

lemma probabilityFunctional_apply (μ : ProbabilityMeasure DiskClass) (f : C(DiskClass, ℝ)) :
    probabilityFunctional μ f = ∫ x, f x ∂(μ : Measure DiskClass) := by
{
  rfl
}

lemma probabilityFunctional_one (μ : ProbabilityMeasure DiskClass) :
    probabilityFunctional μ 1 = 1 := by
{
  simp [probabilityFunctional_apply]
}

lemma probabilityFunctional_pos (μ : ProbabilityMeasure DiskClass) (f : C(DiskClass, ℝ)) (hf : 0 ≤ f) :
    0 ≤ probabilityFunctional μ f := by
{
  exact integral_nonneg hf
}

lemma periodic_dyadic_integral (F : ℝ → ℝ) (hc : Continuous F) (hp : Function.Periodic F 2) :
    (∫ x in (0 : ℝ)..2, (F (-1 / 2 + x / 2) + F (1 / 2 + x / 2))) = 2 * ∫ x in (0 : ℝ)..2, F x := by
{
  have hm : (∫ x in (0 : ℝ)..2, F (-1 / 2 + x / 2)) = 2 * ∫ x in (-1 / 2 : ℝ)..(1 / 2), F x := by
  {
    have hh := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 2) F
      (by norm_num : (1 / 2 : ℝ) ≠ 0) (-1 / 2)
    rw [smul_eq_mul] at hh
    convert hh using 1
    · congr 1; funext x; congr 1; ring
    · norm_num
  }
  have hp' : (∫ x in (0 : ℝ)..2, F (1 / 2 + x / 2)) = 2 * ∫ x in (1 / 2 : ℝ)..(3 / 2), F x := by
  {
    have hh := intervalIntegral.integral_comp_mul_add (a := (0 : ℝ)) (b := 2) F
      (by norm_num : (1 / 2 : ℝ) ≠ 0) (1 / 2)
    rw [smul_eq_mul] at hh
    convert hh using 1
    · congr 1; funext x; congr 1; ring
    · norm_num
  }
  have hi : (∫ x in (-1 / 2 : ℝ)..(3 / 2), F x) = ∫ x in (0 : ℝ)..2, F x := by
  {
    convert hp.intervalIntegral_add_eq (-1 / 2) 0 using 1 <;> norm_num
  }
  have hcm : Continuous (fun x : ℝ => F (-1 / 2 + x / 2)) :=
    hc.comp (continuous_const.add (continuous_id.div_const 2))
  have hcp : Continuous (fun x : ℝ => F (1 / 2 + x / 2)) :=
    hc.comp (continuous_const.add (continuous_id.div_const 2))
  rw [intervalIntegral.integral_add (hcm.intervalIntegrable _ _) (hcp.intervalIntegrable _ _),
    hm, hp', ← mul_add,
    intervalIntegral.integral_add_adjacent_intervals (hc.intervalIntegrable _ _) (hc.intervalIntegrable _ _), hi]
}

lemma continuous_pointOperator_x (y : ℝ) (hy : 0 < y) (f : C(DiskClass, ℝ)) :
    Continuous (fun x : ℝ => pointOperator x y hy f) := by
{
  exact (continuous_affineOperator_apply f).comp
    (continuous_halfPoint continuous_id continuous_const (fun _ => hy))
}

lemma continuous_horizontalOperator (f : C(DiskClass, ℝ)) :
    Continuous (fun x : ℝ => affineOperator (horizontal x) f) := by
{
  exact continuous_pointOperator_x 1 zero_lt_one f
}

def horizontalAverage (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) :
    C(DiskClass, ℝ) →L[ℝ] ℝ :=
  (1 / 2 : ℝ) • intervalFunctional (fun x => affineOperator (horizontal x))
    continuous_horizontalOperator (fun _ => affineOperator_pos _) Λ hp 0 2 (by norm_num)

lemma horizontalAverage_apply (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (f : C(DiskClass, ℝ)) :
    horizontalAverage Λ hp f = (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..2, Λ (affineOperator (horizontal x) f) := by
{
  rfl
}

lemma horizontalAverage_nonneg (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (f : C(DiskClass, ℝ)) (hf : 0 ≤ f) : 0 ≤ horizontalAverage Λ hp f := by
{
  rw [horizontalAverage_apply]
  apply mul_nonneg (by norm_num)
  exact intervalIntegral.integral_nonneg (by norm_num) (fun x _ => hp _ (affineOperator_pos _ f hf))
}

lemma horizontalAverage_mass_pos (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (h1 : 0 < Λ 1) : 0 < horizontalAverage Λ hp 1 := by
{
  rw [horizontalAverage_apply]
  apply mul_pos (by norm_num)
  apply intervalIntegral.integral_pos (by norm_num)
    (Λ.continuous.comp (continuous_horizontalOperator 1)).continuousOn
    (fun x _ => hp _ (affineOperator_pos _ 1 (by intro; simp)))
  refine ⟨0, by norm_num, ?_⟩
  change 0 < Λ (pointOperator 0 1 zero_lt_one 1)
  rw [pointOperator_zero_one, ContinuousLinearMap.one_apply]
  exact h1
}

lemma functional_point_periodic (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ)
    (hper : ∀ f, Λ (affineOperator (horizontal 2) f) = Λ f)
    (y : ℝ) (hy : 0 < y) (f : C(DiskClass, ℝ)) :
    Function.Periodic (fun x : ℝ => Λ (pointOperator x y hy f)) 2 := by
{
  intro x
  have hh := hper (pointOperator x y hy f)
  rw [← pointOperator_horizontal, ← ContinuousLinearMap.mul_apply, pointOperator_mul] at hh
  simpa only [one_mul, add_comm x 2] using hh
}

lemma horizontalAverage_point (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (u v : ℝ) (hv : 0 < v) (f : C(DiskClass, ℝ)) :
    horizontalAverage Λ hp (pointOperator u v hv f) =
      (1 / 2 : ℝ) * ∫ x in (0 : ℝ)..2, Λ (pointOperator (x + u) v hv f) := by
{
  rw [horizontalAverage_apply]
  congr 1
  apply intervalIntegral.integral_congr
  intro x _
  dsimp only
  rw [← pointOperator_horizontal, ← ContinuousLinearMap.mul_apply, pointOperator_mul]
  simp only [one_mul]
}

lemma horizontalAverage_invariant (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hper : ∀ f, Λ (affineOperator (horizontal 2) f) = Λ f)
    (t : ℝ) (f : C(DiskClass, ℝ)) :
    horizontalAverage Λ hp (affineOperator (horizontal t) f) = horizontalAverage Λ hp f := by
{
  rw [← pointOperator_horizontal, horizontalAverage_point]
  rw [intervalIntegral.integral_comp_add_right (fun x => Λ (pointOperator x 1 zero_lt_one f)) t]
  have hh := (functional_point_periodic Λ hper 1 zero_lt_one f).intervalIntegral_add_eq t 0
  rw [zero_add] at hh
  rw [zero_add, add_comm 2 t, hh, horizontalAverage_apply]
  rfl
}

lemma horizontalAverage_half_scale (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hper : ∀ f, Λ (affineOperator (horizontal 2) f) = Λ f)
    (ρ : ℝ) (heig : ∀ f, Λ (transferOperator f) = ρ * Λ f) (f : C(DiskClass, ℝ)) :
    horizontalAverage Λ hp (pointOperator 0 (1 / 2) (by norm_num) f) = ρ * horizontalAverage Λ hp f := by
{
  have he (x : ℝ) : ρ * Λ (affineOperator (horizontal x) f) =
      (1 / 2 : ℝ) * (Λ (pointOperator (-1 / 2 + x / 2) (1 / 2) (by norm_num) f) +
        Λ (pointOperator (1 / 2 + x / 2) (1 / 2) (by norm_num) f)) := by
  {
    rw [← heig]
    change Λ (((1 / 2 : ℝ) • (pointOperator (-1 / 2) (1 / 2) (by norm_num) +
      pointOperator (1 / 2) (1 / 2) (by norm_num)))
      (pointOperator x 1 zero_lt_one f)) = _
    rw [← ContinuousLinearMap.mul_apply, smul_mul_assoc, add_mul]
    simp only [pointOperator_mul, mul_one, ContinuousLinearMap.smul_apply, map_smul,
      ContinuousLinearMap.add_apply, map_add, smul_eq_mul, show (1 / 2 : ℝ) * x = x / 2 by ring]
  }
  have hc : Continuous (fun x : ℝ => Λ (pointOperator x (1 / 2) (by norm_num) f)) :=
    Λ.continuous.comp (continuous_pointOperator_x _ _ f)
  have hi := periodic_dyadic_integral (fun x => Λ (pointOperator x (1 / 2) (by norm_num) f)) hc
    (functional_point_periodic Λ hper (1 / 2) (by norm_num) f)
  rw [horizontalAverage_point, horizontalAverage_apply]
  simp only [add_zero]
  rw [show ρ * ((1 / 2 : ℝ) * ∫ x in (0 : ℝ)..2, Λ (affineOperator (horizontal x) f)) =
    (1 / 2 : ℝ) * (∫ x in (0 : ℝ)..2, ρ * Λ (affineOperator (horizontal x) f)) by
      rw [intervalIntegral.integral_const_mul]; ring]
  simp_rw [he]
  rw [intervalIntegral.integral_const_mul, hi]
  ring
}

lemma period_average_invariant (A : ℝ → C(DiskClass, ℝ) →L[ℝ] C(DiskClass, ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (hm : ∀ t s, A (t + s) = A t * A s)
    (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (l : ℝ) (hl : 0 ≤ l) (hper : ∀ f, Λ (A l f) = Λ f)
    (s : ℝ) (f : C(DiskClass, ℝ)) :
    intervalFunctional A hc hp Λ hΛ 0 l hl (A s f) =
      intervalFunctional A hc hp Λ hΛ 0 l hl f := by
{
  have hfper : Function.Periodic (fun t : ℝ => Λ (A t f)) l := by
  {
    intro t
    dsimp only
    rw [add_comm t l, hm, ContinuousLinearMap.mul_apply, hper]
  }
  rw [intervalFunctional_apply, intervalFunctional_apply]
  have he (t : ℝ) : Λ (A t (A s f)) = Λ (A (t + s) f) := by
  {
    rw [hm, ContinuousLinearMap.mul_apply]
  }
  simp_rw [he]
  rw [intervalIntegral.integral_comp_add_right (fun t => Λ (A t f)) s]
  simpa only [zero_add, add_comm l s] using hfper.intervalIntegral_add_eq s 0
}

lemma intervalFunctional_mass_pos (A : ℝ → C(DiskClass, ℝ) →L[ℝ] C(DiskClass, ℝ))
    (hc : ∀ f, Continuous (fun t => A t f))
    (hp : ∀ t f, 0 ≤ f → 0 ≤ A t f)
    (h0 : A 0 = 1)
    (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ) (hΛ : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (h1 : 0 < Λ 1) (l : ℝ) (hl : 0 < l) :
    0 < intervalFunctional A hc hp Λ hΛ 0 l hl.le 1 := by
{
  rw [intervalFunctional_apply]
  apply intervalIntegral.integral_pos hl (Λ.continuous.comp (hc 1)).continuousOn
    (fun t _ => hΛ _ (hp _ _ (by intro; simp)))
  refine ⟨0, by simp [hl.le], ?_⟩
  change 0 < Λ (A 0 1)
  simpa only [h0, ContinuousLinearMap.one_apply] using h1
}

def logScaledOperator (β t : ℝ) : C(DiskClass, ℝ) →L[ℝ] C(DiskClass, ℝ) :=
  Real.exp (β * t) • pointOperator 0 (Real.exp t) (Real.exp_pos t)

lemma logScaledOperator_apply (β t : ℝ) (f : C(DiskClass, ℝ)) :
    logScaledOperator β t f = Real.exp (β * t) • pointOperator 0 (Real.exp t) (Real.exp_pos t) f := by
{
  rfl
}

lemma continuous_logScaledOperator (β : ℝ) (f : C(DiskClass, ℝ)) :
    Continuous (fun t => logScaledOperator β t f) := by
{
  exact (Real.continuous_exp.comp (continuous_const.mul continuous_id)).smul
    ((continuous_affineOperator_apply f).comp
      (continuous_halfPoint continuous_const Real.continuous_exp Real.exp_pos))
}

lemma logScaledOperator_pos (β t : ℝ) (f : C(DiskClass, ℝ)) (hf : 0 ≤ f) :
    0 ≤ logScaledOperator β t f := by
{
  rw [logScaledOperator_apply]
  exact smul_nonneg (Real.exp_pos _).le (affineOperator_pos _ f hf)
}

lemma logScaledOperator_zero (β : ℝ) : logScaledOperator β 0 = 1 := by
{
  simp only [logScaledOperator, mul_zero, Real.exp_zero, one_smul, pointOperator_zero_one]
}

lemma logScaledOperator_add (β t s : ℝ) :
    logScaledOperator β (t + s) = logScaledOperator β t * logScaledOperator β s := by
{
  simp only [logScaledOperator, smul_mul_smul_comm, pointOperator_mul,
    mul_zero, add_zero, Real.exp_add, mul_add]
}

lemma logScaledOperator_horizontal (β t u : ℝ) :
    logScaledOperator β t * affineOperator (horizontal u) =
      affineOperator (horizontal (Real.exp t * u)) * logScaledOperator β t := by
{
  simp only [logScaledOperator, ← pointOperator_horizontal, smul_mul_assoc,
    mul_smul_comm, pointOperator_mul, mul_one, one_mul, mul_zero, zero_add, add_zero]
}

lemma horizontalAverage_log_period (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hper : ∀ f, Λ (affineOperator (horizontal 2) f) = Λ f)
    (ρ : ℝ) (hρ : 0 < ρ) (heig : ∀ f, Λ (transferOperator f) = ρ * Λ f)
    (f : C(DiskClass, ℝ)) :
    horizontalAverage Λ hp (logScaledOperator (Real.log ρ / Real.log 2) (Real.log 2) f) =
      horizontalAverage Λ hp f := by
{
  have he := horizontalAverage_half_scale Λ hp hper ρ heig (pointOperator 0 2 (by norm_num) f)
  rw [← ContinuousLinearMap.mul_apply, pointOperator_mul] at he
  norm_num only [mul_zero, add_zero, show (1 / 2 : ℝ) * 2 = 1 by norm_num,
    pointOperator_zero_one, ContinuousLinearMap.one_apply] at he
  rw [logScaledOperator_apply, map_smul, smul_eq_mul]
  rw [div_mul_cancel₀ _ (ne_of_gt (Real.log_pos (by norm_num : (1 : ℝ) < 2))),
    Real.exp_log hρ]
  simp only [Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  exact he.symm
}

def scaleAverage (β : ℝ) (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) : C(DiskClass, ℝ) →L[ℝ] ℝ :=
  intervalFunctional (logScaledOperator β) (continuous_logScaledOperator β) (logScaledOperator_pos β)
    Λ hp 0 (Real.log 2) (Real.log_nonneg (by norm_num))

lemma scaleAverage_apply (β : ℝ) (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (f : C(DiskClass, ℝ)) :
    scaleAverage β Λ hp f = ∫ t in (0 : ℝ)..Real.log 2, Λ (logScaledOperator β t f) := by
{
  rfl
}

lemma scaleAverage_pos (β : ℝ) (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (f : C(DiskClass, ℝ)) (hf : 0 ≤ f) :
    0 ≤ scaleAverage β Λ hp f := by
{
  exact intervalFunctional_nonneg _ _ _ _ hp _ _ _ f hf
}

lemma scaleAverage_mass_pos (β : ℝ) (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f) (h1 : 0 < Λ 1) : 0 < scaleAverage β Λ hp 1 := by
{
  exact intervalFunctional_mass_pos _ _ _ (logScaledOperator_zero β) Λ hp h1 _ (Real.log_pos (by norm_num))
}

lemma scaleAverage_covariant (β : ℝ) (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hper : ∀ f, Λ (logScaledOperator β (Real.log 2) f) = Λ f)
    (y : ℝ) (hy : 0 < y) (f : C(DiskClass, ℝ)) :
    scaleAverage β Λ hp (pointOperator 0 y hy f) = y ^ (-β) * scaleAverage β Λ hp f := by
{
  have he := period_average_invariant (logScaledOperator β) (continuous_logScaledOperator β)
    (logScaledOperator_pos β) (logScaledOperator_add β) Λ hp (Real.log 2)
    (Real.log_nonneg (by norm_num)) hper (Real.log y) f
  change scaleAverage β Λ hp (logScaledOperator β (Real.log y) f) = scaleAverage β Λ hp f at he
  simp only [logScaledOperator_apply, map_smul, smul_eq_mul, Real.exp_log hy] at he
  rw [Real.rpow_def_of_pos hy]
  have hinv : Real.exp (Real.log y * (-β)) * Real.exp (β * Real.log y) = 1 := by
  {
    rw [← Real.exp_add, show Real.log y * (-β) + β * Real.log y = 0 by ring, Real.exp_zero]
  }
  calc
    _ = (Real.exp (Real.log y * (-β)) * Real.exp (β * Real.log y)) *
        scaleAverage β Λ hp (pointOperator 0 y hy f) := by rw [hinv, one_mul]
    _ = _ := by rw [mul_assoc, he]
}

lemma scaleAverage_horizontal (β : ℝ) (Λ : C(DiskClass, ℝ) →L[ℝ] ℝ)
    (hp : ∀ f, 0 ≤ f → 0 ≤ Λ f)
    (hh : ∀ u f, Λ (affineOperator (horizontal u) f) = Λ f)
    (u : ℝ) (f : C(DiskClass, ℝ)) :
    scaleAverage β Λ hp (affineOperator (horizontal u) f) = scaleAverage β Λ hp f := by
{
  rw [scaleAverage_apply, scaleAverage_apply]
  apply intervalIntegral.integral_congr
  intro t _
  dsimp only
  rw [← ContinuousLinearMap.mul_apply, logScaledOperator_horizontal,
    ContinuousLinearMap.mul_apply, hh]
}

lemma affineOperator_re_im_decomp (z : H) :
    affineOperator z = affineOperator (horizontal z.1.re) * pointOperator 0 z.1.im z.2 := by
{
  rw [← pointOperator_horizontal, pointOperator_mul]
  congr 1
  apply Subtype.ext
  simpa only [halfPoint, mul_zero, add_zero, one_mul] using z.1.re_add_im.symm
}

lemma exists_weighted_continuous_law (hρ : 2 < rho) :
    ∃ P : ProbabilityMeasure DiskClass, ∀ z : H, ∀ f : C(DiskClass, ℝ),
      (∫ g, diskWeight g z * f (rerootDisk g z) ∂(P : Measure DiskClass)) =
        (z.1.im : ℝ) ^ (-(Real.log rho / Real.log 2)) * (∫ g, f g ∂(P : Measure DiskClass)) := by
{
  let β := Real.log rho / Real.log 2
  obtain ⟨μ, hμ⟩ := exists_growth_eigenmeasure
  let Λ := probabilityFunctional μ
  have hp : ∀ f, 0 ≤ f → 0 ≤ Λ f := probabilityFunctional_pos μ
  have h1 : Λ 1 = 1 := probabilityFunctional_one μ
  have heig : ∀ f, Λ (transferOperator f) = rho * Λ f := hμ
  have hper := eigenfunctional_horizontal_period Λ rho hρ heig
  let H_avg := horizontalAverage Λ hp
  have hH : ∀ f, 0 ≤ f → 0 ≤ H_avg f := horizontalAverage_nonneg Λ hp
  have hH1 : 0 < H_avg 1 := horizontalAverage_mass_pos Λ hp (by rw [h1]; norm_num)
  have hHper : ∀ f, H_avg (logScaledOperator β (Real.log 2) f) = H_avg f :=
    horizontalAverage_log_period Λ hp hper rho (by linarith) heig
  have hHh : ∀ u f, H_avg (affineOperator (horizontal u) f) = H_avg f :=
    horizontalAverage_invariant Λ hp hper
  let ν := scaleAverage β H_avg hH
  have hν : ∀ f, 0 ≤ f → 0 ≤ ν f := scaleAverage_pos β H_avg hH
  have hν1 : 0 < ν 1 := scaleAverage_mass_pos β H_avg hH hH1
  have hνh : ∀ u f, ν (affineOperator (horizontal u) f) = ν f := scaleAverage_horizontal β H_avg hH hHh
  have hνs : ∀ y (hy : 0 < y) f, ν (pointOperator 0 y hy f) = y ^ (-β) * ν f :=
    scaleAverage_covariant β H_avg hH hHper
  let PiF : C(DiskClass, ℝ) →L[ℝ] ℝ := (ν 1)⁻¹ • ν
  have hPiF : ∀ f, 0 ≤ f → 0 ≤ PiF f := fun f hf => mul_nonneg (inv_nonneg.mpr hν1.le) (hν f hf)
  have hPiF1 : PiF 1 = 1 := by
  {
    change (ν 1)⁻¹ * ν 1 = 1
    exact inv_mul_cancel₀ (ne_of_gt hν1)
  }
  obtain ⟨P, hP⟩ := probability_of_positive_functional PiF hPiF hPiF1
  refine ⟨P, fun z f => ?_⟩
  change (∫ g, (affineOperator z f) g ∂(P : Measure DiskClass)) = _
  rw [hP, hP]
  change (ν 1)⁻¹ * ν (affineOperator z f) = _
  rw [affineOperator_re_im_decomp z, ContinuousLinearMap.mul_apply, hνh, hνs]
  change (ν 1)⁻¹ * ((z.1.im : ℝ) ^ (-β) * ν f) = (z.1.im : ℝ) ^ (-β) * ((ν 1)⁻¹ * ν f)
  ring
}

lemma weighted_measure_eq {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : C(X, ℝ)) (hw : ∀ x, 0 ≤ w x)
    (T : C(X, X)) (c : ℝ) (hc : 0 ≤ c)
    (he : ∀ f : C(X, ℝ), (∫ x, w x * f (T x) ∂μ) = c * ∫ x, f x ∂μ) :
    Measure.map T (μ.withDensity (fun x => ENNReal.ofReal (w x))) = ENNReal.ofReal c • μ := by
{
  let ν := μ.withDensity (fun x => ENNReal.ofReal (w x))
  have : IsFiniteMeasure ν := isFiniteMeasure_withDensity_ofReal
    (w.continuous.integrable_of_hasCompactSupport (μ := μ)
      (HasCompactSupport.of_compactSpace w)).hasFiniteIntegral
  have : (ENNReal.ofReal c • μ).Regular := Measure.Regular.smul (μ := μ) ENNReal.ofReal_ne_top
  have hwmeas : Measurable (fun x => ENNReal.ofReal (w x)) := w.continuous.measurable.ennreal_ofReal
  apply Measure.ext_of_integral_eq_on_compactlySupported
  intro f
  change (∫ x, f.toContinuousMap x ∂Measure.map T (μ.withDensity (fun x => ENNReal.ofReal (w x)))) =
    ∫ x, f.toContinuousMap x ∂ENNReal.ofReal c • μ
  rw [integral_map T.continuous.measurable.aemeasurable f.continuous.aestronglyMeasurable]
  rw [integral_withDensity_eq_integral_toReal_smul hwmeas
    (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))]
  simp only [ENNReal.toReal_ofReal (hw _), smul_eq_mul]
  rw [he f.toContinuousMap, integral_smul_measure, ENNReal.toReal_ofReal hc, smul_eq_mul]
}

lemma weighted_lintegral_of_continuous {X : Type*} [TopologicalSpace X] [CompactSpace X]
    [T2Space X] [TopologicalSpace.PseudoMetrizableSpace X] [MeasurableSpace X] [BorelSpace X]
    (μ : Measure X) [IsFiniteMeasure μ] (w : C(X, ℝ)) (hw : ∀ x, 0 ≤ w x)
    (T : C(X, X)) (c : ℝ) (hc : 0 ≤ c)
    (he : ∀ f : C(X, ℝ), (∫ x, w x * f (T x) ∂μ) = c * ∫ x, f x ∂μ)
    (f : X → ℝ≥0∞) (hf : Measurable f) :
    (∫⁻ x, ENNReal.ofReal (w x) * f (T x) ∂μ) = ENNReal.ofReal c * ∫⁻ x, f x ∂μ := by
{
  have hh := weighted_measure_eq μ w hw T c hc he
  have hi := congrArg (fun ν : Measure X => ∫⁻ x, f x ∂ν) hh
  rw [lintegral_map hf T.continuous.measurable, lintegral_smul_measure] at hi
  change (∫⁻ x, (f ∘ T) x ∂μ.withDensity (fun x => ENNReal.ofReal (w x))) = _ at hi
  rw [lintegral_withDensity_eq_lintegral_mul μ w.continuous.measurable.ennreal_ofReal
    (hf.comp T.continuous.measurable)] at hi
  simpa only [Pi.mul_apply, smul_eq_mul, Function.comp_def] using hi
}

lemma continuous_A_weight {z : ℂ} (hz : z ∈ H) :
    Continuous (fun F : KClass => A_weight z F.F) := by
{
  dsimp [A_weight]
  have hQ : Continuous (fun F : KClass => Q F.F z) := by
  {
    simpa only [iteratedDeriv_zero] using continuous_iteratedDeriv_Q_eval 0 hz
  }
  exact hQ.norm.pow 2
}

lemma continuous_T_elem {z : ℂ} (hz : z ∈ H) :
    Continuous (fun F : KClass => T_elem F z hz) := by
{
  rw [continuous_induced_rng]
  have heq : ofKClass ∘ (fun F : KClass => T_elem F z hz) =
      fun F : KClass => rerootDisk (ofKClass F) ⟨z, hz⟩ := by
  {
    funext F
    exact ofKClass_eq_of_eqOn (T_congr (toKClass_ofKClass_eqOn F) hz).symm
  }
  rw [heq]
  exact continuous_comp₂ continuous_rerootDisk continuous_ofKClass continuous_const
}

lemma measurableSet_inseparable_iff {F₁ F₂ : KClass} (hins : Inseparable F₁ F₂)
    {s : Set KClass} (hs : MeasurableSet s) :
    F₁ ∈ s ↔ F₂ ∈ s := by
{
  let m : MeasurableSpace KClass :=
    { MeasurableSet' := fun t => F₁ ∈ t ↔ F₂ ∈ t
      measurableSet_empty := Iff.rfl
      measurableSet_compl := fun _ ht => not_congr ht
      measurableSet_iUnion := fun f hf => by
      {
        simp only [mem_iUnion]
        exact exists_congr hf
      } }
  have hm : instMeasurableSpaceKClass ≤ m := by
  {
    apply MeasurableSpace.generateFrom_le
    intro U hU
    exact hins.mem_open_iff hU
  }
  exact hm s hs
}

lemma measurable_apply_eq_of_inseparable {F₁ F₂ : KClass} (hins : Inseparable F₁ F₂)
    {Phi : KClass → ℝ≥0∞} (hPhi : Measurable Phi) :
    Phi F₁ = Phi F₂ := by
{
  have hmem : F₁ ∈ Phi ⁻¹' {Phi F₁} := rfl
  have hmeas : MeasurableSet (Phi ⁻¹' {Phi F₁}) := hPhi (measurableSet_singleton (Phi F₁))
  exact ((measurableSet_inseparable_iff hins hmeas).mp hmem).symm
}

lemma inseparable_T_elem_toKClass (g : DiskClass) {z : ℂ} (hz : z ∈ H) :
    Inseparable (T_elem (toKClass g) z hz) (toKClass (rerootDisk g ⟨z, hz⟩)) := by
{
  dsimp [rerootDisk]
  rw [Inseparable, nhds_induced ofKClass, nhds_induced ofKClass, ofKClass_toKClass]
}

lemma weighted_covariance_pushforward_continuous (P_disk : ProbabilityMeasure DiskClass)
    (hP_disk : ∀ z : H, ∀ f : C(DiskClass, ℝ),
      (∫ g, diskWeight g z * f (rerootDisk g z) ∂(P_disk : Measure DiskClass)) =
        (z.1.im : ℝ) ^ (-(Real.log rho / Real.log 2)) * (∫ g, f g ∂(P_disk : Measure DiskClass)))
    {z : ℂ} (hz : z ∈ H) {Phi : KClass → ℝ} (hPhi : Continuous Phi) :
    ∫ F, A_weight z F.F * Phi (T_elem F z hz) ∂(Measure.map toKClass (P_disk : Measure DiskClass)) =
      (z.im : ℝ) ^ (-(Real.log rho / Real.log 2)) *
        ∫ F, Phi F ∂(Measure.map toKClass (P_disk : Measure DiskClass)) := by
{
  let f : C(DiskClass, ℝ) := ⟨Phi ∘ toKClass, hPhi.comp continuous_toKClass⟩
  have h_rhs : ∫ F, Phi F ∂(Measure.map toKClass (P_disk : Measure DiskClass)) =
      ∫ g, f g ∂(P_disk : Measure DiskClass) :=
    integral_map continuous_toKClass.measurable.aemeasurable hPhi.aestronglyMeasurable
  have h_lhs_cont : Continuous (fun F : KClass => A_weight z F.F * Phi (T_elem F z hz)) :=
    (continuous_A_weight hz).mul (hPhi.comp (continuous_T_elem hz))
  have h_lhs : ∫ F, A_weight z F.F * Phi (T_elem F z hz) ∂(Measure.map toKClass (P_disk : Measure DiskClass)) =
      ∫ g, diskWeight g ⟨z, hz⟩ * f (rerootDisk g ⟨z, hz⟩) ∂(P_disk : Measure DiskClass) := by
  {
    rw [integral_map continuous_toKClass.measurable.aemeasurable h_lhs_cont.aestronglyMeasurable]
    apply integral_congr_ae
    refine Eventually.of_forall (fun g => ?_)
    dsimp [diskWeight, f]
    rw [((inseparable_T_elem_toKClass g hz).map hPhi).eq]
  }
  rw [h_lhs, h_rhs]
  exact hP_disk ⟨z, hz⟩ f
}

lemma weighted_covariance_pushforward_lintegral (P_disk : ProbabilityMeasure DiskClass)
    (hP_disk : ∀ z : H, ∀ f : C(DiskClass, ℝ),
      (∫ g, diskWeight g z * f (rerootDisk g z) ∂(P_disk : Measure DiskClass)) =
        (z.1.im : ℝ) ^ (-(Real.log rho / Real.log 2)) * (∫ g, f g ∂(P_disk : Measure DiskClass)))
    {z : ℂ} (hz : z ∈ H) {Phi : KClass → ℝ≥0∞} (hPhi : Measurable Phi) :
    ∫⁻ F, ENNReal.ofReal (A_weight z F.F) * Phi (T_elem F z hz)
        ∂(Measure.map toKClass (P_disk : Measure DiskClass)) =
      ENNReal.ofReal ((z.im : ℝ) ^ (-(Real.log rho / Real.log 2))) *
        ∫⁻ F, Phi F ∂(Measure.map toKClass (P_disk : Measure DiskClass)) := by
{
  let f : DiskClass → ℝ≥0∞ := Phi ∘ toKClass
  have hf : Measurable f := hPhi.comp continuous_toKClass.measurable
  have h_rhs : ∫⁻ F, Phi F ∂(Measure.map toKClass (P_disk : Measure DiskClass)) =
      ∫⁻ g, f g ∂(P_disk : Measure DiskClass) :=
    lintegral_map hPhi continuous_toKClass.measurable
  have h_lhs_meas : Measurable (fun F : KClass =>
      ENNReal.ofReal (A_weight z F.F) * Phi (T_elem F z hz)) :=
    (continuous_A_weight hz).measurable.ennreal_ofReal.mul (hPhi.comp (continuous_T_elem hz).measurable)
  have h_lhs : ∫⁻ F, ENNReal.ofReal (A_weight z F.F) * Phi (T_elem F z hz)
        ∂(Measure.map toKClass (P_disk : Measure DiskClass)) =
      ∫⁻ g, ENNReal.ofReal (diskWeight g ⟨z, hz⟩) * f (rerootDisk g ⟨z, hz⟩) ∂(P_disk : Measure DiskClass) := by
  {
    rw [lintegral_map h_lhs_meas continuous_toKClass.measurable]
    apply lintegral_congr (fun g => ?_)
    dsimp [diskWeight, f]
    rw [measurable_apply_eq_of_inseparable (inseparable_T_elem_toKClass g hz) hPhi]
  }
  rw [h_lhs, h_rhs]
  exact weighted_lintegral_of_continuous (P_disk : Measure DiskClass) (weightAt ⟨z, hz⟩)
    (fun g => (diskWeight_pos g ⟨z, hz⟩).le) (actionAt ⟨z, hz⟩)
    ((z.im : ℝ) ^ (-(Real.log rho / Real.log 2))) (Real.rpow_nonneg hz.le _)
    (hP_disk ⟨z, hz⟩) f hf
}

/-- Existence of the weighted affine-covariant eigenmeasure when `ρ > 2` (Lemma 3.1). -/
theorem exists_weighted_covariance_measure (h_rho : rho > 2) :
    ∃ P : MeasureTheory.Measure KClass, IsProbabilityMeasure P ∧
      (∀ (z : ℂ) (hz : z ∈ H) (Phi : KClass → ℝ),
        Continuous Phi →
        ∫ F, A_weight z F.F * Phi ⟨T z F.F, (T_KClass F z hz).1, (T_KClass F z hz).2.1, (T_KClass F z hz).2.2⟩ ∂P =
          (z.im : ℝ) ^ (-(Real.log rho / Real.log 2)) * ∫ F, Phi F ∂P) ∧
      (∀ (z : ℂ) (hz : z ∈ H) (Phi : KClass → ℝ≥0∞),
        Measurable Phi →
        ∫⁻ F, ENNReal.ofReal (A_weight z F.F) *
            Phi ⟨T z F.F, (T_KClass F z hz).1, (T_KClass F z hz).2.1, (T_KClass F z hz).2.2⟩ ∂P =
          ENNReal.ofReal ((z.im : ℝ) ^ (-(Real.log rho / Real.log 2))) * ∫⁻ F, Phi F ∂P) := by
{
  obtain ⟨P_disk, hP_disk⟩ := exists_weighted_continuous_law h_rho
  refine ⟨Measure.map toKClass (P_disk : Measure DiskClass),
    Measure.isProbabilityMeasure_map continuous_toKClass.measurable.aemeasurable,
    fun z hz Phi hPhi => weighted_covariance_pushforward_continuous P_disk hP_disk hz hPhi,
    fun z hz Phi hPhi => weighted_covariance_pushforward_lintegral P_disk hP_disk hz hPhi⟩
}

/-- Chosen probability measure on `KClass` when `ρ > 2`. -/
def P_eigenmeasure : MeasureTheory.Measure KClass :=
  if h : rho > 2 then (exists_weighted_covariance_measure h).choose else 0

/-- Lemma 3.1 (Weighted affine covariance on continuous functions). -/
lemma lemma_3_1_weighted_covariance (h_rho : rho > 2) :
    IsProbabilityMeasure P_eigenmeasure ∧
    ∀ (z : ℂ) (hz : z ∈ H) (Phi : KClass → ℝ),
      Continuous Phi →
      ∫ F, A_weight z F.F * Phi ⟨T z F.F, (T_KClass F z hz).1, (T_KClass F z hz).2.1, (T_KClass F z hz).2.2⟩ ∂P_eigenmeasure =
        (z.im : ℝ) ^ (-(Real.log rho / Real.log 2)) * ∫ F, Phi F ∂P_eigenmeasure := by
{
  dsimp [P_eigenmeasure]
  rw [dif_pos h_rho]
  have h := (exists_weighted_covariance_measure h_rho).choose_spec
  exact ⟨h.1, h.2.1⟩
}

/-- Lemma 3.1 (Weighted affine covariance for nonnegative Borel measurable functions, Eq. 3.1). -/
lemma lemma_3_1_weighted_covariance_lintegral (h_rho : rho > 2) :
    IsProbabilityMeasure P_eigenmeasure ∧
    ∀ (z : ℂ) (hz : z ∈ H) (Phi : KClass → ℝ≥0∞),
      Measurable Phi →
      ∫⁻ F, ENNReal.ofReal (A_weight z F.F) *
          Phi ⟨T z F.F, (T_KClass F z hz).1, (T_KClass F z hz).2.1, (T_KClass F z hz).2.2⟩ ∂P_eigenmeasure =
        ENNReal.ofReal ((z.im : ℝ) ^ (-(Real.log rho / Real.log 2))) * ∫⁻ F, Phi F ∂P_eigenmeasure := by
{
  dsimp [P_eigenmeasure]
  rw [dif_pos h_rho]
  have h := (exists_weighted_covariance_measure h_rho).choose_spec
  exact ⟨h.1, h.2.2⟩
}

/-- Measure-level weighted affine covariance on `KClass` (Lemma 3.1). -/
lemma lemma_3_1_weighted_covariance_measure (h_rho : rho > 2) {z : ℂ} (hz : z ∈ H) :
    Measure.map (fun F : KClass => T_elem F z hz)
      (P_eigenmeasure.withDensity (fun F : KClass => ENNReal.ofReal (A_weight z F.F))) =
      ENNReal.ofReal ((z.im : ℝ) ^ (-(Real.log rho / Real.log 2))) • P_eigenmeasure := by
{
  ext s hs
  have hw_meas : Measurable (fun F : KClass => ENNReal.ofReal (A_weight z F.F)) :=
    (continuous_A_weight hz).measurable.ennreal_ofReal
  have hT_meas : Measurable (fun F : KClass => T_elem F z hz) := (continuous_T_elem hz).measurable
  have hPhi : Measurable (s.indicator (1 : KClass → ℝ≥0∞)) := measurable_const.indicator hs
  rw [← lintegral_indicator_one hs, lintegral_map hPhi hT_meas]
  change (∫⁻ F, ((s.indicator 1) ∘ (fun G : KClass => T_elem G z hz)) F
    ∂P_eigenmeasure.withDensity (fun F => ENNReal.ofReal (A_weight z F.F))) = _
  rw [lintegral_withDensity_eq_lintegral_mul P_eigenmeasure hw_meas (hPhi.comp hT_meas)]
  simp only [Pi.mul_apply, Function.comp_def, T_elem]
  rw [(lemma_3_1_weighted_covariance_lintegral h_rho).2 z hz (s.indicator 1) hPhi,
    lintegral_indicator_one hs, Measure.smul_apply, smul_eq_mul]
}

/-- Lemma 3.1 (Weighted affine covariance for Borel measurable real-valued functions). -/
lemma lemma_3_1_weighted_covariance_measurable (h_rho : rho > 2) :
    IsProbabilityMeasure P_eigenmeasure ∧
    ∀ (z : ℂ) (hz : z ∈ H) (Phi : KClass → ℝ),
      Measurable Phi →
      ∫ F, A_weight z F.F * Phi ⟨T z F.F, (T_KClass F z hz).1, (T_KClass F z hz).2.1, (T_KClass F z hz).2.2⟩ ∂P_eigenmeasure =
        (z.im : ℝ) ^ (-(Real.log rho / Real.log 2)) * ∫ F, Phi F ∂P_eigenmeasure := by
{
  refine ⟨(lemma_3_1_weighted_covariance h_rho).1, fun z hz Phi hPhi => ?_⟩
  have hm := congrArg (fun ν : Measure KClass => ∫ F, Phi F ∂ν)
    (lemma_3_1_weighted_covariance_measure h_rho hz)
  have hw_meas : Measurable (fun F : KClass => ENNReal.ofReal (A_weight z F.F)) :=
    (continuous_A_weight hz).measurable.ennreal_ofReal
  have hT_meas : Measurable (fun F : KClass => T_elem F z hz) := (continuous_T_elem hz).measurable
  rw [integral_map hT_meas.aemeasurable hPhi.aestronglyMeasurable,
    integral_withDensity_eq_integral_toReal_smul hw_meas
      (Eventually.of_forall (fun _ => ENNReal.ofReal_lt_top))] at hm
  have hw_nonneg (F : KClass) : 0 ≤ A_weight z F.F := sq_nonneg _
  have hc_nonneg : 0 ≤ (z.im : ℝ) ^ (-(Real.log rho / Real.log 2)) := Real.rpow_nonneg hz.le _
  simp only [ENNReal.toReal_ofReal (hw_nonneg _), smul_eq_mul] at hm
  rw [integral_smul_measure, ENNReal.toReal_ofReal hc_nonneg, smul_eq_mul] at hm
  exact hm
}

/-!
## 3.2 Moments of the logarithmic derivative (Lemma 3.2)

PAPER: Lemma 3.2 (Moments of the logarithmic derivative). Assume ρ > 2, and let P and β be
PAPER: as in Lemma 3.1. For z = x + iy ∈ H, define
PAPER: qF (z) = iy (Q'F(z) / QF(z)) = -iy (F''(z) / F'(z)) = aF(z) + i bF(z), (3.7)
PAPER: where aF, bF are real.
-/

-- We define q_F(z) as the normalized logarithmic derivative
def q (F : KClass) (z : ℂ) : ℂ :=
  I * (z.im : ℂ) * (deriv (Q F.F) z) / (Q F.F z)

-- Equivalently, via F'' / F'
lemma q_eq_F_deriv2 (F : KClass) (z : ℂ) (h1 : deriv F.F z ≠ 0) (h2 : DifferentiableAt ℂ (deriv F.F) z) :
    q F z = -I * (z.im : ℂ) * (deriv (deriv F.F) z) / (deriv F.F z) := by
{
  dsimp [q]
  have h_Q_def_2 : Q F.F = fun x => 1 / deriv F.F x := by
  {
    ext x
    dsimp [Q]
  }
  rw [h_Q_def_2]
  have h_deriv : deriv (fun x => 1 / deriv F.F x) z = - deriv (deriv F.F) z / (deriv F.F z)^2 := by
  {
    have h_rw : (fun x => 1 / deriv F.F x) = (fun x => (deriv F.F x)⁻¹) := by
    {
      ext x
      rw [one_div]
    }
    rw [h_rw]
    exact deriv_inv'' h2 h1
  }
  rw [h_deriv]
  field_simp
}

-- The real part a_F(z)
def a (F : KClass) (z : ℂ) : ℝ := (q F z).re

-- The imaginary part b_F(z)
def b (F : KClass) (z : ℂ) : ℝ := (q F z).im

lemma Q_at_I (F : KClass) : Q F.F I = 1 := by
{
  simp [Q, F.norm_deriv]
}

lemma norm_Q_at_I_sq (F : KClass) : ‖Q F.F I‖^2 = 1 := by
{
  rw [Q_at_I, norm_one, one_pow]
}

lemma norm_q_at_I_sq (F : KClass) : ‖q F I‖^2 = ‖deriv (Q F.F) I‖^2 := by
{
  dsimp [q]
  simp [Q_at_I]
}

lemma hasDerivAt_Q (F : KClass) {z : ℂ} (hz : z ∈ H) :
    HasDerivAt (Q F.F) (deriv (Q F.F) z) z := by
{
  have han : AnalyticAt ℂ F.F z := F.univalent.1.analyticOnNhd isOpen_H z hz
  have hd : deriv F.F z ≠ 0 := deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz
  have h_eq : Q F.F = fun u => (deriv F.F u)⁻¹ := by
  {
    ext u
    simp [Q]
  }
  rw [h_eq]
  exact (han.deriv.differentiableAt.inv hd).hasDerivAt
}

lemma analyticAt_Q (F : KClass) {z : ℂ} (hz : z ∈ H) :
    AnalyticAt ℂ (Q F.F) z := by
{
  have h_diff : DifferentiableOn ℂ (Q F.F) H := by
  {
    intro w hw
    exact (hasDerivAt_Q F hw).differentiableAt.differentiableWithinAt
  }
  exact h_diff.analyticOnNhd isOpen_H z hz
}

lemma hasDerivAt_deriv_Q (F : KClass) {z : ℂ} (hz : z ∈ H) :
    HasDerivAt (deriv (Q F.F)) (deriv (deriv (Q F.F)) z) z := by
{
  exact (analyticAt_Q F hz).deriv.differentiableAt.hasDerivAt
}

/-!
PAPER: On a compact neighborhood of any interior point, the functions QF , Q'F , Q''F are uniformly
PAPER: bounded over K, by Lemma 2.2. These bounds control the first two real derivatives of
PAPER: |QF|^2, and hence justify differentiation under expectation in (3.10).
PAPER: Holomorphicity and (3.7) give the pointwise identities
PAPER: ∂y|QF|^2 = 2aF/y |QF|^2, ∂x|QF|^2 = 2bF/y |QF|^2, ∆|QF|^2 = 4|Q'F|^2.
-/
-- Algebraic reduction of the pointwise identities using Cauchy-Riemann equations
lemma laplacian_cr_algebra (ux uy vx vy : ℝ) (hCR1 : ux = vy) (hCR2 : uy = -vx) :
    2 * (ux * ux + uy * uy + vx * vx + vy * vy) = 4 * (ux * ux + vx * vx) := by
{
  calc
    2 * (ux * ux + uy * uy + vx * vx + vy * vy)
      = 2 * (ux * ux + (-vx) * (-vx) + vx * vx + ux * ux) := by rw [hCR1, hCR2]
    _ = 4 * (ux * ux + vx * vx) := by ring
}

lemma dy_cr_algebra (u v ux uy vx vy y a normQsq : ℝ)
    (hCR1 : ux = vy) (hCR2 : uy = -vx)
    (hy : y ≠ 0) (hnorm : normQsq ≠ 0)
    (h_a : a = y * (v * ux - u * vx) / normQsq) :
    2 * (u * uy + v * vy) = 2 * a / y * normQsq := by
{
  calc
    2 * (u * uy + v * vy)
      = 2 * (u * (-vx) + v * ux) := by rw [hCR1, hCR2]
    _ = 2 * (v * ux - u * vx) := by ring
    _ = 2 * (a * normQsq / y) := by
    {
      rw [h_a]
      have hy_div : (y * (v * ux - u * vx) / normQsq) * normQsq / y = (v * ux - u * vx) := by
      {
        rw [div_mul_cancel₀ _ hnorm]
        calc (y * (v * ux - u * vx)) / y = (v * ux - u * vx) * y / y := by ring
        _ = (v * ux - u * vx) := by rw [mul_div_cancel_right₀ _ hy]
      }
      rw [hy_div]
    }
    _ = 2 * a / y * normQsq := by ring
}

lemma dx_cr_algebra (u v ux vx y b normQsq : ℝ)
    (hy : y ≠ 0) (hnorm : normQsq ≠ 0)
    (h_b : b = - y * (u * ux + v * vx) / normQsq) :
    2 * (u * ux + v * vx) = - 2 * b / y * normQsq := by
{
  calc
    2 * (u * ux + v * vx)
      = - 2 * (b * normQsq / y) := by
    {
      rw [h_b]
      have hy_div : (- y * (u * ux + v * vx) / normQsq) * normQsq / y = - (u * ux + v * vx) := by
      {
        rw [div_mul_cancel₀ _ hnorm]
        calc (- y * (u * ux + v * vx)) / y = (- (u * ux + v * vx)) * y / y := by ring
        _ = - (u * ux + v * vx) := by rw [mul_div_cancel_right₀ _ hy]
      }
      rw [hy_div]
      ring
    }
    _ = - 2 * b / y * normQsq := by ring
}

lemma hasDerivAt_line_x (x₀ y₀ : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) + y₀ • I) 1 x₀ := by
{
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x₀ := Complex.ofRealCLM.hasDerivAt
  simpa using h1.add_const (y₀ • I)
}

lemma hasDerivAt_line_y (x₀ y₀ : ℝ) :
    HasDerivAt (fun y : ℝ => (x₀ : ℂ) + y • I) I y₀ := by
{
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) * I) ((1 : ℂ) * I) y₀ :=
    Complex.ofRealCLM.hasDerivAt.mul_const I
  have h2 := h1.const_add (x₀ : ℂ)
  simpa [Complex.real_smul] using h2
}

lemma line_pt_eq (z : ℂ) : (z.re : ℂ) + z.im • I = z := by
{
  rw [Complex.real_smul]
  exact Complex.re_add_im z
}

lemma complex_line_deriv_y {g : ℂ → ℂ} {x₀ y₀ : ℝ} {d : ℂ}
    (hg : HasDerivAt g d ((x₀ : ℂ) + y₀ • I)) :
    HasDerivAt (fun y : ℝ => g ((x₀ : ℂ) + y • I)) (d * I) y₀ := by
{
  convert HasDerivAt.comp (𝕜 := ℝ) y₀ hg (hasDerivAt_line_y x₀ y₀) using 1 <;> rfl
}

lemma complex_line_deriv_x {g : ℂ → ℂ} {x₀ y₀ : ℝ} {d : ℂ}
    (hg : HasDerivAt g d ((x₀ : ℂ) + y₀ • I)) :
    HasDerivAt (fun x : ℝ => g ((x : ℂ) + y₀ • I)) (d * 1) x₀ := by
{
  convert HasDerivAt.comp (𝕜 := ℝ) x₀ hg (hasDerivAt_line_x x₀ y₀) using 1 <;> rfl
}

lemma hasDerivAt_Q_line_y (F : KClass) (z : ℂ) (hz : z ∈ H) :
    HasDerivAt (fun y : ℝ => Q F.F (z.re + y • I)) (deriv (Q F.F) z * I) z.im := by
{
  have hQ : HasDerivAt (Q F.F) (deriv (Q F.F) z) ((z.re : ℂ) + z.im • I) := by
  {
    rw [line_pt_eq z]
    exact hasDerivAt_Q F hz
  }
  exact complex_line_deriv_y hQ
}

lemma hasDerivAt_Q_line_x (F : KClass) (z : ℂ) (hz : z ∈ H) :
    HasDerivAt (fun x : ℝ => Q F.F (x + z.im • I)) (deriv (Q F.F) z * 1) z.re := by
{
  have hQ : HasDerivAt (Q F.F) (deriv (Q F.F) z) ((z.re : ℂ) + z.im • I) := by
  {
    rw [line_pt_eq z]
    exact hasDerivAt_Q F hz
  }
  exact complex_line_deriv_x hQ
}

lemma inner_Q_deriv_I_eq (F : KClass) (z : ℂ) (hz : z ∈ H) :
    2 * inner ℝ (Q F.F z) (deriv (Q F.F) z * I) = 2 * a F z / z.im * ‖Q F.F z‖^2 := by
{
  dsimp [a, q]
  have hy : z.im ≠ 0 := ne_of_gt hz
  have hQ_ne : Q F.F z ≠ 0 := one_div_ne_zero (deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz)
  rw [← Complex.normSq_eq_norm_sq]
  have hnorm : Complex.normSq (Q F.F z) ≠ 0 := by
  {
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hQ_ne)
  }
  change 2 * (deriv (Q F.F) z * I * conj (Q F.F z)).re = _
  simp only [Complex.div_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  field_simp
  ring
}

lemma inner_Q_deriv_one_eq (F : KClass) (z : ℂ) (hz : z ∈ H) :
    2 * inner ℝ (Q F.F z) (deriv (Q F.F) z * 1) = 2 * b F z / z.im * ‖Q F.F z‖^2 := by
{
  dsimp [b, q]
  have hy : z.im ≠ 0 := ne_of_gt hz
  have hQ_ne : Q F.F z ≠ 0 := one_div_ne_zero (deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz)
  rw [← Complex.normSq_eq_norm_sq]
  have hnorm : Complex.normSq (Q F.F z) ≠ 0 := by
  {
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hQ_ne)
  }
  change 2 * (deriv (Q F.F) z * 1 * conj (Q F.F z)).re = _
  simp only [Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_one, Complex.conj_re, Complex.conj_im]
  field_simp
  ring
}

-- Pointwise identities for |Q_F|^2
lemma dy_norm_Q_sq (F : KClass) (z : ℂ) (hz : z ∈ H) :
    deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2) z.im = 2 * a F z / z.im * ‖Q F.F z‖^2 := by
{
  have hd := (hasDerivAt_Q_line_y F z hz).norm_sq
  rw [line_pt_eq z] at hd
  rw [hd.deriv, inner_Q_deriv_I_eq F z hz]
}

lemma dx_norm_Q_sq (F : KClass) (z : ℂ) (hz : z ∈ H) :
    deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2) z.re = 2 * b F z / z.im * ‖Q F.F z‖^2 := by
{
  have hd := (hasDerivAt_Q_line_x F z hz).norm_sq
  rw [line_pt_eq z] at hd
  rw [hd.deriv, inner_Q_deriv_one_eq F z hz]
}

lemma second_deriv_norm_Q_sq_x (F : KClass) (z : ℂ) (hz : z ∈ H) :
    deriv (deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2)) z.re =
    2 * (inner ℝ (deriv (Q F.F) z * 1) (deriv (Q F.F) z * 1) +
         inner ℝ (Q F.F z) ((deriv (deriv (Q F.F)) z * 1) * 1)) := by
{
  have h_eq : deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2) =
      fun x : ℝ => 2 * inner ℝ (Q F.F (x + z.im • I)) (deriv (Q F.F) (x + z.im • I) * 1) := by
  {
    ext x
    let w : ℂ := (x : ℂ) + z.im • I
    have hw : w ∈ H := by dsimp [H, w]; simp; exact hz
    have hre : w.re = x := by simp [w, Complex.real_smul]
    have him : w.im = z.im := by simp [w, Complex.real_smul]
    have hd := (hasDerivAt_Q_line_x F w hw).norm_sq
    rw [line_pt_eq w] at hd
    simpa [w, hre, him] using hd.deriv
  }
  rw [h_eq]
  have hQ1 := hasDerivAt_Q_line_x F z hz
  have hQ2 : HasDerivAt (fun x : ℝ => deriv (Q F.F) (x + z.im • I)) (deriv (deriv (Q F.F)) z * 1) z.re := by
  {
    have hD : HasDerivAt (deriv (Q F.F)) (deriv (deriv (Q F.F)) z) ((z.re : ℂ) + z.im • I) := by
    {
      rw [line_pt_eq z]
      exact hasDerivAt_deriv_Q F hz
    }
    exact complex_line_deriv_x hD
  }
  have hd2 := ((hQ1.inner ℝ (hQ2.mul_const 1)).const_mul 2)
  rw [line_pt_eq z] at hd2
  rw [hd2.deriv, add_comm]
}

lemma second_deriv_norm_Q_sq_y (F : KClass) (z : ℂ) (hz : z ∈ H) :
    deriv (deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2)) z.im =
    2 * (inner ℝ (deriv (Q F.F) z * I) (deriv (Q F.F) z * I) +
         inner ℝ (Q F.F z) ((deriv (deriv (Q F.F)) z * I) * I)) := by
{
  have h_eq : deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2) =ᶠ[𝓝 z.im]
      fun y : ℝ => 2 * inner ℝ (Q F.F (z.re + y • I)) (deriv (Q F.F) (z.re + y • I) * I) := by
  {
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    let w : ℂ := (z.re : ℂ) + y • I
    have hw : w ∈ H := by dsimp [H, w]; simp; exact hy
    have hre : w.re = z.re := by simp [w, Complex.real_smul]
    have him : w.im = y := by simp [w, Complex.real_smul]
    have hd := (hasDerivAt_Q_line_y F w hw).norm_sq
    rw [line_pt_eq w] at hd
    simpa [w, hre, him] using hd.deriv
  }
  have hQ1 := hasDerivAt_Q_line_y F z hz
  have hQ2 : HasDerivAt (fun y : ℝ => deriv (Q F.F) (z.re + y • I)) (deriv (deriv (Q F.F)) z * I) z.im := by
  {
    have hD : HasDerivAt (deriv (Q F.F)) (deriv (deriv (Q F.F)) z) ((z.re : ℂ) + z.im • I) := by
    {
      rw [line_pt_eq z]
      exact hasDerivAt_deriv_Q F hz
    }
    exact complex_line_deriv_y hD
  }
  have hd2 := ((hQ1.inner ℝ (hQ2.mul_const I)).const_mul 2).congr_of_eventuallyEq h_eq
  rw [line_pt_eq z] at hd2
  rw [hd2.deriv, add_comm]
}

lemma laplacian_norm_Q_sq (F : KClass) (z : ℂ) (hz : z ∈ H) :
    deriv (deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2)) z.re +
    deriv (deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2)) z.im =
    4 * ‖deriv (Q F.F) z‖^2 := by
{
  rw [second_deriv_norm_Q_sq_x F z hz, second_deriv_norm_Q_sq_y F z hz]
  simp only [mul_one]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  simp only [Complex.norm_mul, Complex.norm_I, mul_one]
  have he : (deriv (deriv (Q F.F)) z * I) * I = - deriv (deriv (Q F.F)) z := by
  {
    rw [mul_assoc, Complex.I_mul_I, mul_neg_one]
  }
  rw [he, inner_neg_right]
  ring
}

/-!
PAPER: They also satisfy
PAPER: qTzF (w) = qF (z · w), z, w ∈ H. (3.9)
-/
-- Covariance of q under the affine transfer operator
lemma q_T_eq (F : KClass) (z w : ℂ) (hz : z ∈ H) (hw : w ∈ H) :
    q ⟨T z F.F, (T_KClass F z hz).1, (T_KClass F z hz).2.1, (T_KClass F z hz).2.2⟩ w = q F (aff z w) := by
{
  dsimp [q]
  have hz_im : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have h_im_aff : (aff z w).im = z.im * w.im := by dsimp [aff]; simp
  have hF_aff : DifferentiableAt ℂ F.F (aff z w) :=
    (F.univalent.1 (aff z w) (aff_mem_H hz hw)).differentiableAt (isOpen_H.mem_nhds (aff_mem_H hz hw))
  have h_Q_val : Q (T z F.F) w = Q F.F (aff z w) / Q F.F z := lemma_2_3_Q F.F z w hF_aff hz_im
  have heq : Q (T z F.F) =ᶠ[𝓝 w] (fun u => Q F.F (aff z u) / Q F.F z) := by
  {
    filter_upwards [isOpen_H.mem_nhds hw] with u hu
    have hF_u : DifferentiableAt ℂ F.F (aff z u) :=
      (F.univalent.1 (aff z u) (aff_mem_H hz hu)).differentiableAt (isOpen_H.mem_nhds (aff_mem_H hz hu))
    exact lemma_2_3_Q F.F z u hF_u hz_im
  }
  have hd_aff : HasDerivAt (aff z) (z.im : ℂ) w := by
  {
    convert (hasDerivAt_const w (z.re : ℂ)).add ((hasDerivAt_id w).const_mul (z.im : ℂ)) using 1 <;>
      first | rfl | simp
  }
  have h_deriv_Q : deriv (Q (T z F.F)) w = (deriv (Q F.F) (aff z w) * z.im) / Q F.F z :=
    ((((hasDerivAt_Q F (aff_mem_H hz hw)).comp w hd_aff).div_const (Q F.F z)).congr_of_eventuallyEq heq).deriv
  rw [h_deriv_Q, h_Q_val, h_im_aff]
  push_cast
  have h_Q_z_ne_zero : Q F.F z ≠ 0 :=
    one_div_ne_zero (deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz)
  field_simp
}

/-!
PAPER: The variables qF (i) are bounded on K, and
PAPER: EaF(i) = -β / 2, EbF(i) = 0, E|qF(i)|^2 = β(β + 1) / 4. (3.8)
-/
lemma continuous_Q_eval {w : ℂ} (hw : w ∈ H) : Continuous (fun F : KClass => Q F.F w) := by
{
  simpa only [iteratedDeriv_zero] using continuous_iteratedDeriv_Q_eval 0 hw
}

lemma continuous_deriv_Q_eval {w : ℂ} (hw : w ∈ H) : Continuous (fun F : KClass => deriv (Q F.F) w) := by
{
  simpa only [iteratedDeriv_one] using continuous_iteratedDeriv_Q_eval 1 hw
}

lemma continuous_deriv2_Q_eval {w : ℂ} (hw : w ∈ H) :
    Continuous (fun F : KClass => deriv (deriv (Q F.F)) w) := by
{
  have h2 : ∀ f : ℂ → ℂ, iteratedDeriv 2 f = deriv (deriv f) := by
  {
    intro f
    rw [iteratedDeriv_succ, iteratedDeriv_one]
  }
  simpa only [h2] using continuous_iteratedDeriv_Q_eval 2 hw
}

def Q_ball_bound (z : ℂ) : ℝ :=
  (((‖z‖ + z.im / 2)^2 + (3 * z.im / 2 + 1)^2)^2) / (z.im / 2)

def Q_deriv_bound (z : ℂ) : ℝ :=
  Q_ball_bound z / (z.im / 4)

def Q_deriv2_bound (z : ℂ) : ℝ :=
  2 * Q_ball_bound z / (z.im / 4)^2

lemma closedBall_half_im_bounds {z w : ℂ} (hw : w ∈ Metric.closedBall z (z.im / 2)) :
    z.im / 2 ≤ w.im ∧ w.im ≤ 3 * z.im / 2 ∧ |w.re| ≤ ‖z‖ + z.im / 2 := by
{
  have hwz : ‖w - z‖ ≤ z.im / 2 := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hw
  have him : |w.im - z.im| ≤ z.im / 2 := by
  {
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (w - z)).trans hwz
  }
  obtain ⟨h1, h2⟩ := abs_le.mp him
  refine ⟨by linarith, by linarith, ?_⟩
  have hnorm : ‖w‖ ≤ ‖z‖ + z.im / 2 := by
  {
    calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
      _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + z.im / 2 := by linarith
  }
  exact (Complex.abs_re_le_norm w).trans hnorm
}

lemma norm_Q_le_on_closedBall (F : KClass) {z : ℂ} (hz : z ∈ H)
    {w : ℂ} (hw : w ∈ Metric.closedBall z (z.im / 2)) :
    ‖Q F.F w‖ ≤ Q_ball_bound z := by
{
  have hy : 0 < z.im := hz
  obtain ⟨hw1, hw2, hw3⟩ := closedBall_half_im_bounds hw
  have hwH : w ∈ H := by dsimp [H]; linarith
  have hgen := norm_Q_le_general F hwH
  have hre2 : w.re^2 ≤ (‖z‖ + z.im / 2)^2 := by
  {
    have hsq := (sq_le_sq₀ (abs_nonneg w.re) (by positivity)).mpr hw3
    nlinarith [sq_abs w.re]
  }
  have him2 : (w.im + 1)^2 ≤ (3 * z.im / 2 + 1)^2 := by nlinarith
  have hD2 : (w.re^2 + (w.im + 1)^2)^2 ≤ ((‖z‖ + z.im / 2)^2 + (3 * z.im / 2 + 1)^2)^2 :=
    sq_le_sq₀ (by positivity) (by positivity) |>.mpr (by linarith)
  exact hgen.trans (div_le_div₀ (by positivity) hD2 (by positivity) hw1)
}

lemma norm_iteratedDeriv_Q_le_on_closedBall (F : KClass) (n : ℕ) {z : ℂ} (hz : z ∈ H)
    {w : ℂ} (hw : w ∈ Metric.closedBall z (z.im / 4)) :
    ‖iteratedDeriv n (Q F.F) w‖ ≤ n.factorial * Q_ball_bound z / (z.im / 4) ^ n := by
{
  have hy : 0 < z.im := hz
  have hr : 0 < z.im / 4 := by positivity
  have hsub : Metric.closedBall w (z.im / 4) ⊆ Metric.closedBall z (z.im / 2) := by
  {
    intro u hu
    rw [Metric.mem_closedBall] at hu hw ⊢
    calc dist u z ≤ dist u w + dist w z := dist_triangle u w z
      _ ≤ z.im / 4 + z.im / 4 := add_le_add hu hw
      _ = z.im / 2 := by ring
  }
  have hd : DifferentiableOn ℂ (Q F.F) (Metric.closedBall w (z.im / 4)) := by
  {
    intro u hu
    have huH : u ∈ H := by
    {
      dsimp [H]
      linarith [(closedBall_half_im_bounds (hsub hu)).1]
    }
    exact (hasDerivAt_Q F huH).differentiableAt.differentiableWithinAt
  }
  have hdf : DiffContOnCl ℂ (Q F.F) (Metric.ball w (z.im / 4)) := by
  {
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball w hr.ne']
    exact hd
  }
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hdf
    (fun u hu => norm_Q_le_on_closedBall F hz (hsub (Metric.sphere_subset_closedBall hu)))
}

lemma norm_deriv_Q_le_on_closedBall (F : KClass) {z : ℂ} (hz : z ∈ H)
    {w : ℂ} (hw : w ∈ Metric.closedBall z (z.im / 4)) :
    ‖deriv (Q F.F) w‖ ≤ Q_deriv_bound z := by
{
  have h := norm_iteratedDeriv_Q_le_on_closedBall F 1 hz hw
  simpa [Q_deriv_bound] using h
}

lemma norm_deriv2_Q_le_on_closedBall (F : KClass) {z : ℂ} (hz : z ∈ H)
    {w : ℂ} (hw : w ∈ Metric.closedBall z (z.im / 4)) :
    ‖deriv (deriv (Q F.F)) w‖ ≤ Q_deriv2_bound z := by
{
  have h := norm_iteratedDeriv_Q_le_on_closedBall F 2 hz hw
  have hi2 : iteratedDeriv 2 (Q F.F) w = deriv (deriv (Q F.F)) w := by
  {
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  }
  rw [hi2, Nat.factorial_two, Nat.cast_ofNat] at h
  exact h
}

/-- Uniform bound on `‖q F I‖` over the compact class K. -/
theorem q_bounded_on_KClass : ∃ C : ℝ, ∀ F : KClass, ‖q F I‖ ≤ C := by
{
  have hzI : I ∈ H := by dsimp [H]; simp
  refine ⟨Q_deriv_bound I, fun F => ?_⟩
  have hq : ‖q F I‖ = ‖deriv (Q F.F) I‖ := by
  {
    dsimp [q]
    simp [Q_at_I]
  }
  rw [hq]
  exact norm_deriv_Q_le_on_closedBall F hzI (Metric.mem_closedBall_self (by dsimp; norm_num))
}

def normFirstQ (v w : ℂ) (F : KClass) : ℝ :=
  2 * inner ℝ (Q F.F w) (deriv (Q F.F) w * v)

def normSecondQ (v w : ℂ) (F : KClass) : ℝ :=
  2 * (inner ℝ (deriv (Q F.F) w * v) (deriv (Q F.F) w * v) +
       inner ℝ (Q F.F w) ((deriv (deriv (Q F.F)) w * v) * v))

lemma continuous_norm_Q_sq {w : ℂ} (hw : w ∈ H) : Continuous (fun F : KClass => ‖Q F.F w‖^2) := by
{
  have hQ := continuous_Q_eval hw
  fun_prop
}

lemma continuous_normFirstQ (v : ℂ) {w : ℂ} (hw : w ∈ H) : Continuous (normFirstQ v w) := by
{
  unfold normFirstQ
  have hQ := continuous_Q_eval hw
  have hdQ := continuous_deriv_Q_eval hw
  fun_prop
}

lemma continuous_normSecondQ (v : ℂ) {w : ℂ} (hw : w ∈ H) : Continuous (normSecondQ v w) := by
{
  unfold normSecondQ
  have hQ := continuous_Q_eval hw
  have hdQ := continuous_deriv_Q_eval hw
  have hd2Q := continuous_deriv2_Q_eval hw
  fun_prop
}

lemma norm_normFirstQ_le (F : KClass) {z v w : ℂ} (hz : z ∈ H) (hv : ‖v‖ = 1)
    (hw : w ∈ Metric.closedBall z (z.im / 4)) :
    ‖normFirstQ v w F‖ ≤ 2 * Q_ball_bound z * Q_deriv_bound z := by
{
  have hw2 : w ∈ Metric.closedBall z (z.im / 2) :=
    Metric.closedBall_subset_closedBall (by linarith [show 0 < z.im from hz]) hw
  have h0 := norm_Q_le_on_closedBall F hz hw2
  have h1 := norm_deriv_Q_le_on_closedBall F hz hw
  have hB0 : 0 ≤ Q_ball_bound z := (norm_nonneg _).trans h0
  unfold normFirstQ
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_assoc]
  gcongr
  calc |inner ℝ (Q F.F w) (deriv (Q F.F) w * v)|
      ≤ ‖Q F.F w‖ * ‖deriv (Q F.F) w * v‖ := abs_real_inner_le_norm _ _
    _ = ‖Q F.F w‖ * ‖deriv (Q F.F) w‖ := by rw [norm_mul, hv, mul_one]
    _ ≤ Q_ball_bound z * Q_deriv_bound z := mul_le_mul h0 h1 (norm_nonneg _) hB0
}

lemma norm_normSecondQ_le (F : KClass) {z v w : ℂ} (hz : z ∈ H) (hv : ‖v‖ = 1)
    (hw : w ∈ Metric.closedBall z (z.im / 4)) :
    ‖normSecondQ v w F‖ ≤
      2 * (Q_deriv_bound z ^ 2 + Q_ball_bound z * Q_deriv2_bound z) := by
{
  have hw2 : w ∈ Metric.closedBall z (z.im / 2) :=
    Metric.closedBall_subset_closedBall (by linarith [show 0 < z.im from hz]) hw
  have h0 := norm_Q_le_on_closedBall F hz hw2
  have h1 := norm_deriv_Q_le_on_closedBall F hz hw
  have h2 := norm_deriv2_Q_le_on_closedBall F hz hw
  have hB0 : 0 ≤ Q_ball_bound z := (norm_nonneg _).trans h0
  have hB1 : 0 ≤ Q_deriv_bound z := (norm_nonneg _).trans h1
  unfold normSecondQ
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  gcongr
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · calc |inner ℝ (deriv (Q F.F) w * v) (deriv (Q F.F) w * v)|
        ≤ ‖deriv (Q F.F) w * v‖ * ‖deriv (Q F.F) w * v‖ := abs_real_inner_le_norm _ _
      _ = ‖deriv (Q F.F) w‖ ^ 2 := by rw [norm_mul, hv, mul_one, sq]
      _ ≤ Q_deriv_bound z ^ 2 := sq_le_sq₀ (norm_nonneg _) hB1 |>.mpr h1
  · calc |inner ℝ (Q F.F w) ((deriv (deriv (Q F.F)) w * v) * v)|
        ≤ ‖Q F.F w‖ * ‖(deriv (deriv (Q F.F)) w * v) * v‖ := abs_real_inner_le_norm _ _
      _ = ‖Q F.F w‖ * ‖deriv (deriv (Q F.F)) w‖ := by rw [norm_mul, norm_mul, hv, mul_one, mul_one]
      _ ≤ Q_ball_bound z * Q_deriv2_bound z := mul_le_mul h0 h2 (norm_nonneg _) hB0
}

lemma hasDerivAt_norm_Q_sq_along (F : KClass) {γ : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hγ : HasDerivAt γ v t) (hH : γ t ∈ H) :
    HasDerivAt (fun s => ‖Q F.F (γ s)‖^2) (normFirstQ v (γ t) F) t := by
{
  have hd : HasDerivAt (fun s => Q F.F (γ s)) (deriv (Q F.F) (γ t) * v) t := by
  {
    convert HasDerivAt.comp (𝕜 := ℝ) t (hasDerivAt_Q F hH) hγ using 1 <;> rfl
  }
  exact hd.norm_sq
}

lemma hasDerivAt_normFirstQ_along (F : KClass) {γ : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hγ : HasDerivAt γ v t) (hH : γ t ∈ H) :
    HasDerivAt (fun s => normFirstQ v (γ s) F) (normSecondQ v (γ t) F) t := by
{
  have hd1 : HasDerivAt (fun s => Q F.F (γ s)) (deriv (Q F.F) (γ t) * v) t := by
  {
    convert HasDerivAt.comp (𝕜 := ℝ) t (hasDerivAt_Q F hH) hγ using 1 <;> rfl
  }
  have hd2 : HasDerivAt (fun s => deriv (Q F.F) (γ s)) (deriv (deriv (Q F.F)) (γ t) * v) t := by
  {
    convert HasDerivAt.comp (𝕜 := ℝ) t (hasDerivAt_deriv_Q F hH) hγ using 1 <;> rfl
  }
  simpa only [normFirstQ, normSecondQ, add_comm] using
    ((hd1.inner ℝ (hd2.mul_const v)).const_mul 2)
}

lemma hasDerivAt_integral_of_uniform_bound (P : Measure KClass) [IsFiniteMeasure P]
    (Φ Φ' : ℝ → KClass → ℝ) {U : Set ℝ} {t C₀ C₁ : ℝ} (hU : U ∈ 𝓝 t) (ht : t ∈ U)
    (hΦc : ∀ s ∈ U, Continuous (Φ s))
    (hΦ'c : Continuous (Φ' t))
    (hb0 : ∀ F, ‖Φ t F‖ ≤ C₀)
    (hb1 : ∀ F, ∀ s ∈ U, ‖Φ' s F‖ ≤ C₁)
    (hd : ∀ F, ∀ s ∈ U, HasDerivAt (fun u => Φ u F) (Φ' s F) s) :
    Integrable (Φ' t) P ∧
      HasDerivAt (fun s => ∫ F, Φ s F ∂P) (∫ F, Φ' t F ∂P) t := by
{
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le hU
    ?_ ?_ hΦ'c.aestronglyMeasurable
    (Eventually.of_forall hb1) (integrable_const C₁) (Eventually.of_forall hd)
  · filter_upwards [hU] with s hs
    exact (hΦc s hs).aestronglyMeasurable
  · exact (integrable_const C₀).mono' (hΦc t ht).aestronglyMeasurable
      (Eventually.of_forall hb0)
}

lemma closedBall_quarter_subset_H {z : ℂ} (hz : z ∈ H)
    {w : ℂ} (hw : w ∈ Metric.closedBall z (z.im / 4)) : w ∈ H := by
{
  have hw2 : w ∈ Metric.closedBall z (z.im / 2) :=
    Metric.closedBall_subset_closedBall (by linarith [show 0 < z.im from hz]) hw
  dsimp [H]
  linarith [show 0 < z.im from hz, (closedBall_half_im_bounds hw2).1]
}

lemma hasDerivAt_integral_along_line (P : Measure KClass) [IsFiniteMeasure P]
    {z v : ℂ} (hz : z ∈ H) (hv : ‖v‖ = 1) {γ : ℝ → ℂ} {t₀ t : ℝ}
    (hγ : ∀ s, HasDerivAt γ v s)
    (hball : ∀ s ∈ Metric.ball t₀ (z.im / 4), γ s ∈ Metric.closedBall z (z.im / 4))
    (ht : t ∈ Metric.ball t₀ (z.im / 4)) :
    HasDerivAt (fun s => ∫ F, ‖Q F.F (γ s)‖^2 ∂P)
      (∫ F, normFirstQ v (γ t) F ∂P) t := by
{
  have hU : Metric.ball t₀ (z.im / 4) ∈ 𝓝 t := Metric.isOpen_ball.mem_nhds ht
  have hw2 : γ t ∈ Metric.closedBall z (z.im / 2) :=
    Metric.closedBall_subset_closedBall (by linarith [show 0 < z.im from hz]) (hball t ht)
  refine (hasDerivAt_integral_of_uniform_bound P
    (fun s F => ‖Q F.F (γ s)‖^2) (fun s F => normFirstQ v (γ s) F)
    (C₀ := Q_ball_bound z ^ 2) hU ht
    (fun s hs => continuous_norm_Q_sq (closedBall_quarter_subset_H hz (hball s hs)))
    (continuous_normFirstQ v (closedBall_quarter_subset_H hz (hball t ht)))
    (fun F => ?_) (fun F s hs => norm_normFirstQ_le F hz hv (hball s hs))
    (fun F s hs => hasDerivAt_norm_Q_sq_along F (hγ s) (closedBall_quarter_subset_H hz (hball s hs)))).2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h0 := norm_Q_le_on_closedBall F hz hw2
  exact sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans h0) |>.mpr h0
}

lemma deriv2_integral_along_line (P : Measure KClass) [IsFiniteMeasure P]
    {z v : ℂ} (hz : z ∈ H) (hv : ‖v‖ = 1) {γ : ℝ → ℂ} {t₀ : ℝ}
    (hγ : ∀ s, HasDerivAt γ v s)
    (hball : ∀ s ∈ Metric.ball t₀ (z.im / 4), γ s ∈ Metric.closedBall z (z.im / 4)) :
    Integrable (fun F => deriv (deriv (fun s => ‖Q F.F (γ s)‖^2)) t₀) P ∧
      deriv (deriv (fun s => ∫ F, ‖Q F.F (γ s)‖^2 ∂P)) t₀ =
        ∫ F, deriv (deriv (fun s => ‖Q F.F (γ s)‖^2)) t₀ ∂P := by
{
  have hr : 0 < z.im / 4 := by linarith [show 0 < z.im from hz]
  have ht0 : t₀ ∈ Metric.ball t₀ (z.im / 4) := Metric.mem_ball_self hr
  have hU : Metric.ball t₀ (z.im / 4) ∈ 𝓝 t₀ := Metric.isOpen_ball.mem_nhds ht0
  have hstep2 := hasDerivAt_integral_of_uniform_bound P
    (fun s F => normFirstQ v (γ s) F) (fun s F => normSecondQ v (γ s) F) hU ht0
    (fun s hs => continuous_normFirstQ v (closedBall_quarter_subset_H hz (hball s hs)))
    (continuous_normSecondQ v (closedBall_quarter_subset_H hz (hball t₀ ht0)))
    (fun F => norm_normFirstQ_le F hz hv (hball t₀ ht0))
    (fun F s hs => norm_normSecondQ_le F hz hv (hball s hs))
    (fun F s hs => hasDerivAt_normFirstQ_along F (hγ s) (closedBall_quarter_subset_H hz (hball s hs)))
  have hev_int : deriv (fun s => ∫ F, ‖Q F.F (γ s)‖^2 ∂P) =ᶠ[𝓝 t₀]
      fun s => ∫ F, normFirstQ v (γ s) F ∂P := by
  {
    filter_upwards [hU] with s hs
    exact (hasDerivAt_integral_along_line P hz hv hγ hball hs).deriv
  }
  have hpt (F : KClass) : deriv (deriv (fun s => ‖Q F.F (γ s)‖^2)) t₀ = normSecondQ v (γ t₀) F := by
  {
    have hev : deriv (fun s => ‖Q F.F (γ s)‖^2) =ᶠ[𝓝 t₀] fun s => normFirstQ v (γ s) F := by
    {
      filter_upwards [hU] with s hs
      exact (hasDerivAt_norm_Q_sq_along F (hγ s) (closedBall_quarter_subset_H hz (hball s hs))).deriv
    }
    rw [hev.deriv_eq]
    exact (hasDerivAt_normFirstQ_along F (hγ t₀) (closedBall_quarter_subset_H hz (hball t₀ ht0))).deriv
  }
  simp_rw [hpt]
  exact ⟨hstep2.1, hev_int.deriv_eq.trans hstep2.2.deriv⟩
}

lemma line_y_mem_closedBall {z : ℂ} {y : ℝ} (hy : y ∈ Metric.ball z.im (z.im / 4)) :
    (z.re : ℂ) + y • I ∈ Metric.closedBall z (z.im / 4) := by
{
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hdiff : ((z.re : ℂ) + y • I) - z = ((y - z.im) : ℂ) * I := by
  {
    have hz_eq := line_pt_eq z
    simp only [Complex.real_smul] at hz_eq ⊢
    linear_combination hz_eq
  }
  rw [hdiff, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact (Metric.mem_ball.mp hy).le
}

lemma line_x_mem_closedBall {z : ℂ} {x : ℝ} (hx : x ∈ Metric.ball z.re (z.im / 4)) :
    (x : ℂ) + z.im • I ∈ Metric.closedBall z (z.im / 4) := by
{
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hdiff : ((x : ℂ) + z.im • I) - z = ((x - z.re) : ℂ) := by
  {
    have hz_eq := line_pt_eq z
    simp only [Complex.real_smul] at hz_eq ⊢
    linear_combination hz_eq
  }
  rw [hdiff, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact (Metric.mem_ball.mp hx).le
}

/-- Differentiation under the integral sign on the compact family K. -/
theorem deriv_integral_y (P : Measure KClass) [IsFiniteMeasure P] (z : ℂ) (hz : z ∈ H) :
    deriv (fun y : ℝ => ∫ F, ‖Q F.F (z.re + y • I)‖^2 ∂P) z.im =
    ∫ F, deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2) z.im ∂P := by
{
  have hr : 0 < z.im / 4 := by linarith [show 0 < z.im from hz]
  have hd := hasDerivAt_integral_along_line P hz Complex.norm_I (hasDerivAt_line_y z.re)
    (fun _ hy => line_y_mem_closedBall hy) (Metric.mem_ball_self hr)
  rw [hd.deriv]
  congr 1
  ext F
  have hpt := (hasDerivAt_Q_line_y F z hz).norm_sq
  simpa [normFirstQ, line_pt_eq z] using hpt.deriv.symm
}

/-- Differentiation under the integral sign wrt x on K. -/
theorem deriv_integral_x (P : Measure KClass) [IsFiniteMeasure P] (z : ℂ) (hz : z ∈ H) :
    deriv (fun x : ℝ => ∫ F, ‖Q F.F (x + z.im • I)‖^2 ∂P) z.re =
    ∫ F, deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2) z.re ∂P := by
{
  have hr : 0 < z.im / 4 := by linarith [show 0 < z.im from hz]
  have hd := hasDerivAt_integral_along_line P hz norm_one (fun x => hasDerivAt_line_x x z.im)
    (fun _ hx => line_x_mem_closedBall hx) (Metric.mem_ball_self hr)
  rw [hd.deriv]
  congr 1
  ext F
  have hpt := (hasDerivAt_Q_line_x F z hz).norm_sq
  simpa [normFirstQ, line_pt_eq z] using hpt.deriv.symm
}

/-- Second derivative under the integral sign on K. -/
theorem deriv2_integral_laplacian (P : Measure KClass) [IsFiniteMeasure P] (z : ℂ) (hz : z ∈ H) :
    deriv (deriv (fun x : ℝ => ∫ F, ‖Q F.F (x + z.im • I)‖^2 ∂P)) z.re +
    deriv (deriv (fun y : ℝ => ∫ F, ‖Q F.F (z.re + y • I)‖^2 ∂P)) z.im =
    ∫ F, (deriv (deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2)) z.re +
          deriv (deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2)) z.im) ∂P := by
{
  have hx := deriv2_integral_along_line P hz norm_one (fun x => hasDerivAt_line_x x z.im)
    (fun _ h => line_x_mem_closedBall h)
  have hy := deriv2_integral_along_line P hz Complex.norm_I (hasDerivAt_line_y z.re)
    (fun _ h => line_y_mem_closedBall h)
  rw [hx.2, hy.2, ← integral_add hx.1 hy.1]
}

/-!
PAPER: Proof. Taking Φ = 1 in (3.1) gives
PAPER: E|QF (x + iy)|^2 = y^{-β}. (3.10)
-/
-- Expected value of |Q_F(z)|^2 over KClass (Equation 3.10)
lemma E_norm_Q_sq (P : Measure KClass) [IsProbabilityMeasure P] (beta : ℝ) (z : ℂ) (hz : z ∈ H)
    (h_P_eigen : ∀ (w : ℂ) (hw : w ∈ H) (Phi : KClass → ℝ),
      Continuous Phi →
      ∫ F, A_weight w F.F * Phi ⟨T w F.F, (T_KClass F w hw).1, (T_KClass F w hw).2.1, (T_KClass F w hw).2.2⟩ ∂P =
        (w.im : ℝ) ^ (-beta) * ∫ F, Phi F ∂P) :
    ∫ F, ‖Q F.F z‖^2 ∂P = (z.im : ℝ) ^ (-beta) := by
{
  have h1 := h_P_eigen z hz (fun _ => 1) continuous_const
  simp only [A_weight, mul_one, integral_const, smul_eq_mul, probReal_univ] at h1
  exact h1
}

lemma E_a_eq (P : Measure KClass) [IsFiniteMeasure P] (beta : ℝ)
    (h_P_eigen : ∀ z ∈ H, ∫ F, ‖Q F.F z‖^2 ∂P = (z.im : ℝ) ^ (-beta)) :
    ∫ F, a F I ∂P = -beta / 2 := by
{
  have hz_I : I ∈ H := by dsimp [H]; simp
  have h_ev : (fun y : ℝ => ∫ F, ‖Q F.F ((0 : ℝ) + y • I)‖^2 ∂P) =ᶠ[𝓝 1] (fun y : ℝ => y ^ (-beta)) := by
  {
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1)] with y hy
    have hyH : ((0 : ℝ) : ℂ) + y • I ∈ H := by dsimp [H]; simp; exact hy
    have h_im : (((0 : ℝ) : ℂ) + y • I).im = y := by simp [Complex.real_smul]
    rw [h_P_eigen _ hyH, h_im]
  }
  have hd_rpow : HasDerivAt (fun y : ℝ => y ^ (-beta)) (-beta * (1 : ℝ) ^ (-beta - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl (by norm_num))
  have h_rhs : deriv (fun y : ℝ => ∫ F, ‖Q F.F ((0 : ℝ) + y • I)‖^2 ∂P) 1 = -beta := by
  {
    rw [h_ev.deriv_eq, hd_rpow.deriv]
    simp
  }
  have h_lhs : deriv (fun y : ℝ => ∫ F, ‖Q F.F ((0 : ℝ) + y • I)‖^2 ∂P) 1 = 2 * ∫ F, a F I ∂P := by
  {
    have h_dy := deriv_integral_y P I hz_I
    simp only [Complex.I_re, Complex.I_im] at h_dy
    rw [h_dy, ← integral_const_mul]
    congr 1
    ext F
    have h_pt := dy_norm_Q_sq F I hz_I
    simp only [Complex.I_re, Complex.I_im, norm_Q_at_I_sq, div_one, mul_one] at h_pt
    exact h_pt
  }
  linarith
}

lemma E_b_eq (P : Measure KClass) [IsFiniteMeasure P] (beta : ℝ)
    (h_P_eigen : ∀ z ∈ H, ∫ F, ‖Q F.F z‖^2 ∂P = (z.im : ℝ) ^ (-beta)) :
    ∫ F, b F I ∂P = 0 := by
{
  have hz_I : I ∈ H := by dsimp [H]; simp
  have h_eq : (fun x : ℝ => ∫ F, ‖Q F.F ((x : ℂ) + (1 : ℝ) • I)‖^2 ∂P) = (fun _ : ℝ => (1 : ℝ) ^ (-beta)) := by
  {
    ext x
    have hxH : (x : ℂ) + (1 : ℝ) • I ∈ H := by dsimp [H]; simp
    have h_im : ((x : ℂ) + (1 : ℝ) • I).im = 1 := by simp
    rw [h_P_eigen _ hxH, h_im]
  }
  have h_rhs : deriv (fun x : ℝ => ∫ F, ‖Q F.F ((x : ℂ) + (1 : ℝ) • I)‖^2 ∂P) 0 = 0 := by
  {
    rw [h_eq, deriv_const]
  }
  have h_lhs : deriv (fun x : ℝ => ∫ F, ‖Q F.F ((x : ℂ) + (1 : ℝ) • I)‖^2 ∂P) 0 = 2 * ∫ F, b F I ∂P := by
  {
    have h_dx := deriv_integral_x P I hz_I
    simp only [Complex.I_re, Complex.I_im] at h_dx
    rw [h_dx, ← integral_const_mul]
    congr 1
    ext F
    have h_pt := dx_norm_Q_sq F I hz_I
    simp only [Complex.I_re, Complex.I_im, norm_Q_at_I_sq, div_one, mul_one] at h_pt
    exact h_pt
  }
  linarith
}

lemma deriv2_rpow_at_one (beta : ℝ) :
    deriv (deriv (fun y : ℝ => y ^ (-beta))) 1 = beta * (beta + 1) := by
{
  have h_ev : deriv (fun y : ℝ => y ^ (-beta)) =ᶠ[𝓝 1] (fun y : ℝ => -beta * y ^ (-beta - 1)) := by
  {
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1)] with y hy
    exact (Real.hasDerivAt_rpow_const (p := -beta) (Or.inl (ne_of_gt hy))).deriv
  }
  have hd2 : HasDerivAt (fun y : ℝ => -beta * y ^ (-beta - 1)) (-beta * ((-beta - 1) * (1 : ℝ) ^ (-beta - 1 - 1))) 1 :=
    (Real.hasDerivAt_rpow_const (p := -beta - 1) (Or.inl (by norm_num))).const_mul (-beta)
  rw [h_ev.deriv_eq, hd2.deriv, Real.one_rpow]
  ring
}

lemma E_q_sq_eq (P : Measure KClass) [IsFiniteMeasure P] (beta : ℝ)
    (h_P_eigen : ∀ z ∈ H, ∫ F, ‖Q F.F z‖^2 ∂P = (z.im : ℝ) ^ (-beta)) :
    ∫ F, ‖q F I‖^2 ∂P = beta * (beta + 1) / 4 := by
{
  have hz_I : I ∈ H := by dsimp [H]; simp
  have h_ev_y : (fun y : ℝ => ∫ F, ‖Q F.F ((0 : ℝ) + y • I)‖^2 ∂P) =ᶠ[𝓝 1] (fun y : ℝ => y ^ (-beta)) := by
  {
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1)] with y hy
    have hyH : ((0 : ℝ) : ℂ) + y • I ∈ H := by dsimp [H]; simp; exact hy
    have h_im : (((0 : ℝ) : ℂ) + y • I).im = y := by simp [Complex.real_smul]
    rw [h_P_eigen _ hyH, h_im]
  }
  have h_eq_x : (fun x : ℝ => ∫ F, ‖Q F.F ((x : ℂ) + (1 : ℝ) • I)‖^2 ∂P) = (fun _ : ℝ => (1 : ℝ) ^ (-beta)) := by
  {
    ext x
    have hxH : (x : ℂ) + (1 : ℝ) • I ∈ H := by dsimp [H]; simp
    have h_im : ((x : ℂ) + (1 : ℝ) • I).im = 1 := by simp
    rw [h_P_eigen _ hxH, h_im]
  }
  have h_lap := deriv2_integral_laplacian P I hz_I
  simp only [Complex.I_re, Complex.I_im] at h_lap
  have h_d2x : deriv (deriv (fun x : ℝ => ∫ F, ‖Q F.F ((x : ℂ) + (1 : ℝ) • I)‖^2 ∂P)) 0 = 0 := by
  {
    rw [h_eq_x, deriv_const', deriv_const]
  }
  have h_d2y : deriv (deriv (fun y : ℝ => ∫ F, ‖Q F.F ((0 : ℝ) + y • I)‖^2 ∂P)) 1 = beta * (beta + 1) := by
  {
    rw [(h_ev_y.deriv).deriv_eq, deriv2_rpow_at_one beta]
  }
  have h_rhs : ∫ F, (deriv (deriv (fun x : ℝ => ‖Q F.F ((x : ℂ) + (1 : ℝ) • I)‖^2)) 0 +
                     deriv (deriv (fun y : ℝ => ‖Q F.F ((0 : ℝ) + y • I)‖^2)) 1) ∂P =
               4 * ∫ F, ‖q F I‖^2 ∂P := by
  {
    rw [← integral_const_mul]
    congr 1
    ext F
    have h_pt := laplacian_norm_Q_sq F I hz_I
    simp only [Complex.I_re, Complex.I_im] at h_pt
    rw [h_pt, norm_q_at_I_sq F]
  }
  linarith
}

end Brennan.Section3
