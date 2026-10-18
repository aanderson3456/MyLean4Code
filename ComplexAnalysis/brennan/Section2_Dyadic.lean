import Mathlib
import brennan.Section2

open Complex Set MeasureTheory Topology Filter
open scoped Classical ComplexConjugate Topology CompactlySupported ENNReal NNReal

noncomputable section

namespace Brennan.Section2_Dyadic

open Brennan.Section2

/-!
# 2.2 Affine rescaling and dyadic growth

PAPER: Identify z = x + iy ∈ H with the affine map w ↦ x + yw. Composition of these source
PAPER: maps is the product
PAPER: z · w = x + yw, z^# = (-x + i)/y, (2.6)
PAPER: with identity i and inverse z^#.
-/
-- (This is already formalized in `Section2.lean` as `aff` and `aff_comp`.)

/-!
PAPER: For F ∈ K define
PAPER: TzF(w) = (F(z · w) - F(z)) / yF'(z). (2.7)
PAPER: It belongs to K.
-/
-- (Formalized in `Section2.lean` as `T`)

/-!
PAPER: On the space C(K) of continuous complex-valued functions, equipped
PAPER: with its supremum norm, define
PAPER: AzΦ(F) = |QF (z)|^2 Φ(TzF), L = 1/2 (A_{-1/2+i/2} + A_{1/2+i/2}). (2.8)
PAPER: An operator is called positive here if it takes nonnegative real-valued functions to nonnega
PAPER: tive functions. The operators in (2.8) are positive. Their weights measure how the inverse
PAPER: derivative changes when the source is rescaled.
-/

-- We define the space of functions on KClass
def C_KClass := KClass → ℂ

@[ext]
lemma KClass_ext {F G : KClass} (h : F.F = G.F) : F = G := by
{
  cases F
  cases G
  congr
}

abbrev disk : Set ℂ := Brennan.Koebe.disk

instance : LocallyCompactSpace disk :=
  (show IsOpen disk from Metric.isOpen_ball).locallyCompactSpace

instance : LocallyCompactSpace H := isOpen_H.locallyCompactSpace

lemma compact_closure_of_disk_bounds (S : Set C(disk, ℂ))
    (hLip : ∀ R : ℝ, R < 1 → ∃ C : ℝ, ∀ g ∈ S, ∀ z w : disk,
      ‖(z : ℂ)‖ ≤ R → ‖(w : ℂ)‖ ≤ R → ‖g z - g w‖ ≤ C * ‖(z : ℂ) - (w : ℂ)‖)
    (hBd : ∀ z : disk, ∃ C : ℝ, ∀ g ∈ S, ‖g z‖ ≤ C) :
    IsCompact (closure S) := by
{
  let : T2Space (UniformOnFun disk ℂ {K | IsCompact K}) :=
    UniformOnFun.t2Space_of_covering (eq_univ_iff_forall.mpr
      (fun x => mem_sUnion_of_mem (mem_singleton x) isCompact_singleton))
  have heq : Equicontinuous (fun g : S => fun z : disk => g.1 z) := by
  {
    intro z
    obtain ⟨R, hzR, hR⟩ := exists_between
      (show ‖(z : ℂ)‖ < 1 by simpa only [disk, Brennan.Koebe.disk, Metric.mem_ball, dist_zero_right] using z.2)
    obtain ⟨C, hC⟩ := hLip R hR
    apply Metric.equicontinuousAt_of_continuity_modulus
      (fun w : disk => C * dist (z : ℂ) (w : ℂ))
    · simpa using (tendsto_const_nhds (x := C)).mul
        ((tendsto_const_nhds (x := (z : ℂ))).dist (continuous_subtype_val.tendsto z))
    · have hn : ∀ᶠ w : disk in 𝓝 z, ‖(w : ℂ)‖ < R :=
        (continuous_norm.comp continuous_subtype_val).continuousAt (Iio_mem_nhds hzR)
      filter_upwards [hn] with w hw g
      simpa [dist_eq_norm] using hC g.1 g.2 z w hzR.le hw.le
  }
  apply ArzelaAscoli.isCompact_closure_of_isClosedEmbedding
    (F := fun g : C(disk, ℂ) => fun z : disk => g z)
    (𝔖 := {K | IsCompact K}) (fun _ h => h)
    (ContinuousMap.isUniformEmbedding_toUniformOnFunIsCompact.isClosedEmbedding)
  · intro K _
    exact heq.equicontinuousOn K
  · intro K _ z _
    obtain ⟨C, hC⟩ := hBd z
    exact ⟨Metric.closedBall 0 C, isCompact_closedBall _ _, by simpa using hC⟩
}

def diskExtend (g : C(disk, ℂ)) (z : ℂ) : ℂ :=
  if hz : z ∈ disk then g ⟨z, hz⟩ else 0

@[simp] lemma diskExtend_apply (g : C(disk, ℂ)) (z : disk) : diskExtend g z = g z := by
{
  simp [diskExtend]
}

lemma diskExtend_convergence {ι : Type*} {l : Filter ι}
    {g : ι → C(disk, ℂ)} {f : C(disk, ℂ)} (h : Tendsto g l (𝓝 f)) :
    TendstoLocallyUniformlyOn (fun i => diskExtend (g i)) (diskExtend f) l disk := by
{
  rw [tendstoLocallyUniformlyOn_iff_tendstoLocallyUniformly_comp_coe]
  simpa only [Function.comp_def, diskExtend_apply] using
    ContinuousMap.tendsto_iff_tendstoLocallyUniformly.mp h
}

def diskSchlichtSet : Set C(disk, ℂ) := {g | Brennan.Koebe.IsClassS (diskExtend g)}

lemma isClosed_diskSchlichtSet : IsClosed diskSchlichtSet := by
{
  rw [isClosed_iff_forall_filter]
  intro g l hl hs hg
  let := hl
  have hS : ∀ᶠ f : C(disk, ℂ) in l, Brennan.Koebe.IsClassS (diskExtend f) :=
    le_principal_iff.mp hs
  have hc := diskExtend_convergence (g := id) hg
  have hhol : ∀ᶠ f : C(disk, ℂ) in l, DifferentiableOn ℂ (diskExtend f) disk :=
    hS.mono (fun _ h => h.1)
  have hgH := hc.differentiableOn hhol (show IsOpen disk from Metric.isOpen_ball)
  refine ⟨hgH, ?_, ?_, ?_⟩
  · intro z hz w hw he
    by_contra hne
    obtain ⟨c, hc0, hs'⟩ := Brennan.Koebe.schlicht_uniform_separation hz hw hne
    have hevent : ∀ᶠ f : C(disk, ℂ) in l, c ≤ ‖diskExtend f w - diskExtend f z‖ :=
      hS.mono (fun f hf => hs' (diskExtend f) hf)
    have ht := ((hc.tendsto_at hw).sub (hc.tendsto_at hz)).norm
    have hc' := ge_of_tendsto ht hevent
    rw [he, sub_self, norm_zero] at hc'
    exact not_le_of_gt hc0 hc'
  · apply tendsto_nhds_unique (hc.tendsto_at (show (0 : ℂ) ∈ disk by simp [disk, Brennan.Koebe.disk]))
    exact tendsto_const_nhds.congr' (hS.mono (fun _ hf => hf.2.2.1.symm))
  · apply tendsto_nhds_unique ((hc.deriv hhol (show IsOpen disk from Metric.isOpen_ball)).tendsto_at
      (show (0 : ℂ) ∈ disk by simp [disk, Brennan.Koebe.disk]))
    exact tendsto_const_nhds.congr' (hS.mono (fun _ hf => hf.2.2.2.symm))
}

lemma isCompact_diskSchlichtSet : IsCompact diskSchlichtSet := by
{
  rw [← isClosed_diskSchlichtSet.closure_eq]
  apply compact_closure_of_disk_bounds
  · intro R hR
    refine ⟨2 / (1 - R)^3, ?_⟩
    intro g hg z w hz hw
    simpa only [diskExtend_apply] using Brennan.Koebe.schlicht_lipschitz_bound hg hR hz hw
  · intro z
    refine ⟨(2 / (1 - ‖(z : ℂ)‖)^3) * ‖(z : ℂ)‖, ?_⟩
    intro g hg
    simpa only [diskExtend_apply] using Brennan.Koebe.schlicht_local_bound hg
      (show ‖(z : ℂ)‖ < 1 by simpa only [disk, Brennan.Koebe.disk, Metric.mem_ball, dist_zero_right] using z.2) le_rfl
}

abbrev DiskClass := diskSchlichtSet

instance : CompactSpace DiskClass := isCompact_iff_compactSpace.mp isCompact_diskSchlichtSet
instance : T2Space DiskClass := inferInstanceAs (T2Space diskSchlichtSet)
instance : TopologicalSpace.PseudoMetrizableSpace DiskClass :=
  inferInstanceAs (TopologicalSpace.PseudoMetrizableSpace diskSchlichtSet)
instance : MeasurableSpace DiskClass := borel DiskClass
instance : BorelSpace DiskClass := ⟨rfl⟩

lemma ofKClass_mem_diskSchlichtSet (F : KClass) :
    (⟨fun z => K_to_S F z, continuousOn_iff_continuous_restrict.mp
      (K_to_S_differentiable F).continuousOn⟩ : C(disk, ℂ)) ∈ diskSchlichtSet := by
{
  have he : EqOn (diskExtend (⟨fun z => K_to_S F z,
    continuousOn_iff_continuous_restrict.mp
      (K_to_S_differentiable F).continuousOn⟩ : C(disk, ℂ))) (K_to_S F) disk := by
  {
    intro z hz
    exact diskExtend_apply _ ⟨z, hz⟩
  }
  have hS := lemma_2_2_bounds_S F
  refine ⟨hS.1.congr he, ?_, ?_, ?_⟩
  · intro z hz w hw h
    exact hS.2.1 hz hw ((he hz).symm.trans (h.trans (he hw)))
  · rw [he (by simp [disk, Brennan.Koebe.disk])]
    exact hS.2.2.1
  · rw [he.deriv Metric.isOpen_ball (by simp [disk, Brennan.Koebe.disk])]
    exact hS.2.2.2
}

def ofKClass (F : KClass) : DiskClass :=
  ⟨⟨fun z => K_to_S F z, continuousOn_iff_continuous_restrict.mp
    (K_to_S_differentiable F).continuousOn⟩, ofKClass_mem_diskSchlichtSet F⟩

instance instTopologicalSpaceKClass : TopologicalSpace KClass :=
  TopologicalSpace.induced ofKClass inferInstance

instance instMeasurableSpaceKClass : MeasurableSpace KClass := borel KClass

instance instBorelSpaceKClass : BorelSpace KClass := ⟨rfl⟩

-- The basic transfer operator A_z
def A_op_val (z : ℂ) (hz : z ∈ H) (Phi : C_KClass) (F : KClass) : ℂ :=
  (A_weight z F.F : ℂ) * Phi (⟨T z F.F, (T_KClass F z hz).1, (T_KClass F z hz).2.1, (T_KClass F z hz).2.2⟩)

lemma L_op_left_H : (-1/2 : ℂ) + I/2 ∈ H := by
{
  dsimp [H]
  simp
}

lemma L_op_right_H : (1/2 : ℂ) + I/2 ∈ H := by
{
  dsimp [H]
  simp
}

-- The dyadic operator L
def L_op_val (Phi : C_KClass) (F : KClass) : ℂ :=
  (1 / 2 : ℂ) * (A_op_val (-1/2 + I/2) L_op_left_H Phi F + A_op_val (1/2 + I/2) L_op_right_H Phi F)

lemma aff_H (z w : ℂ) (hz : z ∈ H) (hw : w ∈ H) : aff z w ∈ H := by
{
  exact aff_mem_H hz hw
}

lemma A_weight_cocycle (F : KClass) (z w : ℂ) (hz : z ∈ H) (hw : w ∈ H) :
    A_weight z F.F * A_weight w (T z F.F) = A_weight (aff z w) F.F := by
{
  dsimp [A_weight]
  have hz_im : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hF_diff : DifferentiableAt ℂ F.F (aff z w) :=
    (F.univalent.1 (aff z w) (aff_mem_H hz hw)).differentiableAt (isOpen_H.mem_nhds (aff_mem_H hz hw))
  rw [lemma_2_3_Q F.F z w hF_diff hz_im, norm_div, div_pow]
  have hdF_z : deriv F.F z ≠ 0 := deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz
  have hQz_ne : ‖Q F.F z‖^2 ≠ 0 := by
  {
    dsimp [Q]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr (one_div_ne_zero hdF_z))
  }
  exact mul_div_cancel₀ _ hQz_ne
}

/-!
PAPER: Lemma 2.3 (Affine identities and transfer growth). For z, w ∈ H and F ∈ K,
PAPER: QTzF (w) = QF (z · w) / QF (z), Tw(TzF) = Tz·wF, AzAw = Az·w. (2.9)
-/
-- (First two identities formalized in `Section2.lean` as `lemma_2_3_Q` and `lemma_2_3_KClass`)
lemma lemma_2_3_A_op (z w : ℂ) (hz : z ∈ H) (hw : w ∈ H) (Phi : C_KClass) :
    A_op_val z hz (A_op_val w hw Phi) = A_op_val (aff z w) (aff_H z w hz hw) Phi := by
{
  funext F
  dsimp [A_op_val]
  rw [← mul_assoc]
  have h_wt : (A_weight z F.F : ℂ) * (A_weight w (T z F.F) : ℂ) = (A_weight (aff z w) F.F : ℂ) := by
  {
    exact_mod_cast A_weight_cocycle F z w hz hw
  }
  rw [h_wt]
  congr 2
  apply KClass_ext
  exact lemma_2_3_KClass F z w hz hw
}

/-!
PAPER: Each Az is bounded on C(K), and for fixed Φ ∈ C(K) the map z ↦ AzΦ is continuous in
PAPER: the supremum norm. For n ≥ 0, put vn = 2^{-n} and un,j = -1 + (2j + 1)vn, 0 ≤ j < 2^n.
PAPER: Then
PAPER: L^n = vn \sum_{j=0}^{2^n-1} Aun,j+ivn, ∥L^n∥ = \max_{F ∈ K} L^n1(F). (2.10)
-/
def v_n (n : ℕ) : ℝ := 2^(- (n : ℝ))
def u_nj (n j : ℕ) : ℝ := -1 + (2 * (j : ℝ) + 1) * v_n n

lemma v_n_pos (n : ℕ) : 0 < v_n n := by
{
  dsimp [v_n]
  positivity
}

lemma v_n_eq_half_pow (n : ℕ) : v_n n = (1 / 2 : ℝ) ^ n := by
{
  dsimp [v_n]
  rw [Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_eq_one_div, div_pow, one_pow]
}

lemma v_n_zero : v_n 0 = 1 := by
{
  rw [v_n_eq_half_pow, pow_zero]
}

lemma v_n_succ (n : ℕ) : v_n (n + 1) = (1 / 2 : ℝ) * v_n n := by
{
  rw [v_n_eq_half_pow, v_n_eq_half_pow, pow_succ']
}

lemma v_n_le_one (n : ℕ) : v_n n ≤ 1 := by
{
  rw [v_n_eq_half_pow]
  exact pow_le_one₀ (by norm_num) (by norm_num)
}

lemma pow_two_mul_v_n (n : ℕ) : (2 : ℝ) ^ n * v_n n = 1 := by
{
  rw [v_n_eq_half_pow, ← mul_pow]
  norm_num
}

def dyadic_pt (n j : ℕ) : ℂ := (u_nj n j : ℂ) + (v_n n : ℂ) * I

lemma dyadic_cell_H (n j : ℕ) : dyadic_pt n j ∈ H := by
{
  dsimp [H, dyadic_pt]
  simp only [ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
  exact v_n_pos n
}

def T_elem (F : KClass) (z : ℂ) (hz : z ∈ H) : KClass :=
  ⟨T z F.F, (T_KClass F z hz).1, (T_KClass F z hz).2.1, (T_KClass F z hz).2.2⟩

lemma T_elem_I (F : KClass) : T_elem F I (by dsimp [H]; simp) = F := by
{
  apply KClass_ext
  ext w
  dsimp [T_elem, T, aff]
  simp [F.norm_zero, F.norm_deriv]
}

lemma T_elem_comp (F : KClass) (z w : ℂ) (hz : z ∈ H) (hw : w ∈ H) :
    T_elem (T_elem F z hz) w hw = T_elem F (aff z w) (aff_H z w hz hw) := by
{
  apply KClass_ext
  exact lemma_2_3_KClass F z w hz hw
}

def idKClass : KClass where
  F := fun z => z - I
  univalent := ⟨differentiableOn_id.sub (differentiableOn_const I),
    fun _ _ _ _ h => sub_left_inj.mp h⟩
  norm_zero := sub_self I
  norm_deriv := by
  {
    have h := ((hasDerivAt_id I).sub_const I).deriv
    exact h
  }

lemma A_weight_idKClass (z : ℂ) : A_weight z idKClass.F = 1 := by
{
  have hd : deriv idKClass.F z = 1 := by
  {
    change deriv (fun w : ℂ => w - I) z = 1
    exact ((hasDerivAt_id z).sub_const I).deriv
  }
  dsimp [A_weight, Q]
  rw [hd]
  simp
}

lemma A_weight_at_I (F : KClass) : A_weight I F.F = 1 := by
{
  dsimp [A_weight, Q]
  rw [F.norm_deriv]
  simp
}

/-- The n-th iterate of the dyadic transfer operator via its explicit dyadic sum (2.10). -/
def L_pow_val (n : ℕ) (Phi : C_KClass) (F : KClass) : ℂ :=
  (v_n n : ℂ) * ∑ j ∈ Finset.range (2^n),
    A_op_val (dyadic_pt n j) (dyadic_cell_H n j) Phi F

/-- Real-valued n-th dyadic transfer operator. -/
def L_pow_real (n : ℕ) (Phi : KClass → ℝ) (F : KClass) : ℝ :=
  v_n n * ∑ j ∈ Finset.range (2^n),
    A_weight (dyadic_pt n j) F.F * Phi (T_elem F (dyadic_pt n j) (dyadic_cell_H n j))

lemma aff_left_dyadic_pt (n k : ℕ) :
    aff (-1/2 + I/2) (dyadic_pt n k) = dyadic_pt (n + 1) k := by
{
  apply Complex.ext
  · simp only [aff, dyadic_pt, u_nj, v_n_succ]
    simp only [add_re, neg_re, div_ofNat_re, one_re, I_re, zero_div, add_zero,
      ofReal_re, mul_re, ofReal_im, I_im, mul_one, mul_zero, sub_zero, add_im, neg_im,
      div_ofNat_im, one_im, zero_add]
    ring
  · simp only [aff, dyadic_pt, v_n_succ]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, add_re, neg_re, div_ofNat_re, one_re,
      I_re, zero_div, add_zero, I_im, mul_one, mul_zero, zero_add, neg_im, div_ofNat_im, one_im]
    ring
}

lemma aff_right_dyadic_pt (n k : ℕ) :
    aff (1/2 + I/2) (dyadic_pt n k) = dyadic_pt (n + 1) (2^n + k) := by
{
  have hp := pow_two_mul_v_n n
  apply Complex.ext
  · simp only [aff, dyadic_pt, u_nj, v_n_succ, Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat]
    simp only [add_re, div_ofNat_re, one_re, I_re, zero_div, add_zero, ofReal_re, mul_re,
      ofReal_im, I_im, mul_one, mul_zero, sub_zero, add_im, div_ofNat_im, one_im, zero_add]
    linear_combination -hp
  · simp only [aff, dyadic_pt, v_n_succ]
    simp only [add_im, ofReal_im, mul_im, ofReal_re, add_re, div_ofNat_re, one_re, I_re,
      zero_div, add_zero, I_im, mul_one, mul_zero, zero_add, div_ofNat_im, one_im]
    ring
}

lemma dyadic_pt_zero_zero : dyadic_pt 0 0 = I := by
{
  dsimp [dyadic_pt, u_nj]
  rw [v_n_zero]
  simp
}

lemma L_pow_real_zero (Phi : KClass → ℝ) (F : KClass) :
    L_pow_real 0 Phi F = Phi F := by
{
  unfold L_pow_real
  rw [pow_zero, Finset.sum_range_one, v_n_zero, one_mul]
  have h0 : T_elem F (dyadic_pt 0 0) (dyadic_cell_H 0 0) = F := by
  {
    apply KClass_ext
    dsimp [T_elem]
    rw [dyadic_pt_zero_zero]
    exact congrArg KClass.F (T_elem_I F)
  }
  rw [h0, dyadic_pt_zero_zero, A_weight_at_I F, one_mul]
}

lemma L_pow_real_succ_left (n k : ℕ) (Phi : KClass → ℝ) (F : KClass) :
    A_weight (dyadic_pt (n + 1) k) F.F *
      Phi (T_elem F (dyadic_pt (n + 1) k) (dyadic_cell_H (n + 1) k)) =
    A_weight (-1/2 + I/2) F.F *
      (A_weight (dyadic_pt n k) (T_elem F (-1/2 + I/2) L_op_left_H).F *
        Phi (T_elem (T_elem F (-1/2 + I/2) L_op_left_H) (dyadic_pt n k) (dyadic_cell_H n k))) := by
{
  have hT : T_elem (T_elem F (-1/2 + I/2) L_op_left_H) (dyadic_pt n k) (dyadic_cell_H n k) =
      T_elem F (dyadic_pt (n + 1) k) (dyadic_cell_H (n + 1) k) := by
  {
    rw [T_elem_comp]
    apply KClass_ext
    dsimp [T_elem]
    rw [aff_left_dyadic_pt]
  }
  rw [hT, ← mul_assoc]
  congr 1
  rw [← aff_left_dyadic_pt n k]
  exact (A_weight_cocycle F (-1/2 + I/2) (dyadic_pt n k) L_op_left_H (dyadic_cell_H n k)).symm
}

lemma L_pow_real_succ_right (n k : ℕ) (Phi : KClass → ℝ) (F : KClass) :
    A_weight (dyadic_pt (n + 1) (2^n + k)) F.F *
      Phi (T_elem F (dyadic_pt (n + 1) (2^n + k)) (dyadic_cell_H (n + 1) (2^n + k))) =
    A_weight (1/2 + I/2) F.F *
      (A_weight (dyadic_pt n k) (T_elem F (1/2 + I/2) L_op_right_H).F *
        Phi (T_elem (T_elem F (1/2 + I/2) L_op_right_H) (dyadic_pt n k) (dyadic_cell_H n k))) := by
{
  have hT : T_elem (T_elem F (1/2 + I/2) L_op_right_H) (dyadic_pt n k) (dyadic_cell_H n k) =
      T_elem F (dyadic_pt (n + 1) (2^n + k)) (dyadic_cell_H (n + 1) (2^n + k)) := by
  {
    rw [T_elem_comp]
    apply KClass_ext
    dsimp [T_elem]
    rw [aff_right_dyadic_pt]
  }
  rw [hT, ← mul_assoc]
  congr 1
  rw [← aff_right_dyadic_pt n k]
  exact (A_weight_cocycle F (1/2 + I/2) (dyadic_pt n k) L_op_right_H (dyadic_cell_H n k)).symm
}

lemma L_pow_real_succ (n : ℕ) (Phi : KClass → ℝ) (F : KClass) :
    L_pow_real (n + 1) Phi F =
      (1 / 2 : ℝ) * (A_weight (-1/2 + I/2) F.F *
          L_pow_real n Phi (T_elem F (-1/2 + I/2) L_op_left_H) +
        A_weight (1/2 + I/2) F.F *
          L_pow_real n Phi (T_elem F (1/2 + I/2) L_op_right_H)) := by
{
  unfold L_pow_real
  have hpow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by ring
  rw [hpow, Finset.sum_range_add, v_n_succ]
  have hL : ∑ k ∈ Finset.range (2 ^ n), A_weight (dyadic_pt (n + 1) k) F.F *
      Phi (T_elem F (dyadic_pt (n + 1) k) (dyadic_cell_H (n + 1) k)) =
    A_weight (-1/2 + I/2) F.F * ∑ k ∈ Finset.range (2 ^ n),
      A_weight (dyadic_pt n k) (T_elem F (-1/2 + I/2) L_op_left_H).F *
        Phi (T_elem (T_elem F (-1/2 + I/2) L_op_left_H) (dyadic_pt n k) (dyadic_cell_H n k)) := by
  {
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => L_pow_real_succ_left n k Phi F)
  }
  have hR : ∑ k ∈ Finset.range (2 ^ n), A_weight (dyadic_pt (n + 1) (2 ^ n + k)) F.F *
      Phi (T_elem F (dyadic_pt (n + 1) (2 ^ n + k)) (dyadic_cell_H (n + 1) (2 ^ n + k))) =
    A_weight (1/2 + I/2) F.F * ∑ k ∈ Finset.range (2 ^ n),
      A_weight (dyadic_pt n k) (T_elem F (1/2 + I/2) L_op_right_H).F *
        Phi (T_elem (T_elem F (1/2 + I/2) L_op_right_H) (dyadic_pt n k) (dyadic_cell_H n k)) := by
  {
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl (fun k _ => L_pow_real_succ_right n k Phi F)
  }
  rw [hL, hR]
  ring
}

lemma L_pow_real_add (m n : ℕ) (Phi : KClass → ℝ) (F : KClass) :
    L_pow_real (m + n) Phi F = L_pow_real m (L_pow_real n Phi) F := by
{
  induction m generalizing F with
  | zero =>
    rw [Nat.zero_add, L_pow_real_zero]
  | succ m ih =>
    rw [Nat.succ_add, L_pow_real_succ, ih, ih, ← L_pow_real_succ]
}

/-- `L^n 1(F)` in equation (2.10). -/
def L_one (n : ℕ) (F : KClass) : ℝ := L_pow_real n (fun _ => 1) F

/-- Operator norm `‖L^n‖ = sup_{F ∈ K} L^n 1(F)` in equation (2.10). -/
def L_norm (n : ℕ) : ℝ := ⨆ F : KClass, L_one n F

lemma L_pow_real_le_mul_L_one (n : ℕ) (Phi : KClass → ℝ) (M : ℝ)
    (hPhi : ∀ G : KClass, Phi G ≤ M) (F : KClass) :
    L_pow_real n Phi F ≤ M * L_one n F := by
{
  dsimp [L_pow_real, L_one]
  have hsum : ∑ j ∈ Finset.range (2 ^ n),
      A_weight (dyadic_pt n j) F.F * Phi (T_elem F (dyadic_pt n j) (dyadic_cell_H n j)) ≤
    M * ∑ j ∈ Finset.range (2 ^ n), A_weight (dyadic_pt n j) F.F * 1 := by
  {
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro j _
    have hA : 0 ≤ A_weight (dyadic_pt n j) F.F := sq_nonneg _
    calc
      A_weight (dyadic_pt n j) F.F * Phi (T_elem F (dyadic_pt n j) (dyadic_cell_H n j)) ≤
          A_weight (dyadic_pt n j) F.F * M :=
        mul_le_mul_of_nonneg_left (hPhi _) hA
      _ = M * (A_weight (dyadic_pt n j) F.F * 1) := by ring
  }
  have hmul := mul_le_mul_of_nonneg_left hsum (v_n_pos n).le
  linarith
}

lemma L_one_idKClass (n : ℕ) : L_one n idKClass = 1 := by
{
  dsimp [L_one, L_pow_real]
  simp_rw [A_weight_idKClass, mul_one, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    mul_one, Nat.cast_pow, Nat.cast_ofNat]
  rw [mul_comm]
  exact pow_two_mul_v_n n
}

lemma L_one_nonneg (n : ℕ) (F : KClass) : 0 ≤ L_one n F := by
{
  dsimp [L_one, L_pow_real]
  refine mul_nonneg (v_n_pos n).le (Finset.sum_nonneg (fun j _ => ?_))
  have hA : 0 ≤ A_weight (dyadic_pt n j) F.F := sq_nonneg _
  linarith
}

lemma u_nj_sq_le_one (n j : ℕ) (hj : j ∈ Finset.range (2^n)) : (u_nj n j) ^ 2 ≤ 1 := by
{
  have hj_lt : j < 2^n := Finset.mem_range.mp hj
  have hj1 : (j : ℝ) + 1 ≤ (2 : ℝ) ^ n := by
  {
    exact_mod_cast Nat.succ_le_of_lt hj_lt
  }
  have hj0 : 0 ≤ (j : ℝ) := Nat.cast_nonneg j
  have hv0 : 0 < v_n n := v_n_pos n
  have hp := pow_two_mul_v_n n
  have hlo : -1 ≤ u_nj n j := by
  {
    dsimp [u_nj]
    nlinarith
  }
  have hhi : u_nj n j ≤ 1 := by
  {
    dsimp [u_nj]
    have hmul : (2 * (j : ℝ) + 1) * v_n n ≤ 2 * ((2 : ℝ) ^ n * v_n n) := by
    {
      nlinarith
    }
    linarith
  }
  nlinarith
}

lemma A_weight_dyadic_le (n j : ℕ) (hj : j ∈ Finset.range (2^n)) (F : KClass) :
    A_weight (dyadic_pt n j) F.F ≤ 625 * (4 : ℝ) ^ n := by
{
  have hQ := norm_Q_le_general F (dyadic_cell_H n j)
  have hre : (dyadic_pt n j).re = u_nj n j := by
  {
    dsimp [dyadic_pt]
    simp
  }
  have him : (dyadic_pt n j).im = v_n n := by
  {
    dsimp [dyadic_pt]
    simp
  }
  rw [hre, him] at hQ
  have hu := u_nj_sq_le_one n j hj
  have hv1 := v_n_le_one n
  have hv0 := v_n_pos n
  have hnum : ((u_nj n j) ^ 2 + (v_n n + 1) ^ 2) ^ 2 ≤ 25 := by
  {
    have hinner : (u_nj n j) ^ 2 + (v_n n + 1) ^ 2 ≤ 5 := by nlinarith
    have hinner0 : 0 ≤ (u_nj n j) ^ 2 + (v_n n + 1) ^ 2 := by positivity
    nlinarith
  }
  have hQ25 : ‖Q F.F (dyadic_pt n j)‖ ≤ 25 / v_n n :=
    hQ.trans (div_le_div_of_nonneg_right hnum hv0.le)
  have hsq : ‖Q F.F (dyadic_pt n j)‖ ^ 2 ≤ (25 / v_n n) ^ 2 :=
    (sq_le_sq₀ (norm_nonneg _) (by positivity)).mpr hQ25
  have hvn_sq : (25 / v_n n) ^ 2 = 625 * (4 : ℝ) ^ n := by
  {
    rw [div_pow, v_n_eq_half_pow, one_div, inv_pow, inv_pow, div_inv_eq_mul, ← pow_mul, mul_comm n 2, pow_mul]
    norm_num
  }
  simpa [A_weight, hvn_sq] using hsq
}

lemma L_one_le_bound (n : ℕ) (F : KClass) : L_one n F ≤ 625 * (4 : ℝ) ^ n := by
{
  dsimp [L_one, L_pow_real]
  have hsum : ∑ j ∈ Finset.range (2^n), A_weight (dyadic_pt n j) F.F * 1 ≤
      ∑ _j ∈ Finset.range (2^n), 625 * (4 : ℝ) ^ n := by
  {
    apply Finset.sum_le_sum
    intro j hj
    simpa using A_weight_dyadic_le n j hj F
  }
  have hmul := mul_le_mul_of_nonneg_left hsum (v_n_pos n).le
  rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul, Nat.cast_pow, Nat.cast_ofNat] at hmul
  have hp := pow_two_mul_v_n n
  have hrhs : v_n n * ((2 : ℝ) ^ n * (625 * (4 : ℝ) ^ n)) = 625 * (4 : ℝ) ^ n := by
  {
    linear_combination (625 * (4 : ℝ) ^ n) * hp
  }
  linarith
}

lemma bddAbove_L_one (n : ℕ) : BddAbove (range (L_one n)) := by
{
  refine ⟨625 * (4 : ℝ) ^ n, ?_⟩
  rintro _ ⟨F, rfl⟩
  exact L_one_le_bound n F
}

lemma le_L_norm (n : ℕ) (F : KClass) : L_one n F ≤ L_norm n := by
{
  exact le_ciSup (bddAbove_L_one n) F
}

lemma one_le_L_norm (n : ℕ) : 1 ≤ L_norm n := by
{
  rw [← L_one_idKClass n]
  exact le_L_norm n idKClass
}

lemma L_norm_pos (n : ℕ) : 0 < L_norm n := by
{
  exact zero_lt_one.trans_le (one_le_L_norm n)
}

lemma L_norm_le_bound (n : ℕ) : L_norm n ≤ 625 * (4 : ℝ) ^ n := by
{
  haveI : Nonempty KClass := ⟨idKClass⟩
  exact ciSup_le (L_one_le_bound n)
}

lemma L_norm_submult (m n : ℕ) : L_norm (m + n) ≤ L_norm m * L_norm n := by
{
  haveI : Nonempty KClass := ⟨idKClass⟩
  apply ciSup_le
  intro F
  have h1 : L_one (m + n) F = L_pow_real m (L_one n) F :=
    L_pow_real_add m n (fun _ => 1) F
  rw [h1]
  calc
    L_pow_real m (L_one n) F ≤ L_norm n * L_one m F :=
      L_pow_real_le_mul_L_one m (L_one n) (L_norm n) (le_L_norm n) F
    _ = L_one m F * L_norm n := mul_comm _ _
    _ ≤ L_norm m * L_norm n :=
      mul_le_mul_of_nonneg_right (le_L_norm m F) (L_norm_pos n).le
}

lemma log_L_norm_subadditive : Subadditive (fun n : ℕ => Real.log (L_norm n)) := by
{
  intro m n
  calc
    Real.log (L_norm (m + n)) ≤ Real.log (L_norm m * L_norm n) :=
      Real.log_le_log (L_norm_pos (m + n)) (L_norm_submult m n)
    _ = Real.log (L_norm m) + Real.log (L_norm n) :=
      Real.log_mul (L_norm_pos m).ne' (L_norm_pos n).ne'
}

lemma log_L_norm_bddBelow : BddBelow (range (fun n : ℕ => Real.log (L_norm n) / n)) := by
{
  refine ⟨0, ?_⟩
  rintro _ ⟨n, rfl⟩
  exact div_nonneg (Real.log_nonneg (one_le_L_norm n)) (Nat.cast_nonneg n)
}

/-- Logarithmic growth rate of `L_norm`. -/
def rho_log : ℝ := log_L_norm_subadditive.lim

/-- Spectral radius `ρ = lim_{n→∞} ‖L^n‖^{1/n}` of the dyadic transfer operator `L`. -/
def rho : ℝ := Real.exp rho_log

lemma tendsto_log_L_norm :
    Tendsto (fun n : ℕ => Real.log (L_norm n) / n) atTop (𝓝 rho_log) := by
{
  exact log_L_norm_subadditive.tendsto_lim log_L_norm_bddBelow
}

lemma rho_ge_one : 1 ≤ rho := by
{
  rw [rho, Real.one_le_exp_iff]
  exact ge_of_tendsto tendsto_log_L_norm
    (Eventually.of_forall (fun n => div_nonneg (Real.log_nonneg (one_le_L_norm n)) (Nat.cast_nonneg n)))
}

lemma rho_le_four : rho ≤ 4 := by
{
  have ht : Tendsto (fun n : ℕ => Real.log 625 / (n : ℝ) + Real.log 4) atTop (𝓝 (Real.log 4)) := by
  {
    simpa using (tendsto_const_nhds.div_atTop tendsto_natCast_atTop_atTop).add_const (Real.log 4)
  }
  have hl : rho_log ≤ Real.log 4 := by
  {
    apply le_of_tendsto_of_tendsto tendsto_log_L_norm ht
    filter_upwards [eventually_gt_atTop (0 : ℕ)] with n hn
    have hnR : (0 : ℝ) < n := by exact_mod_cast hn
    have hlog := Real.log_le_log (L_norm_pos n) (L_norm_le_bound n)
    rw [Real.log_mul (by norm_num) (by positivity), Real.log_pow] at hlog
    calc
      Real.log (L_norm n) / (n : ℝ) ≤ (Real.log 625 + (n : ℝ) * Real.log 4) / (n : ℝ) :=
        div_le_div_of_nonneg_right hlog hnR.le
      _ = Real.log 625 / (n : ℝ) + Real.log 4 := by field_simp
  }
  simpa [rho, Real.exp_log (by norm_num : (0 : ℝ) < 4)] using Real.exp_le_exp.mpr hl
}

/-- Spectral radius bounds `1 ≤ ρ ≤ 4` (Equation 2.11). -/
theorem rho_bounds : 1 ≤ rho ∧ rho ≤ 4 := by
{
  exact ⟨rho_ge_one, rho_le_four⟩
}

/-!
# 2.3 From dyadic samples to disk integral means

PAPER: The next proposition explains why an upper bound on ρ controls an entire circle. The
PAPER: comparison uses the same compact family in every cell, so all its constants are independent
PAPER: of the chosen univalent map.

PAPER: Proposition 2.4 (Uniform disk comparison). If ρ ≤ 2, then for every ε > 0 there is
PAPER: Cε < ∞ such that
PAPER: M_{-2}[f'](r) ≤ Cε(1 - r)^{-1-ε} (f ∈ S, 1/2 ≤ r < 1). (2.12)
PAPER: The constant depends only on ε.
-/
lemma L_norm_eventually_le {r : ℝ} (hr : rho < r) :
    ∀ᶠ n : ℕ in atTop, L_norm n ≤ r ^ n := by
{
  have hr0 : 0 < r := lt_of_lt_of_le zero_lt_one (rho_ge_one.trans hr.le)
  have hlog : rho_log < Real.log r := by
  {
    rwa [← Real.exp_lt_exp, Real.exp_log hr0]
  }
  filter_upwards [tendsto_log_L_norm.eventually (gt_mem_nhds hlog),
    eventually_gt_atTop (0 : ℕ)] with n hn hn0
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn0
  have he : Real.log (L_norm n) ≤ (n : ℝ) * Real.log r := by
  {
    have := (div_lt_iff₀ hnR).mp hn
    linarith
  }
  have hexp := Real.exp_le_exp.mpr he
  simpa only [Real.exp_log (L_norm_pos n), Real.exp_nat_mul, Real.exp_log hr0] using hexp
}

lemma L_norm_uniform_growth (h_rho : rho ≤ 2) {lam : ℝ} (hlam : 2 < lam) :
    ∃ C : ℝ, 0 < C ∧ ∀ n : ℕ, L_norm n ≤ C * lam ^ n := by
{
  have hl : 0 < lam := by linarith
  obtain ⟨N, hN⟩ := eventually_atTop.mp (L_norm_eventually_le (lt_of_le_of_lt h_rho hlam))
  let C : ℝ := 1 + ∑ j ∈ Finset.range N, L_norm j / lam ^ j
  have hC : 1 ≤ C := le_add_of_nonneg_right
    (Finset.sum_nonneg (fun j _ => div_nonneg (L_norm_pos j).le (pow_pos hl j).le))
  refine ⟨C, zero_lt_one.trans_le hC, fun n => ?_⟩
  by_cases hn : N ≤ n
  · exact (hN n hn).trans (le_mul_of_one_le_left (pow_pos hl n).le hC)
  · have hs : L_norm n / lam ^ n ≤ ∑ j ∈ Finset.range N, L_norm j / lam ^ j :=
      Finset.single_le_sum (fun j _ => div_nonneg (L_norm_pos j).le (pow_pos hl j).le)
        (Finset.mem_range.mpr (lt_of_not_ge hn))
    apply (div_le_iff₀ (pow_pos hl n)).mp
    exact hs.trans (by dsimp [C]; linarith)
}

def S_to_K (f : ℂ → ℂ) (z : ℂ) : ℂ := 2 * I * f (inv_cayley z)

lemma hasDerivAt_S_to_K {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    {z : ℂ} (hz : z ∈ H) :
    HasDerivAt (S_to_K f) (-(4 : ℂ) * deriv f (inv_cayley z) / (z + I)^2) z := by
{
  have hd := ((hf _ (inv_cayley_maps hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (inv_cayley_maps hz))).hasDerivAt
  convert (hd.comp z (hasDerivAt_inv_cayley hz)).const_mul (2 * I) using 1 <;> try rfl
  ring_nf
  simp [Complex.I_sq]
}

lemma S_to_K_schlicht {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) :
    UnivalentOn (S_to_K f) H ∧ S_to_K f I = 0 ∧ deriv (S_to_K f) I = 1 := by
{
  have hI : I ∈ H := by dsimp [H]; simp
  have hinvI : inv_cayley I = 0 := by simp [inv_cayley]
  refine ⟨⟨fun z hz => (hasDerivAt_S_to_K hf.1 hz).differentiableAt.differentiableWithinAt, ?_⟩, ?_, ?_⟩
  · intro z hz w hw he
    have hm := hf.2.1 (inv_cayley_maps hz) (inv_cayley_maps hw)
      ((mul_left_cancel₀ (by simp : (2 : ℂ) * I ≠ 0)) he)
    simpa only [cayley_inv_cayley hz, cayley_inv_cayley hw] using congrArg cayley hm
  · simp [S_to_K, hinvI, hf.2.2.1]
  · rw [(hasDerivAt_S_to_K hf.1 hI).deriv, hinvI, hf.2.2.2]
    norm_num [add_sq, mul_assoc, Complex.I_sq, Complex.I_mul_I]
}

def S_to_KClass (f : ℂ → ℂ) (hf : Brennan.Koebe.IsClassS f) : KClass :=
  ⟨S_to_K f, (S_to_K_schlicht hf).1, (S_to_K_schlicht hf).2.1, (S_to_K_schlicht hf).2.2⟩

lemma cayley_add_I {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    cayley w + I = 2 * I / (1 - w) := by
{
  have hd := cayley_den_ne_zero hw
  dsimp [cayley]
  field_simp
  ring
}

lemma inverse_deriv_square_conversion {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f)
    {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    ‖deriv f w‖ ^ (-2 : ℝ) ≤ 16 * A_weight (cayley w) (S_to_KClass f hf).F := by
{
  have hz : cayley w ∈ H := cayley_maps hw
  have hd := (hasDerivAt_S_to_K hf.1 hz).deriv
  rw [inv_cayley_cayley hw, cayley_add_I hw] at hd
  have hw1 : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
  have hb : ‖1 - w‖ ≤ 2 := (norm_sub_le 1 w).trans (by simpa using (show 1 + ‖w‖ ≤ 2 by linarith))
  have hb4 : ‖1 - w‖ ^ 4 ≤ (2 : ℝ) ^ 4 := pow_le_pow_left₀ (norm_nonneg _) hb 4
  have hz0 : 1 - w ≠ 0 := cayley_den_ne_zero hw
  have hnorm0 : ‖1 - w‖ ≠ 0 := norm_ne_zero_iff.mpr hz0
  have hdf0 : deriv f w ≠ 0 := Brennan.Koebe.univalent_deriv_ne_zero Metric.isOpen_ball ⟨hf.1, hf.2.1⟩ hw
  have ha : 0 < ‖deriv f w‖ := norm_pos_iff.mpr hdf0
  have hd_simp : deriv (S_to_K f) (cayley w) = deriv f w * (1 - w) ^ 2 := by
  {
    rw [hd]
    field_simp
    ring_nf
    simp [Complex.I_sq]
  }
  dsimp [S_to_KClass, A_weight, Q]
  rw [hd_simp, one_div, norm_inv, norm_mul, norm_pow, inv_pow,
    Real.rpow_neg (norm_nonneg _), Real.rpow_two]
  field_simp [ha.ne', hnorm0]
  nlinarith
}

def circlePoint (r θ : ℝ) : ℂ := (r : ℂ) * Complex.exp ((θ : ℂ) * I)

def arcInterval : Set ℝ := Icc (-Real.pi / 4) (Real.pi / 4)

def arcD (r θ : ℝ) : ℝ := 1 + 2 * r * Real.cos θ + r ^ 2

def arcX (r θ : ℝ) : ℝ := 2 * r * Real.sin θ / arcD r θ

def arcY (r θ : ℝ) : ℝ := (1 - r ^ 2) / arcD r θ

def arcXDeriv (r θ : ℝ) : ℝ := (4 * r ^ 2 + 2 * r * (1 + r ^ 2) * Real.cos θ) / (arcD r θ) ^ 2

lemma arc_cos_nonneg {θ : ℝ} (hθ : θ ∈ arcInterval) : 0 ≤ Real.cos θ := by
{
  apply Real.cos_nonneg_of_mem_Icc
  constructor <;> have hp := Real.pi_pos <;> dsimp [arcInterval] at hθ <;> linarith [hθ.1, hθ.2]
}

lemma arcD_bounds {r θ : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    1 ≤ arcD r θ ∧ arcD r θ ≤ (1 + r) ^ 2 ∧ arcD r θ ≤ 4 := by
{
  have hc := arc_cos_nonneg hθ
  have hc1 := Real.cos_le_one θ
  have hr0 : 0 ≤ r := by linarith
  have hr2 : 0 ≤ 2 * r := by positivity
  dsimp [arcD]
  have hm := mul_nonneg hr2 hc
  have hm1 := mul_le_mul_of_nonneg_left hc1 hr2
  refine ⟨by nlinarith [sq_nonneg r], by nlinarith, by nlinarith⟩
}

lemma arcX_bounds {r θ : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    arcX r θ ∈ Icc (-1) 1 := by
{
  have hd := arcD_bounds hr hr1 hθ
  have hD : 0 < arcD r θ := by linarith [hd.1]
  have hc := arc_cos_nonneg hθ
  have hs := Real.neg_one_le_sin θ
  have hs1 := Real.sin_le_one θ
  have h2r : 0 ≤ 2 * r := by linarith
  have hm1 := mul_le_mul_of_nonneg_left hs h2r
  have hm2 := mul_le_mul_of_nonneg_left hs1 h2r
  have hD2 : 2 * r ≤ arcD r θ := by
  {
    dsimp [arcD]
    nlinarith [mul_nonneg h2r hc, sq_nonneg (r - 1)]
  }
  exact ⟨(le_div_iff₀ hD).mpr (by nlinarith), (div_le_iff₀ hD).mpr (by nlinarith)⟩
}

lemma arcY_bounds {r θ : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    (1 - r) / 2 ≤ arcY r θ ∧ arcY r θ ≤ 2 * (1 - r) := by
{
  have hd := arcD_bounds hr hr1 hθ
  have hD : 0 < arcD r θ := by linarith [hd.1]
  have hr0 : 0 ≤ r := by linarith
  have hd0 : 0 ≤ 1 - r := by linarith
  constructor
  · apply (le_div_iff₀ hD).mpr
    have h := mul_le_mul_of_nonneg_left hd.2.1 (by positivity : 0 ≤ (1 - r) / 2)
    have hb : (1 - r) / 2 * (1 + r) ^ 2 ≤ 1 - r ^ 2 := by nlinarith [mul_nonneg hd0 (sq_nonneg (1 + r))]
    exact h.trans hb
  · apply (div_le_iff₀ hD).mpr
    have h := mul_le_mul_of_nonneg_left hd.1 (by positivity : 0 ≤ 2 * (1 - r))
    nlinarith [sq_nonneg (r - 1)]
}

lemma arcX_hasDerivAt {r θ : ℝ} (hD : arcD r θ ≠ 0) :
    HasDerivAt (arcX r) (arcXDeriv r θ) θ := by
{
  have hn := (Real.hasDerivAt_sin θ).const_mul (2 * r)
  have hd := (((Real.hasDerivAt_cos θ).const_mul (2 * r)).const_add 1).add_const (r ^ 2)
  have h := hn.div hd hD
  change HasDerivAt (arcX r) _ θ at h
  have he : arcXDeriv r θ =
      (2 * r * Real.cos θ * arcD r θ - 2 * r * Real.sin θ * (2 * r * -Real.sin θ)) / (arcD r θ) ^ 2 := by
  {
    unfold arcXDeriv arcD
    congr 1
    have hc := Real.sin_sq_add_cos_sq θ
    nlinarith [sq_nonneg r]
  }
  rw [he]
  exact h
}

lemma arcXDeriv_lower {r θ : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r < 1) (hθ : θ ∈ arcInterval) :
    1 / 16 ≤ arcXDeriv r θ := by
{
  have hd := arcD_bounds hr hr1 hθ
  have hD : 0 < arcD r θ := by linarith [hd.1]
  have hc := arc_cos_nonneg hθ
  dsimp only [arcXDeriv]
  apply (le_div_iff₀ (sq_pos_of_pos hD)).mpr
  have hm : 0 ≤ 2 * r * (1 + r ^ 2) * Real.cos θ := mul_nonneg (by positivity) hc
  have hsq : (arcD r θ) ^ 2 ≤ 16 := by nlinarith [hd.2.2]
  nlinarith [sq_nonneg (r - 1 / 2)]
}

lemma continuousOn_arcXDeriv {r : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r < 1) :
    ContinuousOn (arcXDeriv r) arcInterval := by
{
  apply ContinuousOn.div
  · fun_prop
  · unfold arcD
    fun_prop
  · intro θ hθ
    exact pow_ne_zero _ (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 hθ).1))
}

lemma arcX_monotone {r : ℝ} (hr : 1 / 2 ≤ r) (hr1 : r < 1) : MonotoneOn (arcX r) arcInterval := by
{
  apply monotoneOn_of_hasDerivWithinAt_nonneg (convex_Icc _ _)
  · intro θ hθ
    exact (arcX_hasDerivAt (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 hθ).1))).continuousAt.continuousWithinAt
  · intro θ hθ
    exact (arcX_hasDerivAt (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 (interior_subset hθ)).1))).hasDerivWithinAt
  · intro θ hθ
    exact le_trans (by norm_num) (arcXDeriv_lower hr hr1 (interior_subset hθ))
}

lemma circlePoint_norm (r θ : ℝ) : ‖circlePoint r θ‖ = |r| := by
{
  simp [circlePoint, Complex.norm_exp]
}

lemma circlePoint_re (r θ : ℝ) : (circlePoint r θ).re = r * Real.cos θ := by
{
  simp [circlePoint, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
}

lemma circlePoint_im (r θ : ℝ) : (circlePoint r θ).im = r * Real.sin θ := by
{
  simp [circlePoint, Complex.exp_mul_I, ← Complex.ofReal_cos, ← Complex.ofReal_sin]
}

lemma one_add_circlePoint_norm_sq (r θ : ℝ) : ‖1 + circlePoint r θ‖ ^ 2 = arcD r θ := by
{
  rw [Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.add_re, Complex.add_im, Complex.one_re, Complex.one_im,
    circlePoint_re, circlePoint_im, zero_add]
  dsimp [arcD]
  nlinarith [Real.sin_sq_add_cos_sq θ, sq_nonneg r]
}

lemma circlePoint_mem_disk {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    circlePoint r θ ∈ Metric.ball (0 : ℂ) 1 := by
{
  simpa [Metric.mem_ball, dist_zero_right, circlePoint_norm, abs_of_nonneg hr] using hr1
}

lemma neg_circlePoint_mem_disk {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    -circlePoint r θ ∈ Metric.ball (0 : ℂ) 1 := by
{
  simpa only [Metric.mem_ball, dist_zero_right, norm_neg] using circlePoint_mem_disk hr hr1 θ
}

lemma cayley_re (z : ℂ) : (cayley z).re = -2 * z.im / ‖1 - z‖ ^ 2 := by
{
  simp only [cayley, Complex.div_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.sub_re, Complex.sub_im, Complex.sq_norm, Complex.normSq_apply]
  ring
}

lemma cayley_neg_circlePoint {r : ℝ} (hr : 0 ≤ r) (_hr1 : r < 1) (θ : ℝ) :
    cayley (-circlePoint r θ) = (arcX r θ : ℂ) + (arcY r θ : ℂ) * I := by
{
  apply Complex.ext
  · rw [cayley_re]
    simp only [Complex.neg_im, circlePoint_im, sub_neg_eq_add, one_add_circlePoint_norm_sq,
      Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.ofReal_im, Complex.I_im]
    dsimp [arcX]
    ring
  · rw [cayley_im]
    simp only [norm_neg, circlePoint_norm, abs_of_nonneg hr, sub_neg_eq_add, one_add_circlePoint_norm_sq,
      Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.ofReal_re, Complex.I_im]
    simp [arcY]
}

lemma A_weight_vertical_bound (F : KClass) {η : ℝ} (hη : 1 / 2 ≤ η) (hη4 : η ≤ 4) :
    A_weight ((0 : ℂ) + (η : ℂ) * I) F.F ≤ 1562500 := by
{
  have hη0 : 0 < η := by linarith
  have hzH : (0 : ℂ) + (η : ℂ) * I ∈ H := by dsimp [H]; simp [hη0]
  have hb := norm_Q_le_general F hzH
  have hre : ((0 : ℂ) + (η : ℂ) * I).re = 0 := by simp
  have him : ((0 : ℂ) + (η : ℂ) * I).im = η := by simp
  rw [hre, him] at hb
  have hp : (0 ^ 2 + (η + 1) ^ 2) ^ 2 ≤ (5 : ℝ) ^ 4 := by
  {
    have hinner : 0 ^ 2 + (η + 1) ^ 2 ≤ (5 : ℝ) ^ 2 := by nlinarith
    have hinner0 : 0 ≤ (0 : ℝ) ^ 2 + (η + 1) ^ 2 := by positivity
    nlinarith
  }
  have ht : ‖Q F.F ((0 : ℂ) + (η : ℂ) * I)‖ ≤ 1250 := by
  {
    apply hb.trans
    apply (div_le_iff₀ hη0).mpr
    norm_num at hp
    linarith
  }
  dsimp [A_weight]
  nlinarith [norm_nonneg (Q F.F ((0 : ℂ) + (η : ℂ) * I))]
}

lemma A_weight_vertical_compare (F : KClass) (x v y : ℝ) (hv : 0 < v)
    (hy : v / 2 ≤ y) (hy4 : y ≤ 4 * v) :
    A_weight ((x : ℂ) + (y : ℂ) * I) F.F ≤
      1562500 * A_weight ((x : ℂ) + (v : ℂ) * I) F.F := by
{
  have hη : 1 / 2 ≤ y / v := (le_div_iff₀ hv).mpr (by linarith)
  have hη4 : y / v ≤ 4 := (div_le_iff₀ hv).mpr hy4
  have hη0 : 0 < y / v := by linarith
  have hzv : (x : ℂ) + (v : ℂ) * I ∈ H := by dsimp [H]; simp [hv]
  have hzη : (0 : ℂ) + ((y / v : ℝ) : ℂ) * I ∈ H := by dsimp [H]; simp [hη0]
  have he : aff ((x : ℂ) + (v : ℂ) * I) ((0 : ℂ) + ((y / v : ℝ) : ℂ) * I) =
      (x : ℂ) + (y : ℂ) * I := by
  {
    apply Complex.ext <;> simp [aff, mul_div_cancel₀ y hv.ne']
  }
  have hc := A_weight_cocycle F ((x : ℂ) + (v : ℂ) * I) ((0 : ℂ) + ((y / v : ℝ) : ℂ) * I) hzv hzη
  rw [he] at hc
  rw [← hc, mul_comm (1562500 : ℝ)]
  exact mul_le_mul_of_nonneg_left
    (A_weight_vertical_bound (T_elem F ((x : ℂ) + (v : ℂ) * I) hzv) hη hη4) (sq_nonneg _)
}

lemma continuous_horizontalWeight (v : ℝ) (hv : 0 < v) (F : KClass) :
    Continuous (fun x : ℝ => A_weight ((x : ℂ) + (v : ℂ) * I) F.F) := by
{
  let γ : ℝ → ℂ := fun x => (x : ℂ) + (v : ℂ) * I
  have hγ : Continuous γ := by fun_prop
  have hγH : ∀ x : ℝ, γ x ∈ H := by
  {
    intro x
    dsimp [H, γ]
    simp [hv]
  }
  have hdF : ContinuousOn (deriv F.F) H := (F.univalent.1.deriv isOpen_H).continuousOn
  have hdγ : Continuous (fun x : ℝ => deriv F.F (γ x)) := hdF.comp_continuous hγ hγH
  have hne : ∀ x : ℝ, deriv F.F (γ x) ≠ 0 :=
    fun x => deriv_ne_zero_of_univalentOn isOpen_H F.univalent (hγH x)
  dsimp [A_weight, Q]
  exact ((continuous_const.div hdγ hne).norm).pow 2
}

def horizontalMass (v : ℝ) (F : KClass) : ℝ :=
  ∫ x in (-1 : ℝ)..1, A_weight ((x : ℂ) + (v : ℂ) * I) F.F

lemma A_weight_horizontal_one_le (F : KClass) {x : ℝ} (hx : x ∈ Icc (-1 : ℝ) 1) :
    A_weight ((x : ℂ) + ((1 : ℝ) : ℂ) * I) F.F ≤ 625 := by
{
  have hx_abs : |x| ≤ 1 := abs_le.mpr hx
  have hQ := lemma_2_2_bounds F x 1 1 zero_lt_one le_rfl hx_abs
  have h25 : ((1 : ℝ) ^ 2 + 4) ^ 2 / (1 : ℝ) = 25 := by norm_num
  rw [h25] at hQ
  rw [A_weight]
  nlinarith [norm_nonneg (Q F.F ((x : ℂ) + ((1 : ℝ) : ℂ) * I))]
}

lemma horizontalMass_one_le (F : KClass) : horizontalMass 1 F ≤ 1250 := by
{
  rw [horizontalMass]
  have hab : (-1 : ℝ) ≤ 1 := by norm_num
  have hi := intervalIntegral.integral_mono_on hab
    ((continuous_horizontalWeight 1 zero_lt_one F).intervalIntegrable (μ := volume) _ _)
    (intervalIntegrable_const (μ := volume)) (fun x hx => A_weight_horizontal_one_le F hx)
  rw [intervalIntegral.integral_const, smul_eq_mul] at hi
  linarith
}

lemma horizontalMass_half_left (v : ℝ) (hv : 0 < v) (F : KClass) (x : ℝ) :
    A_weight (-1/2 + I/2) F.F *
      A_weight ((x : ℂ) + (v : ℂ) * I) (T_elem F (-1/2 + I/2) L_op_left_H).F =
    A_weight ((((1 / 2 : ℝ) * x + (-1 / 2 : ℝ) : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I) F.F := by
{
  have hzv : (x : ℂ) + (v : ℂ) * I ∈ H := by dsimp [H]; simp [hv]
  rw [T_elem, A_weight_cocycle F (-1/2 + I/2) ((x : ℂ) + (v : ℂ) * I) L_op_left_H hzv]
  congr 1
  apply Complex.ext <;> simp [aff] <;> ring
}

lemma horizontalMass_half_right (v : ℝ) (hv : 0 < v) (F : KClass) (x : ℝ) :
    A_weight (1/2 + I/2) F.F *
      A_weight ((x : ℂ) + (v : ℂ) * I) (T_elem F (1/2 + I/2) L_op_right_H).F =
    A_weight ((((1 / 2 : ℝ) * x + (1 / 2 : ℝ) : ℝ) : ℂ) + ((v / 2 : ℝ) : ℂ) * I) F.F := by
{
  have hzv : (x : ℂ) + (v : ℂ) * I ∈ H := by dsimp [H]; simp [hv]
  rw [T_elem, A_weight_cocycle F (1/2 + I/2) ((x : ℂ) + (v : ℂ) * I) L_op_right_H hzv]
  congr 1
  apply Complex.ext <;> simp [aff] <;> ring
}

lemma horizontalMass_half (v : ℝ) (hv : 0 < v) (F : KClass) :
    horizontalMass (v / 2) F =
      (1 / 2 : ℝ) * (A_weight (-1/2 + I/2) F.F *
          horizontalMass v (T_elem F (-1/2 + I/2) L_op_left_H) +
        A_weight (1/2 + I/2) F.F *
          horizontalMass v (T_elem F (1/2 + I/2) L_op_right_H)) := by
{
  dsimp [horizontalMass]
  rw [← intervalIntegral.integral_const_mul, ← intervalIntegral.integral_const_mul]
  simp_rw [horizontalMass_half_left v hv F, horizontalMass_half_right v hv F]
  let g : ℝ → ℝ := fun x => A_weight ((x : ℂ) + ((v / 2 : ℝ) : ℂ) * I) F.F
  have hl := intervalIntegral.integral_comp_mul_add (f := g)
    (a := (-1 : ℝ)) (b := 1) (by norm_num : (1 / 2 : ℝ) ≠ 0) (-1 / 2 : ℝ)
  have hr := intervalIntegral.integral_comp_mul_add (f := g)
    (a := (-1 : ℝ)) (b := 1) (by norm_num : (1 / 2 : ℝ) ≠ 0) (1 / 2 : ℝ)
  rw [smul_eq_mul] at hl hr
  have hl' : (∫ x in (-1 : ℝ)..1, g ((1 / 2 : ℝ) * x + (-1 / 2 : ℝ))) =
      2 * ∫ x in (-1 : ℝ)..0, g x := by
  {
    convert hl using 2 <;> norm_num
  }
  have hr' : (∫ x in (-1 : ℝ)..1, g ((1 / 2 : ℝ) * x + (1 / 2 : ℝ))) =
      2 * ∫ x in (0 : ℝ)..1, g x := by
  {
    convert hr using 2 <;> norm_num
  }
  have hi := (continuous_horizontalWeight (v / 2) (by positivity) F).intervalIntegrable (μ := volume)
  have hs := intervalIntegral.integral_add_adjacent_intervals (hi (-1) 0) (hi 0 1)
  change ∫ x in (-1 : ℝ)..1, g x =
    (1 / 2 : ℝ) * ((∫ x in (-1 : ℝ)..1, g ((1 / 2 : ℝ) * x + (-1 / 2 : ℝ))) +
      ∫ x in (-1 : ℝ)..1, g ((1 / 2 : ℝ) * x + (1 / 2 : ℝ)))
  rw [hl', hr']
  dsimp [g] at hs ⊢
  linarith [hs]
}

lemma horizontalMass_dyadic (n : ℕ) (F : KClass) :
    horizontalMass (v_n n) F = L_pow_real n (horizontalMass 1) F := by
{
  induction n generalizing F with
  | zero =>
    rw [v_n_zero, L_pow_real_zero]
  | succ n ih =>
    rw [v_n_succ, show (1 / 2 : ℝ) * v_n n = v_n n / 2 by ring,
      horizontalMass_half (v_n n) (v_n_pos n) F, ih, ih, ← L_pow_real_succ]
}

lemma horizontalMass_dyadic_le (n : ℕ) (F : KClass) :
    horizontalMass (v_n n) F ≤ 1250 * L_norm n := by
{
  rw [horizontalMass_dyadic]
  exact (L_pow_real_le_mul_L_one n (horizontalMass 1) 1250 horizontalMass_one_le F).trans
    (mul_le_mul_of_nonneg_left (le_L_norm n F) (by norm_num))
}

lemma continuous_circlePoint (r : ℝ) : Continuous (circlePoint r) := by
{
  unfold circlePoint
  fun_prop
}

lemma continuous_circle_deriv_rpow {f : ℂ → ℂ} (hf : UnivalentOn f (Metric.ball 0 1))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    Continuous (fun θ => ‖deriv f (circlePoint r θ)‖ ^ t) := by
{
  have hc : Continuous (fun θ => deriv f (circlePoint r θ)) :=
    ((hf.1.deriv Metric.isOpen_ball).continuousOn).comp_continuous (continuous_circlePoint r)
      (circlePoint_mem_disk hr hr1)
  exact hc.norm.rpow_const (fun θ => Or.inl (norm_ne_zero_iff.mpr
    (deriv_ne_zero_of_univalentOn Metric.isOpen_ball hf (circlePoint_mem_disk hr hr1 θ))))
}

lemma continuous_neg_circle_deriv_rpow {f : ℂ → ℂ} (hf : UnivalentOn f (Metric.ball 0 1))
    {r : ℝ} (hr : 0 ≤ r) (hr1 : r < 1) (t : ℝ) :
    Continuous (fun θ => ‖deriv f (-circlePoint r θ)‖ ^ t) := by
{
  have hc : Continuous (fun θ => deriv f (-circlePoint r θ)) :=
    ((hf.1.deriv Metric.isOpen_ball).continuousOn).comp_continuous (continuous_circlePoint r).neg
      (neg_circlePoint_mem_disk hr hr1)
  exact hc.norm.rpow_const (fun θ => Or.inl (norm_ne_zero_iff.mpr
    (deriv_ne_zero_of_univalentOn Metric.isOpen_ball hf (neg_circlePoint_mem_disk hr hr1 θ))))
}

lemma arc_integrand_bound {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {r v : ℝ}
    (hr : 1 / 2 ≤ r) (hr1 : r < 1) (hv : 0 < v) (hvδ : v ≤ 1 - r) (hδv : 1 - r ≤ 2 * v)
    {θ : ℝ} (hθ : θ ∈ arcInterval) :
    ‖deriv f (-circlePoint r θ)‖ ^ (-2 : ℝ) ≤
      400000000 * (A_weight ((arcX r θ : ℂ) + (v : ℂ) * I) (S_to_KClass f hf).F * arcXDeriv r θ) := by
{
  have hy := arcY_bounds hr hr1 hθ
  have hc := inverse_deriv_square_conversion hf (neg_circlePoint_mem_disk (by linarith) hr1 θ)
  rw [cayley_neg_circlePoint (by linarith) hr1 θ] at hc
  have hb := A_weight_vertical_compare (S_to_KClass f hf) (arcX r θ) v (arcY r θ) hv
    (by linarith) (by linarith)
  have hd := arcXDeriv_lower hr hr1 hθ
  have hWp : 0 ≤ A_weight ((arcX r θ : ℂ) + (v : ℂ) * I) (S_to_KClass f hf).F := sq_nonneg _
  have hm := mul_nonneg hWp (sub_nonneg.mpr hd)
  nlinarith
}

lemma arc_integral_bound {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {r v : ℝ}
    (hr : 1 / 2 ≤ r) (hr1 : r < 1) (hv : 0 < v) (hvδ : v ≤ 1 - r) (hδv : 1 - r ≤ 2 * v) :
    (∫ θ in (-Real.pi / 4)..(Real.pi / 4), ‖deriv f (-circlePoint r θ)‖ ^ (-2 : ℝ)) ≤
      400000000 * horizontalMass v (S_to_KClass f hf) := by
{
  let F := S_to_KClass f hf
  let W : ℝ → ℝ := fun x => A_weight ((x : ℂ) + (v : ℂ) * I) F.F
  have hW : Continuous W := continuous_horizontalWeight v hv F
  have hab : -Real.pi / 4 ≤ Real.pi / 4 := by linarith [Real.pi_pos]
  have hu : uIcc (-Real.pi / 4) (Real.pi / 4) = arcInterval := uIcc_of_le hab
  have hX (θ : ℝ) (hθ : θ ∈ arcInterval) : HasDerivAt (arcX r) (arcXDeriv r θ) θ :=
    arcX_hasDerivAt (ne_of_gt (lt_of_lt_of_le zero_lt_one (arcD_bounds hr hr1 hθ).1))
  have hXc : ContinuousOn (arcX r) arcInterval :=
    fun θ hθ => (hX θ hθ).continuousAt.continuousWithinAt
  have hprod : ContinuousOn (fun θ => W (arcX r θ) * arcXDeriv r θ) arcInterval :=
    (hW.comp_continuousOn hXc).mul (continuousOn_arcXDeriv hr hr1)
  have hi := intervalIntegral.integral_mono_on hab
    ((continuous_neg_circle_deriv_rpow ⟨hf.1, hf.2.1⟩ (by linarith) hr1 (-2)).intervalIntegrable (μ := volume) _ _)
    ((hprod.const_mul 400000000).intervalIntegrable_of_Icc hab)
    (fun θ hθ => arc_integrand_bound hf hr hr1 hv hvδ hδv hθ)
  rw [intervalIntegral.integral_const_mul] at hi
  have hchange := intervalIntegral.integral_comp_mul_deriv
    (fun θ hθ => hX θ (hu ▸ hθ)) (hu ▸ continuousOn_arcXDeriv hr hr1) hW
  change (∫ θ in (-Real.pi / 4)..(Real.pi / 4), W (arcX r θ) * arcXDeriv r θ) = _ at hchange
  rw [hchange] at hi
  have hlo : -Real.pi / 4 ∈ arcInterval := ⟨le_rfl, hab⟩
  have hhi : Real.pi / 4 ∈ arcInterval := ⟨hab, le_rfl⟩
  have hm := arcX_monotone hr hr1 hlo hhi hab
  have hb := intervalIntegral.integral_mono_interval (arcX_bounds hr hr1 hlo).1 hm
    (arcX_bounds hr hr1 hhi).2
    (Eventually.of_forall (fun _ => sq_nonneg _))
    (hW.intervalIntegrable (μ := volume) (-1) 1)
  exact hi.trans (mul_le_mul_of_nonneg_left hb (by norm_num))
}

lemma arc_integral_dyadic_bound {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {r : ℝ}
    (hr : 1 / 2 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hvδ : v_n n ≤ 1 - r) (hδv : 1 - r ≤ 2 * v_n n) :
    (∫ θ in (-Real.pi / 4)..(Real.pi / 4), ‖deriv f (-circlePoint r θ)‖ ^ (-2 : ℝ)) ≤
      (400000000 * 1250) * L_norm n := by
{
  have hb := arc_integral_bound hf hr hr1 (v_n_pos n) hvδ hδv
  have hm := horizontalMass_dyadic_le n (S_to_KClass f hf)
  linarith
}

def rotateDisk (f : ℂ → ℂ) (α z : ℂ) : ℂ := f (α * z) / α

lemma rotateDisk_maps {α : ℂ} (hα : ‖α‖ = 1) :
    MapsTo (fun z => α * z) (Metric.ball 0 1) (Metric.ball 0 1) := by
{
  intro z hz
  simpa [Metric.mem_ball, dist_zero_right, norm_mul, hα] using hz
}

lemma rotateDisk_hasDerivAt {f : ℂ → ℂ} (hf : DifferentiableOn ℂ f (Metric.ball 0 1))
    {α z : ℂ} (hα : ‖α‖ = 1) (hz : z ∈ Metric.ball 0 1) :
    HasDerivAt (rotateDisk f α) (deriv f (α * z)) z := by
{
  have hα0 : α ≠ 0 := by
  {
    intro h
    simp [h] at hα
  }
  have hd := ((hf _ (rotateDisk_maps hα hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (rotateDisk_maps hα hz))).hasDerivAt
  convert (hd.comp z ((hasDerivAt_id z).const_mul α)).div_const α using 1 <;> try rfl
  simp [hα0]
}

lemma rotateDisk_isClassS {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f)
    {α : ℂ} (hα : ‖α‖ = 1) : Brennan.Koebe.IsClassS (rotateDisk f α) := by
{
  have hα0 : α ≠ 0 := by
  {
    intro h
    simp [h] at hα
  }
  refine ⟨fun z hz => (rotateDisk_hasDerivAt hf.1 hα hz).differentiableAt.differentiableWithinAt,
    ?_, ?_, ?_⟩
  · intro z hz w hw he
    exact mul_left_cancel₀ hα0 (hf.2.1 (rotateDisk_maps hα hz) (rotateDisk_maps hα hw)
      ((div_left_inj' hα0).mp he))
  · simp [rotateDisk, hf.2.2.1]
  · rw [(rotateDisk_hasDerivAt hf.1 hα (by simp : (0 : ℂ) ∈ Metric.ball 0 1)).deriv]
    simpa using hf.2.2.2
}

lemma circlePoint_shift (r θ c : ℝ) :
    (-Complex.exp ((c : ℂ) * I)) * (-circlePoint r θ) = circlePoint r (θ + c) := by
{
  simp only [circlePoint, Complex.ofReal_add, add_mul, Complex.exp_add, neg_mul_neg]
  ring
}

lemma circle_arc_dyadic_bound {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {r : ℝ}
    (hr : 1 / 2 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hvδ : v_n n ≤ 1 - r) (hδv : 1 - r ≤ 2 * v_n n) (c : ℝ) :
    (∫ θ in (c - Real.pi / 4)..(c + Real.pi / 4), ‖deriv f (circlePoint r θ)‖ ^ (-2 : ℝ)) ≤
      (400000000 * 1250) * L_norm n := by
{
  let α := -Complex.exp ((c : ℂ) * I)
  have hα : ‖α‖ = 1 := by simp [α, Complex.norm_exp]
  have hb := arc_integral_dyadic_bound (rotateDisk_isClassS hf hα) hr hr1 n hvδ hδv
  have he (θ : ℝ) : deriv (rotateDisk f α) (-circlePoint r θ) = deriv f (circlePoint r (θ + c)) := by
  {
    rw [(rotateDisk_hasDerivAt hf.1 hα (neg_circlePoint_mem_disk (by linarith) hr1 θ)).deriv]
    rw [show α * (-circlePoint r θ) = circlePoint r (θ + c) from circlePoint_shift r θ c]
  }
  simp_rw [he] at hb
  rw [intervalIntegral.integral_comp_add_right (f := fun θ => ‖deriv f (circlePoint r θ)‖ ^ (-2 : ℝ)) c] at hb
  convert hb using 1
  congr 1 <;> ring
}

lemma periodic_circlePoint (r : ℝ) : Function.Periodic (circlePoint r) (2 * Real.pi) := by
{
  simpa [circlePoint, circleMap] using periodic_circleMap (0 : ℂ) r
}

lemma full_circle_dyadic_bound {f : ℂ → ℂ} (hf : Brennan.Koebe.IsClassS f) {r : ℝ}
    (hr : 1 / 2 ≤ r) (hr1 : r < 1) (n : ℕ)
    (hvδ : v_n n ≤ 1 - r) (hδv : 1 - r ≤ 2 * v_n n) :
    (∫ θ in -Real.pi..Real.pi, ‖deriv f (circlePoint r θ)‖ ^ (-2 : ℝ)) ≤
      (1600000000 * 1250) * L_norm n := by
{
  let G : ℝ → ℝ := fun θ => ‖deriv f (circlePoint r θ)‖ ^ (-2 : ℝ)
  have hG := (continuous_circle_deriv_rpow ⟨hf.1, hf.2.1⟩ (by linarith) hr1 (-2)).intervalIntegrable (μ := volume)
  have hper : Function.Periodic G (2 * Real.pi) :=
    (periodic_circlePoint r).comp (fun z => ‖deriv f z‖ ^ (-2 : ℝ))
  have hshift := hper.intervalIntegral_add_eq (-Real.pi) (-Real.pi / 4)
  have h1 := circle_arc_dyadic_bound hf hr hr1 n hvδ hδv 0
  have h2 := circle_arc_dyadic_bound hf hr hr1 n hvδ hδv (Real.pi / 2)
  have h3 := circle_arc_dyadic_bound hf hr hr1 n hvδ hδv Real.pi
  have h4 := circle_arc_dyadic_bound hf hr hr1 n hvδ hδv (3 * Real.pi / 2)
  have e1 : (0 : ℝ) - Real.pi / 4 = -Real.pi / 4 := by ring
  have e2 : (0 : ℝ) + Real.pi / 4 = Real.pi / 4 := by ring
  have e3 : Real.pi / 2 - Real.pi / 4 = Real.pi / 4 := by ring
  have e4 : Real.pi / 2 + Real.pi / 4 = 3 * Real.pi / 4 := by ring
  have e5 : Real.pi - Real.pi / 4 = 3 * Real.pi / 4 := by ring
  have e6 : Real.pi + Real.pi / 4 = 5 * Real.pi / 4 := by ring
  have e7 : 3 * Real.pi / 2 - Real.pi / 4 = 5 * Real.pi / 4 := by ring
  have e8 : 3 * Real.pi / 2 + Real.pi / 4 = 7 * Real.pi / 4 := by ring
  rw [e1, e2] at h1
  rw [e3, e4] at h2
  rw [e5, e6] at h3
  rw [e7, e8] at h4
  have ha := intervalIntegral.integral_add_adjacent_intervals (hG (-Real.pi / 4) (Real.pi / 4)) (hG (Real.pi / 4) (3 * Real.pi / 4))
  have hb := intervalIntegral.integral_add_adjacent_intervals (hG (-Real.pi / 4) (3 * Real.pi / 4)) (hG (3 * Real.pi / 4) (5 * Real.pi / 4))
  have hc := intervalIntegral.integral_add_adjacent_intervals (hG (-Real.pi / 4) (5 * Real.pi / 4)) (hG (5 * Real.pi / 4) (7 * Real.pi / 4))
  have es1 : -Real.pi + 2 * Real.pi = Real.pi := by ring
  have es2 : -Real.pi / 4 + 2 * Real.pi = 7 * Real.pi / 4 := by ring
  rw [es1, es2] at hshift
  dsimp only [G] at hshift
  linarith
}

lemma dyadic_growth_compare {a δ : ℝ} (ha : 0 ≤ a) (hδ : 0 < δ) {n : ℕ}
    (hn : δ ≤ 2 * v_n n) :
    ((2 : ℝ) ^ a) ^ n ≤ (2 : ℝ) ^ a * δ ^ (-a) := by
{
  rw [v_n_eq_half_pow] at hn
  have he : ((2 : ℝ) ^ a) ^ n = ((1 / 2 : ℝ) ^ n) ^ (-a) := by
  {
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_natCast (1 / 2 : ℝ),
      ← Real.rpow_mul (by norm_num)]
    rw [show (1 / 2 : ℝ) = 2 ^ (-1 : ℝ) by norm_num, ← Real.rpow_mul (by norm_num)]
    congr 1
    ring
  }
  rw [he]
  have hb := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < δ / 2)
    (show δ / 2 ≤ (1 / 2 : ℝ) ^ n by linarith) (neg_nonpos.mpr ha)
  refine hb.trans_eq ?_
  rw [Real.div_rpow hδ.le (by norm_num), Real.rpow_neg (by norm_num : (0 : ℝ) ≤ 2),
    div_inv_eq_mul, mul_comm]
}

/-- Circular integral mean `M_t[f'](r)` on `|z| = r`. -/
def integralMean (f : ℂ → ℂ) (t r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi,
    ‖deriv f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ t

/-- Proposition 2.4 (Uniform disk comparison). -/
theorem prop_2_4_uniform_disk_comparison :
    rho ≤ 2 →
    ∀ ε > 0, ∃ C_ε : ℝ, ∀ (f : ℂ → ℂ) (_hf : Brennan.Koebe.IsClassS f) (r : ℝ),
      (1 / 2 : ℝ) ≤ r ∧ r < 1 →
      integralMean f (-2) r ≤ C_ε * (1 - r) ^ ((-1 : ℝ) - ε) := by
{
  intro h_rho ε hε
  have hlam : 2 < (2 : ℝ) ^ (1 + ε) := by
  {
    simpa only [Real.rpow_one] using
      Real.rpow_lt_rpow_of_exponent_lt (by norm_num) (by linarith : (1 : ℝ) < 1 + ε)
  }
  obtain ⟨K, hK, hKn⟩ := L_norm_uniform_growth h_rho hlam
  let A := (2 * Real.pi)⁻¹ * (1600000000 * 1250) * K * (2 : ℝ) ^ (1 + ε)
  refine ⟨A + 1, fun f hf r ⟨hr, hr1⟩ => ?_⟩
  obtain ⟨n, hn1, hn2⟩ := exists_nat_pow_near_of_lt_one (by linarith : 0 < 1 - r)
    (by linarith : 1 - r ≤ 1) (by norm_num : (0 : ℝ) < 1 / 2) (by norm_num : (1 / 2 : ℝ) < 1)
  have hvδ : v_n (n + 1) ≤ 1 - r := by rw [v_n_eq_half_pow]; exact hn1.le
  have hn : 1 - r ≤ 2 * v_n (n + 1) := by rw [v_n_eq_half_pow, pow_succ]; nlinarith
  have hb := full_circle_dyadic_bound hf hr hr1 (n + 1) hvδ hn
  have hc := dyadic_growth_compare (by linarith : 0 ≤ 1 + ε) (by linarith : 0 < 1 - r) hn
  have hx : 0 ≤ (2 * Real.pi)⁻¹ := by positivity
  have hy : 0 ≤ (1600000000 * 1250 : ℝ) := by positivity
  have he : ((-1 : ℝ) - ε) = -(1 + ε) := by ring
  change (2 * Real.pi)⁻¹ * (∫ θ in -Real.pi..Real.pi, ‖deriv f (circlePoint r θ)‖ ^ (-2 : ℝ)) ≤ _
  calc
    _ ≤ (2 * Real.pi)⁻¹ * ((1600000000 * 1250) * L_norm (n + 1)) :=
      mul_le_mul_of_nonneg_left hb hx
    _ ≤ (2 * Real.pi)⁻¹ * ((1600000000 * 1250) * (K * ((2 : ℝ) ^ (1 + ε)) ^ (n + 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (hKn (n + 1)) hy) hx
    _ ≤ (2 * Real.pi)⁻¹ * ((1600000000 * 1250) * (K * ((2 : ℝ) ^ (1 + ε) * (1 - r) ^ (-(1 + ε))))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hc hK.le) hy) hx
    _ = A * (1 - r) ^ ((-1 : ℝ) - ε) := by rw [he]; dsimp [A]; ring
    _ ≤ (A + 1) * (1 - r) ^ ((-1 : ℝ) - ε) :=
      mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg (by linarith) _)
}

end Brennan.Section2_Dyadic
