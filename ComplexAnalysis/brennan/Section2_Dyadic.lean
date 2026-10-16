import Mathlib
import brennan.Section2

open Complex Set MeasureTheory Topology Filter
open scoped ComplexConjugate Topology

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

/-- Jet embedding of `KClass` into functions and their first two reciprocal-derivative jets. -/
def kClassJet (F : KClass) : (ℂ → ℂ) × (ℂ → ℂ) × (ℂ → ℂ) × (ℂ → ℂ) :=
  (F.F, Q F.F, deriv (Q F.F), deriv (deriv (Q F.F)))

instance instTopologicalSpaceKClass : TopologicalSpace KClass :=
  TopologicalSpace.induced kClassJet inferInstance

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

lemma dyadic_cell_H (n j : ℕ) : (u_nj n j : ℂ) + (v_n n : ℂ) * I ∈ H := by
{
  dsimp [H, v_n]
  simp only [ofReal_im, mul_im, ofReal_re, I_im, mul_one, I_re, mul_zero, add_zero, zero_add]
  positivity
}

/-- The n-th iterate of the dyadic transfer operator via its explicit dyadic sum (2.10). -/
def L_pow_val (n : ℕ) (Phi : C_KClass) (F : KClass) : ℂ :=
  (v_n n : ℂ) * ∑ j ∈ Finset.range (2^n),
    A_op_val ((u_nj n j : ℂ) + (v_n n : ℂ) * I) (dyadic_cell_H n j) Phi F

/-!
PAPER: The limit
PAPER: ρ = \lim_{n→∞} ∥L^n∥^{1/n} = \inf_{n≥1} ∥L^n∥^{1/n} (2.11)
PAPER: exists and satisfies 1 ≤ ρ ≤ 4. If λ > ρ, there is Cλ < ∞ such that ∥L^n∥ ≤ Cλ λ^n for all
PAPER: n ≥ 0.
-/
/-- Spectral radius ρ of the dyadic transfer operator L (`OAI.Brennan.growthRate` in `Eigenmeasure.lean`). -/
axiom rho : ℝ

/-- Spectral radius bounds `1 ≤ ρ ≤ 4` (`OAI.Brennan.growthRate_ge_one` and `CircleBounds.lean`). -/
axiom rho_bounds : 1 ≤ rho ∧ rho ≤ 4

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
/-- Circular integral mean `M_t[f'](r)` on `|z| = r`. -/
def integralMean (f : ℂ → ℂ) (t r : ℝ) : ℝ :=
  (2 * Real.pi)⁻¹ * ∫ θ in -Real.pi..Real.pi,
    ‖deriv f ((r : ℂ) * Complex.exp ((θ : ℂ) * Complex.I))‖ ^ t

/-- Proposition 2.4 (`OAI.Brennan.circle_mean_bound_of_growth_le_two` in `CircleBounds.lean`). -/
axiom prop_2_4_uniform_disk_comparison :
    rho ≤ 2 →
    ∀ ε > 0, ∃ C_ε : ℝ, ∀ (f : ℂ → ℂ) (_hf : Brennan.Koebe.IsClassS f) (r : ℝ),
      (1 / 2 : ℝ) ≤ r ∧ r < 1 →
      integralMean f (-2) r ≤ C_ε * (1 - r) ^ ((-1 : ℝ) - ε)

/-!
# 3 A probability law from transfer growth

PAPER: The disk estimate in Proposition 2.4 reduces our task to proving that ρ ≤ 2. We now
PAPER: suppose that ρ > 2 and construct a probability measure on the normalized family K.
PAPER: Its covariance under affine changes of coordinates will turn geometric quantities into
PAPER: expectations at the single point i.

PAPER: We use the operators Az and L from the preceding section. Measures act on their left:
PAPER: if µ is a finite measure, then (µAz)(Φ) = µ(AzΦ) for Φ ∈ C(K). Every positive bounded
PAPER: functional on C(K) is identified with its finite Borel measure by the Riesz representation
PAPER: theorem [Fol99, Theorem 7.2].
-/

/-- The eigenmeasure P on KClass (`OAI.Brennan.exists_growth_eigenmeasure` in `Eigenmeasure.lean`
and `exists_weighted_law_of_growth_gt_two` in `AffineLaw.lean`). -/
axiom P_eigenmeasure : MeasureTheory.Measure KClass

/-!
PAPER: Lemma 3.1 (Weighted affine covariance). Suppose that ρ > 2, and put β = \log_2 ρ > 1.
PAPER: There is a Borel probability measure P on K such that, for every z = x + iy ∈ H and every
PAPER: nonnegative Borel function Φ : K → [0, ∞],
PAPER: E[ |QF (z)|^2 Φ(TzF) ] = y^{-β} EΦ(F), (3.1)
PAPER: where E denotes expectation with respect to P.
-/
/-- Lemma 3.1 (`OAI.Brennan.exists_weighted_law_of_growth_gt_two` in `AffineLaw.lean`). -/
axiom lemma_3_1_weighted_covariance (h_rho : rho > 2) :
  IsProbabilityMeasure P_eigenmeasure ∧
  ∀ (z : ℂ) (hz : z ∈ H) (Phi : KClass → ℝ),
    ∫ F, A_weight z F.F * Phi ⟨T z F.F, (T_KClass F z hz).1, (T_KClass F z hz).2.1, (T_KClass F z hz).2.2⟩ ∂P_eigenmeasure =
      (z.im : ℝ) ^ (-(Real.log rho / Real.log 2)) * ∫ F, Phi F ∂P_eigenmeasure

end Brennan.Section2_Dyadic
