import Mathlib
import brennan.Section3

open Complex Set MeasureTheory Topology Filter Classical
open scoped ComplexConjugate Topology

noncomputable section

namespace Brennan.Sections4and5

open Brennan.Section2
open Brennan.Section2_Dyadic
open Brennan.Section3

variable {rho : ℝ} (h_rho : rho > 2)
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

-- The target potential function V^F_ξ(z)
def V_target (beta : ℝ) (F : KClass) (xi : ℂ) (z : ℂ) : ℝ :=
  ((z.im : ℝ) ^ (k_val beta)) / ‖F.F z - xi‖

/-!
PAPER: Proposition 4.1 (Compact positive superlevels). For P-almost every F ∈ K, for planar
PAPER: area-almost every ξ ∈ C, the set
PAPER: {z ∈ H : V^F_ξ(z) ≥ δ}
PAPER: is compact in H for every δ > 0.
(Verified in `brennanOAI/lean/OAI/Analysis/IntegralMeans/TraceBounds.lean`)
-/
axiom prop_4_1_compact_superlevels (beta : ℝ) (P : Measure KClass) (hP : IsProbabilityMeasure P) :
  ∀ᵐ F ∂P, ∀ᵐ xi ∂volume, ∀ delta > 0, IsCompact {z ∈ H | V_target beta F xi z ≥ delta}

/-!
PAPER: 4.1 A weighted area integral
PAPER: Recall m(z) = (z − i)/(z + i) and the affine inverse z# = (−x + i)/y of z = x + iy. Define
PAPER: S0 = {z ∈ H : |m(z)| ≥ 1/2}, I(F) = ∫_S0 y^{β+1}|F(x + iy)|^{−4} dA(x + iy). (4.3)
PAPER: The complement of S0 has compact closure in H and contains the unique zero i of every F ∈ K.

PAPER: Lemma 4.2 (Weighted inverse area). The function I : K → [0, ∞] is Borel and satisfies
PAPER: EI(F) ≤ 256π. In particular, I(F) < ∞ almost surely.
(Verified in `brennanOAI/lean/OAI/Analysis/IntegralMeans/BoundaryEscape.lean`)
-/
def S0 : Set ℂ := {z | z.im > 0 ∧ ‖(z - I) / (z + I)‖ ≥ 1/2}

def I_func (beta : ℝ) (F : KClass) : ℝ :=
  ∫ z in S0, (z.im : ℝ) ^ (beta + 1) * ‖F.F z‖ ^ (-4 : ℝ) ∂volume

axiom lemma_4_2_weighted_inverse_area (beta : ℝ) (P : Measure KClass) :
  ∫ F, I_func beta F ∂P ≤ 256 * Real.pi

/-!
PAPER: 4.2 Escape and horizontal preimage length
PAPER: Lemma 4.3 (Escape and trace bounds). Let F ∈ K satisfy I(F) < ∞. Then
PAPER: y^k / |F(x + iy)| → 0 as |x| + y → ∞. (4.6)
PAPER: For every compact K ⊂ C and ϵ > 0, F^{−1}(K) ∩ {ℑz ≥ ϵ} is compact in H, and
PAPER: HF,K := sup{ℑz : F(z) ∈ K} < ∞,
PAPER: where the supremum of an empty set is assigned zero. Moreover, there is CF,K < ∞ such that
PAPER: ∫_R 1_K(F(x + iϵ)) dx ≤ CF,K (ϵ > 0). (4.7)
(Verified in `brennanOAI/lean/OAI/Analysis/IntegralMeans/BoundaryEscape.lean` and `TraceIdentity.lean`)
-/
axiom lemma_4_3_escape (beta : ℝ) (F : KClass) (hI : I_func beta F > 0) :
  Filter.Tendsto (fun z : ℂ => V_target beta F 0 z)
    (Filter.comap (fun z : ℂ => abs z.re + z.im) Filter.atTop) (𝓝 0)

axiom lemma_4_3_trace_bounds (beta : ℝ) (F : KClass) (hI : I_func beta F > 0) (K : Set ℂ)
    (hK : IsCompact K) (eps : ℝ) (heps : eps > 0) :
  IsCompact ({z : ℂ | F.F z ∈ K} ∩ {z : ℂ | z.im ≥ eps}) ∧
  ∃ C_F_K : ℝ, ∀ e > 0, ∫ x : ℝ, (if F.F (x + e • I) ∈ K then (1 : ℝ) else 0) ∂volume ≤ C_F_K

/-!
PAPER: 4.3 Targets near the real axis
PAPER: Lemma 4.4 (Measurability of compact superlevels). The set of pairs (F, ξ) ∈ K × C for
PAPER: which every closed positive superlevel of V^F_ξ is compact in H is Borel.
(Verified in `brennanOAI/lean/OAI/Analysis/IntegralMeans/TraceBounds.lean`)
-/
axiom lemma_4_4_measurability (beta : ℝ) :
  MeasurableSet {p : KClass × ℂ | ∀ delta > 0, IsCompact {z ∈ H | V_target beta p.1 p.2 z ≥ delta}}

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
  (∀ delta > 0, IsCompact {z ∈ H | V_target beta F xi z ≥ delta}) ∧
  (∀ z ∈ H, G beta F z = xi → J beta F z ≠ 0)

axiom lemma_5_4_good_pairs (beta : ℝ) (P : Measure KClass) (hP : IsProbabilityMeasure P) :
  MeasurableSet {p : KClass × ℂ | is_good_pair beta p.1 p.2} ∧
  ∀ᵐ F ∂P, volume {xi : ℂ | ¬ is_good_pair beta F xi} = 0

/-!
PAPER: 5.2 The superlevel count
PAPER: Lemma 5.5 (Counting critical points above a level). Fix a good pair (F, ξ). There are
PAPER: only finitely many critical points of V^F_ξ with value at least h, for every h > 0. For every
PAPER: such h,
PAPER: #{maxima with V^F_ξ ≥ h} ≥ #{saddles with V^F_ξ ≥ h}. (5.12)
PAPER: The possible pole is excluded from the maximum count.
(Verified in `brennanOAI/lean/OAI/Analysis/IntegralMeans/SuperlevelCount.lean`)
-/
axiom lemma_5_5_count (beta : ℝ) (F : KClass) (xi : ℂ) (h_good : is_good_pair beta F xi)
    (h : ℝ) (hh : h > 0) :
  {z ∈ H | V_target beta F xi z ≥ h ∧ G beta F z = xi}.Finite ∧
  Nat.card {z ∈ H | is_max beta F xi z ∧ V_target beta F xi z ≥ h} ≥
  Nat.card {z ∈ H | is_saddle beta F xi z ∧ V_target beta F xi z ≥ h}

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

axiom prop_5_6_equivariant_pairing (beta : ℝ) (F : KClass) (z : ℂ) (hz_saddle : J beta F z > 0) :
  is_max beta F (G beta F z) (R_pair beta F z) ∧
  V_target beta F (G beta F z) (R_pair beta F z) ≥ V_target beta F (G beta F z) z

end Brennan.Sections4and5
