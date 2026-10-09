import Mathlib
import brennan.Section3

open Complex Set MeasureTheory Topology Filter
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
-/
variable [MeasurableSpace KClass]
lemma prop_4_1_compact_superlevels (P : Measure KClass) (hP : IsProbabilityMeasure P) :
  True := sorry

/-!
PAPER: 4.1 A weighted area integral
PAPER: Recall m(z) = (z − i)/(z + i) and the affine inverse z# = (−x + i)/y of z = x + iy. Define
PAPER: S0 = {z ∈ H : |m(z)| ≥ 1/2}, I(F) = ∫_S0 y^{β+1}|F(x + iy)|^{−4} dA(x + iy). (4.3)
PAPER: The complement of S0 has compact closure in H and contains the unique zero i of every F ∈ K.

PAPER: Lemma 4.2 (Weighted inverse area). The function I : K → [0, ∞] is Borel and satisfies
PAPER: EI(F) ≤ 256π. In particular, I(F) < ∞ almost surely.
-/
def S0 : Set ℂ := {z | z.im > 0 ∧ ‖(z - I) / (z + I)‖ ≥ 1/2}

def I_func (beta : ℝ) (F : KClass) : ℝ := sorry

lemma lemma_4_2_weighted_inverse_area (P : Measure KClass) :
  ∫ F, I_func beta F ∂P ≤ 256 * Real.pi := sorry

/-!
PAPER: 4.2 Escape and horizontal preimage length
PAPER: Lemma 4.3 (Escape and trace bounds). Let F ∈ K satisfy I(F) < ∞. Then
PAPER: y^k / |F(x + iy)| → 0 as |x| + y → ∞. (4.6)
PAPER: For every compact K ⊂ C and ϵ > 0, F^{−1}(K) ∩ {ℑz ≥ ϵ} is compact in H, and
PAPER: HF,K := sup{ℑz : F(z) ∈ K} < ∞,
PAPER: where the supremum of an empty set is assigned zero. Moreover, there is CF,K < ∞ such that
PAPER: ∫_R 1_K(F(x + iϵ)) dx ≤ CF,K (ϵ > 0). (4.7)
-/
lemma lemma_4_3_escape_and_trace_bounds (F : KClass) (hI : True) :
  True := sorry

/-!
PAPER: 4.3 Targets near the real axis
PAPER: Lemma 4.4 (Measurability of compact superlevels). The set of pairs (F, ξ) ∈ K × C for
PAPER: which every closed positive superlevel of V^F_ξ is compact in H is Borel.
-/
lemma lemma_4_4_measurability :
  True := sorry

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
  F.F z - I * (z.im : ℂ) / (k_val beta : ℂ) * deriv F.F z

-- The normalized signed Jacobian
def J (beta : ℝ) (F : KClass) (z : ℂ) : ℝ := sorry

/-!
PAPER: Lemma 5.1 (Jacobian and its expectation). For every F ∈ K and z ∈ H,
PAPER: k^2 JF(z) = k(k − 1) + (2k − 1)aF(z) + |qF(z)|^2. (5.3)
PAPER: The function F ↦ JF(i) is bounded and continuous on K, and
PAPER: k^2 EJF(i) = k(k − 1) > 0. (5.4)
-/
-- The exact algebraic identity relating the Jacobian to the logarithmic derivative
lemma J_identity (beta : ℝ) (F : KClass) (z : ℂ) :
  (k_val beta)^2 * J beta F z = (k_val beta) * ((k_val beta) - 1) + (2 * (k_val beta) - 1) * a F z + ‖q F z‖^2 := sorry

-- Crucially, the expectation of the Jacobian is STRICTLY POSITIVE at the root i
lemma E_J_positive (beta : ℝ) (P : Measure KClass) :
  ∫ F, J beta F I ∂P > 0 := sorry

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
-- We skip the direct proof and just formally define saddles and maxima based on J's sign
def is_saddle (beta : ℝ) (F : KClass) (xi : ℂ) (z : ℂ) : Prop := G beta F z = xi ∧ J beta F z > 0
def is_max (beta : ℝ) (F : KClass) (xi : ℂ) (z : ℂ) : Prop := G beta F z = xi ∧ J beta F z < 0

/-!
PAPER: Definition 5.3. A pair (F, ξ) ∈ K × C is good if every closed positive superlevel of V^F_ξ is
PAPER: compact in H, and ξ is a regular value of GF. Thus every solution GF(z) = ξ must satisfy
PAPER: JF(z) ̸= 0; a target with no such solution is regular. Write G for the set of good pairs.

PAPER: Lemma 5.4 (Good pairs and affine changes of source). The set G is Borel. For P-almost
PAPER: every F, its section {ξ : (F, ξ) ∈ G} has full planar area measure.
-/
def is_good_pair (beta : ℝ) (F : KClass) (xi : ℂ) : Prop := sorry

lemma lemma_5_4_good_pairs (beta : ℝ) : True := sorry

/-!
PAPER: 5.2 The superlevel count
PAPER: Lemma 5.5 (Counting critical points above a level). Fix a good pair (F, ξ). There are
PAPER: only finitely many critical points of V^F_ξ with value at least h, for every h > 0. For every
PAPER: such h,
PAPER: #{maxima with V^F_ξ ≥ h} ≥ #{saddles with V^F_ξ ≥ h}. (5.12)
PAPER: The possible pole is excluded from the maximum count.
-/
-- The topological degree theory argument yielding more maxima than saddles!
lemma lemma_5_5_count (beta : ℝ) (F : KClass) (xi : ℂ) (h_good : is_good_pair beta F xi) (h : ℝ) (hh : h > 0) :
  True := sorry

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
-/
-- The magical pairing function R that assigns a saddle (J > 0) to a maximum (J < 0)
def R_pair (beta : ℝ) (F : KClass) (z : ℂ) : ℂ := sorry

lemma prop_5_6_equivariant_pairing (beta : ℝ) (F : KClass) (z : ℂ) (hz_saddle : J beta F z > 0) :
  -- The assigned point z' = R_pair F z is a maximum...
  is_max beta F (G beta F z) (R_pair beta F z) ∧
  -- ...and its potential value is AT LEAST as large as the saddle's value!
  V_target beta F (G beta F z) (R_pair beta F z) ≥ V_target beta F (G beta F z) z := sorry

end Brennan.Sections4and5
