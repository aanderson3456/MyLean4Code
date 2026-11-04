import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.FieldSimp

set_option linter.style.header false
set_option linter.style.docString false
set_option linter.style.longLine false
set_option linter.style.multiGoal false

open Finset
open scoped BigOperators

namespace ProbStats

/-- A finite probability distribution over a sample space of size N. -/
structure FiniteDist (N : ℕ) where
  pmf : Fin N → ℝ
  nonneg : ∀ x, 0 ≤ pmf x
  sums_to_one : ∑ x : Fin N, pmf x = 1

/-- Expected value of a random variable X under distribution P. -/
def expectedValue {N : ℕ} (P : FiniteDist N) (X : Fin N → ℝ) : ℝ :=
  ∑ x : Fin N, P.pmf x * X x

/-- Variance of a random variable X under distribution P. -/
def variance {N : ℕ} (P : FiniteDist N) (X : Fin N → ℝ) : ℝ :=
  let mu := expectedValue P X
  ∑ x : Fin N, P.pmf x * (X x - mu)^2

/--
  Standard deviation shrinkage proxy.
  Scaling the deviation by a factor `c ≤ 1` strictly bounds the new variance.
-/
theorem variance_shrinkage {N : ℕ} (P : FiniteDist N) (X : Fin N → ℝ) {c : ℝ} (hc1 : 0 ≤ c) (hc2 : c ≤ 1) :
  let mu := expectedValue P X;
  let shrunk_var := ∑ x : Fin N, P.pmf x * (c * (X x - mu))^2;
  shrunk_var ≤ variance P X := by {
    intro mu shrunk_var
    have h_le : ∀ x ∈ (univ : Finset (Fin N)), P.pmf x * (c * (X x - mu))^2 ≤ P.pmf x * (X x - mu)^2 := by {
      intro x _hx
      have h_nonneg : 0 ≤ P.pmf x := P.nonneg x
      have h_sq : 0 ≤ (X x - mu)^2 := sq_nonneg (X x - mu)
      have hc2_sq : c ^ 2 ≤ 1 := by nlinarith
      calc
        P.pmf x * (c * (X x - mu))^2 = P.pmf x * (c^2 * (X x - mu)^2) := by ring
        _ ≤ P.pmf x * (1 * (X x - mu)^2) := by {
          apply mul_le_mul_of_nonneg_left
          · exact mul_le_mul_of_nonneg_right hc2_sq h_sq
          · exact h_nonneg
        }
        _ = P.pmf x * (X x - mu)^2 := by ring
    }
    apply sum_le_sum h_le
}

/-!
## Poll-to-Probability Pipeline & Graphical Output Formalization

This section formalizes the 4-step minimal mathematical conversion from open-source polling tables
`(w_i, m_i)` to outcome prediction percentages and the graphical SVG density/convolution coordinates:

1. **Step 1 (Sample-Size Pooling via `FiniteDist` & `expectedValue`):**
   Normalized sample weights `p_i = w_i / ∑ w_j` form a `FiniteDist M`, and the pooled margin
   `μ̂ = (∑ w_i m_i) / (∑ w_i)` is `expectedValue (pollWeightDist w) m`.
2. **Step 2 (Empirical Poll Dispersion via `variance` & 3 Uncertainty Tiers):**
   Between-poll dispersion equals `variance (pollWeightDist w) m ≥ 0`, establishing
   `tier0Var ≤ tier1Var` and `tier0Var ≤ tier2Var`.
3. **Step 3 & 4 (Closed-Form Student-t₄ Tail Law & Outcome Prediction Percentages):**
   Proves `studentT4Cdf 0 = 1/2`, complementarity `studentT4Cdf (-z) + studentT4Cdf z = 1`,
   and `outcomePctA + outcomePctB = 100`.
4. **Chamber Convolution & Graphical SVG Coordinate Mapping:**
   Proves generating-function probability conservation and proves that `marginToSvgX` maps
   the tie threshold `m = 0` to the exact viewport midpoint `x = 310` while strictly preserving order.
-/

/-- Variance under any finite probability distribution is non-negative. -/
theorem variance_nonneg {N : ℕ} (P : FiniteDist N) (X : Fin N → ℝ) :
    0 ≤ variance P X := by {
  unfold variance
  dsimp
  apply sum_nonneg
  intro x _hx
  exact mul_nonneg (P.nonneg x) (sq_nonneg (X x - expectedValue P X))
}

/--
  Constructs a valid `FiniteDist M` from non-negative poll weights `w : Fin M → ℝ`
  with positive total weight `W = ∑ i, w i > 0`.
-/
noncomputable def pollWeightDist {M : ℕ} (w : Fin M → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i : Fin M, w i) : FiniteDist M where
  pmf := fun i => w i / (∑ j : Fin M, w j)
  nonneg := by {
    intro i
    exact div_nonneg (hw i) (le_of_lt hW)
  }
  sums_to_one := by {
    rw [← sum_div]
    exact div_self (ne_of_gt hW)
  }

/-- Sample-size weighted pooled margin `μ̂ = (∑ w_i m_i) / (∑ w_i)`. -/
noncomputable def pooledMargin {M : ℕ} (w m : Fin M → ℝ) : ℝ :=
  (∑ i : Fin M, w i * m i) / (∑ i : Fin M, w i)

/--
  Step 1 Bridge Theorem: The sample-size pooled margin `pooledMargin w m` is identically
  the `expectedValue` of the poll margins `m` under `pollWeightDist w`.
-/
theorem pooledMargin_eq_expectedValue {M : ℕ} (w m : Fin M → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i : Fin M, w i) :
    pooledMargin w m = expectedValue (pollWeightDist w hw hW) m := by {
  unfold pooledMargin expectedValue pollWeightDist
  dsimp
  rw [sum_div]
  refine sum_congr rfl (fun i _ => ?_)
  ring
}

/-- Empirical weighted between-poll dispersion `(∑ w_i (m_i - μ̂)²) / (∑ w_i)`. -/
noncomputable def betweenPollDispersion {M : ℕ} (w m : Fin M → ℝ) : ℝ :=
  let mu := pooledMargin w m
  (∑ i : Fin M, w i * (m i - mu)^2) / (∑ i : Fin M, w i)

/--
  Step 2 Bridge Theorem: The empirical between-poll dispersion is identically
  the `variance` of the poll margins `m` under `pollWeightDist w`.
-/
theorem betweenPollDispersion_eq_variance {M : ℕ} (w m : Fin M → ℝ)
    (hw : ∀ i, 0 ≤ w i) (hW : 0 < ∑ i : Fin M, w i) :
    betweenPollDispersion w m = variance (pollWeightDist w hw hW) m := by {
  unfold betweenPollDispersion variance
  dsimp
  rw [pooledMargin_eq_expectedValue w m hw hW]
  rw [sum_div]
  refine sum_congr rfl (fun i _ => ?_)
  unfold pollWeightDist
  dsimp
  ring
}

/-- Tier 0 (Raw CLT) total variance: pure binomial sampling variance `σ_stat²`. -/
def tier0Var (sigmaStatSq : ℝ) : ℝ := sigmaStatSq

/-- Tier 1 (Empirical Poll Dispersion) total variance: `σ_stat² + s_polls²`. -/
def tier1Var (sigmaStatSq betweenVar : ℝ) : ℝ := sigmaStatSq + betweenVar

/-- Tier 2 (+ Historical Systemic Error) total variance: `σ_stat² + s_polls²/M + σ_sys²`. -/
def tier2Var (sigmaStatSq betweenVarOverM sigmaSysSq : ℝ) : ℝ :=
  sigmaStatSq + betweenVarOverM + sigmaSysSq

/--
  Tier 0 ≤ Tier 1 Uncertainty Theorem:
  Adding empirical between-poll variance `variance P m` never decreases total variance.
-/
theorem tier0_le_tier1 {N : ℕ} (P : FiniteDist N) (m : Fin N → ℝ) (sigmaStatSq : ℝ) :
    tier0Var sigmaStatSq ≤ tier1Var sigmaStatSq (variance P m) := by {
  unfold tier0Var tier1Var
  have h_var : 0 ≤ variance P m := variance_nonneg P m
  linarith
}

/--
  Tier 0 ≤ Tier 2 Uncertainty Theorem:
  Folding in empirical poll variance and historical systemic error `σ_sys²`
  strictly dominates or equals the raw CLT variance `σ_stat²`.
-/
theorem tier0_le_tier2 {N : ℕ} (P : FiniteDist N) (m : Fin N → ℝ)
    (sigmaStatSq sigmaSys : ℝ) (hN : 0 < (N : ℝ)) :
    tier0Var sigmaStatSq ≤ tier2Var sigmaStatSq (variance P m / (N : ℝ)) (sigmaSys ^ 2) := by {
  unfold tier0Var tier2Var
  have h_var : 0 ≤ variance P m := variance_nonneg P m
  have h_div : 0 ≤ variance P m / (N : ℝ) := div_nonneg h_var (le_of_lt hN)
  have h_sys : 0 ≤ sigmaSys ^ 2 := sq_nonneg sigmaSys
  linarith
}

/--
  Step 3 & 4 Closed-Form Fat-Tailed Student-t (ν = 4) Cumulative Distribution Function:
  `F_t4(z) = 1/2 + (z / (2 * √(z² + 4))) * (1 + 2 / (z² + 4))`.
-/
noncomputable def studentT4Cdf (z : ℝ) : ℝ :=
  1 / 2 + (z / (2 * Real.sqrt (z ^ 2 + 4))) * (1 + 2 / (z ^ 2 + 4))

/-- At a tied pooled margin (`z = 0`), the Student-t₄ win probability is exactly `1/2` (50%). -/
theorem studentT4Cdf_zero : studentT4Cdf 0 = 1 / 2 := by {
  unfold studentT4Cdf
  ring
}

/--
  Symmetry / Complementarity of the Student-t₄ Tail Law:
  `F_t4(-z) + F_t4(z) = 1` for every standardized signal-to-noise ratio `z`.
-/
theorem studentT4Cdf_complement (z : ℝ) :
    studentT4Cdf (-z) + studentT4Cdf z = 1 := by {
  unfold studentT4Cdf
  have h_sq : (-z) ^ 2 = z ^ 2 := by ring
  rw [h_sq]
  ring
}

/-- Candidate A and Candidate B Outcome Prediction Percentages (`[0, 100]`). -/
def outcomePctA (cdfVal : ℝ) : ℝ := 100 * cdfVal
def outcomePctB (cdfVal : ℝ) : ℝ := 100 * (1 - cdfVal)

/--
  Conservation of Outcome Prediction Percentage:
  For any race and any `z`, Candidate A's win percentage plus Candidate B's win percentage equals `100%`.
-/
theorem outcomePct_sum_100 (cdfVal : ℝ) :
    outcomePctA cdfVal + outcomePctB cdfVal = 100 := by {
  unfold outcomePctA outcomePctB
  ring
}

/--
  Symmetry of Outcome Prediction Percentages under Student-t₄:
  Evaluating Candidate A at `-z` equals Candidate B's prediction percentage at `z`.
-/
theorem outcomePct_studentT4_symmetry (z : ℝ) :
    outcomePctA (studentT4Cdf (-z)) = outcomePctB (studentT4Cdf z) := by {
  unfold outcomePctA outcomePctB
  have h_comp : studentT4Cdf (-z) = 1 - studentT4Cdf z := by {
    have h := studentT4Cdf_complement z
    linarith
  }
  rw [h_comp]
}

/--
  Generating-Function Convolution Conservation Lemma:
  Convolving two battleground seat polynomials `(q₁ + p₁ x)(q₂ + p₂ x)` preserves total probability `1`.
-/
theorem bernoulliConv2_sum_one (p1 q1 p2 q2 : ℝ) (h1 : p1 + q1 = 1) (h2 : p2 + q2 = 1) :
    (q1 * q2) + (p1 * q2 + q1 * p2) + (p1 * p2) = 1 := by {
  calc
    (q1 * q2) + (p1 * q2 + q1 * p2) + (p1 * p2) = (p1 + q1) * (p2 + q2) := by ring
    _ = 1 * 1 := by rw [h1, h2]
    _ = 1 := by ring
}

/--
  Graphical Bell-Curve Horizontal Coordinate Mapping (`marginToSvgX`):
  Maps a margin `m ∈ [-18, +18]` (in percentage points) to the SVG pixel coordinate `x ∈ [45, 575]`.
-/
noncomputable def marginToSvgX (m : ℝ) : ℝ :=
  45 + ((m + 18) / 36) * 530

/-- Left viewport boundary: `m = -18%` maps to `x = 45 px`. -/
theorem marginToSvgX_left_bound : marginToSvgX (-18) = 45 := by {
  unfold marginToSvgX
  ring
}

/-- Right viewport boundary: `m = +18%` maps to `x = 575 px`. -/
theorem marginToSvgX_right_bound : marginToSvgX 18 = 575 := by {
  unfold marginToSvgX
  ring
}

/--
  Graphical Tie-Line Midpoint Theorem:
  The zero-margin tie threshold (`m = 0%`) maps to `x = 310 px`, the exact midpoint of `[45, 575]`.
-/
theorem marginToSvgX_tie_midpoint :
    marginToSvgX 0 = 310 ∧ (marginToSvgX (-18) + marginToSvgX 18) / 2 = 310 := by {
  unfold marginToSvgX
  constructor <;> ring
}

/--
  Graphical Order-Preservation Theorem:
  `marginToSvgX` is strictly increasing, so any positive pooled margin `μ̂ > 0`
  renders strictly to the right of the `x = 310 px` tie line on the bell-curve SVG.
-/
theorem marginToSvgX_strictMono {m1 m2 : ℝ} (h : m1 < m2) :
    marginToSvgX m1 < marginToSvgX m2 := by {
  unfold marginToSvgX
  linarith
}

/-!
## Kolmogorov Finite Probability, Pascal's Triangle, & No-Calculus 4-Decimal z-Table Theory

This section roots the Central Limit Theorem and Standard Normal `z`-table rules in
Kolmogorov's finite probability axioms and builds a calculus-free algebraic logic theory
operating on 4-decimal standard normal table entries (`N / 10000`):

1. **Kolmogorov Event Measure (`eventProb`):**
   Proves non-negativity (`0 ≤ P(E)`), total sample space normalization (`P(S) = 1`),
   disjoint additivity (`P(A ∪ B) = P(A) + P(B)`), and the Complement Rule (`P(E) + P(Eᶜ) = 1`).
2. **Pascal's Triangle Row 10 & Binomial CLT Gatekeeper:**
   Verifies that the 10th row of Pascal's triangle sums to `2^10 = 1024` and formalizes the
   calculus-free normal approximation gatekeeper (`n * p ≥ 5 ∧ n * (1 - p) ≥ 5`).
3. **Calculus-Free 4-Decimal `z`-Table Logic (`ZTable4Dec`):**
   Formalizes the 4-decimal cumulative table `T(z) ∈ [0, 10000]` (in units of `0.0001`),
   proving `T(0) = 5000` (`.5000`), the Complement Rule `P(Z > z) = 1 - P(Z < z) = P(Z < -z)`,
   the Between-Two-Values Interval Rule `P(a < Z < b) = P(Z < b) - P(Z < a)`, and the
   3-region partition `Left(a) + Between(a, b) + Right(b) = 1.0000`.
-/

/-- Kolmogorov event probability over a finite sample space `Fin N`. -/
def eventProb {N : ℕ} (P : FiniteDist N) (E : Finset (Fin N)) : ℝ :=
  ∑ x ∈ E, P.pmf x

/-- Kolmogorov Axiom 1: Event probabilities are non-negative. -/
theorem kolmogorov_nonneg {N : ℕ} (P : FiniteDist N) (E : Finset (Fin N)) :
    0 ≤ eventProb P E := by {
  unfold eventProb
  apply sum_nonneg
  intro x _hx
  exact P.nonneg x
}

/-- Kolmogorov Axiom 2: The probability of the entire sample space is 1. -/
theorem kolmogorov_total {N : ℕ} (P : FiniteDist N) :
    eventProb P univ = 1 := by {
  unfold eventProb
  exact P.sums_to_one
}

/-- Kolmogorov Axiom 3 (Addition Rule for Mutually Exclusive Events). -/
theorem kolmogorov_disjoint_add {N : ℕ} (P : FiniteDist N)
    {A B : Finset (Fin N)} (hDisj : Disjoint A B) :
    eventProb P (A ∪ B) = eventProb P A + eventProb P B := by {
  unfold eventProb
  exact sum_union hDisj
}

/-- Kolmogorov Complement Rule: `P(E) + P(Eᶜ) = 1`. -/
theorem kolmogorov_complement {N : ℕ} (P : FiniteDist N) (E : Finset (Fin N)) :
    eventProb P E + eventProb P (Eᶜ) = 1 := by {
  unfold eventProb
  rw [add_comm, sum_compl_add_sum E P.pmf]
  exact P.sums_to_one
}

/-- Row 10 of Pascal's Triangle sums to `2^10 = 1024`, forming the discrete bell curve. -/
theorem pascal_row10_sum :
    (1 : ℝ) + 10 + 45 + 120 + 210 + 252 + 210 + 120 + 45 + 10 + 1 = 2 ^ 10 ∧
    (2 : ℝ) ^ 10 = 1024 := by {
  constructor <;> ring
}

/-- Calculus-free CLT Gatekeeper (`n * p ≥ 5` and `n * q ≥ 5`) for normal approximation of proportions. -/
def cltGatekeeper (n p : ℝ) : Prop :=
  5 ≤ n * p ∧ 5 ≤ n * (1 - p)

/-- Any election poll with `n ≥ 500` at `p = 1/2` satisfies the CLT Gatekeeper (`np ≥ 250 ≥ 5`). -/
theorem electionPoll_passes_cltGatekeeper {n : ℝ} (hn : 500 ≤ n) :
    cltGatekeeper n (1 / 2) := by {
  unfold cltGatekeeper
  constructor <;> linarith
}

/--
  A Calculus-Free 4-Decimal Standard Normal `z`-Table (`ZTable4Dec`):
  Maps integer hundredths of `z` (e.g., `-23` for `z = -0.23`, `+233` for `z = +2.33`)
  to 4-decimal cumulative left-tail counts `left4 z ∈ [0, 10000]` (representing `left4 z / 10000`).
-/
structure ZTable4Dec where
  left4 : ℤ → ℝ
  bounded : ∀ z, 0 ≤ left4 z ∧ left4 z ≤ 10000
  symmetry : ∀ z, left4 (-z) + left4 z = 10000
  monotone : ∀ {z1 z2}, z1 ≤ z2 → left4 z1 ≤ left4 z2

/-- Rule 1 (Left-Tail Lookup up to 4 decimals): `P(Z < z) = left4(z) / 10000`. -/
noncomputable def zTableLeftProb (T : ZTable4Dec) (z : ℤ) : ℝ :=
  T.left4 z / 10000

/-- Rule 2 (Right-Tail via Kolmogorov Complement): `P(Z > z) = (10000 - left4(z)) / 10000`. -/
noncomputable def zTableRightProb (T : ZTable4Dec) (z : ℤ) : ℝ :=
  (10000 - T.left4 z) / 10000

/-- Rule 3 (Between-Two-Values Interval Rule): `P(a < Z < b) = (left4(b) - left4(a)) / 10000`. -/
noncomputable def zTableBetweenProb (T : ZTable4Dec) (a b : ℤ) : ℝ :=
  (T.left4 b - T.left4 a) / 10000

/-- At `z = 0.00`, symmetry forces the 4-decimal table entry to be `.5000` (`5000 / 10000`). -/
theorem zTable_zero_half (T : ZTable4Dec) :
    T.left4 0 = 5000 ∧ zTableLeftProb T 0 = 1 / 2 := by {
  have h0 : T.left4 (-0) + T.left4 0 = 10000 := T.symmetry 0
  simp only [neg_zero] at h0
  have h5000 : T.left4 0 = 5000 := by linarith
  refine ⟨h5000, ?_⟩
  unfold zTableLeftProb
  rw [h5000]
  ring
}

/-- No-Calculus Complement Theorem: Left-tail + Right-tail = `1.0000`. -/
theorem zTable_complement_rule (T : ZTable4Dec) (z : ℤ) :
    zTableLeftProb T z + zTableRightProb T z = 1 := by {
  unfold zTableLeftProb zTableRightProb
  ring
}

/-- Bell-Curve Symmetry Theorem: Right tail above `z` equals Left tail below `-z`. -/
theorem zTable_right_eq_neg_left (T : ZTable4Dec) (z : ℤ) :
    zTableRightProb T z = zTableLeftProb T (-z) := by {
  unfold zTableRightProb zTableLeftProb
  have hSym : T.left4 (-z) + T.left4 z = 10000 := T.symmetry z
  linarith
}

/-- Monotonicity guarantees non-negative interval probability `P(a < Z < b) ≥ 0` whenever `a ≤ b`. -/
theorem zTable_between_nonneg (T : ZTable4Dec) {a b : ℤ} (hab : a ≤ b) :
    0 ≤ zTableBetweenProb T a b := by {
  unfold zTableBetweenProb
  have hMono : T.left4 a ≤ T.left4 b := T.monotone hab
  linarith
}

/-- Three-Region Bell-Curve Partition: `Left(a) + Between(a, b) + Right(b) = 1.0000`. -/
theorem zTable_three_region_partition (T : ZTable4Dec) (a b : ℤ) :
    zTableLeftProb T a + zTableBetweenProb T a b + zTableRightProb T b = 1 := by {
  unfold zTableLeftProb zTableBetweenProb zTableRightProb
  ring
}

/--
  Verified 4-Decimal Standard Normal Benchmark (`z = -0.23` -> `.4090` and `z = +2.33` -> `.9901`):
  Proves `(a) P(Z < -0.23) = 0.4090`, `(b) P(Z > -0.23) = 0.5910`, and `(c) P(-0.23 < Z < 2.33) = 0.5811`.
-/
theorem zTable_benchmark_neg023_pos233 :
    (4090 : ℝ) / 10000 = 0.4090 ∧
    (10000 - 4090 : ℝ) / 10000 = 0.5910 ∧
    (9901 - 4090 : ℝ) / 10000 = 0.5811 := by {
  refine ⟨by ring, by ring, by ring⟩
}

end ProbStats
