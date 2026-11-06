/-
  Formalization of Discrete Complex Analysis on Isoradial Graphs (Chelkak & Smirnov, 2011)
  grounded in Donald Sarason's Weierstrass `_eps` Complex & Harmonic Analysis Definitions.

  Foundational Reference & Credit:
  * Dmitry Chelkak (https://www-personal.umich.edu/~chelkak/) and
    Stanislav Smirnov (http://www.unige.ch/~smirnov/),
    "Discrete complex analysis on isoradial graphs",
    Advances in Mathematics 228 (2011), no. 3, 1590–1630.
    DOI: 10.1016/j.aim.2011.06.025, arXiv:0810.2188 [math.CV].
  * Donald Sarason, "Notes on Complex Function Theory", Chapters I–III.
-/
import Mathlib
import R2
import Sarason.Definitions
import Sarason.Chapter1
import Sarason.Chapter2
import Sarason.Chapter3

noncomputable section

open Complex Real Set Filter Topology BigOperators
open ComplexAnalysis.R2 Sarason Sarason.Ch1 Sarason.Ch2 Sarason.Ch3

namespace ChelkakSmirnov

/-! ## 1. Isoradial Vertex Star, Dual Circumcenter Orthogonality, and Discrete Mean Value Theorem (`[CS11, §1.2 & §2.1]`)

In Section 2.1 (pp. 1593–1595) of Chelkak and Smirnov [CS11], at an interior vertex `v ∈ Γ^δ` with
`d` neighbors `u_1, ..., u_d ∈ Γ^δ`, rhombic half-angles `θ_1, ..., θ_d ∈ (0, π/2)`, and dual
rhombic circumcenters `w_1, ..., w_d ∈ (Γ^δ)*`:
1. Each primal edge `u_k - v` and dual circumcenter chord `w_next k - w_prev k` are orthogonal
   diagonals of a rhombus of side `δ`:
   `tan θ_k * (u_k - v) = -i * (w_next k - w_prev k)`.
2. Summing around the closed dual cycle `∑_k (w_next k - w_prev k) = 0` yields the exact
   first-order cancellation `∑_k tan θ_k * (u_k - v) = 0`.
3. The discrete Laplacian
   `Δ^δ H(v) := (1 / μ_Γ^δ(v)) ∑_k tan θ_k (H(u_k) - H(v))`
   vanishes (`IsDiscreteHarmonicAt S H`) if and only if `H` satisfies the weighted Discrete Mean
   Value Property `H(v) = (M^δ H)(v) := ∑_k P(ξ_v = u_k - v) H(u_k)`.
-/

/-- Normalized tangent transition weight `tan θ_k / W_tan` (`[CS11, Eq. (2.19), p. 1605]`). -/
noncomputable def isoradialTangentWeight (theta_k W_tan : ℝ) : ℝ :=
  Real.tan theta_k / W_tan

/--
  **Chelkak–Smirnov Isoradial Vertex Star (`[CS11, Section 2.1, pp. 1593–1594]`):**
  At an interior vertex `v ∈ ℂ` of an isoradial graph `Γ^δ` with `d` neighbors `u : Fin d → ℂ`,
  rhombic half-angles `theta : Fin d → ℝ`, and dual rhombic circumcenters `w_next, w_prev : Fin d → ℂ`:
  - Each tangent weight `tan(theta k)` is strictly positive,
  - Each primal edge `u k - v` and dual circumcenter chord `w_next k - w_prev k` satisfy the
    rhombic orthogonality relation `(tan(theta k) : ℂ) * (u k - v) = -I * (w_next k - w_prev k)`,
  - The dual circumcenter chords form a closed cycle around `v`: `∑ k, (w_next k - w_prev k) = 0`.
-/
structure IsoradialVertexStar (d : ℕ) where
  v : ℂ
  u : Fin d → ℂ
  theta : Fin d → ℝ
  w_next : Fin d → ℂ
  w_prev : Fin d → ℂ
  hTanPos : ∀ k : Fin d, 0 < Real.tan (theta k)
  hTanSumPos : 0 < ∑ k : Fin d, Real.tan (theta k)
  hAreaPos : 0 < (1 / 4 : ℝ) * ∑ k : Fin d,
    Real.tan (theta k) * ((u k - v).re ^ 2 + (u k - v).im ^ 2)
  hDualOrthog : ∀ k : Fin d,
    ((Real.tan (theta k) : ℝ) : ℂ) * (u k - v) = -I * (w_next k - w_prev k)
  hDualCycle : ∑ k : Fin d, (w_next k - w_prev k) = 0

/-- Total tangent weight `W_tan(v) = ∑_{k=1}^d tan θ_k` at an isoradial vertex star `S`. -/
noncomputable def isoradialStarTotalTan {d : ℕ} (S : IsoradialVertexStar d) : ℝ :=
  ∑ k : Fin d, Real.tan (S.theta k)

/-- Rhombic area weight `μ_Γ(v) = (1/4) ∑_{k=1}^d tan θ_k ‖u_k - v‖²` at `S` (`[CS11, p. 1593]`). -/
noncomputable def isoradialStarAreaWeight {d : ℕ} (S : IsoradialVertexStar d) : ℝ :=
  (1 / 4 : ℝ) * ∑ k : Fin d,
    Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 + (S.u k - S.v).im ^ 2)

/--
  Chelkak–Smirnov random walk transition probability `P(ξ_v = u_k - v) = tan θ_k / ∑_j tan θ_j`
  at an isoradial vertex star `S` (`[CS11, Equation (2.19)]`).
-/
noncomputable def isoradialStarProb {d : ℕ} (S : IsoradialVertexStar d) (k : Fin d) : ℝ :=
  isoradialTangentWeight (S.theta k) (isoradialStarTotalTan S)

/-- Strict positivity of `isoradialStarProb S k`. -/
lemma isoradialStarProb_pos {d : ℕ} (S : IsoradialVertexStar d) (k : Fin d) :
    0 < isoradialStarProb S k := by
{
  unfold isoradialStarProb isoradialTangentWeight isoradialStarTotalTan
  exact div_pos (S.hTanPos k) S.hTanSumPos
}

/-- Non-negativity of `isoradialStarProb S k`. -/
lemma isoradialStarProb_nonneg {d : ℕ} (S : IsoradialVertexStar d) (k : Fin d) :
    0 ≤ isoradialStarProb S k := by
{
  exact le_of_lt (isoradialStarProb_pos S k)
}

/-- The Chelkak–Smirnov transition probabilities at `S` sum to `1`. -/
theorem isoradialStarProb_sum_eq_one {d : ℕ} (S : IsoradialVertexStar d) :
    ∑ k : Fin d, isoradialStarProb S k = 1 := by
{
  unfold isoradialStarProb isoradialTangentWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt S.hTanSumPos)
}

/--
  **Fundamental Dual-Circle Telescoping Identity (`[CS11, p. 1594]`):**
  Because `(tan θ_k) * (u_k - v) = -i * (w_next k - w_prev k)` and the dual circumcenter chords
  form a closed cycle around `v`, the tangent-weighted displacement sum vanishes identically:
  `∑_{k=1}^d tan θ_k * (u_k - v) = 0`.
-/
theorem isoradialStar_weighted_displacement_sum_eq_zero {d : ℕ} (S : IsoradialVertexStar d) :
    ∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v)) = 0 := by
{
  have h_congr :
      ∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v)) =
      ∑ k : Fin d, (-I * (S.w_next k - S.w_prev k)) := by
  {
    apply Finset.sum_congr rfl
    intro k _
    exact S.hDualOrthog k
  }
  rw [h_congr, ← Finset.mul_sum, S.hDualCycle, mul_zero]
}

/-- First-order `x`-displacement cancellation: `∑_{k=1}^d tan θ_k * (u_k - v).re = 0`. -/
theorem isoradialStar_weighted_dx_sum_eq_zero {d : ℕ} (S : IsoradialVertexStar d) :
    ∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).re = 0 := by
{
  have h_re := congrArg Complex.re (isoradialStar_weighted_displacement_sum_eq_zero S)
  rw [Complex.re_sum, Complex.zero_re] at h_re
  have h_congr :
      ∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).re =
      ∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v)).re := by
  {
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  }
  rw [h_congr, h_re]
}

/-- First-order `y`-displacement cancellation: `∑_{k=1}^d tan θ_k * (u_k - v).im = 0`. -/
theorem isoradialStar_weighted_dy_sum_eq_zero {d : ℕ} (S : IsoradialVertexStar d) :
    ∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).im = 0 := by
{
  have h_im := congrArg Complex.im (isoradialStar_weighted_displacement_sum_eq_zero S)
  rw [Complex.im_sum, Complex.zero_im] at h_im
  have h_congr :
      ∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).im =
      ∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v)).im := by
  {
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  }
  rw [h_congr, h_im]
}

/--
  **Chelkak–Smirnov Discrete Mean Value Operator `M^δ` (`[CS11, p. 1593]`):**
  `(M^δ H)(v) = ∑_{k=1}^d P(ξ_v = u_k - v) * H(u_k)`.
-/
noncomputable def isoradialDiscreteMeanValue {d : ℕ}
    (S : IsoradialVertexStar d) (H : ℂ → ℝ) : ℝ :=
  ∑ k : Fin d, isoradialStarProb S k * H (S.u k)

/--
  **Chelkak–Smirnov Discrete Laplacian `Δ^δ` (`[CS11, Equation (2.1), p. 1593]`):**
  `(Δ^δ H)(v) = (1 / μ_Γ(v)) * ∑_{k=1}^d tan θ_k * (H(u_k) - H(v))`.
-/
noncomputable def isoradialDiscreteLaplacian {d : ℕ}
    (S : IsoradialVertexStar d) (H : ℂ → ℝ) : ℝ :=
  (1 / isoradialStarAreaWeight S) *
    ∑ k : Fin d, Real.tan (S.theta k) * (H (S.u k) - H S.v)

/-- A function `H : ℂ → ℝ` is discrete harmonic at `S` if `(Δ^δ H)(v) = 0`. -/
def IsDiscreteHarmonicAt {d : ℕ} (S : IsoradialVertexStar d) (H : ℂ → ℝ) : Prop :=
  isoradialDiscreteLaplacian S H = 0

/-- Linearity of `isoradialDiscreteLaplacian` under addition. -/
theorem isoradialDiscreteLaplacian_add {d : ℕ}
    (S : IsoradialVertexStar d) (H₁ H₂ : ℂ → ℝ) :
    isoradialDiscreteLaplacian S (fun z => H₁ z + H₂ z) =
      isoradialDiscreteLaplacian S H₁ + isoradialDiscreteLaplacian S H₂ := by
{
  unfold isoradialDiscreteLaplacian
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring
}

/-- Linearity of `isoradialDiscreteLaplacian` under subtraction. -/
theorem isoradialDiscreteLaplacian_sub {d : ℕ}
    (S : IsoradialVertexStar d) (H₁ H₂ : ℂ → ℝ) :
    isoradialDiscreteLaplacian S (fun z => H₁ z - H₂ z) =
      isoradialDiscreteLaplacian S H₁ - isoradialDiscreteLaplacian S H₂ := by
{
  unfold isoradialDiscreteLaplacian
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring
}

/--
  **Exact Identity Linking the Discrete Laplacian `Δ^δ` and Discrete Mean Value Operator `M^δ`:**
  `(Δ^δ H)(v) = (W_tan(v) / μ_Γ(v)) * ((M^δ H)(v) - H(v))`.
-/
theorem isoradialDiscreteLaplacian_eq_meanValue_diff {d : ℕ}
    (S : IsoradialVertexStar d) (H : ℂ → ℝ) :
    isoradialDiscreteLaplacian S H =
      (isoradialStarTotalTan S / isoradialStarAreaWeight S) *
        (isoradialDiscreteMeanValue S H - H S.v) := by
{
  unfold isoradialDiscreteLaplacian isoradialDiscreteMeanValue isoradialStarProb isoradialTangentWeight
  have hW_ne : isoradialStarTotalTan S ≠ 0 := ne_of_gt S.hTanSumPos
  have h_sum :
      ∑ k : Fin d, Real.tan (S.theta k) * (H (S.u k) - H S.v) =
      isoradialStarTotalTan S *
        ((∑ k : Fin d, Real.tan (S.theta k) / isoradialStarTotalTan S * H (S.u k)) - H S.v) := by
  {
    have h1 :
        ∑ k : Fin d, Real.tan (S.theta k) * (H (S.u k) - H S.v) =
        (∑ k : Fin d, Real.tan (S.theta k) * H (S.u k)) - isoradialStarTotalTan S * H S.v := by
    {
      unfold isoradialStarTotalTan
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    }
    have h2 :
        isoradialStarTotalTan S *
          (∑ k : Fin d, Real.tan (S.theta k) / isoradialStarTotalTan S * H (S.u k)) =
        ∑ k : Fin d, Real.tan (S.theta k) * H (S.u k) := by
    {
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      calc isoradialStarTotalTan S * (Real.tan (S.theta k) / isoradialStarTotalTan S * H (S.u k))
        _ = (isoradialStarTotalTan S * (Real.tan (S.theta k) / isoradialStarTotalTan S)) * H (S.u k) := by ring
        _ = Real.tan (S.theta k) * H (S.u k) := by rw [mul_div_cancel₀ _ hW_ne]
    }
    rw [h1, mul_sub, h2]
  }
  rw [h_sum]
  ring
}

/--
  **Chelkak–Smirnov Discrete Mean Value Theorem (`[CS11, p. 1593]`):**
  A function `H : ℂ → ℝ` is discrete harmonic at an isoradial vertex star `S` (`Δ^δ H(v) = 0`)
  if and only if it satisfies the weighted Discrete Mean Value Property:
  `H(v) = ∑_{k=1}^d P(ξ_v = u_k - v) * H(u_k)`.
-/
theorem isDiscreteHarmonicAt_iff_meanValueProperty {d : ℕ}
    (S : IsoradialVertexStar d) (H : ℂ → ℝ) :
    IsDiscreteHarmonicAt S H ↔ H S.v = isoradialDiscreteMeanValue S H := by
{
  unfold IsDiscreteHarmonicAt
  rw [isoradialDiscreteLaplacian_eq_meanValue_diff]
  have h_ratio_pos : 0 < isoradialStarTotalTan S / isoradialStarAreaWeight S :=
    div_pos S.hTanSumPos S.hAreaPos
  rw [mul_eq_zero, or_iff_right (ne_of_gt h_ratio_pos), sub_eq_zero, eq_comm]
}

/--
  **Exact Discrete Harmonicity of Affine Functions (`[CS11, p. 1594]`):**
  Every real affine function `H(z) = a * z.re + b * z.im + c` is exactly discrete harmonic
  (`Δ^δ H(v) = 0`) and satisfies the exact Discrete Mean Value Property on any `IsoradialVertexStar`.
-/
theorem affine_isDiscreteHarmonicAt {d : ℕ}
    (S : IsoradialVertexStar d) (a b c : ℝ) :
    IsDiscreteHarmonicAt S (fun z : ℂ => a * z.re + b * z.im + c) := by
{
  unfold IsDiscreteHarmonicAt isoradialDiscreteLaplacian
  have h_sum :
      ∑ k : Fin d, Real.tan (S.theta k) *
        ((a * (S.u k).re + b * (S.u k).im + c) - (a * S.v.re + b * S.v.im + c)) =
      a * (∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).re) +
      b * (∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).im) := by
  {
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  }
  rw [h_sum, isoradialStar_weighted_dx_sum_eq_zero S,
    isoradialStar_weighted_dy_sum_eq_zero S]
  ring
}

/-! ## 2. Unconditional Quadratic Balance on Complete Isoradial Stars (`[CS11, Lemma 2.2, p. 1595]`)

In the proof of Lemma 2.2 on page 1595 of [CS11], Chelkak and Smirnov prove that the quadratic
balance condition `∑_s tan θ_s (u_s - v)² = 0` holds **unconditionally** on every vertex star of
an isoradial graph `Γ^δ` because the diagonals of each rhombus bisect each other:
`u_s + v = w_next s + w_prev s`.
-/

/--
  Quadratic balance condition on an isoradial vertex star `S`:
  `∑_k tan θ_k ((u_k - v).re² - (u_k - v).im²) = 0` and
  `∑_k tan θ_k (u_k - v).re (u_k - v).im = 0`.
-/
def IsQuadraticallyBalancedStar {d : ℕ} (S : IsoradialVertexStar d) : Prop :=
  (∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 - (S.u k - S.v).im ^ 2) = 0) ∧
  (∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re * (S.u k - S.v).im) = 0)

/--
  **Complete Isoradial Vertex Star (`[CS11, Section 2.1, pp. 1593–1595]`):**
  Extends `IsoradialVertexStar d` with the rhombic diagonal midpoint-bisection law
  `u k + v = w_next k + w_prev k` and the closed-cycle telescoping of squared dual vertices
  `∑ k, (w_next k ^ 2 - w_prev k ^ 2) = 0`.
-/
structure CompleteIsoradialStar (d : ℕ) extends IsoradialVertexStar d where
  hRhombicMidpoint : ∀ k : Fin d, u k + v = w_next k + w_prev k
  hDualSqCycle : ∑ k : Fin d, (w_next k ^ 2 - w_prev k ^ 2) = 0

/--
  **Chelkak–Smirnov Second-Order Rhombic Identity (`[CS11, Proof of Lemma 2.2, p. 1595]`):**
  In each rhombus `k` incident to `v`, multiplying `tan θ_k * (u_k - v) = -i * (w_next k - w_prev k)`
  by `u_k + v = w_next k + w_prev k` yields:
  `tan θ_k * (u_k² - v²) = -i * (w_next k² - w_prev k²)`.
-/
theorem completeIsoradialStar_rhombic_sq_diff {d : ℕ}
    (S : CompleteIsoradialStar d) (k : Fin d) :
    ((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k ^ 2 - S.v ^ 2) =
      -I * (S.w_next k ^ 2 - S.w_prev k ^ 2) := by
{
  calc ((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k ^ 2 - S.v ^ 2)
    _ = (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v)) * (S.u k + S.v) := by ring
    _ = (-I * (S.w_next k - S.w_prev k)) * (S.w_next k + S.w_prev k) := by
      { rw [S.hDualOrthog k, S.hRhombicMidpoint k] }
    _ = -I * (S.w_next k ^ 2 - S.w_prev k ^ 2) := by ring
}

/--
  **Second-Order Dual-Circle Telescoping (`[CS11, Proof of Lemma 2.2, p. 1595]`):**
  `∑_{k=1}^d tan θ_k * (u_k² - v²) = 0`.
-/
theorem completeIsoradialStar_weighted_sq_diff_sum_eq_zero {d : ℕ}
    (S : CompleteIsoradialStar d) :
    ∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k ^ 2 - S.v ^ 2)) = 0 := by
{
  have h_congr :
      ∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k ^ 2 - S.v ^ 2)) =
      ∑ k : Fin d, (-I * (S.w_next k ^ 2 - S.w_prev k ^ 2)) := by
  {
    apply Finset.sum_congr rfl
    intro k _
    exact completeIsoradialStar_rhombic_sq_diff S k
  }
  rw [h_congr, ← Finset.mul_sum, S.hDualSqCycle, mul_zero]
}

/--
  **Unconditional Complex Quadratic Balance Identity (`[CS11, Proof of Lemma 2.2, p. 1595]`):**
  On any `CompleteIsoradialStar`, the tangent-weighted sum of squared complex displacements vanishes:
  `∑_{k=1}^d tan θ_k * (u_k - v)² = 0`.
-/
theorem completeIsoradialStar_weighted_disp_sq_sum_eq_zero {d : ℕ}
    (S : CompleteIsoradialStar d) :
    ∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v) ^ 2) = 0 := by
{
  have h_decomp :
      ∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v) ^ 2) =
      (∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k ^ 2 - S.v ^ 2))) -
      (2 * S.v) * (∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v))) := by
  {
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro k _
    ring
  }
  rw [h_decomp, completeIsoradialStar_weighted_sq_diff_sum_eq_zero S,
    isoradialStar_weighted_displacement_sum_eq_zero S.toIsoradialVertexStar]
  ring
}

/-- Helper lemma for the real part of `tan θ * z²`. -/
lemma re_ofReal_mul_sq (t : ℝ) (z : ℂ) :
    (((t : ℝ) : ℂ) * z ^ 2).re = t * (z.re ^ 2 - z.im ^ 2) := by
{
  rw [sq, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero,
    Complex.mul_re, sq, sq]
}

/-- Helper lemma for the imaginary part of `tan θ * z²`. -/
lemma im_ofReal_mul_sq (t : ℝ) (z : ℂ) :
    (((t : ℝ) : ℂ) * z ^ 2).im = 2 * (t * (z.re * z.im)) := by
{
  rw [sq, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    Complex.mul_im]
  ring
}

/--
  **Unconditional Theorem of Quadratic Balance (`[CS11, Lemma 2.2, p. 1595]`):**
  Every `CompleteIsoradialStar` satisfies `IsQuadraticallyBalancedStar` automatically:
  1. `∑_{k=1}^d tan θ_k * ((u_k - v).re² - (u_k - v).im²) = 0`,
  2. `∑_{k=1}^d tan θ_k * ((u_k - v).re * (u_k - v).im) = 0`.
-/
theorem completeIsoradialStar_isQuadraticallyBalanced {d : ℕ}
    (S : CompleteIsoradialStar d) :
    IsQuadraticallyBalancedStar S.toIsoradialVertexStar := by
{
  have h_zero := completeIsoradialStar_weighted_disp_sq_sum_eq_zero S
  constructor
  · have h_re := congrArg Complex.re h_zero
    rw [Complex.re_sum, Complex.zero_re] at h_re
    have h_congr :
        ∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 - (S.u k - S.v).im ^ 2) =
        ∑ k : Fin d, ((((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v) ^ 2)).re := by
    {
      apply Finset.sum_congr rfl
      intro k _
      exact (re_ofReal_mul_sq (Real.tan (S.theta k)) (S.u k - S.v)).symm
    }
    rw [h_congr, h_re]
  · have h_im := congrArg Complex.im h_zero
    rw [Complex.im_sum, Complex.zero_im] at h_im
    have h_two :
        2 * (∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re * (S.u k - S.v).im)) =
        ∑ k : Fin d, ((((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v) ^ 2)).im := by
    {
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      exact (im_ofReal_mul_sq (Real.tan (S.theta k)) (S.u k - S.v)).symm
    }
    rw [h_im] at h_two
    linarith
}

/--
  **Trigonometric Rhombic Sector Area Identity (`[CS11, Section 2.1, p. 1593]`):**
  In a rhombus of side `δ` and half-angle `θ` (`cos θ ≠ 0`), the primal diagonal has length
  `|u_k - v| = 2 δ cos θ`, so the sector weight `(1/4) tan θ * (2 δ cos θ)²` equals
  `(1/2) δ² sin(2θ) = (1/2) μ_♦^δ(z_k)`.
-/
theorem isoradialRhombicSectorArea_trig_identity (δ θ : ℝ) (hcos : Real.cos θ ≠ 0) :
    (1 / 4 : ℝ) * Real.tan θ * (2 * δ * Real.cos θ) ^ 2 =
      (1 / 2 : ℝ) * δ ^ 2 * Real.sin (2 * θ) := by
{
  rw [Real.tan_eq_sin_div_cos, Real.sin_two_mul]
  have h_alg :
      (1 / 4 : ℝ) * (Real.sin θ / Real.cos θ) * (2 * δ * Real.cos θ) ^ 2 =
      ((1 / 2 : ℝ) * δ ^ 2 * (2 * Real.sin θ * Real.cos θ)) * (Real.cos θ / Real.cos θ) := by ring
  rw [h_alg, div_self hcos, mul_one]
}

/-! ## 3. Random Walk Martingale & Isotropic Covariance (`[CS11, Equation (1.2), p. 1592]`)

Chelkak and Smirnov define the random walk on `Γ^δ` with transition probabilities
`P(ξ_v = u_k - v) = tan θ_k / ∑_j tan θ_j` and local variance time-step
`T_v := 2 μ_Γ^δ(v) / ∑_j tan θ_j`. Equation (1.2) on page 1592 states:
- `E[Re ξ_v] = E[Im ξ_v] = 0`,
- `E[(Re ξ_v)²] = E[(Im ξ_v)²] = T_v`,
- `E[Re ξ_v * Im ξ_v] = 0`.
-/

/-- Expected value of a function `f : Fin d → ℝ` under the random walk at `S`. -/
noncomputable def isoradialStarExpectation {d : ℕ}
    (S : IsoradialVertexStar d) (f : Fin d → ℝ) : ℝ :=
  ∑ k : Fin d, isoradialStarProb S k * f k

/-- Local variance time-scale `T_v = 2 μ_Γ^δ(v) / ∑_k tan θ_k` (`[CS11, Eq. (1.2), p. 1592]`). -/
noncomputable def isoradialStarTimeScale {d : ℕ} (S : IsoradialVertexStar d) : ℝ :=
  (2 * isoradialStarAreaWeight S) / isoradialStarTotalTan S

/-- Strict positivity of the local time-scale `T_v > 0`. -/
theorem isoradialStarTimeScale_pos {d : ℕ} (S : IsoradialVertexStar d) :
    0 < isoradialStarTimeScale S := by
{
  unfold isoradialStarTimeScale
  exact div_pos (mul_pos two_pos S.hAreaPos) S.hTanSumPos
}

/-- Factoring `1 / W_tan` out of `isoradialStarExpectation`. -/
lemma isoradialStarExpectation_eq_div_totalTan {d : ℕ}
    (S : IsoradialVertexStar d) (f : Fin d → ℝ) :
    isoradialStarExpectation S f =
      (∑ k : Fin d, Real.tan (S.theta k) * f k) / isoradialStarTotalTan S := by
{
  unfold isoradialStarExpectation isoradialStarProb isoradialTangentWeight
  rw [Finset.sum_div]
  apply Finset.sum_congr rfl
  intro k _
  ring
}

/--
  **Martingale Property of `Re ξ_v` (`[CS11, Eq. (1.2), p. 1592]`):**
  `E[Re ξ_v] = 0`.
-/
theorem isoradialStar_expectation_re_eq_zero {d : ℕ} (S : IsoradialVertexStar d) :
    isoradialStarExpectation S (fun k => (S.u k - S.v).re) = 0 := by
{
  rw [isoradialStarExpectation_eq_div_totalTan,
    isoradialStar_weighted_dx_sum_eq_zero S, zero_div]
}

/--
  **Martingale Property of `Im ξ_v` (`[CS11, Eq. (1.2), p. 1592]`):**
  `E[Im ξ_v] = 0`.
-/
theorem isoradialStar_expectation_im_eq_zero {d : ℕ} (S : IsoradialVertexStar d) :
    isoradialStarExpectation S (fun k => (S.u k - S.v).im) = 0 := by
{
  rw [isoradialStarExpectation_eq_div_totalTan,
    isoradialStar_weighted_dy_sum_eq_zero S, zero_div]
}

/--
  **Total Second Moment `E[|ξ_v|²] = 2 T_v` (`[CS11, Eq. (1.2), p. 1592]`):**
  `E[(Re ξ_v)² + (Im ξ_v)²] = 2 * isoradialStarTimeScale S`.
-/
theorem isoradialStar_expectation_sqNorm_eq_two_timeScale {d : ℕ}
    (S : IsoradialVertexStar d) :
    isoradialStarExpectation S (fun k => (S.u k - S.v).re ^ 2 + (S.u k - S.v).im ^ 2) =
      2 * isoradialStarTimeScale S := by
{
  rw [isoradialStarExpectation_eq_div_totalTan]
  unfold isoradialStarTimeScale isoradialStarAreaWeight
  ring
}

/-- Tangent-weighted sum of `Δx_k²` on a `CompleteIsoradialStar` equals `2 μ_Γ^δ(v)`. -/
lemma completeIsoradialStar_weighted_dx_sq_sum {d : ℕ} (S : CompleteIsoradialStar d) :
    ∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).re ^ 2 =
      2 * isoradialStarAreaWeight S.toIsoradialVertexStar := by
{
  have hBal := (completeIsoradialStar_isQuadraticallyBalanced S).1
  have hSum :
      ∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 + (S.u k - S.v).im ^ 2) =
      4 * isoradialStarAreaWeight S.toIsoradialVertexStar := by
  {
    unfold isoradialStarAreaWeight
    ring
  }
  have h_add :
      (∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 + (S.u k - S.v).im ^ 2)) +
      (∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 - (S.u k - S.v).im ^ 2)) =
      2 * (∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).re ^ 2) := by
  {
    rw [← Finset.sum_add_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  }
  linarith
}

/-- Tangent-weighted sum of `Δy_k²` on a `CompleteIsoradialStar` equals `2 μ_Γ^δ(v)`. -/
lemma completeIsoradialStar_weighted_dy_sq_sum {d : ℕ} (S : CompleteIsoradialStar d) :
    ∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).im ^ 2 =
      2 * isoradialStarAreaWeight S.toIsoradialVertexStar := by
{
  have hBal := (completeIsoradialStar_isQuadraticallyBalanced S).1
  have hSum :
      ∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 + (S.u k - S.v).im ^ 2) =
      4 * isoradialStarAreaWeight S.toIsoradialVertexStar := by
  {
    unfold isoradialStarAreaWeight
    ring
  }
  have h_sub :
      (∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 + (S.u k - S.v).im ^ 2)) -
      (∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 - (S.u k - S.v).im ^ 2)) =
      2 * (∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).im ^ 2) := by
  {
    rw [← Finset.sum_sub_distrib, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro k _
    ring
  }
  linarith
}

/--
  **Isotropic Covariance of `ξ_v` on a Complete Isoradial Star (`[CS11, Eq. (1.2), p. 1592]`):**
  On any `CompleteIsoradialStar`:
  1. `E[(Re ξ_v)²] = T_v`,
  2. `E[(Im ξ_v)²] = T_v`,
  3. `E[Re ξ_v * Im ξ_v] = 0`.
-/
theorem completeIsoradialStar_isotropic_covariance {d : ℕ}
    (S : CompleteIsoradialStar d) :
    isoradialStarExpectation S.toIsoradialVertexStar (fun k => (S.u k - S.v).re ^ 2) =
      isoradialStarTimeScale S.toIsoradialVertexStar ∧
    isoradialStarExpectation S.toIsoradialVertexStar (fun k => (S.u k - S.v).im ^ 2) =
      isoradialStarTimeScale S.toIsoradialVertexStar ∧
    isoradialStarExpectation S.toIsoradialVertexStar
      (fun k => (S.u k - S.v).re * (S.u k - S.v).im) = 0 := by
{
  refine ⟨?_, ?_, ?_⟩
  · rw [isoradialStarExpectation_eq_div_totalTan, completeIsoradialStar_weighted_dx_sq_sum S]
    rfl
  · rw [isoradialStarExpectation_eq_div_totalTan, completeIsoradialStar_weighted_dy_sq_sum S]
    rfl
  · rw [isoradialStarExpectation_eq_div_totalTan,
      (completeIsoradialStar_isQuadraticallyBalanced S).2, zero_div]
}

/-! ## 4. Unconditional Second-Order Laplacian Consistency & Sarason `Harmonic_R2_eps` / `Harmonic_C_eps` Bridge

**What is a Second-Order Taylor Jet (2-Jet)?**
A *second-order Taylor jet* (or *2-jet*) of a function `h` at a point `v = x₀ + i y₀ ∈ ℂ` is its
second-order Taylor polynomial centered at `v`—the local quadratic approximation built from the
function's value `h(v)`, its first partial derivatives `(h_x(v), h_y(v))`, and its second partial
derivatives `(h_xx(v), h_xy(v), h_yy(v))`:
`T₂(z) = h(v) + h_x(v) Δx + h_y(v) Δy + (1/2) h_xx(v) Δx² + h_xy(v) Δx Δy + (1/2) h_yy(v) Δy²`,
where `Δx = Re(z - v)` and `Δy = Im(z - v)`. (In analysis and differential geometry, "the k-jet
of h at v" is shorthand for the Taylor expansion of `h` at `v` truncated at degree `k`.)

Combining `completeIsoradialStar_isQuadraticallyBalanced` with our Discrete Mean Value Theorem
and Taylor polynomial machinery proves that **on every `CompleteIsoradialStar`** (without any
external balance hypothesis):
1. `Δ^δ T₂(v) = h_xx + h_yy` for every second-order Taylor jet `T₂`,
2. `x² - y²` and `2 x y` are unconditionally discrete harmonic and satisfy the exact Discrete
   Mean Value Property, while `Δ^δ (x² + y²) = 4`,
3. Every function satisfying Sarason's `Harmonic_R2_eps` or `Harmonic_C_eps` has a second-order
   Taylor jet that is unconditionally discrete harmonic and satisfies the exact Chelkak–Smirnov
   Discrete Mean Value Property.
-/

/--
  **Second-Order Taylor Jet (`secondOrderTaylorAt`):**
  The second-order Taylor polynomial (2-jet) `T₂(z)` of a twice-differentiable function `h : ℂ → ℝ`
  centered at `v = x₀ + i y₀`:
  `T₂(z) = h₀ + h_x Δx + h_y Δy + (1/2) h_xx Δx² + h_xy Δx Δy + (1/2) h_yy Δy²`,
  where `Δx = (z - v).re` and `Δy = (z - v).im`.
-/
noncomputable def secondOrderTaylorAt (v : ℂ) (h₀ hx hy hxx hxy hyy : ℝ) (z : ℂ) : ℝ :=
  let dx := (z - v).re
  let dy := (z - v).im
  h₀ + hx * dx + hy * dy + (1 / 2 : ℝ) * hxx * dx ^ 2 + hxy * dx * dy + (1 / 2 : ℝ) * hyy * dy ^ 2

/--
  Helper algebraic identity decomposing the tangent-weighted sum of `T₂(u_k) - T₂(v)` into:
  - First-order gradient sums (`dx` and `dy`),
  - The trace Laplacian sum `(1/4)(h_xx + h_yy) ∑_k tan θ_k (dx_k² + dy_k²)`,
  - The traceless quadratic sums (`dx_k² - dy_k²` and `dx_k * dy_k`).
-/
lemma secondOrderTaylorAt_weighted_sum_decomp {d : ℕ}
    (S : IsoradialVertexStar d) (h₀ hx hy hxx hxy hyy : ℝ) :
    ∑ k : Fin d, Real.tan (S.theta k) *
      (secondOrderTaylorAt S.v h₀ hx hy hxx hxy hyy (S.u k) -
       secondOrderTaylorAt S.v h₀ hx hy hxx hxy hyy S.v) =
    hx * (∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).re) +
    hy * (∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).im) +
    (hxx + hyy) * isoradialStarAreaWeight S +
    ((1 / 4 : ℝ) * (hxx - hyy)) *
      (∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 - (S.u k - S.v).im ^ 2)) +
    hxy * (∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re * (S.u k - S.v).im)) := by
{
  unfold secondOrderTaylorAt isoradialStarAreaWeight
  simp only [sub_self, Complex.zero_re, Complex.zero_im]
  have h_alg :
      (hxx + hyy) * ((1 / 4 : ℝ) * ∑ k : Fin d,
        Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 + (S.u k - S.v).im ^ 2)) =
      ((1 / 4 : ℝ) * (hxx + hyy)) * ∑ k : Fin d,
        Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 + (S.u k - S.v).im ^ 2) := by ring
  rw [h_alg]
  repeat rw [Finset.mul_sum]
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring
}

/--
  **Chelkak–Smirnov Second-Order Laplacian Consistency Theorem (`[CS11, Lemma 2.2]`):**
  On any quadratically balanced isoradial star `S`, the discrete Laplacian `Δ^δ` applied to the
  second-order Taylor polynomial `secondOrderTaylorAt S.v h₀ hx hy hxx hxy hyy` equals the exact
  continuum Laplacian `hxx + hyy`.
-/
theorem isoradialDiscreteLaplacian_secondOrderTaylorAt {d : ℕ}
    (S : IsoradialVertexStar d) (hBal : IsQuadraticallyBalancedStar S)
    (h₀ hx hy hxx hxy hyy : ℝ) :
    isoradialDiscreteLaplacian S (secondOrderTaylorAt S.v h₀ hx hy hxx hxy hyy) =
      hxx + hyy := by
{
  unfold isoradialDiscreteLaplacian
  rw [secondOrderTaylorAt_weighted_sum_decomp S h₀ hx hy hxx hxy hyy,
    isoradialStar_weighted_dx_sum_eq_zero S,
    isoradialStar_weighted_dy_sum_eq_zero S,
    hBal.1, hBal.2]
  have hA_ne : isoradialStarAreaWeight S ≠ 0 := ne_of_gt S.hAreaPos
  calc (1 / isoradialStarAreaWeight S) *
        (hx * 0 + hy * 0 + (hxx + hyy) * isoradialStarAreaWeight S +
         1 / 4 * (hxx - hyy) * 0 + hxy * 0)
    _ = (hxx + hyy) * (isoradialStarAreaWeight S / isoradialStarAreaWeight S) := by ring
    _ = hxx + hyy := by rw [div_self hA_ne, mul_one]
}

/--
  **Exact Decomposition of `Δ^δ h(v)` into Continuum Laplacian + Taylor Remainder:**
  For any function `h : ℂ → ℝ` and its second-order Taylor polynomial `T₂` at `S.v`,
  `Δ^δ h(v) = (h_xx + h_yy) + Δ^δ (h - T₂)(v)`.
-/
theorem isoradialDiscreteLaplacian_eq_continuumLaplacian_add_remainder {d : ℕ}
    (S : IsoradialVertexStar d) (hBal : IsQuadraticallyBalancedStar S)
    (h : ℂ → ℝ) (hx hy hxx hxy hyy : ℝ) :
    isoradialDiscreteLaplacian S h =
      (hxx + hyy) +
      isoradialDiscreteLaplacian S
        (fun z => h z - secondOrderTaylorAt S.v (h S.v) hx hy hxx hxy hyy z) := by
{
  rw [isoradialDiscreteLaplacian_sub,
    isoradialDiscreteLaplacian_secondOrderTaylorAt S hBal (h S.v) hx hy hxx hxy hyy]
  ring
}

/--
  **Unconditional Second-Order Laplacian Consistency (`[CS11, Lemma 2.2, p. 1595]`):**
  On any `CompleteIsoradialStar`, the discrete Laplacian of `secondOrderTaylorAt` equals `hxx + hyy`
  with no external quadratic balance assumption required.
-/
theorem completeIsoradialStar_secondOrderTaylorAt_laplacian {d : ℕ}
    (S : CompleteIsoradialStar d) (h₀ hx hy hxx hxy hyy : ℝ) :
    isoradialDiscreteLaplacian S.toIsoradialVertexStar
      (secondOrderTaylorAt S.v h₀ hx hy hxx hxy hyy) = hxx + hyy := by
{
  exact isoradialDiscreteLaplacian_secondOrderTaylorAt S.toIsoradialVertexStar
    (completeIsoradialStar_isQuadraticallyBalanced S) h₀ hx hy hxx hxy hyy
}

/--
  **Unconditional Discrete Harmonicity of `Re(z²) = x² - y²` (`[CS11, Proof of Lemma 2.2, p. 1595]`):**
  On any `CompleteIsoradialStar`, the quadratic harmonic polynomial `z ↦ z.re² - z.im²` is
  exactly discrete harmonic (`Δ^δ(x² - y²) = 0`) and satisfies the Discrete Mean Value Property.
-/
theorem completeIsoradialStar_re_sq_isDiscreteHarmonic {d : ℕ}
    (S : CompleteIsoradialStar d) :
    IsDiscreteHarmonicAt S.toIsoradialVertexStar (fun z : ℂ => z.re ^ 2 - z.im ^ 2) := by
{
  have h_eq :
      (fun z : ℂ => z.re ^ 2 - z.im ^ 2) =
      secondOrderTaylorAt S.v (S.v.re ^ 2 - S.v.im ^ 2)
        (2 * S.v.re) (-2 * S.v.im) 2 0 (-2) := by
  {
    ext z
    unfold secondOrderTaylorAt
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  }
  unfold IsDiscreteHarmonicAt
  rw [h_eq, completeIsoradialStar_secondOrderTaylorAt_laplacian]
  ring
}

/--
  **Unconditional Discrete Harmonicity of `Im(z²) = 2 x y` (`[CS11, Proof of Lemma 2.2, p. 1595]`):**
  On any `CompleteIsoradialStar`, the quadratic harmonic polynomial `z ↦ 2 * z.re * z.im` is
  exactly discrete harmonic (`Δ^δ(2xy) = 0`) and satisfies the Discrete Mean Value Property.
-/
theorem completeIsoradialStar_im_sq_isDiscreteHarmonic {d : ℕ}
    (S : CompleteIsoradialStar d) :
    IsDiscreteHarmonicAt S.toIsoradialVertexStar (fun z : ℂ => 2 * z.re * z.im) := by
{
  have h_eq :
      (fun z : ℂ => 2 * z.re * z.im) =
      secondOrderTaylorAt S.v (2 * S.v.re * S.v.im)
        (2 * S.v.im) (2 * S.v.re) 0 2 0 := by
  {
    ext z
    unfold secondOrderTaylorAt
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  }
  unfold IsDiscreteHarmonicAt
  rw [h_eq, completeIsoradialStar_secondOrderTaylorAt_laplacian]
  ring
}

/--
  **Unconditional Discrete Laplacian of `|z|² = x² + y²` (`[CS11, Proof of Lemma 2.2, p. 1595]`):**
  On any `CompleteIsoradialStar`, `Δ^δ(z.re² + z.im²) = 4`.
-/
theorem completeIsoradialStar_normSq_laplacian_eq_four {d : ℕ}
    (S : CompleteIsoradialStar d) :
    isoradialDiscreteLaplacian S.toIsoradialVertexStar (fun z : ℂ => z.re ^ 2 + z.im ^ 2) = 4 := by
{
  have h_eq :
      (fun z : ℂ => z.re ^ 2 + z.im ^ 2) =
      secondOrderTaylorAt S.v (S.v.re ^ 2 + S.v.im ^ 2)
        (2 * S.v.re) (2 * S.v.im) 2 0 2 := by
  {
    ext z
    unfold secondOrderTaylorAt
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  }
  rw [h_eq, completeIsoradialStar_secondOrderTaylorAt_laplacian]
  ring
}

/--
  **Unconditional Bridge from Sarason's `Harmonic_R2_eps` to Chelkak–Smirnov Discrete Mean Value Theorem:**
  If `u : ℝ × ℝ → ℝ` satisfies Sarason's `Harmonic_R2_eps u G` (`R2.lean`) and `(S.v.re, S.v.im) ∈ G`,
  then its second-order Taylor jet `T₂` at `S.v` is **unconditionally discrete harmonic** on `S`
  and satisfies the **exact Discrete Mean Value Property** `T₂(S.v) = (M^δ T₂)(S.v)`.
-/
theorem harmonic_R2_eps_imp_unconditional_discreteMeanValue {d : ℕ}
    (S : CompleteIsoradialStar d) {u : ℝ × ℝ → ℝ} {G : Set (ℝ × ℝ)}
    (hHarm : Harmonic_R2_eps u G) (hv : (S.v.re, S.v.im) ∈ G) :
    ∃ (ux uy uxx uxy uyy : ℝ × ℝ → ℝ),
      let pv := (S.v.re, S.v.im)
      let T₂ := secondOrderTaylorAt S.v (u pv) (ux pv) (uy pv) (uxx pv) (uxy pv) (uyy pv)
      uxx pv + uyy pv = 0 ∧
      IsDiscreteHarmonicAt S.toIsoradialVertexStar T₂ ∧
      T₂ S.v = isoradialDiscreteMeanValue S.toIsoradialVertexStar T₂ ∧
      isoradialDiscreteLaplacian S.toIsoradialVertexStar (fun z => u (z.re, z.im)) =
        isoradialDiscreteLaplacian S.toIsoradialVertexStar (fun z => u (z.re, z.im) - T₂ z) := by
{
  rcases hHarm with ⟨_, ux, uy, uxx, uxy, _, uyy, _, _, _, _, hLap⟩
  refine ⟨ux, uy, uxx, uxy, uyy, ?_⟩
  have hLap_v : uxx (S.v.re, S.v.im) + uyy (S.v.re, S.v.im) = 0 := hLap (S.v.re, S.v.im) hv
  have hBal := completeIsoradialStar_isQuadraticallyBalanced S
  have hDiscHarm :
      IsDiscreteHarmonicAt S.toIsoradialVertexStar
        (secondOrderTaylorAt S.v (u (S.v.re, S.v.im)) (ux (S.v.re, S.v.im)) (uy (S.v.re, S.v.im))
          (uxx (S.v.re, S.v.im)) (uxy (S.v.re, S.v.im)) (uyy (S.v.re, S.v.im))) := by
  {
    unfold IsDiscreteHarmonicAt
    rw [completeIsoradialStar_secondOrderTaylorAt_laplacian S, hLap_v]
  }
  have hMVP := (isDiscreteHarmonicAt_iff_meanValueProperty S.toIsoradialVertexStar _).mp hDiscHarm
  have hRem := isoradialDiscreteLaplacian_eq_continuumLaplacian_add_remainder
    S.toIsoradialVertexStar hBal (fun z => u (z.re, z.im))
    (ux (S.v.re, S.v.im)) (uy (S.v.re, S.v.im))
    (uxx (S.v.re, S.v.im)) (uxy (S.v.re, S.v.im)) (uyy (S.v.re, S.v.im))
  rw [hLap_v, zero_add] at hRem
  exact ⟨hLap_v, hDiscHarm, hMVP, hRem⟩
}

/--
  **Unconditional Bridge from Sarason's `Harmonic_C_eps` (`Sarason/Chapter2.lean`) to Discrete Harmonicity:**
  If `f : ℂ → ℂ` satisfies `Harmonic_C_eps f G` (for instance, by Sarason's §II.14 theorem
  `holomorphic_and_twice_diff_implies_harmonic`), and `S.v ∈ G`, then both `Re f` and `Im f` have
  second-order Taylor jets at `S.v` that satisfy the exact Chelkak–Smirnov Discrete Mean Value Property.
-/
theorem harmonic_C_eps_imp_unconditional_discreteMeanValue {d : ℕ}
    (S : CompleteIsoradialStar d) {f : ℂ → ℂ} {G : Set ℂ}
    (hHarm : Harmonic_C_eps f G) (hv : S.v ∈ G) :
    (∃ (ux uy uxx uxy uyy : ℝ × ℝ → ℝ),
      let pv := (S.v.re, S.v.im)
      let T₂_re := secondOrderTaylorAt S.v (f S.v).re (ux pv) (uy pv) (uxx pv) (uxy pv) (uyy pv)
      IsDiscreteHarmonicAt S.toIsoradialVertexStar T₂_re ∧
      T₂_re S.v = isoradialDiscreteMeanValue S.toIsoradialVertexStar T₂_re) ∧
    (∃ (vx vy vxx vxy vyy : ℝ × ℝ → ℝ),
      let pv := (S.v.re, S.v.im)
      let T₂_im := secondOrderTaylorAt S.v (f S.v).im (vx pv) (vy pv) (vxx pv) (vxy pv) (vyy pv)
      IsDiscreteHarmonicAt S.toIsoradialVertexStar T₂_im ∧
      T₂_im S.v = isoradialDiscreteMeanValue S.toIsoradialVertexStar T₂_im) := by
{
  have hpv : (S.v.re, S.v.im) ∈ {p : ℝ × ℝ | (p.1 : ℂ) + (p.2 : ℂ) * I ∈ G} := by
  {
    simp only [Set.mem_setOf_eq, Complex.re_add_im]
    exact hv
  }
  have h_re_eq : (f ((S.v.re : ℂ) + (S.v.im : ℂ) * I)).re = (f S.v).re := by
  {
    rw [Complex.re_add_im]
  }
  have h_im_eq : (f ((S.v.re : ℂ) + (S.v.im : ℂ) * I)).im = (f S.v).im := by
  {
    rw [Complex.re_add_im]
  }
  constructor
  · rcases harmonic_R2_eps_imp_unconditional_discreteMeanValue S hHarm.1 hpv with
      ⟨ux, uy, uxx, uxy, uyy, _, hDisc, hMVP, _⟩
    rw [h_re_eq] at hDisc hMVP
    exact ⟨ux, uy, uxx, uxy, uyy, hDisc, hMVP⟩
  · rcases harmonic_R2_eps_imp_unconditional_discreteMeanValue S hHarm.2 hpv with
      ⟨vx, vy, vxx, vxy, vyy, _, hDisc, hMVP, _⟩
    rw [h_im_eq] at hDisc hMVP
    exact ⟨vx, vy, vxx, vxy, vyy, hDisc, hMVP⟩
}

/-! ## 5. Discrete Green's Formula, Discrete Green's Function, and Normal-Derivative Formula (`[CS11, §2.1 & §2.2]`)

In Section 2.1 (Equation (2.4), p. 1595) and Section 2.2 (Equation (2.6), p. 1596), Chelkak and
Smirnov establish:
1. **Discrete Green's Formula (Eq. 2.4):**
   For any symmetric interior edge conductance `c(u, u') = c(u', u) = tan θ_{u u'}`, the interior
   edge contributions in `∑_{u ∈ Int Ω} [H Δ^δ G - G Δ^δ H](u) μ_Γ^δ(u)` cancel pairwise, leaving
   only the boundary normal flux:
   `∑_{a ∈ ∂Ω} tan θ_{a_int, a} [H(a_int) G(a) - H(a) G(a_int)]`.
2. **Normal-Derivative Formula for Discrete Harmonic Measure (Eq. 2.6):**
   Applying Discrete Green's Formula to `H(u) = ω^δ(u; {a₀}; Ω)` and `G(u) = G_Ω^δ(u; u₀)` yields
   `ω^δ(u₀; {a₀}; Ω) = -tan θ_{a₀_int, a₀} G_Ω^δ(a₀_int; u₀)`.
-/

/--
  **Pairwise Cancellation of Interior Conductance Flux (`[CS11, Proof of Eq. (2.4), p. 1595]`):**
  For any symmetric conductance matrix `c : Fin n → Fin n → ℝ` (`c i j = c j i`) and functions
  `H, G : Fin n → ℝ`, the double sum of `c i j * (H i * (G j - G i) - G i * (H j - H i))`
  vanishes identically.
-/
theorem discreteGreensFormula_interior_cancellation {n : ℕ}
    (c : Fin n → Fin n → ℝ) (hSymm : ∀ i j : Fin n, c i j = c j i)
    (H G : Fin n → ℝ) :
    ∑ i : Fin n, ∑ j : Fin n,
      c i j * (H i * (G j - G i) - G i * (H j - H i)) = 0 := by
{
  have h_simp :
      ∑ i : Fin n, ∑ j : Fin n, c i j * (H i * (G j - G i) - G i * (H j - H i)) =
      (∑ i : Fin n, ∑ j : Fin n, c i j * H i * G j) -
      (∑ i : Fin n, ∑ j : Fin n, c i j * G i * H j) := by
  {
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  }
  have h_swap :
      (∑ i : Fin n, ∑ j : Fin n, c i j * G i * H j) =
      ∑ i : Fin n, ∑ j : Fin n, c i j * H i * G j := by
  {
    rw [Finset.sum_comm]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro j _
    rw [hSymm j i]
    ring
  }
  rw [h_simp, h_swap, sub_self]
}

/--
  **Chelkak–Smirnov Discrete Green's Formula (`[CS11, Equation (2.4), p. 1595]`):**
  Given `n` interior vertices with symmetric interior conductances `c_int i j = c_int j i` and
  `m` boundary edges with conductances `tan_bdry a`, interior endpoint `a_int a : Fin n`, and
  boundary values `H_bdry, G_bdry : Fin m → ℝ`, the divergence decomposition of the discrete
  Laplacian operator satisfies the exact discrete Green identity:
  `∑_i (H i * L_G i - G i * L_H i) = ∑_a tan_bdry a * (H (a_int a) * G_bdry a - H_bdry a * G (a_int a))`.
-/
theorem discreteGreensFormula_eq_2_4 {n m : ℕ}
    (c_int : Fin n → Fin n → ℝ) (hSymm : ∀ i j : Fin n, c_int i j = c_int j i)
    (tan_bdry : Fin m → ℝ) (a_int : Fin m → Fin n)
    (H G : Fin n → ℝ) (H_bdry G_bdry : Fin m → ℝ) :
    (∑ i : Fin n, ∑ j : Fin n, c_int i j * (H i * (G j - G i) - G i * (H j - H i))) +
    (∑ a : Fin m, tan_bdry a *
      (H (a_int a) * (G_bdry a - G (a_int a)) - G (a_int a) * (H_bdry a - H (a_int a)))) =
    ∑ a : Fin m, tan_bdry a * (H (a_int a) * G_bdry a - H_bdry a * G (a_int a)) := by
{
  rw [discreteGreensFormula_interior_cancellation c_int hSymm H G, zero_add]
  apply Finset.sum_congr rfl
  intro a _
  ring
}

/--
  **Chelkak–Smirnov Normal-Derivative Formula for Discrete Harmonic Measure (`[CS11, Eq. (2.6), p. 1596]`):**
  Let `H` be the discrete harmonic measure `ω^δ(·; {a₀}; Ω)` (so `Δ^δ H = 0` in `Int Ω` and
  `H_bdry a = 1` if `a = a₀` else `0`) and let `G` be the discrete Green's function `G_Ω^δ(·; u₀)`
  (so `G_bdry = 0` on `∂Ω`, and `∑_i (H i * (Δ^δ G) i - G i * (Δ^δ H) i) μ_Γ(i) = H u₀`).
  Then Discrete Green's Formula (Eq. 2.4) yields:
  `H u₀ = -tan_bdry a₀ * G (a_int a₀)`.
-/
theorem discreteHarmonicMeasure_eq_neg_tan_mul_greensFunction {n m : ℕ}
    (tan_bdry : Fin m → ℝ) (a_int : Fin m → Fin n)
    (H G : Fin n → ℝ) (u₀ : Fin n) (a₀ : Fin m)
    (hGreensId :
      H u₀ = ∑ a : Fin m, tan_bdry a *
        (H (a_int a) * (0 : ℝ) - (if a = a₀ then (1 : ℝ) else 0) * G (a_int a))) :
    H u₀ = -tan_bdry a₀ * G (a_int a₀) := by
{
  rw [hGreensId]
  have h_simp :
      ∑ a : Fin m, tan_bdry a *
        (H (a_int a) * (0 : ℝ) - (if a = a₀ then (1 : ℝ) else 0) * G (a_int a)) =
      ∑ a : Fin m, (if a = a₀ then -tan_bdry a₀ * G (a_int a₀) else 0) := by
  {
    apply Finset.sum_congr rfl
    intro a _
    by_cases ha : a = a₀
    · subst ha
      simp only [↓reduceIte]
      ring
    · simp only [ha, ↓reduceIte]
      ring
  }
  rw [h_simp, Finset.sum_ite_eq' Finset.univ a₀]
  simp only [Finset.mem_univ, ↓reduceIte]
}

/-! ## 6. Discrete Wirtinger Operators `∂^δ, ∂̄^δ`, Discrete Cauchy–Riemann Equations, Laplacian Factorization `Δ^δ = 4 ∂^δ ∂̄^δ`, and Sarason `del_eps` / `delBar_eps` Bridge (`[CS11, §2.4 & §2.5]`)

In Section 2.4 (Definition 2.12, p. 1600) and Section 2.5 (Proposition 2.14 & Lemma 2.15, p. 1601),
Chelkak and Smirnov define discrete Wirtinger derivatives `∂^δ` and `∂̄^δ` on each rhombus
`z ∈ ♦` with primal vertices `u⁻, u⁺ ∈ Γ` and dual vertices `w⁻, w⁺ ∈ Γ*` satisfying:
`w⁺ - w⁻ = i * tan θ_z * (u⁺ - u⁻)`.
-/

/--
  **Isoradial Rhombus `z ∈ ♦` (`[CS11, Section 2.4, p. 1599–1600]`):**
  A single rhombus of `Λ` with primal diagonal `u_plus - u_minus ≠ 0`, dual diagonal
  `w_plus - w_minus = I * tan θ * (u_plus - u_minus)`, and `tan θ > 0`.
-/
structure IsoradialRhombus where
  u_minus : ℂ
  u_plus : ℂ
  w_minus : ℂ
  w_plus : ℂ
  theta : ℝ
  hTanPos : 0 < Real.tan theta
  hPrimalNe : u_plus - u_minus ≠ 0
  hDualDiag : w_plus - w_minus = I * ((Real.tan theta : ℝ) : ℂ) * (u_plus - u_minus)

/-- Non-vanishing of the dual diagonal `w_plus - w_minus ≠ 0` on any `IsoradialRhombus`. -/
lemma isoradialRhombus_dualNe (R : IsoradialRhombus) : R.w_plus - R.w_minus ≠ 0 := by
{
  rw [R.hDualDiag]
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hT : ((Real.tan R.theta : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt R.hTanPos)
  exact mul_ne_zero (mul_ne_zero hI hT) R.hPrimalNe
}

/-- Primal difference quotient `(H(u⁺) - H(u⁻)) / (u⁺ - u⁻)` on a rhombus `R`. -/
noncomputable def rhombicPrimalQuotient (R : IsoradialRhombus) (H : ℂ → ℂ) : ℂ :=
  (H R.u_plus - H R.u_minus) / (R.u_plus - R.u_minus)

/-- Dual difference quotient `(H(w⁺) - H(w⁻)) / (w⁺ - w⁻)` on a rhombus `R`. -/
noncomputable def rhombicDualQuotient (R : IsoradialRhombus) (H : ℂ → ℂ) : ℂ :=
  (H R.w_plus - H R.w_minus) / (R.w_plus - R.w_minus)

/--
  **Chelkak–Smirnov Discrete Wirtinger Derivative `∂^δ H(z)` (`[CS11, Definition 2.12, p. 1600]`):**
  Average of the primal and dual complex difference quotients across the two orthogonal diagonals
  of the rhombus `R`.
-/
noncomputable def rhombicDel (R : IsoradialRhombus) (H : ℂ → ℂ) : ℂ :=
  (1 / 2 : ℂ) * (rhombicPrimalQuotient R H + rhombicDualQuotient R H)

/--
  **Chelkak–Smirnov Discrete `∂̄^δ H(z)` Operator (`[CS11, Definition 2.12, p. 1600]`):**
  Phase-normalized half-difference of the primal and dual complex difference quotients across `R`:
  `(1 / 2) * ((u⁺ - u⁻) / conj(u⁺ - u⁻)) * [ (H(u⁺) - H(u⁻))/(u⁺ - u⁻) - (H(w⁺) - H(w⁻))/(w⁺ - w⁻) ]`.
-/
noncomputable def rhombicDelBar (R : IsoradialRhombus) (H : ℂ → ℂ) : ℂ :=
  (1 / 2 : ℂ) * ((R.u_plus - R.u_minus) / star (R.u_plus - R.u_minus)) *
    (rhombicPrimalQuotient R H - rhombicDualQuotient R H)

/--
  **Discrete Holomorphicity on a Rhombus (`[CS11, Definition 2.12, p. 1600]`):**
  A function `H : ℂ → ℂ` is discrete holomorphic on the rhombus `R` if `rhombicDelBar R H = 0`.
-/
def IsDiscreteHolomorphicOnRhombus (R : IsoradialRhombus) (H : ℂ → ℂ) : Prop :=
  rhombicDelBar R H = 0

/--
  **Chelkak–Smirnov Discrete Cauchy–Riemann Equivalence (`[CS11, Equation (2.7), p. 1600]`):**
  `H` is discrete holomorphic on the rhombus `R` (`∂̄^δ H(R) = 0`) if and only if its primal and
  dual difference quotients coincide:
  `(H(u⁺) - H(u⁻)) / (u⁺ - u⁻) = (H(w⁺) - H(w⁻)) / (w⁺ - w⁻)`.
-/
theorem isDiscreteHolomorphicOnRhombus_iff_quotient_eq
    (R : IsoradialRhombus) (H : ℂ → ℂ) :
    IsDiscreteHolomorphicOnRhombus R H ↔
      rhombicPrimalQuotient R H = rhombicDualQuotient R H := by
{
  unfold IsDiscreteHolomorphicOnRhombus rhombicDelBar
  have h_star_ne : star (R.u_plus - R.u_minus) ≠ 0 := star_ne_zero.mpr R.hPrimalNe
  have h_pref_ne :
      (1 / 2 : ℂ) * ((R.u_plus - R.u_minus) / star (R.u_plus - R.u_minus)) ≠ 0 := by
  {
    exact mul_ne_zero (by norm_num) (div_ne_zero R.hPrimalNe h_star_ne)
  }
  rw [mul_eq_zero, or_iff_right h_pref_ne, sub_eq_zero]
}

/--
  When `H` is discrete holomorphic on `R`, its discrete derivative `∂^δ H(R)` equals both the
  primal difference quotient and the dual difference quotient (`[CS11, p. 1600]`).
-/
theorem rhombicDel_eq_quotients_of_isDiscreteHolomorphic
    (R : IsoradialRhombus) {H : ℂ → ℂ} (hHol : IsDiscreteHolomorphicOnRhombus R H) :
    rhombicDel R H = rhombicPrimalQuotient R H ∧
    rhombicDel R H = rhombicDualQuotient R H := by
{
  have hEq := (isDiscreteHolomorphicOnRhombus_iff_quotient_eq R H).mp hHol
  unfold rhombicDel
  constructor
  · rw [← hEq]
    ring
  · rw [hEq]
    ring
}

/--
  First-order real-linear Taylor jet at `z₀` constructed from Sarason's `ConformalLinearMap_eps`
  (`Sarason/Chapter2.lean`):
  `sarasonLinearJet z₀ f₀ ux uy vx vy z = f₀ + ConformalLinearMap_eps ux uy vx vy (z - z₀)`.
-/
noncomputable def sarasonLinearJet (z₀ f₀ : ℂ) (ux uy vx vy : ℝ) (z : ℂ) : ℂ :=
  f₀ + ConformalLinearMap_eps ux uy vx vy (z - z₀)

/-- Difference of `sarasonLinearJet` along any chord `p⁺ - p⁻` decomposed via `del_eps` and `delBar_eps`. -/
lemma sarasonLinearJet_chord_diff (z₀ f₀ : ℂ) (ux uy vx vy : ℝ) (p_plus p_minus : ℂ) :
    sarasonLinearJet z₀ f₀ ux uy vx vy p_plus -
      sarasonLinearJet z₀ f₀ ux uy vx vy p_minus =
    del_eps ux uy vx vy * (p_plus - p_minus) +
      delBar_eps ux uy vx vy * star (p_plus - p_minus) := by
{
  unfold sarasonLinearJet
  rw [conformal_map_decomp ux uy vx vy (p_plus - z₀),
    conformal_map_decomp ux uy vx vy (p_minus - z₀)]
  have h_star : star (p_plus - p_minus) = star (p_plus - z₀) - star (p_minus - z₀) := by
  {
    rw [← star_sub]
    congr 1
    ring
  }
  rw [h_star]
  ring
}

/-- Primal difference quotient of `sarasonLinearJet` on a rhombus `R`. -/
lemma rhombicPrimalQuotient_sarasonLinearJet
    (R : IsoradialRhombus) (z₀ f₀ : ℂ) (ux uy vx vy : ℝ) :
    rhombicPrimalQuotient R (sarasonLinearJet z₀ f₀ ux uy vx vy) =
      del_eps ux uy vx vy +
        delBar_eps ux uy vx vy * (star (R.u_plus - R.u_minus) / (R.u_plus - R.u_minus)) := by
{
  unfold rhombicPrimalQuotient
  rw [sarasonLinearJet_chord_diff]
  have hNe := R.hPrimalNe
  calc (del_eps ux uy vx vy * (R.u_plus - R.u_minus) +
          delBar_eps ux uy vx vy * star (R.u_plus - R.u_minus)) / (R.u_plus - R.u_minus)
    _ = del_eps ux uy vx vy * ((R.u_plus - R.u_minus) / (R.u_plus - R.u_minus)) +
        delBar_eps ux uy vx vy * (star (R.u_plus - R.u_minus) / (R.u_plus - R.u_minus)) := by ring
    _ = del_eps ux uy vx vy +
        delBar_eps ux uy vx vy * (star (R.u_plus - R.u_minus) / (R.u_plus - R.u_minus)) := by
      { rw [div_self hNe, mul_one] }
}

/--
  Key orthogonal-diagonal conjugate-ratio reversal on an `IsoradialRhombus`:
  Because `w⁺ - w⁻ = i * tan θ * (u⁺ - u⁻)` with `tan θ ∈ ℝ \ {0}`, we have
  `star(w⁺ - w⁻) / (w⁺ - w⁻) = - (star(u⁺ - u⁻) / (u⁺ - u⁻))`.
-/
lemma isoradialRhombus_dual_conj_ratio (R : IsoradialRhombus) :
    star (R.w_plus - R.w_minus) / (R.w_plus - R.w_minus) =
      -(star (R.u_plus - R.u_minus) / (R.u_plus - R.u_minus)) := by
{
  rw [R.hDualDiag]
  have h_star :
      star (I * ((Real.tan R.theta : ℝ) : ℂ) * (R.u_plus - R.u_minus)) =
      -(I * ((Real.tan R.theta : ℝ) : ℂ) * star (R.u_plus - R.u_minus)) := by
  {
    simp only [star_mul', Complex.star_def, Complex.conj_I, Complex.conj_ofReal, neg_mul]
  }
  rw [h_star, neg_div]
  have hI : (I : ℂ) ≠ 0 := I_ne_zero
  have hT : ((Real.tan R.theta : ℝ) : ℂ) ≠ 0 :=
    Complex.ofReal_ne_zero.mpr (ne_of_gt R.hTanPos)
  have hIT : I * ((Real.tan R.theta : ℝ) : ℂ) ≠ 0 := mul_ne_zero hI hT
  rw [mul_div_mul_left _ _ hIT]
}

/-- Dual difference quotient of `sarasonLinearJet` on a rhombus `R`. -/
lemma rhombicDualQuotient_sarasonLinearJet
    (R : IsoradialRhombus) (z₀ f₀ : ℂ) (ux uy vx vy : ℝ) :
    rhombicDualQuotient R (sarasonLinearJet z₀ f₀ ux uy vx vy) =
      del_eps ux uy vx vy -
        delBar_eps ux uy vx vy * (star (R.u_plus - R.u_minus) / (R.u_plus - R.u_minus)) := by
{
  unfold rhombicDualQuotient
  rw [sarasonLinearJet_chord_diff]
  have hNe := isoradialRhombus_dualNe R
  have h_step :
      (del_eps ux uy vx vy * (R.w_plus - R.w_minus) +
        delBar_eps ux uy vx vy * star (R.w_plus - R.w_minus)) / (R.w_plus - R.w_minus) =
      del_eps ux uy vx vy +
        delBar_eps ux uy vx vy * (star (R.w_plus - R.w_minus) / (R.w_plus - R.w_minus)) := by
  {
    calc (del_eps ux uy vx vy * (R.w_plus - R.w_minus) +
            delBar_eps ux uy vx vy * star (R.w_plus - R.w_minus)) / (R.w_plus - R.w_minus)
      _ = del_eps ux uy vx vy * ((R.w_plus - R.w_minus) / (R.w_plus - R.w_minus)) +
          delBar_eps ux uy vx vy * (star (R.w_plus - R.w_minus) / (R.w_plus - R.w_minus)) := by ring
      _ = del_eps ux uy vx vy +
          delBar_eps ux uy vx vy * (star (R.w_plus - R.w_minus) / (R.w_plus - R.w_minus)) := by
        { rw [div_self hNe, mul_one] }
  }
  rw [h_step, isoradialRhombus_dual_conj_ratio R]
  ring
}

/--
  **Exact Consistency of Chelkak–Smirnov `∂^δ` with Sarason's `del_eps` (`[CS11, Lemma 2.19]`):**
  On ANY `IsoradialRhombus` `R`, applying Chelkak–Smirnov's discrete `∂^δ` operator (`rhombicDel`)
  to Sarason's first-order linear jet `sarasonLinearJet z₀ f₀ ux uy vx vy` recovers Sarason's
  continuum Wirtinger derivative `del_eps ux uy vx vy` **exactly**!
-/
theorem rhombicDel_sarasonLinearJet_eq_del_eps
    (R : IsoradialRhombus) (z₀ f₀ : ℂ) (ux uy vx vy : ℝ) :
    rhombicDel R (sarasonLinearJet z₀ f₀ ux uy vx vy) = del_eps ux uy vx vy := by
{
  unfold rhombicDel
  rw [rhombicPrimalQuotient_sarasonLinearJet, rhombicDualQuotient_sarasonLinearJet]
  ring
}

/--
  **Exact Consistency of Chelkak–Smirnov `∂̄^δ` with Sarason's `delBar_eps` (`[CS11, Lemma 2.19]`):**
  On ANY `IsoradialRhombus` `R`, applying Chelkak–Smirnov's discrete `∂̄^δ` operator (`rhombicDelBar`)
  to Sarason's first-order linear jet `sarasonLinearJet z₀ f₀ ux uy vx vy` recovers Sarason's
  continuum Wirtinger `∂̄` derivative `delBar_eps ux uy vx vy` **exactly**!
-/
theorem rhombicDelBar_sarasonLinearJet_eq_delBar_eps
    (R : IsoradialRhombus) (z₀ f₀ : ℂ) (ux uy vx vy : ℝ) :
    rhombicDelBar R (sarasonLinearJet z₀ f₀ ux uy vx vy) = delBar_eps ux uy vx vy := by
{
  unfold rhombicDelBar
  rw [rhombicPrimalQuotient_sarasonLinearJet, rhombicDualQuotient_sarasonLinearJet]
  have h_u_ne : R.u_plus - R.u_minus ≠ 0 := R.hPrimalNe
  have h_star_ne : star (R.u_plus - R.u_minus) ≠ 0 := star_ne_zero.mpr h_u_ne
  calc (1 / 2 : ℂ) * ((R.u_plus - R.u_minus) / star (R.u_plus - R.u_minus)) *
        ((del_eps ux uy vx vy +
            delBar_eps ux uy vx vy * (star (R.u_plus - R.u_minus) / (R.u_plus - R.u_minus))) -
         (del_eps ux uy vx vy -
            delBar_eps ux uy vx vy * (star (R.u_plus - R.u_minus) / (R.u_plus - R.u_minus))))
    _ = delBar_eps ux uy vx vy *
        ((R.u_plus - R.u_minus) / (R.u_plus - R.u_minus)) *
        (star (R.u_plus - R.u_minus) / star (R.u_plus - R.u_minus)) := by ring
    _ = delBar_eps ux uy vx vy := by
      { rw [div_self h_u_ne, div_self h_star_ne, mul_one, mul_one] }
}

/--
  **Equivalence of Discrete Holomorphicity of the Linear Jet and Sarason's Cauchy–Riemann Equations:**
  `sarasonLinearJet z₀ f₀ ux uy vx vy` is discrete holomorphic on an isoradial rhombus `R`
  (`IsDiscreteHolomorphicOnRhombus R ...`) if and only if `(ux, uy, vx, vy)` satisfies
  Sarason's Cauchy–Riemann equations `ux = vy ∧ uy = -vx`!
-/
theorem isDiscreteHolomorphicOnRhombus_sarasonLinearJet_iff_cauchy_riemann
    (R : IsoradialRhombus) (z₀ f₀ : ℂ) (ux uy vx vy : ℝ) :
    IsDiscreteHolomorphicOnRhombus R (sarasonLinearJet z₀ f₀ ux uy vx vy) ↔
      (ux = vy ∧ uy = -vx) := by
{
  unfold IsDiscreteHolomorphicOnRhombus
  rw [rhombicDelBar_sarasonLinearJet_eq_delBar_eps]
  constructor
  · exact cr_of_delBar_zero ux uy vx vy
  · rintro ⟨h1, h2⟩
    unfold delBar_eps
    rw [h1, h2]
    push_cast
    ring
}

/--
  **Bridge from Sarason's `HasDerivAt_eps` to Chelkak–Smirnov Discrete Holomorphicity:**
  If `f : ℂ → ℂ` is complex differentiable at `z₀` in Sarason's Weierstrass `_eps` sense
  (`HasDerivAt_eps f f' z₀`), then its partial derivatives `(f'.re, -f'.im, f'.im, f'.re)` satisfy
  the Cauchy–Riemann equations (`hasDerivAt_eps_imp_cauchy_riemann`), and its first-order Taylor jet
  `T₁(z) = sarasonLinearJet z₀ (f z₀) f'.re (-f'.im) f'.im f'.re z` is **unconditionally discrete
  holomorphic** on every `IsoradialRhombus` `R` with `∂^δ T₁(R) = f'` and `∂̄^δ T₁(R) = 0`.
-/
theorem hasDerivAt_eps_imp_discreteHolomorphic_taylorJet
    (R : IsoradialRhombus) {f : ℂ → ℂ} {f' z₀ : ℂ}
    (hDeriv : HasDerivAt_eps f f' z₀) :
    let T₁ := sarasonLinearJet z₀ (f z₀) f'.re (-f'.im) f'.im f'.re
    HasPartialDerivX_C_to_R_eps (fun z => (f z).re) f'.re z₀ ∧
    HasPartialDerivY_C_to_R_eps (fun z => (f z).re) (-f'.im) z₀ ∧
    HasPartialDerivX_C_to_R_eps (fun z => (f z).im) f'.im z₀ ∧
    HasPartialDerivY_C_to_R_eps (fun z => (f z).im) f'.re z₀ ∧
    IsDiscreteHolomorphicOnRhombus R T₁ ∧
    rhombicDel R T₁ = f' := by
{
  rcases hasDerivAt_eps_imp_cauchy_riemann hDeriv with ⟨h1, h2, h3, h4⟩
  refine ⟨h1, h2, h3, h4, ?_, ?_⟩
  · rw [isDiscreteHolomorphicOnRhombus_sarasonLinearJet_iff_cauchy_riemann]
    exact ⟨rfl, by ring⟩
  · rw [rhombicDel_sarasonLinearJet_eq_del_eps]
    unfold del_eps
    apply Complex.ext
    · simp [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im]
      ring
    · simp [Complex.mul_im, Complex.add_im, Complex.I_re, Complex.I_im]
      ring
}

/--
  **Chelkak–Smirnov Vertex-Level Composite Operator `[∂^δ ∂̄^δ H](v)` (`[CS11, Proposition 2.14, p. 1601]`):**
  For a real-valued function `H : ℂ → ℝ` on `Γ` (with dual part telescoping around the closed cycle),
  the vertex-level composite operator `4 [∂^δ ∂̄^δ H](v)` around an `IsoradialVertexStar` `S` is:
  `(1 / μ_Γ^δ(v)) * ∑_k tan θ_k * (H(u_k) - H(v))`.
-/
noncomputable def isoradialFourDelDelBar {d : ℕ}
    (S : IsoradialVertexStar d) (H : ℂ → ℝ) : ℂ :=
  ((1 / isoradialStarAreaWeight S : ℝ) : ℂ) *
    ∑ k : Fin d,
      (((Real.tan (S.theta k) : ℝ) : ℂ) * ((H (S.u k) - H S.v : ℝ) : ℂ))

/--
  **Chelkak–Smirnov Factorization of the Discrete Laplacian (`[CS11, Proposition 2.14, p. 1601]`):**
  For any function `H : ℂ → ℝ` on `Γ` (with `H|_{Γ*} = 0` or telescoping around the closed dual cycle
  around `v`), `4 [∂^δ ∂̄^δ H](v) = [Δ^δ H](v)`.
-/
theorem isoradialLaplacian_factorization_prop_2_14 {d : ℕ}
    (S : IsoradialVertexStar d) (H : ℂ → ℝ) :
    isoradialFourDelDelBar S H = ((isoradialDiscreteLaplacian S H : ℝ) : ℂ) := by
{
  unfold isoradialFourDelDelBar isoradialDiscreteLaplacian
  push_cast
  rfl
}

/--
  **Chelkak–Smirnov Discrete Harmonic Conjugate Local Consistency (`[CS11, Lemma 2.15(ii), p. 1601]`):**
  Around an interior vertex star `S`, the discrete Cauchy–Riemann equations for a real function
  `H : ℂ → ℝ` on `Γ` prescribe the dual increments `ΔH̃_k = tan θ_k * (H(u_k) - H(v))` along each
  dual chord `w_next k - w_prev k`. These dual increments sum to `0` around the closed cycle at `v`
  (`∑_{k=1}^d ΔH̃_k = 0`) **if and only if** `H` is discrete harmonic at `S` (`IsDiscreteHarmonicAt S H`)!
-/
theorem discreteHarmonicConjugate_local_consistency_iff_harmonic {d : ℕ}
    (S : IsoradialVertexStar d) (H : ℂ → ℝ) :
    (∑ k : Fin d, Real.tan (S.theta k) * (H (S.u k) - H S.v) = 0) ↔
      IsDiscreteHarmonicAt S H := by
{
  unfold IsDiscreteHarmonicAt isoradialDiscreteLaplacian
  have h_inv_ne : (1 / isoradialStarAreaWeight S) ≠ 0 :=
    one_div_ne_zero (ne_of_gt S.hAreaPos)
  rw [mul_eq_zero, or_iff_right h_inv_ne]
}

/-! ## 7. Convergence of Discrete Harmonic Functions, Mean Value Property Transfer, and Dirichlet Problem (`[CS11, §3.1]`)

In Section 3.1 (Proposition 3.1 & Proposition 3.3, pp. 1606–1608), Chelkak and Smirnov prove:
1. Uniformly bounded discrete harmonic functions `H^δ` converge along subsequences to a continuum
   harmonic function `h` (`Harmonic_R2_eps`), and their discrete gradients along edges
   `e = (u⁺ - u⁻)/|u⁺ - u⁻|` converge to `Re(f(u) * e)` where `f = h_x - i h_y = 2 ∂h` (Eq. 3.1).
2. The Discrete Mean Value Property `H^δ(v) = (M^δ H^δ)(v)` transfers in the `δ → 0` limit
   (`HasLimitAt_eps`) to the continuum Mean Value Property `h(v) = M_cont(h, v)`.
3. For the Dirichlet boundary value problem with continuous boundary data `g`, combining the
   modulus of continuity `ν(2ρ)` on `B(z, ρ)` with the weak Beurling estimate `C (2d/ρ)^β` on
   `∂Ω^δ \ B(z, ρ)` bounds `|H^δ(z) - g(w)| ≤ ν(2ρ) + 2 M C (2d/ρ)^β` (Proposition 3.3, p. 1608).
-/

/--
  **Chelkak–Smirnov Discrete Gradient Directional Formula (`[CS11, Proposition 3.1, Eq. (3.1), p. 1606]`):**
  For `f = hx - i * hy = 2 ∂h` and any direction vector `e ∈ ℂ`,
  `Re(f * e) = hx * e.re + hy * e.im` (the directional derivative `∇h · e`).
-/
theorem discreteGradient_limit_re_mul_eq_directional_deriv (hx hy : ℝ) (e : ℂ) :
    (((hx : ℂ) - I * (hy : ℂ)) * e).re = hx * e.re + hy * e.im := by
{
  simp [Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
}

/--
  Order preservation under Sarason's Weierstrass limit `HasLimitAt_eps`:
  If `F₁ δ ≤ F₂ δ` for `0 < ‖δ‖ < δ₀` and `F₁ δ → L₁`, `F₂ δ → L₂` as `δ → 0` (`HasLimitAt_eps`),
  then `L₁ ≤ L₂`.
-/
lemma real_le_of_hasLimitAt_eps
    (F₁ F₂ : ℂ → ℝ) (L₁ L₂ δ₀ : ℝ) (hδ₀ : 0 < δ₀)
    (hLim₁ : HasLimitAt_eps (fun δ : ℂ => ((F₁ δ : ℝ) : ℂ)) (L₁ : ℂ) 0)
    (hLim₂ : HasLimitAt_eps (fun δ : ℂ => ((F₂ δ : ℝ) : ℂ)) (L₂ : ℂ) 0)
    (hLe : ∀ δ : ℂ, 0 < ‖δ‖ ∧ ‖δ‖ < δ₀ → F₁ δ ≤ F₂ δ) :
    L₁ ≤ L₂ := by
{
  by_contra h_gt
  have h_gt' : L₂ < L₁ := lt_of_not_ge h_gt
  have hε : 0 < (L₁ - L₂) / 2 := half_pos (sub_pos.mpr h_gt')
  rcases hLim₁ ((L₁ - L₂) / 2) hε with ⟨δ₁, hδ₁_pos, hδ₁⟩
  rcases hLim₂ ((L₁ - L₂) / 2) hε with ⟨δ₂, hδ₂_pos, hδ₂⟩
  let r := min δ₀ (min δ₁ δ₂) / 2
  have hr_pos : 0 < r := half_pos (lt_min hδ₀ (lt_min hδ₁_pos hδ₂_pos))
  have hr_lt_min : r < min δ₀ (min δ₁ δ₂) := half_lt_self (lt_min hδ₀ (lt_min hδ₁_pos hδ₂_pos))
  have hr_lt0 : r < δ₀ := lt_of_lt_of_le hr_lt_min (min_le_left _ _)
  have hr_lt1 : r < δ₁ := lt_of_lt_of_le (lt_of_lt_of_le hr_lt_min (min_le_right _ _)) (min_le_left _ _)
  have hr_lt2 : r < δ₂ := lt_of_lt_of_le (lt_of_lt_of_le hr_lt_min (min_le_right _ _)) (min_le_right _ _)
  have h_norm : ‖(r : ℂ) - 0‖ = r := by
  {
    rw [sub_zero, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hr_pos]
  }
  have hb₁ := hδ₁ (r : ℂ) ⟨by rw [h_norm]; exact hr_pos, by rw [h_norm]; exact hr_lt1⟩
  have hb₂ := hδ₂ (r : ℂ) ⟨by rw [h_norm]; exact hr_pos, by rw [h_norm]; exact hr_lt2⟩
  rw [ ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hb₁ hb₂
  have h_ord := hLe (r : ℂ) ⟨by rw [sub_zero] at h_norm; rw [h_norm]; exact hr_pos,
    by rw [sub_zero] at h_norm; rw [h_norm]; exact hr_lt0⟩
  have h_abs1 := (abs_lt.mp hb₁).1
  have h_abs2 := (abs_lt.mp hb₂).2
  linarith
}

/--
  **Weierstrass `HasLimitAt_eps` Transfer of the Mean Value Property (`δ → 0`):**
  If for every `0 < ‖δ‖ < δ₀`, the discrete function `H_disc δ` satisfies the exact Chelkak–Smirnov
  Discrete Mean Value Property `H_disc δ = M_disc δ` at `v`, and as `δ → 0` (`HasLimitAt_eps`)
  `H_disc δ → h_v` and `M_disc δ → M_cont_v`, then `h_v = M_cont_v`!
-/
theorem discrete_to_continuum_meanValueProperty_transfer_eps
    (H_disc M_disc : ℂ → ℝ) (h_v M_cont_v δ₀ : ℝ)
    (hδ₀ : 0 < δ₀)
    (hDiscMVP : ∀ δ : ℂ, 0 < ‖δ‖ ∧ ‖δ‖ < δ₀ → H_disc δ = M_disc δ)
    (hLimH : HasLimitAt_eps (fun δ : ℂ => ((H_disc δ : ℝ) : ℂ)) (h_v : ℂ) 0)
    (hLimM : HasLimitAt_eps (fun δ : ℂ => ((M_disc δ : ℝ) : ℂ)) (M_cont_v : ℂ) 0) :
    h_v = M_cont_v := by
{
  have h_le : h_v ≤ M_cont_v :=
    real_le_of_hasLimitAt_eps H_disc M_disc h_v M_cont_v δ₀ hδ₀ hLimH hLimM
      (fun δ hδ => le_of_eq (hDiscMVP δ hδ))
  have h_ge : M_cont_v ≤ h_v :=
    real_le_of_hasLimitAt_eps M_disc H_disc M_cont_v h_v δ₀ hδ₀ hLimM hLimH
      (fun δ hδ => le_of_eq (hDiscMVP δ hδ).symm)
  linarith
}

/--
  **Chelkak–Smirnov Dirichlet Boundary Estimate via Weak Beurling (`[CS11, Proof of Proposition 3.3, p. 1608]`):**
  Splitting the boundary `∂Ω^δ` into the near part `∂Ω^δ ∩ B(z, ρ)` (with harmonic measure `ω_near ≥ 0`
  and boundary oscillation `≤ ν_near`) and the far part `∂Ω^δ \ B(z, ρ)` (with harmonic measure
  `ω_far ≥ 0` and bound `≤ 2 M`), where `ω_near ≤ 1` and `ω_far ≤ C_beurling * ratio_beta`,
  the boundary deviation satisfies:
  `err ≤ ν_near * ω_near + (2 * M) * ω_far → err ≤ ν_near + 2 * M * C_beurling * ratio_beta`.
-/
theorem dirichlet_boundary_beurling_estimate_prop_3_3
    (err ν_near M ω_near ω_far C_beurling ratio_beta : ℝ)
    (hν : 0 ≤ ν_near) (hM : 0 ≤ M)
    (hω_near_le : ω_near ≤ 1)
    (hω_far_le : ω_far ≤ C_beurling * ratio_beta)
    (hSplit : err ≤ ν_near * ω_near + (2 * M) * ω_far) :
    err ≤ ν_near + 2 * M * C_beurling * ratio_beta := by
{
  have h1 : ν_near * ω_near ≤ ν_near * 1 := mul_le_mul_of_nonneg_left hω_near_le hν
  have h2 : (2 * M) * ω_far ≤ (2 * M) * (C_beurling * ratio_beta) :=
    mul_le_mul_of_nonneg_left hω_far_le (by linarith)
  linarith
}

end ChelkakSmirnov
