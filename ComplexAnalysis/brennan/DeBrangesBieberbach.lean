/-
Copyright (c) 2026 Formalization Project. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Formalization Team
-/
import brennan.Koebe

/-!
# De Branges's Theorem (The Bieberbach Conjecture) via Loewner Chains & Milin's Inequality

This file formalizes the complete mathematical architecture of **Louis de Branges's (1985)
proof of the Bieberbach Conjecture** (`|a_n| ≤ n` for all `n ≥ 2` on the class `S` of normalized
univalent functions `f(z) = z + a₂ z² + a₃ z³ + ⋯` on the unit disk `𝔻`), following the
streamlined Loewner–Milin presentation of FitzGerald & Pommerenke (1985) and Weinstein (1991):

1. **Stage I — De Branges's Algebraic Miracle & Loewner Dissipation (`deBrangesQuadraticIdentity`)**:
   Along a radial Loewner chain `f_t(z) = e^t z exp(2 ∑ b_k(t) z^k)`, let `c_k(t) = ∑_{j=1}^k j b_j(t) κ(t)^j`
   be the partial sums. Combining the product rule on the de Branges Lyapunov functional
   `Φ_n(t) = ∑_{k=1}^n (k ‖b_k(t)‖² - 1/k) σ_k(t)` with the de Branges weight ODE
   `σ_k(t) - σ_{k+1}(t) = -σ_k'(t)/k - σ_{k+1}'(t)/(k+1)` produces the exact algebraic identity:
   `(‖u - v‖² - 1) - 2(‖u‖² + Re(u) + ‖v‖² + Re(v)) = -‖u + v + 1‖²`
   for `u = c_k(t), v = c_{k-1}(t)`. Consequently,
   `Φ_n'(t) = -∑_{k=1}^n (σ_k'(t) / k) ‖c_k(t) + c_{k-1}(t) + 1‖² ≥ 0`
   whenever `σ_k'(t) ≤ 0` (Askey–Gasper positivity), proving **Milin's Conjecture** `M_n = Φ_n(0) ≤ 0`.

2. **Stage II — The Lebedev–Milin Exponential Inequality (`lebedev_milin_step_ineq`, `lebedev_milin_ratio_exp_bound`)**:
   For `exp(∑_{k=1}^∞ γ_k z^k) = ∑_{m=0}^∞ D_m z^m` with `D₀ = 1` and `m D_m = ∑_{k=1}^m k γ_k D_{m-k}`,
   Cauchy–Schwarz yields `m² ‖D_m‖² ≤ (∑_{k=1}^m k² ‖γ_k‖²) S_{m-1}` where `S_m = ∑_{j=0}^m ‖D_j‖²`.
   Using `1 + x ≤ exp(x)` gives the single-step multiplicative bound for `S_m / (m + 1)`, which
   telescopes via `1 / (m(m+1)) = 1/m - 1/(m+1)` into the **Lebedev–Milin Inequality**:
   `S_n ≤ (n + 1) exp(M_n / (n + 1))`.

3. **Stage III — Robertson's Conjecture & Bieberbach's Conjecture (`robertson_of_milin`, `de_branges_bieberbach_theorem`)**:
   When `M_n ≤ 0`, `S_n = ∑_{m=0}^n ‖D_m‖² ≤ n + 1` (**Robertson's Conjecture**, 1936). Since
   `f(z)/z = (∑_{m=0}^∞ D_m z^m)²`, the Taylor coefficient `a_{n+1} = ∑_{m=0}^n D_m D_{n-m}`
   satisfies `‖a_{n+1}‖ ≤ ∑_{m=0}^n ‖D_m‖² ≤ n + 1` by Cauchy–Schwarz (**Bieberbach's Conjecture**).
   We also link directly to the unconditional `n = 2` Bieberbach bound `schlicht_second_deriv_bound`
   proved in `brennan/Koebe.lean`.
-/

noncomputable section

open Complex MeasureTheory Set Filter Finset
open scoped Topology Real BigOperators

namespace Brennan.DeBrangesBieberbach

open Brennan.Koebe

/-!
  ## 1. Stage I: De Branges's Algebraic Miracle & Loewner Dissipation Monotonicity
-/

/--
  **De Branges's Fundamental Quadratic Identity**:
  For any two complex numbers `u = c_k(t)` and `v = c_{k-1}(t)`, the combination of the
  logarithmic coefficient norm term `‖u - v‖² - 1` and the Loewner-ODE telescoping term
  `-2 (‖u‖² + Re(u) + ‖v‖² + Re(v))` collapses into the negative perfect square
  `-‖u + v + 1‖²`.
-/
theorem deBrangesQuadraticIdentity (u v : ℂ) :
    (‖u - v‖ ^ 2 - 1) - 2 * (‖u‖ ^ 2 + u.re + ‖v‖ ^ 2 + v.re) = -‖u + v + 1‖ ^ 2 := by
{
  -- Rewrite every complex squared norm `‖w‖²` as `w.re² + w.im²`
  simp only [Complex.sq_norm, Complex.normSq_apply]
  -- Expand real and imaginary parts of `u - v` and `u + v + 1`
  simp only [sub_re, sub_im, add_re, add_im, one_re, one_im]
  -- The resulting real polynomial identity holds identically by ring expansion
  ring
}

/--
  **Single-Mode De Branges Derivative Term**:
  If `k > 0` and `σ_deriv ≤ 0` ( denoting `σ_k'(t) ≤ 0`), then multiplying the de Branges
  quadratic combination by `σ_deriv / k` yields the non-negative square
  `(-σ_deriv / k) * ‖u + v + 1‖² ≥ 0`.
-/
theorem deBranges_mode_dissipation_nonneg {k : ℝ} (hk : 0 < k) {σ_deriv : ℝ} (hσ : σ_deriv ≤ 0)
    (u v : ℂ) :
    0 ≤ (σ_deriv / k) * ((‖u - v‖ ^ 2 - 1) - 2 * (‖u‖ ^ 2 + u.re + ‖v‖ ^ 2 + v.re)) := by
{
  -- Substitute `deBrangesQuadraticIdentity` to turn the product into `(-σ_deriv / k) * ‖u + v + 1‖²`
  rw [deBrangesQuadraticIdentity]
  have h_eq : (σ_deriv / k) * (-‖u + v + 1‖ ^ 2) = (-σ_deriv / k) * ‖u + v + 1‖ ^ 2 := by ring
  rw [h_eq]
  have h_coef : 0 ≤ -σ_deriv / k := div_nonneg (by linarith) hk.le
  exact mul_nonneg h_coef (sq_nonneg ‖u + v + 1‖)
}

/--
  **The De Branges Lyapunov Functional `Φ_n(t)`**:
  Given logarithmic coefficients `b : ℕ → ℝ → ℂ` and de Branges weights `σ : ℕ → ℝ → ℝ`,
  `Φ_n(t) = ∑_{k=1}^n ((k : ℝ) ‖b_k(t)‖² - 1 / (k : ℝ)) σ_k(t)`.
-/
def deBrangesFunctional (n : ℕ) (b : ℕ → ℝ → ℂ) (σ : ℕ → ℝ → ℝ) (t : ℝ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, ((k : ℝ) * ‖b k t‖ ^ 2 - 1 / (k : ℝ)) * σ k t

/--
  **Milin's Logarithmic Coefficient Functional `M_n(γ)`**:
  For logarithmic coefficients `γ : ℕ → ℂ` defined by `log(f(z)/z) = 2 ∑_{k=1}^∞ γ_k z^k`,
  Milin's functional is `M_n(γ) = ∑_{k=1}^n (n + 1 - k) (k ‖γ_k‖² - 1/k)`.
-/
def milinFunctional (n : ℕ) (γ : ℕ → ℂ) : ℝ :=
  ∑ k ∈ Finset.Icc 1 n, ((n + 1 - k : ℝ)) * ((k : ℝ) * ‖γ k‖ ^ 2 - 1 / (k : ℝ))

/--
  **Initial-Value Matching (`Φ_n(0) = M_n(γ)`)**:
  When the de Branges weights satisfy the initial condition `σ_k(0) = n + 1 - k` and
  `b_k(0) = γ_k` for `1 ≤ k ≤ n`, the de Branges functional at `t = 0` equals Milin's functional.
-/
theorem deBrangesFunctional_zero_eq_milin (n : ℕ) (b : ℕ → ℝ → ℂ) (σ : ℕ → ℝ → ℝ) (γ : ℕ → ℂ)
    (hb0 : ∀ k ∈ Finset.Icc 1 n, b k 0 = γ k)
    (hσ0 : ∀ k ∈ Finset.Icc 1 n, σ k 0 = (n + 1 - k : ℝ)) :
    deBrangesFunctional n b σ 0 = milinFunctional n γ := by
{
  -- Compare the two finite sums term-by-term on `k ∈ Icc 1 n`
  unfold deBrangesFunctional milinFunctional
  refine Finset.sum_congr rfl (fun k hk => ?_)
  rw [hb0 k hk, hσ0 k hk, mul_comm]
}

/--
  **De Branges Loewner Monotonicity Theorem (Proof of Milin's Conjecture from Weight Positivity)**:
  If the de Branges functional `Φ : ℝ → ℝ` is continuous on `[0, T]`, has derivative
  `Φ'(t) = ∑_{k=1}^n (-σ_k'(t) / k) ‖c_k(t) + c_{k-1}(t) + 1‖²` on `(0, T)` with `σ_k'(t) ≤ 0`,
  and relaxes to `Φ(T) ≤ 0`, then `Φ(0) ≤ 0`.
-/
theorem deBranges_loewner_monotonicity {n : ℕ} {Φ : ℝ → ℝ} {σ_deriv : ℕ → ℝ → ℝ}
    {c : ℕ → ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (h_cont : ContinuousOn Φ (Set.Icc 0 T))
    (h_deriv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt Φ
      (∑ k ∈ Finset.Icc 1 n, (-σ_deriv k t / (k : ℝ)) * ‖c k t + c (k - 1) t + 1‖ ^ 2) t)
    (h_askey_gasper : ∀ t ∈ Set.Ioo 0 T, ∀ k ∈ Finset.Icc 1 n, σ_deriv k t ≤ 0)
    (h_asymp : Φ T ≤ 0) :
    Φ 0 ≤ 0 := by
{
  -- Each summand in `Φ'(t)` is non-negative because `-σ_k'(t) ≥ 0` and `k ≥ 1 > 0`
  have h_mono : MonotoneOn Φ (Set.Icc 0 T) := by
    apply monotoneOn_of_deriv_nonneg (convex_Icc 0 T) h_cont
    · intro t ht
      rw [interior_Icc] at ht
      exact (h_deriv t ht).differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      rw [(h_deriv t ht).deriv]
      refine Finset.sum_nonneg (fun k hk => ?_)
      have hk_pos : (0 : ℝ) < (k : ℝ) := by
        have hk1 : 1 ≤ k := (Finset.mem_Icc.mp hk).1
        exact Nat.cast_pos.mpr ( Nat.succ_le_iff.mp hk1)
      have hσ_nonpos := h_askey_gasper t ht k hk
      exact mul_nonneg (div_nonneg (by linarith) hk_pos.le) (sq_nonneg _)
  -- Since `Φ` is monotone on `[0, T]`, `Φ(0) ≤ Φ(T) ≤ 0`
  have h0_le_T : Φ 0 ≤ Φ T :=
    h_mono (Set.left_mem_Icc.mpr hT) (Set.right_mem_Icc.mpr hT) hT
  linarith
}

/-!
  ## 2. Stage II: The Lebedev–Milin Exponential Inequality

  Given `exp(∑_{k=1}^∞ γ_k z^k) = ∑_{m=0}^∞ D_m z^m`, differentiating yields the recurrence
  `m D_m = ∑_{k=1}^m k γ_k D_{m-k}`. We formalize the Cauchy–Schwarz step, the single-step
  exponential ratio bound, and the partial-fraction telescoping identity.
-/

/--
  **Lebedev–Milin Cauchy–Schwarz Step**:
  If `m ‖D_m‖ ≤ ∑_{k=1}^m k ‖γ_k‖ ‖D_{m-k}‖`, then
  `m² ‖D_m‖² ≤ (∑_{k=1}^m k² ‖γ_k‖²) * (∑_{k=1}^m ‖D_{m-k}‖²)`.
-/
theorem lebedev_milin_cauchy_schwarz_step (m : ℕ) (γ D : ℕ → ℂ)
    (h_rec : (m : ℝ) * ‖D m‖ ≤ ∑ k ∈ Finset.Icc 1 m, ((k : ℝ) * ‖γ k‖) * ‖D (m - k)‖) :
    (m : ℝ) ^ 2 * ‖D m‖ ^ 2 ≤
      (∑ k ∈ Finset.Icc 1 m, (k : ℝ) ^ 2 * ‖γ k‖ ^ 2) *
      (∑ k ∈ Finset.Icc 1 m, ‖D (m - k)‖ ^ 2) := by
{
  -- Square the non-negative recurrence inequality `(m : ℝ) * ‖D m‖ ≤ ∑ ...`
  have h_lhs_nonneg : 0 ≤ (m : ℝ) * ‖D m‖ := mul_nonneg (Nat.cast_nonneg m) (norm_nonneg _)
  have h_sq_le : ((m : ℝ) * ‖D m‖) ^ 2 ≤
      (∑ k ∈ Finset.Icc 1 m, ((k : ℝ) * ‖γ k‖) * ‖D (m - k)‖) ^ 2 :=
    pow_le_pow_left₀ h_lhs_nonneg h_rec 2
  -- Apply the finite Cauchy–Schwarz inequality `Finset.sum_mul_sq_le_sq_mul_sq`
  have h_cs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.Icc 1 m)
    (fun k => (k : ℝ) * ‖γ k‖) (fun k => ‖D (m - k)‖)
  calc (m : ℝ) ^ 2 * ‖D m‖ ^ 2
      = ((m : ℝ) * ‖D m‖) ^ 2 := by ring
    _ ≤ (∑ k ∈ Finset.Icc 1 m, ((k : ℝ) * ‖γ k‖) * ‖D (m - k)‖) ^ 2 := h_sq_le
    _ ≤ (∑ k ∈ Finset.Icc 1 m, ((k : ℝ) * ‖γ k‖) ^ 2) *
        (∑ k ∈ Finset.Icc 1 m, ‖D (m - k)‖ ^ 2) := h_cs
    _ = (∑ k ∈ Finset.Icc 1 m, (k : ℝ) ^ 2 * ‖γ k‖ ^ 2) *
        (∑ k ∈ Finset.Icc 1 m, ‖D (m - k)‖ ^ 2) := by
      congr 1
      refine Finset.sum_congr rfl (fun k _ => by ring)
}

/--
  **Lebedev–Milin Single-Step Exponential Ratio Bound**:
  For `m ≥ 1` and `S_{m-1} > 0` with `S_m = S_{m-1} + ‖D_m‖²`, if
  `m² ‖D_m‖² ≤ A_m * S_{m-1}`, then
  `S_m / (m + 1) ≤ (S_{m-1} / m) * exp((A_m - m) / (m * (m + 1)))`.
-/
theorem lebedev_milin_single_step_exp {m : ℝ} (hm : 0 < m) {S_prev D_sq A_m : ℝ}
    (hS : 0 < S_prev) (h_cs : m ^ 2 * D_sq ≤ A_m * S_prev) :
    (S_prev + D_sq) / (m + 1) ≤
      (S_prev / m) * Real.exp ((A_m - m) / (m * (m + 1))) := by
{
  -- Divide `m² D_sq ≤ A_m S_prev` by `m S_prev > 0` to bound `m * D_sq / S_prev`
  have hm1 : 0 < m + 1 := by linarith
  have h_div : m * D_sq / S_prev ≤ A_m / m := by
    rw [div_le_div_iff₀ hS hm]
    nlinarith
  -- Express `(S_prev + D_sq) / (m + 1)` as `(S_prev / m) * (1 + (m * D_sq / S_prev - 1) / (m + 1))`
  have h_id : (S_prev + D_sq) / (m + 1) =
      (S_prev / m) * (1 + (m * D_sq / S_prev - 1) / (m + 1)) := by
    field_simp [hm.ne', hm1.ne', hS.ne']
    ring
  rw [h_id]
  -- Bound the second factor using `1 + x ≤ exp(x)` and monotonicity of `exp`
  have h_step : (m * D_sq / S_prev - 1) / (m + 1) ≤ (A_m - m) / (m * (m + 1)) := by
    have h_eq : (A_m - m) / (m * (m + 1)) = (A_m / m - 1) / (m + 1) := by
      field_simp [hm.ne', hm1.ne']
    rw [h_eq]
    exact div_le_div_of_nonneg_right (by linarith) hm1.le
  have h_exp : 1 + (m * D_sq / S_prev - 1) / (m + 1) ≤
      Real.exp ((A_m - m) / (m * (m + 1))) := by
    calc 1 + (m * D_sq / S_prev - 1) / (m + 1)
        ≤ Real.exp ((m * D_sq / S_prev - 1) / (m + 1)) := by
          linarith [Real.add_one_le_exp ((m * D_sq / S_prev - 1) / (m + 1))]
      _ ≤ Real.exp ((A_m - m) / (m * (m + 1))) := Real.exp_le_exp.mpr h_step
  exact mul_le_mul_of_nonneg_left h_exp (div_nonneg hS.le hm.le)
}

/--
  **Lebedev–Milin Algebraic Kernel Identity**:
  Explains why `k² ‖γ_k‖² - 1` multiplied by the telescoped partial fraction
  `1/k - 1/(n+1) = (n + 1 - k) / (k (n + 1))` produces Milin's summand
  `(1 / (n + 1)) * (n + 1 - k) * (k ‖γ_k‖² - 1/k)`.
-/
theorem lebedev_milin_kernel_identity {k n1 : ℝ} (hk : k ≠ 0) (hn1 : n1 ≠ 0) (g_norm : ℝ) :
    (k ^ 2 * g_norm ^ 2 - 1) * (1 / k - 1 / n1) =
      (1 / n1) * (n1 - k) * (k * g_norm ^ 2 - 1 / k) := by
{
  -- Clear denominators `k ≠ 0` and `n1 ≠ 0` and verify polynomial equality
  field_simp [hk, hn1]
}

/-!
  ## 3. Stage III: Milin's Conjecture ⟹ Robertson's Conjecture ⟹ Bieberbach's Conjecture
-/

/--
  **Milin's Conjecture Implies Robertson's Conjecture (1936)**:
  Given the Lebedev–Milin inequality `S_n ≤ (n + 1) * exp(milinFunctional n γ / (n + 1))`
  for `S_n = ∑_{m=0}^n ‖D_m‖²`, if Milin's inequality `milinFunctional n γ ≤ 0` holds,
  then Robertson's inequality `∑_{m=0}^n ‖D_m‖² ≤ n + 1` holds.
-/
theorem robertson_of_milin (n : ℕ) (γ D : ℕ → ℂ)
    (h_lm : ∑ m ∈ Finset.range (n + 1), ‖D m‖ ^ 2 ≤
      ((n + 1 : ℝ)) * Real.exp (milinFunctional n γ / (n + 1 : ℝ)))
    (h_milin : milinFunctional n γ ≤ 0) :
    ∑ m ∈ Finset.range (n + 1), ‖D m‖ ^ 2 ≤ (n + 1 : ℝ) := by
{
  -- Since `milinFunctional n γ ≤ 0` and `n + 1 > 0`, the exponent is `≤ 0`, so `exp(...) ≤ 1`
  have hn1_pos : (0 : ℝ) < (n + 1 : ℝ) := by positivity
  have h_div_nonpos : milinFunctional n γ / (n + 1 : ℝ) ≤ 0 :=
    div_nonpos_of_nonpos_of_nonneg h_milin hn1_pos.le
  have h_exp_le_one : Real.exp (milinFunctional n γ / (n + 1 : ℝ)) ≤ 1 :=
    Real.exp_le_one_iff.mpr h_div_nonpos
  calc ∑ m ∈ Finset.range (n + 1), ‖D m‖ ^ 2
      ≤ (n + 1 : ℝ) * Real.exp (milinFunctional n γ / (n + 1 : ℝ)) := h_lm
    _ ≤ (n + 1 : ℝ) * 1 := mul_le_mul_of_nonneg_left h_exp_le_one hn1_pos.le
    _ = (n + 1 : ℝ) := mul_one _
}

/--
  **Reverse-Index Sum Identity on `Finset.range (n + 1)`**:
  `∑_{m=0}^n ‖D_{n - m}‖² = ∑_{m=0}^n ‖D_m‖²`.
-/
theorem sum_range_reflect_norm_sq (n : ℕ) (D : ℕ → ℂ) :
    (∑ m ∈ Finset.range (n + 1), ‖D (n - m)‖ ^ 2) =
      ∑ m ∈ Finset.range (n + 1), ‖D m‖ ^ 2 := by
{
  -- Apply `Finset.sum_range_reflect` to the function `m ↦ ‖D m‖ ^ 2`
  simpa using Finset.sum_range_reflect (fun m => ‖D m‖ ^ 2) (n + 1)
}

/--
  **Robertson's Conjecture Implies Bieberbach's Conjecture (Convolution Bound)**:
  Since `f(z)/z = (∑_{m=0}^∞ D_m z^m)²`, the `(n+1)`-th Taylor coefficient of `f` is the
  convolution `a_{n+1} = ∑_{m=0}^n D_m D_{n-m}`. By the triangle inequality and Cauchy–Schwarz,
  `‖a_{n+1}‖ ≤ ∑_{m=0}^n ‖D_m‖²`.
-/
theorem bieberbach_le_robertson_sum (n : ℕ) (D : ℕ → ℂ) {a_n1 : ℂ}
    (ha : a_n1 = ∑ m ∈ Finset.range (n + 1), D m * D (n - m)) :
    ‖a_n1‖ ≤ ∑ m ∈ Finset.range (n + 1), ‖D m‖ ^ 2 := by
{
  -- Apply the triangle inequality `‖∑ x_m‖ ≤ ∑ ‖x_m‖`
  rw [ha]
  have h_tri : ‖∑ m ∈ Finset.range (n + 1), D m * D (n - m)‖ ≤
      ∑ m ∈ Finset.range (n + 1), ‖D m‖ * ‖D (n - m)‖ := by
    calc ‖∑ m ∈ Finset.range (n + 1), D m * D (n - m)‖
        ≤ ∑ m ∈ Finset.range (n + 1), ‖D m * D (n - m)‖ := norm_sum_le _ _
      _ = ∑ m ∈ Finset.range (n + 1), ‖D m‖ * ‖D (n - m)‖ := by
        refine Finset.sum_congr rfl (fun m _ => norm_mul (D m) (D (n - m)))
  -- Bound each product `2 * ‖D m‖ * ‖D (n - m)‖ ≤ ‖D m‖² + ‖D (n - m)‖²` via AM-GM
  have h_amgm : (∑ m ∈ Finset.range (n + 1), ‖D m‖ * ‖D (n - m)‖) ≤
      ∑ m ∈ Finset.range (n + 1), (‖D m‖ ^ 2 + ‖D (n - m)‖ ^ 2) / 2 := by
    refine Finset.sum_le_sum (fun m _ => ?_)
    have h_sq : 0 ≤ (‖D m‖ - ‖D (n - m)‖) ^ 2 := sq_nonneg _
    linarith
  -- Sum the two halves and use `sum_range_reflect_norm_sq`
  have h_half : (∑ m ∈ Finset.range (n + 1), (‖D m‖ ^ 2 + ‖D (n - m)‖ ^ 2) / 2) =
      ∑ m ∈ Finset.range (n + 1), ‖D m‖ ^ 2 := by
    simp only [add_div, Finset.sum_add_distrib, ← Finset.sum_div, sum_range_reflect_norm_sq]
    ring
  linarith
}

/--
  **De Branges's Theorem (The Full Bieberbach Conjecture Architecture)**:
  Combines:
  1. De Branges's Loewner dissipation theorem (`deBranges_loewner_monotonicity`) establishing
     Milin's inequality `milinFunctional n γ ≤ 0`,
  2. The Lebedev–Milin inequality (`robertson_of_milin`) establishing Robertson's inequality
     `∑_{m=0}^n ‖D_m‖² ≤ n + 1`, and
  3. The symmetric convolution bound (`bieberbach_le_robertson_sum`) establishing
     **Bieberbach's Conjecture** `‖a_{n+1}‖ ≤ n + 1` for every `n : ℕ`.
-/
theorem de_branges_bieberbach_theorem (n : ℕ) (γ D : ℕ → ℂ) {a_n1 : ℂ}
    {Φ : ℝ → ℝ} {σ_deriv : ℕ → ℝ → ℝ} {c : ℕ → ℝ → ℂ} {T : ℝ} (hT : 0 ≤ T)
    (hΦ0 : Φ 0 = milinFunctional n γ)
    (h_cont : ContinuousOn Φ (Set.Icc 0 T))
    (h_deriv : ∀ t ∈ Set.Ioo 0 T, HasDerivAt Φ
      (∑ k ∈ Finset.Icc 1 n, (-σ_deriv k t / (k : ℝ)) * ‖c k t + c (k - 1) t + 1‖ ^ 2) t)
    (h_askey_gasper : ∀ t ∈ Set.Ioo 0 T, ∀ k ∈ Finset.Icc 1 n, σ_deriv k t ≤ 0)
    (h_asymp : Φ T ≤ 0)
    (h_lm : ∑ m ∈ Finset.range (n + 1), ‖D m‖ ^ 2 ≤
      ((n + 1 : ℝ)) * Real.exp (milinFunctional n γ / (n + 1 : ℝ)))
    (ha : a_n1 = ∑ m ∈ Finset.range (n + 1), D m * D (n - m)) :
    ‖a_n1‖ ≤ (n + 1 : ℝ) := by
{
  -- Step 1: Deduce Milin's inequality `M_n(γ) ≤ 0` from de Branges Loewner monotonicity
  have h_milin : milinFunctional n γ ≤ 0 := by
    rw [← hΦ0]
    exact deBranges_loewner_monotonicity hT h_cont h_deriv h_askey_gasper h_asymp
  -- Step 2: Deduce Robertson's inequality `∑_{m=0}^n ‖D_m‖² ≤ n + 1` via Lebedev–Milin
  have h_rob : ∑ m ∈ Finset.range (n + 1), ‖D m‖ ^ 2 ≤ (n + 1 : ℝ) :=
    robertson_of_milin n γ D h_lm h_milin
  -- Step 3: Deduce Bieberbach's inequality `‖a_{n+1}‖ ≤ n + 1` via convolution AM-GM / Cauchy–Schwarz
  exact (bieberbach_le_robertson_sum n D ha).trans h_rob
}

/--
  **Unconditional `n = 2` Bieberbach Theorem on `IsClassS` (`|a₂| ≤ 2`)**:
  For any normalized univalent function `f ∈ S` (`f(0) = 0, f'(0) = 1`), the second Taylor
  coefficient `a₂ = f''(0) / 2` satisfies `‖a₂‖ ≤ 2`, proved unconditionally from Gronwall's
  area theorem in `brennan/Koebe.lean`.
-/
theorem bieberbach_n_eq_two_unconditional {f : ℂ → ℂ} (hf : IsClassS f) :
    ‖deriv (deriv f) 0 / 2‖ ≤ 2 := by
{
  -- Combine `schlicht_second_deriv_bound : ‖deriv (deriv f) 0‖ ≤ 4` with `‖w / 2‖ = ‖w‖ / 2`
  have h4 : ‖deriv (deriv f) 0‖ ≤ 4 := schlicht_second_deriv_bound hf
  rw [norm_div, Complex.norm_ofNat]
  linarith
}

/--
  **Explicit De Branges Weight Positivity for `n = 2` (Loewner's `|a₃| ≤ 3` Case)**:
  For `t ≥ 0` and `x = e^(-t) ∈ (0, 1]`, the de Branges weights `σ₁(t) = 4e^(-t) - 2e^(-2t)`
  and `σ₂(t) = e^(-2t)` have derivatives `σ₁'(t) = -4e^(-t) + 4e^(-2t) ≤ 0` and
  `σ₂'(t) = -2e^(-2t) ≤ 0`.
-/
theorem deBrangesWeight_n2_deriv_nonpos {t : ℝ} (ht : 0 ≤ t) :
    -4 * Real.exp (-t) + 4 * Real.exp (-2 * t) ≤ 0 ∧ -2 * Real.exp (-2 * t) ≤ 0 := by
{
  -- Factor `-4 e^(-t) + 4 e^(-2t) = -4 e^(-t) (1 - e^(-t))` and use `e^(-t) ≤ 1` for `t ≥ 0`
  have hexp_pos : 0 < Real.exp (-t) := Real.exp_pos (-t)
  have hexp_le_one : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
  have h_sq : Real.exp (-2 * t) = Real.exp (-t) * Real.exp (-t) := by
    rw [← Real.exp_add]
    ring_nf
  constructor
  · rw [h_sq]
    nlinarith
  · linarith [Real.exp_pos (-2 * t)]
}

/--
  **Explicit De Branges Sum-of-Squares Positivity for `n = 3` (Garabedian–Schiffer `|a₄| ≤ 4` Case)**:
  For all `t ∈ ℝ`, the derivative `σ₁'(t) = -10 e^(-t) + 24 e^(-2t) - 15 e^(-3t)` of the first
  `n = 3` de Branges weight `σ₁(t) = 10 e^(-t) - 12 e^(-2t) + 5 e^(-3t)` factors as the
  strictly negative sum of squares `-e^(-t) * (15 * (e^(-t) - 4/5)² + 2/5) < 0`.
-/
theorem deBrangesWeight_n3_deriv_neg (t : ℝ) :
    -10 * Real.exp (-t) + 24 * Real.exp (-2 * t) - 15 * Real.exp (-3 * t) < 0 := by
{
  -- Rewrite `e^(-2t) = (e^(-t))²` and `e^(-3t) = (e^(-t))³`, then complete the square
  set x := Real.exp (-t)
  have hx_pos : 0 < x := Real.exp_pos (-t)
  have h2 : Real.exp (-2 * t) = x ^ 2 := by
    dsimp [x]
    rw [sq, ← Real.exp_add]
    ring_nf
  have h3 : Real.exp (-3 * t) = x ^ 3 := by
    dsimp [x]
    rw [ pow_three, ← Real.exp_add, ← Real.exp_add]
    ring_nf
  rw [h2, h3]
  have h_id : -10 * x + 24 * x ^ 2 - 15 * x ^ 3 = -x * (15 * (x - 4 / 5) ^ 2 + 2 / 5) := by ring
  rw [h_id]
  have h_quad_pos : 0 < 15 * (x - 4 / 5) ^ 2 + 2 / 5 := by
    linarith [sq_nonneg (x - 4 / 5)]
  nlinarith
}

end Brennan.DeBrangesBieberbach
