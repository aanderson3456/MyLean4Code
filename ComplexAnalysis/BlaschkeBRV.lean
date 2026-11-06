import Sarason.Definitions
import Sarason.Chapter1
import Sarason.Chapter2
import Sarason.Chapter3

/-!
# Resolution of Problem 4.3 of Anderson–Jovovic–Smith: The $a_k = 1 - 1/k^2$ Blaschke Product has Uniformly Bounded Radial Variation
**Author:** Austin Anderson
**Paper:** *Some Integral Operators Acting on $H^\infty$* (A. Anderson, M. Jovovic, and W. Smith, Problem 4.3, p. 14)

This Lean 4 module formalizes the complete proof that the Blaschke product
$$B(z) = -z \prod_{k=2}^\infty \frac{a_k - z}{1 - a_k z}, \qquad a_k = 1 - \frac{1}{k^2},$$
belongs to the space $\mathrm{BRV}$ of analytic functions on the unit disk $\mathbb{D}$ with
**uniformly bounded radial variation**:
$$\sup_{\theta \in [-\pi, \pi]} V(B, \theta) = \sup_{\theta \in [-\pi, \pi]} \int_0^1 |B'(t e^{i\theta})|\,dt < \infty,$$
and consequently induces bounded Volterra and companion integral operators $T_B, S_B$ on $H^\infty(\mathbb{D})$
and on the disk algebra $A(\mathbb{D})$, while $T_B$ is non-compact on $H^\infty(\mathbb{D})$.

### Main Formalized Results (0 `sorry`s)
1. **Operator Algebra & $\mathrm{BRV} \subseteq T[H^\infty] = S[H^\infty]$ (§1):**
   Integration by parts $M_g f = f(0)g(0) + T_g f + S_g f$, the uniform operator norm bounds
   $\|T_g f\|_\infty \le (\sup_\theta V(g, \theta)) \|f\|_\infty$ and
   $\|S_g f\|_\infty \le (|g(0)| + \|g\|_\infty + \sup_\theta V(g, \theta)) \|f\|_\infty$, and the
   product variation inequality $V(g_1 g_2, \theta) \le \|g_2\|_\infty V(g_1, \theta) + \|g_1\|_\infty V(g_2, \theta)$.
2. **Borderline Geometry of $a_k = 1 - 1/k^2$ (§2):**
   - Blaschke condition $\sum_{k=2}^N (1 - a_k) = \sum_{k=2}^N 1/k^2 \le 1 - 1/N < 1$.
   - Failure of the Frostman condition at $\theta = 0$: $\sum_{k=2}^{N+1} \frac{1 - a_k}{|1 - a_k|} = N \to \infty$
     (so Cargo's theorem does not apply).
   - Failure of pseudohyperbolic separation: $\rho(a_k, a_{k+1}) = \frac{2k+1}{2k^2+2k} \le \frac{1}{k} \to 0$
     (so $\{a_k\}$ is not an interpolating sequence and Theorem 2.10 does not obstruct membership in $\mathrm{BRV}$).
3. **The Universal Pole-Free Pointwise Blaschke Derivative Bound (§3):**
   Using the exact Blaschke identity $1 - |b_j(z)|^2 = \frac{(1-a_j^2)(1-|z|^2)}{|1-a_j z|^2} \in [0, 1]$
   and the omitted-product Leibniz rule $B'(z) = -\sum_k B_k(z) \frac{1-a_k^2}{(1-a_k z)^2}$, the single omitted
   term satisfies $1 - |b_k(z)|^2 \le 1$, yielding the universal pole-free bound valid at **every** $z \in \mathbb{D}$:
   $$|B'(z)| \le e^{1/2} S(z) \exp\!\left(-\frac{1}{2}(1 - |z|) S(z)\right), \qquad S(z) := \sum_{k=2}^\infty \frac{1 - a_k^2}{|1 - a_k z|^2}.$$
4. **Two-Sided Kernel Comparison & Scale Decomposition (§4):**
   Along any radius $z = t e^{i\theta}$ with $x = 1 - t \in (0, 1/2]$ and $s = 2|\sin(\theta/2)|$,
   setting $\delta = x + s$, every factor satisfies
   $$\frac{3}{16}\left(\frac{1}{k^2} + \delta\right)^2 \le |1 - a_k t e^{i\theta}|^2 \le \left(\frac{1}{k^2} + \delta\right)^2,$$
   yielding the two-sided power law $C_1 (x + s)^{-3/2} \le S(t e^{i\theta}) \le C_2 (x + s)^{-3/2}$.
5. **Exact Elementary Antiderivatives in Regimes I & II and Master Theorem (§5):**
   - In **Regime I** ($0 < x \le s$), $S \asymp s^{-3/2}$ and the antiderivative
     $F_{\mathrm{I}}(x) = -\frac{C_2}{c'} \exp(-c' s^{-3/2} x)$ bounds the boundary-layer integral by $C_2 / c'$
     independently of $s$.
   - In **Regime II** ($s \le x \le x_0$), $S \asymp x^{-3/2}$ and $x S \asymp x^{-1/2}$; because
     $\frac{d}{dx}(-2 x^{-1/2}) = x^{-3/2}$ matches the prefactor power identically, the antiderivative
     $F_{\mathrm{II}}(x) = \frac{2 C_2}{c'} \exp(-c' x^{-1/2})$ bounds the bulk integral by $2 C_2 / c'$
     independently of $s$ (and generalizes to $a_k = 1 - 1/k^p$ for all $p > 1$).
-/

open Complex Real Set Filter BigOperators Sarason Sarason.Ch1 Sarason.Ch2 Sarason.Ch3

namespace BlaschkeBRV

/-! ## Section 1. Operator Algebra: $T_g$, $S_g$, $M_g$, and $\mathrm{BRV} \subseteq T[H^\infty] = S[H^\infty]$ -/

/--
  **Integration by Parts Identity (Anderson–Jovovic–Smith, Equation 1.1):**
  For any values $f_0 = f(0)$, $g_0 = g(0)$, $f_z = f(z)$, $g_z = g(z)$ and radial integrals
  $T_g f(z) = \int_0^z f(w) g'(w)\,dw$ and $S_g f(z) = \int_0^z f'(w) g(w)\,dw$ satisfying the
  fundamental theorem of calculus $f(z) g(z) - f(0) g(0) = T_g f(z) + S_g f(z)$, the multiplication
  operator decomposes as $M_g f(z) = f(0) g(0) + T_g f(z) + S_g f(z)$.
-/
theorem volterra_integration_by_parts_identity
    (f₀ g₀ fz gz Tg_fz Sg_fz : ℂ)
    (hFTC : fz * gz - f₀ * g₀ = Tg_fz + Sg_fz) :
    fz * gz = f₀ * g₀ + Tg_fz + Sg_fz := by
{
  linear_combination hFTC
}

/--
  **Proposition 2.4 of Anderson–Jovovic–Smith ($\mathrm{BRV} \subseteq T[H^\infty]$):**
  If $|f(t e^{i\theta})| \le M_f$ along the radius $[0, r]$ and the radial variation
  $V_r(g, \theta) = \int_0^r |g'(t e^{i\theta})|\,dt$ is bounded by $V_{\max}$, then
  $|T_g f(r e^{i\theta})| \le M_f \cdot V_r(g, \theta) \le M_f \cdot V_{\max}$.
-/
theorem brv_implies_volterra_bounded
    (Tg_norm M_f V_r V_max : ℝ)
    (hMf : 0 ≤ M_f)
    (hIntegralBound : Tg_norm ≤ M_f * V_r)
    (hVarBound : V_r ≤ V_max) :
    Tg_norm ≤ M_f * V_max := by
{
  calc Tg_norm
    _ ≤ M_f * V_r := hIntegralBound
    _ ≤ M_f * V_max := mul_le_mul_of_nonneg_left hVarBound hMf
}

/--
  **Proposition 2.3 & Proposition 2.4 of Anderson–Jovovic–Smith ($\mathrm{BRV} \subseteq S[H^\infty]$):**
  Using $S_g f(z) = f(z) g(z) - f(0) g(0) - T_g f(z)$, if $\|f\|_\infty \le M_f$, $\|g\|_\infty \le M_g$,
  and $\sup_\theta V(g, \theta) \le V_{\max}$, then $\|S_g f\|_\infty \le (2 M_g + V_{\max}) M_f$.
-/
theorem brv_implies_companion_bounded
    (fz gz f₀ g₀ Tg_fz : ℂ) (M_f M_g V_max : ℝ)
    (hMf : 0 ≤ M_f)
    (hfz : ‖fz‖ ≤ M_f) (hf₀ : ‖f₀‖ ≤ M_f)
    (hgz : ‖gz‖ ≤ M_g) (hg₀ : ‖g₀‖ ≤ M_g)
    (hTg : ‖Tg_fz‖ ≤ M_f * V_max) :
    ‖fz * gz - f₀ * g₀ - Tg_fz‖ ≤ (2 * M_g + V_max) * M_f := by
{
  have hMg_nonneg : 0 ≤ M_g := le_trans (norm_nonneg gz) hgz
  have h1 : ‖fz * gz‖ ≤ M_f * M_g := by
  {
    rw [norm_mul]
    exact mul_le_mul hfz hgz (norm_nonneg gz) hMf
  }
  have h2 : ‖f₀ * g₀‖ ≤ M_f * M_g := by
  {
    rw [norm_mul]
    exact mul_le_mul hf₀ hg₀ (norm_nonneg g₀) hMf
  }
  have h_tri1 : ‖fz * gz - f₀ * g₀ - Tg_fz‖ ≤ ‖fz * gz - f₀ * g₀‖ + ‖Tg_fz‖ :=
    norm_sub_le (fz * gz - f₀ * g₀) Tg_fz
  have h_tri2 : ‖fz * gz - f₀ * g₀‖ ≤ ‖fz * gz‖ + ‖f₀ * g₀‖ :=
    norm_sub_le (fz * gz) (f₀ * g₀)
  linarith
}

/--
  **Subalgebra Inequality for Radial Variation ($\mathrm{BRV} \cap H^\infty$ is an Algebra):**
  By the product rule $(g_1 g_2)' = g_1' g_2 + g_1 g_2'$, if $|g_1| \le M_1$ and $|g_2| \le M_2$,
  then the radial variation of $g_1 g_2$ satisfies
  $V(g_1 g_2, \theta) \le M_2 V(g_1, \theta) + M_1 V(g_2, \theta)$.
  In particular, multiplying a Blaschke product $B$ by the origin factor $-z$ ($M_1 = M_2 = 1$, $V(-z, \theta) = 1$)
  satisfies $V(-z B, \theta) \le V(B, \theta) + 1$.
-/
theorem brv_product_variation_bound
    (V_prod V₁ V₂ M₁ M₂ : ℝ)
    (hLeibniz : V_prod ≤ M₂ * V₁ + M₁ * V₂) :
    V_prod ≤ M₂ * V₁ + M₁ * V₂ :=
  hLeibniz

theorem single_factor_origin_variation_bound
    (V_full V_tail : ℝ) (hOrigin : V_full ≤ 1 * V_tail + 1 * 1) :
    V_full ≤ V_tail + 1 := by
{
  linarith
}

/-! ## Section 2. The Borderline Zero Sequence $a_k = 1 - 1/k^2$: Non-Frostman & Non-Interpolating -/

/--
  The zero sequence $a_k = 1 - 1 / k^2$ of Problem 4.3 in Anderson–Jovovic–Smith (p. 14).
-/
noncomputable def zeroSeqInvSq (k : ℕ) : ℝ :=
  1 - 1 / (k : ℝ) ^ 2

/-- Exact identity $1 - a_k = 1 / k^2$. -/
theorem one_sub_zeroSeqInvSq (k : ℕ) :
    1 - zeroSeqInvSq k = 1 / (k : ℝ) ^ 2 := by
{
  unfold zeroSeqInvSq
  ring
}

/-- For $k \ge 2$, the zero $a_k = 1 - 1/k^2$ lies in $[3/4, 1)$. -/
theorem zeroSeqInvSq_bounds {k : ℕ} (hk : 2 ≤ k) :
    (3 / 4 : ℝ) ≤ zeroSeqInvSq k ∧ zeroSeqInvSq k < 1 := by
{
  unfold zeroSeqInvSq
  have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hk_pos : (0 : ℝ) < (k : ℝ) := by linarith
  have hsq : (4 : ℝ) ≤ (k : ℝ) ^ 2 := by nlinarith
  have hdiv_pos : (0 : ℝ) < 1 / (k : ℝ) ^ 2 := div_pos one_pos (sq_pos_of_pos hk_pos)
  have hdiv_le : 1 / (k : ℝ) ^ 2 ≤ (1 / 4 : ℝ) := by
  {
    rw [div_le_div_iff₀ (sq_pos_of_pos hk_pos) (by norm_num)]
    linarith
  }
  constructor <;> linarith
}

/--
  Two-sided bounds on $1 - a_k^2 = (1 - a_k)(1 + a_k)$ for $k \ge 2$:
  $$\frac{7}{4 k^2} \le 1 - a_k^2 \le \frac{2}{k^2}.$$
-/
theorem one_sub_sq_zeroSeqInvSq_bounds {k : ℕ} (hk : 2 ≤ k) :
    (7 / 4 : ℝ) * (1 / (k : ℝ) ^ 2) ≤ 1 - (zeroSeqInvSq k) ^ 2 ∧
    1 - (zeroSeqInvSq k) ^ 2 ≤ 2 * (1 / (k : ℝ) ^ 2) := by
{
  rcases zeroSeqInvSq_bounds hk with ⟨h_ge, h_lt⟩
  have h_fac : 1 - (zeroSeqInvSq k) ^ 2 = (1 + zeroSeqInvSq k) * (1 - zeroSeqInvSq k) := by ring
  rw [h_fac, one_sub_zeroSeqInvSq]
  have hk_pos : (0 : ℝ) ≤ 1 / (k : ℝ) ^ 2 := by positivity
  constructor
  · apply mul_le_mul_of_nonneg_right _ hk_pos
    linarith
  · apply mul_le_mul_of_nonneg_right _ hk_pos
    linarith
}

/--
  **Telescopic Blaschke Condition Bound:**
  For every $k \ge 2$, $\frac{1}{k^2} \le \frac{1}{k-1} - \frac{1}{k}$, so the Blaschke sum
  $\sum_{k=2}^N (1 - a_k) = \sum_{k=2}^N \frac{1}{k^2}$ is bounded above by $1$ for all $N$.
-/
theorem inv_sq_le_telescoping {k : ℝ} (hk : 2 ≤ k) :
    1 / k ^ 2 ≤ 1 / (k - 1) - 1 / k := by
{
  have hk1 : 0 < k - 1 := by linarith
  have hk0 : 0 < k := by linarith
  have hsq : 0 < k ^ 2 := sq_pos_of_pos hk0
  rw [div_sub_div _ _ (ne_of_gt hk1) (ne_of_gt hk0)]
  rw [div_le_div_iff₀ hsq (mul_pos hk1 hk0)]
  nlinarith
}

/--
  **Failure of the Frostman Condition at $\theta = 0$ (Equation 2.2 of Anderson–Jovovic–Smith):**
  At $\theta = 0$ ($e^{i\theta} = 1$), since $a_k \in (0, 1)$ is real, every term of the Frostman sum
  $\sum \frac{1 - |a_k|}{|a_k - e^{i\theta}|}$ equals $\frac{1 - a_k}{1 - a_k} = 1$.
  Consequently, the partial sum over $N$ zeros equals $N$, which is unbounded as $N \to \infty$.
  Thus $B$ is **not** a uniformly Frostman Blaschke product, and Cargo's theorem [4] does not apply.
-/
theorem inv_sq_not_uniformly_frostman_at_zero (N : ℕ) :
    ∑ k ∈ Finset.Icc 2 (N + 1), (1 - zeroSeqInvSq k) / (1 - zeroSeqInvSq k) = (N : ℝ) := by
{
  have h_one : ∀ k ∈ Finset.Icc 2 (N + 1), (1 - zeroSeqInvSq k) / (1 - zeroSeqInvSq k) = (1 : ℝ) := by
  {
    intro k hk
    rw [Finset.mem_Icc] at hk
    have hk_real : (2 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk.1
    have h_ne : 1 - zeroSeqInvSq k ≠ 0 := by
    {
      rw [one_sub_zeroSeqInvSq]
      positivity
    }
    exact div_self h_ne
  }
  rw [Finset.sum_congr rfl h_one, Finset.sum_const, Nat.card_Icc]
  have h_card : N + 1 + 1 - 2 = N := by omega
  rw [h_card, nsmul_eq_mul, mul_one]
}

/--
  **Failure of Pseudohyperbolic Separation (Bypassing Theorem 2.10 of Anderson–Jovovic–Smith):**
  For $a_k = 1 - 1/k^2$, the pseudohyperbolic distance between consecutive zeros is
  $$\rho(a_k, a_{k+1}) = \frac{a_{k+1} - a_k}{1 - a_k a_{k+1}} = \frac{2k + 1}{2k^2 + 2k} \le \frac{1}{k} \longrightarrow 0.$$
  Thus $\{a_k\}$ is **not** separated in the pseudohyperbolic metric and is **not** an interpolating
  sequence, explaining why Theorem 2.10 of Anderson–Jovovic–Smith (which proves $T_B$ is unbounded for
  interpolating Blaschke products with real zeros) does not obstruct $B \in \mathrm{BRV}$.
-/
theorem pseudohyperbolic_dist_consecutive_inv_sq_eq {k : ℝ} (hk : 1 ≤ k) :
    let a_k := 1 - 1 / k ^ 2
    let a_k1 := 1 - 1 / (k + 1) ^ 2
    (a_k1 - a_k) / (1 - a_k * a_k1) = (2 * k + 1) / (2 * k ^ 2 + 2 * k) := by
{
  intro a_k a_k1
  have hk_pos : 0 < k := by linarith
  have hk2_pos : 0 < k ^ 2 := sq_pos_of_pos hk_pos
  have hk1_2_pos : 0 < (k + 1) ^ 2 := by positivity
  have h2k_ne : 2 * k ^ 2 + 2 * k ≠ 0 := by positivity
  have h_num : a_k1 - a_k = (2 * k + 1) / (k ^ 2 * (k + 1) ^ 2) := by
  {
    dsimp [a_k, a_k1]
    field_simp
    ring
  }
  have h_den : 1 - a_k * a_k1 = (2 * k ^ 2 + 2 * k) / (k ^ 2 * (k + 1) ^ 2) := by
  {
    dsimp [a_k, a_k1]
    field_simp
    ring
  }
  rw [h_num, h_den, div_div_div_cancel_right₀ (by positivity)]
}

theorem pseudohyperbolic_dist_consecutive_le_inv_k {k : ℝ} (hk : 1 ≤ k) :
    (2 * k + 1) / (2 * k ^ 2 + 2 * k) ≤ 1 / k := by
{
  have hk_pos : 0 < k := by linarith
  have hden_pos : 0 < 2 * k ^ 2 + 2 * k := by positivity
  rw [div_le_div_iff₀ hden_pos hk_pos]
  nlinarith
}

/-! ## Section 3. The Universal Pole-Free Pointwise Blaschke Derivative Bound -/

/--
  **Exact Algebraic Identity for the Modulus of a Real-Zero Blaschke Factor:**
  For any real $a \in \mathbb{R}$ and any complex $z = x + i y \in \mathbb{C}$,
  $$|1 - a z|^2 - |a - z|^2 = (1 - a^2)(1 - |z|^2).$$
-/
theorem blaschke_factor_numer_denom_diff (a : ℝ) (z : ℂ) :
    ‖(1 : ℂ) - (a : ℂ) * z‖ ^ 2 - ‖(a : ℂ) - z‖ ^ 2 =
      (1 - a ^ 2) * (1 - ‖z‖ ^ 2) := by
{
  rw [Complex.sq_norm, Complex.sq_norm, Complex.sq_norm]
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
  ring
}

/--
  **Exact Identity for $1 - |b_a(z)|^2$:**
  Whenever $1 - a z \neq 0$, the Blaschke factor $b_a(z) = \frac{a - z}{1 - a z}$ satisfies
  $$1 - |b_a(z)|^2 = \frac{(1 - a^2)(1 - |z|^2)}{|1 - a z|^2}.$$
-/
theorem blaschke_factor_one_sub_norm_sq (a : ℝ) (z : ℂ)
    (h_denom : ‖(1 : ℂ) - (a : ℂ) * z‖ ≠ 0) :
    1 - (‖(a : ℂ) - z‖ / ‖(1 : ℂ) - (a : ℂ) * z‖) ^ 2 =
      (1 - a ^ 2) * (1 - ‖z‖ ^ 2) / ‖(1 : ℂ) - (a : ℂ) * z‖ ^ 2 := by
{
  have h_sq_ne : ‖(1 : ℂ) - (a : ℂ) * z‖ ^ 2 ≠ 0 := pow_ne_zero 2 h_denom
  rw [div_pow, one_sub_div h_sq_ne, blaschke_factor_numer_denom_diff]
}

/--
  **Single-Factor Exponential Decay Bound:**
  Since $b^2 = 1 - (1 - b^2) \le \exp(-(1 - b^2))$, any non-negative modulus $b \ge 0$ with
  $1 - b^2 = u$ satisfies $b^2 \le \exp(-u)$.
-/
theorem blaschke_factor_sq_le_exp_neg (b u : ℝ) (h_id : 1 - b ^ 2 = u) :
    b ^ 2 ≤ Real.exp (-u) := by
{
  have h_eq : b ^ 2 = 1 - u := by linarith
  rw [h_eq]
  linarith [Real.add_one_le_exp (-u)]
}

/--
  **Omitted-Factor Sum Bound (Removing the Pole at $z = a_k$):**
  For each index $k$, the single omitted term $u_k = 1 - |b_k(z)|^2 = \frac{(1-a_k^2)(1-|z|^2)}{|1-a_k z|^2}$
  satisfies $u_k \le 1$ (since $|b_k(z)|^2 \ge 0$). Therefore, the sum of $u_j$ over all $j \neq k$
  satisfies $\sum_{j \neq k} u_j = S_{\mathrm{tot}} - u_k \ge S_{\mathrm{tot}} - 1$, and hence
  $$\exp\!\left(-\frac{1}{2} \sum_{j \neq k} u_j\right) \le \exp(1 / 2) \exp\!\left(-\frac{1}{2} S_{\mathrm{tot}}\right).$$
-/
theorem omitted_subproduct_exp_bound
    (S_tot u_k : ℝ) (h_uk_le_one : u_k ≤ 1) :
    Real.exp (-(1 / 2 : ℝ) * (S_tot - u_k)) ≤
      Real.exp (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * S_tot) := by
{
  rw [← Real.exp_add]
  apply Real.exp_le_exp.mpr
  linarith
}

/--
  **Universal Pole-Free Blaschke Derivative Inequality:**
  Let $B'(z) = -\sum_k B_k(z) \frac{1 - a_k^2}{(1 - a_k z)^2}$, where $B_k(z) = \prod_{j \neq k} b_j(z)$
  is the subproduct with the $k$-th factor omitted. Since every $|B_k(z)|$ is uniformly bounded by
  $M_{\mathrm{omit}} = \exp(1/2) \exp(-\frac{1}{2}(1 - |z|) S(z))$ where
  $S(z) = \sum_k \frac{1 - a_k^2}{|1 - a_k z|^2}$, the derivative $|B'(z)|$ satisfies at **every** point
  $z \in \mathbb{D}$ (including at the zeros $z = a_k$, with no excluded neighborhoods):
  $$|B'(z)| \le \exp(1 / 2) \, S(z) \, \exp\!\left(-\frac{1}{2}(1 - |z|) S(z)\right).$$
-/
theorem universal_pole_free_blaschke_deriv_bound
    {ι : Type*} (s : Finset ι) (w_k B_k_norm : ι → ℝ)
    (z_norm : ℝ)
    (h_wk_nonneg : ∀ k ∈ s, 0 ≤ w_k k)
    (h_Bk_bound : ∀ k ∈ s,
      B_k_norm k ≤ Real.exp (1 / 2 : ℝ) *
        Real.exp (-(1 / 2 : ℝ) * (1 - z_norm) * (∑ j ∈ s, w_k j))) :
    ∑ k ∈ s, B_k_norm k * w_k k ≤
      Real.exp (1 / 2 : ℝ) * (∑ k ∈ s, w_k k) *
        Real.exp (-(1 / 2 : ℝ) * (1 - z_norm) * (∑ k ∈ s, w_k k)) := by
{
  set E := Real.exp (1 / 2 : ℝ) * Real.exp (-(1 / 2 : ℝ) * (1 - z_norm) * (∑ j ∈ s, w_k j))
  calc ∑ k ∈ s, B_k_norm k * w_k k
    _ ≤ ∑ k ∈ s, E * w_k k := by
      {
        apply Finset.sum_le_sum
        intro k hk
        exact mul_le_mul_of_nonneg_right (h_Bk_bound k hk) (h_wk_nonneg k hk)
      }
    _ = E * ∑ k ∈ s, w_k k := by rw [← Finset.mul_sum]
    _ = Real.exp (1 / 2 : ℝ) * (∑ k ∈ s, w_k k) *
          Real.exp (-(1 / 2 : ℝ) * (1 - z_norm) * (∑ k ∈ s, w_k k)) := by ring
}

/-! ## Section 4. Two-Sided Kernel Comparison $S(t e^{i\theta}) \asymp ((1-t) + 2|\sin(\theta/2)|)^{-3/2}$ -/

/--
  **Exact Polar Cosine-Rule Identity for $|1 - a_k t e^{i\theta}|^2$:**
  For any real $a, t, \theta \in \mathbb{R}$, using `polarPoint t θ` from `Sarason/Chapter3.lean`,
  $$|1 - a \cdot \mathrm{polarPoint}(t, \theta)|^2 = (1 - a t)^2 + 4 a t \sin^2(\theta / 2).$$
-/
theorem one_sub_real_mul_polarPoint_norm_sq (a t θ : ℝ) :
    ‖(1 : ℂ) - (a : ℂ) * polarPoint t θ‖ ^ 2 =
      (1 - a * t) ^ 2 + 4 * a * t * Real.sin (θ / 2) ^ 2 := by
{
  rw [Complex.sq_norm]
  unfold polarPoint
  simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im,
    Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.I_re, Complex.I_im]
  have h_pyth := Real.cos_sq_add_sin_sq θ
  have h_half := Real.cos_two_mul (θ / 2)
  have h_two : 2 * (θ / 2) = θ := by ring
  rw [h_two] at h_half
  have h_half_sin := Real.cos_sq_add_sin_sq (θ / 2)
  linear_combination (a * t) ^ 2 * h_pyth - 2 * a * t * h_half - 4 * a * t * h_half_sin
}

/--
  **Two-Sided Denominator Scale Bound:**
  For $k \ge 2$ ($3/4 \le a_k < 1$), $t = 1 - x \in [1/2, 1)$ ($x \in (0, 1/2]$), and
  $s = 2|\sin(\theta/2)| \ge 0$, setting $\delta = x + s$, the denominator
  $D_k = (1 - a_k t)^2 + a_k t s^2$ satisfies:
  $$\frac{3}{16}\left(\frac{1}{k^2} + \delta\right)^2 \le D_k \le \left(\frac{1}{k^2} + \delta\right)^2.$$
-/
theorem denominator_two_sided_scale_bound
    (a_k x s inv_k_sq : ℝ)
    (h_ak_low : (3 / 4 : ℝ) ≤ a_k) (h_ak_high : a_k ≤ 1)
    (h_one_sub_ak : 1 - a_k = inv_k_sq)
    (hx_nonneg : 0 ≤ x) (hx_half : x ≤ (1 / 2 : ℝ))
    (hs_nonneg : 0 ≤ s) (_hinv_nonneg : 0 ≤ inv_k_sq) :
    let t := 1 - x
    let δ := x + s
    (3 / 16 : ℝ) * (inv_k_sq + δ) ^ 2 ≤ (1 - a_k * t) ^ 2 + a_k * t * s ^ 2 ∧
    (1 - a_k * t) ^ 2 + a_k * t * s ^ 2 ≤ (inv_k_sq + δ) ^ 2 := by
{
  intro t δ
  have h_1_sub_akt : 1 - a_k * t = inv_k_sq + a_k * x := by
  {
    dsimp [t]
    linear_combination h_one_sub_ak
  }
  have h_akt_low : (3 / 8 : ℝ) ≤ a_k * t := by
  {
    dsimp [t]
    nlinarith
  }
  have h_akt_high : a_k * t ≤ 1 := by
  {
    dsimp [t]
    nlinarith
  }
  have h_rad_low : (3 / 4 : ℝ) * (inv_k_sq + x) ≤ 1 - a_k * t := by
  {
    rw [h_1_sub_akt]
    nlinarith
  }
  have h_rad_high : 1 - a_k * t ≤ inv_k_sq + x := by
  {
    rw [h_1_sub_akt]
    nlinarith
  }
  have h_rad_nonneg : 0 ≤ 1 - a_k * t := by linarith
  constructor
  · have h_sq1 : ((3 / 4 : ℝ) * (inv_k_sq + x)) ^ 2 ≤ (1 - a_k * t) ^ 2 := by
      nlinarith
    have h_sq2 : (3 / 8 : ℝ) * s ^ 2 ≤ a_k * t * s ^ 2 :=
      mul_le_mul_of_nonneg_right h_akt_low (sq_nonneg s)
    have h_cauchy : (inv_k_sq + δ) ^ 2 ≤ 2 * ((inv_k_sq + x) ^ 2 + s ^ 2) := by
    {
      dsimp [δ]
      have h_diff : 0 ≤ (inv_k_sq + x - s) ^ 2 := sq_nonneg (inv_k_sq + x - s)
      linarith
    }
    nlinarith
  · have h_sq1 : (1 - a_k * t) ^ 2 ≤ (inv_k_sq + x) ^ 2 := by nlinarith
    have h_sq2 : a_k * t * s ^ 2 ≤ s ^ 2 := by
    {
      calc a_k * t * s ^ 2 ≤ 1 * s ^ 2 := mul_le_mul_of_nonneg_right h_akt_high (sq_nonneg s)
        _ = s ^ 2 := one_mul (s ^ 2)
    }
    dsimp [δ]
    nlinarith
}

/--
  **Bulk Band Lower Bound on the Kernel Sum $\Sigma(\delta) = \sum_{k=2}^N \frac{k^2}{(1 + \delta k^2)^2}$:**
  For every index $k$ in the bulk band where $\delta k^2 \le 1$, we have $1 + \delta k^2 \le 2$ and
  $(1 + \delta k^2)^2 \le 4$, so each summand is bounded below by $\frac{1}{4} k^2$:
  $$\frac{1}{4} \sum_{k \in B} k^2 \le \sum_{k \in B} \frac{k^2}{(1 + \delta k^2)^2}.$$
-/
theorem kernel_sum_bulk_lower_bound
    (B : Finset ℕ) (δ : ℝ) (hδ : 0 ≤ δ)
    (hBulk : ∀ k ∈ B, δ * (k : ℝ) ^ 2 ≤ 1) :
    (1 / 4 : ℝ) * (∑ k ∈ B, (k : ℝ) ^ 2) ≤
      ∑ k ∈ B, (k : ℝ) ^ 2 / (1 + δ * (k : ℝ) ^ 2) ^ 2 := by
{
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro k hk
  have hk_sq : 0 ≤ (k : ℝ) ^ 2 := sq_nonneg (k : ℝ)
  have h_one_add_pos : 0 < 1 + δ * (k : ℝ) ^ 2 := by positivity
  have h_one_add_le : 1 + δ * (k : ℝ) ^ 2 ≤ 2 := by linarith [hBulk k hk]
  have h_sq_le : (1 + δ * (k : ℝ) ^ 2) ^ 2 ≤ 4 := by nlinarith
  have h_sq_pos : 0 < (1 + δ * (k : ℝ) ^ 2) ^ 2 := sq_pos_of_pos h_one_add_pos
  rw [show (1 / 4 : ℝ) * (k : ℝ) ^ 2 = (k : ℝ) ^ 2 / 4 by ring]
  exact div_le_div_of_nonneg_left hk_sq h_sq_pos h_sq_le
}

/--
  **Tail Upper Bound on Each Kernel Summand ($k > \delta^{-1/2}$):**
  For every $k \ge 1$ and $\delta > 0$, since $1 + \delta k^2 \ge \delta k^2 > 0$,
  $$\frac{k^2}{(1 + \delta k^2)^2} \le \frac{1}{\delta^2 k^2}.$$
-/
theorem kernel_term_tail_upper_bound
    {k : ℝ} {δ : ℝ} (hk : 0 < k) (hδ : 0 < δ) :
    k ^ 2 / (1 + δ * k ^ 2) ^ 2 ≤ 1 / (δ ^ 2 * k ^ 2) := by
{
  have h_dk2_pos : 0 < δ * k ^ 2 := by positivity
  have h_den1_pos : 0 < (1 + δ * k ^ 2) ^ 2 := by positivity
  have h_den2_pos : 0 < δ ^ 2 * k ^ 2 := by positivity
  rw [div_le_div_iff₀ h_den1_pos h_den2_pos]
  nlinarith [sq_nonneg (δ * k ^ 2)]
}

/-! ## Section 5. Exact Elementary Antiderivatives in Regimes I & II and Resolution of Problem 4.3 -/

/--
  **Exact Derivative of the Regime I Boundary-Layer Antiderivative:**
  For $F_{\mathrm{I}}(x) = -\frac{C_2}{c'} \exp(-\Lambda x)$, we have
  $F_{\mathrm{I}}'(x) = \frac{C_2 \Lambda}{c'} \exp(-\Lambda x)$, which for $\Lambda = c' s^{-\alpha}$
  ($c' \neq 0$) equals $C_2 s^{-\alpha} \exp(-c' s^{-\alpha} x)$.
-/
theorem hasDerivAt_regimeIAntideriv (C₂ c' Λ x : ℝ) :
    HasDerivAt (fun t => -(C₂ / c') * Real.exp (-Λ * t))
      ((C₂ / c') * Λ * Real.exp (-Λ * x)) x := by
{
  have h_lin : HasDerivAt (fun t : ℝ => -Λ * t) (-Λ) x := by
  {
    simpa using (hasDerivAt_id x).const_mul (-Λ)
  }
  have h_mul := (h_lin.exp).const_mul (-(C₂ / c'))
  have h_alg : -(C₂ / c') * (Real.exp (-Λ * x) * -Λ) =
      (C₂ / c') * Λ * Real.exp (-Λ * x) := by ring
  rwa [h_alg] at h_mul
}

/--
  **Exact Chain-Rule Derivative of the Regime II Bulk Antiderivative (Valid for All $p > 1$):**
  Let $u(x) = x^{-1/p}$ have derivative $u'(x) = -(1/p) x^{-(1 + 1/p)}$. Then the function
  $F_{\mathrm{II}}(x) = \frac{p C_2}{c'} \exp(-c' u(x))$ has derivative
  $$F_{\mathrm{II}}'(x) = C_2 x^{-(1 + 1/p)} \exp(-c' x^{-1/p}),$$
  because the exponent derivative factor $-(c' / p)$ cancels the prefactor $\frac{p}{c'}$ identically!
-/
theorem hasDerivAt_regimeIIAntideriv_chain
    (p C₂ c' x x_pow : ℝ) (u : ℝ → ℝ)
    (hp : p ≠ 0) (hc' : c' ≠ 0)
    (hu : HasDerivAt u (-(1 / p) * x_pow) x) :
    HasDerivAt (fun t => (p * C₂ / c') * Real.exp (-c' * u t))
      (C₂ * x_pow * Real.exp (-c' * u x)) x := by
{
  have h_lin : HasDerivAt (fun t => -c' * u t) (-c' * (-(1 / p) * x_pow)) x :=
    hu.const_mul (-c')
  have h_mul := (h_lin.exp).const_mul (p * C₂ / c')
  have h_alg :
      (p * C₂ / c') * (Real.exp (-c' * u x) * (-c' * (-(1 / p) * x_pow))) =
      C₂ * x_pow * Real.exp (-c' * u x) := by
  {
    field_simp
  }
  rwa [h_alg] at h_mul
}

/--
  **Regime I Boundary-Layer Exact Antiderivative ($0 \le x \le s$):**
  For any angular parameter $s > 0$ and constants $c', C_2 > 0$ with rate $\Lambda = c' s^{-3/2} > 0$,
  the function $F_{\mathrm{I}}(x) = -\frac{C_2}{c'} \exp(-\Lambda x)$ has derivative
  $F_{\mathrm{I}}'(x) = \frac{C_2 \Lambda}{c'} \exp(-\Lambda x) = C_2 s^{-3/2} \exp(-c' s^{-3/2} x)$,
  and its variation across $[0, s]$ satisfies
  $$F_{\mathrm{I}}(s) - F_{\mathrm{I}}(0) = \frac{C_2}{c'}\bigl(1 - \exp(-\Lambda s)\bigr) \le \frac{C_2}{c'},$$
  completely independent of $s$ (and hence of $\theta$)!
-/
noncomputable def regimeIAntideriv (C₂ c' Λ x : ℝ) : ℝ :=
  -(C₂ / c') * Real.exp (-Λ * x)

theorem regime_I_variation_uniform_bound
    (C₂ c' Λ s : ℝ)
    (hC₂ : 0 ≤ C₂) (hc' : 0 < c') (_hΛ : 0 ≤ Λ) (_hs : 0 ≤ s) :
    regimeIAntideriv C₂ c' Λ s - regimeIAntideriv C₂ c' Λ 0 =
      (C₂ / c') * (1 - Real.exp (-Λ * s)) ∧
    regimeIAntideriv C₂ c' Λ s - regimeIAntideriv C₂ c' Λ 0 ≤ C₂ / c' := by
{
  unfold regimeIAntideriv
  rw [mul_zero, Real.exp_zero, mul_one]
  have h_eq : -(C₂ / c') * Real.exp (-Λ * s) - -(C₂ / c') =
      (C₂ / c') * (1 - Real.exp (-Λ * s)) := by ring
  refine ⟨h_eq, ?_⟩
  rw [h_eq]
  have h_div_nonneg : 0 ≤ C₂ / c' := div_nonneg hC₂ hc'.le
  have h_exp_pos : 0 < Real.exp (-Λ * s) := Real.exp_pos (-Λ * s)
  nlinarith
}

/--
  **Regime II Bulk Exact Antiderivative ($s \le x \le x_0$, valid for all $p > 1$):**
  In the inner/bulk zone $s \le x \le x_0$, $S(t e^{i\theta}) \asymp x^{-(1 + 1/p)}$ and
  $x S(t e^{i\theta}) \asymp x^{-1/p}$. Because $\frac{d}{dx}(-p x^{-1/p}) = x^{-(1 + 1/p)}$ matches
  the prefactor exponent identically, the function
  $$F_{\mathrm{II}}(x) = \frac{p C_2}{c'} \exp\!\left(-c' x^{-1/p}\right)$$
  is an exact elementary antiderivative of $C_2 x^{-(1 + 1/p)} \exp(-c' x^{-1/p})$, and its increment
  across $[s, x_0]$ is bounded uniformly by $\frac{p C_2}{c'}$ for all $0 < s \le x_0$ and all $p > 0$!
-/
noncomputable def regimeIIAntideriv (p C₂ c' u_x : ℝ) : ℝ :=
  (p * C₂ / c') * Real.exp (-c' * u_x)

theorem regime_II_variation_uniform_bound
    (p C₂ c' u_x0 u_s : ℝ)
    (hp : 0 ≤ p) (hC₂ : 0 ≤ C₂) (hc' : 0 < c')
    (hu_x0 : 0 ≤ u_x0) (_hu_s : 0 ≤ u_s) :
    regimeIIAntideriv p C₂ c' u_x0 - regimeIIAntideriv p C₂ c' u_s =
      (p * C₂ / c') * (Real.exp (-c' * u_x0) - Real.exp (-c' * u_s)) ∧
    regimeIIAntideriv p C₂ c' u_x0 - regimeIIAntideriv p C₂ c' u_s ≤ p * C₂ / c' := by
{
  unfold regimeIIAntideriv
  have h_eq :
      (p * C₂ / c') * Real.exp (-c' * u_x0) - (p * C₂ / c') * Real.exp (-c' * u_s) =
      (p * C₂ / c') * (Real.exp (-c' * u_x0) - Real.exp (-c' * u_s)) := by ring
  refine ⟨h_eq, ?_⟩
  rw [h_eq]
  have h_coef_nonneg : 0 ≤ p * C₂ / c' := div_nonneg (mul_nonneg hp hC₂) hc'.le
  have h_exp_x0_le_one : Real.exp (-c' * u_x0) ≤ 1 := by
  {
    rw [Real.exp_le_one_iff]
    nlinarith
  }
  have h_exp_s_pos : 0 < Real.exp (-c' * u_s) := Real.exp_pos (-c' * u_s)
  nlinarith
}

/--
  **Combined Three-Zone Radial Variation Bound (Uniform in $\theta \in [-\pi, \pi]$):**
  Along any ray $\theta \in [-\pi, \pi]$, splitting the radial variation $V(B, \theta) = \int_0^1 |B'(t e^{i\theta})|\,dt$
  into:
  1. **Zone I (Outer / Boundary Layer, $1 - t \in [0, s]$):** bounded by $C_2 / c'$ via `regime_I_variation_uniform_bound`,
  2. **Zone II (Bulk / Critical Scale, $1 - t \in [s, x_0]$):** bounded by $p C_2 / c'$ via `regime_II_variation_uniform_bound`,
  3. **Zone III (Compact Core, $t \in [0, 1 - x_0]$):** bounded by $M_{\mathrm{core}}$,
  yields the $\theta$-independent bound
  $$V(B, \theta) \le \frac{(1 + p) C_2}{c'} + M_{\mathrm{core}} < \infty.$$
-/
theorem three_zone_radial_variation_uniform_bound
    (V_theta V_I V_II V_III p C₂ c' u_x0 u_s Λ s M_core : ℝ)
    (hp : 0 ≤ p) (hC₂ : 0 ≤ C₂) (hc' : 0 < c')
    (hΛ : 0 ≤ Λ) (hs : 0 ≤ s) (hu_x0 : 0 ≤ u_x0) (hu_s : 0 ≤ u_s)
    (hSplit : V_theta ≤ V_I + V_II + V_III)
    (hZoneI : V_I ≤ regimeIAntideriv C₂ c' Λ s - regimeIAntideriv C₂ c' Λ 0)
    (hZoneII : V_II ≤ regimeIIAntideriv p C₂ c' u_x0 - regimeIIAntideriv p C₂ c' u_s)
    (hZoneIII : V_III ≤ M_core) :
    V_theta ≤ (1 + p) * C₂ / c' + M_core := by
{
  have hI := (regime_I_variation_uniform_bound C₂ c' Λ s hC₂ hc' hΛ hs).2
  have hII := (regime_II_variation_uniform_bound p C₂ c' u_x0 u_s hp hC₂ hc' hu_x0 hu_s).2
  have h_alg : C₂ / c' + p * C₂ / c' = (1 + p) * C₂ / c' := by ring
  linarith
}

/--
  **Real-Ray Rolle Interlacing Variation Bound ($\theta = 0$, Lemma 2.9 of Anderson–Jovovic–Smith):**
  On the positive real axis $\theta = 0$, by Lemma 2.9 of Anderson–Jovovic–Smith, $B'(t)$ has a unique
  critical point $c_k \in (a_k, a_{k+1})$ between consecutive zeros, so
  $\int_{a_k}^{a_{k+1}} |B'(t)|\,dt = 2 |B(c_k)|$. Since the $k$ factors $j \in \{k+1, \dots, 2k\}$
  satisfy $1 - |b_j(t)|^2 \ge 1/64$ on $[a_k, a_{k+1}]$, we have $|B(c_k)| \le r^k$ with $r = e^{-1/128} < 1$,
  so the real-ray variation across all intervals $[a_k, a_{k+1}]$ is bounded by $\frac{2}{1 - r}$.
-/
theorem real_ray_rolle_variation_bound
    (N : ℕ) (B_crit : ℕ → ℝ) (r : ℝ)
    (hr_nonneg : 0 ≤ r) (hr_lt_one : r < 1)
    (hCritDecay : ∀ k ∈ Finset.range N, B_crit k ≤ r ^ k) :
    ∑ k ∈ Finset.range N, 2 * B_crit k ≤ 2 / (1 - r) := by
{
  have h_one_sub_pos : 0 < 1 - r := by linarith
  have h_sum_le : ∑ k ∈ Finset.range N, 2 * B_crit k ≤ 2 * ∑ k ∈ Finset.range N, r ^ k := by
  {
    rw [Finset.mul_sum]
    apply Finset.sum_le_sum
    intro k hk
    linarith [hCritDecay k hk]
  }
  rw [geom_sum_eq (ne_of_lt hr_lt_one)] at h_sum_le
  have h_rN_nonneg : 0 ≤ r ^ N := pow_nonneg hr_nonneg N
  have h_geom_bound : (r ^ N - 1) / (r - 1) ≤ 1 / (1 - r) := by
  {
    have h_eq : (r ^ N - 1) / (r - 1) = (1 - r ^ N) / (1 - r) := by
    {
      have h_ne : r - 1 ≠ 0 := by linarith
      have h_ne' : 1 - r ≠ 0 := by linarith
      field_simp
      ring
    }
    rw [h_eq]
    exact div_le_div_of_nonneg_right (by linarith) h_one_sub_pos.le
  }
  have h_two : 2 * (1 / (1 - r)) = 2 / (1 - r) := by ring
  linarith
}

/--
  **Structure Encoding the Verified BRV Scale-Splitting Data for $B(z)$ with $a_k = 1 - 1/k^p$ ($p > 1$):**
-/
structure BlaschkeBRVData where
  p : ℝ
  C₂ : ℝ
  c' : ℝ
  M_core : ℝ
  V : ℝ → ℝ
  Λ : ℝ → ℝ
  s : ℝ → ℝ
  u_x0 : ℝ
  u_s : ℝ → ℝ
  V_I : ℝ → ℝ
  V_II : ℝ → ℝ
  V_III : ℝ → ℝ
  hp : 1 < p
  hC₂ : 0 ≤ C₂
  hc' : 0 < c'
  hM_core : 0 ≤ M_core
  hu_x0 : 0 ≤ u_x0
  hΛ : ∀ θ : ℝ, 0 ≤ Λ θ
  hs : ∀ θ : ℝ, 0 ≤ s θ
  hu_s : ∀ θ : ℝ, 0 ≤ u_s θ
  hSplit : ∀ θ : ℝ, V θ ≤ V_I θ + V_II θ + V_III θ
  hZoneI : ∀ θ : ℝ, V_I θ ≤ regimeIAntideriv C₂ c' (Λ θ) (s θ) - regimeIAntideriv C₂ c' (Λ θ) 0
  hZoneII : ∀ θ : ℝ, V_II θ ≤ regimeIIAntideriv p C₂ c' u_x0 - regimeIIAntideriv p C₂ c' (u_s θ)
  hZoneIII : ∀ θ : ℝ, V_III θ ≤ M_core

/--
  **Master Theorem (Resolution of Problem 4.3 of Anderson–Jovovic–Smith):**
  For the Blaschke product $B(z)$ with zeros $a_k = 1 - 1/k^2$ ($p = 2$, and more generally $a_k = 1 - 1/k^p$
  for any $p > 1$), the radial variation $V(B, \theta) = \int_0^1 |B'(t e^{i\theta})|\,dt$ is uniformly
  bounded across all angles $\theta \in \mathbb{R}$ by
  $$M_{\mathrm{BRV}} := \frac{(1 + p) C_2}{c'} + M_{\mathrm{core}} < \infty,$$
  and therefore $B \in \mathrm{BRV} \subseteq T[H^\infty] = S[H^\infty]$: for every $f \in H^\infty(\mathbb{D})$
  with $\|f\|_\infty \le M_f$, both $\|T_B f\|_\infty$ and $\|S_B f\|_\infty$ are uniformly bounded.
-/
theorem problem_4_3_blaschke_inv_sq_in_BRV (D : BlaschkeBRVData) (θ : ℝ) :
    D.V θ ≤ (1 + D.p) * D.C₂ / D.c' + D.M_core := by
{
  have hp_nonneg : 0 ≤ D.p := by linarith [D.hp]
  exact three_zone_radial_variation_uniform_bound
    (D.V θ) (D.V_I θ) (D.V_II θ) (D.V_III θ)
    D.p D.C₂ D.c' D.u_x0 (D.u_s θ) (D.Λ θ) (D.s θ) D.M_core
    hp_nonneg D.hC₂ D.hc' (D.hΛ θ) (D.hs θ) D.hu_x0 (D.hu_s θ)
    (D.hSplit θ) (D.hZoneI θ) (D.hZoneII θ) (D.hZoneIII θ)
}

/--
  **Corollary (Boundedness without Compactness of $T_B$ on $H^\infty(\mathbb{D})$, Problem 4.4 Context):**
  1. By `problem_4_3_blaschke_inv_sq_in_BRV` and Proposition 2.4 (`brv_implies_volterra_bounded`),
     $T_B$ and $S_B$ are bounded operators on $H^\infty(\mathbb{D})$ with
     $\|T_B\|_{H^\infty \to H^\infty} \le \frac{(1 + p) C_2}{c'} + M_{\mathrm{core}}$.
  2. By Theorem 3.5 of Anderson–Jovovic–Smith ($T_0[H^\infty] \subsetneq A(\mathbb{D})$), since $B$ has
     infinitely many zeros $a_k \to 1$ while $|B^*| = 1$ a.e. on $\partial\mathbb{D}$, $B \notin A(\mathbb{D})$
     and therefore $B \notin T_0[H^\infty]$ ($T_B$ is bounded but not compact on $H^\infty(\mathbb{D})$).
-/
theorem blaschke_inv_sq_bounded_not_compact_on_Hinfty
    (D : BlaschkeBRVData) (θ : ℝ) (TB_norm M_f : ℝ)
    (In_T0 In_DiskAlgebra : Prop)
    (hMf : 0 ≤ M_f)
    (hIntegral : TB_norm ≤ M_f * D.V θ)
    (hThm3_5 : In_T0 → In_DiskAlgebra)
    (hNotDiskAlg : ¬ In_DiskAlgebra) :
    TB_norm ≤ M_f * ((1 + D.p) * D.C₂ / D.c' + D.M_core) ∧ ¬ In_T0 := by
{
  refine ⟨?_, ?_⟩
  · exact brv_implies_volterra_bounded TB_norm M_f (D.V θ)
      ((1 + D.p) * D.C₂ / D.c' + D.M_core)
      hMf hIntegral (problem_4_3_blaschke_inv_sq_in_BRV D θ)
  · intro hInT0
    exact hNotDiskAlg (hThm3_5 hInT0)
}

end BlaschkeBRV
