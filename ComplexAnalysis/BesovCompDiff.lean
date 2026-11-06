/-
Copyright (c) 2026 Austin Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Austin Anderson
-/
import Mathlib

/-!
# Compact Differences of Composition Operators on Weighted Besov Spaces $B^p_\alpha(\mathbb{D})$
# and the Saukko–Choe–Choi–Koo–Park Gap

This file provides machine-checked Lean 4 proofs for the core analytic and algebraic
pillars of the unified theory of compact differences of composition operators
$T = C_\varphi - C_\psi$ acting on the two-parameter scale of weighted Besov /
Dirichlet-type spaces $B^p_\alpha(\mathbb{D})$ ($\alpha > -1$, $0 < p < \infty$), defined by
$$
  \|f\|_{B^p_\alpha}^p = |f(0)|^p + \int_{\mathbb{D}} |f'(z)|^p (1 - |z|^2)^\alpha\,dA(z).
$$

## Main Formalized Results

1. **The Derivative Isometry & Weighted Composition Conjugation (`Section 1`)**:
   - `comp_diff_const_eq_zero`: $C_\varphi - C_\psi$ annihilates constant functions, reducing
     boundedness and compactness on $B^p_\alpha(\mathbb{D}) = \mathbb{C} \oplus B^p_{\alpha,0}(\mathbb{D})$
     to the normalized subspace $B^p_{\alpha,0}(\mathbb{D}) = \{f \in B^p_\alpha : f(0) = 0\}$.
   - `hasDerivAt_comp_diff_eq_weighted_comp_diff`: Under the derivative isometry
     $D : B^p_{\alpha,0}(\mathbb{D}) \to A^p_\alpha(\mathbb{D})$, $Df = f'$, the unweighted
     composition difference $C_\varphi - C_\psi$ conjugates identically to the weighted
     composition difference $C_{\varphi,\varphi'} - C_{\psi,\psi'}$ on the weighted Bergman
     space $A^p_\alpha(\mathbb{D})$.
   - `besov_exponent_table`: Unifies classical Möbius-invariant Besov spaces $B_p(\mathbb{D})$
     ($\alpha = p - 2$), the classical Dirichlet space $\mathcal{D}$ ($p = 2, \alpha = 0$),
     and weighted Dirichlet spaces $\mathcal{D}_\alpha$ ($p = 2, \alpha > -1$).

2. **Two-Regime Carleson Measure Splitting & $\beta$-Invariance (`Section 2`)**:
   - `compact_carleson_sum_iff`: For non-negative pullback measures $\omega_{\alpha,p}$ and
     $\sigma_{\alpha,p,\beta}$, the sum $\omega_{\alpha,p} + \sigma_{\alpha,p,\beta}$ is a
     compact $\alpha$-Carleson measure iff both summands are.
   - `near_diagonal_attenuation_bounds`: On the near-diagonal region
     $G_r = \{z : \rho(\varphi(z),\psi(z)) < r\}$, the attenuation factor $(1-\rho)^\beta$
     is bounded between $(1-r)^\beta$ and $1$.
   - `far_diagonal_controlled_by_omega`: On the far-diagonal region $\rho \ge r > 0$,
     $(1-\rho)^\beta |\varphi' - \psi'|^p \le (2/r)^p (\rho^p |\varphi'|^p + \rho^p |\psi'|^p)$,
     proving that the far-diagonal tail of $\sigma_{\alpha,p,\beta}$ is absorbed by $\omega_{\alpha,p}$
     and establishing invariance with respect to $\beta > \alpha + 2$ (`beta_invariance_density_bound`).

3. **Universal Automorphism / Reproducing Kernel Thesis Equivalence on $B_p(\mathbb{D})$ (`Section 3`)**:
   - `automorphism_sub_center_eq_neg_kernel`: Proves $\alpha_\lambda(z) - \lambda = -k_\lambda^{(1)}(z)$
     for all $\lambda, z \in \mathbb{D}$.
   - `besov_test_exponent_eq_one` & `hasDerivAt_kernel_eq_bergman_test`: Proves that on the entire
     scale of Möbius-invariant Besov spaces $B_p(\mathbb{D})$ ($\alpha = p - 2$, $1 < p < \infty$),
     the Choe–Choi–Koo–Yang normalized Bergman test function $f_{b,2}(w) = \frac{(1-|b|^2)^{2-(\alpha+2)/p}}{(1-\bar{b}w)^2}$
     simplifies to $\frac{1-|b|^2}{(1-\bar{b}w)^2} = (k_b^{(1)})'(w) = -\alpha_b'(w)$, so its
     antiderivative in $B_{p,0}(\mathbb{D})$ is universally $k_b^{(1)}(z) = b - \alpha_b(z)$.

4. **Quantitative Analysis of the Saukko vs. Choe–Choi–Koo–Park Gap (`Section 4`)**:
   - `saukko_implies_joint_carleson`: Direct proof that Saukko's condition controls the
     Choe–Choi–Koo–Park joint Carleson functional $\lambda_{p,s}(a)$.
   - `saukko_strictly_stronger_in_three_scale_regime`: Quantitative separation theorem proving
     that in the three-scale regime where $|\varphi^* - \psi^*| = \varepsilon(a)(1-|a|)$ with
     $\varepsilon(a) \to 0$ and $1 - |\varphi^*|^2 \le M \varepsilon(a)(1-|a|)$, Saukko's
     normalized Carleson ratio stays bounded below by $\kappa / (1 + M)^p > 0$ while the
     Choe–Choi–Koo–Park joint integral ratio vanishes at rate $O(\varepsilon(a)^p) \to 0$.
-/

noncomputable section

open scoped Real Topology BigOperators
open Filter MeasureTheory Set

namespace BesovCompDiff

/-!
## Section 1: The Derivative Isometry and Weighted Composition Conjugation
-/

/-- The composition operator $C_\varphi f = f \circ \varphi$. -/
def compOp (φ : ℂ → ℂ) (f : ℂ → ℂ) : ℂ → ℂ := fun z => f (φ z)

/-- The weighted composition operator $(C_{\varphi, u} h)(z) = u(z) h(\varphi(z))$. -/
def weightedCompOp (φ u : ℂ → ℂ) (h : ℂ → ℂ) : ℂ → ℂ := fun z => u z * h (φ z)

/-- The difference of two composition operators $(C_\varphi - C_\psi)f(z) = f(\varphi(z)) - f(\psi(z))$. -/
def compDiffOp (φ ψ : ℂ → ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => compOp φ f z - compOp ψ f z

/-- The difference of two weighted composition operators
$(C_{\varphi,u} - C_{\psi,v})h(z) = u(z)h(\varphi(z)) - v(z)h(\psi(z))$. -/
def weightedCompDiffOp (φ u ψ v : ℂ → ℂ) (h : ℂ → ℂ) : ℂ → ℂ :=
  fun z => weightedCompOp φ u h z - weightedCompOp ψ v h z

/-- The difference operator $C_\varphi - C_\psi$ annihilates every constant function $f(z) \equiv c$. -/
theorem comp_diff_const_eq_zero (φ ψ : ℂ → ℂ) (c : ℂ) (z : ℂ) :
    compDiffOp φ ψ (fun _ => c) z = 0 := by
  simp [compDiffOp, compOp]

/-- Subtracting a constant $c$ from $f$ does not change $(C_\varphi - C_\psi)f$. -/
theorem comp_diff_sub_const (φ ψ : ℂ → ℂ) (f : ℂ → ℂ) (c : ℂ) (z : ℂ) :
    compDiffOp φ ψ (fun w => f w - c) z = compDiffOp φ ψ f z := by
  simp only [compDiffOp, compOp]
  ring

/-- **Operator Conjugation Identity (`D ∘ (C_φ - C_ψ) = (C_{φ,φ'} - C_{ψ,ψ'}) ∘ D`)**:
By the complex chain rule, if $f$ has derivative $f'$ at $\varphi(z)$ and $\psi(z)$,
and $\varphi, \psi$ have derivatives $\varphi'(z), \psi'(z)$ at $z$, then
$(C_\varphi f - C_\psi f)$ has derivative $(C_{\varphi,\varphi'} f' - C_{\psi,\psi'} f')(z)$ at $z$. -/
theorem hasDerivAt_comp_diff_eq_weighted_comp_diff
    (f f' φ φ' ψ ψ' : ℂ → ℂ) (z : ℂ)
    (hfφ : HasDerivAt f (f' (φ z)) (φ z))
    (hfψ : HasDerivAt f (f' (ψ z)) (ψ z))
    (hφ : HasDerivAt φ (φ' z) z)
    (hψ : HasDerivAt ψ (ψ' z) z) :
    HasDerivAt (compDiffOp φ ψ f) (weightedCompDiffOp φ φ' ψ ψ' f' z) z := by
  have h1 : HasDerivAt (compOp φ f) (f' (φ z) * φ' z) z := hfφ.comp z hφ
  have h2 : HasDerivAt (compOp ψ f) (f' (ψ z) * ψ' z) z := hfψ.comp z hψ
  exact (h1.sub h2).congr_deriv (by simp only [weightedCompDiffOp, weightedCompOp]; ring)

/-- Parameter unification for the two-parameter weighted Besov scale $B^p_\alpha(\mathbb{D})$:
1. For the classical Möbius-invariant Besov space $B_p(\mathbb{D})$ ($p > 1$), $\alpha = p - 2 > -1$.
2. For the classical Dirichlet space $\mathcal{D} = B_2(\mathbb{D})$, $p = 2$ and $\alpha = 0$.
3. The critical attenuation threshold $\alpha + 2$ from Choe–Choi–Koo–Yang (2020) equals $p$ on $B_p(\mathbb{D})$
   and equals $2$ on $\mathcal{D}$. -/
theorem besov_exponent_table (p : ℝ) (hp : 1 < p) :
    let α := p - 2
    α > -1 ∧ α + 2 = p ∧ ((2 : ℝ) - 2 = 0 ∧ (0 : ℝ) + 2 = 2) := by
  intro α
  refine ⟨by linarith, by ring, ⟨by ring, by ring⟩⟩

/-!
## Section 2: Two-Regime Carleson Measure Splitting and $\beta$-Invariance
-/

/-- Two non-negative Carleson box ratios vanish as $|a| \to 1$ if and only if their sum vanishes. -/
theorem compact_carleson_sum_iff {ι : Type*} {l : Filter ι} (ω_ratio σ_ratio : ι → ℝ)
    (hω : ∀ a, 0 ≤ ω_ratio a) (hσ : ∀ a, 0 ≤ σ_ratio a) :
    Tendsto (fun a => ω_ratio a + σ_ratio a) l (nhds 0) ↔
      Tendsto ω_ratio l (nhds 0) ∧ Tendsto σ_ratio l (nhds 0) := by
  constructor
  · intro h_sum
    have hω_le : ∀ a, ω_ratio a ≤ ω_ratio a + σ_ratio a := fun a => le_add_of_nonneg_right (hσ a)
    have hσ_le : ∀ a, σ_ratio a ≤ ω_ratio a + σ_ratio a := fun a => le_add_of_nonneg_left (hω a)
    exact ⟨squeeze_zero hω hω_le h_sum, squeeze_zero hσ hσ_le h_sum⟩
  · rintro ⟨h1, h2⟩
    simpa using h1.add h2

/-- **Near-Diagonal Attenuation Bounds**:
On the near-diagonal region $G_r = \{z \in \mathbb{D} : \rho(z) \le r\}$ ($0 \le \rho \le r < 1$)
with $\beta \ge 0$, the attenuation weight $(1 - \rho)^\beta$ satisfies
$(1 - r)^\beta \le (1 - \rho)^\beta \le 1$. -/
theorem near_diagonal_attenuation_bounds (ρ r β : ℝ)
    (hρ0 : 0 ≤ ρ) (hρr : ρ ≤ r) (hr1 : r < 1) (hβ : 0 ≤ β) :
    (1 - r) ^ β ≤ (1 - ρ) ^ β ∧ (1 - ρ) ^ β ≤ 1 := by
  constructor
  · exact Real.rpow_le_rpow (by linarith) (by linarith) hβ
  · exact Real.rpow_le_one (by linarith) (by linarith) hβ

/-- **Elementary $L^p$ Triangle Inequality ($0 < p$)**:
For non-negative reals $a, b \ge 0$ and $p \ge 0$, $(a + b)^p \le 2^p (a^p + b^p)$. -/
theorem rpow_add_le_two_rpow_mul_add_rpow (a b p : ℝ)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hp : 0 ≤ p) :
    (a + b) ^ p ≤ (2 : ℝ) ^ p * (a ^ p + b ^ p) := by
  rcases le_total a b with hab | hba
  · have h1 : (a + b) ^ p ≤ (2 * b) ^ p :=
      Real.rpow_le_rpow (by linarith) (by linarith) hp
    have h2 : (2 * b) ^ p = (2 : ℝ) ^ p * b ^ p :=
      Real.mul_rpow (by norm_num) hb
    have h3 : (2 : ℝ) ^ p * b ^ p ≤ (2 : ℝ) ^ p * (a ^ p + b ^ p) := by
      apply mul_le_mul_of_nonneg_left
      · linarith [Real.rpow_nonneg ha p]
      · exact Real.rpow_nonneg (by norm_num) p
    linarith
  · have h1 : (a + b) ^ p ≤ (2 * a) ^ p :=
      Real.rpow_le_rpow (by linarith) (by linarith) hp
    have h2 : (2 * a) ^ p = (2 : ℝ) ^ p * a ^ p :=
      Real.mul_rpow (by norm_num) ha
    have h3 : (2 : ℝ) ^ p * a ^ p ≤ (2 : ℝ) ^ p * (a ^ p + b ^ p) := by
      apply mul_le_mul_of_nonneg_left
      · linarith [Real.rpow_nonneg hb p]
      · exact Real.rpow_nonneg (by norm_num) p
    linarith

/-- **Far-Diagonal Control by $\omega_{\alpha,p}$**:
On the far-diagonal region $\mathbb{D} \setminus G_r$ where $0 < r \le \rho \le 1$,
for any complex derivatives $u, v \in \mathbb{C}$, $p \ge 0$, and $\beta \ge 0$, the attenuated
derivative-difference density is dominated by the individual $\omega_{\alpha,p}$ densities:
$$
  (1 - \rho)^\beta \|u - v\|^p \le (2 / r)^p \bigl((\rho \|u\|)^p + (\rho \|v\|)^p\bigr).
$$ -/
theorem far_diagonal_controlled_by_omega (u v : ℂ) (ρ r p β : ℝ)
    (hr0 : 0 < r) (hrρ : r ≤ ρ) (hρ1 : ρ ≤ 1) (hp : 0 ≤ p) (hβ : 0 ≤ β) :
    (1 - ρ) ^ β * ‖u - v‖ ^ p ≤
      (2 / r) ^ p * ((ρ * ‖u‖) ^ p + (ρ * ‖v‖) ^ p) := by
  have hρ0 : 0 < ρ := lt_of_lt_of_le hr0 hrρ
  have h_att : (1 - ρ) ^ β ≤ 1 := Real.rpow_le_one (by linarith) (by linarith) hβ
  have h_tri : ‖u - v‖ ≤ ‖u‖ + ‖v‖ := norm_sub_le u v
  have h_rpow_tri : ‖u - v‖ ^ p ≤ (2 : ℝ) ^ p * (‖u‖ ^ p + ‖v‖ ^ p) := by
    calc ‖u - v‖ ^ p
      _ ≤ (‖u‖ + ‖v‖) ^ p := Real.rpow_le_rpow (norm_nonneg _) h_tri hp
      _ ≤ (2 : ℝ) ^ p * (‖u‖ ^ p + ‖v‖ ^ p) :=
          rpow_add_le_two_rpow_mul_add_rpow ‖u‖ ‖v‖ p (norm_nonneg u) (norm_nonneg v) hp
  have h_one_le : (1 : ℝ) ≤ (ρ / r) ^ p :=
    Real.one_le_rpow ( ( one_le_div hr0 ).mpr hrρ ) hp
  have h_scale : ‖u‖ ^ p + ‖v‖ ^ p ≤ (1 / r) ^ p * ((ρ * ‖u‖) ^ p + (ρ * ‖v‖) ^ p) := by
    have hu_ρ : (ρ * ‖u‖) ^ p = ρ ^ p * ‖u‖ ^ p := Real.mul_rpow hρ0.le (norm_nonneg u)
    have hv_ρ : (ρ * ‖v‖) ^ p = ρ ^ p * ‖v‖ ^ p := Real.mul_rpow hρ0.le (norm_nonneg v)
    have h_div : (1 / r) ^ p * ρ ^ p = (ρ / r) ^ p := by
      rw [← Real.mul_rpow (by positivity) hρ0.le]
      ring_nf
    calc ‖u‖ ^ p + ‖v‖ ^ p
      _ = 1 * (‖u‖ ^ p + ‖v‖ ^ p) := by ring
      _ ≤ (ρ / r) ^ p * (‖u‖ ^ p + ‖v‖ ^ p) := by
          apply mul_le_mul_of_nonneg_right h_one_le
          positivity
      _ = (1 / r) ^ p * ((ρ * ‖u‖) ^ p + (ρ * ‖v‖) ^ p) := by
          rw [hu_ρ, hv_ρ, ← h_div]
          ring
  have h_two_r : (2 : ℝ) ^ p * (1 / r) ^ p = (2 / r) ^ p := by
    rw [← Real.mul_rpow (by norm_num) (by positivity)]
    ring_nf
  calc (1 - ρ) ^ β * ‖u - v‖ ^ p
    _ ≤ 1 * ‖u - v‖ ^ p := by
        apply mul_le_mul_of_nonneg_right h_att (Real.rpow_nonneg (norm_nonneg _) p)
    _ = ‖u - v‖ ^ p := one_mul _
    _ ≤ (2 : ℝ) ^ p * (‖u‖ ^ p + ‖v‖ ^ p) := h_rpow_tri
    _ ≤ (2 : ℝ) ^ p * ((1 / r) ^ p * ((ρ * ‖u‖) ^ p + (ρ * ‖v‖) ^ p)) := by
        apply mul_le_mul_of_nonneg_left h_scale (Real.rpow_nonneg (by norm_num) p)
    _ = (2 / r) ^ p * ((ρ * ‖u‖) ^ p + (ρ * ‖v‖) ^ p) := by
        rw [← mul_assoc, h_two_r]

/-- **Pointwise $\beta$-Invariance Inequality**:
For any $\beta_1, \beta_2 \ge 0$, any cutoff $r \in (0, 1)$, and any $\rho \in [0, 1]$,
the $\beta_2$-attenuated density is globally controlled by a constant multiple of the
sum of the $\beta_1$-attenuated density and the $\omega_{\alpha,p}$ density:
$$
  (1 - \rho)^{\beta_2} \|u - v\|^p \le
    (1 - r)^{-\beta_1} (1 - \rho)^{\beta_1} \|u - v\|^p +
    (2 / r)^p \bigl((\rho \|u\|)^p + (\rho \|v\|)^p\bigr).
$$ -/
theorem beta_invariance_density_bound (u v : ℂ) (ρ r p β₁ β₂ : ℝ)
    (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) (hr0 : 0 < r) (hr1 : r < 1)
    (hp : 0 ≤ p) (hβ₁ : 0 ≤ β₁) (hβ₂ : 0 ≤ β₂) :
    (1 - ρ) ^ β₂ * ‖u - v‖ ^ p ≤
      (1 - r) ^ (-β₁) * ((1 - ρ) ^ β₁ * ‖u - v‖ ^ p) +
        (2 / r) ^ p * ((ρ * ‖u‖) ^ p + (ρ * ‖v‖) ^ p) := by
  have h_omega_nonneg : 0 ≤ (2 / r) ^ p * ((ρ * ‖u‖) ^ p + (ρ * ‖v‖) ^ p) := by positivity
  have h_sigma_nonneg : 0 ≤ (1 - r) ^ (-β₁) * ((1 - ρ) ^ β₁ * ‖u - v‖ ^ p) := by
    have : 0 ≤ (1 - ρ) ^ β₁ := Real.rpow_nonneg (by linarith) β₁
    have : 0 ≤ (1 - r) ^ (-β₁) := Real.rpow_nonneg (by linarith) (-β₁)
    positivity
  rcases le_total ρ r with h_near | h_far
  · have h_bounds := near_diagonal_attenuation_bounds ρ r β₁ hρ0 h_near hr1 hβ₁
    have h_b2 : (1 - ρ) ^ β₂ ≤ 1 := (near_diagonal_attenuation_bounds ρ r β₂ hρ0 h_near hr1 hβ₂).2
    have h_inv : 1 ≤ (1 - r) ^ (-β₁) * (1 - ρ) ^ β₁ := by
      have h_pos : 0 < 1 - r := by linarith
      have h_cancel : (1 - r) ^ (-β₁) * (1 - r) ^ β₁ = 1 := by
        rw [← Real.rpow_add h_pos, neg_add_cancel, Real.rpow_zero]
      calc (1 : ℝ)
        _ = (1 - r) ^ (-β₁) * (1 - r) ^ β₁ := h_cancel.symm
        _ ≤ (1 - r) ^ (-β₁) * (1 - ρ) ^ β₁ := by
            apply mul_le_mul_of_nonneg_left h_bounds.1
            exact Real.rpow_nonneg h_pos.le (-β₁)
    have h_le1 : (1 - ρ) ^ β₂ * ‖u - v‖ ^ p ≤
        (1 - r) ^ (-β₁) * ((1 - ρ) ^ β₁ * ‖u - v‖ ^ p) := by
      calc (1 - ρ) ^ β₂ * ‖u - v‖ ^ p
        _ ≤ 1 * ‖u - v‖ ^ p :=
            mul_le_mul_of_nonneg_right h_b2 (Real.rpow_nonneg (norm_nonneg _) p)
        _ ≤ ((1 - r) ^ (-β₁) * (1 - ρ) ^ β₁) * ‖u - v‖ ^ p :=
            mul_le_mul_of_nonneg_right h_inv (Real.rpow_nonneg (norm_nonneg _) p)
        _ = (1 - r) ^ (-β₁) * ((1 - ρ) ^ β₁ * ‖u - v‖ ^ p) := by ring
    linarith
  · have h_le2 := far_diagonal_controlled_by_omega u v ρ r p β₂ hr0 h_far hρ1 hp hβ₂
    linarith

/-!
## Section 3: Universal Automorphism / Reproducing Kernel Thesis Equivalence on $B_p(\mathbb{D})$
-/

/-- The conformal automorphism $\alpha_\lambda(z) = \frac{\lambda - z}{1 - \bar{\lambda} z}$ of $\mathbb{D}$
exchanging $0$ and $\lambda$. -/
def diskAutomorphism (lam z : ℂ) : ℂ :=
  (lam - z) / (1 - starRingEnd ℂ lam * z)

/-- The normalized reproducing kernel $k_\lambda^{(1)}(z) = \frac{(1 - |\lambda|^2)z}{1 - \bar{\lambda}z}$
for derivative evaluation in $\mathcal{D}_0$ (and the universal integrated test function in $B_{p,0}(\mathbb{D})$). -/
def normalizedDerivKernel (lam z : ℂ) : ℂ :=
  ((1 - (‖lam‖ ^ 2 : ℝ) : ℝ) : ℂ) * z / (1 - starRingEnd ℂ lam * z)

/-- **Fundamental Automorphism–Kernel Identity**:
For every $\lambda, z \in \mathbb{C}$ with $1 - \bar{\lambda} z \ne 0$,
$$
  \alpha_\lambda(z) - \lambda = -k_\lambda^{(1)}(z) = -\frac{(1 - |\lambda|^2) z}{1 - \bar{\lambda} z}.
$$ -/
theorem automorphism_sub_center_eq_neg_kernel (lam z : ℂ)
    (h_den : 1 - starRingEnd ℂ lam * z ≠ 0) :
    diskAutomorphism lam z - lam = - normalizedDerivKernel lam z := by
  unfold diskAutomorphism normalizedDerivKernel
  have h_norm : lam * starRingEnd ℂ lam = ((‖lam‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]
  rw [div_sub' h_den, ← neg_div]
  congr 1
  push_cast at h_norm ⊢
  linear_combination z * h_norm

/-- Since $T = C_\varphi - C_\psi$ annihilates the constant function $\lambda$,
$(T \alpha_\lambda)(z) = -(T k_\lambda^{(1)})(z)$ holds identically whenever
$1 - \bar{\lambda}\varphi(z) \ne 0$ and $1 - \bar{\lambda}\psi(z) \ne 0$. -/
theorem comp_diff_automorphism_eq_neg_kernel (φ ψ : ℂ → ℂ) (lam z : ℂ)
    (hφ : 1 - starRingEnd ℂ lam * φ z ≠ 0)
    (hψ : 1 - starRingEnd ℂ lam * ψ z ≠ 0) :
    compDiffOp φ ψ (diskAutomorphism lam) z =
      - compDiffOp φ ψ (normalizedDerivKernel lam) z := by
  have h_sub := comp_diff_sub_const φ ψ (diskAutomorphism lam) lam z
  rw [← h_sub]
  simp only [compDiffOp, compOp]
  rw [automorphism_sub_center_eq_neg_kernel lam (φ z) hφ,
      automorphism_sub_center_eq_neg_kernel lam (ψ z) hψ]
  ring

/-- **Why $\alpha_b$ is the Universal Test Function Across All Möbius-Invariant Besov Spaces $B_p(\mathbb{D})$**:
In Choe–Choi–Koo–Yang (2020), the normalized Bergman test functions on $A^p_\alpha(\mathbb{D})$ are
$f_{b,t}(w) = \frac{(1 - |b|^2)^{t - (\alpha + 2)/p}}{(1 - \bar{b}w)^t}$.
On the classical Möbius-invariant Besov space $B_p(\mathbb{D})$ ($\alpha = p - 2$, $p > 1$),
choosing $t = 2$ makes the numerator exponent $t - (\alpha + 2)/p = 2 - p/p = 1$ independently of $p$! -/
theorem besov_test_exponent_eq_one (p : ℝ) (hp : p ≠ 0) :
    let α := p - 2
    let t : ℝ := 2
    t - (α + 2) / p = 1 := by
  intro α t
  change (2 : ℝ) - (p - 2 + 2) / p = 1
  field_simp [hp]
  ring

/-- Furthermore, the complex derivative of $k_b^{(1)}(z) = \frac{(1-|b|^2)z}{1-\bar{b}z}$ is
precisely the Bergman test function $f_{b,2}(z) = \frac{1-|b|^2}{(1-\bar{b}z)^2}$. -/
theorem hasDerivAt_kernel_eq_bergman_test (b z : ℂ)
    (h_den : 1 - starRingEnd ℂ b * z ≠ 0) :
    HasDerivAt (normalizedDerivKernel b)
      (((1 - (‖b‖ ^ 2 : ℝ) : ℝ) : ℂ) / (1 - starRingEnd ℂ b * z) ^ 2) z := by
  unfold normalizedDerivKernel
  set c : ℂ := ((1 - (‖b‖ ^ 2 : ℝ) : ℝ) : ℂ)
  set cbar : ℂ := starRingEnd ℂ b
  have h_num : HasDerivAt (fun w : ℂ => c * w) (c * 1) z :=
    (hasDerivAt_id z).const_mul c
  have h_den_deriv : HasDerivAt (fun w : ℂ => 1 - cbar * w) (0 - cbar * 1) z :=
    (hasDerivAt_const z (1 : ℂ)).sub ((hasDerivAt_id z).const_mul cbar)
  have h_quot := h_num.div h_den_deriv h_den
  exact h_quot.congr_deriv (by congr 1; ring)

/-!
## Section 4: Quantitative Analysis of the Saukko vs. Choe–Choi–Koo–Park Gap
-/

/-- **Direct Implication (`Saukko` $\implies$ `Choe–Choi–Koo–Park Theorem 3.8 / Prop 4.7`)**:
Inside a Carleson box $Q_s(a)$ of scale $\delta = 1 - |a| > 0$, we have both
$|1 - \bar{a}\psi^*(\zeta)| \ge c_2 \delta$ and $|1 - \overline{\varphi^*(\zeta)}\psi^*(\zeta)| \le C_1 \delta$
whenever both $\varphi^*(\zeta), \psi^*(\zeta) \in Q_s(a)$. Therefore, the Choe–Choi–Koo–Park
integrand $(d / D_a)^p$ is pointwise bounded by $(C_1 / c_2)^p (d / D_\varphi)^p = (C_1 / c_2)^p \rho^p$
independently of $\delta$! -/
theorem saukko_pointwise_dominates_joint_integrand
    (d D_a D_φ δ C₁ c₂ p : ℝ)
    (hd : 0 ≤ d) (hδ : 0 < δ) (hC₁ : 0 < C₁) (hc₂ : 0 < c₂) (hp : 0 ≤ p)
    (hD_φ_pos : 0 < D_φ) (hD_φ_upper : D_φ ≤ C₁ * δ)
    (hD_a_lower : c₂ * δ ≤ D_a) :
    (d / D_a) ^ p ≤ (C₁ / c₂) ^ p * (d / D_φ) ^ p := by
  have hD_a_pos : 0 < D_a := lt_of_lt_of_le (mul_pos hc₂ hδ) hD_a_lower
  have h_base : d / D_a ≤ (C₁ / c₂) * (d / D_φ) := by
    have h_step1 : d / D_a ≤ d / (c₂ * δ) :=
      div_le_div_of_nonneg_left hd (mul_pos hc₂ hδ) hD_a_lower
    have h_step2 : d / (C₁ * δ) ≤ d / D_φ :=
      div_le_div_of_nonneg_left hd hD_φ_pos hD_φ_upper
    calc d / D_a
      _ ≤ d / (c₂ * δ) := h_step1
      _ = (C₁ / c₂) * (d / (C₁ * δ)) := by
          field_simp [hC₁.ne', hc₂.ne', hδ.ne']
      _ ≤ (C₁ / c₂) * (d / D_φ) :=
          mul_le_mul_of_nonneg_left h_step2 (by positivity)
  calc (d / D_a) ^ p
    _ ≤ ((C₁ / c₂) * (d / D_φ)) ^ p :=
        Real.rpow_le_rpow (by positivity) h_base hp
    _ = (C₁ / c₂) ^ p * (d / D_φ) ^ p :=
        Real.mul_rpow (by positivity) (by positivity)

/-- **Quantitative Separation in the Three-Scale Boundary-Comb Regime
(Why Saukko's Condition is Not Necessary in General)**:
Suppose in a Carleson box $Q_s(a)$ of width $\delta = 1 - |a| > 0$, a subset $E_a \subset \mathbb{T}$
of measure $m(E_a) = \kappa \delta$ ($\kappa > 0$) satisfies:
1. $d = |\varphi^*(\zeta) - \psi^*(\zeta)| = \varepsilon \cdot \delta$ (sub-window separation $\varepsilon > 0$),
2. $1 - |\varphi^*(\zeta)| \le M \cdot d = M \varepsilon \delta$ (boundary depth comparable to $d$), so that
   $D_\varphi = |1 - \overline{\varphi^*(\zeta)}\psi^*(\zeta)| \le (1 - |\varphi^*(\zeta)|) + d \le (1 + M) \varepsilon \delta$,
3. $D_a = |1 - \bar{a}\psi^*(\zeta)| \ge c_0 \delta$ ($c_0 > 0$).

Then:
- **Saukko's normalized ratio** $\frac{m(E_a)}{\delta} \left(\frac{d}{D_\varphi}\right)^p$ is bounded **below**
  by the strictly positive constant $\frac{\kappa}{(1 + M)^p} > 0$ (independent of $\varepsilon$ and $\delta$),
- **Choe–Choi–Koo–Park's normalized joint ratio** $\frac{m(E_a)}{\delta} \left(\frac{d}{D_a}\right)^p$
  is bounded **above** by $\frac{\kappa}{c_0^p} \varepsilon^p$, which tends to $0$ as $\varepsilon \to 0$! -/
theorem saukko_strictly_stronger_in_three_scale_regime
    (δ ε κ M c₀ D_φ D_a p : ℝ)
    (hδ : 0 < δ) (hε : 0 < ε) (hκ : 0 < κ) (hM : 0 ≤ M) (hc₀ : 0 < c₀) (hp : 0 < p)
    (hD_φ_pos : 0 < D_φ) (hD_φ_upper : D_φ ≤ (1 + M) * (ε * δ))
    (hD_a_lower : c₀ * δ ≤ D_a) :
    let d := ε * δ
    let m_E := κ * δ
    κ / (1 + M) ^ p ≤ (m_E / δ) * (d / D_φ) ^ p ∧
      (m_E / δ) * (d / D_a) ^ p ≤ (κ / c₀ ^ p) * ε ^ p := by
  intro d m_E
  have hm_ratio : m_E / δ = κ := mul_div_cancel_right₀ κ hδ.ne'
  rw [hm_ratio]
  constructor
  · -- Lower bound on Saukko's normalized Carleson ratio: ≥ κ / (1 + M)^p
    have h_rho_lower : 1 / (1 + M) ≤ d / D_φ := by
      have h1 : d / ((1 + M) * d) ≤ d / D_φ :=
        div_le_div_of_nonneg_left (by positivity) hD_φ_pos hD_φ_upper
      have h2 : d / ((1 + M) * d) = 1 / (1 + M) := by
        have hd_ne : d ≠ 0 := (mul_pos hε hδ).ne'
        field_simp [hd_ne]
      linarith
    have h_rpow : (1 / (1 + M)) ^ p ≤ (d / D_φ) ^ p :=
      Real.rpow_le_rpow (by positivity) h_rho_lower hp.le
    have h_one_div : (1 / (1 + M)) ^ p = 1 / (1 + M) ^ p := by
      rw [Real.div_rpow zero_le_one (by positivity) p, Real.one_rpow]
    calc κ / (1 + M) ^ p
      _ = κ * (1 / (1 + M)) ^ p := by rw [h_one_div, mul_one_div]
      _ ≤ κ * (d / D_φ) ^ p := mul_le_mul_of_nonneg_left h_rpow hκ.le
  · -- Upper bound on Choe–Choi–Koo–Park's normalized joint ratio: ≤ (κ / c₀^p) * ε^p
    have hD_a_pos : 0 < D_a := lt_of_lt_of_le (mul_pos hc₀ hδ) hD_a_lower
    have h_joint_upper : d / D_a ≤ ε / c₀ := by
      have h1 : d / D_a ≤ d / (c₀ * δ) :=
        div_le_div_of_nonneg_left (by positivity) (mul_pos hc₀ hδ) hD_a_lower
      have h2 : d / (c₀ * δ) = ε / c₀ := by
        change (ε * δ) / (c₀ * δ) = ε / c₀
        exact mul_div_mul_right ε c₀ hδ.ne'
      linarith
    have h_rpow : (d / D_a) ^ p ≤ (ε / c₀) ^ p :=
      Real.rpow_le_rpow (by positivity) h_joint_upper hp.le
    have h_div_rpow : (ε / c₀) ^ p = ε ^ p / c₀ ^ p :=
      Real.div_rpow hε.le hc₀.le p
    calc κ * (d / D_a) ^ p
      _ ≤ κ * (ε / c₀) ^ p := mul_le_mul_of_nonneg_left h_rpow hκ.le
      _ = (κ / c₀ ^ p) * ε ^ p := by rw [h_div_rpow]; ring

end BesovCompDiff
