/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Sarason.Definitions
import Sarason.Chapter1
import Sarason.Chapter2
import Sarason.Chapter3

/-!
# Sarason - Chapter 4: Elementary Functions

Formalization of Section IV of Donald Sarason's "Notes on Complex Function Theory".
Focus:
- §IV.1 Definition of $e^z$ (`exp_Sarason`)
- §IV.2 Law of Exponents (`IV_2_law_of_exponents`)
- §IV.3 $e^z$ is Holomorphic in the Weierstrass `_eps` sense (`IV_3_hasDerivAt_exp_eps`, `IV_3_holomorphicOn_exp_eps`)
- §IV.4 Periodicity of $e^z$ (`IV_4_exp_eq_one_iff`, `IV_4_exp_eq_exp_iff`, `IV_4_is_period_of_exp_iff`)
- §IV.5 $e^z$ as a Map: Punctured-plane range, vertical lines to circles, horizontal strip injectivity
- §IV.6–§IV.7 Hyperbolic Functions $\cosh z, \sinh z$ and Complete Zero Characterizations
- §IV.8 Trigonometric Functions $\cos z, \sin z$, Holomorphicity, and Complete Zero Characterizations
- §IV.9–§IV.11 Logarithms, Branches on the Slit Plane, and `_eps` Holomorphicity of $\operatorname{Log} z$

Credit: Donald Sarason
-/

open Complex Filter Metric Sarason Sarason.Ch1 Sarason.Ch2 Sarason.Ch3
open scoped Real Topology

noncomputable section

namespace Sarason.Ch4

/-!
  ## §IV.1 Definition of $e^z$
-/

/--
  §IV.1 Sarason's Euler-formula definition of the complex exponential function:
  For $z = x + i y \in \mathbb{C}$, $e^z := e^x (\cos y + i \sin y)$.
-/
def exp_Sarason (z : ℂ) : ℂ :=
  ((Real.exp z.re * Real.cos z.im : ℝ) : ℂ) + ((Real.exp z.re * Real.sin z.im : ℝ) : ℂ) * I

@[simp]
lemma exp_Sarason_re (z : ℂ) : (exp_Sarason z).re = Real.exp z.re * Real.cos z.im := by
{
  unfold exp_Sarason
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring
}

@[simp]
lemma exp_Sarason_im (z : ℂ) : (exp_Sarason z).im = Real.exp z.re * Real.sin z.im := by
{
  unfold exp_Sarason
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring
}

/--
  §IV.1 Agreement between Sarason's explicit definition `exp_Sarason` and Mathlib's `Complex.exp`.
-/
theorem exp_Sarason_eq_exp (z : ℂ) : exp_Sarason z = Complex.exp z := by
{
  apply Complex.ext
  · rw [exp_Sarason_re, Complex.exp_re]
  · rw [exp_Sarason_im, Complex.exp_im]
}

/--
  §IV.1 Restriction of `exp_Sarason` to the real axis agrees with the real exponential `Real.exp`.
-/
lemma exp_Sarason_ofReal (x : ℝ) : exp_Sarason (x : ℂ) = (Real.exp x : ℂ) := by
{
  apply Complex.ext
  · rw [exp_Sarason_re, Complex.ofReal_re, Complex.ofReal_re, Complex.ofReal_im,
      Real.cos_zero, mul_one]
  · rw [exp_Sarason_im, Complex.ofReal_im, Complex.ofReal_im, Real.sin_zero, mul_zero]
}

/--
  §IV.1 Euler's formula on the imaginary axis: $e^{i y} = \cos y + i \sin y$.
-/
lemma exp_Sarason_mul_I (y : ℝ) :
    exp_Sarason ((y : ℂ) * I) = (Real.cos y : ℂ) + (Real.sin y : ℂ) * I := by
{
  have h_re : ((y : ℂ) * I).re = 0 := by simp
  have h_im : ((y : ℂ) * I).im = y := by simp
  apply Complex.ext
  · rw [exp_Sarason_re, h_re, h_im, Real.exp_zero, one_mul]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  · rw [exp_Sarason_im, h_re, h_im, Real.exp_zero, one_mul]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
}

/--
  §IV.1 Modulus of $e^z$: $\|e^z\| = e^{\operatorname{Re} z}$, proved directly from $\cos^2 y + \sin^2 y = 1$.
-/
theorem norm_exp_Sarason (z : ℂ) : ‖exp_Sarason z‖ = Real.exp z.re := by
{
  have h_sq : ‖exp_Sarason z‖ ^ 2 = (Real.exp z.re) ^ 2 := by
  {
    rw [Complex.sq_norm, Complex.normSq_apply, exp_Sarason_re, exp_Sarason_im]
    calc (Real.exp z.re * Real.cos z.im) * (Real.exp z.re * Real.cos z.im) +
          (Real.exp z.re * Real.sin z.im) * (Real.exp z.re * Real.sin z.im)
        = (Real.exp z.re) ^ 2 * (Real.cos z.im ^ 2 + Real.sin z.im ^ 2) := by ring
      _ = (Real.exp z.re) ^ 2 * 1 := by rw [Real.cos_sq_add_sin_sq]
      _ = (Real.exp z.re) ^ 2 := by ring
  }
  have h_sqrt := congrArg Real.sqrt h_sq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq (Real.exp_pos z.re).le] at h_sqrt
}

/--
  §IV.1 The complex exponential never vanishes: $e^z \neq 0$ for all $z \in \mathbb{C}$.
-/
theorem exp_Sarason_ne_zero (z : ℂ) : exp_Sarason z ≠ 0 := by
{
  intro h0
  have h_norm := norm_exp_Sarason z
  rw [h0, norm_zero] at h_norm
  exact (Real.exp_pos z.re).ne h_norm
}

/--
  §IV.1 Conjugation symmetry of $e^z$: $e^{\bar{z}} = \overline{e^z}$.
-/
lemma exp_Sarason_conj (z : ℂ) : exp_Sarason (star z) = star (exp_Sarason z) := by
{
  apply Complex.ext
  · simp [exp_Sarason_re]
  · simp [exp_Sarason_im]
}

/-!
  ## §IV.2 Law of Exponents
-/

/--
  §IV.2 **Law of Exponents (`exp_Sarason (z₁ + z₂) = exp_Sarason z₁ * exp_Sarason z₂`)**:
  Proved directly from `Real.exp_add` and the trigonometric addition formulas `Real.cos_add`
  and `Real.sin_add`, following Sarason §IV.2.
-/
theorem IV_2_law_of_exponents (z₁ z₂ : ℂ) :
    exp_Sarason (z₁ + z₂) = exp_Sarason z₁ * exp_Sarason z₂ := by
{
  apply Complex.ext
  · simp only [exp_Sarason_re, exp_Sarason_im, Complex.add_re, Complex.add_im, Complex.mul_re]
    rw [Real.exp_add, Real.cos_add]
    ring
  · simp only [exp_Sarason_re, exp_Sarason_im, Complex.add_re, Complex.add_im, Complex.mul_im]
    rw [Real.exp_add, Real.sin_add]
    ring
}

@[simp]
lemma exp_Sarason_zero : exp_Sarason 0 = 1 := by
{
  apply Complex.ext <;> simp [exp_Sarason_re, exp_Sarason_im]
}

/--
  §IV.2 Reciprocal identity: $e^{-z} = (e^z)^{-1}$.
-/
lemma exp_Sarason_neg (z : ℂ) : exp_Sarason (-z) = (exp_Sarason z)⁻¹ := by
{
  have h_prod : exp_Sarason (-z) * exp_Sarason z = 1 := by
  {
    rw [← IV_2_law_of_exponents, neg_add_cancel, exp_Sarason_zero]
  }
  exact eq_inv_of_mul_eq_one_left h_prod
}

/--
  §IV.2 Quotient law of exponents: $e^{z_1 - z_2} = e^{z_1} / e^{z_2}$.
-/
lemma exp_Sarason_sub (z₁ z₂ : ℂ) :
    exp_Sarason (z₁ - z₂) = exp_Sarason z₁ / exp_Sarason z₂ := by
{
  rw [sub_eq_add_neg, IV_2_law_of_exponents, exp_Sarason_neg, div_eq_mul_inv]
}

/--
  §IV.2 Natural-number power / De Moivre law: $e^{n z} = (e^z)^n$ for all $n \in \mathbb{N}$.
-/
lemma exp_Sarason_nat_mul (n : ℕ) (z : ℂ) :
    exp_Sarason ((n : ℂ) * z) = (exp_Sarason z) ^ n := by
{
  induction n with
  | zero =>
    simp [exp_Sarason_zero]
  | succ k ih =>
    push_cast
    rw [add_mul, one_mul, IV_2_law_of_exponents, ih, pow_succ]
}

/-!
  ## §IV.3 $e^z$ is Holomorphic
-/

/--
  §IV.3 Real $x$-partial derivative of $u(x, y) = \operatorname{Re}(e^z) = e^x \cos y$ in `_eps` form.
-/
lemma exp_Sarason_re_hasPartialDerivX_eps (z : ℂ) :
    HasPartialDerivX_C_to_R_eps (fun w => (exp_Sarason w).re) ((exp_Sarason z).re) z := by
{
  rw [← hasPartialDerivX_iff_eps]
  have h_fn : (fun x : ℝ => (exp_Sarason ((x : ℂ) + (z.im : ℂ) * I)).re) =
      fun x : ℝ => Real.exp x * Real.cos z.im := by
  {
    ext x
    simp [exp_Sarason_re]
  }
  rw [h_fn, exp_Sarason_re]
  exact (Real.hasDerivAt_exp z.re).mul_const (Real.cos z.im)
}

/--
  §IV.3 Real $y$-partial derivative of $u(x, y) = \operatorname{Re}(e^z) = e^x \cos y$ in `_eps` form.
-/
lemma exp_Sarason_re_hasPartialDerivY_eps (z : ℂ) :
    HasPartialDerivY_C_to_R_eps (fun w => (exp_Sarason w).re) (-(exp_Sarason z).im) z := by
{
  rw [← hasPartialDerivY_iff_eps]
  have h_fn : (fun y : ℝ => (exp_Sarason ((z.re : ℂ) + (y : ℂ) * I)).re) =
      fun y : ℝ => Real.exp z.re * Real.cos y := by
  {
    ext y
    simp [exp_Sarason_re]
  }
  rw [h_fn, exp_Sarason_im]
  have h_d := (Real.hasDerivAt_cos z.im).const_mul (Real.exp z.re)
  rwa [mul_neg] at h_d
}

/--
  §IV.3 Real $x$-partial derivative of $v(x, y) = \operatorname{Im}(e^z) = e^x \sin y$ in `_eps` form.
-/
lemma exp_Sarason_im_hasPartialDerivX_eps (z : ℂ) :
    HasPartialDerivX_C_to_R_eps (fun w => (exp_Sarason w).im) ((exp_Sarason z).im) z := by
{
  rw [← hasPartialDerivX_iff_eps]
  have h_fn : (fun x : ℝ => (exp_Sarason ((x : ℂ) + (z.im : ℂ) * I)).im) =
      fun x : ℝ => Real.exp x * Real.sin z.im := by
  {
    ext x
    simp [exp_Sarason_im]
  }
  rw [h_fn, exp_Sarason_im]
  exact (Real.hasDerivAt_exp z.re).mul_const (Real.sin z.im)
}

/--
  §IV.3 Real $y$-partial derivative of $v(x, y) = \operatorname{Im}(e^z) = e^x \sin y$ in `_eps` form.
-/
lemma exp_Sarason_im_hasPartialDerivY_eps (z : ℂ) :
    HasPartialDerivY_C_to_R_eps (fun w => (exp_Sarason w).im) ((exp_Sarason z).re) z := by
{
  rw [← hasPartialDerivY_iff_eps]
  have h_fn : (fun y : ℝ => (exp_Sarason ((z.re : ℂ) + (y : ℂ) * I)).im) =
      fun y : ℝ => Real.exp z.re * Real.sin y := by
  {
    ext y
    simp [exp_Sarason_im]
  }
  rw [h_fn, exp_Sarason_re]
  exact (Real.hasDerivAt_sin z.im).const_mul (Real.exp z.re)
}

/--
  §IV.3 **Theorem IV.3 ($e^z$ has Weierstrass Complex Derivative $e^z$ Everywhere)**:
  For every $z \in \mathbb{C}$, `HasDerivAt_eps exp_Sarason (exp_Sarason z) z`.
-/
theorem IV_3_hasDerivAt_exp_eps (z : ℂ) :
    HasDerivAt_eps exp_Sarason (exp_Sarason z) z := by
{
  rw [← hasDerivAt_iff_eps]
  have h_eq : exp_Sarason = Complex.exp := funext exp_Sarason_eq_exp
  rw [h_eq]
  exact Complex.hasDerivAt_exp z
}

/--
  §IV.3 $e^z$ is an entire holomorphic function (`HolomorphicOn_eps exp_Sarason ℂ_set`).
-/
theorem IV_3_holomorphicOn_exp_eps : HolomorphicOn_eps exp_Sarason ℂ_set := by
{
  intro z _
  exact ⟨exp_Sarason z, IV_3_hasDerivAt_exp_eps z⟩
}

/--
  §IV.3 Value of `deriv_eps exp_Sarason` at any $z \in \mathbb{C}$ equals `exp_Sarason z`.
-/
theorem IV_3_deriv_exp_eps (z : ℂ) (hd : DifferentiableAt_eps exp_Sarason z) :
    deriv_eps exp_Sarason z hd = exp_Sarason z := by
{
  rw [← deriv_eq_deriv_eps]
  exact ((hasDerivAt_iff_eps _ _ z).mpr (IV_3_hasDerivAt_exp_eps z)).deriv
}

/-!
  ## §IV.4 Periodicity
-/

/--
  §IV.4 $2\pi i$ is a period of $e^z$: $e^{z + 2\pi i} = e^z$.
-/
lemma exp_Sarason_add_two_pi_I (z : ℂ) :
    exp_Sarason (z + 2 * Real.pi * I) = exp_Sarason z := by
{
  rw [IV_2_law_of_exponents]
  have h_per : exp_Sarason (2 * Real.pi * I) = 1 := by
  {
    have h_cast : (2 * Real.pi * I : ℂ) = ((2 * Real.pi : ℝ) : ℂ) * I := by push_cast; ring
    rw [h_cast, exp_Sarason_mul_I]
    simp [Real.cos_two_pi, Real.sin_two_pi]
  }
  rw [h_per, mul_one]
}

/--
  §IV.4 **Characterization of Solutions to $e^z = 1$**:
  $e^z = 1$ if and only if $z = 2\pi i k$ for some integer $k \in \mathbb{Z}$.
-/
theorem IV_4_exp_eq_one_iff (z : ℂ) :
    exp_Sarason z = 1 ↔ ∃ k : ℤ, z = (k : ℂ) * (2 * Real.pi * I) := by
{
  rw [exp_Sarason_eq_exp, Complex.exp_eq_one_iff]
}

/--
  §IV.4 **Equality Criterion for $e^{z_1} = e^{z_2}$**:
  $e^{z_1} = e^{z_2}$ if and only if $z_1 = z_2 + 2\pi i k$ for some integer $k \in \mathbb{Z}$.
-/
theorem IV_4_exp_eq_exp_iff (z₁ z₂ : ℂ) :
    exp_Sarason z₁ = exp_Sarason z₂ ↔ ∃ k : ℤ, z₁ = z₂ + (k : ℂ) * (2 * Real.pi * I) := by
{
  have h_div : exp_Sarason z₁ = exp_Sarason z₂ ↔ exp_Sarason (z₁ - z₂) = 1 := by
  {
    rw [exp_Sarason_sub, div_eq_one_iff_eq (exp_Sarason_ne_zero z₂)]
  }
  rw [h_div, IV_4_exp_eq_one_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, eq_add_of_sub_eq' hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩
}

/--
  §IV.4 **Complete Characterization of All Periods of $e^z$**:
  A complex number $p \in \mathbb{C}$ satisfies $e^{z + p} = e^z$ for all $z \in \mathbb{C}$
  if and only if $p = 2\pi i k$ for some $k \in \mathbb{Z}$.
-/
theorem IV_4_is_period_of_exp_iff (p : ℂ) :
    (∀ z : ℂ, exp_Sarason (z + p) = exp_Sarason z) ↔ ∃ k : ℤ, p = (k : ℂ) * (2 * Real.pi * I) := by
{
  constructor
  · intro h_all
    have h0 := h_all 0
    rw [zero_add, exp_Sarason_zero] at h0
    exact (IV_4_exp_eq_one_iff p).mp h0
  · rintro ⟨k, rfl⟩ z
    rw [IV_2_law_of_exponents, (IV_4_exp_eq_one_iff _).mpr ⟨k, rfl⟩, mul_one]
}

/-!
  ## §IV.5 $e^z$ as a Map
-/

/--
  §IV.5 Half-open horizontal strip $\{z \in \mathbb{C} : y_0 < \operatorname{Im} z \le y_0 + 2\pi\}$
  of height $2\pi$.
-/
def horizontalStrip (y₀ : ℝ) : Set ℂ :=
  {z : ℂ | y₀ < z.im ∧ z.im ≤ y₀ + 2 * Real.pi}

/--
  §IV.5 Open horizontal strip $\{z \in \mathbb{C} : y_0 < \operatorname{Im} z < y_0 + 2\pi\}$
  of height $2\pi$.
-/
def openHorizontalStrip (y₀ : ℝ) : Set ℂ :=
  {z : ℂ | y₀ < z.im ∧ z.im < y₀ + 2 * Real.pi}

/--
  §IV.5 **Range of $e^z$**: `exp_Sarason` maps $\mathbb{C}$ onto the punctured plane $\mathbb{C} \setminus \{0\}$.
-/
theorem IV_5_range_exp_Sarason : Set.range exp_Sarason = {w : ℂ | w ≠ 0} := by
{
  ext w
  simp only [Set.mem_range, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, rfl⟩
    exact exp_Sarason_ne_zero z
  · intro hw
    refine ⟨(Real.log ‖w‖ : ℂ) + (Complex.arg w : ℂ) * I, ?_⟩
    rw [exp_Sarason_eq_exp]
    exact Complex.exp_log hw
}

/--
  §IV.5 Vertical lines $\{z \in \mathbb{C} : \operatorname{Re} z = x_0\}$ map onto circles
  $\{w \in \mathbb{C} : \|w\| = e^{x_0}\}$ centered at the origin.
-/
theorem IV_5_image_vertical_line (x₀ : ℝ) :
    exp_Sarason '' {z : ℂ | z.re = x₀} = {w : ℂ | ‖w‖ = Real.exp x₀} := by
{
  ext w
  simp only [Set.mem_image, Set.mem_setOf_eq]
  constructor
  · rintro ⟨z, rfl, rfl⟩
    exact norm_exp_Sarason z
  · intro hw
    have hw_ne : w ≠ 0 := by
    {
      intro h0
      rw [h0, norm_zero] at hw
      exact (Real.exp_pos x₀).ne' hw.symm
    }
    refine ⟨(x₀ : ℂ) + (Complex.arg w : ℂ) * I, by simp, ?_⟩
    have h_log : Real.log ‖w‖ = x₀ := by rw [hw, Real.log_exp]
    rw [← h_log, exp_Sarason_eq_exp]
    exact Complex.exp_log hw_ne
}

/--
  §IV.5 **Injectivity of $e^z$ on Any Horizontal Strip of Height $2\pi$**:
  For every $y_0 \in \mathbb{R}$, `exp_Sarason` is injective on `horizontalStrip y₀`.
-/
theorem IV_5_injOn_horizontalStrip (y₀ : ℝ) :
    Set.InjOn exp_Sarason (horizontalStrip y₀) := by
{
  intro z₁ hz₁ z₂ hz₂ h_eq
  rcases (IV_4_exp_eq_exp_iff z₁ z₂).mp h_eq with ⟨k, hk⟩
  have h_im : z₁.im = z₂.im + (k : ℝ) * (2 * Real.pi) := by
  {
    have him := congrArg Complex.im hk
    simpa [Complex.add_im, Complex.mul_im] using him
  }
  have h_lt1 : (k : ℝ) * (2 * Real.pi) < 1 * (2 * Real.pi) := by linarith [hz₁.2, hz₂.1]
  have h_gt1 : (-1 : ℝ) * (2 * Real.pi) < (k : ℝ) * (2 * Real.pi) := by linarith [hz₁.1, hz₂.2]
  have hk_upper : (k : ℝ) < (1 : ℤ) := by
  {
    simpa using lt_of_mul_lt_mul_right h_lt1 Real.two_pi_pos.le
  }
  have hk_lower : ((-1 : ℤ) : ℝ) < (k : ℝ) := by
  {
    simpa using lt_of_mul_lt_mul_right h_gt1 Real.two_pi_pos.le
  }
  have hk_le : k ≤ 0 := Int.le_of_lt_add_one (Int.cast_lt.mp hk_upper)
  have hk_ge : 0 ≤ k := Int.le_of_lt_add_one (by {
    have h' : -1 + 1 ≤ k := Int.add_one_le_of_lt (Int.cast_lt.mp hk_lower)
    linarith
  })
  have hk0 : k = 0 := le_antisymm hk_le hk_ge
  rw [hk, hk0]
  simp
}

/-!
  ## §IV.6–§IV.7 Hyperbolic Functions and Zeros of $\cosh z$ and $\sinh z$
-/

/-- §IV.6 Complex hyperbolic cosine: $\cosh z := (e^z + e^{-z}) / 2$. -/
def cosh_Sarason (z : ℂ) : ℂ :=
  (exp_Sarason z + exp_Sarason (-z)) / 2

/-- §IV.6 Complex hyperbolic sine: $\sinh z := (e^z - e^{-z}) / 2$. -/
def sinh_Sarason (z : ℂ) : ℂ :=
  (exp_Sarason z - exp_Sarason (-z)) / 2

lemma cosh_Sarason_eq_cosh (z : ℂ) : cosh_Sarason z = Complex.cosh z := by
{
  unfold cosh_Sarason Complex.cosh
  rw [exp_Sarason_eq_exp, exp_Sarason_eq_exp]
}

lemma sinh_Sarason_eq_sinh (z : ℂ) : sinh_Sarason z = Complex.sinh z := by
{
  unfold sinh_Sarason Complex.sinh
  rw [exp_Sarason_eq_exp, exp_Sarason_eq_exp]
}

lemma cosh_Sarason_even (z : ℂ) : cosh_Sarason (-z) = cosh_Sarason z := by
{
  unfold cosh_Sarason
  rw [neg_neg, add_comm]
}

lemma sinh_Sarason_odd (z : ℂ) : sinh_Sarason (-z) = -sinh_Sarason z := by
{
  unfold sinh_Sarason
  rw [neg_neg]
  ring
}

/--
  §IV.6 Fundamental hyperbolic identity: $\cosh^2 z - \sinh^2 z = 1$.
-/
theorem IV_6_cosh_sq_sub_sinh_sq (z : ℂ) :
    cosh_Sarason z ^ 2 - sinh_Sarason z ^ 2 = 1 := by
{
  unfold cosh_Sarason sinh_Sarason
  have h_prod : exp_Sarason z * exp_Sarason (-z) = 1 := by
  {
    rw [← IV_2_law_of_exponents, add_neg_cancel, exp_Sarason_zero]
  }
  linear_combination h_prod
}

/--
  §IV.6 Weierstrass `_eps` derivative of $\cosh z$: $\frac{d}{dz} \cosh z = \sinh z$.
-/
theorem IV_6_hasDerivAt_cosh_eps (z : ℂ) :
    HasDerivAt_eps cosh_Sarason (sinh_Sarason z) z := by
{
  rw [← hasDerivAt_iff_eps]
  have h_fn : cosh_Sarason = fun w : ℂ => (Complex.exp w + Complex.exp (-w)) / 2 := by
  {
    ext w
    unfold cosh_Sarason
    rw [exp_Sarason_eq_exp, exp_Sarason_eq_exp]
  }
  rw [h_fn]
  have h_neg : _root_.HasDerivAt (fun w : ℂ => Complex.exp (-w)) (-Complex.exp (-z)) z := by
  {
    simpa [Function.comp_def] using (Complex.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)
  }
  have h_d := ((Complex.hasDerivAt_exp z).add h_neg).div_const (2 : ℂ)
  have h_val : (Complex.exp z + -Complex.exp (-z)) / 2 = sinh_Sarason z := by
  {
    unfold sinh_Sarason
    rw [exp_Sarason_eq_exp, exp_Sarason_eq_exp]
    ring
  }
  rwa [h_val] at h_d
}

/--
  §IV.6 Weierstrass `_eps` derivative of $\sinh z$: $\frac{d}{dz} \sinh z = \cosh z$.
-/
theorem IV_6_hasDerivAt_sinh_eps (z : ℂ) :
    HasDerivAt_eps sinh_Sarason (cosh_Sarason z) z := by
{
  rw [← hasDerivAt_iff_eps]
  have h_fn : sinh_Sarason = fun w : ℂ => (Complex.exp w - Complex.exp (-w)) / 2 := by
  {
    ext w
    unfold sinh_Sarason
    rw [exp_Sarason_eq_exp, exp_Sarason_eq_exp]
  }
  rw [h_fn]
  have h_neg : _root_.HasDerivAt (fun w : ℂ => Complex.exp (-w)) (-Complex.exp (-z)) z := by
  {
    simpa [Function.comp_def] using (Complex.hasDerivAt_exp (-z)).comp z (hasDerivAt_neg z)
  }
  have h_d := ((Complex.hasDerivAt_exp z).sub h_neg).div_const (2 : ℂ)
  have h_val : (Complex.exp z - -Complex.exp (-z)) / 2 = cosh_Sarason z := by
  {
    unfold cosh_Sarason
    rw [exp_Sarason_eq_exp, exp_Sarason_eq_exp]
    ring
  }
  rwa [h_val] at h_d
}

/--
  §IV.7 **Zeros of $\sinh z$**: $\sinh z = 0$ if and only if $z = k \pi i$ for some $k \in \mathbb{Z}$.
-/
theorem IV_7_sinh_eq_zero_iff (z : ℂ) :
    sinh_Sarason z = 0 ↔ ∃ k : ℤ, z = (k : ℂ) * (Real.pi * I) := by
{
  unfold sinh_Sarason
  have h_div : (exp_Sarason z - exp_Sarason (-z)) / 2 = 0 ↔ exp_Sarason z = exp_Sarason (-z) := by
  {
    rw [div_eq_zero_iff, sub_eq_zero]
    exact ⟨fun h => h.resolve_right two_ne_zero, fun h => Or.inl h⟩
  }
  rw [h_div, IV_4_exp_eq_exp_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linear_combination (1 / 2 : ℂ) * hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩
}

/--
  §IV.7 **Zeros of $\cosh z$**: $\cosh z = 0$ if and only if $z = (k + 1/2) \pi i$ for some $k \in \mathbb{Z}$.
-/
theorem IV_7_cosh_eq_zero_iff (z : ℂ) :
    cosh_Sarason z = 0 ↔ ∃ k : ℤ, z = ((k : ℂ) + 1 / 2) * (Real.pi * I) := by
{
  unfold cosh_Sarason
  have h_neg_one : -1 = exp_Sarason (Real.pi * I) := by
  {
    rw [exp_Sarason_mul_I]
    simp [Real.cos_pi, Real.sin_pi]
  }
  have h_step : (exp_Sarason z + exp_Sarason (-z)) / 2 = 0 ↔
      exp_Sarason z = exp_Sarason (-z + Real.pi * I) := by
  {
    rw [div_eq_zero_iff, IV_2_law_of_exponents, ← h_neg_one]
    constructor
    · intro h
      have h0 := h.resolve_right two_ne_zero
      linear_combination h0
    · intro h
      left
      linear_combination h
  }
  rw [h_step, IV_4_exp_eq_exp_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, by linear_combination (1 / 2 : ℂ) * hk⟩
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩
}

/-!
  ## §IV.8 Trigonometric Functions
-/

/-- §IV.8 Complex cosine defined via Euler's formula: $\cos z := (e^{i z} + e^{-i z}) / 2$. -/
def cos_Sarason (z : ℂ) : ℂ :=
  (exp_Sarason (I * z) + exp_Sarason (-(I * z))) / 2

/-- §IV.8 Complex sine defined via Euler's formula: $\sin z := (e^{i z} - e^{-i z}) / (2 i)$. -/
def sin_Sarason (z : ℂ) : ℂ :=
  (exp_Sarason (I * z) - exp_Sarason (-(I * z))) / (2 * I)

lemma cos_Sarason_eq_cosh_mul_I (z : ℂ) : cos_Sarason z = cosh_Sarason (I * z) := by
{
  rfl
}

lemma sin_Sarason_eq_neg_I_mul_sinh_mul_I (z : ℂ) :
    sin_Sarason z = -I * sinh_Sarason (I * z) := by
{
  unfold sin_Sarason sinh_Sarason
  have h2i : (2 : ℂ) * I ≠ 0 := mul_ne_zero two_ne_zero I_ne_zero
  rw [div_eq_iff h2i]
  calc exp_Sarason (I * z) - exp_Sarason (-(I * z))
      = -(I * I) * (exp_Sarason (I * z) - exp_Sarason (-(I * z))) := by rw [I_mul_I]; ring
    _ = -I * ((exp_Sarason (I * z) - exp_Sarason (-(I * z))) / 2) * (2 * I) := by ring
}

lemma cos_Sarason_eq_cos (z : ℂ) : cos_Sarason z = Complex.cos z := by
{
  have h1 : -z * I = -(I * z) := by ring
  have h2 : z * I = I * z := by ring
  unfold cos_Sarason Complex.cos
  rw [exp_Sarason_eq_exp, exp_Sarason_eq_exp, h1, h2]
}

lemma sin_Sarason_eq_sin (z : ℂ) : sin_Sarason z = Complex.sin z := by
{
  have h1 : -z * I = -(I * z) := by ring
  have h2 : z * I = I * z := by ring
  rw [sin_Sarason_eq_neg_I_mul_sinh_mul_I, sinh_Sarason_eq_sinh]
  unfold Complex.sin Complex.sinh
  rw [h1, h2]
  ring
}

/--
  §IV.8 Complex Pythagorean identity: $\cos^2 z + \sin^2 z = 1$ for all $z \in \mathbb{C}$.
-/
theorem IV_8_cos_sq_add_sin_sq (z : ℂ) :
    cos_Sarason z ^ 2 + sin_Sarason z ^ 2 = 1 := by
{
  rw [cos_Sarason_eq_cosh_mul_I, sin_Sarason_eq_neg_I_mul_sinh_mul_I]
  have hI2 : (-I) ^ 2 = -1 := by
  {
    calc (-I) ^ 2 = I * I := by ring
      _ = -1 := I_mul_I
  }
  calc cosh_Sarason (I * z) ^ 2 + (-I * sinh_Sarason (I * z)) ^ 2
      = cosh_Sarason (I * z) ^ 2 + (-I) ^ 2 * sinh_Sarason (I * z) ^ 2 := by ring
    _ = cosh_Sarason (I * z) ^ 2 - sinh_Sarason (I * z) ^ 2 := by rw [hI2]; ring
    _ = 1 := IV_6_cosh_sq_sub_sinh_sq (I * z)
}

/--
  §IV.8 Weierstrass `_eps` derivative of $\cos z$: $\frac{d}{dz} \cos z = -\sin z$.
-/
theorem IV_8_hasDerivAt_cos_eps (z : ℂ) :
    HasDerivAt_eps cos_Sarason (-sin_Sarason z) z := by
{
  rw [← hasDerivAt_iff_eps]
  have h_eq : cos_Sarason = Complex.cos := funext cos_Sarason_eq_cos
  rw [h_eq, sin_Sarason_eq_sin]
  exact Complex.hasDerivAt_cos z
}

/--
  §IV.8 Weierstrass `_eps` derivative of $\sin z$: $\frac{d}{dz} \sin z = \cos z$.
-/
theorem IV_8_hasDerivAt_sin_eps (z : ℂ) :
    HasDerivAt_eps sin_Sarason (cos_Sarason z) z := by
{
  rw [← hasDerivAt_iff_eps]
  have h_eq : sin_Sarason = Complex.sin := funext sin_Sarason_eq_sin
  rw [h_eq, cos_Sarason_eq_cos]
  exact Complex.hasDerivAt_sin z
}

/--
  §IV.8 **Zeros of $\sin z$ in $\mathbb{C}$**:
  $\sin z = 0$ if and only if $z = k \pi$ for some $k \in \mathbb{Z}$ (all zeros are real).
-/
theorem IV_8_sin_eq_zero_iff (z : ℂ) :
    sin_Sarason z = 0 ↔ ∃ k : ℤ, z = (k : ℂ) * Real.pi := by
{
  rw [sin_Sarason_eq_neg_I_mul_sinh_mul_I, mul_eq_zero,
    or_iff_right (neg_ne_zero.mpr I_ne_zero), IV_7_sinh_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, mul_left_cancel₀ I_ne_zero ?_⟩
    linear_combination hk
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩
}

/--
  §IV.8 **Zeros of $\cos z$ in $\mathbb{C}$**:
  $\cos z = 0$ if and only if $z = (k + 1/2) \pi$ for some $k \in \mathbb{Z}$ (all zeros are real).
-/
theorem IV_8_cos_eq_zero_iff (z : ℂ) :
    cos_Sarason z = 0 ↔ ∃ k : ℤ, z = ((k : ℂ) + 1 / 2) * Real.pi := by
{
  rw [cos_Sarason_eq_cosh_mul_I, IV_7_cosh_eq_zero_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, mul_left_cancel₀ I_ne_zero ?_⟩
    linear_combination hk
  · rintro ⟨k, rfl⟩
    exact ⟨k, by ring⟩
}

/-!
  ## §IV.9–§IV.11 Logarithms, Branches on the Slit Plane, and Holomorphicity of $\operatorname{Log} z$
-/

/--
  §IV.9 Multi-valued complex logarithm relation: $w$ is a logarithm of $z$ iff $e^w = z$.
-/
def IsLogOf (w z : ℂ) : Prop :=
  exp_Sarason w = z

/--
  §IV.10 The slit complex plane $\mathbb{C} \setminus (-\infty, 0] = \{z \in \mathbb{C} : \operatorname{Re} z > 0 \vee \operatorname{Im} z \neq 0\}$.
-/
def slitPlane_Sarason : Set ℂ :=
  {z : ℂ | 0 < z.re ∨ z.im ≠ 0}

lemma slitPlane_Sarason_eq_slitPlane : slitPlane_Sarason = Complex.slitPlane := by
{
  rfl
}

/--
  §IV.10 A continuous branch of $\log z$ on $G \subseteq \mathbb{C}$ is a continuous function
  $L : \mathbb{C} \to \mathbb{C}$ on $G$ satisfying $e^{L(z)} = z$ for every $z \in G$.
-/
def IsBranchOfLog (L : ℂ → ℂ) (G : Set ℂ) : Prop :=
  ContinuousOn L G ∧ ∀ z ∈ G, exp_Sarason (L z) = z

/--
  §IV.10 Sarason's principal branch of the logarithm:
  $\operatorname{Log} z := \ln \|z\| + i \operatorname{arg} z$ for $-\pi < \operatorname{arg} z \le \pi$.
-/
def Log_Sarason (z : ℂ) : ℂ :=
  (Real.log ‖z‖ : ℂ) + (Complex.arg z : ℂ) * I

lemma Log_Sarason_eq_log (z : ℂ) : Log_Sarason z = Complex.log z := by
{
  rfl
}

/--
  §IV.9 Right-inverse identity: $e^{\operatorname{Log} z} = z$ for every $z \neq 0$.
-/
theorem IV_9_exp_Log_Sarason {z : ℂ} (hz : z ≠ 0) :
    exp_Sarason (Log_Sarason z) = z := by
{
  rw [exp_Sarason_eq_exp, Log_Sarason_eq_log]
  exact Complex.exp_log hz
}

/--
  §IV.9 Complete description of all logarithms of $z \neq 0$:
  $e^w = z$ if and only if $w = \operatorname{Log} z + 2\pi i k$ for some $k \in \mathbb{Z}$.
-/
theorem IV_9_isLogOf_iff {w z : ℂ} (hz : z ≠ 0) :
    IsLogOf w z ↔ ∃ k : ℤ, w = Log_Sarason z + (k : ℂ) * (2 * Real.pi * I) := by
{
  unfold IsLogOf
  rw [← IV_9_exp_Log_Sarason hz, IV_4_exp_eq_exp_iff, IV_9_exp_Log_Sarason hz]
}

/--
  §IV.11 **Theorem IV.11 (Weierstrass `_eps` Derivative of $\operatorname{Log} z$ on the Slit Plane)**:
  At every point $z \in \mathbb{C} \setminus (-\infty, 0]$ (`slitPlane_Sarason`),
  $\operatorname{Log} z$ has complex derivative $1 / z = z^{-1}$ in the `_eps` sense.
-/
theorem IV_11_hasDerivAt_Log_eps {z : ℂ} (hz : z ∈ slitPlane_Sarason) :
    HasDerivAt_eps Log_Sarason z⁻¹ z := by
{
  rw [← hasDerivAt_iff_eps]
  exact Complex.hasDerivAt_log hz
}

/--
  §IV.11 $\operatorname{Log} z$ is holomorphic on the slit plane (`HolomorphicOn_eps Log_Sarason slitPlane_Sarason`).
-/
theorem IV_11_holomorphicOn_Log_eps :
    HolomorphicOn_eps Log_Sarason slitPlane_Sarason := by
{
  intro z hz
  exact ⟨z⁻¹, IV_11_hasDerivAt_Log_eps hz⟩
}

/--
  §IV.10–§IV.11 `Log_Sarason` is a genuine continuous branch of the logarithm on `slitPlane_Sarason`.
-/
theorem IV_11_isBranchOfLog_Log :
    IsBranchOfLog Log_Sarason slitPlane_Sarason := by
{
  refine ⟨?_, ?_⟩
  · intro z hz
    exact (Complex.differentiableAt_log hz).continuousAt.continuousWithinAt
  · intro z hz
    exact IV_9_exp_Log_Sarason (Complex.slitPlane_ne_zero hz)
}

end Sarason.Ch4
