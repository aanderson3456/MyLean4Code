/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Sarason.Chapter2

/-!
# Sarason - Chapter 3: Linear-Fractional Transformations

Formalization of Section III of Donald Sarason's "Notes on Complex Function Theory".
Focus: Complex projective space, linear-fractional transformations (Möbius transformations),
decomposition into basic translations, scaling, and inversion, conformality (§III.3),
and fixed points (§III.4).

Credit: Donald Sarason
-/

open Complex OnePoint MatrixGroups Matrix Sarason Sarason.Ch2

namespace Sarason.Ch3

/--
  §III.1 A linear-fractional transformation (Möbius transformation) on ℂ,
  defined by φ(z) = (a * z + b) / (c * z + d) for complex coefficients a, b, c, d
  satisfying the non-degeneracy condition a * d - b * c ≠ 0.
-/
noncomputable def linFracTrans (a b c d z : ℂ) : ℂ :=
  -- Numerator a * z + b divided by denominator c * z + d in ℂ
  (a * z + b) / (c * z + d)

/--
  Sarason's shorthand notation φ(z) = (a * z + b) / (c * z + d)
  for a linear-fractional transformation on ℂ.
-/
noncomputable abbrev φ (a b c d z : ℂ) : ℂ :=
  -- Direct alias for `linFracTrans a b c d z`
  linFracTrans a b c d z

/--
  §III.1–§III.2 Action of a 2×2 invertible complex matrix `g : GL (Fin 2) ℂ` on a finite
  complex number `z : ℂ` (embedded in the Riemann sphere `OnePoint ℂ` as `some z`).
  Here `Fin 2` is the two-element index type `{0, 1}`, so the 2×2 matrix entries are
  `a = g 0 0`, `b = g 0 1`, `c = g 1 0`, `d = g 1 1`.
  The Möbius transformation maps `z` to:
  - `∞` if the denominator `g 1 0 * z + g 1 1 = 0`,
  - `linFracTrans (g 0 0) (g 0 1) (g 1 0) (g 1 1) z = (g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1)` otherwise.
-/
theorem moebius_apply_some (g : GL (Fin 2) ℂ) (z : ℂ) :
    g • (z : OnePoint ℂ) =
      if g 1 0 * z + g 1 1 = 0 then ∞ else (linFracTrans (g 0 0) (g 0 1) (g 1 0) (g 1 1) z : ℂ) := by
{
  -- Mathlib's `OnePoint.smul_some_eq_ite` unfolds the projective line action on finite points
  exact OnePoint.smul_some_eq_ite
}

/--
  §III.2 Action of a Möbius transformation `g : GL (Fin 2) ℂ` on the point at infinity `∞`.
  With `a = g 0 0`, `b = g 0 1`, `c = g 1 0`, `d = g 1 1`, the transformation maps `∞` to:
  - `∞` if `c = g 1 0 = 0`,
  - `a / c = g 0 0 / g 1 0` otherwise (the limit of `(a * z + b) / (c * z + d)` as `z → ∞`).
-/
theorem moebius_apply_infty (g : GL (Fin 2) ℂ) :
    g • (∞ : OnePoint ℂ) =
      if g 1 0 = 0 then ∞ else (g 0 0 / g 1 0 : ℂ) := by
{
  -- Mathlib's `OnePoint.smul_infty_eq_ite` gives the projective action on the point at infinity
  exact OnePoint.smul_infty_eq_ite g
}

/--
  §III.1 The 2×2 matrix in `GL (Fin 2) ℂ` representing the translation `z ↦ z + b`,
  corresponding to coefficients `a = 1, b = b, c = 0, d = 1` with determinant `1 * 1 - b * 0 = 1 ≠ 0`.
-/
noncomputable def translationMatrix (b : ℂ) : GL (Fin 2) ℂ :=
  -- Construct an element of GL(2, ℂ) from the 2×2 matrix !![1, b; 0, 1] and its non-zero determinant
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, b; 0, 1] (by {
    simp [det_fin_two]
  })

/--
  §III.1 Applying `translationMatrix b` to a finite complex number `z : ℂ` yields `z + b`.
-/
theorem translation_apply (b : ℂ) (z : ℂ) :
    translationMatrix b • (z : OnePoint ℂ) = (z + b : ℂ) := by
{
  -- Express the matrix action in terms of `linFracTrans` via `moebius_apply_some`
  rw [moebius_apply_some]
  unfold linFracTrans
  -- The denominator is 0 * z + 1 = 1, which never vanishes
  have h_den : (translationMatrix b) 1 0 * z + (translationMatrix b) 1 1 = 1 := by
  {
    simp [translationMatrix]
  }
  -- Substitute the denominator 1 and simplify the numerator 1 * z + b to z + b
  rw [h_den]
  simp [translationMatrix]
}

/--
  §III.1 The 2×2 matrix in `GL (Fin 2) ℂ` representing the scaling (dilation/rotation) `z ↦ a * z`
  for `a ≠ 0`, corresponding to `a = a, b = 0, c = 0, d = 1` with determinant `a ≠ 0`.
-/
noncomputable def scalingMatrix (a : ℂ) (ha : a ≠ 0) : GL (Fin 2) ℂ :=
  -- Construct an element of GL(2, ℂ) from !![a, 0; 0, 1] using `ha : a ≠ 0` for the determinant
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, 1] (by {
    simp [det_fin_two, ha]
  })

/--
  §III.1 Applying `scalingMatrix a ha` to a finite complex number `z : ℂ` yields `a * z`.
-/
theorem scaling_apply (a : ℂ) (ha : a ≠ 0) (z : ℂ) :
    scalingMatrix a ha • (z : OnePoint ℂ) = (a * z : ℂ) := by
{
  -- Express the matrix action in terms of `linFracTrans`
  rw [moebius_apply_some]
  unfold linFracTrans
  -- The denominator is 0 * z + 1 = 1, which is non-zero
  have h_den : (scalingMatrix a ha) 1 0 * z + (scalingMatrix a ha) 1 1 = 1 := by
  {
    simp [scalingMatrix]
  }
  -- Substitute the denominator 1 and simplify the numerator a * z + 0 to a * z
  rw [h_den]
  simp [scalingMatrix]
}

/--
  §III.1 The 2×2 matrix in `GL (Fin 2) ℂ` representing the inversion `z ↦ 1 / z`,
  corresponding to `a = 0, b = 1, c = 1, d = 0` with determinant `0 * 0 - 1 * 1 = -1 ≠ 0`.
-/
noncomputable def inversionMatrix : GL (Fin 2) ℂ :=
  -- Construct an element of GL(2, ℂ) from the anti-diagonal matrix !![0, 1; 1, 0]
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by {
    simp [det_fin_two]
  })

/--
  §III.1 Applying `inversionMatrix` to a non-zero complex number `z ≠ 0` yields `z⁻¹ = 1 / z`.
-/
theorem inversion_apply_some (z : ℂ) (hz : z ≠ 0) :
    inversionMatrix • (z : OnePoint ℂ) = (z⁻¹ : ℂ) := by
{
  -- Rewrite the action using `moebius_apply_some` and unfold `linFracTrans`
  rw [moebius_apply_some]
  unfold linFracTrans
  -- The denominator is 1 * z + 0 = z
  have h_den : (inversionMatrix) 1 0 * z + (inversionMatrix) 1 1 = z := by
  {
    simp [inversionMatrix]
  }
  rw [h_den]
  -- Split on whether the denominator z is zero; `hz : z ≠ 0` rules out the `∞` branch
  split_ifs with h
  · contradiction
  · -- The numerator is 0 * z + 1 = 1, so the fraction is 1 / z = z⁻¹
    have h_num : (inversionMatrix) 0 0 * z + (inversionMatrix) 0 1 = 1 := by
    {
      simp [inversionMatrix]
    }
    rw [h_num]
    rw [one_div]
}

/--
  §III.2 Applying `inversionMatrix` to `0 : ℂ` yields the point at infinity `∞`.
-/
theorem inversion_apply_zero :
    inversionMatrix • ((0 : ℂ) : OnePoint ℂ) = ∞ := by
{
  -- At z = 0, the denominator 1 * 0 + 0 vanishes, so the `if` takes the `∞` branch
  rw [moebius_apply_some]
  have h_den : (inversionMatrix) 1 0 * 0 + (inversionMatrix) 1 1 = 0 := by
  {
    simp [inversionMatrix]
  }
  rw [h_den]
  simp
}

/--
  §III.2 Applying `inversionMatrix` to `∞` yields `0 : ℂ`.
-/
theorem inversion_apply_infty :
    inversionMatrix • (∞ : OnePoint ℂ) = (0 : ℂ) := by
{
  -- At ∞, the lower-left entry c = 1 is non-zero, so ∞ maps to a / c = 0 / 1 = 0
  rw [moebius_apply_infty]
  have h_den : (inversionMatrix) 1 0 = 1 := by
  {
    simp [inversionMatrix]
  }
  rw [h_den]
  simp [inversionMatrix]
}

/-!
  §III.3 Conformality of Linear-Fractional Transformations
-/

/--
  §III.3 Difference quotient identity for a linear-fractional transformation:
  For `z ≠ z₀` with `c * z + d ≠ 0` and `c * z₀ + d ≠ 0`,
  `(φ(z) - φ(z₀)) / (z - z₀) = (a * d - b * c) / ((c * z + d) * (c * z₀ + d))`.
  This algebraic identity is the key step in Sarason §III.3 for computing `φ'(z₀)`.
-/
lemma linFracTrans_slope_eq (a b c d z z₀ : ℂ)
    (hz : c * z + d ≠ 0) (hz₀ : c * z₀ + d ≠ 0) (hne : z - z₀ ≠ 0) :
    (linFracTrans a b c d z - linFracTrans a b c d z₀) / (z - z₀) =
      (a * d - b * c) / ((c * z + d) * (c * z₀ + d)) := by
{
  -- Unfold φ(z) and φ(z₀) and combine the two fractions over the common denominator
  unfold linFracTrans
  rw [div_sub_div _ _ hz hz₀, div_div]
  -- Cross-multiplying the numerators cancels the quadratic terms in z * z₀, leaving (ad - bc)(z - z₀)
  have h_num : (a * z + b) * (c * z₀ + d) - (c * z + d) * (a * z₀ + b) =
      (a * d - b * c) * (z - z₀) := by
  {
    ring
  }
  -- Cancel the non-zero factor (z - z₀) from numerator and denominator
  rw [h_num, mul_div_mul_right _ _ hne]
}

/--
  §III.3 Mathlib `HasDerivAt` for a linear-fractional transformation at `z₀` when `c * z₀ + d ≠ 0`:
  the derivative of `φ(z) = (a * z + b) / (c * z + d)` is `(a * d - b * c) / (c * z₀ + d) ^ 2`.
-/
lemma linFracTrans_hasDerivAt (a b c d z₀ : ℂ) (h_den : c * z₀ + d ≠ 0) :
    HasDerivAt (linFracTrans a b c d) ((a * d - b * c) / (c * z₀ + d) ^ 2) z₀ := by
{
  unfold linFracTrans
  -- Derivative of the affine numerator z ↦ a * z + b is a
  have h_num : HasDerivAt (fun z : ℂ ↦ a * z + b) a z₀ := by
  {
    simpa [mul_one] using ((hasDerivAt_id z₀).const_mul a).add_const b
  }
  -- Derivative of the affine denominator z ↦ c * z + d is c
  have h_den_deriv : HasDerivAt (fun z : ℂ ↦ c * z + d) c z₀ := by
  {
    simpa [mul_one] using ((hasDerivAt_id z₀).const_mul c).add_const d
  }
  -- Apply the quotient rule `HasDerivAt.div` at z₀ where c * z₀ + d ≠ 0
  have h_div := h_num.div h_den_deriv h_den
  -- Simplify the quotient-rule numerator a(cz₀ + d) - (az₀ + b)c to ad - bc
  have h_eq : (a * (c * z₀ + d) - (a * z₀ + b) * c) / (c * z₀ + d) ^ 2 =
      (a * d - b * c) / (c * z₀ + d) ^ 2 := by
  {
    ring
  }
  rwa [h_eq] at h_div
}

/--
  §III.3 Weierstrass ε-δ complex derivative of a linear-fractional transformation:
  At any `z₀ ∈ ℂ` with `c * z₀ + d ≠ 0`, `φ(z) = (a * z + b) / (c * z + d)` has complex derivative
  `φ'(z₀) = (a * d - b * c) / (c * z₀ + d) ^ 2`.
-/
theorem linFracTrans_hasDerivAt_eps (a b c d z₀ : ℂ) (h_den : c * z₀ + d ≠ 0) :
    HasDerivAt_eps (linFracTrans a b c d) ((a * d - b * c) / (c * z₀ + d) ^ 2) z₀ := by
{
  -- Bridge from our Weierstrass ε-δ definition `HasDerivAt_eps` to Mathlib's `HasDerivAt`
  rw [← hasDerivAt_iff_eps]
  exact linFracTrans_hasDerivAt a b c d z₀ h_den
}

/--
  §III.3 A linear-fractional transformation is complex differentiable (in the Weierstrass ε-δ sense)
  at every point `z₀ ∈ ℂ` where `c * z₀ + d ≠ 0`.
-/
theorem linFracTrans_differentiableAt_eps (a b c d z₀ : ℂ) (h_den : c * z₀ + d ≠ 0) :
    DifferentiableAt_eps (linFracTrans a b c d) z₀ := by
{
  -- Provide `(a * d - b * c) / (c * z₀ + d) ^ 2` as the witness for differentiability
  exact ⟨(a * d - b * c) / (c * z₀ + d) ^ 2, linFracTrans_hasDerivAt_eps a b c d z₀ h_den⟩
}

/--
  §III.3 A linear-fractional transformation is holomorphic on the open domain `{z ∈ ℂ | c * z + d ≠ 0}`.
-/
theorem linFracTrans_holomorphicOn_eps (a b c d : ℂ) :
    HolomorphicOn_eps (linFracTrans a b c d) {z : ℂ | c * z + d ≠ 0} := by
{
  -- Every point z in the domain satisfies c * z + d ≠ 0, hence is complex differentiable
  intro z hz
  exact linFracTrans_differentiableAt_eps a b c d z hz
}

/--
  §III.3 Formula for `deriv (linFracTrans a b c d) z₀` when `c * z₀ + d ≠ 0`.
-/
lemma deriv_linFracTrans (a b c d z₀ : ℂ) (h_den : c * z₀ + d ≠ 0) :
    deriv (linFracTrans a b c d) z₀ = (a * d - b * c) / (c * z₀ + d) ^ 2 := by
{
  -- Extract the `deriv` value from `HasDerivAt`
  exact (linFracTrans_hasDerivAt a b c d z₀ h_den).deriv
}

/--
  §III.3 Non-vanishing of the derivative:
  When `a * d - b * c ≠ 0` and `c * z₀ + d ≠ 0`, the derivative `(a * d - b * c) / (c * z₀ + d) ^ 2`
  of the linear-fractional transformation is non-zero.
-/
lemma linFracTrans_deriv_ne_zero (a b c d z₀ : ℂ)
    (h_det : a * d - b * c ≠ 0) (h_den : c * z₀ + d ≠ 0) :
    (a * d - b * c) / (c * z₀ + d) ^ 2 ≠ 0 := by
{
  -- A quotient is non-zero when both numerator (ad - bc) and denominator ((cz₀ + d)²) are non-zero
  exact div_ne_zero h_det (pow_ne_zero 2 h_den)
}

/--
  §III.3 Conformality of Linear-Fractional Transformations (Sarason path-angle formulation):
  Every linear-fractional transformation `φ(z) = (a * z + b) / (c * z + d)` with `a * d - b * c ≠ 0`
  is conformal (preserves angles between regular intersecting curves) at every point `z₀ ∈ ℂ`
  where `c * z₀ + d ≠ 0`.
-/
theorem III_3 (a b c d z₀ : ℂ)
    (h_det : a * d - b * c ≠ 0)
    (h_den : c * z₀ + d ≠ 0)
    (h_arg : ∀ {x y} (γ : path_in_C x y) t,
      γ.extend t = z₀ →
      HasDerivAt_R_to_C_eps γ.extend (pathDeriv γ t) t →
      pathDeriv γ t ≠ 0 →
      arg (((a * d - b * c) / (c * z₀ + d) ^ 2) * pathDeriv γ t) =
        arg ((a * d - b * c) / (c * z₀ + d) ^ 2) + arg (pathDeriv γ t)) :
    conformal (linFracTrans a b c d) z₀ := by
{
  -- Apply §II.11 (`conformality_at_point`) using the derivative `(ad - bc)/(cz₀ + d)² ≠ 0`
  exact conformality_at_point
    (linFracTrans a b c d)
    z₀
    ((a * d - b * c) / (c * z₀ + d) ^ 2)
    (linFracTrans_hasDerivAt_eps a b c d z₀ h_den)
    (linFracTrans_deriv_ne_zero a b c d z₀ h_det h_den)
    h_arg
}

/--
  §III.3 Mathlib `ConformalAt` version:
  A linear-fractional transformation with `a * d - b * c ≠ 0` is `ConformalAt` every `z₀`
  where `c * z₀ + d ≠ 0`.
-/
theorem III_3_conformalAt (a b c d z₀ : ℂ)
    (h_det : a * d - b * c ≠ 0)
    (h_den : c * z₀ + d ≠ 0) :
    ConformalAt (linFracTrans a b c d) z₀ := by
{
  -- By complex analysis, any function differentiable at z₀ with non-zero derivative is conformal at z₀
  apply DifferentiableAt.conformalAt
  · exact (linFracTrans_hasDerivAt a b c d z₀ h_den).differentiableAt
  · rw [deriv_linFracTrans a b c d z₀ h_den]
    exact linFracTrans_deriv_ne_zero a b c d z₀ h_det h_den
}

/-!
  §III.4 Fixed Points of Linear-Fractional Transformations
-/

/--
  §III.2 / §III.4 Extended linear-fractional transformation on the Riemann sphere
  `OnePoint ℂ` (ℂ ∪ {∞}):
  - maps a finite point `z : ℂ` to `∞` if the denominator `c * z + d = 0` (the pole of φ),
    and to `linFracTrans a b c d z = (a * z + b) / (c * z + d)` otherwise;
  - maps `∞` to `∞` if `c = 0`, and to `a / c` otherwise.
-/
noncomputable def linFracTransExt (a b c d : ℂ) : OnePoint ℂ → OnePoint ℂ
  -- Finite complex input z ∈ ℂ: check whether z is the pole -d / c
  | (z : ℂ) => if c * z + d = 0 then ∞ else (linFracTrans a b c d z : ℂ)
  -- Point at infinity ∞: check whether φ is affine (c = 0) or genuinely rational (c ≠ 0)
  | ∞ => if c = 0 then ∞ else (a / c : ℂ)

/--
  Definitional unfolding lemma for `linFracTransExt` at a finite complex number `z : ℂ`.
-/
lemma linFracTransExt_coe (a b c d z : ℂ) :
    linFracTransExt a b c d (z : ℂ) =
      if c * z + d = 0 then ∞ else (linFracTrans a b c d z : ℂ) := by
{
  -- Holds by pattern-matching definition of `linFracTransExt` on `(z : ℂ)`
  rfl
}

/--
  Definitional unfolding lemma for `linFracTransExt` at the point at infinity `∞`.
-/
lemma linFracTransExt_infty (a b c d : ℂ) :
    linFracTransExt a b c d ∞ = if c = 0 then ∞ else (a / c : ℂ) := by
{
  -- Holds by pattern-matching definition of `linFracTransExt` on `∞`
  rfl
}

/--
  §III.2 Agreement between Mathlib's `GL (Fin 2) ℂ` Möbius action on `OnePoint ℂ`
  and our explicit extended linear-fractional transformation `linFracTransExt`:
  Here `Fin 2` is the 2-element index type `{0, 1}` indexing the rows and columns of the
  2×2 matrix `g = !![g 0 0, g 0 1; g 1 0, g 1 1] = !![a, b; c, d]`.
-/
theorem moebius_eq_linFracTransExt (g : GL (Fin 2) ℂ) (w : OnePoint ℂ) :
    g • w = linFracTransExt (g 0 0) (g 0 1) (g 1 0) (g 1 1) w := by
{
  -- Case split on whether w ∈ ℂ ∪ {∞} is the point at infinity or a finite complex number
  cases w with
  | infty =>
    -- At w = ∞, both sides reduce to `if g 1 0 = 0 then ∞ else g 0 0 / g 1 0`
    exact moebius_apply_infty g
  | coe z =>
    -- At w = (z : ℂ), both sides reduce to `if g 1 0 * z + g 1 1 = 0 then ∞ else φ(z)`
    exact moebius_apply_some g z
}

/--
  §III.4 Characterization of when `∞` is a fixed point of `linFracTransExt a b c d`:
  `φ(∞) = ∞` if and only if `c = 0` (i.e., `φ` is an affine transformation `(a * z + b) / d`).
-/
lemma linFracTransExt_fixed_infty_iff (a b c d : ℂ) :
    linFracTransExt a b c d ∞ = ∞ ↔ c = 0 := by
{
  -- Unfold the action at ∞ and split on whether c = 0
  rw [linFracTransExt_infty]
  split_ifs with hc
  · -- When c = 0, φ(∞) = ∞ holds trivially
    exact iff_of_true rfl hc
  · -- When c ≠ 0, φ(∞) = (a / c : ℂ) is finite and therefore cannot equal ∞
    exact iff_of_false (OnePoint.coe_ne_infty _) hc
}

/--
  §III.4 Characterization of when a finite point `z : ℂ` is a fixed point of `linFracTransExt`:
  `φ(z) = z` in `OnePoint ℂ` if and only if the denominator `c * z + d` is non-zero
  and `(a * z + b) / (c * z + d) = z` in `ℂ`.
-/
lemma linFracTransExt_fixed_coe_iff (a b c d z : ℂ) :
    linFracTransExt a b c d (z : ℂ) = (z : ℂ) ↔
      c * z + d ≠ 0 ∧ linFracTrans a b c d z = z := by
{
  -- Unfold `linFracTransExt` at `(z : ℂ)` and split on whether `c * z + d = 0`
  rw [linFracTransExt_coe]
  split_ifs with h_den
  · -- If c * z + d = 0, then φ(z) = ∞ ≠ (z : ℂ), so z is not a fixed point
    exact iff_of_false (OnePoint.infty_ne_coe z) (fun h => h.1 h_den)
  · -- If c * z + d ≠ 0, injectivity of the coercion `ℂ → OnePoint ℂ` reduces to `φ(z) = z` in ℂ
    rw [OnePoint.coe_eq_coe]
    exact ⟨fun h => ⟨h_den, h⟩, fun h => h.2⟩
}

/--
  §III.4 Sarason's Quadratic Fixed-Point Equation:
  When `a * d - b * c ≠ 0`, a finite point `z : ℂ` satisfies `c * z + d ≠ 0` and `φ(z) = z`
  if and only if `z` is a root of the quadratic equation `c * z ^ 2 + (d - a) * z - b = 0`.
  Crucially, `a * d - b * c ≠ 0` guarantees that no root of `c * z ^ 2 + (d - a) * z - b = 0`
  can ever make the denominator `c * z + d` vanish.
-/
lemma linFracTrans_fixed_iff_quad (a b c d z : ℂ) (h_det : a * d - b * c ≠ 0) :
    (c * z + d ≠ 0 ∧ linFracTrans a b c d z = z) ↔
      c * z ^ 2 + (d - a) * z - b = 0 := by
{
  constructor
  · -- Forward direction: clear the non-zero denominator c * z + d from (a * z + b) / (c * z + d) = z
    rintro ⟨h_den, h_eq⟩
    unfold linFracTrans at h_eq
    have h_mul : a * z + b = z * (c * z + d) := (div_eq_iff h_den).mp h_eq
    -- Rearrange a * z + b = c * z^2 + d * z into c * z^2 + (d - a) * z - b = 0
    linear_combination -h_mul
  · -- Reverse direction: assume z satisfies c * z^2 + (d - a) * z - b = 0
    intro h_quad
    -- First show c * z + d ≠ 0: if c * z + d = 0, then a * d - b * c = c * h_quad - (c * z - a) * 0 = 0
    have h_den : c * z + d ≠ 0 := by
    {
      intro h0
      apply h_det
      linear_combination c * h_quad - (c * z - a) * h0
    }
    -- With c * z + d ≠ 0 established, divide a * z + b = z * (c * z + d) by c * z + d
    refine ⟨h_den, ?_⟩
    unfold linFracTrans
    rw [div_eq_iff h_den]
    linear_combination -h_quad
}

/--
  §III.4 Combined fixed-point criterion for a finite point `z : ℂ` in `OnePoint ℂ`:
  When `a * d - b * c ≠ 0`, `linFracTransExt a b c d (z : ℂ) = (z : ℂ)` holds
  if and only if `c * z ^ 2 + (d - a) * z - b = 0`.
-/
lemma linFracTransExt_fixed_coe_iff_quad (a b c d z : ℂ) (h_det : a * d - b * c ≠ 0) :
    linFracTransExt a b c d (z : ℂ) = (z : ℂ) ↔
      c * z ^ 2 + (d - a) * z - b = 0 := by
{
  -- Chain `linFracTransExt_fixed_coe_iff` with `linFracTrans_fixed_iff_quad`
  rw [linFracTransExt_fixed_coe_iff, linFracTrans_fixed_iff_quad a b c d z h_det]
}

/--
  §III.4 Characterization of the trivial identity linear-fractional transformation on `OnePoint ℂ`:
  When `a * d - b * c ≠ 0`, `linFracTransExt a b c d` fixes every point of `OnePoint ℂ`
  if and only if `a = d`, `b = 0`, and `c = 0` (so `φ(z) = (a * z + 0) / (0 * z + a) = z`).
-/
lemma linFracTransExt_eq_id_iff (a b c d : ℂ) (h_det : a * d - b * c ≠ 0) :
    (∀ w : OnePoint ℂ, linFracTransExt a b c d w = w) ↔ (a = d ∧ b = 0 ∧ c = 0) := by
{
  constructor
  · -- If φ fixes every point, test w = ∞, w = 0, and w = 1 to force c = 0, b = 0, and a = d
    intro h
    have hc : c = 0 := (linFracTransExt_fixed_infty_iff a b c d).mp (h ∞)
    -- Evaluating the quadratic fixed-point equation at z = 0 gives -b = 0
    have h0 : c * (0 : ℂ) ^ 2 + (d - a) * 0 - b = 0 :=
      (linFracTransExt_fixed_coe_iff_quad a b c d 0 h_det).mp (h (0 : ℂ))
    -- Evaluating the quadratic fixed-point equation at z = 1 gives c + (d - a) - b = 0
    have h1 : c * (1 : ℂ) ^ 2 + (d - a) * 1 - b = 0 :=
      (linFracTransExt_fixed_coe_iff_quad a b c d 1 h_det).mp (h (1 : ℂ))
    have hb : b = 0 := by
    {
      linear_combination -h0
    }
    have had : a = d := by
    {
      linear_combination h0 - h1 + hc
    }
    exact ⟨had, hb, hc⟩
  · -- Conversely, if a = d, b = 0, and c = 0, then both ∞ and every finite z ∈ ℂ are fixed
    rintro ⟨had, hb, hc⟩ w
    cases w with
    | infty =>
      exact (linFracTransExt_fixed_infty_iff a b c d).mpr hc
    | coe z =>
      rw [linFracTransExt_fixed_coe_iff_quad a b c d z h_det]
      linear_combination (z ^ 2) * hc - z * had - hb
}

/--
  §III.4 Case 1a (`c = 0`, `a = d`, `b ≠ 0`, i.e., a non-trivial translation `z ↦ z + b / d`):
  No finite point `z ∈ ℂ` is fixed because `(d - a) * z - b = -b ≠ 0`,
  so `∞` is the unique fixed point of `linFracTransExt a b 0 d` in `OnePoint ℂ`.
-/
lemma linFracTransExt_fixed_c_zero_a_eq_d (a b d : ℂ)
    (h_det : a * d - b * 0 ≠ 0) (had : a = d) (hb : b ≠ 0) (w : OnePoint ℂ) :
    linFracTransExt a b 0 d w = w ↔ w = ∞ := by
{
  -- Split on whether w is ∞ or a finite complex number z
  cases w with
  | infty =>
    -- Since c = 0, ∞ is fixed
    rw [linFracTransExt_fixed_infty_iff]
    exact iff_of_true rfl rfl
  | coe z =>
    -- For finite z, the fixed-point equation reduces to -b = 0, which is false since b ≠ 0
    rw [linFracTransExt_fixed_coe_iff_quad a b 0 d z h_det]
    have h_lhs : (0 : ℂ) * z ^ 2 + (d - a) * z - b = -b := by
    {
      linear_combination -z * had
    }
    rw [h_lhs, neg_eq_zero]
    exact iff_of_false hb (OnePoint.coe_ne_infty z)
}

/--
  §III.4 Case 1b (`c = 0`, `a ≠ d`, i.e., a non-translation affine map `z ↦ (a / d) * z + b / d`):
  `linFracTransExt a b 0 d` has exactly two distinct fixed points in `OnePoint ℂ`:
  the unique finite solution `z₀ = b / (d - a)` of `(d - a) * z - b = 0`, and `∞`.
-/
lemma linFracTransExt_fixed_c_zero_a_ne_d (a b d : ℂ)
    (h_det : a * d - b * 0 ≠ 0) (had : a ≠ d) (w : OnePoint ℂ) :
    linFracTransExt a b 0 d w = w ↔ w = (b / (d - a) : ℂ) ∨ w = ∞ := by
{
  -- Since a ≠ d, the linear coefficient d - a is non-zero
  have hda : d - a ≠ 0 := sub_ne_zero.mpr had.symm
  cases w with
  | infty =>
    -- At w = ∞, c = 0 ensures ∞ is a fixed point
    rw [linFracTransExt_fixed_infty_iff]
    exact iff_of_true rfl (Or.inr rfl)
  | coe z =>
    -- At finite w = z, the quadratic equation degenerates to the linear equation z * (d - a) = b
    rw [linFracTransExt_fixed_coe_iff_quad a b 0 d z h_det]
    have h_quad : (0 : ℂ) * z ^ 2 + (d - a) * z - b = 0 ↔ z * (d - a) = b := by
    {
      constructor <;> intro h <;> linear_combination h
    }
    -- Divide by d - a ≠ 0 to isolate the unique finite fixed point z = b / (d - a)
    rw [h_quad, ← eq_div_iff hda, ← OnePoint.coe_eq_coe]
    exact ⟨Or.inl, fun h => h.resolve_right (OnePoint.coe_ne_infty z)⟩
}

/--
  §III.4 Sarason's Quadratic Formula Factorization (`c ≠ 0`):
  When `c ≠ 0` and `s ∈ ℂ` is a square root of the discriminant `Δ = (d - a) ^ 2 + 4 * b * c`
  (so `s * s = (d - a) ^ 2 + 4 * b * c`), completing the square gives
  `4 * c * (c * z ^ 2 + (d - a) * z - b) = (2 * c * z - (a - d + s)) * (2 * c * z - (a - d - s))`.
  Hence the roots of `c * z ^ 2 + (d - a) * z - b = 0` are precisely
  `z = (a - d + s) / (2 * c)` and `z = (a - d - s) / (2 * c)`.
-/
lemma quad_factor_roots (a b c d s z : ℂ) (hc : c ≠ 0) (hs : s * s = (d - a) ^ 2 + 4 * b * c) :
    c * z ^ 2 + (d - a) * z - b = 0 ↔
      z = (a - d + s) / (2 * c) ∨ z = (a - d - s) / (2 * c) := by
{
  -- Since c ≠ 0, both 2 * c and 4 * c are non-zero in ℂ
  have h2c : (2 : ℂ) * c ≠ 0 := mul_ne_zero two_ne_zero hc
  have h4c : (4 : ℂ) * c ≠ 0 := mul_ne_zero (by norm_num) hc
  -- Complete the square by multiplying the quadratic by 4 * c and substituting s * s = (d - a)^2 + 4bc
  have h_ident : 4 * c * (c * z ^ 2 + (d - a) * z - b) =
      (z * (2 * c) - (a - d + s)) * (z * (2 * c) - (a - d - s)) := by
  {
    linear_combination hs
  }
  -- Multiplying by the non-zero factor 4 * c preserves the zero set
  have h_mul : c * z ^ 2 + (d - a) * z - b = 0 ↔
      4 * c * (c * z ^ 2 + (d - a) * z - b) = 0 := by
  {
    exact ⟨fun h => by rw [h, mul_zero], fun h => (mul_eq_zero.mp h).resolve_left h4c⟩
  }
  -- Factor the product of linear terms and divide each factor by 2 * c ≠ 0
  rw [h_mul, h_ident, mul_eq_zero, sub_eq_zero, sub_eq_zero]
  rw [← eq_div_iff h2c, ← eq_div_iff h2c]
}

/--
  §III.4 Distinctness of the two quadratic roots when the discriminant is non-zero (`s ≠ 0`):
  When `c ≠ 0` and `s ≠ 0`, `(a - d + s) / (2 * c) ≠ (a - d - s) / (2 * c)`.
-/
lemma quad_roots_ne_of_s_ne_zero (a c d s : ℂ) (hc : c ≠ 0) (hs_ne : s ≠ 0) :
    (a - d + s) / (2 * c) ≠ (a - d - s) / (2 * c) := by
{
  -- Multiply both sides of a putative equality by 2 * c ≠ 0 to clear denominators
  have h2c : (2 : ℂ) * c ≠ 0 := mul_ne_zero two_ne_zero hc
  intro h_eq
  have h_num : a - d + s = a - d - s := by
  {
    have h1 := congrArg (· * (2 * c)) h_eq
    rwa [div_mul_cancel₀ _ h2c, div_mul_cancel₀ _ h2c] at h1
  }
  -- Subtracting a - d - s from a - d + s yields 2 * s = 0, contradicting s ≠ 0
  have h2s : (2 : ℂ) * s = 0 := by
  {
    linear_combination h_num
  }
  exact mul_ne_zero two_ne_zero hs_ne h2s
}

/--
  §III.4 Case 2 (`c ≠ 0`):
  When `c ≠ 0`, `∞` is not a fixed point (since `φ(∞) = a / c ∈ ℂ`), so all fixed points of
  `linFracTransExt a b c d` in `OnePoint ℂ` are finite and coincide with the quadratic roots
  `((a - d + s) / (2 * c) : ℂ)` and `((a - d - s) / (2 * c) : ℂ)`.
-/
lemma linFracTransExt_fixed_c_ne_zero (a b c d s : ℂ)
    (h_det : a * d - b * c ≠ 0) (hc : c ≠ 0) (hs : s * s = (d - a) ^ 2 + 4 * b * c)
    (w : OnePoint ℂ) :
    linFracTransExt a b c d w = w ↔
      w = ((a - d + s) / (2 * c) : ℂ) ∨ w = ((a - d - s) / (2 * c) : ℂ) := by
{
  -- Split on whether w is ∞ or a finite complex number z ∈ ℂ
  cases w with
  | infty =>
    -- Since c ≠ 0, w = ∞ is neither fixed nor equal to either finite root
    rw [linFracTransExt_fixed_infty_iff]
    exact iff_of_false hc
      (fun h => h.elim (OnePoint.infty_ne_coe _) (OnePoint.infty_ne_coe _))
  | coe z =>
    -- For finite w = z, reduce to the quadratic equation and apply `quad_factor_roots`
    rw [linFracTransExt_fixed_coe_iff_quad a b c d z h_det]
    rw [quad_factor_roots a b c d s z hc hs]
    rw [OnePoint.coe_eq_coe, OnePoint.coe_eq_coe]
}

/--
  §III.4 Fixed Points of a Linear-Fractional Transformation (Finite Case, `c ≠ 0`):
  When `a * d - b * c ≠ 0` and `c ≠ 0`, `linFracTrans a b c d` has either one or two
  finite fixed points in `{z ∈ ℂ | c * z + d ≠ 0}`, corresponding to whether the discriminant
  `Δ = (d - a) ^ 2 + 4 * b * c` of `c * z ^ 2 + (d - a) * z - b = 0` is zero or non-zero.
-/
theorem III_4_finite (a b c d : ℂ) (h_det : a * d - b * c ≠ 0) (hc : c ≠ 0) :
    (∃ z₀ : ℂ, ∀ z : ℂ, (c * z + d ≠ 0 ∧ linFracTrans a b c d z = z) ↔ z = z₀) ∨
    (∃ z₁ z₂ : ℂ, z₁ ≠ z₂ ∧
      ∀ z : ℂ, (c * z + d ≠ 0 ∧ linFracTrans a b c d z = z) ↔ z = z₁ ∨ z = z₂) := by
{
  -- Extract a complex square root s of the quadratic discriminant Δ = (d - a)^2 + 4bc
  obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self ((d - a) ^ 2 + 4 * b * c)
  -- Split on whether the discriminant square root s is zero (double root) or non-zero (two distinct roots)
  by_cases hs0 : s = 0
  · -- Subcase Δ = 0 (s = 0): the two quadratic formula branches collapse to a single fixed point
    left
    refine ⟨(a - d + s) / (2 * c), fun z => ?_⟩
    rw [linFracTrans_fixed_iff_quad a b c d z h_det, quad_factor_roots a b c d s z hc hs.symm]
    have h_eq : (a - d - s) / (2 * c) = (a - d + s) / (2 * c) := by
    {
      rw [hs0, sub_zero, add_zero]
    }
    rw [h_eq, or_self]
  · -- Subcase Δ ≠ 0 (s ≠ 0): the quadratic formula gives two distinct finite fixed points
    right
    refine ⟨(a - d + s) / (2 * c), (a - d - s) / (2 * c),
      quad_roots_ne_of_s_ne_zero a c d s hc hs0, fun z => ?_⟩
    rw [linFracTrans_fixed_iff_quad a b c d z h_det, quad_factor_roots a b c d s z hc hs.symm]
}

/--
  §III.4 Fixed Points of a Linear-Fractional Transformation (Full Riemann Sphere):
  Excluding the trivial identity transformation, any linear-fractional transformation
  with `a * d - b * c ≠ 0` has either one or two fixed points in `OnePoint ℂ` (ℂ ∪ {∞}).
-/
theorem III_4 (a b c d : ℂ)
    (h_det : a * d - b * c ≠ 0)
    (h_not_id : ¬ ∀ w : OnePoint ℂ, linFracTransExt a b c d w = w) :
    (∃ w₀ : OnePoint ℂ, ∀ w : OnePoint ℂ, linFracTransExt a b c d w = w ↔ w = w₀) ∨
    (∃ w₁ w₂ : OnePoint ℂ, w₁ ≠ w₂ ∧
      ∀ w : OnePoint ℂ, linFracTransExt a b c d w = w ↔ w = w₁ ∨ w = w₂) := by
{
  -- Follow Sarason's §III.4 case split: first check whether c = 0 or c ≠ 0
  by_cases hc : c = 0
  · subst hc
    -- When c = 0, ∞ is always a fixed point; now split on whether a = d or a ≠ d
    by_cases had : a = d
    · -- When c = 0 and a = d, non-identity (`h_not_id`) forces b ≠ 0, giving the unique fixed point ∞
      have hb : b ≠ 0 := by
      {
        intro hb0
        exact h_not_id ((linFracTransExt_eq_id_iff a b 0 d h_det).mpr ⟨had, hb0, rfl⟩)
      }
      left
      exact ⟨∞, linFracTransExt_fixed_c_zero_a_eq_d a b d h_det had hb⟩
    · -- When c = 0 and a ≠ d, there are two distinct fixed points: b / (d - a) ∈ ℂ and ∞
      right
      exact ⟨(b / (d - a) : ℂ), ∞, OnePoint.coe_ne_infty _,
        linFracTransExt_fixed_c_zero_a_ne_d a b d h_det had⟩
  · -- When c ≠ 0, ∞ is not fixed, and finite fixed points solve c * z^2 + (d - a) * z - b = 0
    obtain ⟨s, hs⟩ := IsAlgClosed.exists_eq_mul_self ((d - a) ^ 2 + 4 * b * c)
    -- Split on whether the square root s of the discriminant Δ = (d - a)^2 + 4bc vanishes
    by_cases hs0 : s = 0
    · -- When s = 0 (zero discriminant), (a - d) / (2 * c) is the unique fixed point
      left
      refine ⟨((a - d + s) / (2 * c) : ℂ), fun w => ?_⟩
      rw [linFracTransExt_fixed_c_ne_zero a b c d s h_det hc hs.symm w]
      have h_eq : ((a - d - s) / (2 * c) : ℂ) = (a - d + s) / (2 * c) := by
      {
        rw [hs0, sub_zero, add_zero]
      }
      rw [h_eq, or_self]
    · -- When s ≠ 0 (non-zero discriminant), the quadratic formula yields two distinct fixed points
      right
      refine ⟨((a - d + s) / (2 * c) : ℂ), ((a - d - s) / (2 * c) : ℂ), ?_,
        linFracTransExt_fixed_c_ne_zero a b c d s h_det hc hs.symm⟩
      intro h_coe
      exact quad_roots_ne_of_s_ne_zero a c d s hc hs0 (OnePoint.coe_eq_coe.mp h_coe)
}

/-!
  ### Connecting Sarason's Quadratic Formula Proof (`c * z^2 + (d - a) * z - b = 0`) to `GL (Fin 2) ℂ`

  In Mathlib, Möbius transformations on the Riemann sphere `OnePoint ℂ` are represented by the group
  `GL (Fin 2) ℂ` of invertible 2×2 complex matrices, where `Fin 2 = {0, 1}` is simply the 2-element
  index type labeling the two rows (`0` and `1`) and two columns (`0` and `1`) of a 2×2 matrix:
  ```
      g = !![ g 0 0, g 0 1 ;
              g 1 0, g 1 1 ]  =  !![ a, b ;
                                     c, d ]
  ```
  1. **Dictionary between coefficients `(a, b, c, d)` and `Fin 2` matrix entries**:
     Reading off the four entries indexed by `Fin 2` gives
     `a = g 0 0`, `b = g 0 1`, `c = g 1 0`, and `d = g 1 1`.
  2. **Non-degeneracy (`a * d - b * c ≠ 0`) from `GL (Fin 2) ℂ`**:
     Because `g` belongs to the general linear group `GL (Fin 2) ℂ`, its determinant `g.det` is a
     unit in `ℂ` (`g.det.ne_zero`), and `Matrix.det_fin_two` expands `det g` over `Fin 2` into
     `g 0 0 * g 1 1 - g 0 1 * g 1 0 = a * d - b * c ≠ 0`.
  3. **Projective action vs. Sarason's quadratic fixed-point equation**:
     By `moebius_eq_linFracTransExt`, the `GL (Fin 2) ℂ` action `g • w` on `OnePoint ℂ` is
     identically `linFracTransExt (g 0 0) (g 0 1) (g 1 0) (g 1 1) w`. Thus `g • w = w` reduces
     directly to Sarason's fixed-point equation `c * z^2 + (d - a) * z - b = 0` (with
     `a = g 0 0, b = g 0 1, c = g 1 0, d = g 1 1`), whose roots come from the quadratic formula
     `z = ((a - d) ± √((d - a)^2 + 4bc)) / (2c)` proved in `quad_factor_roots` and `III_4`.
     (Geometrically, in complex projective space `ℂℙ¹ ≅ OnePoint ℂ`, a fixed point of `g • ·` is an
     eigenvector of the 2×2 matrix `g`, and the characteristic polynomial `det(g - λI) = λ^2 - (a+d)λ + (ad-bc)`
     has discriminant `(a + d)^2 - 4(ad - bc) = (d - a)^2 + 4bc`, matching Sarason's quadratic discriminant!)
-/

/--
  `GL (Fin 2) ℂ` Möbius action version of §III.4:
  Any non-identity Möbius transformation `g • ·` on `OnePoint ℂ` has one or two fixed points,
  obtained by applying `III_4` (and its quadratic formula proof on `c * z^2 + (d - a) * z - b = 0`)
  to the 2×2 matrix entries `a = g 0 0`, `b = g 0 1`, `c = g 1 0`, `d = g 1 1`.
-/
theorem III_4_moebius (g : GL (Fin 2) ℂ)
    (h_not_id : ¬ ∀ w : OnePoint ℂ, g • w = w) :
    (∃ w₀ : OnePoint ℂ, ∀ w : OnePoint ℂ, g • w = w ↔ w = w₀) ∨
    (∃ w₁ w₂ : OnePoint ℂ, w₁ ≠ w₂ ∧ ∀ w : OnePoint ℂ, g • w = w ↔ w = w₁ ∨ w = w₂) := by
{
  -- Extract Sarason's condition a * d - b * c ≠ 0 from the invertibility of the 2×2 matrix g ∈ GL (Fin 2) ℂ
  have h_det : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
  {
    have h_ne : (g : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := g.det.ne_zero
    rwa [Matrix.det_fin_two] at h_ne
  }
  -- Translate the non-identity hypothesis from `g • w` to `linFracTransExt (g 0 0) (g 0 1) (g 1 0) (g 1 1) w`
  have h_not_id' : ¬ ∀ w : OnePoint ℂ,
      linFracTransExt (g 0 0) (g 0 1) (g 1 0) (g 1 1) w = w := by
  {
    intro h_id
    apply h_not_id
    intro w
    rw [moebius_eq_linFracTransExt g w]
    exact h_id w
  }
  -- Rewrite `g • w` into `linFracTransExt` and invoke `III_4` (which solves c * z^2 + (d - a) * z - b = 0)
  simp only [moebius_eq_linFracTransExt g]
  exact III_4 (g 0 0) (g 0 1) (g 1 0) (g 1 1) h_det h_not_id'
}

/-!
  §III.5 Determining a Linear-Fractional Transformation; 3-Fold Transitivity
-/

/--
  §III.5 Predicate characterizing when a map `φ : OnePoint ℂ → OnePoint ℂ` on the Riemann sphere
  is a linear-fractional transformation:
  `φ = linFracTransExt a b c d` for some `a, b, c, d ∈ ℂ` with `a * d - b * c ≠ 0`.
-/
def IsLinFracTrans (φ : OnePoint ℂ → OnePoint ℂ) : Prop :=
  -- Existential witness of non-degenerate coefficients a, b, c, d ∈ ℂ
  ∃ a b c d : ℂ, a * d - b * c ≠ 0 ∧ φ = linFracTransExt a b c d

/--
  §III.2 / §III.5 Constructs the invertible 2×2 matrix in `GL (Fin 2) ℂ` associated with
  coefficients `a, b, c, d ∈ ℂ` satisfying `a * d - b * c ≠ 0`.
-/
noncomputable def gl2OfCoeffs (a b c d : ℂ) (h_det : a * d - b * c ≠ 0) : GL (Fin 2) ℂ :=
  -- Package the 2×2 matrix !![a, b; c, d] together with its non-zero determinant proof
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, b; c, d] (by {
    simpa [Matrix.det_fin_two] using h_det
  })

/--
  The `GL (Fin 2) ℂ` action of `gl2OfCoeffs a b c d h_det` on `OnePoint ℂ` coincides with
  `linFracTransExt a b c d`.
-/
lemma gl2OfCoeffs_smul (a b c d : ℂ) (h_det : a * d - b * c ≠ 0) (w : OnePoint ℂ) :
    gl2OfCoeffs a b c d h_det • w = linFracTransExt a b c d w := by
{
  -- Rewrite via `moebius_eq_linFracTransExt` and unfold the 2×2 matrix entries
  rw [moebius_eq_linFracTransExt]
  rfl
}

/--
  §III.5 Equivalence between `IsLinFracTrans φ` and the projective `GL (Fin 2) ℂ` action:
  a map `φ : OnePoint ℂ → OnePoint ℂ` satisfies `IsLinFracTrans φ` if and only if
  `φ = (g • ·)` for some `g ∈ GL (Fin 2) ℂ`.
-/
lemma isLinFracTrans_iff_gl2 (φ : OnePoint ℂ → OnePoint ℂ) :
    IsLinFracTrans φ ↔ ∃ g : GL (Fin 2) ℂ, φ = (g • ·) := by
{
  constructor
  · -- Forward direction: package coefficients (a, b, c, d) into `gl2OfCoeffs a b c d h_det`
    rintro ⟨a, b, c, d, h_det, rfl⟩
    refine ⟨gl2OfCoeffs a b c d h_det, ?_⟩
    ext w
    exact (gl2OfCoeffs_smul a b c d h_det w).symm
  · -- Reverse direction: read off the 2×2 matrix entries a = g 0 0, b = g 0 1, c = g 1 0, d = g 1 1
    rintro ⟨g, rfl⟩
    have h_det : g 0 0 * g 1 1 - g 0 1 * g 1 0 ≠ 0 := by
    {
      have h_ne : (g : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := g.det.ne_zero
      rwa [Matrix.det_fin_two] at h_ne
    }
    refine ⟨g 0 0, g 0 1, g 1 0, g 1 1, h_det, ?_⟩
    ext w
    exact moebius_eq_linFracTransExt g w
}

/--
  Pigeonhole principle for 3 distinct points vs. a 2-element set `{w₁, w₂}`:
  three pairwise distinct points `z 0, z 1, z 2` cannot all lie in `{w₁, w₂}`.
-/
lemma three_pts_not_in_pair {α : Type*} (z : Fin 3 → α) (hz : Function.Injective z)
    (w₁ w₂ : α) (h : ∀ j : Fin 3, z j = w₁ ∨ z j = w₂) : False := by
{
  -- Extract pairwise distinctness of z 0, z 1, z 2 from injectivity of z
  have h01 : z 0 ≠ z 1 := fun heq => (by decide : (0 : Fin 3) ≠ 1) (hz heq)
  have h02 : z 0 ≠ z 2 := fun heq => (by decide : (0 : Fin 3) ≠ 2) (hz heq)
  have h12 : z 1 ≠ z 2 := fun heq => (by decide : (1 : Fin 3) ≠ 2) (hz heq)
  -- Exhaust the 2³ = 8 cases of assigning z 0, z 1, z 2 to w₁ or w₂
  rcases h 0 with h0 | h0 <;> rcases h 1 with h1 | h1 <;> rcases h 2 with h2 | h2
  · exact h01 (h0.trans h1.symm)
  · exact h01 (h0.trans h1.symm)
  · exact h02 (h0.trans h2.symm)
  · exact h12 (h1.trans h2.symm)
  · exact h12 (h1.trans h2.symm)
  · exact h02 (h0.trans h2.symm)
  · exact h01 (h0.trans h1.symm)
  · exact h01 (h0.trans h1.symm)
}

/--
  §III.5 Consequence of §III.4 (Three Fixed Points Imply the Identity):
  If a Möbius transformation `g ∈ GL (Fin 2) ℂ` fixes three distinct points `z 0, z 1, z 2`
  in `OnePoint ℂ`, then `g` acts as the identity on all of `OnePoint ℂ`.
-/
lemma moebius_eq_id_of_three_fixed (g : GL (Fin 2) ℂ) (z : Fin 3 → OnePoint ℂ)
    (hz : Function.Injective z) (hfix : ∀ j : Fin 3, g • z j = z j) :
    ∀ x : OnePoint ℂ, g • x = x := by
{
  -- Suppose for contradiction that g is not the identity transformation on OnePoint ℂ
  by_contra h_not_id
  -- By Theorem III_4_moebius, g has either 1 or 2 fixed points in OnePoint ℂ
  rcases III_4_moebius g h_not_id with ⟨w₀, hw₀⟩ | ⟨w₁, w₂, _, hw₁₂⟩
  · -- If g has a single fixed point w₀, then z 0 = w₀ = z 1, contradicting injectivity of z
    have hz0 : z 0 = w₀ := (hw₀ (z 0)).mp (hfix 0)
    have hz1 : z 1 = w₀ := (hw₀ (z 1)).mp (hfix 1)
    exact (by decide : (0 : Fin 3) ≠ 1) (hz (hz0.trans hz1.symm))
  · -- If g has two fixed points w₁, w₂, then z 0, z 1, z 2 ∈ {w₁, w₂}, contradicting pigeonhole
    exact three_pts_not_in_pair z hz w₁ w₂ (fun j => (hw₁₂ (z j)).mp (hfix j))
}

/--
  §III.5 Uniqueness of a Möbius Transformation on Three Distinct Points:
  If `g₁, g₂ ∈ GL (Fin 2) ℂ` agree on three distinct points `z 0, z 1, z 2 ∈ OnePoint ℂ`,
  then `g₁ • x = g₂ • x` for every `x ∈ OnePoint ℂ`.
-/
lemma moebius_unique_of_three_pts (g₁ g₂ : GL (Fin 2) ℂ) (z : Fin 3 → OnePoint ℂ)
    (hz : Function.Injective z) (heq : ∀ j : Fin 3, g₁ • z j = g₂ • z j) :
    ∀ x : OnePoint ℂ, g₁ • x = g₂ • x := by
{
  -- Following Sarason §III.5, form the composition g₁⁻¹ * g₂, which fixes z 0, z 1, and z 2
  have hfix : ∀ j : Fin 3, (g₁⁻¹ * g₂) • z j = z j := by
  {
    intro j
    rw [mul_smul, ← heq j, inv_smul_smul]
  }
  -- By `moebius_eq_id_of_three_fixed`, g₁⁻¹ * g₂ acts as the identity everywhere
  have hid := moebius_eq_id_of_three_fixed (g₁⁻¹ * g₂) z hz hfix
  intro x
  -- Apply g₁ • · to both sides of (g₁⁻¹ * g₂) • x = x to conclude g₂ • x = g₁ • x
  have hx := congrArg (g₁ • ·) (hid x)
  rw [mul_smul, smul_inv_smul] at hx
  exact hx.symm
}

/--
  §III.5 Auxiliary step 1 for Existence:
  Given any point `p ∈ OnePoint ℂ`, there exists `S ∈ GL (Fin 2) ℂ` mapping `p ↦ ∞`
  (the identity if `p = ∞`, or `z ↦ 1 / (z - ζ)` if `p = (ζ : ℂ)` is finite).
-/
lemma exists_gl2_send_to_infty (p : OnePoint ℂ) :
    ∃ S : GL (Fin 2) ℂ, S • p = ∞ := by
{
  cases p with
  | infty =>
    -- If p is already ∞, the identity matrix 1 ∈ GL (Fin 2) ℂ fixes ∞
    exact ⟨1, one_smul _ _⟩
  | coe ζ =>
    -- If p = ζ ∈ ℂ is finite, use S(z) = 1 / (z - ζ) with determinant 0 * (-ζ) - 1 * 1 = -1 ≠ 0
    have h_det : (0 : ℂ) * (-ζ) - 1 * 1 ≠ 0 := by norm_num
    refine ⟨gl2OfCoeffs 0 1 1 (-ζ) h_det, ?_⟩
    rw [gl2OfCoeffs_smul]
    -- At z = ζ, the denominator 1 * ζ + (-ζ) vanishes, so S maps ζ to ∞
    change (if (1 : ℂ) * ζ + -ζ = 0 then ∞ else (linFracTrans 0 1 1 (-ζ) ζ : OnePoint ℂ)) = ∞
    have h0 : (1 : ℂ) * ζ + -ζ = 0 := by ring
    rw [if_pos h0]
}

/--
  §III.5 Auxiliary step 2 for Existence (Affine Case `z₂ = ∞`):
  Given two distinct finite points `ζ₀ ≠ ζ₁` in `ℂ`, the affine linear-fractional transformation
  `T(z) = (z - ζ₀) / (ζ₁ - ζ₀)` maps `ζ₀ ↦ 0`, `ζ₁ ↦ 1`, and `∞ ↦ ∞`.
-/
lemma exists_gl2_affine_std_triple (ζ₀ ζ₁ : ℂ) (h01 : ζ₀ ≠ ζ₁) :
    ∃ T : GL (Fin 2) ℂ,
      T • (ζ₀ : OnePoint ℂ) = (0 : ℂ) ∧
      T • (ζ₁ : OnePoint ℂ) = (1 : ℂ) ∧
      T • (∞ : OnePoint ℂ) = ∞ := by
{
  -- Since ζ₀ ≠ ζ₁, the denominator d = ζ₁ - ζ₀ is non-zero
  have h_sub : ζ₁ - ζ₀ ≠ 0 := sub_ne_zero.mpr h01.symm
  have h_det : (1 : ℂ) * (ζ₁ - ζ₀) - (-ζ₀) * 0 ≠ 0 := by
  {
    simpa using h_sub
  }
  -- Construct T from coefficients a = 1, b = -ζ₀, c = 0, d = ζ₁ - ζ₀
  refine ⟨gl2OfCoeffs 1 (-ζ₀) 0 (ζ₁ - ζ₀) h_det, ?_, ?_, ?_⟩
  · -- Verify T(ζ₀) = (ζ₀ - ζ₀) / (ζ₁ - ζ₀) = 0
    rw [gl2OfCoeffs_smul]
    change (if (0 : ℂ) * ζ₀ + (ζ₁ - ζ₀) = 0 then ∞
      else (linFracTrans 1 (-ζ₀) 0 (ζ₁ - ζ₀) ζ₀ : OnePoint ℂ)) = (0 : ℂ)
    have h_den : (0 : ℂ) * ζ₀ + (ζ₁ - ζ₀) ≠ 0 := by simpa using h_sub
    rw [if_neg h_den, OnePoint.coe_eq_coe]
    unfold linFracTrans
    have h_num : (1 : ℂ) * ζ₀ + -ζ₀ = 0 := by ring
    rw [h_num, zero_div]
  · -- Verify T(ζ₁) = (ζ₁ - ζ₀) / (ζ₁ - ζ₀) = 1
    rw [gl2OfCoeffs_smul]
    change (if (0 : ℂ) * ζ₁ + (ζ₁ - ζ₀) = 0 then ∞
      else (linFracTrans 1 (-ζ₀) 0 (ζ₁ - ζ₀) ζ₁ : OnePoint ℂ)) = (1 : ℂ)
    have h_den : (0 : ℂ) * ζ₁ + (ζ₁ - ζ₀) ≠ 0 := by simpa using h_sub
    rw [if_neg h_den, OnePoint.coe_eq_coe]
    unfold linFracTrans
    have h_num : (1 : ℂ) * ζ₁ + -ζ₀ = ζ₁ - ζ₀ := by ring
    have h_den_eq : (0 : ℂ) * ζ₁ + (ζ₁ - ζ₀) = ζ₁ - ζ₀ := by ring
    rw [h_num, h_den_eq, div_self h_sub]
  · -- Verify T(∞) = ∞ since c = 0
    rw [gl2OfCoeffs_smul]
    exact (linFracTransExt_fixed_infty_iff 1 (-ζ₀) 0 (ζ₁ - ζ₀)).mpr rfl
}

/--
  §III.5 Mapping Any Three Distinct Points to `(0, 1, ∞)`:
  Given any three distinct points `z 0, z 1, z 2 ∈ OnePoint ℂ`, there exists `G ∈ GL (Fin 2) ℂ`
  mapping `z 0 ↦ 0`, `z 1 ↦ 1`, and `z 2 ↦ ∞`.
-/
lemma exists_gl2_std_triple (z : Fin 3 → OnePoint ℂ) (hz : Function.Injective z) :
    ∃ G : GL (Fin 2) ℂ,
      G • z 0 = (0 : ℂ) ∧ G • z 1 = (1 : ℂ) ∧ G • z 2 = ∞ := by
{
  -- First choose S ∈ GL (Fin 2) ℂ sending z 2 to ∞
  obtain ⟨S, hS2⟩ := exists_gl2_send_to_infty (z 2)
  -- Since S • · is injective and z 0 ≠ z 2, S • z 0 cannot be ∞
  have h02 : S • z 0 ≠ ∞ := by
  {
    rw [← hS2]
    intro heq
    exact (by decide : (0 : Fin 3) ≠ 2) (hz (MulAction.injective S heq))
  }
  -- Similarly, since z 1 ≠ z 2, S • z 1 cannot be ∞
  have h12 : S • z 1 ≠ ∞ := by
  {
    rw [← hS2]
    intro heq
    exact (by decide : (1 : Fin 3) ≠ 2) (hz (MulAction.injective S heq))
  }
  -- Thus S • z 0 = (ζ₀ : ℂ) and S • z 1 = (ζ₁ : ℂ) are both finite complex numbers
  cases hS0 : S • z 0 with
  | infty => exact (h02 hS0).elim
  | coe ζ₀ =>
    cases hS1 : S • z 1 with
    | infty => exact (h12 hS1).elim
    | coe ζ₁ =>
      -- Moreover, ζ₀ ≠ ζ₁ since z 0 ≠ z 1 and S • · is injective
      have h01 : ζ₀ ≠ ζ₁ := by
      {
        intro heq
        have h_smul : S • z 0 = S • z 1 := by rw [hS0, hS1, heq]
        exact (by decide : (0 : Fin 3) ≠ 1) (hz (MulAction.injective S h_smul))
      }
      -- Apply the affine map T sending (ζ₀, ζ₁, ∞) ↦ (0, 1, ∞) and compose G = T * S
      obtain ⟨T, hT0, hT1, hT2⟩ := exists_gl2_affine_std_triple ζ₀ ζ₁ h01
      refine ⟨T * S, ?_, ?_, ?_⟩
      · rw [mul_smul, hS0, hT0]
      · rw [mul_smul, hS1, hT1]
      · rw [mul_smul, hS2, hT2]
}

/--
  §III.5 Existence of a Möbius Transformation Mapping `z j ↦ w j` (`j = 0, 1, 2`):
  Given two injective triples `z, w : Fin 3 → OnePoint ℂ`, composing `G_z` (sending `z` to `(0, 1, ∞)`)
  with `G_w⁻¹` (sending `(0, 1, ∞)` to `w`) produces `G = G_w⁻¹ * G_z ∈ GL (Fin 2) ℂ`
  satisfying `G • z j = w j` for `j = 0, 1, 2`.
-/
lemma exists_gl2_three_pts (z w : Fin 3 → OnePoint ℂ)
    (hz : Function.Injective z) (hw : Function.Injective w) :
    ∃ G : GL (Fin 2) ℂ, ∀ j : Fin 3, G • z j = w j := by
{
  -- Obtain G_z mapping (z 0, z 1, z 2) ↦ (0, 1, ∞) and G_w mapping (w 0, w 1, w 2) ↦ (0, 1, ∞)
  obtain ⟨Gz, hGz0, hGz1, hGz2⟩ := exists_gl2_std_triple z hz
  obtain ⟨Gw, hGw0, hGw1, hGw2⟩ := exists_gl2_std_triple w hw
  -- Their composition Gw⁻¹ * Gz maps z j ↦ w j for each j ∈ {0, 1, 2}
  refine ⟨Gw⁻¹ * Gz, ?_⟩
  rintro ⟨_ | _ | _ | n, hn⟩
  · -- Case j = 0: Gw⁻¹ • (Gz • z 0) = Gw⁻¹ • 0 = Gw⁻¹ • (Gw • w 0) = w 0
    change (Gw⁻¹ * Gz) • z 0 = w 0
    rw [mul_smul, hGz0, ← hGw0, inv_smul_smul]
  · -- Case j = 1: Gw⁻¹ • (Gz • z 1) = Gw⁻¹ • 1 = Gw⁻¹ • (Gw • w 1) = w 1
    change (Gw⁻¹ * Gz) • z 1 = w 1
    rw [mul_smul, hGz1, ← hGw1, inv_smul_smul]
  · -- Case j = 2: Gw⁻¹ • (Gz • z 2) = Gw⁻¹ • ∞ = Gw⁻¹ • (Gw • w 2) = w 2
    change (Gw⁻¹ * Gz) • z 2 = w 2
    rw [mul_smul, hGz2, ← hGw2, inv_smul_smul]
  · -- Impossible case: n + 3 < 3
    exact (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hn)).elim
}

/--
  §III.5 Three-Fold Transitivity of Linear-Fractional Transformations:
  Given any three distinct points `z 0, z 1, z 2 ∈ OnePoint ℂ` and any three distinct points
  `w 0, w 1, w 2 ∈ OnePoint ℂ`, there exists a unique linear-fractional transformation `φ`
  such that `φ (z j) = w j` for `j = 0, 1, 2`.
-/
theorem III_5 (z w : Fin 3 → OnePoint ℂ)
    (hz : Function.Injective z) (hw : Function.Injective w) :
    ∃! φ : OnePoint ℂ → OnePoint ℂ,
      IsLinFracTrans φ ∧ ∀ j : Fin 3, φ (z j) = w j := by
{
  -- Step 1 (Existence): obtain G ∈ GL (Fin 2) ℂ mapping z j ↦ w j for j = 0, 1, 2
  obtain ⟨G, hG⟩ := exists_gl2_three_pts z w hz hw
  refine ⟨(G • ·), ⟨(isLinFracTrans_iff_gl2 _).mpr ⟨G, rfl⟩, hG⟩, ?_⟩
  -- Step 2 (Uniqueness): any linear-fractional transformation φ' agreeing with φ on z 0, z 1, z 2 equals φ
  rintro φ' ⟨hφ'_lft, hφ'_pts⟩
  obtain ⟨G', rfl⟩ := (isLinFracTrans_iff_gl2 φ').mp hφ'_lft
  ext x
  exact moebius_unique_of_three_pts G' G z hz (fun j => (hφ'_pts j).trans (hG j).symm) x
}

/-!
  ### Exercise III.5.1: Finding the Linear-Fractional Transformation Mapping `(0, 1, ∞) ↦ (1, ∞, -i)`

  To find `φ(z) = (a * z + b) / (c * z + d)` mapping `0 ↦ 1`, `1 ↦ ∞`, and `∞ ↦ -i`:
  1. Since `φ(1) = ∞`, the denominator `c * z + d` must vanish at `z = 1`, so we may take `c = 1` and `d = -1`.
  2. Since `φ(∞) = a / c = -i` and `c = 1`, we obtain `a = -i`.
  3. Since `φ(0) = b / d = 1` and `d = -1`, we obtain `b = -1`.
  Thus `φ(z) = (-i * z - 1) / (z - 1) = (i * z + 1) / (1 - z)` with non-zero determinant
  `a * d - b * c = (-i) * (-1) - (-1) * 1 = 1 + i ≠ 0`.
-/

/--
  Non-zero determinant check for the coefficients `(a, b, c, d) = (-i, -1, 1, -1)` in Exercise III.5.1:
  `(-i) * (-1) - (-1) * 1 = 1 + i ≠ 0`.
-/
lemma exercise_III_5_1_det : (-Complex.I) * (-1 : ℂ) - (-1 : ℂ) * (1 : ℂ) ≠ 0 := by
{
  -- If (-i)*(-1) - (-1)*1 = 0, taking real parts gives 1 = 0, a contradiction
  intro h_zero
  have h_re := congrArg Complex.re h_zero
  norm_num at h_re
}

/--
  Exercise III.5.1:
  The linear-fractional transformation `φ(z) = (-i * z - 1) / (z - 1)` (`linFracTransExt (-Complex.I) (-1) 1 (-1)`)
  is a valid non-degenerate linear-fractional transformation (`IsLinFracTrans`) that maps
  `0 ↦ 1`, `1 ↦ ∞`, and `∞ ↦ -i`.
-/
lemma exercise_III_5_1 :
    IsLinFracTrans (linFracTransExt (-Complex.I) (-1) 1 (-1)) ∧
    linFracTransExt (-Complex.I) (-1) 1 (-1) (0 : ℂ) = (1 : ℂ) ∧
    linFracTransExt (-Complex.I) (-1) 1 (-1) (1 : ℂ) = ∞ ∧
    linFracTransExt (-Complex.I) (-1) 1 (-1) ∞ = (-Complex.I : ℂ) := by
{
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- 1. Verify IsLinFracTrans using a = -i, b = -1, c = 1, d = -1 and `exercise_III_5_1_det`
    exact ⟨-Complex.I, -1, 1, -1, exercise_III_5_1_det, rfl⟩
  · -- 2. Verify φ(0) = (-i * 0 - 1) / (1 * 0 - 1) = (-1) / (-1) = 1
    rw [linFracTransExt_coe]
    have h_den : (1 : ℂ) * 0 + -1 ≠ 0 := by norm_num
    rw [if_neg h_den, OnePoint.coe_eq_coe]
    unfold linFracTrans
    norm_num
  · -- 3. Verify φ(1) = ∞ since the denominator 1 * 1 + (-1) = 0 vanishes at z = 1
    rw [linFracTransExt_coe]
    have h_den : (1 : ℂ) * 1 + -1 = 0 := by ring
    rw [if_pos h_den]
  · -- 4. Verify φ(∞) = a / c = -i / 1 = -i since c = 1 ≠ 0
    rw [linFracTransExt_infty]
    rw [if_neg one_ne_zero, div_one]
}

/-!
  ### Cross-Ratio on the Riemann Sphere (`cross_ratio_Cinfty`) and Exercise III.5.2 (Invariance)

  Following Sarason §III.5, for any three distinct points `z₁, z₂, z₃ ∈ ℂ ∪ {∞}` and a fourth point
  `z₄ ∈ ℂ ∪ {∞}`, the **cross-ratio** `(z₁, z₂, z₃, z₄)` (`cross_ratio_Cinfty z₁ z₂ z₃ z₄`) is defined
  as the image `φ(z₄)` of `z₄` under the unique linear-fractional transformation `φ` mapping
  `z₁ ↦ ∞`, `z₂ ↦ 0`, and `z₃ ↦ 1`.
-/

/--
  §III.2 / §III.5 Closure of linear-fractional transformations under composition:
  If `φ` and `ψ` are linear-fractional transformations on `OnePoint ℂ`, then so is `φ ∘ ψ`.
-/
lemma IsLinFracTrans.comp {φ ψ : OnePoint ℂ → OnePoint ℂ}
    (hφ : IsLinFracTrans φ) (hψ : IsLinFracTrans ψ) :
    IsLinFracTrans (φ ∘ ψ) := by
{
  -- Represent φ = (g₁ • ·) and ψ = (g₂ • ·) for invertible 2×2 matrices g₁, g₂ ∈ GL (Fin 2) ℂ
  obtain ⟨g₁, rfl⟩ := (isLinFracTrans_iff_gl2 φ).mp hφ
  obtain ⟨g₂, rfl⟩ := (isLinFracTrans_iff_gl2 ψ).mp hψ
  -- By the group action law `mul_smul`, (g₁ • ·) ∘ (g₂ • ·) = ((g₁ * g₂) • ·)
  refine (isLinFracTrans_iff_gl2 _).mpr ⟨g₁ * g₂, ?_⟩
  ext w
  exact (mul_smul g₁ g₂ w).symm
}

/--
  §III.2 / §III.5 Every linear-fractional transformation on `OnePoint ℂ` is injective.
-/
lemma IsLinFracTrans.injective {ψ : OnePoint ℂ → OnePoint ℂ}
    (hψ : IsLinFracTrans ψ) : Function.Injective ψ := by
{
  -- Represent ψ = (g • ·) for g ∈ GL (Fin 2) ℂ and apply `MulAction.injective`
  obtain ⟨g, rfl⟩ := (isLinFracTrans_iff_gl2 ψ).mp hψ
  exact MulAction.injective g
}

/--
  Helper packaging three points `z₁, z₂, z₃ ∈ OnePoint ℂ` into a map `Fin 3 → OnePoint ℂ`.
-/
def triple3 (z₁ z₂ z₃ : OnePoint ℂ) : Fin 3 → OnePoint ℂ
  | 0 => z₁
  | 1 => z₂
  | 2 => z₃

/--
  If `z₁, z₂, z₃ ∈ OnePoint ℂ` are pairwise distinct, then `triple3 z₁ z₂ z₃ : Fin 3 → OnePoint ℂ`
  is injective.
-/
lemma injective_triple3 {z₁ z₂ z₃ : OnePoint ℂ}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    Function.Injective (triple3 z₁ z₂ z₃) := by
{
  -- Check all pairs i, j ∈ {0, 1, 2}
  rintro ⟨_ | _ | _ | i, hi⟩ ⟨_ | _ | _ | j, hj⟩ h_eq
  · rfl
  · exact (h12 h_eq).elim
  · exact (h13 h_eq).elim
  · exact (Nat.not_lt_zero j (Nat.lt_of_add_lt_add_right hj)).elim
  · exact (h12 h_eq.symm).elim
  · rfl
  · exact (h23 h_eq).elim
  · exact (Nat.not_lt_zero j (Nat.lt_of_add_lt_add_right hj)).elim
  · exact (h13 h_eq.symm).elim
  · exact (h23 h_eq.symm).elim
  · rfl
  · exact (Nat.not_lt_zero j (Nat.lt_of_add_lt_add_right hj)).elim
  all_goals exact (Nat.not_lt_zero i (Nat.lt_of_add_lt_add_right hi)).elim
}

/--
  The standard target triple `(∞, 0, 1)` in `OnePoint ℂ` is pairwise distinct, so
  `triple3 ∞ (0 : ℂ) (1 : ℂ)` is injective.
-/
lemma injective_triple3_infty_zero_one :
    Function.Injective (triple3 (∞ : OnePoint ℂ) (0 : ℂ) (1 : ℂ)) := by
{
  -- Apply `injective_triple3` using ∞ ≠ 0, ∞ ≠ 1, and 0 ≠ 1
  refine injective_triple3 (OnePoint.infty_ne_coe 0) (OnePoint.infty_ne_coe 1) ?_
  intro h01
  exact zero_ne_one (OnePoint.coe_eq_coe.mp h01)
}

/--
  Equivalence between pointwise agreement on `triple3 z₁ z₂ z₃` and the three equations
  `φ z₁ = w₁`, `φ z₂ = w₂`, `φ z₃ = w₃`.
-/
lemma forall_triple3_iff (φ : OnePoint ℂ → OnePoint ℂ) (z₁ z₂ z₃ w₁ w₂ w₃ : OnePoint ℂ) :
    (∀ j : Fin 3, φ (triple3 z₁ z₂ z₃ j) = triple3 w₁ w₂ w₃ j) ↔
      (φ z₁ = w₁ ∧ φ z₂ = w₂ ∧ φ z₃ = w₃) := by
{
  constructor
  · -- Evaluate at j = 0, 1, 2
    intro h
    exact ⟨h 0, h 1, h 2⟩
  · -- Pattern match on j ∈ {0, 1, 2}
    rintro ⟨h0, h1, h2⟩ ⟨_ | _ | _ | n, hn⟩
    · exact h0
    · exact h1
    · exact h2
    · exact (Nat.not_lt_zero n (Nat.lt_of_add_lt_add_right hn)).elim
}

/--
  §III.5 Existence and uniqueness of the linear-fractional transformation mapping three
  distinct points `z₁, z₂, z₃ ∈ OnePoint ℂ` to `∞, 0, 1` respectively (direct specialization of `III_5`).
-/
lemma existsUnique_lft_infty_zero_one {z₁ z₂ z₃ : OnePoint ℂ}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    ∃! φ : OnePoint ℂ → OnePoint ℂ,
      IsLinFracTrans φ ∧ φ z₁ = ∞ ∧ φ z₂ = (0 : ℂ) ∧ φ z₃ = (1 : ℂ) := by
{
  -- Apply `III_5` to `triple3 z₁ z₂ z₃` and `triple3 ∞ 0 1`, then rewrite via `forall_triple3_iff`
  have h_ex := III_5 (triple3 z₁ z₂ z₃) (triple3 ∞ (0 : ℂ) (1 : ℂ))
    (injective_triple3 h12 h13 h23) injective_triple3_infty_zero_one
  simpa only [forall_triple3_iff] using h_ex
}

/--
  §III.5 **Cross-Ratio on the Extended Complex Plane (`cross_ratio_Cinfty`)**:
  Takes four inputs `z₁, z₂, z₃, z₄ ∈ OnePoint ℂ` and outputs the image `φ(z₄)` of `z₄`
  under the linear-fractional transformation `φ` mapping `z₁ ↦ ∞`, `z₂ ↦ 0`, and `z₃ ↦ 1`.
-/
noncomputable def cross_ratio_Cinfty (z₁ z₂ z₃ z₄ : OnePoint ℂ) : OnePoint ℂ :=
  -- Select the linear-fractional transformation φ sending (z₁, z₂, z₃) ↦ (∞, 0, 1) and evaluate at z₄
  (Classical.epsilon (fun φ : OnePoint ℂ → OnePoint ℂ =>
    IsLinFracTrans φ ∧ φ z₁ = ∞ ∧ φ z₂ = (0 : ℂ) ∧ φ z₃ = (1 : ℂ))) z₄

/--
  §III.5 Characterization of `cross_ratio_Cinfty`:
  If `z₁, z₂, z₃` are pairwise distinct and `φ` is *any* linear-fractional transformation
  mapping `z₁ ↦ ∞`, `z₂ ↦ 0`, and `z₃ ↦ 1`, then `cross_ratio_Cinfty z₁ z₂ z₃ z₄ = φ z₄`.
-/
lemma cross_ratio_Cinfty_eq_of_maps {z₁ z₂ z₃ : OnePoint ℂ}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    {φ : OnePoint ℂ → OnePoint ℂ}
    (hφ : IsLinFracTrans φ ∧ φ z₁ = ∞ ∧ φ z₂ = (0 : ℂ) ∧ φ z₃ = (1 : ℂ))
    (z₄ : OnePoint ℂ) :
    cross_ratio_Cinfty z₁ z₂ z₃ z₄ = φ z₄ := by
{
  -- By `existsUnique_lft_infty_zero_one`, the epsilon-selected map satisfies the same 3-point condition
  obtain ⟨φ₀, hφ₀, h_uniq⟩ := existsUnique_lft_infty_zero_one h12 h13 h23
  have h_eps := @Classical.epsilon_spec (OnePoint ℂ → OnePoint ℂ)
    (fun f => IsLinFracTrans f ∧ f z₁ = ∞ ∧ f z₂ = (0 : ℂ) ∧ f z₃ = (1 : ℂ)) ⟨φ₀, hφ₀⟩
  -- Uniqueness forces the epsilon-selected map to equal φ₀, and φ to equal φ₀
  have h_eq : Classical.epsilon (fun f : OnePoint ℂ → OnePoint ℂ =>
      IsLinFracTrans f ∧ f z₁ = ∞ ∧ f z₂ = (0 : ℂ) ∧ f z₃ = (1 : ℂ)) = φ :=
    (h_uniq _ h_eps).trans (h_uniq _ hφ).symm
  exact congrFun h_eq z₄
}

/--
  Exercise III.5.2 (Invariance of the Cross-Ratio Under Linear-Fractional Transformations):
  For any linear-fractional transformation `ψ` (`IsLinFracTrans ψ`), any three distinct points
  `z₁, z₂, z₃ ∈ OnePoint ℂ`, and any `z₄ ∈ OnePoint ℂ`,
  `cross_ratio_Cinfty (ψ z₁) (ψ z₂) (ψ z₃) (ψ z₄) = cross_ratio_Cinfty z₁ z₂ z₃ z₄`.
-/
theorem exercise_III_5_2 (ψ : OnePoint ℂ → OnePoint ℂ) (hψ : IsLinFracTrans ψ)
    (z₁ z₂ z₃ z₄ : OnePoint ℂ) (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    cross_ratio_Cinfty (ψ z₁) (ψ z₂) (ψ z₃) (ψ z₄) = cross_ratio_Cinfty z₁ z₂ z₃ z₄ := by
{
  -- Step 1: Since ψ is injective, ψ z₁, ψ z₂, ψ z₃ are pairwise distinct
  have hψ_inj := hψ.injective
  have hψ12 : ψ z₁ ≠ ψ z₂ := fun h => h12 (hψ_inj h)
  have hψ13 : ψ z₁ ≠ ψ z₃ := fun h => h13 (hψ_inj h)
  have hψ23 : ψ z₂ ≠ ψ z₃ := fun h => h23 (hψ_inj h)
  -- Step 2: Let φ be the unique linear-fractional transformation sending (ψ z₁, ψ z₂, ψ z₃) ↦ (∞, 0, 1)
  obtain ⟨φ, ⟨hφ_lft, hφ1, hφ2, hφ3⟩, _⟩ := existsUnique_lft_infty_zero_one hψ12 hψ13 hψ23
  -- By `cross_ratio_Cinfty_eq_of_maps`, the LHS equals φ (ψ z₄) = (φ ∘ ψ) z₄
  have h_lhs : cross_ratio_Cinfty (ψ z₁) (ψ z₂) (ψ z₃) (ψ z₄) = (φ ∘ ψ) z₄ :=
    cross_ratio_Cinfty_eq_of_maps hψ12 hψ13 hψ23 ⟨hφ_lft, hφ1, hφ2, hφ3⟩ (ψ z₄)
  -- Step 3: Observe that φ ∘ ψ is a linear-fractional transformation sending (z₁, z₂, z₃) ↦ (∞, 0, 1)
  have h_comp : IsLinFracTrans (φ ∘ ψ) ∧
      (φ ∘ ψ) z₁ = ∞ ∧ (φ ∘ ψ) z₂ = (0 : ℂ) ∧ (φ ∘ ψ) z₃ = (1 : ℂ) :=
    ⟨hφ_lft.comp hψ, hφ1, hφ2, hφ3⟩
  -- Therefore, by `cross_ratio_Cinfty_eq_of_maps` on (z₁, z₂, z₃), the RHS also equals (φ ∘ ψ) z₄
  have h_rhs : cross_ratio_Cinfty z₁ z₂ z₃ z₄ = (φ ∘ ψ) z₄ :=
    cross_ratio_Cinfty_eq_of_maps h12 h13 h23 h_comp z₄
  exact h_lhs.trans h_rhs.symm
}

/-!
  §III.6 Elementary Linear-Fractional Transformations and Decomposition of `GL(2, ℂ)`

  Sarason §III.6 shows that every linear-fractional transformation `φ(z) = (a * z + b) / (c * z + d)`
  (and hence `(g • ·)` for every `g ∈ GL (Fin 2) ℂ`) is a composition of four elementary maps:
  dilations (`z ↦ r * z`, `r > 0`), rotations (`z ↦ u * z`, `‖u‖ = 1`), translations (`z ↦ z + β`),
  and inversion (`z ↦ 1 / z`), using `(a * z + b) / (c * z + d) = (b - a * d / c) / (c * z + d) + a / c`.
-/

/-- §III.6 Elementary Translation `z ↦ z + β` on `OnePoint ℂ`. -/
noncomputable def transLFT (β : ℂ) : OnePoint ℂ → OnePoint ℂ := linFracTransExt 1 β 0 1

/-- §III.6 Complex Scaling `z ↦ α * z` on `OnePoint ℂ` (encompassing dilations `r > 0` and rotations `‖u‖ = 1`). -/
noncomputable def scaleLFT (α : ℂ) : OnePoint ℂ → OnePoint ℂ := linFracTransExt α 0 0 1

/-- §III.6 Elementary Inversion `z ↦ 1 / z` on `OnePoint ℂ`. -/
noncomputable def invLFT : OnePoint ℂ → OnePoint ℂ := linFracTransExt 0 1 1 0

@[simp] lemma transLFT_infty (β : ℂ) : transLFT β ∞ = ∞ := by { simp [transLFT, linFracTransExt_infty] }

@[simp] lemma transLFT_coe (β z : ℂ) : transLFT β (z : ℂ) = ((z + β : ℂ) : OnePoint ℂ) := by
{
  -- Denominator 0 * z + 1 = 1 ≠ 0, so transLFT β z = (1 * z + β) / 1 = z + β
  rw [transLFT, linFracTransExt_coe, if_neg (by norm_num : (0 : ℂ) * z + 1 ≠ 0), OnePoint.coe_eq_coe]
  unfold linFracTrans; ring
}

@[simp] lemma scaleLFT_infty (α : ℂ) : scaleLFT α ∞ = ∞ := by { simp [scaleLFT, linFracTransExt_infty] }

@[simp] lemma scaleLFT_coe (α z : ℂ) : scaleLFT α (z : ℂ) = ((α * z : ℂ) : OnePoint ℂ) := by
{
  -- Denominator 0 * z + 1 = 1 ≠ 0, so scaleLFT α z = (α * z + 0) / 1 = α * z
  rw [scaleLFT, linFracTransExt_coe, if_neg (by norm_num : (0 : ℂ) * z + 1 ≠ 0), OnePoint.coe_eq_coe]
  unfold linFracTrans; ring
}

@[simp] lemma invLFT_infty : invLFT ∞ = ((0 : ℂ) : OnePoint ℂ) := by
{
  rw [invLFT, linFracTransExt_infty, if_neg one_ne_zero, zero_div]
}

@[simp] lemma invLFT_zero : invLFT ((0 : ℂ) : OnePoint ℂ) = ∞ := by
{
  rw [invLFT, linFracTransExt_coe, if_pos (by ring : (1 : ℂ) * 0 + 0 = 0)]
}

lemma invLFT_coe_of_ne_zero {z : ℂ} (hz : z ≠ 0) :
    invLFT (z : ℂ) = ((1 / z : ℂ) : OnePoint ℂ) := by
{
  -- For z ≠ 0, denominator 1 * z + 0 = z ≠ 0, so invLFT z = 1 / z
  rw [invLFT, linFracTransExt_coe, if_neg (by simpa using hz), OnePoint.coe_eq_coe]
  unfold linFracTrans; ring
}

/--
  §III.6 **The Key Algebraic Link**:
  When `c ≠ 0` and `c * z + d ≠ 0`, `(a * z + b) / (c * z + d) = (b - a * d / c) / (c * z + d) + a / c`.
-/
lemma linFracTrans_key_link (a b c d z : ℂ) (hc : c ≠ 0) (h_den : c * z + d ≠ 0) :
    linFracTrans a b c d z = (b - a * d / c) / (c * z + d) + a / c := by
{
  -- Combine fractions on the RHS using `c ≠ 0` and `c * z + d ≠ 0`
  unfold linFracTrans
  rw [div_add_div _ _ h_den hc, div_eq_div_iff h_den (mul_ne_zero h_den hc)]
  have h_c : a * d / c * c = a * d := div_mul_cancel₀ (a * d) hc
  linear_combination (c * z + d) * h_c
}

/--
  §III.6 Affine decomposition (`c = 0`): `linFracTransExt a b 0 d = transLFT (b / d) ∘ scaleLFT (a / d)`.
-/
lemma linFracTransExt_decomp_c_zero (a b d : ℂ) (hd : d ≠ 0) :
    linFracTransExt a b 0 d = transLFT (b / d) ∘ scaleLFT (a / d) := by
{
  -- Verify agreement at ∞ and at every finite z : ℂ
  ext w; cases w with
  | infty => simp [linFracTransExt_infty]
  | coe z =>
    rw [linFracTransExt_coe, if_neg (by simpa using hd)]
    simp only [Function.comp_apply, scaleLFT_coe, transLFT_coe, OnePoint.coe_eq_coe]
    unfold linFracTrans; field_simp [hd]; ring
}

/--
  §III.6 Non-affine decomposition (`c ≠ 0`) via `linFracTrans_key_link`:
  `linFracTransExt a b c d = transLFT (a / c) ∘ scaleLFT (b - a * d / c) ∘ invLFT ∘ transLFT d ∘ scaleLFT c`.
-/
lemma linFracTransExt_decomp_c_ne_zero (a b c d : ℂ) (hc : c ≠ 0) :
    linFracTransExt a b c d =
      transLFT (a / c) ∘ scaleLFT (b - a * d / c) ∘ invLFT ∘ transLFT d ∘ scaleLFT c := by
{
  -- Verify agreement at ∞, at the pole c * z + d = 0, and away from the pole
  ext w; cases w with
  | infty => rw [linFracTransExt_infty, if_neg hc]; simp
  | coe z =>
    rw [linFracTransExt_coe]
    simp only [Function.comp_apply, scaleLFT_coe, transLFT_coe]
    by_cases h_den : c * z + d = 0
    · rw [if_pos h_den, h_den, invLFT_zero, scaleLFT_infty, transLFT_infty]
    · rw [if_neg h_den, invLFT_coe_of_ne_zero h_den, scaleLFT_coe, transLFT_coe, OnePoint.coe_eq_coe]
      rw [linFracTrans_key_link a b c d z hc h_den]; ring
}

/--
  §III.6 Inductive predicate for maps on `OnePoint ℂ` generated by the four elementary maps:
  dilations (`r > 0`), rotations (`‖u‖ = 1`), translations (`β ∈ ℂ`), and inversion (`z ↦ 1 / z`).
-/
inductive GeneratedByFourElementary : (OnePoint ℂ → OnePoint ℂ) → Prop
  | dilation (r : ℝ) (hr : 0 < r) : GeneratedByFourElementary (scaleLFT (r : ℂ))
  | rotation (u : ℂ) (hu : ‖u‖ = 1) : GeneratedByFourElementary (scaleLFT u)
  | translation (β : ℂ) : GeneratedByFourElementary (transLFT β)
  | inversion : GeneratedByFourElementary invLFT
  | comp {φ ψ : OnePoint ℂ → OnePoint ℂ} :
      GeneratedByFourElementary φ → GeneratedByFourElementary ψ →
      GeneratedByFourElementary (φ ∘ ψ)

/--
  Every non-zero complex scaling `scaleLFT α` (`α ≠ 0`) factors into a dilation by `‖α‖ > 0`
  and a rotation by `α / ‖α‖` (`‖α / ‖α‖‖ = 1`).
-/
lemma generatedByFourElementary_scaleLFT {α : ℂ} (hα : α ≠ 0) :
    GeneratedByFourElementary (scaleLFT α) := by
{
  have h_pos : 0 < ‖α‖ := norm_pos_iff.mpr hα
  have h_norm_ne : (‖α‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr h_pos.ne'
  have hu : ‖α / (‖α‖ : ℂ)‖ = 1 := by
    rw [norm_div, Complex.norm_real, Real.norm_of_nonneg h_pos.le, div_self h_pos.ne']
  -- Show scaleLFT α = scaleLFT ‖α‖ ∘ scaleLFT (α / ‖α‖)
  have h_eq : scaleLFT α = scaleLFT (‖α‖ : ℂ) ∘ scaleLFT (α / (‖α‖ : ℂ)) := by
    ext w; cases w with
    | infty => simp
    | coe z =>
      simp only [Function.comp_apply, scaleLFT_coe, OnePoint.coe_eq_coe]
      rw [← mul_assoc, mul_div_cancel₀ _ h_norm_ne]
  rw [h_eq]
  exact GeneratedByFourElementary.comp
    (GeneratedByFourElementary.dilation ‖α‖ h_pos)
    (GeneratedByFourElementary.rotation (α / (‖α‖ : ℂ)) hu)
}

/--
  §III.6 **Theorem III_6 (Elementary Decomposition of `GL(2, ℂ)`)**:
  By translating between `g ∈ GL (Fin 2) ℂ` and `linFracTransExt` via `moebius_eq_linFracTransExt`
  and applying `linFracTransExt_decomp_c_zero` (`c = 0`) or `linFracTransExt_decomp_c_ne_zero`
  (`c ≠ 0`, via the key link `(b - a * d / c) / (c * z + d) + a / c`), every `g ∈ GL (Fin 2) ℂ`
  is generated by the four elementary maps.
-/
theorem III_6 (g : GL (Fin 2) ℂ) : GeneratedByFourElementary (g • ·) := by
{
  -- Extract a * d - b * c ≠ 0 from det g ≠ 0 and translate (g • ·) to linFracTransExt
  set a := g 0 0; set b := g 0 1; set c := g 1 0; set d := g 1 1
  have h_det : a * d - b * c ≠ 0 := by
    have h_ne : (g : Matrix (Fin 2) (Fin 2) ℂ).det ≠ 0 := g.det.ne_zero
    rwa [Matrix.det_fin_two] at h_ne
  have h_moeb : (g • ·) = linFracTransExt a b c d := funext (moebius_eq_linFracTransExt g)
  rw [h_moeb]
  -- Split into Case 1 (c = 0) and Case 2 (c ≠ 0)
  by_cases hc : c = 0
  · -- Case 1 (c = 0): linFracTransExt a b 0 d = transLFT (b / d) ∘ scaleLFT (a / d)
    have h_ad : a * d ≠ 0 := by simpa [hc] using h_det
    rw [hc, linFracTransExt_decomp_c_zero a b d (right_ne_zero_of_mul h_ad)]
    exact GeneratedByFourElementary.comp (GeneratedByFourElementary.translation (b / d))
      (generatedByFourElementary_scaleLFT (div_ne_zero (left_ne_zero_of_mul h_ad) (right_ne_zero_of_mul h_ad)))
  · -- Case 2 (c ≠ 0): 5-step decomposition via (b - a * d / c) / (c * z + d) + a / c
    have h_scale_ne : b - a * d / c ≠ 0 := by
      intro h0; apply h_det
      have h_c : a * d / c * c = a * d := div_mul_cancel₀ (a * d) hc
      linear_combination -h_c - c * h0
    rw [linFracTransExt_decomp_c_ne_zero a b c d hc]
    exact GeneratedByFourElementary.comp (GeneratedByFourElementary.translation (a / c))
      (GeneratedByFourElementary.comp (generatedByFourElementary_scaleLFT h_scale_ne)
        (GeneratedByFourElementary.comp GeneratedByFourElementary.inversion
          (GeneratedByFourElementary.comp (GeneratedByFourElementary.translation d)
            (generatedByFourElementary_scaleLFT hc))))
}

/-!
  §III.7–§III.9 Cross-Ratio Formula, Clines (Circles and Lines), and Cline Preservation
-/

/--
  §III.7 Explicit rational formula for the cross-ratio `(z₁, z₂, z₃, z₄)` of four finite complex
  numbers `z₁, z₂, z₃, z₄ ∈ ℂ`:
  `crossRatioFin z₁ z₂ z₃ z₄ = ((z₄ - z₂) * (z₃ - z₁)) / ((z₄ - z₁) * (z₃ - z₂))`.
  As a function of `z₄`, this is the linear-fractional transformation mapping
  `z₁ ↦ ∞`, `z₂ ↦ 0`, and `z₃ ↦ 1`.
-/
noncomputable def crossRatioFin (z₁ z₂ z₃ z₄ : ℂ) : ℂ :=
  ((z₄ - z₂) * (z₃ - z₁)) / ((z₄ - z₁) * (z₃ - z₂))

/--
  §III.7 Expressing the cross-ratio map `z ↦ crossRatioFin z₁ z₂ z₃ z` as `linFracTrans a b c d z`
  with `a = z₃ - z₁`, `b = -z₂ * (z₃ - z₁)`, `c = z₃ - z₂`, `d = -z₁ * (z₃ - z₂)`.
-/
lemma crossRatioFin_eq_linFracTrans (z₁ z₂ z₃ z₄ : ℂ) :
    crossRatioFin z₁ z₂ z₃ z₄ =
      linFracTrans (z₃ - z₁) (-z₂ * (z₃ - z₁)) (z₃ - z₂) (-z₁ * (z₃ - z₂)) z₄ := by
{
  unfold crossRatioFin linFracTrans
  congr 1 <;> ring
}

/--
  §III.7 Non-vanishing determinant of the cross-ratio linear-fractional transformation
  when `z₁, z₂, z₃ ∈ ℂ` are pairwise distinct:
  `a * d - b * c = (z₁ - z₂) * (z₁ - z₃) * (z₂ - z₃) ≠ 0`.
-/
lemma crossRatioFin_det_ne_zero {z₁ z₂ z₃ : ℂ}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    (z₃ - z₁) * (-z₁ * (z₃ - z₂)) - (-z₂ * (z₃ - z₁)) * (z₃ - z₂) ≠ 0 := by
{
  have h_fac : (z₃ - z₁) * (-z₁ * (z₃ - z₂)) - (-z₂ * (z₃ - z₁)) * (z₃ - z₂) =
      (z₂ - z₁) * (z₃ - z₁) * (z₃ - z₂) := by
  {
    ring
  }
  rw [h_fac]
  exact mul_ne_zero (mul_ne_zero (sub_ne_zero.mpr h12.symm) (sub_ne_zero.mpr h13.symm))
    (sub_ne_zero.mpr h23.symm)
}

/--
  §III.7 The extended linear-fractional transformation associated with four finite points
  `z₁, z₂, z₃, z₄ ∈ ℂ` maps `z₁ ↦ ∞`, `z₂ ↦ 0`, and `z₃ ↦ 1`.
-/
lemma crossRatioFin_maps_std {z₁ z₂ z₃ : ℂ}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    let φ := linFracTransExt (z₃ - z₁) (-z₂ * (z₃ - z₁)) (z₃ - z₂) (-z₁ * (z₃ - z₂))
    IsLinFracTrans φ ∧ φ (z₁ : ℂ) = ∞ ∧ φ (z₂ : ℂ) = (0 : ℂ) ∧ φ (z₃ : ℂ) = (1 : ℂ) := by
{
  dsimp only
  have h32 : z₃ - z₂ ≠ 0 := sub_ne_zero.mpr h23.symm
  have h21 : z₂ - z₁ ≠ 0 := sub_ne_zero.mpr h12.symm
  have h31 : z₃ - z₁ ≠ 0 := sub_ne_zero.mpr h13.symm
  refine ⟨⟨_, _, _, _, crossRatioFin_det_ne_zero h12 h13 h23, rfl⟩, ?_, ?_, ?_⟩
  · -- At z₁, the denominator (z₃ - z₂) * z₁ - z₁ * (z₃ - z₂) = 0 vanishes
    rw [linFracTransExt_coe, if_pos (by ring)]
  · -- At z₂, the denominator is (z₃ - z₂) * (z₂ - z₁) ≠ 0 and numerator is 0
    have h_den2 : (z₃ - z₂) * z₂ + -z₁ * (z₃ - z₂) ≠ 0 := by
    {
      have h_eq : (z₃ - z₂) * z₂ + -z₁ * (z₃ - z₂) = (z₃ - z₂) * (z₂ - z₁) := by ring
      rw [h_eq]
      exact mul_ne_zero h32 h21
    }
    rw [linFracTransExt_coe, if_neg h_den2, OnePoint.coe_eq_coe]
    unfold linFracTrans
    have h_num2 : (z₃ - z₁) * z₂ + -z₂ * (z₃ - z₁) = 0 := by ring
    rw [h_num2, zero_div]
  · -- At z₃, numerator and denominator both equal (z₃ - z₁) * (z₃ - z₂) ≠ 0
    have h_den3 : (z₃ - z₂) * z₃ + -z₁ * (z₃ - z₂) ≠ 0 := by
    {
      have h_eq : (z₃ - z₂) * z₃ + -z₁ * (z₃ - z₂) = (z₃ - z₂) * (z₃ - z₁) := by ring
      rw [h_eq]
      exact mul_ne_zero h32 h31
    }
    rw [linFracTransExt_coe, if_neg h_den3, OnePoint.coe_eq_coe]
    unfold linFracTrans
    have h_eq3 : (z₃ - z₁) * z₃ + -z₂ * (z₃ - z₁) = (z₃ - z₂) * z₃ + -z₁ * (z₃ - z₂) := by ring
    rw [h_eq3, div_self h_den3]
}

/--
  §III.7 Agreement between the abstract spherical cross-ratio `cross_ratio_Cinfty` and the
  explicit finite rational formula `crossRatioFin` when `z₁, z₂, z₃, z₄ ∈ ℂ` with `z₄ ≠ z₁`.
-/
theorem cross_ratio_Cinfty_coe_eq {z₁ z₂ z₃ z₄ : ℂ}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) (h41 : z₄ ≠ z₁) :
    cross_ratio_Cinfty (z₁ : OnePoint ℂ) (z₂ : OnePoint ℂ) (z₃ : OnePoint ℂ) (z₄ : OnePoint ℂ) =
      (crossRatioFin z₁ z₂ z₃ z₄ : OnePoint ℂ) := by
{
  have h12' : (z₁ : OnePoint ℂ) ≠ (z₂ : OnePoint ℂ) := fun h => h12 (OnePoint.coe_eq_coe.mp h)
  have h13' : (z₁ : OnePoint ℂ) ≠ (z₃ : OnePoint ℂ) := fun h => h13 (OnePoint.coe_eq_coe.mp h)
  have h23' : (z₂ : OnePoint ℂ) ≠ (z₃ : OnePoint ℂ) := fun h => h23 (OnePoint.coe_eq_coe.mp h)
  rw [cross_ratio_Cinfty_eq_of_maps h12' h13' h23' (crossRatioFin_maps_std h12 h13 h23)]
  have h_den : (z₃ - z₂) * z₄ + -z₁ * (z₃ - z₂) ≠ 0 := by
  {
    have h_eq : (z₃ - z₂) * z₄ + -z₁ * (z₃ - z₂) = (z₃ - z₂) * (z₄ - z₁) := by ring
    rw [h_eq]
    exact mul_ne_zero (sub_ne_zero.mpr h23.symm) (sub_ne_zero.mpr h41)
  }
  rw [linFracTransExt_coe, if_neg h_den, crossRatioFin_eq_linFracTrans]
}

/--
  §III.8 The extended real axis `ℝ ∪ {∞}` inside `OnePoint ℂ`:
  consists of `∞` together with all finite points `(z : ℂ)` whose imaginary part vanishes (`z.im = 0`).
-/
def extendedRealAxis : Set (OnePoint ℂ) :=
  {w : OnePoint ℂ | w = ∞ ∨ ∃ z : ℂ, w = (z : ℂ) ∧ z.im = 0}

/--
  Characterization of when a finite point `(z : ℂ)` belongs to `extendedRealAxis`:
  `(z : OnePoint ℂ) ∈ extendedRealAxis ↔ z.im = 0`.
-/
@[simp] lemma coe_mem_extendedRealAxis_iff (z : ℂ) :
    (z : OnePoint ℂ) ∈ extendedRealAxis ↔ z.im = 0 := by
{
  simp only [extendedRealAxis, Set.mem_setOf_eq, OnePoint.coe_ne_infty, OnePoint.coe_eq_coe,
    false_or]
  exact ⟨fun ⟨w, hw, him⟩ => hw.symm ▸ him, fun him => ⟨z, rfl, him⟩⟩
}

/--
  The point at infinity `∞` belongs to `extendedRealAxis`.
-/
@[simp] lemma infty_mem_extendedRealAxis : (∞ : OnePoint ℂ) ∈ extendedRealAxis := by
{
  exact Or.inl rfl
}

@[simp] lemma star_re (z : ℂ) : (star z).re = z.re := by { rfl }
@[simp] lemma star_im (z : ℂ) : (star z).im = -z.im := by { rfl }

/--
  §III.8–§III.9 Sarason's general algebraic locus of a circle or line (cline) in `OnePoint ℂ`:
  Given real parameters `α, γ ∈ ℝ` and a complex parameter `β ∈ ℂ` (satisfying `‖β‖ ^ 2 > α * γ`),
  - a finite point `(z : ℂ)` lies on `clineLocus α β γ` iff `α * ‖z‖ ^ 2 + 2 * (star β * z).re + γ = 0`;
  - the point `∞` lies on `clineLocus α β γ` iff `α = 0` (the Euclidean line case).
-/
def clineLocus (α : ℝ) (β : ℂ) (γ : ℝ) : Set (OnePoint ℂ) :=
  {w : OnePoint ℂ | match w with
    | ∞ => α = 0
    | (z : ℂ) => α * ‖z‖ ^ 2 + 2 * (star β * z).re + γ = 0}

/--
  §III.8–§III.9 Predicate `IsCline S` stating that `S ⊆ OnePoint ℂ` is a non-degenerate cline
  (a circle on the Riemann sphere, corresponding in `ℂ` to either a Euclidean circle when `α ≠ 0`
  or a Euclidean line together with `∞` when `α = 0`).
-/
def IsCline (S : Set (OnePoint ℂ)) : Prop :=
  ∃ (α : ℝ) (β : ℂ) (γ : ℝ), α * γ < ‖β‖ ^ 2 ∧ S = clineLocus α β γ

/--
  §III.8 Every Euclidean circle `{z ∈ ℂ : ‖z - z₀‖ = r}` (`r > 0`) is a cline (`α = 1`, `β = -z₀`,
  `γ = ‖z₀‖ ^ 2 - r ^ 2`, with `‖β‖ ^ 2 - α * γ = r ^ 2 > 0`).
-/
lemma clineLocus_circle (z₀ : ℂ) (r : ℝ) (z : ℂ) :
    ((z : OnePoint ℂ) ∈ clineLocus 1 (-z₀) (‖z₀‖ ^ 2 - r ^ 2)) ↔ ‖z - z₀‖ ^ 2 = r ^ 2 := by
{
  simp only [clineLocus, Set.mem_setOf_eq]
  have h_norm : ‖z - z₀‖ ^ 2 = ‖z‖ ^ 2 + 2 * (star (-z₀) * z).re + ‖z₀‖ ^ 2 := by
  {
    simp only [Complex.sq_norm, Complex.normSq_apply, star_neg, Complex.mul_re,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, star_re, star_im]
    ring
  }
  constructor <;> intro h <;> linarith
}

/--
  §III.8 The extended real axis `extendedRealAxis` is a cline (`α = 0`, `β = i / 2`, `γ = 0`).
-/
lemma isCline_extendedRealAxis : IsCline extendedRealAxis := by
{
  refine ⟨0, Complex.I / 2, 0, ?_, ?_⟩
  · have h_norm : ‖Complex.I / (2 : ℂ)‖ = 1 / 2 := by simp
    rw [h_norm]
    norm_num
  · ext w
    cases w with
    | infty =>
      simp [extendedRealAxis, clineLocus]
    | coe z =>
      simp only [coe_mem_extendedRealAxis_iff, clineLocus, Set.mem_setOf_eq, zero_mul,
        zero_add, add_zero]
      have h_re : 2 * (star (Complex.I / 2) * z).re = z.im := by
      {
        simp only [Complex.mul_re, star_re, star_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
          Complex.I_re, Complex.I_im]
        ring
      }
      rw [h_re]
}

/--
  §III.8 Key algebraic identity for inversion `w = 1 / z` on a cline locus:
  For `z ≠ 0`, `α * ‖1 / z‖ ^ 2 + 2 * (star β * (1 / z)).re + γ =
  (γ * ‖z‖ ^ 2 + 2 * (star (star β) * z).re + α) / ‖z‖ ^ 2`.
-/
lemma cline_inversion_identity (α γ : ℝ) (β z : ℂ) (hz : z ≠ 0) :
    α * ‖1 / z‖ ^ 2 + 2 * (star β * (1 / z)).re + γ =
      (γ * ‖z‖ ^ 2 + 2 * (star (star β) * z).re + α) / ‖z‖ ^ 2 := by
{
  have h_nsq : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have h_inv_re : (star β * (1 / z)).re = (star (star β) * z).re / ‖z‖ ^ 2 := by
  {
    rw [star_star, one_div]
    simp only [Complex.mul_re, Complex.inv_re, Complex.inv_im, ← Complex.sq_norm,
      star_re, star_im]
    ring
  }
  rw [norm_div, norm_one, div_pow, one_pow, h_inv_re]
  field_simp [h_nsq]
  ring
}

/--
  §III.8 Preimage of `clineLocus α β γ` under inversion `invLFT` (`z ↦ 1 / z`) is
  `clineLocus γ (star β) α`: inversion swaps `α ↔ γ` and conjugates `β`.
-/
lemma preimage_invLFT_clineLocus (α : ℝ) (β : ℂ) (γ : ℝ) :
    invLFT ⁻¹' (clineLocus α β γ) = clineLocus γ (star β) α := by
{
  ext w
  cases w with
  | infty =>
    simp [clineLocus, invLFT_infty]
  | coe z =>
    by_cases hz : z = 0
    · subst hz
      simp [clineLocus, invLFT_zero]
    · have h_nsq_pos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
      simp only [Set.mem_preimage, invLFT_coe_of_ne_zero hz, clineLocus, Set.mem_setOf_eq]
      rw [cline_inversion_identity α γ β z hz, div_eq_zero_iff]
      exact ⟨fun h => h.resolve_right h_nsq_pos.ne', fun h => Or.inl h⟩
}

/--
  §III.8 Preimage of a cline under `invLFT` is a cline.
-/
lemma IsCline.preimage_invLFT {S : Set (OnePoint ℂ)} (hS : IsCline S) :
    IsCline (invLFT ⁻¹' S) := by
{
  rcases hS with ⟨α, β, γ, h_disc, rfl⟩
  refine ⟨γ, star β, α, ?_, preimage_invLFT_clineLocus α β γ⟩
  rw [norm_star, mul_comm γ α]
  exact h_disc
}

/--
  §III.8 Preimage of `clineLocus α β γ` under complex scaling `scaleLFT a` (`a ≠ 0`) is
  `clineLocus (α * ‖a‖ ^ 2) (star a * β) γ`.
-/
lemma preimage_scaleLFT_clineLocus (α : ℝ) (β : ℂ) (γ : ℝ) {a : ℂ} (ha : a ≠ 0) :
    scaleLFT a ⁻¹' (clineLocus α β γ) = clineLocus (α * ‖a‖ ^ 2) (star a * β) γ := by
{
  ext w
  cases w with
  | infty =>
    simp [clineLocus, scaleLFT_infty, ha]
  | coe z =>
    simp only [Set.mem_preimage, scaleLFT_coe, clineLocus, Set.mem_setOf_eq]
    have h_alg : α * ‖a * z‖ ^ 2 + 2 * (star β * (a * z)).re + γ =
        (α * ‖a‖ ^ 2) * ‖z‖ ^ 2 + 2 * (star (star a * β) * z).re + γ := by
    {
      rw [norm_mul, mul_pow, star_mul, star_star]
      ring_nf
    }
    rw [h_alg]
}

/--
  §III.8 Preimage of a cline under `scaleLFT a` (`a ≠ 0`) is a cline.
-/
lemma IsCline.preimage_scaleLFT {S : Set (OnePoint ℂ)} (hS : IsCline S) {a : ℂ} (ha : a ≠ 0) :
    IsCline (scaleLFT a ⁻¹' S) := by
{
  rcases hS with ⟨α, β, γ, h_disc, rfl⟩
  have ha_sq : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
  refine ⟨α * ‖a‖ ^ 2, star a * β, γ, ?_, preimage_scaleLFT_clineLocus α β γ ha⟩
  rw [norm_mul, norm_star, mul_pow]
  nlinarith
}

/--
  §III.8 Algebraic expansion for the translated cline equation at `z + b`:
  `α * ‖z + b‖ ^ 2 + 2 * (star β * (z + b)).re + γ` equals
  `α * ‖z‖ ^ 2 + 2 * (star (β + α * b) * z).re + (α * ‖b‖ ^ 2 + 2 * (star β * b).re + γ)`.
-/
lemma cline_translation_identity (α γ : ℝ) (β b z : ℂ) :
    α * ‖z + b‖ ^ 2 + 2 * (star β * (z + b)).re + γ =
      α * ‖z‖ ^ 2 + 2 * (star (β + (α : ℂ) * b) * z).re +
        (α * ‖b‖ ^ 2 + 2 * (star β * b).re + γ) := by
{
  simp only [Complex.sq_norm, Complex.normSq_apply, star_add, star_mul,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    star_re, star_im, Complex.ofReal_re, Complex.ofReal_im]
  ring
}

/--
  §III.8 Discriminant invariance under translation `z ↦ z + b`:
  `‖β + α * b‖ ^ 2 - α * (α * ‖b‖ ^ 2 + 2 * (star β * b).re + γ) = ‖β‖ ^ 2 - α * γ`.
-/
lemma cline_translation_discriminant (α γ : ℝ) (β b : ℂ) :
    ‖β + (α : ℂ) * b‖ ^ 2 - α * (α * ‖b‖ ^ 2 + 2 * (star β * b).re + γ) =
      ‖β‖ ^ 2 - α * γ := by
{
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, star_re, star_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring
}

/--
  §III.8 Preimage of a cline under `transLFT b` (`z ↦ z + b`) is a cline.
-/
lemma IsCline.preimage_transLFT {S : Set (OnePoint ℂ)} (hS : IsCline S) (b : ℂ) :
    IsCline (transLFT b ⁻¹' S) := by
{
  rcases hS with ⟨α, β, γ, h_disc, rfl⟩
  refine ⟨α, β + (α : ℂ) * b, α * ‖b‖ ^ 2 + 2 * (star β * b).re + γ, ?_, ?_⟩
  · have h_id := cline_translation_discriminant α γ β b
    linarith
  · ext w
    cases w with
    | infty =>
      simp [clineLocus, transLFT_infty]
    | coe z =>
      simp only [Set.mem_preimage, transLFT_coe, clineLocus, Set.mem_setOf_eq]
      rw [cline_translation_identity α γ β b z]
}

/--
  §III.9 Every map generated by the four elementary transformations (`GeneratedByFourElementary φ`)
  preserves clines under preimage (`IsCline S → IsCline (φ ⁻¹' S)`).
-/
lemma GeneratedByFourElementary.preimage_isCline {φ : OnePoint ℂ → OnePoint ℂ}
    (hφ : GeneratedByFourElementary φ) {S : Set (OnePoint ℂ)} (hS : IsCline S) :
    IsCline (φ ⁻¹' S) := by
{
  induction hφ generalizing S with
  | dilation r hr =>
    exact hS.preimage_scaleLFT (Complex.ofReal_ne_zero.mpr hr.ne')
  | rotation u hu =>
    have hu_ne : u ≠ 0 := by
    {
      intro h0
      rw [h0, norm_zero] at hu
      exact zero_ne_one hu
    }
    exact hS.preimage_scaleLFT hu_ne
  | translation β =>
    exact hS.preimage_transLFT β
  | inversion =>
    exact hS.preimage_invLFT
  | comp _ _ ihφ ihψ =>
    rw [Set.preimage_comp]
    exact ihψ (ihφ hS)
}

/--
  §III.9 **Theorem III_9 (Möbius Transformations Preserve Circles and Lines / Clines)**:
  For every invertible 2×2 matrix `g ∈ GL (Fin 2) ℂ` and every cline `S ⊆ OnePoint ℂ`,
  both the preimage `(g • ·) ⁻¹' S` and the forward image `(g • ·) '' S` are clines in `OnePoint ℂ`.
-/
theorem III_9 (g : GL (Fin 2) ℂ) {S : Set (OnePoint ℂ)} (hS : IsCline S) :
    IsCline ((g • ·) ⁻¹' S) ∧ IsCline ((g • ·) '' S) := by
{
  refine ⟨(III_6 g).preimage_isCline hS, ?_⟩
  -- Since g • · is a group action, the forward image under g • · is the preimage under g⁻¹ • ·
  have h_img : (g • ·) '' S = (g⁻¹ • ·) ⁻¹' S := by
  {
    ext w
    simp only [Set.mem_image, Set.mem_preimage]
    exact ⟨fun ⟨z, hz, hw⟩ => by rw [← hw, inv_smul_smul]; exact hz,
      fun hw => ⟨g⁻¹ • w, hw, smul_inv_smul g w⟩⟩
  }
  rw [h_img]
  exact (III_6 g⁻¹).preimage_isCline hS
}

/--
  §III.9 **Cross-Ratio Reality Criterion for Cocircularity / Collinearity**:
  Given three distinct points `z₁, z₂, z₃ ∈ OnePoint ℂ`, the set of points `z₄ ∈ OnePoint ℂ`
  whose cross-ratio `cross_ratio_Cinfty z₁ z₂ z₃ z₄` lies in `extendedRealAxis` (`ℝ ∪ {∞}`)
  is a cline passing through `z₁, z₂, z₃`.
-/
theorem cross_ratio_real_isCline {z₁ z₂ z₃ : OnePoint ℂ}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    IsCline {z₄ : OnePoint ℂ | cross_ratio_Cinfty z₁ z₂ z₃ z₄ ∈ extendedRealAxis} := by
{
  obtain ⟨φ, hφ_spec, _⟩ := existsUnique_lft_infty_zero_one h12 h13 h23
  obtain ⟨g, hg⟩ := (isLinFracTrans_iff_gl2 φ).mp hφ_spec.1
  have h_set : {z₄ : OnePoint ℂ | cross_ratio_Cinfty z₁ z₂ z₃ z₄ ∈ extendedRealAxis} =
      (g • ·) ⁻¹' extendedRealAxis := by
  {
    ext z₄
    simp only [Set.mem_setOf_eq, Set.mem_preimage,
      cross_ratio_Cinfty_eq_of_maps h12 h13 h23 hφ_spec z₄, hg]
  }
  rw [h_set]
  exact (III_9 g isCline_extendedRealAxis).1
}

/-!
  §III.10 Symmetry Across Circles and Lines (Schwarz Reflection Preparation)
-/

/--
  §III.10 Extended complex conjugation `w ↦ w̄` on `OnePoint ℂ`:
  maps a finite complex number `(z : ℂ)` to `(star z : ℂ)` and fixes `∞`.
-/
def conjExt : OnePoint ℂ → OnePoint ℂ
  | ∞ => ∞
  | (z : ℂ) => (star z : ℂ)

@[simp] lemma conjExt_infty : conjExt ∞ = ∞ := rfl
@[simp] lemma conjExt_coe (z : ℂ) : conjExt (z : ℂ) = (star z : ℂ) := rfl

/--
  §III.10 `conjExt` is an involution on `OnePoint ℂ`: `conjExt (conjExt w) = w`.
-/
@[simp] lemma conjExt_involutive (w : OnePoint ℂ) : conjExt (conjExt w) = w := by
{
  cases w with
  | infty => rfl
  | coe z => simp
}

/--
  §III.10 A point `w ∈ OnePoint ℂ` is fixed by `conjExt` if and only if `w ∈ extendedRealAxis`.
-/
lemma conjExt_fixed_iff (w : OnePoint ℂ) :
    conjExt w = w ↔ w ∈ extendedRealAxis := by
{
  cases w with
  | infty =>
    simp [extendedRealAxis]
  | coe z =>
    simp only [conjExt_coe, OnePoint.coe_eq_coe, coe_mem_extendedRealAxis_iff]
    rw [Complex.ext_iff, star_re, star_im]
    exact ⟨fun ⟨_, h⟩ => by linarith, fun h => ⟨rfl, by linarith⟩⟩
}

/--
  §III.10 Reflection (inversion) `z* = z₀ + R² / conj(z - z₀)` across the circle
  `{z ∈ ℂ : ‖z - z₀‖ = R}` in the complex plane `ℂ`.
-/
noncomputable def circleReflect (z₀ : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  z₀ + (R ^ 2 : ℂ) / star (z - z₀)

/--
  §III.10 Extended reflection `z*` across the circle `{z ∈ ℂ : ‖z - z₀‖ = R}` on `OnePoint ℂ`:
  interchanges the center `(z₀ : ℂ)` and `∞`, and maps `(z : ℂ)` (`z ≠ z₀`) to
  `z₀ + R² / conj(z - z₀)`.
-/
noncomputable def circleReflectExt (z₀ : ℂ) (R : ℝ) : OnePoint ℂ → OnePoint ℂ
  | ∞ => (z₀ : ℂ)
  | (z : ℂ) => if z = z₀ then ∞ else (circleReflect z₀ R z : ℂ)

/--
  §III.10 For `R ≠ 0` and `z ≠ z₀`, `circleReflect z₀ R z ≠ z₀` and
  `circleReflect z₀ R (circleReflect z₀ R z) = z`.
-/
lemma circleReflect_involutive (z₀ : ℂ) {R : ℝ} (hR : R ≠ 0) {z : ℂ} (hz : z ≠ z₀) :
    circleReflect z₀ R z ≠ z₀ ∧ circleReflect z₀ R (circleReflect z₀ R z) = z := by
{
  have hR2 : (R : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hR)
  have h_sub : star (z - z₀) ≠ 0 := star_ne_zero.mpr (sub_ne_zero.mpr hz)
  have h_ne : circleReflect z₀ R z ≠ z₀ := by
  {
    unfold circleReflect
    intro h_eq
    have h0 : (R : ℂ) ^ 2 / star (z - z₀) = 0 := by linear_combination h_eq
    exact div_ne_zero hR2 h_sub h0
  }
  refine ⟨h_ne, ?_⟩
  unfold circleReflect
  have h_star_R2 : star ((R : ℂ) ^ 2) = (R : ℂ) ^ 2 := by
  {
    rw [star_pow, Complex.star_def, Complex.conj_ofReal]
  }
  rw [add_sub_cancel_left, star_div₀, star_star, h_star_R2, div_div_cancel₀ hR2, add_sub_cancel]
}

/--
  §III.10 For `R ≠ 0`, `circleReflectExt z₀ R` is an involution on `OnePoint ℂ`: `(z*)* = z`.
-/
theorem circleReflectExt_involutive (z₀ : ℂ) {R : ℝ} (hR : R ≠ 0) (w : OnePoint ℂ) :
    circleReflectExt z₀ R (circleReflectExt z₀ R w) = w := by
{
  cases w with
  | infty =>
    simp [circleReflectExt]
  | coe z =>
    by_cases hz : z = z₀
    · subst hz; simp [circleReflectExt]
    · obtain ⟨h_ne, h_inv⟩ := circleReflect_involutive z₀ hR hz
      change circleReflectExt z₀ R (if z = z₀ then ∞ else (circleReflect z₀ R z : OnePoint ℂ)) = (z : OnePoint ℂ)
      rw [if_neg hz]
      change (if circleReflect z₀ R z = z₀ then ∞ else (circleReflect z₀ R (circleReflect z₀ R z) : OnePoint ℂ)) = (z : OnePoint ℂ)
      rw [if_neg h_ne, h_inv]
}

/--
  §III.10 A finite point `z ≠ z₀` is fixed by `circleReflect z₀ R` (`R > 0`) if and only if
  `z` lies on the circle `‖z - z₀‖ = R`.
-/
theorem circleReflect_fixed_iff (z₀ z : ℂ) {R : ℝ} (hR : 0 < R) (hz : z ≠ z₀) :
    circleReflect z₀ R z = z ↔ ‖z - z₀‖ = R := by
{
  have h_sub : star (z - z₀) ≠ 0 := star_ne_zero.mpr (sub_ne_zero.mpr hz)
  unfold circleReflect
  have h_add : z₀ + (R : ℂ) ^ 2 / star (z - z₀) = z ↔ (R : ℂ) ^ 2 / star (z - z₀) = z - z₀ := by
  {
    constructor <;> intro h <;> linear_combination h
  }
  have h_mul_star : (z - z₀) * star (z - z₀) = (‖z - z₀‖ : ℂ) ^ 2 := by
  {
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  }
  rw [h_add, div_eq_iff h_sub, h_mul_star, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    Complex.ofReal_inj]
  have h_nonneg : 0 ≤ ‖z - z₀‖ := norm_nonneg (z - z₀)
  exact ⟨fun h => by nlinarith [sq_nonneg (‖z - z₀‖ - R)], fun h => by rw [h]⟩
}

/--
  §III.10 **Sarason's Cross-Ratio Definition of Symmetry with Respect to a Cline**:
  Two points `z, z_star ∈ OnePoint ℂ` are symmetric with respect to the cline through three
  distinct points `z₁, z₂, z₃ ∈ OnePoint ℂ` if
  `cross_ratio_Cinfty z₁ z₂ z₃ z_star = conjExt (cross_ratio_Cinfty z₁ z₂ z₃ z)`.
-/
def SymmetricWrtTriple (z₁ z₂ z₃ z z_star : OnePoint ℂ) : Prop :=
  cross_ratio_Cinfty z₁ z₂ z₃ z_star = conjExt (cross_ratio_Cinfty z₁ z₂ z₃ z)

/--
  §III.10 **Theorem III_10 (The Symmetry Principle for Linear-Fractional Transformations)**:
  Every linear-fractional transformation `ψ` (`IsLinFracTrans ψ`) preserves symmetry with respect
  to clines: if `z` and `z_star` are symmetric with respect to `(z₁, z₂, z₃)`, then `ψ z` and
  `ψ z_star` are symmetric with respect to `(ψ z₁, ψ z₂, ψ z₃)`.
-/
theorem III_10_symmetry_principle (ψ : OnePoint ℂ → OnePoint ℂ) (hψ : IsLinFracTrans ψ)
    {z₁ z₂ z₃ : OnePoint ℂ} (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (z z_star : OnePoint ℂ) (h_sym : SymmetricWrtTriple z₁ z₂ z₃ z z_star) :
    SymmetricWrtTriple (ψ z₁) (ψ z₂) (ψ z₃) (ψ z) (ψ z_star) := by
{
  -- By Cross-Ratio Invariance (Exercise III.5.2), ψ preserves both cross-ratios identically
  unfold SymmetricWrtTriple at *
  rw [exercise_III_5_2 ψ hψ z₁ z₂ z₃ z_star h12 h13 h23,
      exercise_III_5_2 ψ hψ z₁ z₂ z₃ z h12 h13 h23]
  exact h_sym
}

/-!
  §III.11–§III.12 The Cayley Transform, the Herglotz Kernel, and Disk Automorphisms `Aut(𝔻)`
-/

/-- §III.11 The open upper half-plane `ℍ = {z ∈ ℂ : Im z > 0}`. -/
def upperHalfPlaneSet : Set ℂ := {z : ℂ | 0 < z.im}

/-- §III.11 The open right half-plane `{w ∈ ℂ : Re w > 0}`. -/
def rightHalfPlaneSet : Set ℂ := {w : ℂ | 0 < w.re}

/-- §III.11 The open unit disk `𝔻 = {z ∈ ℂ : ‖z‖ < 1}`. -/
def unitDiskSet : Set ℂ := {z : ℂ | ‖z‖ < 1}

/-- §III.11 The unit circle `∂𝔻 = {z ∈ ℂ : ‖z‖ = 1}`. -/
def unitCircleSet : Set ℂ := {z : ℂ | ‖z‖ = 1}

/--
  §III.11 **The Cayley Transform** `w = (z - i) / (z + i)` mapping the upper half-plane `ℍ`
  onto the open unit disk `𝔻`.
-/
noncomputable def cayleyMap (z : ℂ) : ℂ :=
  linFracTrans 1 (-Complex.I) 1 Complex.I z

/--
  §III.11 **The Inverse Cayley Transform** `z = i * (1 + w) / (1 - w)` mapping the open unit disk `𝔻`
  onto the upper half-plane `ℍ`.
-/
noncomputable def cayleyInvMap (w : ℂ) : ℂ :=
  linFracTrans Complex.I Complex.I (-1) 1 w

/--
  §III.11 Fundamental norm identity for the Cayley numerator and denominator:
  `‖z + i‖ ^ 2 - ‖z - i‖ ^ 2 = 4 * z.im`.
-/
lemma cayley_norm_sq_diff (z : ℂ) :
    ‖z + Complex.I‖ ^ 2 - ‖z - Complex.I‖ ^ 2 = 4 * z.im := by
{
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  ring
}

/--
  §III.11 For any `z ∈ ℂ` with `z.im ≥ 0`, the Cayley denominator `z + i` is non-zero.
-/
lemma cayley_den_ne_zero {z : ℂ} (hz : 0 ≤ z.im) : z + Complex.I ≠ 0 := by
{
  intro h0
  have him := congrArg Complex.im h0
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
  linarith
}

/--
  §III.11 Fundamental radial identity for the Cayley transform:
  When `z + i ≠ 0`, `1 - ‖cayleyMap z‖ ^ 2 = (4 * z.im) / ‖z + i‖ ^ 2`.
-/
theorem cayleyMap_one_sub_norm_sq {z : ℂ} (h_den : z + Complex.I ≠ 0) :
    1 - ‖cayleyMap z‖ ^ 2 = (4 * z.im) / ‖z + Complex.I‖ ^ 2 := by
{
  have h_nsq : ‖z + Complex.I‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h_den)
  unfold cayleyMap linFracTrans
  have h_num : (1 : ℂ) * z + -Complex.I = z - Complex.I := by ring
  have h_den' : (1 : ℂ) * z + Complex.I = z + Complex.I := by ring
  rw [h_num, h_den', norm_div, div_pow, one_sub_div h_nsq, cayley_norm_sq_diff]
}

/--
  §III.11 The Cayley transform maps `ℍ` (`z.im > 0`) into `𝔻` (`‖cayleyMap z‖ < 1`),
  maps `z = i` to `0`, and maps the real axis (`z.im = 0`) into the unit circle `∂𝔻`.
-/
theorem III_11_cayley_maps :
    cayleyMap Complex.I = 0 ∧
    (∀ z ∈ upperHalfPlaneSet, cayleyMap z ∈ unitDiskSet) ∧
    (∀ x : ℝ, cayleyMap (x : ℂ) ∈ unitCircleSet) := by
{
  refine ⟨?_, ?_, ?_⟩
  · unfold cayleyMap linFracTrans
    have h_num : (1 : ℂ) * Complex.I + -Complex.I = 0 := by ring
    rw [h_num, zero_div]
  · intro z hz
    simp only [upperHalfPlaneSet, Set.mem_setOf_eq] at hz
    simp only [unitDiskSet, Set.mem_setOf_eq]
    have h_den : z + Complex.I ≠ 0 := cayley_den_ne_zero hz.le
    have h_pos : 0 < (4 * z.im) / ‖z + Complex.I‖ ^ 2 :=
      div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr h_den))
    have h_id := cayleyMap_one_sub_norm_sq h_den
    have h_norm_nonneg : 0 ≤ ‖cayleyMap z‖ := norm_nonneg _
    nlinarith [sq_nonneg (1 - ‖cayleyMap z‖)]
  · intro x
    simp only [unitCircleSet, Set.mem_setOf_eq]
    have h_im : (x : ℂ).im = 0 := Complex.ofReal_im x
    have h_den : (x : ℂ) + Complex.I ≠ 0 := cayley_den_ne_zero (le_of_eq h_im.symm)
    have h_id := cayleyMap_one_sub_norm_sq h_den
    rw [h_im, mul_zero, zero_div] at h_id
    have h_norm_nonneg : 0 ≤ ‖cayleyMap (x : ℂ)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖cayleyMap (x : ℂ)‖ - 1)]
}

/--
  §III.11 `cayleyInvMap` is the two-sided inverse of `cayleyMap`:
  for `z + i ≠ 0`, `cayleyInvMap (cayleyMap z) = z`, and for `1 - w ≠ 0`,
  `cayleyMap (cayleyInvMap w) = w`.
-/
theorem cayleyMap_inv {z w : ℂ} (hz : z + Complex.I ≠ 0) (hw : 1 - w ≠ 0) :
    cayleyInvMap (cayleyMap z) = z ∧ cayleyMap (cayleyInvMap w) = w := by
{
  have h2i : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  unfold cayleyMap cayleyInvMap linFracTrans
  have hz' : (1 : ℂ) * z + Complex.I ≠ 0 := by simpa using hz
  have hw' : (-1 : ℂ) * w + 1 ≠ 0 := by
  {
    intro h0; apply hw; linear_combination h0
  }
  refine ⟨?_, ?_⟩
  · field_simp [hz', h2i]
    ring
  · have h_den2 : (1 : ℂ) * ((Complex.I * w + Complex.I) / (-1 * w + 1)) + Complex.I =
        (2 * Complex.I) / (-1 * w + 1) := by
    {
      rw [one_mul, div_add' _ _ _ hw']
      congr 1
      ring
    }
    have h_num2 : (1 : ℂ) * ((Complex.I * w + Complex.I) / (-1 * w + 1)) + -Complex.I =
        (2 * Complex.I * w) / (-1 * w + 1) := by
    {
      rw [one_mul, div_add' _ _ _ hw']
      congr 1
      ring
    }
    rw [h_num2, h_den2, div_div_div_cancel_right₀ hw', mul_div_cancel_left₀ w h2i]
}

/--
  §III.11 **The Herglotz Kernel** `H(ζ, z) = (ζ + z) / (ζ - z)` mapping `z ∈ 𝔻` onto the
  right half-plane `{w ∈ ℂ : Re w > 0}` for `ζ ∈ ∂𝔻`.
-/
noncomputable def herglotzKernel (ζ z : ℂ) : ℂ :=
  (ζ + z) / (ζ - z)

/--
  §III.11 **The Poisson Kernel Identity via the Herglotz Kernel**:
  For any `ζ ∈ ∂𝔻` (`‖ζ‖ = 1`) and `z ≠ ζ`,
  `Re ((ζ + z) / (ζ - z)) = (1 - ‖z‖ ^ 2) / ‖ζ - z‖ ^ 2`.
-/
theorem herglotzKernel_re {ζ z : ℂ} (hζ : ‖ζ‖ = 1) :
    (herglotzKernel ζ z).re = (1 - ‖z‖ ^ 2) / ‖ζ - z‖ ^ 2 := by
{
  unfold herglotzKernel
  have h_ζ_sq : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by
  {
    have h1 : ‖ζ‖ ^ 2 = 1 := by rw [hζ, one_pow]
    rwa [Complex.sq_norm, Complex.normSq_apply] at h1
  }
  rw [Complex.div_re, ← Complex.sq_norm, Complex.sq_norm z, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  linear_combination (1 / ‖ζ - z‖ ^ 2) * h_ζ_sq
}

/--
  §III.11 **Properties of the Herglotz Kernel on `𝔻` and `∂𝔻`**:
  For `ζ ∈ ∂𝔻` (`‖ζ‖ = 1`):
  1. `herglotzKernel ζ 0 = 1`,
  2. For every `z ∈ 𝔻` (`‖z‖ < 1`), `Re (herglotzKernel ζ z) > 0` (maps `𝔻` into the right half-plane),
  3. For every `z ∈ ∂𝔻` (`‖z‖ = 1`), `Re (herglotzKernel ζ z) = 0` (purely imaginary on `∂𝔻 \ {ζ}`).
-/
theorem III_11_herglotz_properties {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    herglotzKernel ζ 0 = 1 ∧
    (∀ z ∈ unitDiskSet, 0 < (herglotzKernel ζ z).re) ∧
    (∀ z ∈ unitCircleSet, (herglotzKernel ζ z).re = 0) := by
{
  have hζ_ne : ζ ≠ 0 := by
  {
    intro h0; rw [h0, norm_zero] at hζ; exact zero_ne_one hζ
  }
  refine ⟨?_, ?_, ?_⟩
  · unfold herglotzKernel
    rw [add_zero, sub_zero, div_self hζ_ne]
  · intro z hz
    simp only [unitDiskSet, Set.mem_setOf_eq] at hz
    have h_ne : ζ - z ≠ 0 := by
    {
      intro h_sub
      have h_eq : ζ = z := sub_eq_zero.mp h_sub
      rw [← h_eq, hζ] at hz
      exact lt_irrefl 1 hz
    }
    rw [herglotzKernel_re hζ]
    have h_num_pos : 0 < 1 - ‖z‖ ^ 2 := by
    {
      have h_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
      nlinarith
    }
    exact div_pos h_num_pos (sq_pos_of_pos (norm_pos_iff.mpr h_ne))
  · intro z hz
    simp only [unitCircleSet, Set.mem_setOf_eq] at hz
    rw [herglotzKernel_re hζ, hz, one_pow, sub_self, zero_div]
}

/--
  §III.12 **Blaschke / Disk Automorphism Factor** `φ_a(z) = (z - a) / (1 - ā * z)` for `a ∈ 𝔻`.
-/
noncomputable def blaschkeFactor (a z : ℂ) : ℂ :=
  (z - a) / (1 - star a * z)

/--
  §III.12 General disk automorphism `diskAut λ a z = λ * (z - a) / (1 - ā * z)` for `‖λ‖ = 1` and `a ∈ 𝔻`.
-/
noncomputable def diskAut (u a z : ℂ) : ℂ :=
  u * blaschkeFactor a z

/--
  §III.12 **Fundamental Algebraic Identity for Disk Automorphisms**:
  `‖1 - ā * z‖ ^ 2 - ‖z - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2)`.
-/
theorem blaschke_norm_sq_diff (a z : ℂ) :
    ‖1 - star a * z‖ ^ 2 - ‖z - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
{
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, star_re, star_im]
  ring
}

/--
  §III.12 For `a ∈ 𝔻` (`‖a‖ < 1`) and `‖z‖ ≤ 1`, the denominator `1 - ā * z` is non-zero.
-/
lemma blaschke_den_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - star a * z ≠ 0 := by
{
  intro h0
  have h_eq : star a * z = 1 := (sub_eq_zero.mp h0).symm
  have h_norm : ‖star a * z‖ = 1 := by rw [h_eq, norm_one]
  rw [norm_mul, norm_star] at h_norm
  have ha_nonneg : 0 ≤ ‖a‖ := norm_nonneg a
  nlinarith
}

/--
  §III.12 **Radial Identity for `blaschkeFactor`**:
  When `1 - ā * z ≠ 0`,
  `1 - ‖blaschkeFactor a z‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - ā * z‖ ^ 2`.
-/
theorem blaschkeFactor_one_sub_norm_sq {a z : ℂ} (h_den : 1 - star a * z ≠ 0) :
    1 - ‖blaschkeFactor a z‖ ^ 2 =
      ((1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2)) / ‖1 - star a * z‖ ^ 2 := by
{
  have h_nsq : ‖1 - star a * z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h_den)
  unfold blaschkeFactor
  rw [norm_div, div_pow, one_sub_div h_nsq, blaschke_norm_sq_diff]
}

/--
  §III.12 **Theorem III_12 (Properties of Disk Automorphisms `blaschkeFactor a`)**:
  For every `a ∈ 𝔻` (`‖a‖ < 1`):
  1. `blaschkeFactor a a = 0` and `blaschkeFactor a 0 = -a`,
  2. `blaschkeFactor a` maps `𝔻` (`‖z‖ < 1`) into `𝔻` (`‖blaschkeFactor a z‖ < 1`),
  3. `blaschkeFactor a` maps `∂𝔻` (`‖z‖ = 1`) into `∂𝔻` (`‖blaschkeFactor a z‖ = 1`),
  4. `blaschkeFactor (-a)` is the inverse of `blaschkeFactor a` on `{z : ‖z‖ ≤ 1}`.
-/
theorem III_12_blaschke_properties {a : ℂ} (ha : ‖a‖ < 1) :
    blaschkeFactor a a = 0 ∧
    blaschkeFactor a 0 = -a ∧
    (∀ z ∈ unitDiskSet, blaschkeFactor a z ∈ unitDiskSet) ∧
    (∀ z ∈ unitCircleSet, blaschkeFactor a z ∈ unitCircleSet) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → blaschkeFactor (-a) (blaschkeFactor a z) = z) := by
{
  have ha_nonneg : 0 ≤ ‖a‖ := norm_nonneg a
  have ha_sq_pos : 0 < 1 - ‖a‖ ^ 2 := by nlinarith
  have ha_one_ne : (1 : ℂ) - star a * a ≠ 0 := by
  {
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_one, ← Complex.ofReal_pow,
      ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr ha_sq_pos.ne'
  }
  refine ⟨by unfold blaschkeFactor; rw [sub_self, zero_div],
          by unfold blaschkeFactor; simp, ?_, ?_, ?_⟩
  · intro z hz
    simp only [unitDiskSet, Set.mem_setOf_eq] at hz ⊢
    have h_den := blaschke_den_ne_zero ha hz.le
    have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
    have h_pos : 0 < ((1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2)) / ‖1 - star a * z‖ ^ 2 :=
      div_pos (mul_pos ha_sq_pos (by nlinarith)) (sq_pos_of_pos (norm_pos_iff.mpr h_den))
    have h_id := blaschkeFactor_one_sub_norm_sq h_den
    have h_norm_nonneg : 0 ≤ ‖blaschkeFactor a z‖ := norm_nonneg _
    nlinarith [sq_nonneg (1 - ‖blaschkeFactor a z‖)]
  · intro z hz
    simp only [unitCircleSet, Set.mem_setOf_eq] at hz ⊢
    have h_den := blaschke_den_ne_zero ha (le_of_eq hz)
    have h_id := blaschkeFactor_one_sub_norm_sq h_den
    rw [hz, one_pow, sub_self, mul_zero, zero_div] at h_id
    have h_norm_nonneg : 0 ≤ ‖blaschkeFactor a z‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖blaschkeFactor a z‖ - 1)]
  · intro z hz
    have h_den := blaschke_den_ne_zero ha hz
    unfold blaschkeFactor
    rw [star_neg, sub_neg_eq_add, neg_mul, sub_neg_eq_add]
    have h_num : (z - a) / (1 - star a * z) + a =
        (z * (1 - star a * a)) / (1 - star a * z) := by
    {
      rw [div_add' _ _ _ h_den]
      congr 1
      ring
    }
    have h_den2 : 1 + star a * ((z - a) / (1 - star a * z)) =
        (1 - star a * a) / (1 - star a * z) := by
    {
      rw [mul_div_assoc', add_div' _ _ _ h_den]
      congr 1
      ring
    }
    rw [h_num, h_den2, div_div_div_cancel_right₀ h_den, mul_div_cancel_right₀ z ha_one_ne]
}

/--
  §III.12 Complex derivative of `blaschkeFactor a` at any `z ∈ ℂ` with `1 - ā * z ≠ 0`:
  `(d/dz) ((z - a) / (1 - ā * z)) = (1 - ‖a‖ ^ 2) / (1 - ā * z) ^ 2`.
-/
theorem blaschkeFactor_hasDerivAt (a z : ℂ) (h_den : 1 - star a * z ≠ 0) :
    HasDerivAt (blaschkeFactor a) ((1 - (‖a‖ : ℂ) ^ 2) / (1 - star a * z) ^ 2) z := by
{
  have h_eq_lft : blaschkeFactor a = linFracTrans 1 (-a) (-star a) 1 := by
  {
    ext w
    unfold blaschkeFactor linFracTrans
    ring
  }
  have h_den' : (-star a) * z + 1 ≠ 0 := by
  {
    intro h0; apply h_den; linear_combination h0
  }
  rw [h_eq_lft]
  have h_deriv := linFracTrans_hasDerivAt 1 (-a) (-star a) 1 z h_den'
  have h_num : ((1 : ℂ) * 1 - (-a) * (-star a)) / ((-star a) * z + 1) ^ 2 =
      (1 - (‖a‖ : ℂ) ^ 2) / (1 - star a * z) ^ 2 := by
  {
    have h_aa : a * star a = (‖a‖ : ℂ) ^ 2 := by
    {
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    }
    congr 1
    · linear_combination -h_aa
    · ring
  }
  rwa [h_num] at h_deriv
}

/-!
  §III.13 Starlike Domains and Starlike Holomorphic Maps in Terms of Polar Angle θ.
  Connecting the polar coordinate operators `polar_partial_theta` and `polar_partial_r`
  from `Sarason/Definitions.lean` and the polar Cauchy–Riemann equations (`exercise_II_6_3`)
  and argument `arg` from `Sarason/Chapter2.lean` to starlike univalent functions and
  the Herglotz–Pommerenke logarithmic derivative representation of radial slit maps.
-/

/--
  §III.13 Polar coordinate point `z = r cos θ + i r sin θ` in `ℂ`, matching the
  `(p.1 * Real.cos p.2, p.1 * Real.sin p.2)` parameterization of `polar_partial_r`
  and `polar_partial_theta` in `Sarason/Definitions.lean`.
-/
noncomputable def polarPoint (r θ : ℝ) : ℂ :=
  ((r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * I

@[simp]
lemma polarPoint_re (r θ : ℝ) : (polarPoint r θ).re = r * Real.cos θ := by
{
  unfold polarPoint
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring
}

@[simp]
lemma polarPoint_im (r θ : ℝ) : (polarPoint r θ).im = r * Real.sin θ := by
{
  unfold polarPoint
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring
}

lemma polarPoint_scale (t r θ : ℝ) :
    polarPoint (t * r) θ = (t : ℂ) * polarPoint r θ := by
{
  apply Complex.ext
  · simp only [polarPoint_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · simp only [polarPoint_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
}

lemma polarPoint_norm_sq (r θ : ℝ) : ‖polarPoint r θ‖ ^ 2 = r ^ 2 := by
{
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, polarPoint_re, polarPoint_im]
  calc (r * Real.cos θ) * (r * Real.cos θ) + (r * Real.sin θ) * (r * Real.sin θ)
      = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
    _ = r ^ 2 * 1 := by rw [Real.cos_sq_add_sin_sq θ]
    _ = r ^ 2 := by ring
}

lemma polarPoint_norm_of_nonneg {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖polarPoint r θ‖ = r := by
{
  have h_sq := polarPoint_norm_sq r θ
  have h_sqrt := congrArg Real.sqrt h_sq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hr] at h_sqrt
}

lemma polarPoint_ne_zero_of_pos {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    polarPoint r θ ≠ 0 := by
{
  intro h0
  have h_norm := polarPoint_norm_of_nonneg hr.le θ
  rw [h0, norm_zero] at h_norm
  linarith
}

lemma polarPoint_mem_unitDiskSet {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    polarPoint r θ ∈ unitDiskSet := by
{
  simp only [unitDiskSet, Set.mem_setOf_eq]
  rw [polarPoint_norm_of_nonneg hr0 θ]
  exact hr1
}

lemma polarPoint_one_mem_unitCircleSet (θ : ℝ) :
    polarPoint 1 θ ∈ unitCircleSet := by
{
  simp only [unitCircleSet, Set.mem_setOf_eq]
  exact polarPoint_norm_of_nonneg zero_le_one θ
}

/--
  §III.13 Weierstrass `HasDerivAt_R_to_C_eps` derivative of the polar circle path
  `θ ↦ polarPoint r θ` with respect to the polar angle `θ`:
  `d/dθ (r cos θ + i r sin θ) = i * polarPoint r θ₀`.
-/
theorem polarPoint_hasDerivAt_theta_eps (r θ₀ : ℝ) :
    HasDerivAt_R_to_C_eps (fun θ => polarPoint r θ) (I * polarPoint r θ₀) θ₀ := by
{
  have h_x := ComplexAnalysis.R2.polar_partial_theta_is_deriv
    (u := fun p => 1 * p.1 + 0 * p.2) (ux₀ := 1) (uy₀ := 0) (r₀ := r) (θ₀ := θ₀) (by {
      have h0 := linear_hasFDerivAt_R2_eps 1 0 0 0 (r * Real.cos θ₀, r * Real.sin θ₀)
      simpa using h0
    })
  have h_y := ComplexAnalysis.R2.polar_partial_theta_is_deriv
    (u := fun p => 0 * p.1 + 1 * p.2) (ux₀ := 0) (uy₀ := 1) (r₀ := r) (θ₀ := θ₀) (by {
      have h0 := linear_hasFDerivAt_R2_eps 0 1 0 0 (r * Real.cos θ₀, r * Real.sin θ₀)
      simpa using h0
    })
  have h_iff_x := (HasDerivAt_RtoR2_eps_iff_R_to_C_eps _ _ θ₀).mp h_x
  have h_iff_y := (HasDerivAt_RtoR2_eps_iff_R_to_C_eps _ _ θ₀).mp h_y
  rw [← hasDerivAt_R_to_C_iff_eps] at h_iff_x h_iff_y ⊢
  have hx_clean : HasDerivAt (fun θ : ℝ => ((r * Real.cos θ : ℝ) : ℂ))
      (((-r * Real.sin θ₀ : ℝ) : ℂ)) θ₀ := by
  {
    convert h_iff_x using 1
    · ext θ; apply Complex.ext <;> simp
    · apply Complex.ext <;> simp
  }
  have hy_clean : HasDerivAt (fun θ : ℝ => ((r * Real.sin θ : ℝ) : ℂ))
      (((r * Real.cos θ₀ : ℝ) : ℂ)) θ₀ := by
  {
    convert h_iff_y using 1
    · ext θ; apply Complex.ext <;> simp
    · apply Complex.ext <;> simp
  }
  have h_comb := hx_clean.add (hy_clean.mul_const I)
  have h_val :
      (((-r * Real.sin θ₀ : ℝ) : ℂ)) + (((r * Real.cos θ₀ : ℝ) : ℂ)) * I =
      I * polarPoint r θ₀ := by
  {
    apply Complex.ext
    · simp only [polarPoint_re, polarPoint_im, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    · simp only [polarPoint_re, polarPoint_im, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
  }
  rw [← h_val]
  exact h_comb
}

/--
  Every complex number `z` is represented in polar coordinates by its modulus `‖z‖`
  and its principal argument `arg z` (`z = polarPoint ‖z‖ (arg z)`).
-/
lemma polarPoint_norm_arg (z : ℂ) : polarPoint ‖z‖ (arg z) = z := by
{
  by_cases hz : z = 0
  · subst hz
    apply Complex.ext <;> simp [polarPoint_re, polarPoint_im]
  · have h_norm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    apply Complex.ext
    · rw [polarPoint_re, Complex.cos_arg hz, mul_div_cancel₀ _ h_norm]
    · rw [polarPoint_im, Complex.sin_arg, mul_div_cancel₀ _ h_norm]
}

/--
  §III.13 Geometric definition of a starlike domain `Ω ⊆ ℂ` with respect to the origin `0`
  in terms of the polar angle `θ`: `0 ∈ Ω`, and along every ray of fixed polar angle `θ`,
  if `polarPoint r θ ∈ Ω` (`r ≥ 0`), then `polarPoint (t * r) θ ∈ Ω` for all `t ∈ [0, 1]`.
-/
def IsStarlikeDomain_theta (Ω : Set ℂ) : Prop :=
  (0 : ℂ) ∈ Ω ∧
  ∀ (r θ : ℝ), 0 ≤ r → polarPoint r θ ∈ Ω →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → polarPoint (t * r) θ ∈ Ω

/--
  Equivalence between the polar-angle definition `IsStarlikeDomain_theta Ω` and ray
  starlikeness using `arg z`: `0 ∈ Ω` and for every `z ∈ Ω` and `t ∈ [0, 1]`,
  `polarPoint (t * ‖z‖) (arg z) ∈ Ω`.
-/
theorem isStarlikeDomain_theta_iff_arg_ray (Ω : Set ℂ) :
    IsStarlikeDomain_theta Ω ↔
      ((0 : ℂ) ∈ Ω ∧ ∀ z ∈ Ω, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → polarPoint (t * ‖z‖) (arg z) ∈ Ω) := by
{
  constructor
  · rintro ⟨h0, hray⟩
    refine ⟨h0, fun z hz t ht0 ht1 => ?_⟩
    apply hray ‖z‖ (arg z) (norm_nonneg z)
    · rw [polarPoint_norm_arg]
      exact hz
    · exact ht0
    · exact ht1
  · rintro ⟨h0, harg⟩
    refine ⟨h0, fun r θ hr hmem t ht0 ht1 => ?_⟩
    have hz := harg (polarPoint r θ) hmem t ht0 ht1
    rw [polarPoint_norm_of_nonneg hr θ] at hz
    rw [polarPoint_scale, ← polarPoint_norm_arg (polarPoint r θ),
      polarPoint_norm_of_nonneg hr θ, ← polarPoint_scale]
    exact hz
}

/--
  §III.13 Angular rate of change `∂(arg f)/∂θ` of the image argument along the polar circle
  `p = (r, θ)` (`z = r cos θ + i r sin θ`), defined directly in terms of `polar_partial_theta`
  from `Sarason/Definitions.lean` and `Sarason/Chapter2.lean`:
  `(u * v_θ - v * u_θ) / (u² + v²)`.
-/
noncomputable def argPolarDeriv_theta (u v ux uy vx vy : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  let q : ℝ × ℝ := (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
  (u q * polar_partial_theta vx vy p - v q * polar_partial_theta ux uy p) /
    (u q ^ 2 + v q ^ 2)

/--
  Under the Cartesian Cauchy–Riemann equations at `q = (r cos θ, r sin θ)`, the complex
  polar `θ`-derivative `u_θ + i v_θ` equals `i z f'(z)`.
-/
lemma polar_partial_theta_complex_of_cr (ux uy vx vy : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (h_CR1 : ux (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = vy (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
    (h_CR2 : uy (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = -vx (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) :
    let q : ℝ × ℝ := (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
    (polar_partial_theta ux uy p : ℂ) + (polar_partial_theta vx vy p : ℂ) * I =
      I * polarPoint p.1 p.2 * ((ux q : ℂ) + (vx q : ℂ) * I) := by
{
  intro q
  unfold polar_partial_theta polarPoint
  dsimp [q]
  rw [h_CR1, h_CR2]
  apply Complex.ext
  · simp; ring
  · simp; ring
}

/--
  Using the polar Cauchy–Riemann equations (`exercise_II_6_3` from `Sarason/Chapter2.lean`),
  the angular argument derivative `argPolarDeriv_theta` equals `r * ∂(ln |f|)/∂r`, i.e.,
  `r * (u * u_r + v * v_r) / (u² + v²)`.
-/
theorem argPolarDeriv_theta_eq_polar_partial_r (u v ux uy vx vy : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (h_CR1 : ux (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = vy (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
    (h_CR2 : uy (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = -vx (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) :
    let q : ℝ × ℝ := (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
    argPolarDeriv_theta u v ux uy vx vy p =
      p.1 * (u q * polar_partial_r ux uy p + v q * polar_partial_r vx vy p) /
        (u q ^ 2 + v q ^ 2) := by
{
  intro q
  rcases exercise_II_6_3 ux uy vx vy p h_CR1 h_CR2 with ⟨h_ur, h_vr⟩
  unfold argPolarDeriv_theta
  dsimp [q]
  have h_num :
      u (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * polar_partial_theta vx vy p -
        v (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * polar_partial_theta ux uy p =
      p.1 * (u (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * polar_partial_r ux uy p +
        v (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * polar_partial_r vx vy p) := by
  {
    linear_combination
      u (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * h_ur.symm +
      v (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * h_vr.symm
  }
  rw [h_num]
}

/--
  §III.13 Fundamental Starlike Angle-Derivative Identity:
  Under the Cauchy–Riemann equations at `z = polarPoint r θ`, the polar angular rate of change
  `argPolarDeriv_theta` of `arg f(r e^{iθ})` with respect to `θ` equals `Re(z f'(z) / f(z))`.
-/
theorem argPolarDeriv_theta_eq_re_logDeriv (u v ux uy vx vy : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (h_CR1 : ux (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = vy (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
    (h_CR2 : uy (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = -vx (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) :
    let q : ℝ × ℝ := (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
    let f_z : ℂ := (u q : ℂ) + (v q : ℂ) * I
    let f'_z : ℂ := (ux q : ℂ) + (vx q : ℂ) * I
    argPolarDeriv_theta u v ux uy vx vy p = ((polarPoint p.1 p.2 * f'_z) / f_z).re := by
{
  intros q f_z f'_z
  unfold argPolarDeriv_theta polar_partial_theta polarPoint
  dsimp [q, f_z, f'_z]
  rw [h_CR1, h_CR2, Complex.div_re, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring
}

/--
  Connection to `Complex.arg` from Chapter 2: for `w = (z * f') / f_z ≠ 0`,
  `Re(z f' / f_z) = ‖z f' / f_z‖ * cos(arg(z f' / f_z))`, so `Re(z f' / f_z) > 0`
  if and only if `cos(arg(z f' / f_z)) > 0`.
-/
theorem re_logDeriv_pos_iff_cos_arg_pos {z f' f_z : ℂ} (hw : (z * f') / f_z ≠ 0) :
    0 < ((z * f') / f_z).re ↔ 0 < Real.cos (arg ((z * f') / f_z)) := by
{
  have h_cos := Complex.cos_arg hw
  have h_norm_pos : 0 < ‖(z * f') / f_z‖ := norm_pos_iff.mpr hw
  rw [h_cos, div_pos_iff_of_pos_right h_norm_pos]
}

/--
  §III.13 Angle-based (`θ` / `polar_partial_theta`) and `_eps`-based definition of a
  starlike holomorphic function `f : ℂ → ℂ` on the unit disk `unitDiskSet`:
  1. `HolomorphicOn_eps f unitDiskSet`
  2. `f 0 = 0` and `∀ z ∈ unitDiskSet, z ≠ 0 → f z ≠ 0`
  3. On every circle of radius `0 < r < 1`, the angular argument derivative
     `argPolarDeriv_theta` with respect to `θ` is strictly positive (`∂(arg f)/∂θ > 0`).
-/
def IsStarlikeOnDisk_theta_eps (f : ℂ → ℂ) : Prop :=
  HolomorphicOn_eps f unitDiskSet ∧
  f 0 = 0 ∧
  (∀ z ∈ unitDiskSet, z ≠ 0 → f z ≠ 0) ∧
  ∀ (r θ : ℝ) (ux uy vx vy : ℝ × ℝ → ℝ),
    0 < r → r < 1 →
    HasPartialDerivX_C_to_R_eps (fun w => (f w).re) (ux (r * Real.cos θ, r * Real.sin θ)) (polarPoint r θ) →
    HasPartialDerivY_C_to_R_eps (fun w => (f w).re) (uy (r * Real.cos θ, r * Real.sin θ)) (polarPoint r θ) →
    HasPartialDerivX_C_to_R_eps (fun w => (f w).im) (vx (r * Real.cos θ, r * Real.sin θ)) (polarPoint r θ) →
    HasPartialDerivY_C_to_R_eps (fun w => (f w).im) (vy (r * Real.cos θ, r * Real.sin θ)) (polarPoint r θ) →
    0 < argPolarDeriv_theta
      (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).re)
      (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).im)
      ux uy vx vy (r, θ)

/--
  §III.13 Analytic logarithmic-derivative definition of a starlike holomorphic function on
  `unitDiskSet` using `HolomorphicOn_eps`, `DifferentiableAt_eps`, and `deriv_eps`:
  `Re(z * deriv_eps f z hd / f z) > 0` for all `z ∈ unitDiskSet \ {0}`.
-/
def IsStarlikeLogDeriv_eps (f : ℂ → ℂ) : Prop :=
  HolomorphicOn_eps f unitDiskSet ∧
  f 0 = 0 ∧
  (∀ z ∈ unitDiskSet, z ≠ 0 → f z ≠ 0) ∧
  ∀ (z : ℂ), z ∈ unitDiskSet → z ≠ 0 →
    ∀ (hd : DifferentiableAt_eps f z), 0 < ((z * deriv_eps f z hd) / f z).re

lemma isStarlikeLogDeriv_eps_of_theta_eps {f : ℂ → ℂ} (h : IsStarlikeOnDisk_theta_eps f) :
    IsStarlikeLogDeriv_eps f := by
{
  rcases h with ⟨h_hol, h0, hne0, h_theta⟩
  refine ⟨h_hol, h0, hne0, fun z hz hzne hd => ?_⟩
  have hr_pos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
  have hz_polar : polarPoint ‖z‖ (arg z) = z := polarPoint_norm_arg z
  let f' : ℂ := deriv_eps f z hd
  have h_deriv : HasDerivAt_eps f f' (polarPoint ‖z‖ (arg z)) := by
  {
    rw [hz_polar]
    exact Classical.choose_spec hd
  }
  rcases hasDerivAt_eps_imp_cauchy_riemann h_deriv with ⟨h_ux, h_uy, h_vx, h_vy⟩
  let ux : ℝ × ℝ → ℝ := fun _ => f'.re
  let uy : ℝ × ℝ → ℝ := fun _ => -f'.im
  let vx : ℝ × ℝ → ℝ := fun _ => f'.im
  let vy : ℝ × ℝ → ℝ := fun _ => f'.re
  have h_pos := h_theta ‖z‖ (arg z) ux uy vx vy hr_pos hz h_ux h_uy h_vx h_vy
  have h_id := argPolarDeriv_theta_eq_re_logDeriv
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).re)
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).im)
    ux uy vx vy (‖z‖, arg z) rfl (by ring)
  dsimp [ux, vx] at h_id
  change argPolarDeriv_theta
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).re)
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).im)
    ux uy vx vy (‖z‖, arg z) =
    (polarPoint ‖z‖ (arg z) * ((f'.re : ℂ) + (f'.im : ℂ) * I) /
      (((f (polarPoint ‖z‖ (arg z))).re : ℂ) + ((f (polarPoint ‖z‖ (arg z))).im : ℂ) * I)).re at h_id
  rw [hz_polar, Complex.re_add_im (f z), Complex.re_add_im f'] at h_id
  rwa [← h_id]
}

lemma isStarlikeOnDisk_theta_eps_of_logDeriv_eps {f : ℂ → ℂ} (h : IsStarlikeLogDeriv_eps f) :
    IsStarlikeOnDisk_theta_eps f := by
{
  rcases h with ⟨h_hol, h0, hne0, h_log⟩
  refine ⟨h_hol, h0, hne0, fun r θ ux uy vx vy hr0 hr1 h_ux h_uy h_vx h_vy => ?_⟩
  have hz_mem : polarPoint r θ ∈ unitDiskSet := polarPoint_mem_unitDiskSet hr0.le hr1 θ
  have hz_ne : polarPoint r θ ≠ 0 := polarPoint_ne_zero_of_pos hr0 θ
  have hd : DifferentiableAt_eps f (polarPoint r θ) := h_hol (polarPoint r θ) hz_mem
  have h_deriv : HasDerivAt_eps f (deriv_eps f (polarPoint r θ) hd) (polarPoint r θ) :=
    Classical.choose_spec hd
  rcases hasDerivAt_eps_imp_cauchy_riemann h_deriv with ⟨h_ux', h_uy', h_vx', h_vy'⟩
  have h_ux_eq := partial_deriv_unique_x _ _ _ _ h_ux h_ux'
  have h_uy_eq := partial_deriv_unique_y _ _ _ _ h_uy h_uy'
  have h_vx_eq := partial_deriv_unique_x _ _ _ _ h_vx h_vx'
  have h_vy_eq := partial_deriv_unique_y _ _ _ _ h_vy h_vy'
  have h_id := argPolarDeriv_theta_eq_re_logDeriv
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).re)
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).im)
    ux uy vx vy (r, θ) (h_ux_eq.trans h_vy_eq.symm) (by rw [h_uy_eq, h_vx_eq])
  dsimp at h_id
  change argPolarDeriv_theta
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).re)
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).im)
    ux uy vx vy (r, θ) =
    (polarPoint r θ * ((ux (r * Real.cos θ, r * Real.sin θ) : ℂ) +
      (vx (r * Real.cos θ, r * Real.sin θ) : ℂ) * I) /
      (((f (polarPoint r θ)).re : ℂ) + ((f (polarPoint r θ)).im : ℂ) * I)).re at h_id
  rw [h_ux_eq, h_vx_eq, Complex.re_add_im, Complex.re_add_im (f (polarPoint r θ))] at h_id
  rw [h_id]
  exact h_log (polarPoint r θ) hz_mem hz_ne hd
}

/--
  Equivalence between the polar-angle (`θ` / `polar_partial_theta`) definition
  `IsStarlikeOnDisk_theta_eps f` and the logarithmic-derivative `_eps` definition
  `IsStarlikeLogDeriv_eps f`.
-/
theorem isStarlikeOnDisk_theta_eps_iff_logDeriv_eps (f : ℂ → ℂ) :
    IsStarlikeOnDisk_theta_eps f ↔ IsStarlikeLogDeriv_eps f := by
{
  exact ⟨isStarlikeLogDeriv_eps_of_theta_eps, isStarlikeOnDisk_theta_eps_of_logDeriv_eps⟩
}

/--
  §III.13 Single-factor Herglotz–Pommerenke identity: for `ζ ∈ unitCircleSet` (`‖ζ‖ = 1`),
  `1 + 2 * (conj ζ * z) / (1 - conj ζ * z) = herglotzKernel ζ z`.
-/
lemma pommerenke_single_term_eq_herglotz {ζ z : ℂ}
    (hζ : ζ ∈ unitCircleSet) (hne : ζ - z ≠ 0) :
    (1 : ℂ) + (2 : ℂ) * (star ζ * z) / (1 - star ζ * z) = herglotzKernel ζ z := by
{
  simp only [unitCircleSet, Set.mem_setOf_eq] at hζ
  have hζ_ne : ζ ≠ 0 := by
  {
    intro h0; rw [h0, norm_zero] at hζ; norm_num at hζ
  }
  have h_mul_conj : ζ * star ζ = 1 := by
  {
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]
    norm_num
  }
  have h_den_eq : ζ * (1 - star ζ * z) = ζ - z := by
  {
    calc ζ * (1 - star ζ * z) = ζ - (ζ * star ζ) * z := by ring
      _ = ζ - 1 * z := by rw [h_mul_conj]
      _ = ζ - z := by ring
  }
  have h_den_ne : 1 - star ζ * z ≠ 0 := by
  {
    intro h0
    apply hne
    rw [← h_den_eq, h0, mul_zero]
  }
  unfold herglotzKernel
  rw [add_div' _ _ _ h_den_ne, one_mul]
  have h_num_eq : ζ * (1 - star ζ * z + 2 * (star ζ * z)) = ζ + z := by
  {
    calc ζ * (1 - star ζ * z + 2 * (star ζ * z))
        = ζ + (ζ * star ζ) * z := by ring
      _ = ζ + 1 * z := by rw [h_mul_conj]
      _ = ζ + z := by ring
  }
  calc (1 - star ζ * z + 2 * (star ζ * z)) / (1 - star ζ * z)
      = (ζ * (1 - star ζ * z + 2 * (star ζ * z))) / (ζ * (1 - star ζ * z)) :=
          (mul_div_mul_left _ _ hζ_ne).symm
    _ = (ζ + z) / (ζ - z) := by rw [h_num_eq, h_den_eq]
}

/--
  §III.13 The Herglotz–Pommerenke logarithmic derivative of a starlike radial slit map
  `f(z) = z ∏_{j=1}^m (1 - conj(ζ_j) z)^{-σ_j}`:
  `z f'(z) / f(z) = ∑_{j=1}^m (σ_j / 2) * herglotzKernel (ζ_j) z`.
-/
noncomputable def pommerenkeLogDeriv {m : ℕ} (ζ : Fin m → ℂ) (σ : Fin m → ℝ) (z : ℂ) : ℂ :=
  ∑ j : Fin m, ((σ j / 2 : ℝ) : ℂ) * herglotzKernel (ζ j) z

/--
  Real part of `pommerenkeLogDeriv`:
  `Re(pommerenkeLogDeriv ζ σ z) = ∑_{j=1}^m (σ_j / 2) * Re(herglotzKernel (ζ_j) z)`.
-/
lemma pommerenkeLogDeriv_re {m : ℕ} (ζ : Fin m → ℂ) (σ : Fin m → ℝ) (z : ℂ) :
    (pommerenkeLogDeriv ζ σ z).re =
      ∑ j : Fin m, (σ j / 2) * (herglotzKernel (ζ j) z).re := by
{
  unfold pommerenkeLogDeriv
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re]
}

/--
  §III.13 Interior Starlikeness of the Pommerenke Slit Map (`∂(arg f)/∂θ > 0` on `𝔻`):
  If `m > 0`, every `ζ_j ∈ unitCircleSet`, and every channel exponent `σ_j > 0`,
  then for every `z ∈ unitDiskSet`, `0 < (pommerenkeLogDeriv ζ σ z).re`.
-/
theorem pommerenkeLogDeriv_re_pos_on_disk {m : ℕ} (hm : 0 < m)
    (ζ : Fin m → ℂ) (σ : Fin m → ℝ)
    (hζ : ∀ j, ζ j ∈ unitCircleSet)
    (hσ : ∀ j, 0 < σ j) :
    ∀ z ∈ unitDiskSet, 0 < (pommerenkeLogDeriv ζ σ z).re := by
{
  intro z hz
  rw [pommerenkeLogDeriv_re]
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  apply Finset.sum_pos
  · intro j _
    have h_herg := (III_11_herglotz_properties (hζ j)).2.1 z hz
    exact mul_pos (half_pos (hσ j)) h_herg
  · exact Finset.univ_nonempty
}

/--
  §III.13 Boundary Constant-Angle Slit Property (`∂(arg f)/∂θ = 0` on `∂𝔻`):
  If every `ζ_j ∈ unitCircleSet`, then for every boundary point `z ∈ unitCircleSet`,
  `(pommerenkeLogDeriv ζ σ z).re = 0`, so each boundary arc `(ζ_k, ζ_{k+1}) ⊂ ∂𝔻` maps
  to a radial slit of constant polar angle `θ_k`.
-/
theorem pommerenkeLogDeriv_re_zero_on_circle {m : ℕ}
    (ζ : Fin m → ℂ) (σ : Fin m → ℝ)
    (hζ : ∀ j, ζ j ∈ unitCircleSet) :
    ∀ z ∈ unitCircleSet, (pommerenkeLogDeriv ζ σ z).re = 0 := by
{
  intro z hz
  rw [pommerenkeLogDeriv_re]
  apply Finset.sum_eq_zero
  intro j _
  rw [(III_11_herglotz_properties (hζ j)).2.2 z hz, mul_zero]
}

/--
  §III.13 Equivalence between the Herglotz kernel representation `pommerenkeLogDeriv ζ σ z`
  and the product logarithmic derivative `1 + ∑_{j=1}^m σ_j conj(ζ_j) z / (1 - conj(ζ_j) z)`
  when `∑_{j=1}^m σ_j = 2`.
-/
theorem pommerenkeLogDeriv_eq_product_logDeriv {m : ℕ}
    (ζ : Fin m → ℂ) (σ : Fin m → ℝ) (z : ℂ)
    (hζ : ∀ j, ζ j ∈ unitCircleSet)
    (hne : ∀ j, ζ j - z ≠ 0)
    (hsum : ∑ j : Fin m, σ j = 2) :
    pommerenkeLogDeriv ζ σ z =
      1 + ∑ j : Fin m, (σ j : ℂ) * (star (ζ j) * z) / (1 - star (ζ j) * z) := by
{
  unfold pommerenkeLogDeriv
  have h_term : ∀ j : Fin m,
      ((σ j / 2 : ℝ) : ℂ) * herglotzKernel (ζ j) z =
        ((σ j / 2 : ℝ) : ℂ) + (σ j : ℂ) * (star (ζ j) * z) / (1 - star (ζ j) * z) := by
  {
    intro j
    rw [← pommerenke_single_term_eq_herglotz (hζ j) (hne j)]
    push_cast
    ring
  }
  simp_rw [h_term, Finset.sum_add_distrib]
  congr 1
  have h_half_sum : ∑ j : Fin m, ((σ j / 2 : ℝ) : ℂ) = (((∑ j : Fin m, σ j) / 2 : ℝ) : ℂ) := by
  {
    rw [Finset.sum_div]
    push_cast
    rfl
  }
  rw [h_half_sum, hsum]
  norm_num
}

/--
  §III.13 `herglotzKernel ζ` is the linear-fractional transformation `linFracTrans 1 ζ (-1) ζ`.
-/
lemma herglotzKernel_eq_linFracTrans (ζ : ℂ) :
    herglotzKernel ζ = linFracTrans 1 ζ (-1) ζ := by
{
  ext z
  unfold herglotzKernel linFracTrans
  ring
}

/--
  §III.13 For `ζ ∈ unitCircleSet` and `z ∈ unitDiskSet`, `ζ - z ≠ 0`.
-/
lemma unitCircle_sub_unitDisk_ne_zero {ζ z : ℂ}
    (hζ : ζ ∈ unitCircleSet) (hz : z ∈ unitDiskSet) :
    ζ - z ≠ 0 := by
{
  simp only [unitCircleSet, unitDiskSet, Set.mem_setOf_eq] at hζ hz
  intro h_sub
  have h_eq : ζ = z := sub_eq_zero.mp h_sub
  rw [← h_eq, hζ] at hz
  exact lt_irrefl 1 hz
}

/--
  §III.13 Weierstrass `HasDerivAt_eps` derivative of `herglotzKernel ζ`:
  at any `z₀` with `ζ - z₀ ≠ 0`, `d/dz ((ζ + z) / (ζ - z)) = 2 * ζ / (ζ - z₀) ^ 2`.
-/
theorem herglotzKernel_hasDerivAt_eps {ζ z₀ : ℂ} (hne : ζ - z₀ ≠ 0) :
    HasDerivAt_eps (herglotzKernel ζ) (2 * ζ / (ζ - z₀) ^ 2) z₀ := by
{
  have h_den : (-1 : ℂ) * z₀ + ζ ≠ 0 := by
  {
    intro h0
    apply hne
    linear_combination h0
  }
  have h_lft := linFracTrans_hasDerivAt_eps 1 ζ (-1) ζ z₀ h_den
  rw [← herglotzKernel_eq_linFracTrans ζ] at h_lft
  have h_val : ((1 : ℂ) * ζ - ζ * (-1)) / ((-1 : ℂ) * z₀ + ζ) ^ 2 = 2 * ζ / (ζ - z₀) ^ 2 := by
  {
    have h_sq : ((-1 : ℂ) * z₀ + ζ) ^ 2 = (ζ - z₀) ^ 2 := by ring
    have h_num : (1 : ℂ) * ζ - ζ * (-1) = 2 * ζ := by ring
    rw [h_sq, h_num]
  }
  rwa [h_val] at h_lft
}

/--
  §III.13 For every `ζ ∈ unitCircleSet`, `herglotzKernel ζ` is holomorphic on `unitDiskSet`
  in the Weierstrass `_eps` sense (`HolomorphicOn_eps (herglotzKernel ζ) unitDiskSet`).
-/
theorem herglotzKernel_holomorphicOn_eps {ζ : ℂ} (hζ : ζ ∈ unitCircleSet) :
    HolomorphicOn_eps (herglotzKernel ζ) unitDiskSet := by
{
  intro z hz
  exact ⟨2 * ζ / (ζ - z) ^ 2,
    herglotzKernel_hasDerivAt_eps (unitCircle_sub_unitDisk_ne_zero hζ hz)⟩
}

/--
  §III.13 Weierstrass `HasDerivAt_eps` derivative of `pommerenkeLogDeriv ζ σ` on `unitDiskSet`.
-/
theorem pommerenkeLogDeriv_hasDerivAt_eps {m : ℕ}
    (ζ : Fin m → ℂ) (σ : Fin m → ℝ)
    (hζ : ∀ j, ζ j ∈ unitCircleSet)
    {z₀ : ℂ} (hz₀ : z₀ ∈ unitDiskSet) :
    HasDerivAt_eps (pommerenkeLogDeriv ζ σ)
      (∑ j : Fin m, ((σ j / 2 : ℝ) : ℂ) * (2 * ζ j / (ζ j - z₀) ^ 2)) z₀ := by
{
  rw [← hasDerivAt_iff_eps]
  have h_sum := HasDerivAt.sum (u := Finset.univ)
    (A := fun (j : Fin m) (z : ℂ) => ((σ j / 2 : ℝ) : ℂ) * herglotzKernel (ζ j) z)
    (A' := fun (j : Fin m) => ((σ j / 2 : ℝ) : ℂ) * (2 * ζ j / (ζ j - z₀) ^ 2))
    (x := z₀) (fun j _ => by {
      have h_j := (hasDerivAt_iff_eps _ _ z₀).mpr
        (herglotzKernel_hasDerivAt_eps (unitCircle_sub_unitDisk_ne_zero (hζ j) hz₀))
      exact h_j.const_mul ((σ j / 2 : ℝ) : ℂ)
    })
  have h_fn : pommerenkeLogDeriv ζ σ =
      ∑ j ∈ Finset.univ, fun z : ℂ => ((σ j / 2 : ℝ) : ℂ) * herglotzKernel (ζ j) z := by
  {
    ext z
    simp [pommerenkeLogDeriv, Finset.sum_apply]
  }
  rw [h_fn]
  exact h_sum
}

/--
  §III.13 For `∀ j, ζ j ∈ unitCircleSet`, the Herglotz–Pommerenke logarithmic derivative
  `pommerenkeLogDeriv ζ σ` is holomorphic on `unitDiskSet` (`HolomorphicOn_eps`).
-/
theorem pommerenkeLogDeriv_holomorphicOn_eps {m : ℕ}
    (ζ : Fin m → ℂ) (σ : Fin m → ℝ)
    (hζ : ∀ j, ζ j ∈ unitCircleSet) :
    HolomorphicOn_eps (pommerenkeLogDeriv ζ σ) unitDiskSet := by
{
  intro z hz
  exact ⟨_, pommerenkeLogDeriv_hasDerivAt_eps ζ σ hζ hz⟩
}

/--
  §III.13 Squared chordal distance on the unit circle in terms of polar angles `φ` and `t`:
  `‖polarPoint 1 φ - polarPoint 1 t‖ ^ 2 = 2 * (1 - Real.cos (t - φ))`.
-/
theorem polarPoint_unitCircle_dist_sq (φ t : ℝ) :
    ‖polarPoint 1 φ - polarPoint 1 t‖ ^ 2 = 2 * (1 - Real.cos (t - φ)) := by
{
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, polarPoint_re, polarPoint_im, one_mul]
  have h_cos := Real.cos_sub t φ
  have h_φ := Real.cos_sq_add_sin_sq φ
  have h_t := Real.cos_sq_add_sin_sq t
  linear_combination h_φ + h_t + 2 * h_cos
}

/--
  §III.13 Boundary Cotangent Formula for the Herglotz Kernel on `∂𝔻`:
  For boundary points `ζ = polarPoint 1 φ` and `z = polarPoint 1 t` on `∂𝔻`,
  `Im(herglotzKernel (polarPoint 1 φ) (polarPoint 1 t)) = sin(t - φ) / (1 - cos(t - φ))`.
-/
theorem herglotzKernel_unitCircle_im (φ t : ℝ) :
    (herglotzKernel (polarPoint 1 φ) (polarPoint 1 t)).im =
      Real.sin (t - φ) / (1 - Real.cos (t - φ)) := by
{
  unfold herglotzKernel
  rw [Complex.div_im, ← Complex.sq_norm, polarPoint_unitCircle_dist_sq φ t]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    polarPoint_re, polarPoint_im, one_mul]
  have h_num :
      (Real.sin φ + Real.sin t) * (Real.cos φ - Real.cos t) -
        (Real.cos φ + Real.cos t) * (Real.sin φ - Real.sin t) =
      2 * Real.sin (t - φ) := by
  {
    have h_sin := Real.sin_sub t φ
    linear_combination -2 * h_sin
  }
  rw [← sub_div, h_num, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
}

/--
  §III.13 Imaginary part of `pommerenkeLogDeriv` on `∂𝔻`:
  At `z = polarPoint 1 t ∈ ∂𝔻` with `ζ_j = polarPoint 1 (φ j)`,
  `Im(pommerenkeLogDeriv ζ σ (polarPoint 1 t)) = ∑ j, (σ_j / 2) * sin(t - φ_j) / (1 - cos(t - φ_j))`.
-/
lemma pommerenkeLogDeriv_unitCircle_im {m : ℕ}
    (φ σ : Fin m → ℝ) (t : ℝ) :
    (pommerenkeLogDeriv (fun j => polarPoint 1 (φ j)) σ (polarPoint 1 t)).im =
      ∑ j : Fin m, (σ j / 2) * (Real.sin (t - φ j) / (1 - Real.cos (t - φ j))) := by
{
  unfold pommerenkeLogDeriv
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    herglotzKernel_unitCircle_im]
}

/--
  §III.13 Boundary Slit-Tip Formula for `pommerenkeLogDeriv` on `∂𝔻`:
  At `z = polarPoint 1 t ∈ ∂𝔻` with `ζ_j = polarPoint 1 (φ j)`, the logarithmic derivative
  `pommerenkeLogDeriv ζ σ (polarPoint 1 t)` is purely imaginary and given by
  `I * ∑ j, (σ_j / 2) * sin(t - φ_j) / (1 - cos(t - φ_j))`.
-/
theorem pommerenkeLogDeriv_unitCircle_eq {m : ℕ}
    (φ σ : Fin m → ℝ) (t : ℝ) :
    pommerenkeLogDeriv (fun j => polarPoint 1 (φ j)) σ (polarPoint 1 t) =
      ((∑ j : Fin m, (σ j / 2) * (Real.sin (t - φ j) / (1 - Real.cos (t - φ j))) : ℝ) : ℂ) * I := by
{
  have h_re := pommerenkeLogDeriv_re_zero_on_circle
    (fun j => polarPoint 1 (φ j)) σ (fun j => polarPoint_one_mem_unitCircleSet (φ j))
    (polarPoint 1 t) (polarPoint_one_mem_unitCircleSet t)
  apply Complex.ext
  · rw [h_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  · rw [pommerenkeLogDeriv_unitCircle_im]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
}

/--
  §III.13 Half-angle identities for `1 - cos α` and `sin α`:
  `1 - cos α = 2 * sin(α / 2) ^ 2` and `sin α = 2 * sin(α / 2) * cos(α / 2)`.
-/
lemma one_sub_cos_and_sin_halfAngle (α : ℝ) :
    1 - Real.cos α = 2 * Real.sin (α / 2) ^ 2 ∧
    Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
{
  have h2 : α = 2 * (α / 2) := by ring
  have h_cos : Real.cos α = Real.cos (α / 2) ^ 2 - Real.sin (α / 2) ^ 2 := by
  {
    conv_lhs => rw [h2]
    exact Real.cos_two_mul' (α / 2)
  }
  have h_sin : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
  {
    conv_lhs => rw [h2]
    exact Real.sin_two_mul (α / 2)
  }
  have h_pyth := Real.cos_sq_add_sin_sq (α / 2)
  constructor
  · linear_combination -h_cos - h_pyth
  · exact h_sin
}

/--
  §III.13 Positive Half-Angle Polar Factorization of `1 - e^{i α}` (`0 < α < 2π`):
  `1 - polarPoint 1 α = polarPoint (2 * sin(α / 2)) ((α - π) / 2)`.
  When `t > φ_j` on `(0, 2π)`, `2 * sin((t - φ_j) / 2) > 0`, so the polar angle of
  `1 - e^{i(t - φ_j)}` is `(t - φ_j - π) / 2`.
-/
theorem one_sub_polarPoint_eq_pos_halfAngle (α : ℝ) :
    1 - polarPoint 1 α = polarPoint (2 * Real.sin (α / 2)) ((α - Real.pi) / 2) := by
{
  rcases one_sub_cos_and_sin_halfAngle α with ⟨h_cos_half, h_sin_half⟩
  have h_ang : (α - Real.pi) / 2 = α / 2 - Real.pi / 2 := by ring
  have h_c : Real.cos ((α - Real.pi) / 2) = Real.sin (α / 2) := by
  {
    rw [h_ang, Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  }
  have h_s : Real.sin ((α - Real.pi) / 2) = -Real.cos (α / 2) := by
  {
    rw [h_ang, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  }
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, polarPoint_re, one_mul, h_c]
    linear_combination h_cos_half
  · simp only [Complex.sub_im, Complex.one_im, polarPoint_im, one_mul, h_s]
    linear_combination -h_sin_half
}

/--
  §III.13 Negative Half-Angle Polar Factorization of `1 - e^{i α}` (`-2π < α < 0`):
  `1 - polarPoint 1 α = polarPoint (-2 * sin(α / 2)) ((α + π) / 2)`.
  When `t < φ_j` on `(0, 2π)`, `-2 * sin((t - φ_j) / 2) > 0`, so the polar angle of
  `1 - e^{i(t - φ_j)}` is `(t - φ_j + π) / 2`.
-/
theorem one_sub_polarPoint_eq_neg_halfAngle (α : ℝ) :
    1 - polarPoint 1 α = polarPoint (-2 * Real.sin (α / 2)) ((α + Real.pi) / 2) := by
{
  rcases one_sub_cos_and_sin_halfAngle α with ⟨h_cos_half, h_sin_half⟩
  have h_ang : (α + Real.pi) / 2 = α / 2 + Real.pi / 2 := by ring
  have h_c : Real.cos ((α + Real.pi) / 2) = -Real.sin (α / 2) := by
  {
    rw [h_ang, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  }
  have h_s : Real.sin ((α + Real.pi) / 2) = Real.cos (α / 2) := by
  {
    rw [h_ang, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  }
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, polarPoint_re, one_mul, h_c]
    linear_combination h_cos_half
  · simp only [Complex.sub_im, Complex.one_im, polarPoint_im, one_mul, h_s]
    linear_combination -h_sin_half
}

/--
  §III.13 Boundary phase contribution of the `j`-th Pommerenke factor `(1 - e^{-i φ_j} e^{i t})^{-σ_j}`:
  - Before the pole (`t < φ_j`, `beforePole = true`): `-σ_j * (t - φ_j + π) / 2`,
  - After the pole (`t > φ_j`, `beforePole = false`): `-σ_j * (t - φ_j - π) / 2`.
-/
noncomputable def pommerenkeFactorPhase (φ_j σ_j t : ℝ) (beforePole : Bool) : ℝ :=
  -σ_j * ((t - φ_j + (if beforePole then Real.pi else -Real.pi)) / 2)

/--
  §III.13 Total boundary phase `arg f(e^{i t})` of `f(z) = z ∏_{j=0}^{m-1} (1 - e^{-i φ_j} z)^{-σ_j}`
  on the `k`-th boundary arc `(φ_{k-1}, φ_k)` (where `t > φ_j` for `j < k` and `t < φ_j` for `j ≥ k`).
-/
noncomputable def pommerenkeArcPhase (m k : ℕ) (φ σ : ℕ → ℝ) (t : ℝ) : ℝ :=
  t + ∑ j ∈ Finset.range m, pommerenkeFactorPhase (φ j) (σ j) t (decide (k ≤ j))

/--
  §III.13 The constant slit angle `θ_k` on the `k`-th boundary arc of the Pommerenke slit map:
  `θ_k = ∑_{j=0}^{m-1} σ_j (φ_j ∓ π) / 2`.
-/
noncomputable def pommerenkeSlitAngle (m k : ℕ) (φ σ : ℕ → ℝ) : ℝ :=
  pommerenkeArcPhase m k φ σ 0

/--
  §III.13 **Constancy of the Boundary Argument on Each Open Arc (`arg f(e^{i t}) = θ_k`):**
  When the Pommerenke exponents satisfy the starlike normalization `∑_{j=0}^{m-1} σ_j = 2`,
  the linear `t`-terms in `pommerenkeArcPhase m k φ σ t` cancel identically (`t - (∑ σ_j / 2) t = 0`),
  so `pommerenkeArcPhase m k φ σ t = pommerenkeSlitAngle m k φ σ` for all `t ∈ ℝ`.
-/
theorem pommerenkeArcPhase_eq_slitAngle (m k : ℕ) (φ σ : ℕ → ℝ)
    (h_sum : ∑ j ∈ Finset.range m, σ j = 2) (t : ℝ) :
    pommerenkeArcPhase m k φ σ t = pommerenkeSlitAngle m k φ σ := by
{
  unfold pommerenkeSlitAngle pommerenkeArcPhase pommerenkeFactorPhase
  have h_split :
      ∑ j ∈ Finset.range m,
        -σ j * ((t - φ j + (if decide (k ≤ j) then Real.pi else -Real.pi)) / 2) =
      -(t / 2) * (∑ j ∈ Finset.range m, σ j) +
      ∑ j ∈ Finset.range m,
        -σ j * ((0 - φ j + (if decide (k ≤ j) then Real.pi else -Real.pi)) / 2) := by
  {
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  }
  rw [h_split, h_sum]
  ring
}

/--
  §III.13 Single-factor phase jump across the `k`-th pole `φ_k`:
  For `j = k`, `decide (k + 1 ≤ k) = false` and `decide (k ≤ k) = true`, so the factor phase jumps
  by `σ_k * π`; for `j ≠ k`, `decide (k + 1 ≤ j) = decide (k ≤ j)`, so the difference vanishes.
-/
lemma pommerenkeFactorPhase_jump (k j : ℕ) (φ_j σ_j t : ℝ) :
    pommerenkeFactorPhase φ_j σ_j t (decide (k + 1 ≤ j)) -
      pommerenkeFactorPhase φ_j σ_j t (decide (k ≤ j)) =
    if j = k then σ_j * Real.pi else 0 := by
{
  by_cases hjk : j = k
  · subst hjk
    have h1 : decide (j + 1 ≤ j) = false := decide_eq_false (Nat.not_succ_le_self j)
    have h2 : decide (j ≤ j) = true := decide_eq_true ( le_rfl )
    unfold pommerenkeFactorPhase
    rw [if_pos rfl, h1, h2]
    simp only [ Bool.false_eq_true, ↓reduceIte]
    ring
  · rw [if_neg hjk]
    have h_eq : decide (k + 1 ≤ j) = decide (k ≤ j) := by
    {
      by_cases hle : k ≤ j
      · have hlt : k < j := lt_of_le_of_ne hle (Ne.symm hjk)
        rw [decide_eq_true (Nat.succ_le_of_lt hlt), decide_eq_true hle]
      · have hnot : ¬ (k + 1 ≤ j) := fun h => hle (Nat.le_of_succ_le h)
        rw [decide_eq_false hnot, decide_eq_false hle]
    }
    rw [h_eq, sub_self]
}

/--
  §III.13 **Derivation of the Channel Opening Angle Formula `θ_{k+1} - θ_k = σ_k π`:**
  For every `k < m`, crossing the pole `z_k = e^{i φ_k}` increases the Pommerenke slit angle
  `pommerenkeSlitAngle m k φ σ` by `σ_k * π`.
-/
theorem pommerenkeSlitAngle_succ_sub_eq_sigma_mul_pi (m k : ℕ) (φ σ : ℕ → ℝ) (hk : k < m) :
    pommerenkeSlitAngle m (k + 1) φ σ - pommerenkeSlitAngle m k φ σ =
      σ k * Real.pi := by
{
  unfold pommerenkeSlitAngle pommerenkeArcPhase
  rw [ zero_add, zero_add, ← Finset.sum_sub_distrib]
  have h_congr :
      ∑ j ∈ Finset.range m,
        (pommerenkeFactorPhase (φ j) (σ j) 0 (decide (k + 1 ≤ j)) -
         pommerenkeFactorPhase (φ j) (σ j) 0 (decide (k ≤ j))) =
      ∑ j ∈ Finset.range m, (if j = k then σ j * Real.pi else 0) := by
  {
    apply Finset.sum_congr rfl
    intro j _
    exact pommerenkeFactorPhase_jump k j (φ j) (σ j) 0
  }
  rw [h_congr, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hk)]
}

/--
  §III.13 **Derived Equivalence of Monotone Channel Opening Angles and Monotone `σ_k`:**
  Directly from `pommerenkeSlitAngle_succ_sub_eq_sigma_mul_pi` (without assuming `Δθ_k = σ_k π`
  as an external axiom), for any `k + 1 < m`,
  `θ_{k+1} - θ_k ≤ θ_{k+2} - θ_{k+1} ↔ σ_k ≤ σ_{k+1}`.
-/
theorem pommerenkeSlitAngle_diff_monotone_iff_sigma_monotone
    (m k : ℕ) (φ σ : ℕ → ℝ) (hk : k + 1 < m) :
    pommerenkeSlitAngle m (k + 1) φ σ - pommerenkeSlitAngle m k φ σ ≤
      pommerenkeSlitAngle m (k + 2) φ σ - pommerenkeSlitAngle m (k + 1) φ σ ↔
      σ k ≤ σ (k + 1) := by
{
  have hk0 : k < m := Nat.lt_of_succ_lt hk
  rw [pommerenkeSlitAngle_succ_sub_eq_sigma_mul_pi m k φ σ hk0,
    pommerenkeSlitAngle_succ_sub_eq_sigma_mul_pi m (k + 1) φ σ hk]
  exact mul_le_mul_iff_of_pos_right Real.pi_pos
}

end Sarason.Ch3
