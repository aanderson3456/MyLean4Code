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

end Sarason.Ch3
