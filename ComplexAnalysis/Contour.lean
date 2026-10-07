/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.
-/
import Mathlib
import Sarason.Definitions

open Complex Classical
/-!
# Sarason - Contour Integration

Foundational contour integration definitions built explicitly on epsilon-delta limits,
as preparation for Newman's Tauberian Theorem contour bounds.
-/

open Complex Filter TopologicalSpace Metric Bornology
open Sarason

namespace Sarason.PNT

/--
  In classical complex analysis, a contour integral is defined as the limit of Riemann sums.
  Given a path `γ` from `[0, 1] \to \mathbb{C}`, and a function `f`, we approximate the integral
  by evaluating `f` at sample points and multiplying by the differences in `γ`.

  For our formalization, we define a uniform partition of `[0, 1]` with `N` steps.
-/
noncomputable def uniformPartitionSum (f : ℂ → ℂ) (γ : ℝ → ℂ) (N : ℕ) : ℂ :=
  -- We sum over `i` from `0` to `N - 1`.
  -- At each step, we multiply the value of `f` at the start of the interval
  -- by the complex difference `γ(t_{i+1}) - γ(t_i)`.
  ∑ i ∈ Finset.range N, 
    f (γ (i / N)) * (γ ((i + 1) / N) - γ (i / N))

/--
  Weierstrass epsilon-delta definition of the contour integral.
  
  The integral of `f` along the path `γ` converges to `L` if, for any `ε > 0`,
  there exists a sufficiently large number of partition steps `N₀` such that 
  for all `N \ge N₀`, the uniform partition sum is within `ε` of `L`.
-/
def HasContourIntegral_eps (f : ℂ → ℂ) (γ : ℝ → ℂ) (L : ℂ) : Prop :=
  -- For any strictly positive tolerance ε
  ∀ ε > 0, 
  -- There is a threshold N₀
  ∃ N₀ : ℕ, 
  -- Such that for any finer uniform partition N ≥ N₀
  ∀ N ≥ N₀, 
    -- The distance between the Riemann sum and the integral value L is strictly bounded by ε.
    ‖uniformPartitionSum f γ N - L‖ < ε

/--
  The classical value of the contour integral of `f` along `γ`.
  
  We extract the limit `L` using the Axiom of Choice if the integral converges.
  If the integral does not converge in the epsilon-delta sense, it evaluates to 0.
-/
noncomputable def contourIntegral_eps (f : ℂ → ℂ) (γ : ℝ → ℂ) : ℂ :=
  if h : ∃ L, HasContourIntegral_eps f γ L then 
    -- Extract the unique limit
    Classical.choose h 
  else 
    -- Default to zero if non-integrable
    0

/--
  A specialized path: the straight line segment from `a` to `b` in the complex plane.
  Parametrized by `t \in [0, 1]`.
-/
def lineSegment (a b : ℂ) (t : ℝ) : ℂ :=
  -- Evaluates to `a` at t=0 and `b` at t=1.
  (1 - t : ℂ) * a + (t : ℂ) * b

/--
  A specialized path: a semicircle centered at the origin, ranging from 
  the negative imaginary axis to the positive imaginary axis in the right half-plane.
  
  Parametrized using the complex exponential. `R` is the radius.
-/
noncomputable def rightSemicircle (R : ℝ) (t : ℝ) : ℂ :=
  -- The angle ranges from -π/2 to π/2 as t goes from 0 to 1.
  -- θ(t) = π * t - π / 2
  let θ := Real.pi * t - Real.pi / 2
  -- z(t) = R * e^{iθ}
  (R : ℂ) * exp (θ * I)

/--
  Linearity of the Riemann sum: the partition sum of `f + g` is the sum of their individual partition sums.
  This forms the algebraic foundation for the linearity of the contour integral.
-/
lemma uniformPartitionSum_add (f g : ℂ → ℂ) (γ : ℝ → ℂ) (N : ℕ) :
    uniformPartitionSum (fun z => f z + g z) γ N =
    uniformPartitionSum f γ N + uniformPartitionSum g γ N := by
{
  -- Unfold the definition of our partition sum
  unfold uniformPartitionSum
  -- Apply the linearity of finite sums over the range N
  rw [← Finset.sum_add_distrib]
  -- We must show the terms match point-by-point
  apply Finset.sum_congr rfl
  -- Introduce the arbitrary index `i` and the hypothesis that it's in the range
  intro i _
  -- Distribute the complex multiplication over the addition `(f(z) + g(z)) * dz`
  ring
}

/--
  Scalar multiplication of the Riemann sum: the partition sum of `c * f` is `c` times the partition sum of `f`.
  This allows us to scale integrals by complex constants.
-/
lemma uniformPartitionSum_smul (c : ℂ) (f : ℂ → ℂ) (γ : ℝ → ℂ) (N : ℕ) :
    uniformPartitionSum (fun z => c * f z) γ N =
    c * uniformPartitionSum f γ N := by
{
  -- Unfold the partition sum definition
  unfold uniformPartitionSum
  -- Pull the constant `c` out of the finite sum
  rw [Finset.mul_sum]
  -- Match the terms point-by-point
  apply Finset.sum_congr rfl
  -- Introduce the index
  intro i _
  -- Reassociate the complex multiplication `c * (f(z) * dz) = (c * f(z)) * dz`
  ring
}

/--
  The contour norm bound (triangle inequality for partition sums):
  The norm of the partition sum is bounded by the sum of the norms of its terms.
  This is the discrete analog of |∫ f dz| ≤ ∫ |f| |dz|.
-/
lemma uniformPartitionSum_norm_le (f : ℂ → ℂ) (γ : ℝ → ℂ) (N : ℕ) :
    ‖uniformPartitionSum f γ N‖ ≤ ∑ i ∈ Finset.range N, ‖f (γ (i / N))‖ * ‖γ ((i + 1) / N) - γ (i / N)‖ := by
{
  -- Unfold the definition of the partition sum
  unfold uniformPartitionSum
  -- Apply the general triangle inequality for finite sums: ‖∑ x‖ ≤ ∑ ‖x‖
  have h_triangle := norm_sum_le (Finset.range N) (fun i => f (γ (i / N)) * (γ ((i + 1) / N) - γ (i / N)))
  -- Bound the norm of the sum by the sum of the norms
  apply le_trans h_triangle
  -- Now we must show that the sum of the norms is exactly the sum of the products of norms
  apply Finset.sum_le_sum
  -- Introduce the arbitrary index
  intro i _
  -- Apply the multiplicative property of the complex norm: ‖a * b‖ = ‖a‖ * ‖b‖
  exact le_of_eq (norm_mul (f (γ (i / N))) (γ ((i + 1) / N) - γ (i / N)))
}

/--
  The magnitude of any point on the right semicircle is exactly the radius R.
  This allows us to substitute |z| = R directly in our contour bounds.
-/
lemma norm_rightSemicircle (R : ℝ) (hR : 0 ≤ R) (t : ℝ) :
    ‖rightSemicircle R t‖ = R := by
{
  -- Unfold the definition of the right semicircle
  unfold rightSemicircle
  -- Apply the multiplicative property of the norm
  rw [norm_mul]
  -- The norm of a real number R (where R >= 0) is just R
  have h_norm_R : ‖(R : ℂ)‖ = R := by
  {
    exact (Complex.norm_real R).trans (abs_of_nonneg hR)
  }
  rw [h_norm_R]
  -- The norm of e^{iθ} is exactly 1
  have h_norm_exp : ‖exp ((Real.pi * t - Real.pi / 2 : ℝ) * I)‖ = 1 := by
  {
    -- We use Mathlib's built-in property for the norm of pure imaginary exponentials
    exact Complex.norm_exp_ofReal_mul_I (Real.pi * t - Real.pi / 2)
  }
  rw [h_norm_exp]
  -- Multiplication by 1 preserves R
  exact mul_one R
}

/--
  The magnitude of the exponential scaling factor e^{zT} depends strictly on the real part of z.
  This is the core reason Newman's method works: on the left semicircle (Re z < 0), this factor
  decays exponentially as T -> ∞, while on the right semicircle it is strictly controlled.
-/
lemma norm_exp_mul_real (z : ℂ) (T : ℝ) :
    ‖exp (z * (T : ℂ))‖ = Real.exp (z.re * T) := by
{
  -- The norm of the complex exponential is the real exponential of the real part
  rw [Complex.norm_exp]
  -- We just need to show that the real part of (z * T) is z.re * T
  have h_re : (z * (T : ℂ)).re = z.re * T := by
  {
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero]
  }
  rw [h_re]
}

/--
  A specialized path: a semicircle centered at the origin, ranging from 
  the positive imaginary axis to the negative imaginary axis in the left half-plane.
  
  Parametrized using the complex exponential. `R` is the radius.
-/
noncomputable def leftSemicircle (R : ℝ) (t : ℝ) : ℂ :=
  -- The angle ranges from π/2 to 3π/2 as t goes from 0 to 1.
  -- θ(t) = π * t + π / 2
  let θ := Real.pi * t + Real.pi / 2
  (R : ℂ) * exp (θ * I)

/--
  The magnitude of any point on the left semicircle is exactly the radius R.
  This mirrors the right semicircle property exactly.
-/
lemma norm_leftSemicircle (R : ℝ) (hR : 0 ≤ R) (t : ℝ) :
    ‖leftSemicircle R t‖ = R := by
{
  -- Unfold the definition of the left semicircle
  unfold leftSemicircle
  -- Apply the multiplicative property of the norm
  rw [norm_mul]
  -- The norm of a real number R (where R >= 0) is just R
  have h_norm_R : ‖(R : ℂ)‖ = R := by
  {
    exact (Complex.norm_real R).trans (abs_of_nonneg hR)
  }
  rw [h_norm_R]
  -- The norm of e^{iθ} is exactly 1
  have h_norm_exp : ‖exp ((Real.pi * t + Real.pi / 2 : ℝ) * I)‖ = 1 := by
  {
    exact Complex.norm_exp_ofReal_mul_I (Real.pi * t + Real.pi / 2)
  }
  rw [h_norm_exp]
  -- Multiplication by 1 preserves R
  exact mul_one R
}

/--
  The real part of the left semicircle is always non-positive.
  This is strictly required to establish that e^{zT} decays or is bounded by 1.
-/
lemma re_leftSemicircle_le_zero (R : ℝ) (hR : 0 ≤ R) (t : ℝ) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (leftSemicircle R t).re ≤ 0 := by
{
  -- Unfold the definition
  unfold leftSemicircle
  -- Extract the real part of the exponential
  have h_re : ((R : ℂ) * exp ((Real.pi * t + Real.pi / 2 : ℝ) * I)).re = R * Real.cos (Real.pi * t + Real.pi / 2) := by
  {
    rw [mul_re, ofReal_re, ofReal_im, exp_mul_I]
    have h1 : (cos ↑(Real.pi * t + Real.pi / 2)).re = Real.cos (Real.pi * t + Real.pi / 2) := by rw [← ofReal_cos, ofReal_re]
    have h2 : (sin ↑(Real.pi * t + Real.pi / 2)).im = 0 := by rw [← ofReal_sin, ofReal_im]
    rw [add_re, mul_re, I_re, I_im]
    rw [h1, h2]
    ring
  }
  rw [h_re]
  -- Rewrite cos(x + π/2) = -sin(x)
  rw [Real.cos_add_pi_div_two]
  -- Factor out the negative
  rw [mul_neg]
  -- To show -R * sin(πt) ≤ 0, it suffices to show R * sin(πt) ≥ 0
  apply neg_nonpos.mpr
  apply mul_nonneg hR
  -- Show sin(πt) ≥ 0
  apply Real.sin_nonneg_of_nonneg_of_le_pi
  · -- πt ≥ 0
    exact mul_nonneg Real.pi_pos.le ht0
  · -- πt ≤ π
    have h_pi_mul : Real.pi * t ≤ Real.pi * 1 := mul_le_mul_of_nonneg_left ht1 Real.pi_pos.le
    rw [mul_one] at h_pi_mul
    exact h_pi_mul
}

/--
  Newman's geometric modifier factor.
  This factor introduces a pole at z=0 to extract the limit via Cauchy's residue theorem,
  and its magnitude on the circle |z| = R perfectly balances the exponential growth on the right semicircle.
  We define it in its expanded additive form to easily apply `uniformPartitionSum_add` later.
-/
noncomputable def newmanModifier (R : ℝ) (z : ℂ) : ℂ :=
  1 / z + z / (R : ℂ)^2

/--
  On the contour |z| = R, the newmanModifier can be factored to show its norm 
  is explicitly proportional to the real part of z.
  Specifically, 1/z + z/R^2 = (R^2 + z^2) / (R^2 * z), which evaluates to 2 Re(z) / R^2 on |z|=R.
-/
lemma newmanModifier_eq_on_circle (R : ℝ) (z : ℂ) (hz : z * star z = (R : ℂ)^2) (hz0 : z ≠ 0) :
    newmanModifier R z = (z + star z) / (R : ℂ)^2 := by
{
  unfold newmanModifier
  -- We know 1/z = star z / (z * star z) = star z / R^2
  have h_inv : 1 / z = star z / (R : ℂ)^2 := by
  {
    have h1 : (1 : ℂ) / z = (star z * 1) / (star z * z) := by
    {
      rw [div_eq_div_iff]
      · ring
      · exact hz0
      · exact mul_ne_zero (star_ne_zero.mpr hz0) hz0
    }
    have h2 : (1 : ℂ) / z = star z / (z * star z) := by
    {
      rw [h1]
      ring
    }
    rw [h2, hz]
  }
  rw [h_inv]
  -- Now we just add the fractions
  ring
}

end Sarason.PNT
