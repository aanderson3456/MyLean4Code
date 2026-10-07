/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.
-/
import Mathlib.Analysis.Complex.Basic
import Sarason.Definitions
import Contour

/-!
# Sarason - Laplace Transforms and Newman's Tauberian Theorem

Formalizing the specific Tauberian theorem needed for the Prime Number Theorem.
-/

open Complex Filter TopologicalSpace Metric Bornology Classical
open Sarason

namespace Sarason.PNT

/--
  The Laplace transform definition over a finite interval `[0, T]`.
  
  For a function `f`, we compute its Riemann integral against the kernel `e^{-zt}`.
  We approximate this finite integral using our uniform partition sum.
-/
noncomputable def finiteLaplaceSum (f : ℝ → ℂ) (z : ℂ) (T : ℝ) (N : ℕ) : ℂ :=
  -- Summing over N uniformly spaced steps in [0, T]
  ∑ i ∈ Finset.range N,
    -- f(t_i) * e^{-z * t_i} * (T/N)
    f (T * (i / N)) * exp (-z * (T * (i / N))) * (T / N)

/--
  Weierstrass epsilon-delta definition of the Laplace transform limit.
  
  The improper integral from 0 to ∞ converges to `L` if for every `ε > 0`,
  there exists a large enough `T₀` such that for all `T ≥ T₀`, the finite
  integral over `[0, T]` is within `ε` of `L`.
-/
def HasLaplaceTransform_eps (f : ℝ → ℂ) (z : ℂ) (L : ℂ) : Prop :=
  -- For any strictly positive tolerance ε
  ∀ ε > 0, 
  -- There is a threshold T₀
  ∃ T₀ > 0, 
  -- For any time horizon T beyond T₀
  ∀ T ≥ T₀, 
    -- There exists a partition threshold N₀ for the finite integral
    ∃ N₀ : ℕ, 
    -- For any sufficiently fine partition N
    ∀ N ≥ N₀, 
      -- The finite Riemann sum is within ε of the true improper integral L
      ‖finiteLaplaceSum f z T N - L‖ < ε

/--
  The classical value of the Laplace transform extracted via Choice.
-/
noncomputable def laplaceTransform_eps (f : ℝ → ℂ) (z : ℂ) : ℂ :=
  if h : ∃ L, HasLaplaceTransform_eps f z L then 
    -- Extract the unique limit
    Classical.choose h 
  else 
    -- Default to zero if non-integrable
    0

/--
  A function is bounded on `[0, ∞)` if there is some `M > 0` such that 
  `|f(t)| \le M` for all `t \ge 0`.
-/
def IsBounded_eps (f : ℝ → ℂ) : Prop :=
  -- There exists an absolute bound M
  ∃ M > 0, 
  -- For all non-negative t
  ∀ t ≥ 0, 
    -- The norm of f(t) is bounded by M
    ‖f t‖ ≤ M

/--
  Newman's Tauberian Theorem (Statement).
  
  If `f` is bounded on `[0, ∞)`, and its Laplace transform `g(z)` extends 
  holomorphically to the closed right half-plane `\Re(z) \ge 0`, 
  then the improper integral `\int_0^\infty f(t) dt` converges.
  
  (In our formalization, `laplaceTransform_eps f 0` represents this integral).
-/
def NewmansTauberianTheorem (f : ℝ → ℂ) (g : ℂ → ℂ) : Prop :=
  -- Hypothesis 1: f is a bounded function
  IsBounded_eps f → 
  -- Hypothesis 2: g(z) is the Laplace transform of f(t) for Re(z) > 0
  (∀ z, 0 < z.re → HasLaplaceTransform_eps f z (g z)) →
  -- Hypothesis 3: g(z) is holomorphic on the closed right half-plane Re(z) >= 0
  (∀ z, 0 ≤ z.re → HolomorphicAt_eps g z) → 
  -- Conclusion: The integral of f(t) from 0 to infinity converges (which is the Laplace transform at z=0)
  (∃ L, HasLaplaceTransform_eps f 0 L)

end Sarason.PNT
