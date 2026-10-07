/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Calculus.FDeriv.Star

open Complex

/-- 
  Example 1: f(z) = z^2 is holomorphic everywhere.
  This example demonstrates that polynomial functions like $z \mapsto z^2$ 
  are complex differentiable over the entire complex plane.
-/
example (z : ℂ) : DifferentiableAt ℂ (fun z => z^2) z :=
  differentiableAt_pow 2

/-- 
  Example 2: f(z) = conj(z) is NOT holomorphic anywhere.
  This is a classic counterexample in complex analysis.
  We prove it by using the fact that the real derivative of the complex conjugate 
  is the conjugate mapping itself, which fails to be complex linear.
-/
example (z : ℂ) : ¬ DifferentiableAt ℂ (fun z => star z) z := by
{
  intro h
  
  -- The real derivative of `star` (conjugation) is just `star` itself.
  -- This relies on `star` being a continuous real-linear equivalence.
  have hstar : HasFDerivAt star ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) z :=
    HasFDerivAt.star (hasFDerivAt_id (𝕜 := ℝ) z)
    
  -- If `star` were complex differentiable at `z`, we could extract its 
  -- complex derivative and restrict its scalars to ℝ to get a real-linear map `L`.
  let f'' := fderiv ℂ (fun z => star z) z
  let L : ℂ →L[ℝ] ℂ := f''.restrictScalars ℝ
  
  -- Because the real derivative is unique, this `L` must exactly equal `star`.
  have h_real : HasFDerivAt star L z := h.hasFDerivAt.restrictScalars ℝ
  have hL : ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) = L := hstar.unique h_real
  
  -- Complex linear maps must commute with multiplication by the imaginary unit `I`.
  -- We extract this property from the definition of the complex derivative `f''`.
  have h_comm : L I = I * L 1 := by
  {
    have h_smul := f''.map_smul I 1
    simp at h_smul
    exact h_smul
  }
  
  -- Using our knowledge that `L` is just the `star` (conjugation) operator,
  -- we evaluate `L` on `I` and `1`. Conjugating `I` gives `-I`.
  have h_star : L I = -I := by
  {
    rw [← hL]
    simp
  }
  
  -- Conjugating `1` gives `1`, since 1 is entirely real.
  have h_star1 : L 1 = 1 := by
  {
    rw [← hL]
    simp
  }
  
  -- We substitute our evaluations of `L I` and `L 1` back into the commutativity 
  -- equation to derive a blatant contradiction: `-I = I`.
  have h_contra : -I = I := by
  {
    calc -I = L I := h_star.symm
    _ = I * L 1 := h_comm
    _ = I * 1 := by rw [h_star1]
    _ = I := by rw [mul_one]
  }
  
  -- If `-I = I`, then adding `I` to both sides gives `2 * I = 0`.
  have : (2 : ℂ) * I = 0 := by
  {
    calc (2 : ℂ) * I = I - (-I) := by ring
    _ = I - I := by rw [h_contra]
    _ = 0 := by ring
  }
  
  -- Since we are in an integral domain, `2 * I = 0` implies either `2 = 0` or `I = 0`.
  -- We eliminate both possibilities to finish the proof by contradiction.
  have h_mul : (2 : ℂ) = 0 ∨ I = 0 := mul_eq_zero.mp this
  rcases h_mul with h2 | hI
  · norm_num at h2
  · exact I_ne_zero hI
}
