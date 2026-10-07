import Mathlib.Analysis.Complex.Basic

open Complex

lemma continuousOn_C_of_R2 (u : ℝ × ℝ → ℝ) (G : Set ℂ)
    (h : ContinuousOn u {p : ℝ × ℝ | p.1 + p.2 * I ∈ G}) :
    ContinuousOn (fun z : ℂ => u (z.re, z.im)) G := by
{
  have h_comp : ContinuousOn (u ∘ (fun z : ℂ => (z.re, z.im))) G := by
  {
    refine ContinuousOn.comp h (Continuous.continuousOn (by fun_prop)) ?_
    intro z hz
    simp at hz ⊢
    exact hz
  }
  exact h_comp
}
