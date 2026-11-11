import Mathlib

open Set Complex Metric MeasureTheory Filter
open scoped Topology

def disk : Set ℂ := Metric.ball 0 1

lemma liouville_contradiction (φ : ℂ → ℂ) (h_diff : DifferentiableOn ℂ φ univ) (h_bij : BijOn φ univ disk) : False := by
  have hd : Differentiable ℂ φ := differentiableOn_univ.mp h_diff
  have h_bound : Bornology.IsBounded (range φ) := by
    have h_range : range φ = disk := by
      ext y
      simp only [mem_range]
      constructor
      · rintro ⟨x, rfl⟩
        exact h_bij.mapsTo (mem_univ x)
      · intro hy
        exact h_bij.surjOn hy
    rw [h_range]
    exact Metric.isBounded_ball
  have h_const : ∀ x y, φ x = φ y := hd.apply_eq_apply_of_bounded h_bound
  have h0 : (0 : ℂ) ∈ disk := by simp [disk, ball]
  have hhalf : (1/2 : ℂ) ∈ disk := by simp [disk, ball, norm, Complex.abs, normSq] ; norm_num
  rcases h_bij.surjOn h0 with ⟨x1, _, hx1⟩
  rcases h_bij.surjOn hhalf with ⟨x2, _, hx2⟩
  have heq := h_const x1 x2
  rw [hx1, hx2] at heq
  norm_num at heq
