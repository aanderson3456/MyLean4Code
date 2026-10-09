import Mathlib

open Set Complex Metric MeasureTheory Filter
open scoped Topology

def disk : Set ℂ := Metric.ball 0 1

def SphericalBoundaryNontrivial (W : Set ℂ) : Prop :=
  Set.Nontrivial (frontier (((↑) : ℂ → OnePoint ℂ) '' W))

/-- The geometric sub-claim of OpenAI's MainStatement -/
def GeometricBrennan : Prop :=
  ∀ W : Set ℂ, IsOpen W → IsConnected W → SimplyConnectedSpace W →
    SphericalBoundaryNontrivial W → ∀ φ : ℂ → ℂ,
      DifferentiableOn ℂ φ W → Set.BijOn φ W disk →
      ∀ s : ℝ, 4 / 3 < s → s < 4 →
        MeasureTheory.IntegrableOn (fun z => ‖deriv φ z‖ ^ s) W MeasureTheory.volume

/-- Your formulation -/
def BrennansConjectureStatement : Prop :=
  ∀ (W : Set ℂ) (f : ℂ → ℂ) (p : ℝ),
    IsOpen W →
    W.Nonempty →
    W ≠ univ →
    DifferentiableOn ℂ f W →
    InjOn f W →
    f '' W = disk →
    (4 / 3 < p ∧ p < 4) →
    IntegrableOn (fun z => ‖deriv f z‖ ^ p) W volume

/-- Your formulation directly implies OpenAI's geometric formulation -/
theorem yours_implies_theirs (h : BrennansConjectureStatement) : GeometricBrennan := by
  intro W hW_open hW_conn hW_simp hW_sph φ h_diff h_bij s hs_lower hs_upper
  apply h W φ s
  · exact hW_open
  · -- W is nonempty because it bijects to the disk, which is nonempty (contains 0)
    have h_disk_nonempty : (disk : Set ℂ).Nonempty := ⟨0, by simp [disk, ball]⟩
    have himg_nonempty : (φ '' W).Nonempty := h_disk_nonempty.mono h_bij.2.2
    exact himg_nonempty.of_image
  · intro hW_univ
    have h_diff_univ : Differentiable ℂ φ := differentiableOn_univ.mp (hW_univ ▸ h_diff)
    have h_bij_univ : BijOn φ univ disk := hW_univ ▸ h_bij
    have h_bound : Bornology.IsBounded (range φ) := by
      have h_range : range φ = disk := by
        ext y
        simp only [mem_range, mem_image]
        constructor
        · rintro ⟨x, rfl⟩
          exact h_bij_univ.mapsTo (mem_univ x)
        · intro hy
          have hy_img := h_bij_univ.surjOn hy
          simp only [mem_image, mem_univ, true_and] at hy_img
          exact hy_img
      rw [h_range]
      exact Metric.isBounded_ball
    have h_const : ∀ x y, φ x = φ y := h_diff_univ.apply_eq_apply_of_bounded h_bound
    have h0 : (0 : ℂ) ∈ disk := by simp [disk, ball]
    have hhalf : (1/2 : ℂ) ∈ disk := by simp [disk, ball]; norm_num
    rcases h_bij_univ.surjOn h0 with ⟨x1, _, hx1⟩
    rcases h_bij_univ.surjOn hhalf with ⟨x2, _, hx2⟩
    have heq := h_const x1 x2
    rw [hx1, hx2] at heq
    norm_num at heq
  · exact h_diff
  · -- A bijection is injective
    exact h_bij.2.1
  · -- A bijection maps exactly to its target
    exact h_bij.image_eq
  · exact ⟨hs_lower, hs_upper⟩

