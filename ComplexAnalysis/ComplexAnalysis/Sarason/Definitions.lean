/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope

/-!
# Sarason - Definitions

Weierstrass-style definitions for limits, derivatives, and continuity to maintain the 
classical flavor of Sarason's notes, along with equivalence theorems to Mathlib filters.
-/

open Complex Filter TopologicalSpace Metric Bornology

namespace Sarason

--  Weierstrass definition of a limit at a finite point.
def HasLimitAt_eps (f : ℂ → ℂ) (L : ℂ) (z₀ : ℂ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ z, 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < δ → ‖f z - L‖ < ε

--  Weierstrass definition of a limit at infinity.
def HasLimitAtInf_eps (f : ℂ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ M > 0, ∀ z, ‖z‖ > M → |f z - L| < ε

--  Weierstrass definition of having a complex derivative at z₀.
def HasDerivAt_eps (f : ℂ → ℂ) (f' : ℂ) (z₀ : ℂ) : Prop :=
  HasLimitAt_eps (fun z => (f z - f z₀) / (z - z₀)) f' z₀

--  Weierstrass definition of complex differentiability at z₀.
def DifferentiableAt_eps (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ f', HasDerivAt_eps f f' z₀

-- Weierstrass definition of partial derivative with respect to x.
def HasPartialDerivX_C_to_R_eps (u : ℂ → ℝ) (ux : ℝ) (z₀ : ℂ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - z₀.re| ∧ |x - z₀.re| < δ →
    |(u ((x : ℂ) + (z₀.im : ℂ) * I) - u z₀) / (x - z₀.re) - ux| < ε

-- Weierstrass definition of partial derivative with respect to y.
def HasPartialDerivY_C_to_R_eps (u : ℂ → ℝ) (uy : ℝ) (z₀ : ℂ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y : ℝ, 0 < |y - z₀.im| ∧ |y - z₀.im| < δ →
    |(u ((z₀.re : ℂ) + (y : ℂ) * I) - u z₀) / (y - z₀.im) - uy| < ε

--  Equivalence theorem between Mathlib's limit at a point (using punctured neighborhoods) and Weierstrass epsilon-delta limit.
theorem tendsto_nhds_iff_eps (f : ℂ → ℂ) (L z₀ : ℂ) :
    Tendsto f (nhdsWithin z₀ {z₀}ᶜ) (nhds L) ↔ HasLimitAt_eps f L z₀ := by {
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, dist_eq_norm]
  unfold HasLimitAt_eps
  simp only [and_imp]
  have h_ne (x : ℂ) : 0 < ‖x - z₀‖ ↔ x ≠ z₀ := by {
    rw [norm_pos_iff, sub_ne_zero]
  }
  simp only [h_ne]
}

--  Equivalence theorem between Mathlib's limit at infinity (using cobounded filter) and Weierstrass epsilon-delta limit at infinity.
theorem tendsto_cobounded_iff_eps (f : ℂ → ℝ) (L : ℝ) :
    Tendsto f (cobounded ℂ) (nhds L) ↔ HasLimitAtInf_eps f L := by {
  rw [(Metric.hasBasis_cobounded_compl_ball (0 : ℂ)).tendsto_iff nhds_basis_ball]
  simp only [Set.mem_compl_iff, mem_ball, dist_zero_right, true_and, Real.dist_eq]
  unfold HasLimitAtInf_eps
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨r, hr⟩
    use max r 1
    constructor
    · exact lt_of_lt_of_le zero_lt_one (le_max_right _ _)
    · intro z hz
      apply hr
      intro hz'
      have : ‖z‖ ≤ r := by {
        exact hz'.le
      }
      have : ‖z‖ ≤ max r 1 := by {
        exact this.trans (le_max_left _ _)
      }
      exact not_lt.mpr this hz
  · intro h ε hε
    rcases h ε hε with ⟨M, hM, hr⟩
    use M + 1
    intro z hz
    apply hr
    have h_ge : ‖z‖ ≥ M + 1 := by {
      exact not_lt.mp hz
    }
    exact lt_of_lt_of_le (lt_add_one M) h_ge
}

--  Equivalence theorem between Mathlib's derivative at a point and Weierstrass derivative.
theorem hasDerivAt_iff_eps (f : ℂ → ℂ) (f' z₀ : ℂ) :
    _root_.HasDerivAt f f' z₀ ↔ HasDerivAt_eps f f' z₀ := by {
  rw [hasDerivAt_iff_tendsto_slope]
  rw [tendsto_nhds_iff_eps]
  unfold HasDerivAt_eps
  rw [slope_fun_def_field]
}

--  Equivalence theorem between Mathlib's differentiability at a point and Weierstrass differentiability.
theorem differentiableAt_iff_eps (f : ℂ → ℂ) (z₀ : ℂ) :
    _root_.DifferentiableAt ℂ f z₀ ↔ DifferentiableAt_eps f z₀ := by {
  unfold DifferentiableAt_eps
  constructor
  · intro h
    use deriv f z₀
    rw [← hasDerivAt_iff_eps]
    exact h.hasDerivAt
  · rintro ⟨f', hf'⟩
    rw [← hasDerivAt_iff_eps] at hf'
    exact hf'.differentiableAt
}

-- Equivalence theorem between Mathlib's 1D derivative at a point (using filters) and Weierstrass epsilon-delta limit.
theorem hasDerivAt_R_iff_eps (f : ℝ → ℝ) (f' x₀ : ℝ) :
    _root_.HasDerivAt f f' x₀ ↔ ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - x₀| ∧ |x - x₀| < δ → |(f x - f x₀) / (x - x₀) - f'| < ε := by {
  rw [hasDerivAt_iff_tendsto_slope]
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, Real.dist_eq]
  rw [slope_fun_def_field]
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x ⟨hx1, hx2⟩
    have hx_ne : x ≠ x₀ := sub_ne_zero.mp (abs_pos.mp hx1)
    exact hδ hx_ne hx2
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x hx_ne hx2
    apply hδ
    refine ⟨?_, hx2⟩
    exact abs_pos.mpr (sub_ne_zero.mpr hx_ne)
}

theorem hasPartialDerivX_iff_eps (u : ℂ → ℝ) (ux : ℝ) (z₀ : ℂ) :
    _root_.HasDerivAt (fun x : ℝ ↦ u ((x : ℂ) + (z₀.im : ℂ) * I)) ux z₀.re ↔ HasPartialDerivX_C_to_R_eps u ux z₀ := by {
  rw [hasDerivAt_R_iff_eps]
  unfold HasPartialDerivX_C_to_R_eps
  have h_eq : ((z₀.re : ℂ) + (z₀.im : ℂ) * I) = z₀ := by {
    exact Complex.re_add_im z₀
  }
  rw [h_eq]
}

theorem hasPartialDerivY_iff_eps (u : ℂ → ℝ) (uy : ℝ) (z₀ : ℂ) :
    _root_.HasDerivAt (fun y : ℝ ↦ u ((z₀.re : ℂ) + (y : ℂ) * I)) uy z₀.im ↔ HasPartialDerivY_C_to_R_eps u uy z₀ := by {
  rw [hasDerivAt_R_iff_eps]
  unfold HasPartialDerivY_C_to_R_eps
  have h_eq : ((z₀.re : ℂ) + (z₀.im : ℂ) * I) = z₀ := by {
    exact Complex.re_add_im z₀
  }
  rw [h_eq]
}

end Sarason

