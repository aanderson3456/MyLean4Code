/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Topology.Path
import ComplexAnalysis.R2

/-!
# Sarason - Definitions

Weierstrass-style definitions for limits, derivatives, and continuity to maintain the 
classical flavor of Sarason's notes, along with equivalence theorems to Mathlib filters.
-/

open Complex Filter TopologicalSpace Metric Bornology ComplexAnalysis.R2

namespace Sarason



--  Weierstrass definition of a limit at a finite point.
def HasLimitAt_eps (f : ℂ → ℂ) (L : ℂ) (z₀ : ℂ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ z, 0 < ‖z - z₀‖ ∧ ‖z - z₀‖ < δ → ‖f z - L‖ < ε

--  Weierstrass definition of a limit at infinity.
def HasLimitAtInf_eps (f : ℂ → ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ M > 0, ∀ z, ‖z‖ > M → |f z - L| < ε

--  Weierstrass definition of having a complex derivative at z₀.
def HasDerivAt_eps (f : ℂ → ℂ) (f'₀ : ℂ) (z₀ : ℂ) : Prop :=
  HasLimitAt_eps (fun z => (f z - f z₀) / (z - z₀)) f'₀ z₀

--  Weierstrass definition of complex differentiability at z₀.
def DifferentiableAt_eps (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∃ f'₀, HasDerivAt_eps f f'₀ z₀

-- Weierstrass definition of partial derivative with respect to x.
def HasPartialDerivX_C_to_R_eps (u : ℂ → ℝ) (ux₀ : ℝ) (z₀ : ℂ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - z₀.re| ∧ |x - z₀.re| < δ →
    |(u ((x : ℂ) + (z₀.im : ℂ) * I) - u z₀) / (x - z₀.re) - ux₀| < ε

-- Weierstrass definition of partial derivative with respect to y.
def HasPartialDerivY_C_to_R_eps (u : ℂ → ℝ) (uy₀ : ℝ) (z₀ : ℂ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y : ℝ, 0 < |y - z₀.im| ∧ |y - z₀.im| < δ →
    |(u ((z₀.re : ℂ) + (y : ℂ) * I) - u z₀) / (y - z₀.im) - uy₀| < ε

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
theorem hasDerivAt_iff_eps (f : ℂ → ℂ) (f'₀ z₀ : ℂ) :
    _root_.HasDerivAt f f'₀ z₀ ↔ HasDerivAt_eps f f'₀ z₀ := by {
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
  · rintro ⟨f'₀, hf'₀⟩
    rw [← hasDerivAt_iff_eps] at hf'₀
    exact hf'₀.differentiableAt
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

theorem hasPartialDerivX_iff_eps (u : ℂ → ℝ) (ux₀ : ℝ) (z₀ : ℂ) :
    _root_.HasDerivAt (fun x : ℝ ↦ u ((x : ℂ) + (z₀.im : ℂ) * I)) ux₀ z₀.re ↔ HasPartialDerivX_C_to_R_eps u ux₀ z₀ := by {
  rw [hasDerivAt_R_iff_eps]
  unfold HasPartialDerivX_C_to_R_eps
  have h_eq : ((z₀.re : ℂ) + (z₀.im : ℂ) * I) = z₀ := by {
    exact Complex.re_add_im z₀
  }
  rw [h_eq]
}

theorem hasPartialDerivY_iff_eps (u : ℂ → ℝ) (uy₀ : ℝ) (z₀ : ℂ) :
    _root_.HasDerivAt (fun y : ℝ ↦ u ((z₀.re : ℂ) + (y : ℂ) * I)) uy₀ z₀.im ↔ HasPartialDerivY_C_to_R_eps u uy₀ z₀ := by {
  rw [hasDerivAt_R_iff_eps]
  unfold HasPartialDerivY_C_to_R_eps
  have h_eq : ((z₀.re : ℂ) + (z₀.im : ℂ) * I) = z₀ := by {
    exact Complex.re_add_im z₀
  }
  rw [h_eq]
}

open Classical

noncomputable def deriv_eps (f : ℂ → ℂ) (z₀ : ℂ) (h : DifferentiableAt_eps f z₀) : ℂ :=
  Classical.choose h

theorem deriv_eq_deriv_eps (f : ℂ → ℂ) (z₀ : ℂ) (h : DifferentiableAt_eps f z₀) : 
    deriv f z₀ = deriv_eps f z₀ h := by {
  unfold deriv_eps
  have h1 : HasDerivAt_eps f (Classical.choose h) z₀ := Classical.choose_spec h
  have h2 : HasDerivAt f (Classical.choose h) z₀ := (hasDerivAt_iff_eps f _ _).mpr h1
  exact h2.deriv
}


def HasDerivAt_R_to_C_eps (f : ℝ → ℂ) (f'₀ : ℂ) (t₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 < |t - t₀| ∧ |t - t₀| < δ → ‖(f t - f t₀) / ((t - t₀ : ℝ) : ℂ) - f'₀‖ < ε

theorem hasDerivAt_R_to_C_iff_eps (f : ℝ → ℂ) (f'₀ : ℂ) (t₀ : ℝ) :
    _root_.HasDerivAt f f'₀ t₀ ↔ HasDerivAt_R_to_C_eps f f'₀ t₀ := by {
  rw [hasDerivAt_iff_tendsto_slope]
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, dist_eq_norm]
  unfold HasDerivAt_R_to_C_eps
  have h_slope : ∀ x, x ≠ t₀ → slope f t₀ x = (f x - f t₀) / ((x - t₀ : ℝ) : ℂ) := by {
    intro x hx
    unfold slope
    simp only [vsub_eq_sub]
    have h1 : (x - t₀)⁻¹ • (f x - f t₀) = ((x - t₀ : ℝ) : ℂ)⁻¹ * (f x - f t₀) := by {
      rw [Complex.real_smul]
      congr 1
      exact ofReal_inv (x - t₀)
    }
    rw [h1]
    have h2 : (f x - f t₀) / ((x - t₀ : ℝ) : ℂ) = (f x - f t₀) * ((x - t₀ : ℝ) : ℂ)⁻¹ := by {
      exact div_eq_mul_inv (f x - f t₀) ((x - t₀ : ℝ) : ℂ)
    }
    rw [h2, mul_comm]
  }
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x ⟨hx1, hx2⟩
    have hx_ne : x ≠ t₀ := sub_ne_zero.mp (abs_pos.mp hx1)
    have h_eval := hδ hx_ne hx2
    rw [← h_slope x hx_ne]
    exact h_eval
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x hx_ne hx2
    have hx1 : 0 < |x - t₀| := abs_pos.mpr (sub_ne_zero.mpr hx_ne)
    have h_eval2 := hδ x ⟨hx1, hx2⟩
    rw [h_slope x hx_ne]
    exact h_eval2
}

/-- A function is holomorphic at a point if it is complex differentiable at that point.
    (Often this is defined as differentiable in a neighborhood, but in these notes it frequently refers to pointwise differentiability). -/
def HolomorphicAt_eps (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  DifferentiableAt_eps f z₀

/-- A function is holomorphic on a set if it is complex differentiable at every point of the set. -/
def HolomorphicOn_eps (f : ℂ → ℂ) (G : Set ℂ) : Prop :=
  ∀ z ∈ G, DifferentiableAt_eps f z

end Sarason

/-!
  NOTE FOR FUTURE AGENTS: 
  Currently, some theorems in `Chapter2.lean` (such as `conformal_implies_holomorphic`) 
  use Mathlib's `DifferentiableAt ℝ f z` to represent continuous first partial derivatives / real-differentiability.
  Eventually, we want to replace this with our own custom epsilon-delta definitions 
  (similar to `HasDerivAt_eps`) that will define $\mathbb{R}^2$ differentiability from scratch.
-/

-- R^2 Euclidean Metrics (from AnalysTSP)

