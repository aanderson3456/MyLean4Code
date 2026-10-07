import R2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.Deriv.Mul

open ComplexAnalysis.R2

lemma HasDerivAt_RtoR2_eps_iff_HasDerivAt (f : ℝ → ℝ × ℝ) (f'₀ : ℝ × ℝ) (t₀ : ℝ) :
    HasDerivAt_RtoR2_eps f f'₀ t₀ ↔ _root_.HasDerivAt f f'₀ t₀ := by
{
  rw [hasDerivAt_iff_tendsto_slope]
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, dist_eq_norm]
  unfold HasDerivAt_RtoR2_eps
  constructor
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro t ht
    have hd := hδ t ht
    -- slope f t₀ t = (t - t₀)⁻¹ • (f t - f t₀)
    -- norm (slope f t₀ t - f'₀) = norm ((t - t₀)⁻¹ • (f t - f t₀) - f'₀)
    -- = |t - t₀|⁻¹ * norm (f t - f t₀ - (t - t₀) • f'₀)
    sorry
  · sorry
}

