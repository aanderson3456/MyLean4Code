import Mathlib
import AnalysTSP.WeierstrassLimitR2

example : UnitInterval = Set.Icc (0 : ℝ) 1 := rfl

example (u : ℕ → ℝ) (hu : ∀ n, u n ∈ UnitInterval) : 
  ∃ a ∈ UnitInterval, ∃ φ : ℕ → ℕ, StrictMono φ ∧ Filter.Tendsto (u ∘ φ) Filter.atTop (nhds a) := by
  have hicc : ∀ n, u n ∈ Set.Icc (0:ℝ) 1 := hu
  exact isCompact_Icc.isSeqCompact hicc
