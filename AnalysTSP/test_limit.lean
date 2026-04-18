import Mathlib
import AnalysTSP.WeierstrassLimitR2

example (u : ℕ → ℝ) (φ : ℕ → ℕ) (a : ℝ) (h_tendsto : Filter.Tendsto (u ∘ φ) Filter.atTop (nhds a)) :
  ConvergesR (u ∘ φ) a := by
  intro ε hε
  rw [Metric.tendsto_atTop] at h_tendsto
  rcases h_tendsto ε hε with ⟨N, hN⟩
  use N
  intro n hn
  have hd := hN n hn
  rw [Real.dist_eq, abs_sub_comm] at hd
  exact hd
