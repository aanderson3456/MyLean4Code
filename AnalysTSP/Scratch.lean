import Mathlib
import AnalyticTSP

open Set MeasureTheory Topology

lemma test_hausdorff_pow (φ : ℝ → ℝ × ℝ) (r : ENNReal) (t : ℕ → Set (ℝ × ℝ)) :
  (∑' (n : ℕ), ⨆ (_ : (t n).Nonempty), Metric.ediam (t n) ^ (1 : ℝ≥0)) = (∑' (n : ℕ), ⨆ (_ : (t n).Nonempty), Metric.ediam (t n)) := by {
  -- Let's test what simplifies this
  simp
}
