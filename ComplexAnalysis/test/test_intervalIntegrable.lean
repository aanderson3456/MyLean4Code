import Mathlib.Analysis.Complex.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

open Complex Filter TopologicalSpace Metric Bornology Classical MeasureTheory

lemma intervalIntegrable_of_zero {f : ℝ → ℝ} {a b : ℝ} 
    (hf : ∀ T > 0, IntervalIntegrable f volume 0 T) (ha : 0 < a) (hb : 0 < b) : 
    IntervalIntegrable f volume a b := by
{
  have h1 := hf a ha
  have h2 := hf b hb
  exact h1.symm.trans h2
}
