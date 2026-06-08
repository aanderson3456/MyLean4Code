import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set

open MeasureTheory Set ENNReal
open scoped ENNReal

example (p : ℝ) (hc : (∫⁻ r in Ioo 0 (1/2), ENNReal.ofReal (r ^ (3 - p)) ∂volume) < ⊤) :
    IntegrableOn (fun r : ℝ ↦ r ^ (3 - p)) (Ioo 0 (1/2)) volume := by {
  constructor
  · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
    intro x hx
    apply ContinuousAt.continuousWithinAt
    apply Real.continuousAt_rpow_const
    left
    exact hx.1.ne'
  · have h_eq_lintegral : (∫⁻ x, (‖(x : ℝ) ^ (3 - p)‖₊ : ℝ≥0∞) ∂(volume.restrict (Ioo 0 (1/2)))) =
        (∫⁻ r in Ioo 0 (1/2), ENNReal.ofReal (r ^ (3 - p)) ∂volume) := by {
      apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
      have hr_pos : 0 < r := hr.1
      have hrpow_nonneg : 0 ≤ r ^ (3 - p) := Real.rpow_nonneg hr_pos.le (3 - p)
      rw [Real.nnnorm_of_nonneg hrpow_nonneg]
      rw [ENNReal.ofReal]
      rw [Real.toNNReal_of_nonneg hrpow_nonneg]
    }
    change (∫⁻ x, (‖(x : ℝ) ^ (3 - p)‖₊ : ℝ≥0∞) ∂(volume.restrict (Ioo 0 (1/2)))) < ⊤
    rw [h_eq_lintegral]
    exact hc
}
