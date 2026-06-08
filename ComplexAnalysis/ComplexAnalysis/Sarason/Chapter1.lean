/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.InnerProductSpace.PiL2
import ComplexAnalysis.Sarason.Definitions

/-!
# Sarason - Chapter 1: Complex Numbers

Formalization of Section I of Donald Sarason's "Notes on Complex Function Theory".
Focus: The complex plane, stereographic projection, and the chordal metric.

Credit: Donald Sarason
-/

open Complex Sarason

namespace Sarason.Ch1

/-! 
  §I.14 The Extended Complex Plane and Stereographic Projection.
  Sarason introduces the Riemann Sphere as the unit sphere S in ℝ³.
  The stereographic projection maps z = x + iy to a point (x₁, x₂, x₃) on S.
-/

/-- 
  The chordal metric ρ(z, w) is the Euclidean distance in ℝ³ between 
  the stereographic projections of z and w.
-/
noncomputable def chordalMetric (z w : ℂ) : ℝ :=
  (2 * ‖z - w‖) / (Real.sqrt (‖z‖ ^ 2 + 1) * Real.sqrt (‖w‖ ^ 2 + 1))

/-- 
  The chordal distance to infinity.
  Exercise: ρ(z, ∞) = 2 / sqrt(|z|² + 1)
-/
noncomputable def chordalMetricToInf (z : ℂ) : ℝ :=
  2 / Real.sqrt (‖z‖ ^ 2 + 1)

/-- 
  Exercise from §I.14:
  Show that the chordal distance from z to infinity is given by 2 / sqrt(|z|² + 1).
  Using the Weierstrass definition of limits.
-/
lemma test_h (z w : ℂ) (ε' : ℝ) (hε' : 0 < ε') 
    (hw : (‖z‖ + 2) / ε' + 1 < ‖w‖) 
    (h_w_pos : 0 < ‖w‖) 
    (h_sqrt_w_pos : 0 < Real.sqrt (‖w‖ ^ 2 + 1)) : 
    ‖z - w‖ / Real.sqrt (‖w‖ ^ 2 + 1) - 1 < ε' := by {
  have h_w_lt_sqrt : ‖w‖ ≤ Real.sqrt (‖w‖ ^ 2 + 1) := by {
    calc ‖w‖ = Real.sqrt (‖w‖ ^ 2) := by rw [Real.sqrt_sq (norm_nonneg w)]
    _ ≤ Real.sqrt (‖w‖ ^ 2 + 1) := Real.sqrt_le_sqrt (by linarith)
  }
  have h_z_lt : ‖z‖ < ε' * ‖w‖ := by {
    have h_div : (‖z‖ + 2) / ε' < ‖w‖ := by linarith
    have h_mul : ‖z‖ + 2 < ε' * ‖w‖ := by {
      rwa [div_lt_iff₀ hε', mul_comm ‖w‖] at h_div
    }
    linarith
  }
  have h_num : ‖z - w‖ ≤ ‖z‖ + ‖w‖ := norm_sub_le z w
  have h_lt : ‖z - w‖ < (1 + ε') * Real.sqrt (‖w‖ ^ 2 + 1) := by {
    calc ‖z - w‖ ≤ ‖z‖ + ‖w‖ := h_num
    _ < ε' * ‖w‖ + ‖w‖ := by linarith
    _ = (1 + ε') * ‖w‖ := by ring
    _ ≤ (1 + ε') * Real.sqrt (‖w‖ ^ 2 + 1) := by {
      apply mul_le_mul_of_nonneg_left h_w_lt_sqrt
      linarith
    }
  }
  have h_lt' : ‖z - w‖ / Real.sqrt (‖w‖ ^ 2 + 1) < 1 + ε' := by {
    rwa [div_lt_iff₀ h_sqrt_w_pos]
  }
  linarith
}

lemma test_h_lower (z w : ℂ) (ε' : ℝ) (hε' : 0 < ε') 
    (hw : (‖z‖ + 2) / ε' + 1 < ‖w‖) 
    (h_w_pos : 0 < ‖w‖) 
    (h_sqrt_w_pos : 0 < Real.sqrt (‖w‖ ^ 2 + 1)) : 
    -(ε') < ‖z - w‖ / Real.sqrt (‖w‖ ^ 2 + 1) - 1 := by {
  have h_sqrt_lt_w_add_one : Real.sqrt (‖w‖ ^ 2 + 1) < ‖w‖ + 1 := by {
    rw [Real.sqrt_lt']
    · have : (‖w‖ + 1) ^ 2 = ‖w‖ ^ 2 + 2 * ‖w‖ + 1 := by ring
      rw [this]
      linarith
    · linarith
  }
  by_cases h_eps : 1 - ε' ≤ 0
  · have h_eps_ge : 1 ≤ ε' := by linarith
    have h_rhs_ge : -1 ≤ ‖z - w‖ / Real.sqrt (‖w‖ ^ 2 + 1) - 1 := by {
      have : 0 ≤ ‖z - w‖ / Real.sqrt (‖w‖ ^ 2 + 1) := by {
        apply div_nonneg (norm_nonneg _) (Real.sqrt_nonneg _)
      }
      linarith
    }
    rcases lt_or_eq_of_le h_eps_ge with h_eps_gt | h_eps_eq
    · -- 1 < ε'
      have : -ε' < -1 := by linarith
      linarith
    · -- 1 = ε'
      have h_norm_lt : ‖z‖ < ‖w‖ := by {
        have h_div : (‖z‖ + 2) / ε' + 1 < ‖w‖ := hw
        rw [← h_eps_eq] at h_div
        linarith
      }
      have h_zw_ne : z ≠ w := by {
        intro h_eq
        rw [h_eq] at h_norm_lt
        linarith
      }
      have h_zw_pos : 0 < ‖z - w‖ := by {
        rwa [norm_pos_iff, sub_ne_zero]
      }
      have h_div_pos : 0 < ‖z - w‖ / Real.sqrt (‖w‖ ^ 2 + 1) := by {
        apply div_pos h_zw_pos h_sqrt_w_pos
      }
      linarith
  · have h_eps : 0 < 1 - ε' := by linarith
    have h_w_minus_z : ‖w‖ - ‖z‖ ≤ ‖z - w‖ := by {
      have h_tri := norm_sub_norm_le w z
      rw [norm_sub_rev w z] at h_tri
      exact h_tri
    }
    have h_z_lt : 1 + ‖z‖ < ε' * (‖w‖ + 1) := by {
      have h_div : (‖z‖ + 2) / ε' + 1 < ‖w‖ := hw
      have h_ineq : (‖z‖ + 1) / ε' < ‖w‖ - 1 := by {
        have : (‖z‖ + 1) / ε' < (‖z‖ + 2) / ε' := by {
          apply div_lt_div_of_pos_right _ hε'
          linarith
        }
        linarith
      }
      have h_mul : ‖z‖ + 1 < ε' * (‖w‖ - 1) := by {
        rwa [div_lt_iff₀ hε', mul_comm] at h_ineq
      }
      have h_ineq2 : ε' * (‖w‖ - 1) < ε' * (‖w‖ + 1) := mul_lt_mul_of_pos_left (by linarith) hε'
      linarith
    }
    have h_lt : (1 - ε') * Real.sqrt (‖w‖ ^ 2 + 1) < ‖z - w‖ := by {
      calc (1 - ε') * Real.sqrt (‖w‖ ^ 2 + 1)
        _ < (1 - ε') * (‖w‖ + 1) := mul_lt_mul_of_pos_left h_sqrt_lt_w_add_one h_eps
        _ = ‖w‖ + 1 - ε' * (‖w‖ + 1) := by ring
        _ < ‖w‖ - ‖z‖ := by linarith
        _ ≤ ‖z - w‖ := h_w_minus_z
    }
    have h_lt' : 1 - ε' < ‖z - w‖ / Real.sqrt (‖w‖ ^ 2 + 1) := by {
      rwa [lt_div_iff₀ h_sqrt_w_pos]
    }
    linarith
}

theorem chordal_dist_limit (z : ℂ) :
    HasLimitAtInf_eps (fun w => chordalMetric z w) (chordalMetricToInf z) := by {
  unfold HasLimitAtInf_eps chordalMetric chordalMetricToInf
  intro ε hε
  let C := 2 / Real.sqrt (‖z‖ ^ 2 + 1)
  have hC : 0 < C := by {
    apply div_pos (by norm_num)
    apply Real.sqrt_pos.mpr
    have : 0 ≤ ‖z‖ ^ 2 := sq_nonneg ‖z‖
    linarith
  }
  let ε' := ε / C
  have hε' : 0 < ε' := div_pos hε hC
  use (2 * ‖z‖ + 2 + (4 * ‖z‖ + 4) / ε')
  constructor
  · have h_z_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
    have h1 : 0 < 2 * ‖z‖ + 2 := by linarith
    have h2 : 0 < (4 * ‖z‖ + 4) / ε' := by {
      apply div_pos (by linarith) hε'
    }
    linarith
  · intro w hw
    have h_w_pos : 0 < ‖w‖ := by {
      have : 0 < 2 * ‖z‖ + 2 + (4 * ‖z‖ + 4) / ε' := by {
        have h_z_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
        have h1 : 0 < 2 * ‖z‖ + 2 := by linarith
        have h2 : 0 < (4 * ‖z‖ + 4) / ε' := by {
          apply div_pos (by linarith) hε'
        }
        linarith
      }
      linarith
    }
    have h_sqrt_w_pos : 0 < Real.sqrt (‖w‖ ^ 2 + 1) := by {
      apply Real.sqrt_pos.mpr
      have : 0 ≤ ‖w‖ ^ 2 := sq_nonneg ‖w‖
      linarith
    }
    have hw' : (‖z‖ + 2) / ε' + 1 < ‖w‖ := by {
      have h_z_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
      have h_div1 : (‖z‖ + 2) / ε' < (4 * ‖z‖ + 4) / ε' := by {
        rw [add_div, add_div]
        have h_z : ‖z‖ / ε' ≤ 4 * ‖z‖ / ε' := by {
          apply div_le_div_of_nonneg_right _ hε'.le
          linarith [norm_nonneg z]
        }
        have h_const : 2 / ε' < 4 / ε' := by {
          apply div_lt_div_of_pos_right (by norm_num) hε'
        }
        linarith
      }
      linarith
    }
    have h_upper := test_h z w ε' hε' hw' h_w_pos h_sqrt_w_pos
    have h_lower := test_h_lower z w ε' hε' hw' h_w_pos h_sqrt_w_pos
    have h_factor : (2 * ‖z - w‖) / (Real.sqrt (‖z‖ ^ 2 + 1) * Real.sqrt (‖w‖ ^ 2 + 1)) - 2 / Real.sqrt (‖z‖ ^ 2 + 1)
        = C * (‖z - w‖ / Real.sqrt (‖w‖ ^ 2 + 1) - 1) := by {
      unfold C
      ring
    }
    rw [h_factor, abs_mul, abs_of_pos hC]
    have h_abs : |‖z - w‖ / Real.sqrt (‖w‖ ^ 2 + 1) - 1| < ε' := by {
      rw [abs_lt]
      exact ⟨h_lower, h_upper⟩
    }
    have : C * |‖z - w‖ / Real.sqrt (‖w‖ ^ 2 + 1) - 1| < C * ε' := by {
      apply mul_lt_mul_of_pos_left h_abs hC
    }
    have h_eq : C * ε' = ε := by {
      unfold ε'
      rw [mul_div_cancel₀ ε hC.ne']
    }
    linarith
}

end Sarason.Ch1
