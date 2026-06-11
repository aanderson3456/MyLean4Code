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

open BigOperators

/--
  Stereographic projection map Φ from the complex plane ℂ to the Riemann Sphere in ℝ³.
  Maps z = x + iy to a point (x₁, x₂, x₃) on the unit sphere in ℝ³.
-/
noncomputable def Φ (z : ℂ) : EuclideanSpace ℝ (Fin 3) :=
  WithLp.equiv 2 (Fin 3 → ℝ) |>.symm ![
    2 * z.re / (‖z‖ ^ 2 + 1),
    2 * z.im / (‖z‖ ^ 2 + 1),
    (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1)
  ]

--  Component evaluation lemmas for Φ at index 0, 1, and 2.
lemma Φ_apply_zero (z : ℂ) : Φ z 0 = 2 * z.re / (‖z‖ ^ 2 + 1) := by {
  unfold Φ
  simp
}

lemma Φ_apply_one (z : ℂ) : Φ z 1 = 2 * z.im / (‖z‖ ^ 2 + 1) := by {
  unfold Φ
  simp
}

lemma Φ_apply_two (z : ℂ) : Φ z 2 = (‖z‖ ^ 2 - 1) / (‖z‖ ^ 2 + 1) := by {
  unfold Φ
  simp
}

--  Lemma expressing the norm squared of a complex number in terms of its real and imaginary parts.
lemma norm_sq_eq_re_im (u : ℂ) : ‖u‖ ^ 2 = u.re ^ 2 + u.im ^ 2 := by {
  rw [← Complex.normSq_eq_norm_sq]
  rw [Complex.normSq_apply]
  ring
}

--  Lemma expressing the norm squared of a complex difference in terms of real coordinates.
lemma sub_norm_sq_eq_re_im (z w : ℂ) : ‖z - w‖ ^ 2 = (z.re - w.re) ^ 2 + (z.im - w.im) ^ 2 := by {
  have := norm_sq_eq_re_im (z - w)
  simp only [sub_re, sub_im] at this
  exact this
}

--  Algebraic identity establishing equality between the Euclidean distance squared in ℝ³ and the chordal metric formula.
lemma Φ_ident (z w : ℂ) :
    (Φ z 0 - Φ w 0) ^ 2 + (Φ z 1 - Φ w 1) ^ 2 + (Φ z 2 - Φ w 2) ^ 2 =
      (4 * ‖z - w‖ ^ 2) / ((‖z‖ ^ 2 + 1) * (‖w‖ ^ 2 + 1)) := by {
  rw [Φ_apply_zero, Φ_apply_one, Φ_apply_two]
  rw [Φ_apply_zero, Φ_apply_one, Φ_apply_two]
  rw [norm_sq_eq_re_im z, norm_sq_eq_re_im w, sub_norm_sq_eq_re_im z w]
  have hz_den : z.re ^ 2 + z.im ^ 2 + 1 ≠ 0 := by {
    have : 0 ≤ z.re ^ 2 + z.im ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  }
  have hw_den : w.re ^ 2 + w.im ^ 2 + 1 ≠ 0 := by {
    have : 0 ≤ w.re ^ 2 + w.im ^ 2 := add_nonneg (sq_nonneg _) (sq_nonneg _)
    linarith
  }
  field_simp
  ring
}

--  Expansion of the Euclidean distance squared of the projected points in ℝ³.
lemma dist_sq_Φ (z w : ℂ) : dist (Φ z) (Φ w) ^ 2 = (Φ z 0 - Φ w 0) ^ 2 + (Φ z 1 - Φ w 1) ^ 2 + (Φ z 2 - Φ w 2) ^ 2 := by {
  rw [EuclideanSpace.dist_sq_eq, Fin.sum_univ_three]
  simp only [Real.dist_eq]
  have h_sq (a b : ℝ) : |a - b| ^ 2 = (a - b) ^ 2 := sq_abs (a - b)
  rw [h_sq, h_sq, h_sq]
}

--  Non-negativity of the chordalMetric function.
lemma chordalMetric_nonneg (z w : ℂ) : 0 ≤ chordalMetric z w := by {
  unfold chordalMetric
  apply div_nonneg
  · apply mul_nonneg (by norm_num) (norm_nonneg _)
  · apply mul_nonneg
    · apply Real.sqrt_nonneg
    · apply Real.sqrt_nonneg
}

--  Equality of the squares of the Euclidean distance and the chordalMetric.
lemma dist_sq_eq_chordalMetric_sq (z w : ℂ) : dist (Φ z) (Φ w) ^ 2 = chordalMetric z w ^ 2 := by {
  rw [dist_sq_Φ, Φ_ident]
  unfold chordalMetric
  rw [div_pow, mul_pow]
  have h_sq1 : (2 : ℝ) ^ 2 = 4 := by norm_num
  rw [h_sq1]
  have h_sqrt_z : Real.sqrt (‖z‖ ^ 2 + 1) ^ 2 = ‖z‖ ^ 2 + 1 := by {
    apply Real.sq_sqrt
    have : 0 ≤ ‖z‖ ^ 2 := sq_nonneg ‖z‖
    linarith
  }
  have h_sqrt_w : Real.sqrt (‖w‖ ^ 2 + 1) ^ 2 = ‖w‖ ^ 2 + 1 := by {
    apply Real.sq_sqrt
    have : 0 ≤ ‖w‖ ^ 2 := sq_nonneg ‖w‖
    linarith
  }
  rw [mul_pow, h_sqrt_z, h_sqrt_w]
}

--  Euclidean distance between projected points matches the chordalMetric.
theorem dist_Φ_eq_chordalMetric (z w : ℂ) : dist (Φ z) (Φ w) = chordalMetric z w := by {
  have h_sq := dist_sq_eq_chordalMetric_sq z w
  have h_dist_nonneg : 0 ≤ dist (Φ z) (Φ w) := dist_nonneg
  have h_chordal_nonneg := chordalMetric_nonneg z w
  have h_eq : Real.sqrt (dist (Φ z) (Φ w) ^ 2) = Real.sqrt (chordalMetric z w ^ 2) := congrArg Real.sqrt h_sq
  rw [Real.sqrt_sq h_dist_nonneg, Real.sqrt_sq h_chordal_nonneg] at h_eq
  exact h_eq
}

--  Helper establishing equality of norms if two points map to the same point on the sphere.
lemma norm_eq_of_Φ_eq {z w : ℂ} (h : Φ z = Φ w) : ‖z‖ = ‖w‖ := by {
  have h2 : Φ z 2 = Φ w 2 := congrArg (fun f => f 2) h
  rw [Φ_apply_two z, Φ_apply_two w] at h2
  have hz_den : ‖z‖ ^ 2 + 1 ≠ 0 := by {
    have : 0 ≤ ‖z‖ ^ 2 := sq_nonneg ‖z‖
    linarith
  }
  have hw_den : ‖w‖ ^ 2 + 1 ≠ 0 := by {
    have : 0 ≤ ‖w‖ ^ 2 := sq_nonneg ‖w‖
    linarith
  }
  have h_mul := (div_eq_div_iff hz_den hw_den).mp h2
  have h_ring : ‖z‖ ^ 2 = ‖w‖ ^ 2 := by {
    linarith [h_mul]
  }
  have hz_nonneg := norm_nonneg z
  have hw_nonneg := norm_nonneg w
  have h_diff : (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) = 0 := by {
    calc (‖z‖ - ‖w‖) * (‖z‖ + ‖w‖) = ‖z‖ ^ 2 - ‖w‖ ^ 2 := by ring
    _ = 0 := by linarith [h_ring]
  }
  cases mul_eq_zero.mp h_diff with
  | inl h_sub => linarith [h_sub]
  | inr h_add =>
    have : ‖z‖ = 0 := by linarith [hz_nonneg, hw_nonneg, h_add]
    have : ‖w‖ = 0 := by linarith [hz_nonneg, hw_nonneg, h_add]
    linarith
}

--  Injectivity of the stereographic projection map Φ.
lemma Φ_injective : Function.Injective Φ := by {
  intro z w h
  have h_norm := norm_eq_of_Φ_eq h
  have h0 : Φ z 0 = Φ w 0 := congrArg (fun f => f 0) h
  have h1 : Φ z 1 = Φ w 1 := congrArg (fun f => f 1) h
  rw [Φ_apply_zero z, Φ_apply_zero w, h_norm] at h0
  rw [Φ_apply_one z, Φ_apply_one w, h_norm] at h1
  have hz_den : ‖w‖ ^ 2 + 1 ≠ 0 := by {
    have : 0 ≤ ‖w‖ ^ 2 := sq_nonneg ‖w‖
    linarith
  }
  have h_re : z.re = w.re := by {
    have h0' : 2 * z.re = 2 * w.re := (div_left_inj' hz_den).mp h0
    linarith
  }
  have h_im : z.im = w.im := by {
    have h1' : 2 * z.im = 2 * w.im := (div_left_inj' hz_den).mp h1
    linarith
  }
  apply Complex.ext
  · exact h_re
  · exact h_im
}

/-- Type synonym for ℂ equipped with the chordal metric. -/
def Chordalℂ : Type := ℂ

--  MetricSpace instance for Chordalℂ induced by stereographic projection.
noncomputable instance : MetricSpace Chordalℂ :=
  MetricSpace.induced (fun (z : Chordalℂ) => Φ (z : ℂ)) Φ_injective inferInstance

--  The distance on Chordalℂ matches the chordalMetric function.
theorem dist_chordalℂ_eq (z w : Chordalℂ) : dist z w = chordalMetric (z : ℂ) (w : ℂ) := by {
  exact dist_Φ_eq_chordalMetric (z : ℂ) (w : ℂ)
}

end Sarason.Ch1
