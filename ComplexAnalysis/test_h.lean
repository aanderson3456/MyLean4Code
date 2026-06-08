import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Instances.Complex
import Mathlib.Analysis.InnerProductSpace.PiL2
import ComplexAnalysis.Sarason.Definitions
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Group.Measure

open Complex Sarason MeasureTheory ENNReal Set
open scoped ENNReal



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

noncomputable def chordalMetric (z w : ℂ) : ℝ :=
  (2 * ‖z - w‖) / (Real.sqrt (‖z‖ ^ 2 + 1) * Real.sqrt (‖w‖ ^ 2 + 1))

noncomputable def chordalMetricToInf (z : ℂ) : ℝ :=
  2 / Real.sqrt (‖z‖ ^ 2 + 1)

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

open MeasureTheory

lemma test_polar_indicator (f : ℂ → ℝ≥0∞) (s : Set ℂ) (hs : MeasurableSet s) :
    (∫⁻ p in s, f p) = ∫⁻ p in (polarCoord.target ∩ (Complex.polarCoord.symm ⁻¹' s)),
      (ENNReal.ofReal p.1) * f (Complex.polarCoord.symm p) := by {
  have h_cont : Continuous Complex.polarCoord.symm := by {
    have h_fun_eq : (Complex.polarCoord.symm : ℝ × ℝ → ℂ) = fun p ↦ p.1 * (Real.cos p.2 + Real.sin p.2 * Complex.I) := by {
      ext p
      exact Complex.polarCoord_symm_apply p
    }
    rw [h_fun_eq]
    fun_prop
  }
  rw [← lintegral_indicator hs]
  rw [← Complex.lintegral_comp_polarCoord_symm (s.indicator f)]
  have h_meas : MeasurableSet (polarCoord.target ∩ Complex.polarCoord.symm ⁻¹' s) := by {
    apply MeasurableSet.inter
    · exact polarCoord.open_target.measurableSet
    · exact hs.preimage h_cont.measurable
  }
  rw [← lintegral_indicator polarCoord.open_target.measurableSet]
  rw [← lintegral_indicator h_meas]
  congr 1
  ext p
  by_cases hp : p ∈ polarCoord.target
  · rw [Set.indicator_of_mem hp]
    by_cases hps : Complex.polarCoord.symm p ∈ s
    · rw [Set.indicator_of_mem hps]
      have hps2 : p ∈ Complex.polarCoord.symm ⁻¹' s := hps
      have hp_mem : p ∈ polarCoord.target ∩ Complex.polarCoord.symm ⁻¹' s := ⟨hp, hps2⟩
      rw [Set.indicator_of_mem hp_mem]
      simp only [smul_eq_mul]
    · rw [Set.indicator_of_notMem hps]
      have hps2 : p ∉ Complex.polarCoord.symm ⁻¹' s := hps
      have hp_mem : p ∉ polarCoord.target ∩ Complex.polarCoord.symm ⁻¹' s := by {
        intro h
        exact hps2 h.2
      }
      rw [Set.indicator_of_notMem hp_mem]
      simp only [smul_eq_mul, mul_zero]
  · rw [Set.indicator_of_notMem hp]
    have hp_mem : p ∉ polarCoord.target ∩ Complex.polarCoord.symm ⁻¹' s := by {
      intro h
      exact hp h.1
    }
    rw [Set.indicator_of_notMem hp_mem]
}

lemma lintegral_prod_mul {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (f : α → ℝ≥0∞) (g : β → ℝ≥0∞)
    (hf : AEMeasurable f μ) (hg : AEMeasurable g ν) :
    (∫⁻ p, f p.1 * g p.2 ∂(μ.prod ν)) = (∫⁻ x, f x ∂μ) * (∫⁻ y, g y ∂ν) := by {
  have h_ae : AEMeasurable (fun p : α × β => f p.1 * g p.2) (μ.prod ν) := by {
    apply AEMeasurable.mul
    · exact hf.comp_fst
    · exact hg.comp_snd
  }
  rw [lintegral_prod _ h_ae]
  exact lintegral_lintegral_mul hf hg
}

lemma test_sub_preserving : MeasurePreserving (fun z : ℂ ↦ 1 - z) volume volume := by {
  have h1 : MeasurePreserving (fun z : ℂ ↦ -z) volume volume := (LinearIsometryEquiv.neg ℝ : ℂ ≃ₗᵢ[ℝ] ℂ).measurePreserving
  have h2 : MeasurePreserving (fun z : ℂ ↦ 1 + z) volume volume := measurePreserving_add_left volume 1
  have h_comp := h2.comp h1
  have h_eq : (fun z : ℂ ↦ 1 + -z) = (fun z : ℂ ↦ 1 - z) := by {
    ext z
    rw [sub_eq_add_neg]
  }
  rw [← h_eq]
  exact h_comp
}

def R : Set (ℝ × ℝ) := Ioo (0 : ℝ) (1/2) ×ˢ Ioo (-(Real.pi/4)) (Real.pi/4)

def S0 : Set ℂ := { z | 0 < ‖z‖ ∧ ‖z‖ < 1/2 ∧ z.arg ∈ Ioo (-(Real.pi/4)) (Real.pi/4) }

lemma test_domain_eq (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
    Complex.polarCoord.symm p ∈ S0 ↔ p ∈ R := by {
  have h_eq : Complex.polarCoord (Complex.polarCoord.symm p) = p := Complex.polarCoord.right_inv hp
  have h_apply : Complex.polarCoord (Complex.polarCoord.symm p) = (‖Complex.polarCoord.symm p‖, Complex.arg (Complex.polarCoord.symm p)) := Complex.polarCoord_apply _
  rw [h_apply] at h_eq
  have h_fst : ‖Complex.polarCoord.symm p‖ = p.1 := congrArg Prod.fst h_eq
  have h_snd : Complex.arg (Complex.polarCoord.symm p) = p.2 := congrArg Prod.snd h_eq
  constructor
  · intro h
    simp only [S0, mem_setOf_eq] at h
    obtain ⟨_, h1, h2⟩ := h
    rw [h_fst] at h1
    rw [h_snd] at h2
    simp only [R, mem_prod, mem_Ioo]
    have hp_target : 0 < p.1 := hp.1
    exact ⟨⟨hp_target, h1⟩, h2⟩
  · intro h
    simp only [R, mem_prod, mem_Ioo] at h
    simp only [S0, mem_setOf_eq]
    rw [h_fst, h_snd]
    exact ⟨h.1.1, h.1.2, h.2⟩
}

lemma test_sector_in_disk (z : ℂ) (hz : z ∈ S0) : ‖1 - z‖ < 1 := by {
  simp only [S0, mem_setOf_eq] at hz
  obtain ⟨hz_norm_pos, hz_norm, hz_arg⟩ := hz
  rw [mem_Ioo] at hz_arg
  have h_norm_sq : ‖1 - z‖^2 = 1 - 2 * z.re + ‖z‖^2 := by {
    have : ‖1 - z‖^2 = Complex.normSq (1 - z) := by rw [Complex.normSq_eq_norm_sq]
    rw [this]
    simp only [sub_re, one_re, sub_im, one_im, zero_sub, normSq_apply]
    have h_z_norm_sq : ‖z‖^2 = z.re^2 + z.im^2 := by {
      rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply]
      ring
    }
    rw [h_z_norm_sq]
    ring
  }
  have h_cos_gt : Real.cos (Real.pi / 4) < Real.cos z.arg := by {
    rw [← Real.cos_abs z.arg]
    have h_abs : |z.arg| < Real.pi / 4 := abs_lt.mpr hz_arg
    have h_zero : 0 ≤ |z.arg| := abs_nonneg _
    have h_le : |z.arg| < Real.pi := by {
      have : Real.pi / 4 < Real.pi := by linarith [Real.pi_pos]
      linarith
    }
    have h_pi_four : Real.pi / 4 ∈ Set.Icc 0 Real.pi := ⟨by linarith [Real.pi_pos], by linarith [Real.pi_pos]⟩
    exact Real.strictAntiOn_cos ⟨h_zero, h_le.le⟩ h_pi_four h_abs
  }
  have h_re : z.re = ‖z‖ * Real.cos z.arg := (Complex.norm_mul_cos_arg z).symm
  have h_cos_pi_div_four : Real.cos (Real.pi / 4) = Real.sqrt 2 / 2 := Real.cos_pi_div_four
  rw [h_cos_pi_div_four] at h_cos_gt
  have h_re_gt : ‖z‖ * (Real.sqrt 2 / 2) < z.re := by {
    rw [h_re]
    apply mul_lt_mul_of_pos_left h_cos_gt hz_norm_pos
  }
  have h_two_re : ‖z‖ * Real.sqrt 2 < 2 * z.re := by {
    linarith
  }
  have h_sqrt2_gt_one : 1 < Real.sqrt 2 := by {
    rw [Real.lt_sqrt (by norm_num)]
    norm_num
  }
  have h_norm_lt_two_re : ‖z‖^2 < 2 * z.re := by {
    calc ‖z‖^2 = ‖z‖ * ‖z‖ := by ring
    _ < ‖z‖ * (1/2) := by {
      apply mul_lt_mul_of_pos_left hz_norm hz_norm_pos
    }
    _ = ‖z‖ / 2 := by ring
    _ < ‖z‖ * Real.sqrt 2 := by {
      apply mul_lt_mul_of_pos_left _ hz_norm_pos
      linarith
    }
    _ < 2 * z.re := h_two_re
  }
  have h_lt : ‖1 - z‖^2 < 1 := by {
    rw [h_norm_sq]
    linarith
  }
  rwa [sq_lt_one_iff₀ (norm_nonneg _)] at h_lt
}












