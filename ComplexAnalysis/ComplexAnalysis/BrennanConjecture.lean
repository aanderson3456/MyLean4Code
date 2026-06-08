/- formalization copyright Austin Anderson using Gemini 2026 -/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open Complex Set MeasureTheory

/--
  Brennan's Conjecture (Statement):
  Let W be an open, simply connected proper subset of the complex plane ℂ.
  Let f : ℂ → ℂ be a conformal map (holomorphic and injective on W)
  mapping W bijectively onto the open unit disk 𝔻 = Metric.ball 0 1.
  Then for any real p such that 4/3 < p < 4, the p-th power of the derivative
  magnitude |f'(z)|^p is integrable (< ∞) on W with respect to the Lebesgue measure.
-/
def BrennansConjectureStatement : Prop :=
  ∀ (W : Set ℂ) (f : ℂ → ℂ) (p : ℝ),
    IsOpen W →
    W.Nonempty →
    W ≠ univ →
    DifferentiableOn ℂ f W →
    InjOn f W →
    -- `f '' W` represents the image of set W under function f, i.e., {f(z) | z ∈ W}
    f '' W = Metric.ball (0 : ℂ) 1 →
    (4 / 3 < p ∧ p < 4) →
    IntegrableOn (fun z => ‖deriv f z‖ ^ p) W volume

/-- The Koebe slit function: K(z) = z / (1 - z)^2 -/
noncomputable def koebe (z : ℂ) : ℂ := z / (1 - z) ^ 2

/-- The Koebe slit domain W_Koebe = ℂ \ (-∞, -1/4] -/
def KoebeSlitDomain : Set ℂ := {z | z.re > -1/4 ∨ z.im ≠ 0}

/-- Define the principal complex square root -/
noncomputable def csqrt (z : ℂ) : ℂ := Complex.exp (Complex.log z / 2)

--  For any complex number z not on the negative real line, (csqrt z)^2 = z.
theorem csqrt_sq (z : ℂ) (hz : z ∈ slitPlane) : csqrt z ^ 2 = z := by {
  unfold csqrt
  rw [sq]
  rw [← Complex.exp_add]
  have h_add : Complex.log z / 2 + Complex.log z / 2 = Complex.log z := by ring
  rw [h_add]
  have hz_ne : z ≠ 0 := by {
    unfold slitPlane at hz
    intro h
    subst h
    simp at hz
  }
  exact Complex.exp_log hz_ne
}

--  The principal complex square root is differentiable on the slit plane.
theorem differentiableOn_csqrt : DifferentiableOn ℂ csqrt slitPlane := by {
  unfold csqrt
  apply DifferentiableOn.cexp
  apply DifferentiableOn.div_const
  apply DifferentiableOn.clog
  · exact differentiableOn_id
  · intro x hx
    exact hx
}

--  If w is in the Koebe slit domain, then 4w + 1 is in the slit plane.
theorem koebe_domain_mapping (w : ℂ) (hw : w ∈ KoebeSlitDomain) : 4 * w + 1 ∈ slitPlane := by {
  unfold KoebeSlitDomain slitPlane at *
  rcases hw with h1 | h2
  · left
    simp only [add_re, mul_re, one_re] at *
    norm_num at *
    linarith
  · right
    simp only [add_im, mul_im, one_im] at *
    norm_num at *
    exact h2
}

/-- The inverse of the Koebe function, mapping the slit domain back to the unit disk -/
noncomputable def koebeInv (w : ℂ) : ℂ :=
  if w = 0 then 0
  else ((2 * w + 1) - csqrt (4 * w + 1)) / (2 * w)

--  The principal complex square root has a positive real part on the slit plane.
theorem csqrt_re_pos (z : ℂ) (hz : z ∈ slitPlane) : 0 < (csqrt z).re := by {
  unfold csqrt
  rw [exp_re]
  apply mul_pos
  · exact Real.exp_pos _
  · have h_im : (log z / 2).im = z.arg / 2 := by {
      rw [div_im, log_im]
      norm_num
      ring
    }
    rw [h_im]
    apply Real.cos_pos_of_mem_Ioo
    constructor
    · have h_arg := neg_pi_lt_arg z
      linarith
    · have h_arg_ne := slitPlane_arg_ne_pi hz
      have h_arg_le := arg_le_pi z
      have h_arg_lt : z.arg < Real.pi := lt_of_le_of_ne h_arg_le h_arg_ne
      linarith
}

--  For a complex number with positive real part, the square root of its square is itself.
lemma csqrt_sq_eq_self {A : ℂ} (hA : 0 < A.re) : csqrt (A ^ 2) = A := by {
  have hA0 : A ≠ 0 := by {
    intro h
    subst h
    simp at hA
  }
  have h_arg : -(Real.pi / 2) < A.arg ∧ A.arg < Real.pi / 2 := by {
    have h_abs := (abs_arg_lt_pi_div_two_iff.mpr (Or.inl hA))
    exact abs_lt.mp h_abs
  }
  have h_arg_double : A.arg + A.arg ∈ Set.Ioc (-Real.pi) Real.pi := by {
    constructor
    · linarith [h_arg.1]
    · linarith [h_arg.2]
  }
  have h_log_sq : Complex.log (A ^ 2) = 2 * Complex.log A := by {
    rw [sq]
    have h_log_mul := (log_mul_eq_add_log_iff hA0 hA0).mpr h_arg_double
    rw [h_log_mul]
    ring
  }
  unfold csqrt
  rw [h_log_sq]
  have h_div : 2 * Complex.log A / 2 = Complex.log A := by ring
  rw [h_div]
  exact Complex.exp_log hA0
}

--  The real part of (1+z)/(1-z) is positive for z in the unit disk.
lemma re_one_add_div_one_sub_pos {z : ℂ} (hz : ‖z‖ < 1) : 0 < ((1 + z) / (1 - z)).re := by {
  rw [div_re]
  have h_num : (1 + z).re * (1 - z).re + (1 + z).im * (1 - z).im = 1 - ‖z‖ ^ 2 := by {
    simp only [add_re, one_re, sub_re, add_im, one_im, zero_add, sub_im, zero_sub]
    rw [← Complex.normSq_eq_norm_sq]
    rw [Complex.normSq_apply]
    ring
  }
  rw [← add_div, h_num]
  apply div_pos
  · have h_norm_sq : ‖z‖ ^ 2 < 1 := by {
      have hz_nonneg := norm_nonneg z
      nlinarith
    }
    linarith
  · rw [normSq_pos]
    intro h_sub
    have hz1 : z = 1 := (sub_eq_zero.mp h_sub).symm
    have h_norm : ‖z‖ = 1 := by rw [hz1, norm_one]
    linarith
}

--  An algebraic identity matching 4w + 1 to ((1+z)/(1-z))^2 for w = koebe z.
lemma koebe_algebraic_identity {z : ℂ} (hz : ‖z‖ < 1) : 4 * (z / (1 - z) ^ 2) + 1 = ((1 + z) / (1 - z)) ^ 2 := by {
  have h_ne : 1 - z ≠ 0 := by {
    intro h_sub
    have hz1 : z = 1 := (sub_eq_zero.mp h_sub).symm
    have h_norm : ‖z‖ = 1 := by rw [hz1, norm_one]
    linarith
  }
  have h_sq_ne : (1 - z) ^ 2 ≠ 0 := pow_ne_zero 2 h_ne
  rw [div_pow]
  apply (eq_div_iff h_sq_ne).mpr
  calc (4 * (z / (1 - z) ^ 2) + 1) * (1 - z) ^ 2
    _ = (4 * (z / (1 - z) ^ 2)) * (1 - z) ^ 2 + (1 - z) ^ 2 := by ring
    _ = 4 * (z / (1 - z) ^ 2 * (1 - z) ^ 2) + (1 - z) ^ 2 := by ring
    _ = 4 * z + (1 - z) ^ 2 := by {
      rw [div_mul_cancel₀ _ h_sq_ne]
    }
    _ = (1 + z) ^ 2 := by ring
}

--  The inverse Koebe function maps the Koebe slit domain into the open unit disk.
theorem koebeInv_target_mapping (w : ℂ) (hw : w ∈ KoebeSlitDomain) : ‖koebeInv w‖ < 1 := by {
  unfold koebeInv
  split_ifs with h
  · simp
  · let B := csqrt (4 * w + 1)
    have hB_plane := koebe_domain_mapping w hw
    have hB_re : 0 < B.re := csqrt_re_pos (4 * w + 1) hB_plane
    have hB_ne_neg1 : B + 1 ≠ 0 := by {
      intro h_eq
      have h_re : (B + 1).re = 0 := by rw [h_eq, zero_re]
      simp only [add_re, one_re] at h_re
      linarith
    }
    have h_koebeInv_eq : ((2 * w + 1) - B) / (2 * w) = (B - 1) / (B + 1) := by {
      have hB2 : B ^ 2 = 4 * w + 1 := csqrt_sq (4 * w + 1) hB_plane
      have h_2w : 2 * w ≠ 0 := mul_ne_zero (by norm_num) h
      apply (div_eq_div_iff h_2w hB_ne_neg1).mpr
      calc (2 * w + 1 - B) * (B + 1)
        _ = 2 * w * B + 2 * w + 1 - B ^ 2 := by ring
        _ = 2 * w * B + 2 * w + 1 - (4 * w + 1) := by rw [hB2]
        _ = (B - 1) * (2 * w) := by ring
    }
    have h_LHS : ‖B - 1‖ ^ 2 = (B.re - 1) ^ 2 + B.im ^ 2 := by {
      rw [← Complex.normSq_eq_norm_sq]
      rw [Complex.normSq_apply]
      simp
      ring
    }
    have h_RHS : ‖B + 1‖ ^ 2 = (B.re + 1) ^ 2 + B.im ^ 2 := by {
      rw [← Complex.normSq_eq_norm_sq]
      rw [Complex.normSq_apply]
      simp
      ring
    }
    have h_norm_lt : ‖B - 1‖ < ‖B + 1‖ := by {
      have h_norm_sq : ‖B - 1‖ ^ 2 < ‖B + 1‖ ^ 2 := by {
        rw [h_LHS, h_RHS]
        have : (B.re + 1) ^ 2 - (B.re - 1) ^ 2 = 4 * B.re := by ring
        have h_ineq : (B.re - 1) ^ 2 < (B.re + 1) ^ 2 := by linarith
        linarith
      }
      rwa [sq_lt_sq, abs_of_nonneg (norm_nonneg _), abs_of_nonneg (norm_nonneg _)] at h_norm_sq
    }
    have h_norm_div : ‖(B - 1) / (B + 1)‖ = ‖B - 1‖ / ‖B + 1‖ := by rw [norm_div]
    rw [h_koebeInv_eq, h_norm_div]
    have h_norm_pos : 0 < ‖B + 1‖ := by {
      rw [norm_pos_iff]
      exact hB_ne_neg1
    }
    exact (div_lt_one h_norm_pos).mpr h_norm_lt
}

--  The algebraic branch simplification for koebeInv (koebe z) when z ≠ 0.
lemma koebeInv_koebe_nonzero {z : ℂ} (hz : ‖z‖ < 1) (h : koebe z ≠ 0) : koebeInv (koebe z) = z := by {
  let w := koebe z
  have h_ne : 1 - z ≠ 0 := by {
    intro h_sub
    have hz1 : z = 1 := (sub_eq_zero.mp h_sub).symm
    have h_norm : ‖z‖ = 1 := by rw [hz1, norm_one]
    linarith
  }
  have h_sq_ne : (1 - z) ^ 2 ≠ 0 := pow_ne_zero 2 h_ne
  have h_alg := koebe_algebraic_identity hz
  have h_csqrt : csqrt (4 * w + 1) = (1 + z) / (1 - z) := by {
    change csqrt (4 * (z / (1 - z) ^ 2) + 1) = (1 + z) / (1 - z)
    rw [h_alg]
    exact csqrt_sq_eq_self (re_one_add_div_one_sub_pos hz)
  }
  have h_w_eq : 2 * w * (1 - z) = 2 * z / (1 - z) := by {
    unfold w koebe
    calc 2 * (z / (1 - z) ^ 2) * (1 - z)
      _ = 2 * z / (1 - z) ^ 2 * (1 - z) := by ring
      _ = 2 * z * (1 - z) / (1 - z) ^ 2 := by ring
      _ = 2 * z * (1 - z) / ((1 - z) * (1 - z)) := by rw [sq]
      _ = 2 * z / (1 - z) := by {
        rw [mul_div_mul_right _ _ h_ne]
      }
  }
  have h_alg2 : (2 * w + 1) - (1 + z) / (1 - z) = z * (2 * w) := by {
    have h_zero : 2 * w * (1 - z) + 1 - (1 + z) / (1 - z) = 0 := by {
      rw [h_w_eq]
      calc 2 * z / (1 - z) + 1 - (1 + z) / (1 - z)
        _ = 2 * z / (1 - z) + (1 - (1 + z) / (1 - z)) := by ring
        _ = 2 * z / (1 - z) + ((1 - z) - (1 + z)) / (1 - z) := by {
          have : 1 - (1 + z) / (1 - z) = ((1 - z) - (1 + z)) / (1 - z) := by {
            rw [sub_div, div_self h_ne]
          }
          rw [this]
        }
        _ = (2 * z + ((1 - z) - (1 + z))) / (1 - z) := by rw [← add_div]
        _ = 0 := by {
          have : 2 * z + ((1 - z) - (1 + z)) = 0 := by ring
          rw [this, zero_div]
        }
    }
    calc (2 * w + 1) - (1 + z) / (1 - z)
      _ = 2 * w * (1 - z) + 1 - (1 + z) / (1 - z) + 2 * w * z := by ring
      _ = 0 + 2 * w * z := by rw [h_zero]
      _ = z * (2 * w) := by ring
  }
  have h_2w_ne : 2 * w ≠ 0 := by {
    exact mul_ne_zero (by norm_num) h
  }
  unfold koebeInv
  split_ifs with hw
  · contradiction
  · rw [h_csqrt]
    exact (div_eq_iff h_2w_ne).mpr h_alg2
}

--  The inverse Koebe function is a left inverse of the Koebe function on the unit disk.
theorem koebeInv_koebe (z : ℂ) (hz : ‖z‖ < 1) : koebeInv (koebe z) = z := by {
  by_cases h : koebe z = 0
  · unfold koebeInv
    rw [if_pos h]
    have hz0 : z = 0 := by {
      have h_div : z / (1 - z) ^ 2 = 0 := h
      have h_or := div_eq_zero_iff.mp h_div
      rcases h_or with hz0 | h_den
      · exact hz0
      · have : 1 - z = 0 := sq_eq_zero_iff.mp h_den
        have hz1 : z = 1 := (sub_eq_zero.mp this).symm
        have h_norm : ‖z‖ = 1 := by rw [hz1, norm_one]
        linarith
    }
    subst hz0
    simp
  · exact koebeInv_koebe_nonzero hz h
}

theorem koebe_koebeInv (w : ℂ) (hw : w ∈ KoebeSlitDomain) : koebe (koebeInv w) = w := by {
  unfold koebe koebeInv
  split_ifs with h
  · -- w = 0
    subst h
    simp
  · -- w ≠ 0
    let z := ((2 * w + 1) - csqrt (4 * w + 1)) / (2 * w)
    have hz1 : z ≠ 1 := by {
      intro hz_eq
      have hz_eq' : ((2 * w + 1) - csqrt (4 * w + 1)) = 2 * w := by {
        have h_div : ((2 * w + 1) - csqrt (4 * w + 1)) / (2 * w) = 1 := hz_eq
        have h_mul := div_eq_iff (by exact mul_ne_zero (by norm_num) h) |>.mp h_div
        rw [one_mul] at h_mul
        exact h_mul
      }
      have h1 : 1 = csqrt (4 * w + 1) := by {
        calc 1 = (2 * w + 1 - csqrt (4 * w + 1)) - 2 * w + csqrt (4 * w + 1) := by ring
        _ = 2 * w - 2 * w + csqrt (4 * w + 1) := by rw [hz_eq']
        _ = csqrt (4 * w + 1) := by ring
      }
      have h2 : (1 : ℂ) ^ 2 = csqrt (4 * w + 1) ^ 2 := congrArg (fun x => x ^ 2) h1
      have h_plane := koebe_domain_mapping w hw
      rw [csqrt_sq (4 * w + 1) h_plane] at h2
      simp only [one_pow] at h2
      have h_zero : w = 0 := by {
        calc w = (4 * w + 1 - 1) / 4 := by ring
        _ = (1 - 1) / 4 := by rw [← h2]
        _ = 0 := by ring
      }
      exact h h_zero
    }
    have hB2 : csqrt (4 * w + 1) ^ 2 = 4 * w + 1 := by {
      have h_plane := koebe_domain_mapping w hw
      exact csqrt_sq (4 * w + 1) h_plane
    }
    have h_eq2 : 2 * w * z = 2 * w + 1 - csqrt (4 * w + 1) := by {
      unfold z
      rw [mul_comm]
      exact div_mul_cancel₀ (2 * w + 1 - csqrt (4 * w + 1)) (mul_ne_zero (by norm_num) h)
    }
    have h_eq3 : 2 * w * (1 - z) = csqrt (4 * w + 1) - 1 := by {
      calc 2 * w * (1 - z) = 2 * w - 2 * w * z := by ring
      _ = 2 * w - (2 * w + 1 - csqrt (4 * w + 1)) := by rw [h_eq2]
      _ = csqrt (4 * w + 1) - 1 := by ring
    }
    have h_sq : (2 * w * (1 - z)) ^ 2 = (csqrt (4 * w + 1) - 1) ^ 2 := by rw [h_eq3]
    have h_sq2 : 4 * w ^ 2 * (1 - z) ^ 2 = 4 * w + 2 - 2 * csqrt (4 * w + 1) := by {
      calc 4 * w ^ 2 * (1 - z) ^ 2 = (2 * w * (1 - z)) ^ 2 := by ring
      _ = (csqrt (4 * w + 1) - 1) ^ 2 := h_sq
      _ = csqrt (4 * w + 1) ^ 2 - 2 * csqrt (4 * w + 1) + 1 := by ring
      _ = (4 * w + 1) - 2 * csqrt (4 * w + 1) + 1 := by rw [hB2]
      _ = 4 * w + 2 - 2 * csqrt (4 * w + 1) := by ring
    }
    have h_final : 4 * w ^ 2 * (1 - z) ^ 2 = 4 * w * z := by {
      rw [h_sq2]
      calc 4 * w + 2 - 2 * csqrt (4 * w + 1) = 2 * (2 * w * z) := by {
        rw [h_eq2]
        ring
      }
      _ = 4 * w * z := by ring
    }
    have h_cancel : w * (1 - z) ^ 2 = z := by {
      have h_mul : 4 * w * (w * (1 - z) ^ 2) = 4 * w * z := by {
        calc 4 * w * (w * (1 - z) ^ 2) = 4 * w ^ 2 * (1 - z) ^ 2 := by ring
        _ = 4 * w * z := h_final
      }
      exact mul_left_cancel₀ (mul_ne_zero (by norm_num) h) h_mul
    }
    have h_div_eq : z / (1 - z) ^ 2 = w := by {
      apply (div_eq_iff ?_).mpr
      · exact h_cancel.symm
      · intro hz_zero
        have hz_one : z = 1 := by {
          have h_sub : 1 - z = 0 := sq_eq_zero_iff.mp hz_zero
          calc z = 1 - (1 - z) := by ring
          _ = 1 - 0 := by rw [h_sub]
          _ = 1 := by ring
        }
        exact hz1 hz_one
    }
    exact h_div_eq
}

--  The inverse Koebe function can be written in a simplified form without piecewise definition.
lemma koebeInv_eq_simplified (w : ℂ) (hw : w ∈ KoebeSlitDomain) :
    koebeInv w = (csqrt (4 * w + 1) - 1) / (csqrt (4 * w + 1) + 1) := by {
  unfold koebeInv
  split_ifs with h
  · subst h
    have h1 : csqrt (4 * 0 + 1) = 1 := by {
      simp only [mul_zero, zero_add]
      unfold csqrt
      rw [Complex.log_one, zero_div, Complex.exp_zero]
    }
    rw [h1]
    simp
  · let B := csqrt (4 * w + 1)
    have hB_plane := koebe_domain_mapping w hw
    have hB_ne_neg1 : B + 1 ≠ 0 := by {
      intro h_eq
      have h_re : (B + 1).re = 0 := by rw [h_eq, zero_re]
      simp only [add_re, one_re] at h_re
      have hB_re := csqrt_re_pos (4 * w + 1) hB_plane
      linarith
    }
    have hB2 : B ^ 2 = 4 * w + 1 := csqrt_sq (4 * w + 1) hB_plane
    have h_2w : 2 * w ≠ 0 := mul_ne_zero (by norm_num) h
    apply (div_eq_div_iff h_2w hB_ne_neg1).mpr
    calc (2 * w + 1 - B) * (B + 1)
      _ = 2 * w * B + 2 * w + 1 - B ^ 2 := by ring
      _ = 2 * w * B + 2 * w + 1 - (4 * w + 1) := by rw [hB2]
      _ = (B - 1) * (2 * w) := by ring
}

theorem differentiableOn_koebeInv : DifferentiableOn ℂ koebeInv KoebeSlitDomain := by {
  have h_eq : EqOn koebeInv (fun w => (csqrt (4 * w + 1) - 1) / (csqrt (4 * w + 1) + 1)) KoebeSlitDomain := by {
    intro w hw
    exact koebeInv_eq_simplified w hw
  }
  apply DifferentiableOn.congr (f := fun w => (csqrt (4 * w + 1) - 1) / (csqrt (4 * w + 1) + 1)) _ h_eq
  have h_diff : DifferentiableOn ℂ (fun w => 4 * w + 1) KoebeSlitDomain := by {
    apply DifferentiableOn.add_const
    apply DifferentiableOn.const_mul
    exact differentiableOn_id
  }
  have h_map : MapsTo (fun w => 4 * w + 1) KoebeSlitDomain slitPlane := by {
    intro w hw
    exact koebe_domain_mapping w hw
  }
  have h_diff_csqrt : DifferentiableOn ℂ (csqrt ∘ (fun w => 4 * w + 1)) KoebeSlitDomain := by {
    exact DifferentiableOn.comp differentiableOn_csqrt h_diff h_map
  }
  apply DifferentiableOn.div
  · apply DifferentiableOn.sub_const
    exact h_diff_csqrt
  · apply DifferentiableOn.add_const
    exact h_diff_csqrt
  · intro w hw
    let B := csqrt (4 * w + 1)
    have hB_plane := koebe_domain_mapping w hw
    have hB_re := csqrt_re_pos (4 * w + 1) hB_plane
    intro h_eq2
    have h_re : (B + 1).re = 0 := by rw [h_eq2, zero_re]
    simp only [add_re, one_re] at h_re
    linarith
}

--  The derivative of the inverse Koebe function is given by (1 - K^-1(w))^3 / (1 + K^-1(w)).
theorem deriv_koebeInv (w : ℂ) (hw : w ∈ KoebeSlitDomain) :
    deriv koebeInv w = (1 - koebeInv w) ^ 3 / (1 + koebeInv w) := by {
  sorry
}

--  Integrability of the inverse derivative over the slit domain is equivalent to integrability of the Koebe derivative over the unit disk.
theorem IntegrableOn_koebeInv_iff (p : ℝ) :
    IntegrableOn (fun z => ‖deriv koebeInv z‖ ^ p) KoebeSlitDomain volume ↔
    IntegrableOn (fun w => ‖deriv koebe w‖ ^ (2 - p)) (Metric.ball 0 1) volume := by {
  sorry
}

--  The integral of |K'(w)|^(2-p) over the unit disk diverges for p >= 4 due to the cusp singularity at w = -1.
theorem cusp_divergence (p : ℝ) (hp : p ≥ 4) :
    ¬ IntegrableOn (fun w => ‖deriv koebe w‖ ^ (2 - p)) (Metric.ball 0 1) volume := by {
  sorry
}

--  The integral of |K'(w)|^(2-p) over the unit disk diverges for p <= 4/3 due to the pole singularity at w = 1.
theorem pole_divergence (p : ℝ) (hp : p ≤ 4 / 3) :
    ¬ IntegrableOn (fun w => ‖deriv koebe w‖ ^ (2 - p)) (Metric.ball 0 1) volume := by {
  sorry
}

/--
  The Koebe slit function is conformal from the unit disk to the slit domain,
  and its inverse shows that the bounds 4/3 < p < 4 in Brennan's Conjecture are sharp.
  Specifically, if p ≥ 4 or p ≤ 4/3, the integral of |f'(z)|^p over the slit domain diverges.
-/
--  The sharpness limit of Brennan's Conjecture: the integral of |(K^-1)'(z)|^p diverges if p >= 4 or p <= 4/3.
theorem KoebeSharpnessLimit (p : ℝ) (h : p ≥ 4 ∨ p ≤ 4/3) :
    ¬ IntegrableOn (fun z => ‖deriv koebeInv z‖ ^ p) KoebeSlitDomain volume := by {
  rw [IntegrableOn_koebeInv_iff]
  rcases h with hp | hp
  · exact cusp_divergence p hp
  · exact pole_divergence p hp
}
