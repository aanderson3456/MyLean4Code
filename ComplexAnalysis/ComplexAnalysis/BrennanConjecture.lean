/-
  This formalization of complex analysis and Brennan's Conjecture is spearheaded by Austin Anderson,
  aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv
import ComplexAnalysis.Sarason.Definitions
import Mathlib.RingTheory.Complex
import Mathlib.MeasureTheory.Function.Jacobian
import Mathlib.Analysis.SpecialFunctions.PolarCoord
import Mathlib.MeasureTheory.Group.Measure
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic


open Complex Set MeasureTheory Sarason Filter ENNReal
open scoped Topology ENNReal


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
  apply _root_.mul_pos

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

--  The Koebe function is the right-inverse of the inverse Koebe function on the slit domain.
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

--  The inverse Koebe function is differentiable on the Koebe slit domain.
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

--  The derivative of the principal complex square root on the slit plane.
lemma hasDerivAt_csqrt {z : ℂ} (hz : z ∈ slitPlane) : HasDerivAt csqrt (csqrt z / (2 * z)) z := by {
  unfold csqrt
  have h1 : HasDerivAt (fun x => log x / 2) (z⁻¹ / 2) z := by {
    apply HasDerivAt.div_const
    exact hasDerivAt_log hz
  }
  have h2 := HasDerivAt.cexp h1
  have h_eq : exp (log z / 2) * (z⁻¹ / 2) = csqrt z / (2 * z) := by {
    unfold csqrt
    have hz0 : z ≠ 0 := slitPlane_ne_zero hz
    field_simp [hz0]
  }
  rw [h_eq] at h2
  exact h2
}

--  Algebraic simplification of the derivative formula for the Koebe inverse.
lemma deriv_koebeInv_algebraic (B : ℂ) (hB : B + 1 ≠ 0) (hB_ne_zero : B ≠ 0) :
    4 / (B * (B + 1) ^ 2) = (1 - (B - 1) / (B + 1)) ^ 3 / (1 + (B - 1) / (B + 1)) := by {
  have h1 : 1 - (B - 1) / (B + 1) = 2 / (B + 1) := by {
    have : 1 - (B - 1) / (B + 1) = (B + 1) / (B + 1) - (B - 1) / (B + 1) := by {
      rw [div_self hB]
    }
    rw [this, ← sub_div]
    ring_nf
  }
  have h2 : 1 + (B - 1) / (B + 1) = 2 * B / (B + 1) := by {
    have : 1 + (B - 1) / (B + 1) = (B + 1) / (B + 1) + (B - 1) / (B + 1) := by {
      rw [div_self hB]
    }
    rw [this, ← add_div]
    ring_nf
  }
  rw [h1, h2]
  have h_num : (2 / (B + 1)) ^ 3 = 8 / (B + 1) ^ 3 := by {
    rw [div_pow]
    norm_num
  }
  rw [h_num]
  have hB_pow : (B + 1) ^ 3 = (B + 1) ^ 2 * (B + 1) := by ring
  rw [hB_pow]
  have h_div : 4 / (B * (B + 1) ^ 2) = (8 / ((B + 1) ^ 2 * (B + 1))) / (2 * B / (B + 1)) := by {
    field_simp [hB, hB_ne_zero]
    ring
  }
  exact h_div
}

--  The Koebe slit domain is an open subset of ℂ.
theorem isOpen_koebeSlitDomain : IsOpen KoebeSlitDomain := by {
  have h1 : IsOpen {z : ℂ | z.re > -1/4} := by {
    have h_pre : {z : ℂ | z.re > -1/4} = Complex.re ⁻¹' (Ioi (-1/4)) := rfl
    rw [h_pre]
    exact continuous_re.isOpen_preimage _ isOpen_Ioi
  }
  have h2 : IsOpen {z : ℂ | z.im ≠ 0} := by {
    have h_pre : {z : ℂ | z.im ≠ 0} = Complex.im ⁻¹' {0}ᶜ := rfl
    rw [h_pre]
    exact continuous_im.isOpen_preimage _ isOpen_compl_singleton
  }
  exact IsOpen.union h1 h2
}

--  The derivative of the inverse Koebe function is given by (1 - K^-1(w))^3 / (1 + K^-1(w)).
theorem deriv_koebeInv (w : ℂ) (hw : w ∈ KoebeSlitDomain) :
    deriv koebeInv w = (1 - koebeInv w) ^ 3 / (1 + koebeInv w) := by {
  let B := csqrt (4 * w + 1)
  have hB_plane := koebe_domain_mapping w hw
  have hB_ne_neg1 : B + 1 ≠ 0 := by {
    intro h_eq
    have h_re : (B + 1).re = 0 := by rw [h_eq, zero_re]
    simp only [add_re, one_re] at h_re
    have hB_re := csqrt_re_pos (4 * w + 1) hB_plane
    linarith
  }
  have hB_ne_zero : B ≠ 0 := by {
    intro h_eq
    have h_re : B.re = 0 := by rw [h_eq, zero_re]
    have hB_re := csqrt_re_pos (4 * w + 1) hB_plane
    linarith
  }
  have h_eq_nhds : koebeInv =ᶠ[nhds w] (fun u => (csqrt (4 * u + 1) - 1) / (csqrt (4 * u + 1) + 1)) := by {
    apply Filter.eventually_of_mem (IsOpen.mem_nhds isOpen_koebeSlitDomain hw)
    intro u hu
    exact koebeInv_eq_simplified u hu
  }
  have h_deriv_eq : deriv koebeInv w = deriv (fun u => (csqrt (4 * u + 1) - 1) / (csqrt (4 * u + 1) + 1)) w :=
    h_eq_nhds.deriv_eq
  have h_deriv_calc : HasDerivAt (fun u => (csqrt (4 * u + 1) - 1) / (csqrt (4 * u + 1) + 1)) (4 / (B * (B + 1) ^ 2)) w := by {
    have h_deriv_lin : HasDerivAt (fun u => 4 * u + 1) 4 w := by {
      have h_id := hasDerivAt_id' w
      have h_mul := HasDerivAt.const_mul 4 h_id
      have h_add := HasDerivAt.add_const 1 h_mul
      simpa using h_add
    }
    have h_comp := HasDerivAt.comp w (hasDerivAt_csqrt hB_plane) h_deriv_lin
    have h_csqrt_val : csqrt (4 * w + 1) = B := rfl
    have h_B_sq : 4 * w + 1 = B ^ 2 := (csqrt_sq (4 * w + 1) hB_plane).symm
    have h_deriv_csqrt_comp : HasDerivAt (fun u => csqrt (4 * u + 1)) (2 / B) w := by {
      have h_calc : (csqrt (4 * w + 1) / (2 * (4 * w + 1))) * 4 = 2 / B := by {
        rw [h_csqrt_val, h_B_sq]
        field_simp [hB_ne_zero]
        ring
      }
      rw [h_calc] at h_comp
      exact h_comp
    }
    have h_deriv_g : HasDerivAt (fun u => csqrt (4 * u + 1) - 1) (2 / B) w := by {
      have h_sub := HasDerivAt.sub_const 1 h_deriv_csqrt_comp
      simpa using h_sub
    }
    have h_deriv_h : HasDerivAt (fun u => csqrt (4 * u + 1) + 1) (2 / B) w := by {
      have h_add := HasDerivAt.add_const 1 h_deriv_csqrt_comp
      simpa using h_add
    }
    have h_deriv_div := HasDerivAt.div h_deriv_g h_deriv_h hB_ne_neg1
    have h_calc2 : ((2 / B) * (csqrt (4 * w + 1) + 1) - (csqrt (4 * w + 1) - 1) * (2 / B)) / (csqrt (4 * w + 1) + 1) ^ 2 = 4 / (B * (B + 1) ^ 2) := by {
      rw [h_csqrt_val]
      field_simp [hB_ne_zero, hB_ne_neg1]
      ring
    }
    rw [h_calc2] at h_deriv_div
    exact h_deriv_div
  }
  have h_deriv_val : deriv (fun u => (csqrt (4 * u + 1) - 1) / (csqrt (4 * u + 1) + 1)) w = 4 / (B * (B + 1) ^ 2) :=
    h_deriv_calc.deriv
  have h_koebeInv_val : koebeInv w = (B - 1) / (B + 1) := koebeInv_eq_simplified w hw
  rw [h_deriv_eq, h_deriv_val, h_koebeInv_val]
  exact deriv_koebeInv_algebraic B hB_ne_neg1 hB_ne_zero
}

--  The derivative of the inverse Koebe function under the classical epsilon-delta definition.
theorem HasDerivAt_koebeInv_eps (w : ℂ) (hw : w ∈ KoebeSlitDomain) :
    HasDerivAt_eps koebeInv ((1 - koebeInv w) ^ 3 / (1 + koebeInv w)) w := by {
  rw [← hasDerivAt_iff_eps]
  have h_diff : _root_.DifferentiableAt ℂ koebeInv w :=
    differentiableOn_koebeInv.differentiableAt (IsOpen.mem_nhds isOpen_koebeSlitDomain hw)
  have h_deriv := h_diff.hasDerivAt
  rw [deriv_koebeInv w hw] at h_deriv
  exact h_deriv
}

--  Differentiability of the inverse Koebe function under the classical epsilon-delta definition.
theorem DifferentiableAt_koebeInv_eps (w : ℂ) (hw : w ∈ KoebeSlitDomain) :
    DifferentiableAt_eps koebeInv w := by {
  use (1 - koebeInv w) ^ 3 / (1 + koebeInv w)
  exact HasDerivAt_koebeInv_eps w hw
}

--  Squaring a complex number in the right half-plane yields a number in the slit plane.
lemma sq_mem_slitPlane_of_re_pos {A : ℂ} (hA : 0 < A.re) : A ^ 2 ∈ slitPlane := by {
  unfold slitPlane
  by_cases h : (A ^ 2).im = 0
  · left
    have h_im : 2 * A.re * A.im = 0 := by {
      have h1 : (A ^ 2).im = 2 * A.re * A.im := by {
        simp [sq, mul_im]
        ring
      }
      rw [h1] at h
      exact h
    }
    have hA_im : A.im = 0 := by {
      cases mul_eq_zero.mp h_im with
      | inl h_mul =>
        cases mul_eq_zero.mp h_mul with
        | inl h2 => norm_num at h2
        | inr h_re => linarith
      | inr h_im' => exact h_im'
    }
    have h_re : (A ^ 2).re = A.re ^ 2 := by {
      simp [sq, mul_re, hA_im]
    }
    rw [h_re]
    exact sq_pos_of_ne_zero (ne_of_gt hA)
  · right
    exact h
}

--  The Koebe function maps the unit disk into the Koebe slit domain.
lemma koebe_mapping {z : ℂ} (hz : ‖z‖ < 1) : koebe z ∈ KoebeSlitDomain := by {
  unfold koebe
  have h_alg := koebe_algebraic_identity hz
  have hA : 0 < ((1 + z) / (1 - z)).re := re_one_add_div_one_sub_pos hz
  have h_slit := sq_mem_slitPlane_of_re_pos hA
  rw [← h_alg] at h_slit
  unfold KoebeSlitDomain
  unfold slitPlane at h_slit
  rcases h_slit with h1 | h2
  · left
    have h_re : (4 * (z / (1 - z) ^ 2)).re = 4 * (z / (1 - z) ^ 2).re := by {
      have : (4 : ℂ).im = 0 := by rfl
      rw [mul_re]
      simp [this]
    }
    simp only [add_re, one_re] at h1
    rw [h_re] at h1
    linarith
  · right
    have h_im : (4 * (z / (1 - z) ^ 2) + 1).im = 4 * (z / (1 - z) ^ 2).im := by {
      simp
    }
    rw [h_im] at h2
    intro h_zero
    rw [h_zero, mul_zero] at h2
    exact h2 rfl
}

--  The image of the unit disk under the Koebe function is exactly the Koebe slit domain.
lemma koebe_image_eq : koebe '' (Metric.ball 0 1) = KoebeSlitDomain := by {
  ext w
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Metric.mem_ball, dist_zero_right] at hz
    exact koebe_mapping hz
  · intro hw
    use koebeInv w
    constructor
    · rw [Metric.mem_ball, dist_zero_right]
      exact koebeInv_target_mapping w hw
    · exact koebe_koebeInv w hw
}

--  The Koebe function is complex-differentiable on the open unit disk.
lemma differentiableOn_koebe : DifferentiableOn ℂ koebe (Metric.ball 0 1) := by {
  unfold koebe
  apply DifferentiableOn.div
  · exact differentiableOn_id
  · apply DifferentiableOn.pow
    apply DifferentiableOn.const_sub
    exact differentiableOn_id
  · intro z hz
    rw [Metric.mem_ball, dist_zero_right] at hz
    intro h
    have h1 : 1 - z = 0 := sq_eq_zero_iff.mp h
    have h2 : 1 = z := sub_eq_zero.mp h1
    have : z = 1 := h2.symm
    have : ‖z‖ = 1 := by {
      rw [this]
      simp
    }
    linarith
}

--  The complex derivative of the Koebe function.
lemma hasDerivAt_koebe (w : ℂ) (hw : ‖w‖ < 1) :
    HasDerivAt koebe ((1 + w) / (1 - w) ^ 3) w := by {
  have h_ne : 1 - w ≠ 0 := by {
    intro h_sub
    have hz1 : w = 1 := (sub_eq_zero.mp h_sub).symm
    have h_norm : ‖w‖ = 1 := by rw [hz1, norm_one]
    linarith
  }
  have h_sq_ne : (1 - w) ^ 2 ≠ 0 := pow_ne_zero 2 h_ne
  unfold koebe
  have h_id := hasDerivAt_id' w
  have h1 : HasDerivAt (fun w => 1 - w) (-1) w := by {
    exact HasDerivAt.const_sub (1 : ℂ) h_id
  }
  have h2 : HasDerivAt (fun w => (1 - w)^2) (-2 * (1 - w)) w := by {
    have h_pow := HasDerivAt.pow h1 2
    change HasDerivAt (fun w => (1 - w)^2) (2 * (1 - w) ^ (2 - 1) * -1) w at h_pow
    convert h_pow using 1
    have : 2 - 1 = 1 := by norm_num
    rw [this, pow_one]
    ring
  }
  have h_div := HasDerivAt.div h_id h2 h_sq_ne
  have h_calc2 : ((1 : ℂ) * (1 - w) ^ 2 - w * (-2 * (1 - w))) / ((1 - w) ^ 2) ^ 2 = (1 + w) / (1 - w) ^ 3 := by {
    have h_num : (1 : ℂ) * (1 - w) ^ 2 - w * (-2 * (1 - w)) = (1 - w) * (1 + w) := by ring
    have h_den : ((1 - w) ^ 2) ^ 2 = (1 - w) * (1 - w) ^ 3 := by ring
    rw [h_num, h_den]
    rw [mul_div_mul_left _ _ h_ne]
  }
  rw [h_calc2] at h_div
  exact h_div
}

lemma deriv_koebe (w : ℂ) (hw : ‖w‖ < 1) :
    deriv koebe w = (1 + w) / (1 - w) ^ 3 := by {
  exact (hasDerivAt_koebe w hw).deriv
}

--  The Koebe function has a real Fréchet derivative at every point of the unit disk.
lemma koebe_hasFDerivWithinAt (w : ℂ) (hw : w ∈ Metric.ball 0 1) :
    HasFDerivWithinAt koebe ((deriv koebe w) • (1 : ℂ →L[ℝ] ℂ)) (Metric.ball 0 1) w := by {
  have h_diff := differentiableOn_koebe.differentiableAt (IsOpen.mem_nhds (Metric.isOpen_ball) hw)
  have h_deriv := h_diff.hasDerivAt
  have h_fderiv := h_deriv.complexToReal_fderiv
  exact h_fderiv.hasFDerivWithinAt
}

--  For any complex number A, the determinant of multiplication by A as a real linear map is ‖A‖^2.
lemma complex_det_fderiv_eq_norm_sq (A : ℂ) :
    |(A • (1 : ℂ →L[ℝ] ℂ)).det| = ‖A‖ ^ 2 := by {
  change |LinearMap.det (A • (1 : ℂ →ₗ[ℝ] ℂ))| = ‖A‖ ^ 2
  have h_lmul : (A • (1 : ℂ →ₗ[ℝ] ℂ)) = Algebra.lmul ℝ ℂ A := by {
    ext x
    simp
  }
  rw [h_lmul]
  change |Algebra.norm ℝ A| = ‖A‖ ^ 2
  rw [Algebra.norm_complex_apply]
  have h_pos : 0 ≤ Complex.normSq A := Complex.normSq_nonneg A
  rw [abs_of_nonneg h_pos]
  rw [Complex.normSq_eq_norm_sq]
}

--  The real Fréchet derivative of the Koebe function at a point w in the unit disk is equal to multiplication by its complex derivative.
lemma fderiv_koebe_eq (w : ℂ) (hw : w ∈ Metric.ball 0 1) :
    fderiv ℝ koebe w = (deriv koebe w) • (1 : ℂ →L[ℝ] ℂ) := by {
  have h_diff := differentiableOn_koebe.differentiableAt (IsOpen.mem_nhds (Metric.isOpen_ball) hw)
  have h_deriv := h_diff.hasDerivAt
  have h_fderiv := h_deriv.complexToReal_fderiv
  exact h_fderiv.fderiv
}

--  The product of the derivatives of the Koebe function and its inverse at corresponding points is 1.
lemma deriv_koebeInv_mul_deriv_koebe_eq_one (w : ℂ) (hw : w ∈ Metric.ball 0 1) :
    deriv koebeInv (koebe w) * deriv koebe w = 1 := by {
  have h_w_ball : ‖w‖ < 1 := by rwa [Metric.mem_ball, dist_zero_right] at hw
  have h_diff_k := differentiableOn_koebe.differentiableAt (IsOpen.mem_nhds Metric.isOpen_ball hw)
  have h_kw := koebe_mapping h_w_ball
  have h_diff_ki := differentiableOn_koebeInv.differentiableAt (IsOpen.mem_nhds isOpen_koebeSlitDomain h_kw)
  have h_comp := deriv_comp w h_diff_ki h_diff_k
  have h_eq : (koebeInv ∘ koebe) =ᶠ[𝓝 w] id := by {
    have h_nhds : Metric.ball 0 1 ∈ 𝓝 w := IsOpen.mem_nhds Metric.isOpen_ball hw
    apply eventually_of_mem h_nhds
    intro z hz
    simp only [Function.comp_apply, id_eq]
    have hz_norm : ‖z‖ < 1 := by {
      have h_mem : dist z 0 < 1 := hz
      rwa [dist_zero_right] at h_mem
    }
    exact koebeInv_koebe z hz_norm
  }
  have h_deriv_comp : deriv (koebeInv ∘ koebe) w = deriv id w := h_eq.deriv_eq
  rw [h_deriv_comp] at h_comp
  rw [deriv_id] at h_comp
  exact h_comp.symm
}

--  The pullback integrand is simplified under the change of variables.
lemma integrand_pullback_eq (p : ℝ) (w : ℂ) (hw : w ∈ Metric.ball 0 1) :
    |(fderiv ℝ koebe w).det| * ‖deriv koebeInv (koebe w)‖ ^ p = ‖deriv koebe w‖ ^ (2 - p) := by {
  have h_fderiv := fderiv_koebe_eq w hw
  have h_det : |(fderiv ℝ koebe w).det| = ‖deriv koebe w‖ ^ 2 := by {
    rw [h_fderiv]
    exact complex_det_fderiv_eq_norm_sq (deriv koebe w)
  }
  rw [h_det]
  have h_mul := deriv_koebeInv_mul_deriv_koebe_eq_one w hw
  have h_norm_mul : ‖deriv koebeInv (koebe w)‖ * ‖deriv koebe w‖ = 1 := by {
    have : ‖deriv koebeInv (koebe w) * deriv koebe w‖ = 1 := by {
      rw [h_mul]
      simp
    }
    rwa [norm_mul] at this
  }
  have h_norm_ne_zero : ‖deriv koebe w‖ ≠ 0 := by {
    intro h_zero
    rw [h_zero, mul_zero] at h_norm_mul
    norm_num at h_norm_mul
  }
  have h_norm_pos : 0 < ‖deriv koebe w‖ := norm_pos_iff.mpr (by {
    intro h_zero'
    exact h_norm_ne_zero (by rw [h_zero', norm_zero])
  })
  have h_inv : ‖deriv koebeInv (koebe w)‖ = 1 / ‖deriv koebe w‖ := by {
    rw [eq_div_iff h_norm_ne_zero]
    exact h_norm_mul
  }
  rw [h_inv]
  have h_rpow : (1 / ‖deriv koebe w‖) ^ p = ‖deriv koebe w‖ ^ (-p) := by {
    rw [one_div]
    rw [← Real.rpow_neg_eq_inv_rpow]
  }
  rw [h_rpow]
  rw [← Real.rpow_two]
  rw [← Real.rpow_add h_norm_pos]
  have : (2 : ℝ) + -p = 2 - p := by ring
  rw [this]
}

--  Integrability of the inverse derivative over the slit domain is equivalent to integrability of the Koebe derivative over the unit disk.
theorem IntegrableOn_koebeInv_iff (p : ℝ) :
    IntegrableOn (fun z => ‖deriv koebeInv z‖ ^ p) KoebeSlitDomain volume ↔
    IntegrableOn (fun w => ‖deriv koebe w‖ ^ (2 - p)) (Metric.ball 0 1) volume := by {
  have h_inj : InjOn koebe (Metric.ball 0 1) := by {
    intro z1 hz1 z2 hz2 h_eq
    rw [Metric.mem_ball, dist_zero_right] at hz1 hz2
    have h1 := koebeInv_koebe z1 hz1
    have h2 := koebeInv_koebe z2 hz2
    rw [h_eq] at h1
    exact h1.symm.trans h2
  }
  have hf' : ∀ w ∈ Metric.ball 0 1, HasFDerivWithinAt koebe (fderiv ℝ koebe w) (Metric.ball 0 1) w := by {
    intro w hw
    rw [fderiv_koebe_eq w hw]
    exact koebe_hasFDerivWithinAt w hw
  }
  have h_meas : MeasurableSet (Metric.ball (0 : ℂ) 1) := Metric.isOpen_ball.measurableSet
  have h_change := integrableOn_image_iff_integrableOn_abs_det_fderiv_smul volume h_meas hf' h_inj (fun z => ‖deriv koebeInv z‖ ^ p)
  rw [koebe_image_eq] at h_change
  rw [h_change]
  apply integrableOn_congr_fun _ h_meas
  intro w hw
  simp only
  rw [smul_eq_mul]
  exact integrand_pullback_eq p w hw
}

lemma measurePreserving_sub_one : MeasurePreserving (fun z : ℂ ↦ 1 - z) volume volume := by {
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

lemma lintegral_polar_indicator (f : ℂ → ℝ≥0∞) (s : Set ℂ) (hs : MeasurableSet s) :

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
def R : Set (ℝ × ℝ) := Ioo (0 : ℝ) (1/2) ×ˢ Ioo (-(Real.pi/4)) (Real.pi/4)

def S0 : Set ℂ := { z | 0 < ‖z‖ ∧ ‖z‖ < 1/2 ∧ z.arg ∈ Ioo (-(Real.pi/4)) (Real.pi/4) }

lemma S0_measurable : MeasurableSet S0 := by {
  have h1 : MeasurableSet {z : ℂ | 0 < ‖z‖} := by {
    have : {z : ℂ | 0 < ‖z‖} = norm ⁻¹' (Ioi 0) := rfl
    rw [this]
    exact measurableSet_preimage continuous_norm.measurable isOpen_Ioi.measurableSet
  }
  have h2 : MeasurableSet {z : ℂ | ‖z‖ < 1/2} := by {
    have : {z : ℂ | ‖z‖ < 1/2} = norm ⁻¹' (Iio (1/2)) := rfl
    rw [this]
    exact measurableSet_preimage continuous_norm.measurable isOpen_Iio.measurableSet
  }
  have h3 : MeasurableSet {z : ℂ | z.arg ∈ Ioo (-(Real.pi/4)) (Real.pi/4)} := by {
    have : {z : ℂ | z.arg ∈ Ioo (-(Real.pi/4)) (Real.pi/4)} = Complex.arg ⁻¹' (Ioo (-(Real.pi/4)) (Real.pi/4)) := rfl
    rw [this]
    exact measurableSet_preimage Complex.measurable_arg measurableSet_Ioo
  }
  have h_inter : S0 = {z : ℂ | 0 < ‖z‖} ∩ {z : ℂ | ‖z‖ < 1/2} ∩ {z : ℂ | z.arg ∈ Ioo (-(Real.pi/4)) (Real.pi/4)} := by {
    ext z
    simp only [S0, mem_setOf_eq, mem_inter_iff, mem_Ioo]
    tauto
  }
  rw [h_inter]
  exact h1.inter h2 |>.inter h3
}

lemma R_measurable : MeasurableSet R :=
  measurableSet_Ioo.prod measurableSet_Ioo

lemma S0_polar_preimage (p : ℝ × ℝ) (hp : p ∈ polarCoord.target) :
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

lemma sector_in_disk (z : ℂ) (hz : z ∈ S0) : ‖1 - z‖ < 1 := by {
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

lemma preimage_sub_one_S0_subset : (fun z : ℂ ↦ 1 - z) ⁻¹' S0 ⊆ Metric.ball 0 1 := by {
  intro z hz
  simp only [mem_preimage] at hz
  rw [Metric.mem_ball, dist_zero_right]
  have h_norm := sector_in_disk (1 - z) hz
  have h_eq : 1 - (1 - z) = z := by ring
  rw [h_eq] at h_norm
  exact h_norm
}

lemma sub_one_measurableEmbedding : MeasurableEmbedding (fun z : ℂ ↦ 1 - z) := by {
  have : (fun z : ℂ ↦ 1 - z) = ⇑(Homeomorph.subLeft 1) := by rfl
  rw [this]
  exact (Homeomorph.subLeft 1).toMeasurableEquiv.measurableEmbedding
}

lemma preimage_add_one_S0_subset : (fun w : ℂ ↦ w + 1) ⁻¹' S0 ⊆ Metric.ball 0 1 := by {
  intro w hw
  simp only [mem_preimage] at hw
  rw [Metric.mem_ball, dist_zero_right]
  have h_norm := sector_in_disk (w + 1) hw
  have h_eq : 1 - (w + 1) = -w := by ring
  rw [h_eq, norm_neg] at h_norm
  exact h_norm
}

lemma measurePreserving_add_one : MeasurePreserving (fun w : ℂ ↦ w + 1) volume volume := by {
  have h_eq : (fun w : ℂ ↦ w + 1) = (fun w : ℂ ↦ (1 : ℂ) + w) := by {
    ext w
    ring
  }
  rw [h_eq]
  exact measurePreserving_add_left volume (1 : ℂ)
}

lemma add_one_measurableEmbedding : MeasurableEmbedding (fun w : ℂ ↦ w + 1) := by {
  have : (fun w : ℂ ↦ w + 1) = ⇑(Homeomorph.addLeft (1 : ℂ)) := by {
    ext w
    simp [add_comm]
  }
  rw [this]
  exact (Homeomorph.addLeft (1 : ℂ)).toMeasurableEquiv.measurableEmbedding
}

--  The integral of |K'(w)|^(2-p) over the unit disk diverges for p >= 4 due to the cusp singularity at w = -1.
theorem cusp_divergence (p : ℝ) (hp : p ≥ 4) :
    ¬ IntegrableOn (fun w => ‖deriv koebe w‖ ^ (2 - p)) (Metric.ball 0 1) volume := by {
  intro h_int
  have h_subset : (fun w : ℂ ↦ w + 1) ⁻¹' S0 ⊆ Metric.ball 0 1 := preimage_add_one_S0_subset
  have h_int_sub := h_int.mono_set h_subset
  have h_finite_val : (∫⁻ x in (fun w : ℂ ↦ w + 1) ⁻¹' S0, (‖‖deriv koebe x‖ ^ (2 - p)‖₊ : ℝ≥0∞) ∂volume) < ⊤ := h_int_sub.hasFiniteIntegral
  have h_cv : (∫⁻ w in (fun w : ℂ ↦ w + 1) ⁻¹' S0, (‖‖deriv koebe w‖ ^ (2 - p)‖₊ : ℝ≥0∞) ∂volume) =
      (∫⁻ z in S0, (‖‖deriv koebe (z - 1)‖ ^ (2 - p)‖₊ : ℝ≥0∞) ∂volume) := by {
    have h_eq : (fun w : ℂ ↦ (‖‖deriv koebe w‖ ^ (2 - p)‖₊ : ℝ≥0∞)) =
        (fun z : ℂ ↦ (‖‖deriv koebe (z - 1)‖ ^ (2 - p)‖₊ : ℝ≥0∞)) ∘ (fun w : ℂ ↦ w + 1) := by {
      ext w
      simp only [Function.comp_apply]
      congr 3
      ring
    }
    rw [h_eq]
    exact measurePreserving_add_one.setLIntegral_comp_preimage_emb add_one_measurableEmbedding (fun z : ℂ ↦ (‖‖deriv koebe (z - 1)‖ ^ (2 - p)‖₊ : ℝ≥0∞)) S0
  }
  have h_finite_S0 : (∫⁻ z in S0, (‖‖deriv koebe (z - 1)‖ ^ (2 - p)‖₊ : ℝ≥0∞) ∂volume) < ⊤ := h_cv ▸ h_finite_val

  have h_deriv_eq : ∀ z ∈ S0, deriv koebe (z - 1) = z / (2 - z) ^ 3 := by {
    intro z hz
    have hz_norm : ‖z - 1‖ < 1 := by {
      rw [norm_sub_rev]
      exact sector_in_disk z hz
    }
    rw [deriv_koebe (z - 1) hz_norm]
    have h1 : 1 + (z - 1) = z := by ring
    have h2 : 1 - (z - 1) = 2 - z := by ring
    rw [h1, h2]
  }
  have h_norm_le : ∀ z ∈ S0, ‖deriv koebe (z - 1)‖ ≤ ‖z‖ * (8 / 27) := by {
    intro z hz
    rw [h_deriv_eq z hz]
    rw [norm_div]
    have hz_norm_pos : 0 < ‖z‖ := hz.1
    have h_den : 3 / 2 ≤ ‖2 - z‖ := by {
      have : ‖(2 : ℂ)‖ - ‖z‖ ≤ ‖2 - z‖ := norm_sub_norm_le (2 : ℂ) z
      have h_two : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h_two] at this
      linarith [hz.2.1]
    }
    have h_den_cub : (3 / 2) ^ 3 ≤ ‖2 - z‖ ^ 3 := by {
      apply pow_le_pow_left₀ (by norm_num) h_den
    }
    have h_den_val : (3 / 2 : ℝ) ^ 3 = 27 / 8 := by norm_num
    rw [h_den_val] at h_den_cub
    have h_inv : 1 / ‖2 - z‖ ^ 3 ≤ 8 / 27 := by {
      have h1 : 1 / ‖2 - z‖ ^ 3 = (‖2 - z‖ ^ 3)⁻¹ := by ring
      rw [h1]
      have h2 : (8 / 27 : ℝ) = (27 / 8 : ℝ)⁻¹ := by norm_num
      rw [h2]
      apply inv_anti₀ (by norm_num) h_den_cub
    }
    have h_pow : ‖(2 - z) ^ 3‖ = ‖2 - z‖ ^ 3 := by rw [norm_pow]
    rw [h_pow]
    have h_eq_mul : ‖z‖ / ‖2 - z‖ ^ 3 = ‖z‖ * (1 / ‖2 - z‖ ^ 3) := by ring
    rw [h_eq_mul]
    apply mul_le_mul_of_nonneg_left h_inv
    positivity
  }
  have h_rpow_ge : ∀ z ∈ S0, (‖z‖ * (8 / 27)) ^ (2 - p) ≤ ‖deriv koebe (z - 1)‖ ^ (2 - p) := by {
    intro z hz
    have h_pos : 0 < ‖deriv koebe (z - 1)‖ := by {
      rw [h_deriv_eq z hz]
      rw [norm_pos_iff, div_ne_zero_iff]
      have hz_ne : z ≠ 0 := by {
        intro hz0
        have : ‖z‖ = 0 := by rw [hz0, norm_zero]
        have hz_pos := hz.1
        linarith
      }
      refine ⟨hz_ne, ?_⟩
      intro h_eq
      have hz_norm : ‖z‖ < 1/2 := hz.2.1
      have : ‖2 - z‖ ≥ 3/2 := by {
        have := norm_sub_norm_le (2 : ℂ) z
        have h_two : ‖(2 : ℂ)‖ = 2 := by simp
        rw [h_two] at this
        linarith
      }
      have h_zero : 2 - z = 0 := by {
        rwa [pow_eq_zero_iff (by decide : 3 ≠ 0)] at h_eq
      }
      have : ‖2 - z‖ = 0 := by rw [h_zero, norm_zero]
      linarith
    }
    have h_le := h_norm_le z hz
    have h_exp : 2 - p ≤ 0 := by linarith
    have h_pos_y : 0 < ‖z‖ * (8 / 27) := by {
      apply mul_pos hz.1
      norm_num
    }
    exact Real.rpow_le_rpow_of_nonpos h_pos h_le h_exp
  }
  have h_pow_eq : ∀ z ∈ S0, (‖z‖ * (8 / 27)) ^ (2 - p) = (8 / 27) ^ (2 - p) * ‖z‖ ^ (2 - p) := by {
    intro z hz
    have hz_pos : 0 < ‖z‖ := hz.1
    rw [mul_comm]
    rw [Real.mul_rpow (by norm_num) hz_pos.le]
  }
  have h_lintegral_ge : (∫⁻ z in S0, (‖‖deriv koebe (z - 1)‖ ^ (2 - p)‖₊ : ℝ≥0∞) ∂volume) ≥
      (∫⁻ z in S0, ENNReal.ofReal ((8 / 27) ^ (2 - p) * ‖z‖ ^ (2 - p)) ∂volume) := by {
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem S0_measurable] with z hz
    have h_rpow := h_rpow_ge z hz
    have h_pow := h_pow_eq z hz
    have h_nnnorm : (‖‖deriv koebe (z - 1)‖ ^ (2 - p)‖₊ : ℝ≥0∞) = ENNReal.ofReal (‖deriv koebe (z - 1)‖ ^ (2 - p)) := by {
      rw [Real.nnnorm_of_nonneg (by positivity)]
      rw [ENNReal.ofReal]
      rw [Real.toNNReal_of_nonneg (by positivity)]
    }
    rw [h_nnnorm]
    rw [← h_pow]
    exact ENNReal.ofReal_le_ofReal h_rpow
  }
  have h_domain : polarCoord.target ∩ Complex.polarCoord.symm ⁻¹' S0 = R := by {
    ext pt
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hp, hz⟩
      rwa [S0_polar_preimage pt hp] at hz
    · intro hp_R
      have hp : pt ∈ polarCoord.target := by {
        unfold R at hp_R
        simp only [mem_prod, mem_Ioo] at hp_R
        change pt ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
        simp only [mem_prod, mem_Ioi, mem_Ioo]
        refine ⟨hp_R.1.1, ?_⟩
        constructor
        · linarith [Real.pi_pos, hp_R.2.1]
        · linarith [Real.pi_pos, hp_R.2.2]
      }
      refine ⟨hp, ?_⟩
      rwa [S0_polar_preimage pt hp]
  }
  have h_polar : (∫⁻ z in S0, ENNReal.ofReal (‖z‖ ^ (2 - p)) ∂volume) =
      ∫⁻ pt in R, ENNReal.ofReal (pt.1 ^ (3 - p)) ∂(volume.prod volume) := by {
    rw [lintegral_polar_indicator _ S0 S0_measurable]
    rw [h_domain]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem R_measurable] with pt hpt
    have hp_target : pt ∈ polarCoord.target := by {
      unfold R at hpt
      simp only [mem_prod, mem_Ioo] at hpt
      change pt ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
      simp only [mem_prod, mem_Ioi, mem_Ioo]
      refine ⟨hpt.1.1, ?_⟩
      constructor
      · linarith [Real.pi_pos, hpt.2.1]
      · linarith [Real.pi_pos, hpt.2.2]
    }
    have h_eq := Complex.polarCoord.right_inv hp_target
    have h_apply : Complex.polarCoord (Complex.polarCoord.symm pt) = (‖Complex.polarCoord.symm pt‖, Complex.arg (Complex.polarCoord.symm pt)) := Complex.polarCoord_apply _
    rw [h_apply] at h_eq
    have h_norm : ‖Complex.polarCoord.symm pt‖ = pt.1 := congrArg Prod.fst h_eq
    rw [h_norm]
    have hp_pos : 0 < pt.1 := hpt.1.1
    rw [← ENNReal.ofReal_mul hp_pos.le]
    congr 1
    calc pt.1 * pt.1 ^ (2 - p) = pt.1 ^ (1 : ℝ) * pt.1 ^ (2 - p) := by rw [Real.rpow_one]
    _ = pt.1 ^ ((1 : ℝ) + (2 - p)) := by rw [← Real.rpow_add hp_pos]
    _ = pt.1 ^ (3 - p) := by congr 1; ring
  }
  have h_split : (∫⁻ pt in R, ENNReal.ofReal (pt.1 ^ (3 - p)) ∂(volume.prod volume)) =
      (∫⁻ r in Ioo 0 (1/2), ENNReal.ofReal (r ^ (3 - p)) ∂volume) * ENNReal.ofReal (Real.pi / 2) := by {
    have h_meas_eq : (volume.prod volume).restrict R = (volume.restrict (Ioo (0 : ℝ) (1/2))).prod (volume.restrict (Ioo (-(Real.pi/4)) (Real.pi/4))) := by {
      unfold R
      rw [Measure.prod_restrict]
    }
    have h_restrict : (∫⁻ pt in R, ENNReal.ofReal (pt.1 ^ (3 - p)) ∂(volume.prod volume)) =
        ∫⁻ pt, ENNReal.ofReal (pt.1 ^ (3 - p)) ∂((volume.prod volume).restrict R) := rfl
    rw [h_restrict]
    rw [h_meas_eq]
    have h_fun_eq : (fun pt : ℝ × ℝ ↦ ENNReal.ofReal (pt.1 ^ (3 - p))) =
        (fun pt ↦ (fun r ↦ ENNReal.ofReal (r ^ (3 - p))) pt.1 * (fun _ ↦ (1 : ℝ≥0∞)) pt.2) := by {
      ext pt
      rw [mul_one]
    }
    rw [h_fun_eq]
    have h_meas : AEMeasurable (fun r ↦ ENNReal.ofReal (r ^ (3 - p))) (volume.restrict (Ioo 0 (1/2))) := by {
      apply ContinuousOn.aemeasurable _ measurableSet_Ioo
      have h_cont : ContinuousOn (fun r : ℝ ↦ r ^ (3 - p)) (Ioo 0 (1/2)) := by {
        intro x hx
        apply ContinuousAt.continuousWithinAt
        apply Real.continuousAt_rpow_const
        left
        exact hx.1.ne'
      }
      exact ENNReal.continuous_ofReal.continuousOn.comp h_cont (mapsTo_univ _ _)
    }
    rw [MeasureTheory.lintegral_prod_mul h_meas aemeasurable_const]
    have h_restrict_Ioo : (∫⁻ r in Ioo 0 (1/2), ENNReal.ofReal (r ^ (3 - p)) ∂volume) =
        ∫⁻ r, ENNReal.ofReal (r ^ (3 - p)) ∂(volume.restrict (Ioo 0 (1/2))) := rfl
    rw [← h_restrict_Ioo]
    have h_ν : (∫⁻ y, (1 : ℝ≥0∞) ∂(volume.restrict (Ioo (-(Real.pi/4)) (Real.pi/4)))) = ENNReal.ofReal (Real.pi / 2) := by {
      rw [lintegral_one, Measure.restrict_apply MeasurableSet.univ]
      have h_vol : volume (univ ∩ Ioo (-(Real.pi/4)) (Real.pi/4)) = ENNReal.ofReal (Real.pi / 2) := by {
        rw [univ_inter]
        rw [Real.volume_Ioo]
        congr 1
        ring
      }
      rw [h_vol]
    }
    rw [h_ν]
  }
  have h_radial_inf : (∫⁻ r in Ioo 0 (1/2), ENNReal.ofReal (r ^ (3 - p)) ∂volume) = ⊤ := by {
    by_contra hc
    rw [← ne_eq, ← lt_top_iff_ne_top] at hc
    have h_int_rpow : IntegrableOn (fun r : ℝ ↦ r ^ (3 - p)) (Ioo 0 (1/2)) volume := by {
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
    have h_iff := intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1/2) |>.mp h_int_rpow
    have h_exponent : 3 - p ≤ -1 := by linarith
    linarith
  }
  have h_prod_inf : (∫⁻ pt in R, ENNReal.ofReal (pt.1 ^ (3 - p)) ∂(volume.prod volume)) = ⊤ := by {
    rw [h_split, h_radial_inf]
    apply ENNReal.mul_eq_top.mpr
    right
    refine ⟨rfl, ?_⟩
    intro hc
    rw [ENNReal.ofReal_eq_zero] at hc
    have : 0 < Real.pi := Real.pi_pos
    linarith
  }
  have h_const_mul : (∫⁻ z in S0, ENNReal.ofReal ((8 / 27) ^ (2 - p) * ‖z‖ ^ (2 - p)) ∂volume) =
      ENNReal.ofReal ((8 / 27) ^ (2 - p)) * ∫⁻ z in S0, ENNReal.ofReal (‖z‖ ^ (2 - p)) ∂volume := by {
    rw [← lintegral_const_mul']
    · apply lintegral_congr_ae
      filter_upwards [ae_restrict_mem S0_measurable] with z hz
      have hz_pos : 0 < ‖z‖ := hz.1
      have h_const_nonneg : 0 ≤ (8 / 27 : ℝ) ^ (2 - p) := Real.rpow_nonneg (by norm_num) _
      have h_pow_nonneg : 0 ≤ ‖z‖ ^ (2 - p) := Real.rpow_nonneg hz_pos.le _
      rw [← ENNReal.ofReal_mul h_const_nonneg]
    · exact ofReal_ne_top
  }
  have h_lhs_top : (∫⁻ z in S0, ENNReal.ofReal ((8 / 27) ^ (2 - p) * ‖z‖ ^ (2 - p)) ∂volume) = ⊤ := by {
    rw [h_const_mul]
    rw [h_polar, h_prod_inf]
    apply ENNReal.mul_eq_top.mpr
    left
    refine ⟨?_, rfl⟩
    intro hc
    rw [ENNReal.ofReal_eq_zero] at hc
    have : (0 : ℝ) < 8 / 27 := by norm_num
    have h_pow_pos := Real.rpow_pos_of_pos this (2 - p)
    linarith [h_pow_pos]
  }
  have h_inf : (∫⁻ z in S0, (‖‖deriv koebe (z - 1)‖ ^ (2 - p)‖₊ : ℝ≥0∞) ∂volume) = ⊤ := by {
    apply le_antisymm
    · exact le_top
    · rw [← h_lhs_top]
      exact h_lintegral_ge
  }
  rw [h_inf] at h_finite_S0
  exact lt_irrefl ⊤ h_finite_S0
}

--  The integral of |K'(w)|^(2-p) over the unit disk diverges for p <= 4/3 due to the pole singularity at w = 1.
theorem pole_divergence (p : ℝ) (hp : p ≤ 4 / 3) :
    ¬ IntegrableOn (fun w => ‖deriv koebe w‖ ^ (2 - p)) (Metric.ball 0 1) volume := by {
  intro h_int
  have h_subset : (fun z : ℂ ↦ 1 - z) ⁻¹' S0 ⊆ Metric.ball 0 1 := preimage_sub_one_S0_subset
  have h_int_sub := h_int.mono_set h_subset
  have h_finite_val : (∫⁻ x in (fun z : ℂ ↦ 1 - z) ⁻¹' S0, (‖‖deriv koebe x‖ ^ (2 - p)‖₊ : ℝ≥0∞) ∂volume) < ⊤ := h_int_sub.hasFiniteIntegral
  have h_cv : (∫⁻ z in (fun z : ℂ ↦ 1 - z) ⁻¹' S0, (‖‖deriv koebe z‖ ^ (2 - p)‖₊ : ℝ≥0∞) ∂volume) =
      (∫⁻ z in S0, (‖‖deriv koebe (1 - z)‖ ^ (2 - p)‖₊ : ℝ≥0∞) ∂volume) := by {
    have h_eq : (fun z : ℂ ↦ (‖‖deriv koebe z‖ ^ (2 - p)‖₊ : ℝ≥0∞)) =
        (fun z : ℂ ↦ (‖‖deriv koebe (1 - z)‖ ^ (2 - p)‖₊ : ℝ≥0∞)) ∘ (fun z : ℂ ↦ 1 - z) := by {
      ext z
      simp only [Function.comp_apply]
      congr 3
      ring
    }
    rw [h_eq]
    exact measurePreserving_sub_one.setLIntegral_comp_preimage_emb sub_one_measurableEmbedding (fun z : ℂ ↦ (‖‖deriv koebe (1 - z)‖ ^ (2 - p)‖₊ : ℝ≥0∞)) S0
  }
  have h_finite_S0 : (∫⁻ z in S0, (‖‖deriv koebe (1 - z)‖ ^ (2 - p)‖₊ : ℝ≥0∞) ∂volume) < ⊤ := h_cv ▸ h_finite_val

  have h_deriv_eq : ∀ z ∈ S0, deriv koebe (1 - z) = (2 - z) / z ^ 3 := by {
    intro z hz
    have hz_norm : ‖1 - z‖ < 1 := sector_in_disk z hz
    rw [deriv_koebe (1 - z) hz_norm]
    have h1 : 1 + (1 - z) = 2 - z := by ring
    have h2 : 1 - (1 - z) = z := by ring
    rw [h1, h2]
  }
  have h_norm_ge : ∀ z ∈ S0, 1 / ‖z‖ ^ 3 ≤ ‖deriv koebe (1 - z)‖ := by {
    intro z hz
    rw [h_deriv_eq z hz]
    rw [norm_div]
    have hz_norm_pos : 0 < ‖z‖ := hz.1
    have h_num : 1 ≤ ‖2 - z‖ := by {
      have : ‖(2 : ℂ)‖ - ‖z‖ ≤ ‖2 - z‖ := norm_sub_norm_le (2 : ℂ) z
      have h_two : ‖(2 : ℂ)‖ = 2 := by simp
      rw [h_two] at this
      linarith [hz.2.1]
    }
    have h_den : ‖z ^ 3‖ = ‖z‖ ^ 3 := by simp
    rw [h_den]
    apply div_le_div_of_nonneg_right h_num
    positivity
  }
  have h_rpow_ge : ∀ z ∈ S0, (1 / ‖z‖ ^ 3) ^ (2 - p) ≤ ‖deriv koebe (1 - z)‖ ^ (2 - p) := by {
    intro z hz
    apply Real.rpow_le_rpow
    · positivity
    · exact h_norm_ge z hz
    · linarith
  }
  have h_pow_eq : ∀ z ∈ S0, (1 / ‖z‖ ^ 3) ^ (2 - p) = ‖z‖ ^ (3 * p - 6) := by {
    intro z hz
    have h_pos : 0 < ‖z‖ := hz.1
    rw [one_div]
    have h_eq : (‖z‖ ^ 3)⁻¹ = ‖z‖ ^ (-3 : ℝ) := by {
      rw [Real.rpow_neg h_pos.le]
      congr 1
      exact (Real.rpow_natCast ‖z‖ 3).symm
    }
    rw [h_eq]
    rw [← Real.rpow_mul h_pos.le]
    congr 1
    ring
  }
  have h_lintegral_ge : (∫⁻ z in S0, (‖‖deriv koebe (1 - z)‖ ^ (2 - p)‖₊ : ℝ≥0∞) ∂volume) ≥
      (∫⁻ z in S0, ENNReal.ofReal (‖z‖ ^ (3 * p - 6)) ∂volume) := by {
    apply lintegral_mono_ae
    filter_upwards [ae_restrict_mem S0_measurable] with z hz
    have h_rpow := h_rpow_ge z hz
    have h_pow := h_pow_eq z hz
    have h_nnnorm : (‖‖deriv koebe (1 - z)‖ ^ (2 - p)‖₊ : ℝ≥0∞) = ENNReal.ofReal (‖deriv koebe (1 - z)‖ ^ (2 - p)) := by {
      rw [Real.nnnorm_of_nonneg (by positivity)]
      rw [ENNReal.ofReal]
      rw [Real.toNNReal_of_nonneg (by positivity)]
    }
    rw [h_nnnorm]
    rw [← h_pow]
    exact ENNReal.ofReal_le_ofReal h_rpow
  }
  have h_domain : polarCoord.target ∩ Complex.polarCoord.symm ⁻¹' S0 = R := by {
    ext pt
    simp only [mem_inter_iff, mem_preimage]
    constructor
    · rintro ⟨hp, hz⟩
      rwa [S0_polar_preimage pt hp] at hz
    · intro hp_R
      have hp : pt ∈ polarCoord.target := by {
        unfold R at hp_R
        simp only [mem_prod, mem_Ioo] at hp_R
        change pt ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
        simp only [mem_prod, mem_Ioi, mem_Ioo]
        refine ⟨hp_R.1.1, ?_⟩
        constructor
        · linarith [Real.pi_pos, hp_R.2.1]
        · linarith [Real.pi_pos, hp_R.2.2]
      }
      refine ⟨hp, ?_⟩
      rwa [S0_polar_preimage pt hp]
  }
  have h_polar : (∫⁻ z in S0, ENNReal.ofReal (‖z‖ ^ (3 * p - 6)) ∂volume) =
      ∫⁻ pt in R, ENNReal.ofReal (pt.1 ^ (3 * p - 5)) ∂(volume.prod volume) := by {
    rw [lintegral_polar_indicator _ S0 S0_measurable]
    rw [h_domain]
    apply lintegral_congr_ae
    filter_upwards [ae_restrict_mem R_measurable] with pt hpt
    have hp_target : pt ∈ polarCoord.target := by {
      unfold R at hpt
      simp only [mem_prod, mem_Ioo] at hpt
      change pt ∈ Ioi (0 : ℝ) ×ˢ Ioo (-Real.pi) Real.pi
      simp only [mem_prod, mem_Ioi, mem_Ioo]
      refine ⟨hpt.1.1, ?_⟩
      constructor
      · linarith [Real.pi_pos, hpt.2.1]
      · linarith [Real.pi_pos, hpt.2.2]
    }
    have h_eq := Complex.polarCoord.right_inv hp_target
    have h_apply : Complex.polarCoord (Complex.polarCoord.symm pt) = (‖Complex.polarCoord.symm pt‖, Complex.arg (Complex.polarCoord.symm pt)) := Complex.polarCoord_apply _
    rw [h_apply] at h_eq
    have h_norm : ‖Complex.polarCoord.symm pt‖ = pt.1 := congrArg Prod.fst h_eq
    rw [h_norm]
    have hp_pos : 0 < pt.1 := hpt.1.1
    rw [← ENNReal.ofReal_mul hp_pos.le]
    congr 1
    calc pt.1 * pt.1 ^ (3 * p - 6) = pt.1 ^ (1 : ℝ) * pt.1 ^ (3 * p - 6) := by rw [Real.rpow_one]
    _ = pt.1 ^ ((1 : ℝ) + (3 * p - 6)) := by rw [← Real.rpow_add hp_pos]
    _ = pt.1 ^ (3 * p - 5) := by congr 1; ring
  }
  have h_split : (∫⁻ pt in R, ENNReal.ofReal (pt.1 ^ (3 * p - 5)) ∂(volume.prod volume)) =
      (∫⁻ r in Ioo 0 (1/2), ENNReal.ofReal (r ^ (3 * p - 5)) ∂volume) * ENNReal.ofReal (Real.pi / 2) := by {
    have h_meas_eq : (volume.prod volume).restrict R = (volume.restrict (Ioo (0 : ℝ) (1/2))).prod (volume.restrict (Ioo (-(Real.pi/4)) (Real.pi/4))) := by {
      unfold R
      rw [Measure.prod_restrict]
    }
    have h_restrict : (∫⁻ pt in R, ENNReal.ofReal (pt.1 ^ (3 * p - 5)) ∂(volume.prod volume)) =
        ∫⁻ pt, ENNReal.ofReal (pt.1 ^ (3 * p - 5)) ∂((volume.prod volume).restrict R) := rfl
    rw [h_restrict]
    rw [h_meas_eq]
    have h_fun_eq : (fun pt : ℝ × ℝ ↦ ENNReal.ofReal (pt.1 ^ (3 * p - 5))) =
        (fun pt ↦ (fun r ↦ ENNReal.ofReal (r ^ (3 * p - 5))) pt.1 * (fun _ ↦ (1 : ℝ≥0∞)) pt.2) := by {
      ext pt
      rw [mul_one]
    }
    rw [h_fun_eq]
    have h_meas : AEMeasurable (fun r ↦ ENNReal.ofReal (r ^ (3 * p - 5))) (volume.restrict (Ioo 0 (1/2))) := by {
      apply ContinuousOn.aemeasurable _ measurableSet_Ioo
      have h_cont : ContinuousOn (fun r : ℝ ↦ r ^ (3 * p - 5)) (Ioo 0 (1/2)) := by {
        intro x hx
        apply ContinuousAt.continuousWithinAt
        apply Real.continuousAt_rpow_const
        left
        exact hx.1.ne'
      }
      exact ENNReal.continuous_ofReal.continuousOn.comp h_cont (mapsTo_univ _ _)
    }
    rw [MeasureTheory.lintegral_prod_mul h_meas aemeasurable_const]
    have h_restrict_Ioo : (∫⁻ r in Ioo 0 (1/2), ENNReal.ofReal (r ^ (3 * p - 5)) ∂volume) =
        ∫⁻ r, ENNReal.ofReal (r ^ (3 * p - 5)) ∂(volume.restrict (Ioo 0 (1/2))) := rfl
    rw [← h_restrict_Ioo]
    have h_ν : (∫⁻ y, (1 : ℝ≥0∞) ∂(volume.restrict (Ioo (-(Real.pi/4)) (Real.pi/4)))) = ENNReal.ofReal (Real.pi / 2) := by {
      rw [lintegral_one, Measure.restrict_apply MeasurableSet.univ]
      have h_vol : volume (univ ∩ Ioo (-(Real.pi/4)) (Real.pi/4)) = ENNReal.ofReal (Real.pi / 2) := by {
        rw [univ_inter]
        rw [Real.volume_Ioo]
        congr 1
        ring
      }
      rw [h_vol]
    }
    rw [h_ν]
  }
  have h_radial_inf : (∫⁻ r in Ioo 0 (1/2), ENNReal.ofReal (r ^ (3 * p - 5)) ∂volume) = ⊤ := by {
    by_contra hc
    rw [← ne_eq, ← lt_top_iff_ne_top] at hc
    have h_int_rpow : IntegrableOn (fun r : ℝ ↦ r ^ (3 * p - 5)) (Ioo 0 (1/2)) volume := by {
      constructor
      · refine ContinuousOn.aestronglyMeasurable ?_ measurableSet_Ioo
        intro x hx
        apply ContinuousAt.continuousWithinAt
        apply Real.continuousAt_rpow_const
        left
        exact hx.1.ne'
      · have h_eq_lintegral : (∫⁻ x, (‖(x : ℝ) ^ (3 * p - 5)‖₊ : ℝ≥0∞) ∂(volume.restrict (Ioo 0 (1/2)))) =
            (∫⁻ r in Ioo 0 (1/2), ENNReal.ofReal (r ^ (3 * p - 5)) ∂volume) := by {
          apply lintegral_congr_ae
          filter_upwards [ae_restrict_mem measurableSet_Ioo] with r hr
          have hr_pos : 0 < r := hr.1
          have hrpow_nonneg : 0 ≤ r ^ (3 * p - 5) := Real.rpow_nonneg hr_pos.le (3 * p - 5)
          rw [Real.nnnorm_of_nonneg hrpow_nonneg]
          rw [ENNReal.ofReal]
          rw [Real.toNNReal_of_nonneg hrpow_nonneg]
        }
        change (∫⁻ x, (‖(x : ℝ) ^ (3 * p - 5)‖₊ : ℝ≥0∞) ∂(volume.restrict (Ioo 0 (1/2)))) < ⊤
        rw [h_eq_lintegral]
        exact hc
    }
    have h_iff := intervalIntegral.integrableOn_Ioo_rpow_iff (by norm_num : (0 : ℝ) < 1/2) |>.mp h_int_rpow
    have h_exponent : 3 * p - 5 ≤ -1 := by {
      calc 3 * p - 5 ≤ 3 * (4 / 3) - 5 := by linarith
      _ = -1 := by ring
    }
    linarith
  }
  have h_prod_inf : (∫⁻ pt in R, ENNReal.ofReal (pt.1 ^ (3 * p - 5)) ∂(volume.prod volume)) = ⊤ := by {
    rw [h_split, h_radial_inf]
    apply ENNReal.mul_eq_top.mpr
    right
    refine ⟨rfl, ?_⟩
    intro hc
    rw [ENNReal.ofReal_eq_zero] at hc
    have : 0 < Real.pi := Real.pi_pos
    linarith
  }
  have h_inf : (∫⁻ z in S0, (‖‖deriv koebe (1 - z)‖ ^ (2 - p)‖₊ : ℝ≥0∞) ∂volume) = ⊤ := by {
    apply le_antisymm
    · exact le_top
    · rw [← h_prod_inf, ← h_polar]
      exact h_lintegral_ge
  }
  rw [h_inf] at h_finite_S0
  exact lt_irrefl ⊤ h_finite_S0
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
