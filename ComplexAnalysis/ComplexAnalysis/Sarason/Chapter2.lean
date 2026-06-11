/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Complex.RealDeriv
import Mathlib.Analysis.Complex.Conformal
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.FDeriv.Star
import ComplexAnalysis.Sarason.Definitions
/-!
# Sarason - Chapter 2: Complex Differentiation

Formalization of Section II of Donald Sarason's "Notes on Complex Function Theory".
Focus: Definition of the derivative, Cauchy-Riemann equations, and Differential Operators.

Credit: Donald Sarason
-/

open Complex Filter Metric Sarason TopologicalSpace ContinuousLinearMap
open scoped Topology

noncomputable section

namespace Sarason.Ch2

/-
  §II.1 Definition of the Derivative (Sarason's Weierstrass style).
  DifferentiableAt is defined in Definitions.lean using HasLimitAt_eps.
-/

/-- The ∂ operator (del) for a function f : ℂ → ℂ at point z. -/
def del (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  let L := fderiv ℝ f z
  let df_dx := L 1
  let df_dy := L I
  (1 / 2 : ℂ) * (df_dx - I * df_dy)

/-- The ∂̄ operator (del-bar) for a function f : ℂ → ℂ at point z. -/
def delBar (f : ℂ → ℂ) (z : ℂ) : ℂ :=
  let L := fderiv ℝ f z
  let df_dx := L 1
  let df_dy := L I
  (1 / 2 : ℂ) * (df_dx + I * df_dy)

-- Local notation for Sarason's flavor
local notation f "𝓏" => del f
local notation f "𝓏bar" => delBar f

/--
  Relating Sarason's Weierstrass derivative to Mathlib's Filter-based HasDerivAt.
-/
theorem differentiableAt_iff_mathlib (f : ℂ → ℂ) (f' : ℂ) (z₀ : ℂ) :
    HasDerivAt_eps f f' z₀ ↔ _root_.HasDerivAt f f' z₀ := by {
  rw [hasDerivAt_iff_eps]
}

/--
  §II.6 Cauchy-Riemann Equations (Sarason's version).
-/
theorem hasComplexDerivAt_iff_delBar_eq_zero {f : ℂ → ℂ} {z : ℂ} (h : _root_.DifferentiableAt ℝ f z) :
    (∃ f', HasDerivAt_eps f f' z) ↔ (delBar f z = 0) := by {
  have hd : (∃ f', HasDerivAt_eps f f' z) ↔ DifferentiableAt_eps f z := Iff.rfl
  rw [hd]
  rw [← differentiableAt_iff_eps]
  rw [differentiableAt_complex_iff_differentiableAt_real]
  simp only [h, true_and]
  unfold delBar
  dsimp only
  have : (1 / 2 : ℂ) ≠ 0 := by norm_num
  rw [mul_eq_zero, or_iff_right this]
  simp only [smul_eq_mul]
  constructor
  · intro h_cr
    rw [h_cr]
    have : I * (I * fderiv ℝ f z 1) = - fderiv ℝ f z 1 := by {
      calc I * (I * fderiv ℝ f z 1) = (I * I) * fderiv ℝ f z 1 := by ring
      _ = -1 * fderiv ℝ f z 1 := by rw [I_mul_I]
      _ = - fderiv ℝ f z 1 := by ring
    }
    rw [this]
    ring
  · intro h_delbar
    have h1 : I * (fderiv ℝ f z 1 + I * fderiv ℝ f z I) = I * 0 := by rw [h_delbar]
    simp only [mul_zero, mul_add] at h1
    have h2 : I * (I * fderiv ℝ f z I) = - fderiv ℝ f z I := by {
      calc I * (I * fderiv ℝ f z I) = (I * I) * fderiv ℝ f z I := by ring
      _ = -1 * fderiv ℝ f z I := by rw [I_mul_I]
      _ = - fderiv ℝ f z I := by ring
    }
    rw [h2] at h1
    have h3 : I * fderiv ℝ f z 1 - fderiv ℝ f z I = 0 := by {
      calc I * fderiv ℝ f z 1 - fderiv ℝ f z I = I * fderiv ℝ f z 1 + - fderiv ℝ f z I := by ring
      _ = 0 := h1
    }
    exact (sub_eq_zero.mp h3).symm
}


/--
  Example 1: f(z) = z^2 is holomorphic everywhere.
-/
example (z : ℂ) : DifferentiableAt ℂ (fun z => z^2) z :=
  differentiableAt_pow 2

/--
  Example 2: f(z) = conj z is NOT holomorphic.
  We use the fact that the derivative of `conj` is `conj`,
  which is not complex linear.
-/
example (z : ℂ) : ¬ DifferentiableAt ℂ (fun z => star z) z := by {
  intro h
  -- The real derivative of `star` is `star` itself.
  have hstar : HasFDerivAt star ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) z :=
    HasFDerivAt.star (hasFDerivAt_id (𝕜 := ℝ) z)
  -- If `star` were complex differentiable, its real derivative would be complex linear.
  let f'' := fderiv ℂ (fun z => star z) z
  let L : ℂ →L[ℝ] ℂ := f''.restrictScalars ℝ
  have h_real : HasFDerivAt star L z := h.hasFDerivAt.restrictScalars ℝ
  have hL : ((starL' ℝ : ℂ ≃L[ℝ] ℂ) : ℂ →L[ℝ] ℂ) = L := hstar.unique h_real
  have h_comm : L I = I * L 1 := by {
    have h_smul := f''.map_smul I 1
    simp at h_smul
    exact h_smul
  }
  have h_star : L I = -I := by {
    rw [← hL]
    simp
  }
  have h_star1 : L 1 = 1 := by {
    rw [← hL]
    simp
  }
  have h_contra : -I = I := by {
    calc -I = L I := h_star.symm
    _ = I * L 1 := h_comm
    _ = I * 1 := by rw [h_star1]
    _ = I := by rw [mul_one]
  }
  have : (2 : ℂ) * I = 0 := by {
    calc (2 : ℂ) * I = I - (-I) := by ring
    _ = I - I := by rw [h_contra]
    _ = 0 := by ring
  }
  have h_mul : (2 : ℂ) = 0 ∨ I = 0 := mul_eq_zero.mp this
  rcases h_mul with h2 | hI
  · norm_num at h2
  · exact I_ne_zero hI
}

theorem hasFDerivAt_of_hasPartialDeriv {G : Set ℂ} (hG : IsOpen G)
    (u : ℂ → ℝ) (ux uy : ℂ → ℝ)
    (hu_x : ∀ z ∈ G, HasPartialDerivX_C_to_R_eps u (ux z) z)
    (hu_y : ∀ z ∈ G, HasPartialDerivY_C_to_R_eps u (uy z) z)
    (h_cont_ux : ContinuousOn ux G) (h_cont_uy : ContinuousOn uy G)
    (z₀ : ℂ) (hz₀ : z₀ ∈ G) :
    HasFDerivAt u (ux z₀ • reCLM + uy z₀ • imCLM) z₀ := by {
  let f : ℝ → ℝ → ℝ := fun x y ↦ u ⟨x, y⟩
  let f₁ : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun x y ↦ toSpanSingleton ℝ (ux ⟨x, y⟩)
  let f₂ : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun x y ↦ toSpanSingleton ℝ (uy ⟨x, y⟩)
  let p₀ : ℝ × ℝ := (z₀.re, z₀.im)
  -- G is a neighborhood of z₀ because G is open.
  have h_G_nhds : G ∈ 𝓝 z₀ := hG.mem_nhds hz₀
  -- Since ux is continuous on G, it is continuous at the point z₀.
  have h_cont_ux_z₀ : ContinuousAt ux z₀ := h_cont_ux.continuousAt h_G_nhds
  -- Since uy is continuous on G, it is continuous at the point z₀.
  have h_cont_uy_z₀ : ContinuousAt uy z₀ := h_cont_uy.continuousAt h_G_nhds

  -- We show that the coordinate-wise function v ↦ ux(v.1, v.2) is continuous at p₀ by composing ux with the equivalence between ℝ² and ℂ.
  have h_ux_comp_cont : ContinuousAt (fun v : ℝ × ℝ ↦ ux ⟨v.1, v.2⟩) p₀ := by {
    have : (fun v : ℝ × ℝ ↦ ux ⟨v.1, v.2⟩) = ux ∘ equivRealProdCLM.symm := by {
      ext v
      rfl
    }
    rw [this]
    exact h_cont_ux_z₀.comp equivRealProdCLM.symm.continuous.continuousAt
  }

  -- Similarly, we show that the coordinate-wise function v ↦ uy(v.1, v.2) is continuous at p₀.
  have h_uy_comp_cont : ContinuousAt (fun v : ℝ × ℝ ↦ uy ⟨v.1, v.2⟩) p₀ := by {
    have : (fun v : ℝ × ℝ ↦ uy ⟨v.1, v.2⟩) = uy ∘ equivRealProdCLM.symm := by {
      ext v
      rfl
    }
    rw [this]
    exact h_cont_uy_z₀.comp equivRealProdCLM.symm.continuous.continuousAt
  }

  -- Since the scalar-to-linear-map operator toSpanSingleton is continuous, the partial derivative map f₁ (curried) is continuous at p₀.
  have cf₁ : ContinuousAt ↿f₁ p₀ := by {
    have : ↿f₁ = (toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)) ∘ (fun v : ℝ × ℝ ↦ ux ⟨v.1, v.2⟩) := by {
      ext v
      rfl
    }
    rw [this]
    exact (toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.continuousAt.comp h_ux_comp_cont
  }

  -- Similarly, the partial derivative map f₂ is continuous at p₀.
  have cf₂ : ContinuousAt ↿f₂ p₀ := by {
    have : ↿f₂ = (toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)) ∘ (fun v : ℝ × ℝ ↦ uy ⟨v.1, v.2⟩) := by {
      ext v
      rfl
    }
    rw [this]
    exact (toSpanSingletonCLE : ℝ ≃L[ℝ] (ℝ →L[ℝ] ℝ)).continuous.continuousAt.comp h_uy_comp_cont
  }

  -- The preimage of G under the ℝ² ≃ ℂ equivalence is a neighborhood of p₀ in ℝ².
  have h_G_preimage : equivRealProdCLM.symm ⁻¹' G ∈ 𝓝 p₀ := by {
    apply IsOpen.mem_nhds
    · exact hG.preimage equivRealProdCLM.symm.continuous
    · exact hz₀
  }

  -- At every point in the neighborhood, the x-partial derivative of u (fixing y) is the 1D derivative of f with respect to x.
  have h_df₁_of_mem : ∀ v ∈ equivRealProdCLM.symm ⁻¹' G, HasFDerivAt (f · v.2) (f₁ v.1 v.2) v.1 := by {
    intro v hv
    have hw : ⟨v.1, v.2⟩ ∈ G := hv
    have h_part := hu_x ⟨v.1, v.2⟩ hw
    rw [← hasPartialDerivX_iff_eps] at h_part
    rw [hasDerivAt_iff_hasFDerivAt] at h_part
    have h_fun_eq : (fun x : ℝ ↦ u ((x : ℂ) + (v.2 : ℂ) * I)) = (f · v.2) := by {
      ext x
      congr 1
      exact Complex.re_add_im ⟨x, v.2⟩
    }
    rw [h_fun_eq] at h_part
    exact h_part
  }

  -- Similarly, the y-partial derivative of u (fixing x) is the 1D derivative of f with respect to y.
  have h_df₂_of_mem : ∀ v ∈ equivRealProdCLM.symm ⁻¹' G, HasFDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2 := by {
    intro v hv
    have hw : ⟨v.1, v.2⟩ ∈ G := hv
    have h_part := hu_y ⟨v.1, v.2⟩ hw
    rw [← hasPartialDerivY_iff_eps] at h_part
    rw [hasDerivAt_iff_hasFDerivAt] at h_part
    have h_fun_eq : (fun y : ℝ ↦ u ((v.1 : ℂ) + (y : ℂ) * I)) = (f v.1 ·) := by {
      ext y
      congr 1
      exact Complex.re_add_im ⟨v.1, y⟩
    }
    rw [h_fun_eq] at h_part
    exact h_part
  }

  -- Consequently, the x-partial derivative map is a derivative in a neighborhood of p₀.
  have df₁ : ∀ᶠ v in 𝓝 p₀, HasFDerivAt (f · v.2) (f₁ v.1 v.2) v.1 := by {
    filter_upwards [h_G_preimage] using h_df₁_of_mem
  }

  -- Consequently, the y-partial derivative map is a derivative in a neighborhood of p₀.
  have df₂ : ∀ᶠ v in 𝓝 p₀, HasFDerivAt (f v.1 ·) (f₂ v.1 v.2) v.2 := by {
    filter_upwards [h_G_preimage] using h_df₂_of_mem
  }

  -- By the total differentiability criterion (hasStrictFDerivAt_uncurry_coprod), since the partial derivatives exist in a neighborhood and are continuous at the point, u is strictly differentiable at p₀ in ℝ².
  have h_strict : HasStrictFDerivAt (fun p ↦ f p.1 p.2) ((f₁ p₀.1 p₀.2).coprod (f₂ p₀.1 p₀.2)) p₀ := by {
    exact hasStrictFDerivAt_uncurry_coprod df₁ df₂ cf₁ cf₂
  }

  -- Strict differentiability implies standard Fréchet differentiability at p₀.
  have h_fderiv : HasFDerivAt (fun p ↦ u ⟨p.1, p.2⟩) ((f₁ p₀.1 p₀.2).coprod (f₂ p₀.1 p₀.2)) p₀ := h_strict.hasFDerivAt

  -- We rewrite p₀ using the equivalence back to z₀ in ℂ.
  have hp₀_eq : p₀ = equivRealProdCLM z₀ := (equivRealProdCLM_apply z₀).symm
  rw [hp₀_eq] at h_fderiv

  -- By the chain rule, we compose u (on ℝ²) with the linear equivalence (ℂ ≃ ℝ²) to get a derivative on ℂ.
  have h_comp_deriv := HasFDerivAt.comp z₀ h_fderiv (ContinuousLinearMap.hasFDerivAt (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ) : HasFDerivAt (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ) (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ) z₀)

  -- We show that the coproduct derivative under the equivalence simplifies to the standard form: ux * re + uy * im.
  have h_deriv_eq : ((f₁ (equivRealProdCLM z₀).1 (equivRealProdCLM z₀).2).coprod (f₂ (equivRealProdCLM z₀).1 (equivRealProdCLM z₀).2)).comp (equivRealProdCLM : ℂ →L[ℝ] ℝ × ℝ) = ux z₀ • reCLM + uy z₀ • imCLM := by {
    apply ContinuousLinearMap.ext
    intro h
    simp only [comp_apply, ContinuousLinearEquiv.coe_coe, equivRealProdCLM_apply, coprod_apply, f₁, f₂,
      toSpanSingleton_apply, add_apply, smul_apply, reCLM_apply, imCLM_apply,
      smul_eq_mul]
    have : (⟨z₀.re, z₀.im⟩ : ℂ) = z₀ := by {
      apply Complex.ext <;> rfl
    }
    rw [this]
    ring
  }
  rw [h_deriv_eq] at h_comp_deriv
  exact h_comp_deriv
}

theorem differentiableAt_real_of_parts {f : ℂ → ℂ} {u v : ℂ → ℝ} {x : ℂ}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (h_parts : ∀ z, f z = u z + I * v z) :
    DifferentiableAt ℝ f x := by {
  have h_eq : f = (fun z => (u z : ℂ) + I * (v z : ℂ)) := by {
    ext z
    exact h_parts z
  }
  rw [h_eq]
  refine DifferentiableAt.add ?_ ?_
  · have h_comp : (fun z => (u z : ℂ)) = ofRealCLM ∘ u := by { ext z; rfl }
    rw [h_comp]
    exact ofRealCLM.differentiableAt.comp x hu
  · have h_comp : (fun z => I * (v z : ℂ)) = (I • ContinuousLinearMap.id ℝ ℂ) ∘ (ofRealCLM ∘ v) := by {
      ext z
      simp only [Function.comp_apply, ofRealCLM_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    }
    rw [h_comp]
    refine (I • ContinuousLinearMap.id ℝ ℂ).differentiableAt.comp x ?_
    exact ofRealCLM.differentiableAt.comp x hv
}

theorem fderiv_parts {f : ℂ → ℂ} {u v : ℂ → ℝ} {x : ℂ}
    (hu : DifferentiableAt ℝ u x) (hv : DifferentiableAt ℝ v x)
    (h_parts : ∀ z, f z = u z + I * v z) :
    fderiv ℝ f x = ofRealCLM.comp (fderiv ℝ u x) + (I • ContinuousLinearMap.id ℝ ℂ).comp (ofRealCLM.comp (fderiv ℝ v x)) := by {
  have h_eq : f = (fun z => (u z : ℂ) + I * (v z : ℂ)) := by {
    ext z
    exact h_parts z
  }
  rw [h_eq]
  have h_u_diff : DifferentiableAt ℝ (fun z => (u z : ℂ)) x := by {
    have h_comp : (fun z => (u z : ℂ)) = ofRealCLM ∘ u := by { ext z; rfl }
    rw [h_comp]
    exact ofRealCLM.differentiableAt.comp x hu
  }
  have h_v_diff : DifferentiableAt ℝ (fun z => I * (v z : ℂ)) x := by {
    have h_comp : (fun z => I * (v z : ℂ)) = (I • ContinuousLinearMap.id ℝ ℂ) ∘ (ofRealCLM ∘ v) := by {
      ext z
      simp only [Function.comp_apply, ofRealCLM_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
    }
    rw [h_comp]
    refine (I • ContinuousLinearMap.id ℝ ℂ).differentiableAt.comp x ?_
    exact ofRealCLM.differentiableAt.comp x hv
  }
  have h_sum : (fun z => (u z : ℂ) + I * (v z : ℂ)) = (fun z => (u z : ℂ)) + (fun z => I * (v z : ℂ)) := rfl
  rw [h_sum]
  rw [fderiv_add h_u_diff h_v_diff]
  congr 1
  · have h_comp : (fun z => (u z : ℂ)) = ofRealCLM ∘ u := by { ext z; rfl }
    rw [h_comp]
    rw [fderiv_comp x ofRealCLM.differentiableAt hu]
    rw [ofRealCLM.fderiv]
  · have h_comp : (fun z => I * (v z : ℂ)) = (I • ContinuousLinearMap.id ℝ ℂ) ∘ (ofRealCLM ∘ v) := by {
      ext z
      simp only [Function.comp_apply, ofRealCLM_apply, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.id_apply, smul_eq_mul]
    }
    rw [h_comp]
    have h_v2 : DifferentiableAt ℝ (ofRealCLM ∘ v) x := ofRealCLM.differentiableAt.comp x hv
    rw [fderiv_comp x (I • ContinuousLinearMap.id ℝ ℂ).differentiableAt h_v2]
    rw [(I • ContinuousLinearMap.id ℝ ℂ).fderiv]
    congr 1
    rw [fderiv_comp x ofRealCLM.differentiableAt hv]
    rw [ofRealCLM.fderiv]
}

/--
  Theorem II.7: Let f = u + i*v where real-valued u and v are defined in an open subset G of ℂ,
  and assume u and v have continuous first partial derivatives and satisfy the Cauchy-Riemann equations.
  Then f is differentiable in G.
-/
theorem II_7 {G : Set ℂ} (hG : IsOpen G)
    (u v : ℂ → ℝ) (ux uy vx vy : ℂ → ℝ)
    (hu_x : ∀ z ∈ G, HasPartialDerivX_C_to_R_eps u (ux z) z)
    (hu_y : ∀ z ∈ G, HasPartialDerivY_C_to_R_eps u (uy z) z)
    (hv_x : ∀ z ∈ G, HasPartialDerivX_C_to_R_eps v (vx z) z)
    (hv_y : ∀ z ∈ G, HasPartialDerivY_C_to_R_eps v (vy z) z)
    (h_cont_ux : ContinuousOn ux G) (h_cont_uy : ContinuousOn uy G)
    (h_cont_vx : ContinuousOn vx G) (h_cont_vy : ContinuousOn vy G)
    (h_cr : ∀ z ∈ G, ux z = vy z ∧ uy z = -vx z)
    (f : ℂ → ℂ) (hf : ∀ z, f z = u z + I * v z) :
    ∀ z ∈ G, DifferentiableAt_eps f z := by {
  intro z hz
  rw [← differentiableAt_iff_eps]
  rw [differentiableAt_complex_iff_differentiableAt_real]
  have hu_deriv : HasFDerivAt u (ux z • reCLM + uy z • imCLM) z :=
    hasFDerivAt_of_hasPartialDeriv hG u ux uy hu_x hu_y h_cont_ux h_cont_uy z hz
  have hv_deriv : HasFDerivAt v (vx z • reCLM + vy z • imCLM) z :=
    hasFDerivAt_of_hasPartialDeriv hG v vx vy hv_x hv_y h_cont_vx h_cont_vy z hz
  have hu_diff : DifferentiableAt ℝ u z := hu_deriv.differentiableAt
  have hv_diff : DifferentiableAt ℝ v z := hv_deriv.differentiableAt
  have h_f_diff : DifferentiableAt ℝ f z := differentiableAt_real_of_parts hu_diff hv_diff hf
  refine ⟨h_f_diff, ?_⟩
  have h_fderiv_f : fderiv ℝ f z = ofRealCLM.comp (fderiv ℝ u z) + (I • ContinuousLinearMap.id ℝ ℂ).comp (ofRealCLM.comp (fderiv ℝ v z)) := by {
    exact fderiv_parts hu_diff hv_diff hf
  }
  have h_fderiv_u : fderiv ℝ u z = ux z • reCLM + uy z • imCLM := hu_deriv.fderiv
  have h_fderiv_v : fderiv ℝ v z = vx z • reCLM + vy z • imCLM := hv_deriv.fderiv
  rw [h_fderiv_f, h_fderiv_u, h_fderiv_v]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    reCLM_apply, imCLM_apply, ofRealCLM_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  simp only [I_re, I_im, one_re, one_im]
  rcases h_cr z hz with ⟨hux, huy⟩
  rw [hux, huy]
  simp
  have h_eval_I : I * (↑(vy z) + I * ↑(vx z)) = -↑(vx z) + I * ↑(vy z) := by {
    calc I * (↑(vy z) + I * ↑(vx z))
      _ = I * ↑(vy z) + (I * I) * ↑(vx z) := by ring
      _ = I * ↑(vy z) + (-1) * ↑(vx z) := by rw [I_mul_I]
      _ = -↑(vx z) + I * ↑(vy z) := by ring
  }
  rw [h_eval_I]
}

end Sarason.Ch2

end
