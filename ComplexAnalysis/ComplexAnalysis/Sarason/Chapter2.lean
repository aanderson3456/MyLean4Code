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
import Mathlib.Analysis.Calculus.Deriv.Star
import Mathlib.Analysis.SpecialFunctions.Complex.Arg
import ComplexAnalysis.Sarason.Definitions
/-!
# Sarason - Chapter 2: Complex Differentiation

Formalization of Section II of Donald Sarason's "Notes on Complex Function Theory".
Focus: Definition of the derivative, Cauchy-Riemann equations, and Differential Operators.

If you like this, credit Donald Sarason.  If you don't, blame Austin Anderson.

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
/--
  If a real-valued function u has continuous partial derivatives on an open set G,
  then u is Fréchet differentiable in G.
-/
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
/--
  If u and v are real-differentiable at x, then their complex combination f = u + I * v
  is also real-differentiable at x.
-/
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
/--
  Expresses the real Fréchet derivative of a complex-valued function f = u + I * v
  in terms of the real Fréchet derivatives of its real and imaginary parts u and v.
-/
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
  Theorem II.7:
  Let f = u + i*v be defined on an open set G in ℂ. Suppose that u and v have
  first partials in G.  If these partials are continuous and satisfy the CR equations
  at z₀ ∈ G, then f has a complex derivative at z₀.
-/

theorem II_7 {G : Set ℂ} (hG : IsOpen G)
    (u v : ℂ → ℝ) (ux uy vx vy : ℂ → ℝ)
    (hu_x : ∀ z ∈ G, HasPartialDerivX_C_to_R_eps u (ux z) z)
    (hu_y : ∀ z ∈ G, HasPartialDerivY_C_to_R_eps u (uy z) z)
    (hv_x : ∀ z ∈ G, HasPartialDerivX_C_to_R_eps v (vx z) z)
    (hv_y : ∀ z ∈ G, HasPartialDerivY_C_to_R_eps v (vy z) z)
    (h_cont_ux : ContinuousOn ux G) (h_cont_uy : ContinuousOn uy G)
    (h_cont_vx : ContinuousOn vx G) (h_cont_vy : ContinuousOn vy G)
    (z₀ : ℂ) (hz₀ : z₀ ∈ G)
    (h_cr : ux z₀ = vy z₀ ∧ uy z₀ = -vx z₀)
    (f : ℂ → ℂ) (hf : ∀ z, f z = u z + I * v z) :
    DifferentiableAt_eps f z₀ := by {
  rw [← differentiableAt_iff_eps]
  rw [differentiableAt_complex_iff_differentiableAt_real]
  have hu_deriv : HasFDerivAt u (ux z₀ • reCLM + uy z₀ • imCLM) z₀ :=
    hasFDerivAt_of_hasPartialDeriv hG u ux uy hu_x hu_y h_cont_ux h_cont_uy z₀ hz₀
  have hv_deriv : HasFDerivAt v (vx z₀ • reCLM + vy z₀ • imCLM) z₀ :=
    hasFDerivAt_of_hasPartialDeriv hG v vx vy hv_x hv_y h_cont_vx h_cont_vy z₀ hz₀
  have hu_diff : DifferentiableAt ℝ u z₀ := hu_deriv.differentiableAt
  have hv_diff : DifferentiableAt ℝ v z₀ := hv_deriv.differentiableAt
  have h_f_diff : DifferentiableAt ℝ f z₀ := differentiableAt_real_of_parts hu_diff hv_diff hf
  refine ⟨h_f_diff, ?_⟩
  have h_fderiv_f : fderiv ℝ f z₀ = ofRealCLM.comp (fderiv ℝ u z₀) + (I • ContinuousLinearMap.id ℝ ℂ).comp (ofRealCLM.comp (fderiv ℝ v z₀)) := by {
    exact fderiv_parts hu_diff hv_diff hf
  }
  have h_fderiv_u : fderiv ℝ u z₀ = ux z₀ • reCLM + uy z₀ • imCLM := hu_deriv.fderiv
  have h_fderiv_v : fderiv ℝ v z₀ = vx z₀ • reCLM + vy z₀ • imCLM := hv_deriv.fderiv
  rw [h_fderiv_f, h_fderiv_u, h_fderiv_v]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply,
    reCLM_apply, imCLM_apply, ofRealCLM_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  simp only [I_re, I_im, one_re, one_im]
  rcases h_cr with ⟨hux, huy⟩
  rw [hux, huy]
  simp
  have h_eval_I : I * (↑(vy z₀) + I * ↑(vx z₀)) = -↑(vx z₀) + I * ↑(vy z₀) := by {
    calc I * (↑(vy z₀) + I * ↑(vx z₀))
      _ = I * ↑(vy z₀) + (I * I) * ↑(vx z₀) := by ring
      _ = I * ↑(vy z₀) + (-1) * ↑(vx z₀) := by rw [I_mul_I]
      _ = -↑(vx z₀) + I * ↑(vy z₀) := by ring
  }
  rw [h_eval_I]
}
/--
  If f is complex-differentiable at z₀ with derivative f', then the real and imaginary
  parts of f have partial derivatives at z₀, given by:
  - (u_x, u_y) = (re f', -im f')
  - (v_x, v_y) = (im f', re f')
-/
theorem hasDerivAt_eps_imp_cauchy_riemann {f : ℂ → ℂ} {f' : ℂ} {z₀ : ℂ} (h : HasDerivAt_eps f f' z₀) :
    HasPartialDerivX_C_to_R_eps (fun z ↦ (f z).re) f'.re z₀ ∧
    HasPartialDerivY_C_to_R_eps (fun z ↦ (f z).re) (-f'.im) z₀ ∧
    HasPartialDerivX_C_to_R_eps (fun z ↦ (f z).im) f'.im z₀ ∧
    HasPartialDerivY_C_to_R_eps (fun z ↦ (f z).im) f'.re z₀ := by {
  rw [← hasDerivAt_iff_eps] at h
  have h_eq_point : ((z₀.re : ℂ) + (z₀.im : ℂ) * I) = z₀ := re_add_im z₀

  have h_gx : HasDerivAt (fun x : ℝ ↦ (x : ℂ) + (z₀.im : ℂ) * I) (1 : ℂ) z₀.re := by {
    have h_base : HasDerivAt (fun x : ℝ ↦ (x : ℂ)) 1 z₀.re := by {
      have h_eq : (fun x : ℝ ↦ (x : ℂ)) = ofRealCLM := by { ext x; rfl }
      rw [h_eq]
      have h_fderiv : HasFDerivAt ofRealCLM ofRealCLM z₀.re := ofRealCLM.hasFDerivAt
      rw [hasDerivAt_iff_hasFDerivAt]
      have h_clm_eq : ofRealCLM = ContinuousLinearMap.toSpanSingleton ℝ (1 : ℂ) := by {
        apply ContinuousLinearMap.ext
        intro r
        simp [ofRealCLM, ContinuousLinearMap.toSpanSingleton_apply]
      }
      rw [h_clm_eq] at h_fderiv ⊢
      exact h_fderiv
    }
    exact HasDerivAt.add_const ((z₀.im : ℂ) * I) h_base
  }

  have h_gy : HasDerivAt (fun y : ℝ ↦ (z₀.re : ℂ) + (y : ℂ) * I) I z₀.im := by {
    have h_base : HasDerivAt (fun y : ℝ ↦ (y : ℂ)) 1 z₀.im := by {
      have h_eq : (fun y : ℝ ↦ (y : ℂ)) = ofRealCLM := by { ext y; rfl }
      rw [h_eq]
      have h_fderiv : HasFDerivAt ofRealCLM ofRealCLM z₀.im := ofRealCLM.hasFDerivAt
      rw [hasDerivAt_iff_hasFDerivAt]
      have h_clm_eq : ofRealCLM = ContinuousLinearMap.toSpanSingleton ℝ (1 : ℂ) := by {
        apply ContinuousLinearMap.ext
        intro r
        simp [ofRealCLM, ContinuousLinearMap.toSpanSingleton_apply]
      }
      rw [h_clm_eq] at h_fderiv ⊢
      exact h_fderiv
    }
    have h_mul := HasDerivAt.const_mul I h_base
    have h_mul_simp : HasDerivAt (fun y : ℝ ↦ I * (y : ℂ)) I z₀.im := by {
      simpa using h_mul
    }
    have h_base_mul : HasDerivAt (fun y : ℝ ↦ (y : ℂ) * I) I z₀.im := by {
      have h_eq : (fun y : ℝ ↦ (y : ℂ) * I) = (fun y : ℝ ↦ I * (y : ℂ)) := by {
        ext y
        rw [mul_comm]
      }
      rw [h_eq]
      exact h_mul_simp
    }
    exact HasDerivAt.const_add (z₀.re : ℂ) h_base_mul
  }

  have h_fderiv_f : HasFDerivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) z₀ := h.complexToReal_fderiv
  have h_fderiv_f' : HasFDerivAt f (f' • (1 : ℂ →L[ℝ] ℂ)) ((z₀.re : ℂ) + (z₀.im : ℂ) * I) := by {
    rwa [h_eq_point]
  }

  have h_comp_x : HasFDerivAt (f ∘ fun x : ℝ ↦ (x : ℂ) + (z₀.im : ℂ) * I) ((f' • (1 : ℂ →L[ℝ] ℂ)).comp (ContinuousLinearMap.toSpanSingleton ℝ 1)) z₀.re := by {
    have h_fderiv_gx : HasFDerivAt (fun x : ℝ ↦ (x : ℂ) + (z₀.im : ℂ) * I) (ContinuousLinearMap.toSpanSingleton ℝ 1) z₀.re := h_gx.hasFDerivAt
    have h_comp := HasFDerivAt.comp z₀.re h_fderiv_f' h_fderiv_gx
    exact h_comp
  }

  have h_comp_y : HasFDerivAt (f ∘ fun y : ℝ ↦ (z₀.re : ℂ) + (y : ℂ) * I) ((f' • (1 : ℂ →L[ℝ] ℂ)).comp (ContinuousLinearMap.toSpanSingleton ℝ I)) z₀.im := by {
    have h_fderiv_gy : HasFDerivAt (fun y : ℝ ↦ (z₀.re : ℂ) + (y : ℂ) * I) (ContinuousLinearMap.toSpanSingleton ℝ I) z₀.im := h_gy.hasFDerivAt
    have h_comp := HasFDerivAt.comp z₀.im h_fderiv_f' h_fderiv_gy
    exact h_comp
  }

  have h_re_x : HasPartialDerivX_C_to_R_eps (fun z ↦ (f z).re) f'.re z₀ := by {
    rw [← hasPartialDerivX_iff_eps]
    have h_comp_re_x := HasFDerivAt.comp z₀.re (ContinuousLinearMap.hasFDerivAt reCLM : HasFDerivAt reCLM reCLM (f ((z₀.re : ℂ) + (z₀.im : ℂ) * I))) h_comp_x
    rw [hasDerivAt_iff_hasFDerivAt]
    have h_clm_eq : reCLM.comp ((f' • (1 : ℂ →L[ℝ] ℂ)).comp (ContinuousLinearMap.toSpanSingleton ℝ 1)) = ContinuousLinearMap.toSpanSingleton ℝ f'.re := by {
      apply ContinuousLinearMap.ext
      intro r
      simp [ContinuousLinearMap.toSpanSingleton_apply]
      rw [mul_comm]
    }
    rw [h_clm_eq] at h_comp_re_x
    exact h_comp_re_x
  }

  have h_re_y : HasPartialDerivY_C_to_R_eps (fun z ↦ (f z).re) (-f'.im) z₀ := by {
    rw [← hasPartialDerivY_iff_eps]
    have h_comp_re_y := HasFDerivAt.comp z₀.im (ContinuousLinearMap.hasFDerivAt reCLM : HasFDerivAt reCLM reCLM (f ((z₀.re : ℂ) + (z₀.im : ℂ) * I))) h_comp_y
    rw [hasDerivAt_iff_hasFDerivAt]
    have h_clm_eq : reCLM.comp ((f' • (1 : ℂ →L[ℝ] ℂ)).comp (ContinuousLinearMap.toSpanSingleton ℝ I)) = ContinuousLinearMap.toSpanSingleton ℝ (-f'.im) := by {
      apply ContinuousLinearMap.ext
      intro r
      simp [ContinuousLinearMap.toSpanSingleton_apply]
      rw [mul_comm]
    }
    rw [h_clm_eq] at h_comp_re_y
    exact h_comp_re_y
  }

  have h_im_x : HasPartialDerivX_C_to_R_eps (fun z ↦ (f z).im) f'.im z₀ := by {
    rw [← hasPartialDerivX_iff_eps]
    have h_comp_im_x := HasFDerivAt.comp z₀.re (ContinuousLinearMap.hasFDerivAt imCLM : HasFDerivAt imCLM imCLM (f ((z₀.re : ℂ) + (z₀.im : ℂ) * I))) h_comp_x
    rw [hasDerivAt_iff_hasFDerivAt]
    have h_clm_eq : imCLM.comp ((f' • (1 : ℂ →L[ℝ] ℂ)).comp (ContinuousLinearMap.toSpanSingleton ℝ 1)) = ContinuousLinearMap.toSpanSingleton ℝ f'.im := by {
      apply ContinuousLinearMap.ext
      intro r
      simp [ContinuousLinearMap.toSpanSingleton_apply]
      rw [mul_comm]
    }
    rw [h_clm_eq] at h_comp_im_x
    exact h_comp_im_x
  }

  have h_im_y : HasPartialDerivY_C_to_R_eps (fun z ↦ (f z).im) f'.re z₀ := by {
    rw [← hasPartialDerivY_iff_eps]
    have h_comp_im_y := HasFDerivAt.comp z₀.im (ContinuousLinearMap.hasFDerivAt imCLM : HasFDerivAt imCLM imCLM (f ((z₀.re : ℂ) + (z₀.im : ℂ) * I))) h_comp_y
    rw [hasDerivAt_iff_hasFDerivAt]
    have h_clm_eq : imCLM.comp ((f' • (1 : ℂ →L[ℝ] ℂ)).comp (ContinuousLinearMap.toSpanSingleton ℝ I)) = ContinuousLinearMap.toSpanSingleton ℝ f'.re := by {
      apply ContinuousLinearMap.ext
      intro r
      simp [ContinuousLinearMap.toSpanSingleton_apply]
      rw [mul_comm]
    }
    rw [h_clm_eq] at h_comp_im_y
    exact h_comp_im_y
  }

  exact ⟨h_re_x, h_re_y, h_im_x, h_im_y⟩
}
/--
  If f is complex-differentiable at z₀, then the partial derivatives of its real
  and imaginary parts exist at z₀ and satisfy the Cauchy-Riemann equations:
  u_x = v_y and u_y = -v_x.
-/
theorem cauchy_riemann_equations_of_differentiable {f : ℂ → ℂ} {z₀ : ℂ} (h : DifferentiableAt_eps f z₀) :
    ∃ ux uy vx vy : ℝ,
      HasPartialDerivX_C_to_R_eps (fun z ↦ (f z).re) ux z₀ ∧
      HasPartialDerivY_C_to_R_eps (fun z ↦ (f z).re) uy z₀ ∧
      HasPartialDerivX_C_to_R_eps (fun z ↦ (f z).im) vx z₀ ∧
      HasPartialDerivY_C_to_R_eps (fun z ↦ (f z).im) vy z₀ ∧
      ux = vy ∧ uy = -vx := by {
  rcases h with ⟨f', hf'⟩
  have h_cr := hasDerivAt_eps_imp_cauchy_riemann hf'
  exact ⟨f'.re, -f'.im, f'.im, f'.re, h_cr.1, h_cr.2.1, h_cr.2.2.1, h_cr.2.2.2, rfl, by ring⟩
}

/-
  II.8 Sarason notes that complex differentiability,
  a.k.a. being holomorphic, is extra structure
  compared to differentiability of the real and imaginary parts separately
  in the ℝ^2 sense.
  Continuity of first partials is an extra requirement
  to obtain complex differentiability from differentiability
  in the ℝ^2 sense given the Cauchy-Riemann equations hold.
  He hints at future results showing holomorphic functions
  are in fact infinitely differentiable, not the case for
  differentiable functions in the ℝ^2 sense.
-/

/-- If the derivative of a holomorphic function is everywhere zero, the function is constant. -/
theorem exerciseII_8_1a (f : ℂ → ℂ) (hf : ∀ z, DifferentiableAt_eps f z) (hf' : ∀ z, deriv_eps f z (hf z) = 0) (z w : ℂ) : f z = f w := by {
  have h_diff : Differentiable ℂ f := by {
    intro x
    exact (differentiableAt_iff_eps f x).mpr (hf x)
  }
  have h_deriv_zero : ∀ z, deriv f z = 0 := by {
    intro x
    rw [deriv_eq_deriv_eps f x (hf x)]
    exact hf' x
  }
  exact is_const_of_deriv_eq_zero h_diff h_deriv_zero z w
}

/-- If the x-partial derivative of the constant zero function is c, then c = 0. -/
theorem partial_deriv_zero_imp_zero_x (c : ℝ) (z₀ : ℂ) (h : HasPartialDerivX_C_to_R_eps (fun _ => 0) c z₀) : c = 0 := by {
  unfold HasPartialDerivX_C_to_R_eps at h
  by_contra hc
  have hc_pos : 0 < |c| := abs_pos.mpr hc
  rcases h |c| hc_pos with ⟨δ, hδ_pos, hδ⟩
  have h_x : ∃ x : ℝ, 0 < |x - z₀.re| ∧ |x - z₀.re| < δ := by {
    use z₀.re + δ / 2
    have h_sub : (z₀.re + δ / 2) - z₀.re = δ / 2 := by ring
    rw [h_sub]
    have h1 : 0 < δ / 2 := half_pos hδ_pos
    have h2 : |δ / 2| = δ / 2 := abs_of_pos h1
    rw [h2]
    exact ⟨h1, by linarith⟩
  }
  rcases h_x with ⟨x, hx⟩
  have h_abs := hδ x hx
  simp at h_abs
}

/-- If the y-partial derivative of the constant zero function is c, then c = 0. -/
theorem partial_deriv_zero_imp_zero_y (c : ℝ) (z₀ : ℂ) (h : HasPartialDerivY_C_to_R_eps (fun _ => 0) c z₀) : c = 0 := by {
  unfold HasPartialDerivY_C_to_R_eps at h
  by_contra hc
  have hc_pos : 0 < |c| := abs_pos.mpr hc
  rcases h |c| hc_pos with ⟨δ, hδ_pos, hδ⟩
  have h_y : ∃ y : ℝ, 0 < |y - z₀.im| ∧ |y - z₀.im| < δ := by {
    use z₀.im + δ / 2
    have h_sub : (z₀.im + δ / 2) - z₀.im = δ / 2 := by ring
    rw [h_sub]
    have h1 : 0 < δ / 2 := half_pos hδ_pos
    have h2 : |δ / 2| = δ / 2 := abs_of_pos h1
    rw [h2]
    exact ⟨h1, by linarith⟩
  }
  rcases h_y with ⟨y, hy⟩
  have h_abs := hδ y hy
  simp at h_abs
}

/-- If a holomorphic function is strictly real-valued (its imaginary part is zero), it is constant. -/
theorem exerciseII_8_1b (f : ℂ → ℂ) (hf : ∀ z, DifferentiableAt_eps f z)
    (h_real : ∀ z, (f z).im = 0) (z w : ℂ) : f z = f w := by {
  have h_deriv_zero : ∀ x, deriv_eps f x (hf x) = 0 := by {
    intro x
    set f' := deriv_eps f x (hf x)
    have h_deriv : HasDerivAt_eps f f' x := by {
      have h1 := Classical.choose_spec (hf x)
      exact h1
    }
    have h_cr := hasDerivAt_eps_imp_cauchy_riemann h_deriv
    rcases h_cr with ⟨_, _, hvx, hvy⟩

    have h_im_zero : (fun z ↦ (f z).im) = (fun z ↦ 0) := by {
      ext z
      exact h_real z
    }
    rw [h_im_zero] at hvx hvy

    have h_f_im : f'.im = 0 := partial_deriv_zero_imp_zero_x f'.im x hvx
    have h_f_re : f'.re = 0 := partial_deriv_zero_imp_zero_y f'.re x hvy

    apply Complex.ext
    · exact h_f_re
    · exact h_f_im
  }
  exact exerciseII_8_1a f hf h_deriv_zero z w
}

/-- If the modulus of a holomorphic function is constant, the function is constant. -/
theorem exerciseII_8_1c (f : ℂ → ℂ) (hf : ∀ z, DifferentiableAt_eps f z)
    (h_norm : ∀ z w, normSq (f z) = normSq (f w)) (z w : ℂ) : f z = f w := by {
  have h_diff : Differentiable ℂ f := by {
    intro x
    exact (differentiableAt_iff_eps f x).mpr (hf x)
  }
  by_cases hf_zero : f z = 0
  · have h1 : normSq (f z) = 0 := by rw [hf_zero, normSq_zero]
    have h2 : normSq (f w) = 0 := by rw [← h_norm z w, h1]
    have h3 : f w = 0 := normSq_eq_zero.mp h2
    rw [hf_zero, h3]
  · have h1 : normSq (f z) ≠ 0 := mt normSq_eq_zero.mp hf_zero
    set c := normSq (f z)
    have hc : ∀ x, normSq (f x) = c := fun x ↦ h_norm x z

    have h_f_ne_zero : ∀ x, f x ≠ 0 := by {
      intro x h_fx
      have h2 : normSq (f x) = 0 := by rw [h_fx, normSq_zero]
      rw [hc x] at h2
      exact h1 h2
    }

    set g := fun x ↦ (c : ℂ) * (f x)⁻¹
    have hg_diff : Differentiable ℂ g := by {
      apply Differentiable.const_mul
      exact Differentiable.inv h_diff h_f_ne_zero
    }

    have h_conj : ∀ x, star (f x) = g x := by {
      intro x
      have h_normSq : f x * star (f x) = (normSq (f x) : ℂ) := by {
        exact mul_conj (f x)
      }
      rw [hc x] at h_normSq
      have h_calc : star (f x) = (c : ℂ) * (f x)⁻¹ := by {
        calc star (f x) = star (f x) * (f x * (f x)⁻¹) := by {
               rw [mul_inv_cancel₀ (h_f_ne_zero x), mul_one]
             }
             _ = star (f x) * f x * (f x)⁻¹ := by rw [mul_assoc]
             _ = f x * star (f x) * (f x)⁻¹ := by rw [mul_comm (star (f x)) (f x)]
             _ = (c : ℂ) * (f x)⁻¹ := by rw [h_normSq]
      }
      exact h_calc
    }

    have h_star_diff : Differentiable ℂ (fun x ↦ star (f x)) := by {
      have h_eq : (fun x ↦ star (f x)) = g := funext h_conj
      rw [h_eq]
      exact hg_diff
    }

    have h_re_diff : Differentiable ℂ (fun x ↦ ((f x).re : ℂ)) := by {
      have h_eq : (fun x ↦ ((f x).re : ℂ)) = (fun x ↦ (f x + star (f x)) * (2 : ℂ)⁻¹) := by {
        ext x
        have h_add : f x + star (f x) = ↑(2 * (f x).re) := Complex.add_conj (f x)
        apply Eq.symm
        calc (f x + star (f x)) * (2 : ℂ)⁻¹ = (↑(2 * (f x).re) : ℂ) * (2 : ℂ)⁻¹ := by rw [h_add]
        _ = (2 * ↑(f x).re : ℂ) * (2 : ℂ)⁻¹ := by push_cast; rfl
        _ = ↑(f x).re * (2 * 2⁻¹) := by ring
        _ = ↑(f x).re * 1 := by rw [mul_inv_cancel₀ (by norm_num)]
        _ = ↑(f x).re := by ring
      }
      rw [h_eq]
      apply Differentiable.mul_const
      exact Differentiable.add h_diff h_star_diff
    }

    have h_re_const : ∀ x y, (f x).re = (f y).re := by {
      intro x y
      have h_re_eps : ∀ v, DifferentiableAt_eps (fun x ↦ ((f x).re : ℂ)) v := by {
        intro v
        exact (differentiableAt_iff_eps _ v).mp (h_re_diff v)
      }
      have h_im_zero : ∀ v, ((fun x ↦ ((f x).re : ℂ)) v).im = 0 := by {
        intro v
        exact Complex.ofReal_im (f v).re
      }
      have h_eq_C := exerciseII_8_1b (fun x ↦ ((f x).re : ℂ)) h_re_eps h_im_zero x y
      exact ofReal_inj.mp h_eq_C
    }

    have h_im_diff : Differentiable ℂ (fun x ↦ ((f x).im : ℂ)) := by {
      have h_eq : (fun x ↦ ((f x).im : ℂ)) = (fun x ↦ (f x - star (f x)) * (2 * I)⁻¹) := by {
        ext x
        have h_sub : f x - star (f x) = ↑(2 * (f x).im) * I := Complex.sub_conj (f x)
        apply Eq.symm
        calc (f x - star (f x)) * (2 * I)⁻¹ = (↑(2 * (f x).im) * I : ℂ) * (2 * I)⁻¹ := by rw [h_sub]
        _ = (2 * ↑(f x).im * I : ℂ) * (2 * I)⁻¹ := by push_cast; rfl
        _ = ↑(f x).im * (2 * I * (2 * I)⁻¹) := by ring
        _ = ↑(f x).im * 1 := by rw [mul_inv_cancel₀ (by norm_num)]
        _ = ↑(f x).im := by ring
      }
      rw [h_eq]
      apply Differentiable.mul_const
      exact Differentiable.sub h_diff h_star_diff
    }

    have h_im_const : ∀ x y, (f x).im = (f y).im := by {
      intro x y
      have h_im_eps : ∀ v, DifferentiableAt_eps (fun x ↦ ((f x).im : ℂ)) v := by {
        intro v
        exact (differentiableAt_iff_eps _ v).mp (h_im_diff v)
      }
      have h_im_zero : ∀ v, ((fun x ↦ ((f x).im : ℂ)) v).im = 0 := by {
        intro v
        exact Complex.ofReal_im (f v).im
      }
      have h_eq_C := exerciseII_8_1b (fun x ↦ ((f x).im : ℂ)) h_im_eps h_im_zero x y
      exact ofReal_inj.mp h_eq_C
    }

    apply Complex.ext
    · exact h_re_const z w
    · exact h_im_const z w
}

/-- If the argument of a holomorphic function is constant, the function is constant. -/
theorem exerciseII_8_1d (f : ℂ → ℂ) (hf : ∀ z, DifferentiableAt_eps f z)
    (h_arg : ∀ z w, arg (f z) = arg (f w)) (z w : ℂ) : f z = f w := by {
  have h_diff : Differentiable ℂ f := by {
    intro x
    exact (differentiableAt_iff_eps f x).mpr (hf x)
  }
  set c := arg (f z)
  have hc : ∀ x, arg (f x) = c := fun x ↦ h_arg x z

  set g := fun x ↦ f x * exp (-I * (c : ℂ))
  have hg_diff : Differentiable ℂ g := by {
    apply Differentiable.mul_const h_diff
  }

  have hg_eps : ∀ v, DifferentiableAt_eps g v := by {
    intro v
    exact (differentiableAt_iff_eps g v).mp (hg_diff v)
  }

  have hg_real : ∀ x, (g x).im = 0 := by {
    intro x
    have h_f : f x = (‖f x‖ : ℂ) * exp ((arg (f x) : ℂ) * I) := by {
      exact (norm_mul_exp_arg_mul_I (f x)).symm
    }
    have h_g : g x = (‖f x‖ : ℂ) := by {
      have h_g_def : g x = f x * exp (-I * (c : ℂ)) := rfl
      rw [h_g_def]
      nth_rewrite 1 [h_f]
      calc ((‖f x‖ : ℂ) * exp ((arg (f x) : ℂ) * I)) * exp (-I * (c : ℂ))
        = (‖f x‖ : ℂ) * (exp (c * I) * exp (-I * c)) := by {
        rw [hc x]
        ring
      }
      _ = (‖f x‖ : ℂ) * exp (c * I - I * c) := by rw [← exp_add]; ring_nf
      _ = (‖f x‖ : ℂ) * exp 0 := by ring_nf
      _ = (‖f x‖ : ℂ) * 1 := by rw [exp_zero]
      _ = (‖f x‖ : ℂ) := by ring
    }
    rw [h_g]
    simp
  }

  have hg_const := exerciseII_8_1b g hg_eps hg_real z w

  have h_f_eq : f z = g z * exp (I * (c : ℂ)) := by {
    have h : g z * exp (I * (c : ℂ)) = f z := by {
      calc g z * exp (I * (c : ℂ)) = (f z * exp (-I * (c : ℂ))) * exp (I * (c : ℂ)) := rfl
      _ = f z * (exp (-I * c) * exp (I * c)) := by ring
      _ = f z * exp (-I * c + I * c) := by rw [← exp_add]
      _ = f z * exp 0 := by ring_nf
      _ = f z * 1 := by rw [exp_zero]
      _ = f z := by ring
    }
    exact h.symm
  }

  have h_w_eq : f w = g w * exp (I * (c : ℂ)) := by {
    have h : g w * exp (I * (c : ℂ)) = f w := by {
      calc g w * exp (I * (c : ℂ)) = (f w * exp (-I * (c : ℂ))) * exp (I * (c : ℂ)) := rfl
      _ = f w * (exp (-I * c) * exp (I * c)) := by ring
      _ = f w * exp (-I * c + I * c) := by rw [← exp_add]
      _ = f w * exp 0 := by ring_nf
      _ = f w * 1 := by rw [exp_zero]
      _ = f w := by ring
    }
    exact h.symm
  }

  rw [h_f_eq, h_w_eq, hg_const]
}

/-- If f is differentiable at z, then z ↦ star (f (star z)) is differentiable at star z. -/
theorem exerciseII_8_2 (f : ℂ → ℂ) (z : ℂ) (hf : DifferentiableAt_eps f z) :
    DifferentiableAt_eps (fun z ↦ star (f (star z))) (star z) := by {
  rw [← differentiableAt_iff_eps] at hf ⊢
  have h_comp : (fun z ↦ star (f (star z))) = star ∘ f ∘ star := rfl
  rw [h_comp]
  exact hf.star_conj
}

/-- If f is holomorphic on G, then z ↦ star (f (star z)) is holomorphic on G* = star '' G. -/
theorem exerciseII_8_2_domain (G : Set ℂ) (f : ℂ → ℂ) (hf : ∀ z ∈ G, DifferentiableAt_eps f z) :
    ∀ w ∈ star '' G, DifferentiableAt_eps (fun z ↦ star (f (star z))) w := by {
  rintro w ⟨z, hz, rfl⟩
  exact exerciseII_8_2 f z (hf z hz)
}


/-
  §II.9 Curves and their directions.
-/

/-- A continuous path in the complex plane ℂ connecting x to y. -/
def path_in_C (x y : ℂ) : Type := Path x y

/-- Velocity / derivative of a path γ : path_in_C x y at parameter time t ∈ ℝ. -/
noncomputable def pathDeriv {x y : ℂ} (γ : path_in_C x y) (t : ℝ) : ℂ :=
  deriv γ.extend t

/-- The direction of a path γ at time t is the argument of its derivative. -/
noncomputable def pathDirection {x y : ℂ} (γ : path_in_C x y) (t : ℝ) : ℝ :=
  arg (pathDeriv γ t)

/-- The angle between two paths γ₁ and γ₂ at times t₁ and t₂ is the difference of their directions. -/
noncomputable def pathAngle {x₁ y₁ x₂ y₂ : ℂ} (γ₁ : path_in_C x₁ y₁) (t₁ : ℝ) (γ₂ : path_in_C x₂ y₂) (t₂ : ℝ) : ℝ :=
  pathDirection γ₂ t₂ - pathDirection γ₁ t₁

/--
  The angle between two paths is equal to the argument of the product of the second path's derivative
  and the conjugate of the first path's derivative, modulo 2π.
  We prove this equality here assuming the angle difference stays within the principal branch bounds.
-/
theorem pathAngle_eq_arg_mul_conj {x₁ y₁ x₂ y₂ : ℂ}
    (γ₁ : path_in_C x₁ y₁) (t₁ : ℝ) (γ₂ : path_in_C x₂ y₂) (t₂ : ℝ)
    (h1 : pathDeriv γ₁ t₁ ≠ 0)
    (h2 : pathDeriv γ₂ t₂ ≠ 0)
    (h3 : arg (pathDeriv γ₁ t₁) ≠ Real.pi)
    (h_bounds : arg (pathDeriv γ₂ t₂) - arg (pathDeriv γ₁ t₁) ∈ Set.Ioc (-Real.pi) Real.pi) :
    pathAngle γ₁ t₁ γ₂ t₂ = arg (pathDeriv γ₂ t₂ * star (pathDeriv γ₁ t₁)) := by {
  unfold pathAngle pathDirection
  have h_conj : arg (star (pathDeriv γ₁ t₁)) = - arg (pathDeriv γ₁ t₁) := by {
    have h_conj' := arg_conj (pathDeriv γ₁ t₁)
    rw [if_neg h3] at h_conj'
    exact h_conj'
  }
  have h_star_ne_zero : star (pathDeriv γ₁ t₁) ≠ 0 := by {
    exact star_ne_zero.mpr h1
  }
  have h_bounds_add : arg (pathDeriv γ₂ t₂) + arg (star (pathDeriv γ₁ t₁)) ∈ Set.Ioc (-Real.pi) Real.pi := by {
    rw [h_conj]
    exact h_bounds
  }
  have h_mul := arg_mul h2 h_star_ne_zero h_bounds_add
  rw [h_conj] at h_mul
  have h_sub : arg (pathDeriv γ₂ t₂) + -arg (pathDeriv γ₁ t₁) = arg (pathDeriv γ₂ t₂) - arg (pathDeriv γ₁ t₁) := by ring
  rw [h_sub] at h_mul
  exact h_mul.symm
}


/--
  If f is holomorphic (or just differentiable) at z₀ = γ(t₀), and γ is a path,
  then the composition f ∘ γ is differentiable at t₀ with derivative f'(z₀) * γ'(t₀).
-/
theorem path_comp_deriv {x y : ℂ} (γ : path_in_C x y) (t₀ : ℝ)
    (f : ℂ → ℂ) (z₀ : ℂ) (f' : ℂ) (h_z₀ : γ.extend t₀ = z₀)
    (hf : HasDerivAt_eps f f' z₀)
    (hγ : HasDerivAt_R_to_C_eps γ.extend (pathDeriv γ t₀) t₀) :
    HasDerivAt_R_to_C_eps (f ∘ γ.extend) (f' * pathDeriv γ t₀) t₀ := by {
  rw [← hasDerivAt_iff_eps] at hf
  rw [← hasDerivAt_R_to_C_iff_eps] at hγ ⊢
  subst h_z₀
  have hf_real := hf.complexToReal_fderiv
  have hγ_real := hγ.hasFDerivAt
  have h_comp := HasFDerivAt.comp t₀ hf_real hγ_real
  rw [hasDerivAt_iff_hasFDerivAt]
  have h_eq : (f' • (1 : ℂ →L[ℝ] ℂ)).comp (ContinuousLinearMap.toSpanSingleton ℝ (pathDeriv γ t₀)) =
      ContinuousLinearMap.toSpanSingleton ℝ (f' * pathDeriv γ t₀) := by {
    apply ContinuousLinearMap.ext
    intro r
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.toSpanSingleton_apply,
      ContinuousLinearMap.one_apply, Complex.real_smul]
    ring
  }
  rw [h_eq] at h_comp
  exact h_comp
}

lemma HasDerivAt_R_to_C_eps_unique {f : ℝ → ℂ} {d₁ d₂ : ℂ} {t₀ : ℝ}
    (h₁ : HasDerivAt_R_to_C_eps f d₁ t₀) (h₂ : HasDerivAt_R_to_C_eps f d₂ t₀) : d₁ = d₂ := by {
  rw [← hasDerivAt_R_to_C_iff_eps] at h₁ h₂
  exact h₁.unique h₂
}

/-- A function is conformal at z₀ if it preserves angles between any two regular paths intersecting at z₀
    (and mapped to regular paths). -/
def conformal (f : ℂ → ℂ) (z₀ : ℂ) : Prop :=
  ∀ (x₁ y₁ x₂ y₂ : ℂ) (γ₁ : path_in_C x₁ y₁) (t₁ : ℝ) (γ₂ : path_in_C x₂ y₂) (t₂ : ℝ) (d₁ d₂ : ℂ),
    γ₁.extend t₁ = z₀ →
    γ₂.extend t₂ = z₀ →
    HasDerivAt_R_to_C_eps γ₁.extend (pathDeriv γ₁ t₁) t₁ →
    HasDerivAt_R_to_C_eps γ₂.extend (pathDeriv γ₂ t₂) t₂ →
    pathDeriv γ₁ t₁ ≠ 0 →
    pathDeriv γ₂ t₂ ≠ 0 →
    -- HasDerivAt_R_to_C_eps f f' t says f' is the derivative of f at t.
    HasDerivAt_R_to_C_eps (f ∘ γ₁.extend) d₁ t₁ →
    HasDerivAt_R_to_C_eps (f ∘ γ₂.extend) d₂ t₂ →
    d₁ ≠ 0 →
    d₂ ≠ 0 →
    arg d₂ - arg d₁ = pathAngle γ₁ t₁ γ₂ t₂

/--
  §II.11 Angle preservation at a point.  CONFORMALITY.
  If f is holomorphic at z₀ with non-zero derivative, then it preserves angles between regular paths intersecting at z₀.
-/
theorem conformality_at_point (f : ℂ → ℂ) (z₀ : ℂ) (f' : ℂ)
    (hf : HasDerivAt_eps f f' z₀)
    (_ : f' ≠ 0)
    (h_arg : ∀ {x y} (γ : path_in_C x y) t, γ.extend t = z₀ → HasDerivAt_R_to_C_eps γ.extend (pathDeriv γ t) t → pathDeriv γ t ≠ 0 → arg (f' * pathDeriv γ t) = arg f' + arg (pathDeriv γ t)) :
    conformal f z₀ := by {
  unfold conformal pathAngle pathDirection
  intro x₁ y₁ x₂ y₂ γ₁ t₁ γ₂ t₂ d₁ d₂ hz₁ hz₂ hγ₁ hγ₂ hreg₁ hreg₂ hd₁ hd₂ hd₁_ne hd₂_ne
  have hd₁_comp := path_comp_deriv γ₁ t₁ f z₀ f' hz₁ hf hγ₁
  have hd₂_comp := path_comp_deriv γ₂ t₂ f z₀ f' hz₂ hf hγ₂
  have heq₁ := HasDerivAt_R_to_C_eps_unique hd₁ hd₁_comp
  have heq₂ := HasDerivAt_R_to_C_eps_unique hd₂ hd₂_comp
  subst heq₁
  subst heq₂
  rw [h_arg γ₁ t₁ hz₁ hγ₁ hreg₁, h_arg γ₂ t₂ hz₂ hγ₂ hreg₂]
  ring
}

/--
  §II.11 Angle preservation on a domain G.
  If f is holomorphic on G with non-zero derivative, then it preserves angles between regular paths intersecting in G.
-/
theorem conformality_on_domain
    (G : Set ℂ)
    (f : ℂ → ℂ) (z₀ : ℂ)
    (h_z₀ : z₀ ∈ G)
    (hf_holom : HolomorphicOn_eps f G)
    (hf_ne : deriv f z₀ ≠ 0)
    (h_arg : ∀ {x y} (γ : path_in_C x y) t, γ.extend t = z₀ → HasDerivAt_R_to_C_eps γ.extend (pathDeriv γ t) t → pathDeriv γ t ≠ 0 → arg (deriv f z₀ * pathDeriv γ t) = arg (deriv f z₀) + arg (pathDeriv γ t)) :
    conformal f z₀ := by {
  have hf_diff : DifferentiableAt_eps f z₀ := hf_holom z₀ h_z₀
  have hf_deriv : HasDerivAt_eps f (deriv f z₀) z₀ := by {
    rw [← hasDerivAt_iff_eps]
    rw [← differentiableAt_iff_eps] at hf_diff
    exact hf_diff.hasDerivAt
  }
  exact conformality_at_point f z₀ (deriv f z₀) hf_deriv hf_ne h_arg
}

end Sarason.Ch2

noncomputable section

namespace Sarason.Ch2

/--
  §II.12 Conformal implies Holomorphic.
  If a map preserves angles, it is holomorphic. We build this up by first analyzing real-linear maps on ℂ.

  Any real-linear map on ℂ can be written in the form f(z) = a * z + b * star z
-/
lemma real_linear_eq_z_add_conj (f : ℂ →L[ℝ] ℂ) :
    ∃ a b : ℂ, ∀ z, f z = a * z + b * star z := by {
  use (f 1 - I * f I) / 2
  use (f 1 + I * f I) / 2
  intro z
  have h1 : f z = f ((z.re : ℝ) • (1 : ℂ) + (z.im : ℝ) • I) := by {
    congr 1
    apply Complex.ext
    · simp
    · simp
  }
  rw [f.map_add, f.map_smul, f.map_smul] at h1
  have h2 : (z.re : ℝ) • f 1 = (z.re : ℂ) * f 1 := rfl
  have h3 : (z.im : ℝ) • f I = (z.im : ℂ) * f I := rfl
  rw [h2, h3] at h1
  have hz : z = (z.re : ℂ) + (z.im : ℂ) * I := by exact (Complex.re_add_im z).symm
  have hs : star z = (z.re : ℂ) - (z.im : ℂ) * I := by {
    apply Complex.ext
    · simp
    · simp
  }
  calc f z = (z.re : ℂ) * f 1 + (z.im : ℂ) * f I := h1
    _ = (z.re : ℂ) * f 1 - (z.im : ℂ) * f I * (-1) := by ring
    _ = (z.re : ℂ) * f 1 - (z.im : ℂ) * f I * (I ^ 2) := by rw [Complex.I_sq]
    _ = (f 1 - I * f I) / 2 * ((z.re : ℂ) + (z.im : ℂ) * I) + (f 1 + I * f I) / 2 * ((z.re : ℂ) - (z.im : ℂ) * I) := by ring
    _ = (f 1 - I * f I) / 2 * z + (f 1 + I * f I) / 2 * star z := by {
      rw [←hz, ←hs]
    }
}

lemma conformal_linear_case_add_zero (a b : ℂ)
    (h_conformal : ∀ v₁ v₂ : ℂ, v₁ ≠ 0 → v₂ ≠ 0 →
      a * v₁ + b * star v₁ ≠ 0 → a * v₂ + b * star v₂ ≠ 0 →
      arg (a * v₂ + b * star v₂) - arg (a * v₁ + b * star v₁) = arg v₂ - arg v₁)
    (hab : a + b = 0) : b = 0 := by {
  have hb : b = -a := by {
    calc b = a + b - a := by ring
      _ = 0 - a := by rw [hab]
      _ = -a := by ring
  }
  by_cases ha : a = 0
  · rw [ha, neg_zero] at hb
    exact hb
  · have h1 : I ≠ 0 := I_ne_zero
    have h2 : 1 + I ≠ 0 := by {
      intro h
      have h_re : (1 + I : ℂ).re = 0 := by rw [h]; rfl
      simp at h_re
    }
    have hf1 : a * I + b * star I = 2 * a * I := by {
      rw [hb]
      apply Complex.ext <;> simp <;> ring
    }
    have hf2 : a * (1 + I) + b * star (1 + I) = 2 * a * I := by {
      rw [hb]
      apply Complex.ext <;> simp <;> ring
    }
    have hf1_ne : a * I + b * star I ≠ 0 := by {
      rw [hf1]
      intro h
      cases mul_eq_zero.mp h with
      | inl h_2a =>
        cases mul_eq_zero.mp h_2a with
        | inl h2 => norm_num at h2
        | inr ha2 => exact ha ha2
      | inr h_I => exact I_ne_zero h_I
    }
    have h_arg := h_conformal I (1 + I) h1 h2 hf1_ne (by { rw [hf2, ← hf1]; exact hf1_ne })
    rw [hf1, hf2] at h_arg
    simp at h_arg
    have h_arg_eq : arg (1 + I) = arg I := by {
      rw [arg_I]
      exact sub_eq_zero.mp h_arg.symm
    }
    have h_c := (arg_eq_arg_iff h2 h1).mp h_arg_eq
    have h_re : (((‖I‖:ℂ) / (‖1 + I‖:ℂ)) * (1 + I)).re = I.re := congrArg re h_c
    have h_c_real : (((‖I‖:ℂ) / (‖1 + I‖:ℂ))).im = 0 := by simp
    have h_c_re : (((‖I‖:ℂ) / (‖1 + I‖:ℂ))).re = ‖I‖ / ‖1 + I‖ := by simp
    have h_re2 : ‖I‖ / ‖1 + I‖ * 1 = 0 := by {
      calc ‖I‖ / ‖1 + I‖ * 1 = (((‖I‖:ℂ) / (‖1 + I‖:ℂ))).re * (1 + I : ℂ).re - (((‖I‖:ℂ) / (‖1 + I‖:ℂ))).im * (1 + I : ℂ).im := by simp
        _ = (((‖I‖:ℂ) / (‖1 + I‖:ℂ)) * (1 + I)).re := by simp [mul_re]
        _ = I.re := h_re
        _ = 0 := rfl
    }
    rw [mul_one] at h_re2
    have h_norm_I : ‖I‖ = 1 := norm_I
    rw [h_norm_I] at h_re2
    have h_norm_zero : (1 : ℝ) = 0 := by {
      have hh : (1 : ℝ) / ‖1 + I‖ * ‖1 + I‖ = 0 * ‖1 + I‖ := by rw [h_re2]
      rw [zero_mul] at hh
      have h_cancel : (1 : ℝ) / ‖1 + I‖ * ‖1 + I‖ = 1 := by {
        apply div_mul_cancel₀
        intro h
        have h_eq_zero : 1 + I = 0 := norm_eq_zero.mp h
        exact h2 h_eq_zero
      }
      rw [h_cancel] at hh
      exact hh
    }
    norm_num at h_norm_zero
}

lemma conformal_linear_helper (a b v : ℂ)
    (h_conformal : ∀ v₁ v₂ : ℂ, v₁ ≠ 0 → v₂ ≠ 0 →
      a * v₁ + b * star v₁ ≠ 0 → a * v₂ + b * star v₂ ≠ 0 →
      arg (a * v₂ + b * star v₂) - arg (a * v₁ + b * star v₁) = arg v₂ - arg v₁)
    (hab : a + b ≠ 0)
    (hv_ne : v ≠ 0)
    (hfv_ne : a * v + b * star v ≠ 0) :
    ∃ c : ℝ, (c : ℂ) * (a + b) = a + b * (star v / v) := by {
  have h1_ne : (1 : ℂ) ≠ 0 := one_ne_zero
  have hf1_ne : a * 1 + b * star 1 ≠ 0 := by {
    simp [hab]
  }
  have h_arg := h_conformal 1 v h1_ne hv_ne hf1_ne hfv_ne
  simp at h_arg
  have eq1 : a * v + b * star v = ‖a * v + b * star v‖ * exp (arg (a * v + b * star v) * I) := (norm_mul_exp_arg_mul_I _).symm
  have eq2 : exp (arg (a * v + b * star v) * I) = exp ((arg v : ℂ) * I) * exp ((arg (a + b) : ℂ) * I) := by {
    have h_eq : arg (a * v + b * star v) = arg v + arg (a + b) := eq_add_of_sub_eq h_arg
    rw [h_eq]
    push_cast
    rw [add_mul, exp_add]
  }
  rw [eq2] at eq1
  have eq3 : exp (arg v * I) = v / ‖v‖ := by {
    have h := norm_mul_exp_arg_mul_I v
    have h_div : exp (arg v * I) = v / ‖v‖ := by {
      calc exp (arg v * I) = (‖v‖ : ℂ)⁻¹ * (‖v‖ * exp (arg v * I)) := by {
             rw [← mul_assoc, inv_mul_cancel₀, one_mul]
             intro hh
             have hh2 : ‖v‖ = 0 := by exact_mod_cast hh
             exact hv_ne (norm_eq_zero.mp hh2)
           }
        _ = (‖v‖ : ℂ)⁻¹ * v := by rw [h]
        _ = v / ‖v‖ := by ring
    }
    exact h_div
  }
  have eq4 : exp (arg (a + b) * I) = (a + b) / ‖a + b‖ := by {
    have h := norm_mul_exp_arg_mul_I (a + b)
    have h_div : exp (arg (a + b) * I) = (a + b) / ‖a + b‖ := by {
      calc exp (arg (a + b) * I) = (‖a + b‖ : ℂ)⁻¹ * (‖a + b‖ * exp (arg (a + b) * I)) := by {
             rw [← mul_assoc, inv_mul_cancel₀, one_mul]
             intro hh
             have hh2 : ‖a + b‖ = 0 := by exact_mod_cast hh
             exact hab (norm_eq_zero.mp hh2)
           }
        _ = (‖a + b‖ : ℂ)⁻¹ * (a + b) := by rw [h]
        _ = (a + b) / ‖a + b‖ := by ring
    }
    exact h_div
  }
  rw [eq3, eq4] at eq1
  use ‖a * v + b * star v‖ / (‖v‖ * ‖a + b‖)
  push_cast
  calc (‖a * v + b * star v‖ / (‖v‖ * ‖a + b‖) : ℂ) * (a + b) = (‖a * v + b * star v‖ / (‖v‖ * ‖a + b‖) : ℂ) * (a + b) * (v / v) := by {
         rw [div_self hv_ne, mul_one]
       }
    _ = (‖a * v + b * star v‖ * (v / ‖v‖ * ((a + b) / ‖a + b‖))) / v := by {
         ring
       }
    _ = (a * v + b * star v) / v := by rw [← eq1]
    _ = a + b * (star v / v) := by {
         calc (a * v + b * star v) / v = a * (v / v) + b * (star v / v) := by ring
           _ = a * 1 + b * (star v / v) := by rw [div_self hv_ne]
           _ = a + b * (star v / v) := by ring
       }
}

/-- If a real-linear map f(z) = a * z + b * star z preserves angles, then b = 0. -/

lemma conformal_linear_implies_b_zero (a b : ℂ)
    (h_conformal : ∀ v₁ v₂ : ℂ, v₁ ≠ 0 → v₂ ≠ 0 →
      a * v₁ + b * star v₁ ≠ 0 → a * v₂ + b * star v₂ ≠ 0 →
      arg (a * v₂ + b * star v₂) - arg (a * v₁ + b * star v₁) = arg v₂ - arg v₁) :
    b = 0 := by {
  by_cases hab : a + b = 0
  · exact conformal_linear_case_add_zero a b h_conformal hab
  · -- a + b \neq 0
    -- To prove b = 0, we use the geometric insight from Sarason:
    -- "as gamma traverses the unit circle, a + b * (star gamma)/(gamma) twice traverses the unit circle"
    --
    -- This geometric insight relies on the relation: c * (a+b) = a + b * (star v / v).
    -- 1. Conformality Means Angle Preservation: The angle between f(v) and f(1) must equal
    --    the angle between v and 1. This means the complex argument of f(v)/f(1) matches the argument of v.
    -- 2. Real Scalars for Equal Arguments: If two complex numbers have the same argument, they lie on the
    --    same ray from the origin, meaning one is a real scalar multiple of the other: f(v)/f(1) = c * v
    --    for some real number c > 0.
    -- 3. Applying the Linear Map: Since f(z) = az + b\bar{z}, f(v) = av + b\bar{v} and f(1) = a + b.
    --    So (av + b\bar{v})/(a+b) = cv. Multiplying by (a+b) gives av + b\bar{v} = cv(a+b).
    --    Dividing by v yields the constraint: a + b(\bar{v}/v) = c(a+b).
    --
    -- The Geometric Meaning:
    -- As a vector v traverses the unit circle, the fraction \bar{v}/v (which equals v^-2) traces
    -- the unit circle twice. The left side, a + b(\bar{v}/v), traces a circle of radius |b| centered at a.
    -- The right side, c(a+b), traces a straight line passing through the origin and a+b.
    -- A circle can only lie entirely on a straight line if its radius is 0, implying |b| = 0 and thus b = 0.
    --
    -- Rather than formalizing continuous curve traversal, we evaluate this algebraic relation
    -- at specific orthogonal points (I and 1+I) to algebraically force b = 0.

    have h1 : I ≠ 0 := I_ne_zero
    have h2 : 1 + I ≠ 0 := by {
      intro h
      have h_re : (1 + I : ℂ).re = 0 := by rw [h]; rfl
      simp at h_re
    }

    by_cases hfI : a * I + b * star I = 0
    · -- Handle the edge case where the map sends I to the origin
      -- if f(I) = 0, then a * I - b * I = 0 \implies a = b.
      have hab_eq : a = b := by {
        have h_simp : a * I + b * (-I) = 0 := by {
          -- Simplify star I to -I
          calc a * I + b * (-I) = a * I + b * star I := by { rw [star_def, conj_I] }
            _ = 0 := hfI
        }
        have h_div : (a - b) * I = 0 := by {
          calc (a - b) * I = a * I - b * I := by ring
            _ = a * I + b * (-I) := by ring
            _ = 0 := h_simp
        }
        cases mul_eq_zero.mp h_div with
        | inl h_ab => exact sub_eq_zero.mp h_ab
        | inr h_I => exact False.elim (I_ne_zero h_I)
      }
      -- f(1) = a + b = 2a
      have hf1 : a * 1 + b * star 1 = 2 * a := by {
        have h_star1 : star (1 : ℂ) = 1 := by { apply Complex.ext <;> simp }
        rw [hab_eq, h_star1]
        ring
      }
      have hf2 : a * (1 + I) + b * star (1 + I) = 2 * a := by {
        rw [hab_eq]
        apply Complex.ext <;> simp <;> ring
      }
      by_cases ha_zero : a = 0
      · rw [ha_zero] at hab_eq
        exact hab_eq.symm
      have ha2_ne : 2 * a ≠ 0 := by {
        -- Prove 2a != 0 to ensure f(1) != 0 for conformality
        intro h
        cases mul_eq_zero.mp h with
        | inl h2 => norm_num at h2
        | inr ha => exact ha_zero ha
      }
      have hf1_ne : a * 1 + b * star 1 ≠ 0 := by {
        -- Establish f(1) != 0
        rw [hf1]
        exact ha2_ne
      }
      have h1_one : (1 : ℂ) ≠ 0 := one_ne_zero

      -- Apply conformality between the points 1 and 1+I
      have h_arg := h_conformal 1 (1 + I) h1_one h2 hf1_ne (by { rw [hf2, ← hf1]; exact hf1_ne })
      rw [hf1, hf2] at h_arg
      simp at h_arg

      -- Use the argument equality to extract the norm and arrive at a contradiction
      -- h_arg : 0 = arg (1 + I) - arg 1
      have h_arg_1_I : arg (1 + I) = arg 1 := by {
        rw [arg_one]
        exact h_arg.symm
      }
      have h_c := (arg_eq_arg_iff h2 h1_one).mp h_arg_1_I
      have h_im : (((‖(1:ℂ)‖:ℂ) / (‖1 + I‖:ℂ)) * (1 + I)).im = (1 : ℂ).im := congrArg im h_c
      have h_im2 : ‖(1:ℂ)‖ / ‖1 + I‖ * 1 = 0 := by {
        calc ‖(1:ℂ)‖ / ‖1 + I‖ * 1 = (((‖(1:ℂ)‖:ℂ) / (‖1 + I‖:ℂ))).re * (1 + I : ℂ).im + (((‖(1:ℂ)‖:ℂ) / (‖1 + I‖:ℂ))).im * (1 + I : ℂ).re := by simp
          _ = (((‖(1:ℂ)‖:ℂ) / (‖1 + I‖:ℂ)) * (1 + I)).im := by simp [mul_im]
          _ = (1 : ℂ).im := h_im
          _ = 0 := rfl
      }
      rw [mul_one] at h_im2
      have h_norm : ‖(1:ℂ)‖ / ‖1 + I‖ = 0 := h_im2
      have h_norm_one : ‖(1:ℂ)‖ = 1 := norm_one
      rw [h_norm_one] at h_norm
      have h_norm_zero : (1 : ℝ) = 0 := by {
        have hh : (1 : ℝ) / ‖1 + I‖ * ‖1 + I‖ = 0 * ‖1 + I‖ := by rw [h_norm]
        rw [zero_mul] at hh
        have h_cancel : (1 : ℝ) / ‖1 + I‖ * ‖1 + I‖ = 1 := by {
          apply div_mul_cancel₀
          intro h
          have h_eq_zero : 1 + I = 0 := norm_eq_zero.mp h
          exact h2 h_eq_zero
        }
        rw [h_cancel] at hh
        exact hh
      }
      norm_num at h_norm_zero

    · -- Now a * I + b * star I \neq 0
      by_cases hf1I : a * (1 + I) + b * star (1 + I) = 0
      · -- Handle the second edge case where f(1+I) = 0
        -- f(1+I) = 0 \implies a(1+I) + b(1-I) = 0 \implies b = -aI
        have h_mul : (a * (1 + I) + b * star (1 + I)) * (1 + I) = 0 := by {
          rw [hf1I, zero_mul]
        }
        have h_alg : (a * (1 + I) + b * star (1 + I)) * (1 + I) = 2 * a * I + 2 * b := by {
          -- Expand the multiplication by (1+I) to simplify terms
          have h_star : star (1 + I) = 1 - I := by { apply Complex.ext <;> simp }
          rw [h_star]
          apply Complex.ext <;> simp <;> ring
        }
        rw [h_alg] at h_mul
        have hb_eq : 2 * b = -2 * a * I := by {
          -- Isolate 2b to show b = -aI
          calc 2 * b = 2 * a * I + 2 * b - 2 * a * I := by ring
            _ = 0 - 2 * a * I := by rw [h_mul]
            _ = -2 * a * I := by ring
        }
        have hb_eq2 : b = -a * I := by {
          calc b = (2 * b) / 2 := by ring
            _ = (-2 * a * I) / 2 := by rw [hb_eq]
            _ = -a * I := by ring
        }
        have ha_ne : a ≠ 0 := by {
          -- Ensure a != 0 to prevent a+b=0 contradiction
          intro h
          rw [h] at hb_eq2
          have hb_zero : b = 0 := by { rw [hb_eq2]; ring }
          have hab_zero : a + b = 0 := by rw [h, hb_zero, add_zero]
          exact hab hab_zero
        }

        -- Apply the linear helper at I to extract a real scalar c1
        have h_c1 := conformal_linear_helper a b I h_conformal hab h1 hfI
        rcases h_c1 with ⟨c1, hc1⟩
        have hv1 : star I / I = -1 := by {
          -- Evaluate the \bar{v}/v term for I
          rw [star_def, conj_I]
          calc -I / I = -(I / I) := neg_div I I
            _ = -1 := by { rw [div_self I_ne_zero] }
        }
        rw [hv1] at hc1
        have hc1_re : (c1 : ℂ) * (a * (1 - I)) = a * (1 + I) := by {
          calc (c1 : ℂ) * (a * (1 - I)) = (c1 : ℂ) * (a + -a * I) := by ring
            _ = (c1 : ℂ) * (a + b) := by { rw [hb_eq2] }
            _ = a + b * -1 := hc1
            _ = a - b := by ring
            _ = a - (-a * I) := by { rw [hb_eq2] }
            _ = a * (1 + I) := by ring
        }
        have hc1_c : (c1 : ℂ) * (1 - I) = 1 + I := by {
          -- Cancel out 'a' to yield a purely numerical relation involving c1
          have h_mul_a : a * ((c1 : ℂ) * (1 - I)) = a * (1 + I) := by {
            calc a * ((c1 : ℂ) * (1 - I)) = (c1 : ℂ) * (a * (1 - I)) := by ring
              _ = a * (1 + I) := hc1_re
          }
          exact mul_left_cancel₀ ha_ne h_mul_a
        }
        have hc1_im : ((c1 : ℂ) * (1 - I)).im = (1 + I : ℂ).im := by rw [hc1_c]
        have hc1_re2 : ((c1 : ℂ) * (1 - I)).re = (1 + I : ℂ).re := by rw [hc1_c]

        -- The resulting equality for c1 yields a contradiction since c1 is real
        simp at hc1_im
        simp at hc1_re2
        linarith

      · -- Main Case: Neither f(I) nor f(1+I) is zero.
        -- We apply the linear helper to both I and 1+I to establish our system of equations
        have h_c1 := conformal_linear_helper a b I h_conformal hab h1 hfI
        have h_c2 := conformal_linear_helper a b (1 + I) h_conformal hab h2 hf1I
        rcases h_c1 with ⟨c1, hc1⟩
        rcases h_c2 with ⟨c2, hc2⟩
        -- For v = I, \bar{v}/v = -1.
        have hv1 : star I / I = -1 := by {
          rw [star_def, conj_I]
          calc -I / I = -(I / I) := neg_div I I
            _ = -1 := by { rw [div_self I_ne_zero] }
        }
        rw [hv1] at hc1

        -- For v = 1+I, \bar{v}/v = -I.
        have hv2 : star (1 + I) / (1 + I) = -I := by {
          -- Evaluate the \bar{v}/v term for 1+I
          have h_star : star (1 + I) = 1 - I := by { apply Complex.ext <;> simp }
          rw [h_star]
          apply mul_right_cancel₀ h2
          calc (1 - I) / (1 + I) * (1 + I) = 1 - I := div_mul_cancel₀ _ h2
            _ = -I * (1 + I) := by { apply Complex.ext <;> simp }
        }
        rw [hv2] at hc2

        have hc1_alg : b * (1 + c1 : ℂ) = a * (1 - c1 : ℂ) := by {
          -- Algebraically rearrange the first equation to isolate 'b * factor'
          calc b * (1 + c1 : ℂ) = b + c1 * b := by ring
            _ = b + (c1 * a + c1 * b) - c1 * a := by ring
            _ = b + (c1 : ℂ) * (a + b) - c1 * a := by ring
            _ = b + (a - b) - c1 * a := by {
                 have h_sub : a + b * -1 = a - b := by ring
                 rw [hc1, h_sub]
               }
            _ = a - c1 * a := by ring
            _ = a * (1 - c1 : ℂ) := by ring
        }

        have hc2_alg : b * (c2 + I : ℂ) = a * (1 - c2 : ℂ) := by {
          -- Algebraically rearrange the second equation to isolate 'b * factor'
          calc b * (c2 + I : ℂ) = b * c2 + b * I := by ring
            _ = b * I + c2 * b := by ring
            _ = b * I + (c2 * a + c2 * b) - c2 * a := by ring
            _ = b * I + (c2 : ℂ) * (a + b) - c2 * a := by ring
            _ = b * I + (a - b * I) - c2 * a := by {
                 have h_sub : a + b * -I = a - b * I := by ring
                 rw [hc2, h_sub]
               }
            _ = a - c2 * a := by ring
            _ = a * (1 - c2 : ℂ) := by ring
        }

        have h_combine : b * ((1 + c1 : ℂ) * (1 - c2 : ℂ) - (c2 + I : ℂ) * (1 - c1 : ℂ)) = 0 := by {
          -- Combine the two equations by cross-multiplying the terms associated with 'a'
          -- This eliminates 'a' completely and leaves an equation solely in terms of 'b'
          calc b * ((1 + c1 : ℂ) * (1 - c2 : ℂ) - (c2 + I : ℂ) * (1 - c1 : ℂ))
            = b * (1 + c1 : ℂ) * (1 - c2 : ℂ) - b * (c2 + I : ℂ) * (1 - c1 : ℂ) := by ring
          _ = a * (1 - c1 : ℂ) * (1 - c2 : ℂ) - a * (1 - c2 : ℂ) * (1 - c1 : ℂ) := by {
               rw [hc1_alg, hc2_alg]
             }
          _ = 0 := by ring
        }

        cases mul_eq_zero.mp h_combine with
        | inl hb_zero => exact hb_zero
        | inr h_factor_zero =>
          -- If b is not zero, the scalar factor must be zero.
          -- We extract the imaginary part to show c1 = 1.
          have h_im_calc : ((1 + c1 : ℂ) * (1 - c2 : ℂ) - (c2 + I : ℂ) * (1 - c1 : ℂ)).im = (c1 : ℝ) - 1 := by {
            simp
          }
          have h_im_zero : ((1 + c1 : ℂ) * (1 - c2 : ℂ) - (c2 + I : ℂ) * (1 - c1 : ℂ)).im = 0 := by rw [h_factor_zero]; rfl
          rw [h_im_calc] at h_im_zero
          have hc1_eq_1 : (c1 : ℝ) = 1 := sub_eq_zero.mp h_im_zero

          -- Substitute c1 = 1 back into the first equation to trivially force b = 0
          have hc1_1_complex : (c1 : ℂ) = 1 := by exact_mod_cast hc1_eq_1
          rw [hc1_1_complex] at hc1_alg
          have h_rhs : a * (1 - (1 : ℂ)) = 0 := by ring
          rw [h_rhs] at hc1_alg
          have h_lhs : b * (1 + 1 : ℂ) = b * 2 := by ring
          rw [h_lhs] at hc1_alg

          -- This final equality proves b * 2 = 0, which means b = 0
          cases mul_eq_zero.mp hc1_alg with
          | inl h_b => exact h_b
          | inr h_2 => norm_num at h_2
}

/--
  Algebraic identity for the total real derivative of a complex function,
  decomposed into the ∂ and ∂̄ operators applied to v and \bar{v}.
-/
lemma fderiv_eq_del_add_delBar (f : ℂ → ℂ) (z : ℂ) (v : ℂ) :
    fderiv ℝ f z v = (del f z) * v + (delBar f z) * star v := by {
  let L := fderiv ℝ f z
  have hv : v = (v.re : ℂ) * 1 + (v.im : ℂ) * I := by {
    calc v = (v.re : ℂ) + (v.im : ℂ) * I := by exact Eq.symm (re_add_im v)
      _ = (v.re : ℂ) * 1 + (v.im : ℂ) * I := by rw [mul_one]
  }
  have hstar : star v = (v.re : ℂ) * 1 - (v.im : ℂ) * I := by {
    calc star v = (v.re : ℂ) - (v.im : ℂ) * I := by { apply Complex.ext <;> simp }
      _ = (v.re : ℂ) * 1 - (v.im : ℂ) * I := by rw [mul_one]
  }
  
  have h_L_v : L v = (v.re : ℝ) • L 1 + (v.im : ℝ) • L I := by {
    calc L v = L ((v.re : ℂ) + (v.im : ℂ) * I) := by { congr 1; exact Eq.symm (re_add_im v) }
      _ = L ((v.re : ℝ) • 1 + (v.im : ℝ) • I) := by {
            congr 1
            have h1 : (v.re : ℝ) • (1 : ℂ) = (v.re : ℂ) := by { apply Complex.ext <;> simp }
            have h2 : (v.im : ℝ) • I = (v.im : ℂ) * I := by { apply Complex.ext <;> simp }
            rw [h1, h2]
          }
      _ = (v.re : ℝ) • L 1 + (v.im : ℝ) • L I := by {
            rw [L.map_add, L.map_smul, L.map_smul]
          }
  }

  unfold del delBar
  dsimp only
  
  have h_alg : (1 / 2 : ℂ) * (L 1 - I * L I) * v + (1 / 2 : ℂ) * (L 1 + I * L I) * star v = 
               (v.re : ℂ) * L 1 + (v.im : ℂ) * L I := by {
    nth_rw 1 [hv]
    nth_rw 1 [hstar]
    calc (1 / 2 : ℂ) * (L 1 - I * L I) * (↑v.re * 1 + ↑v.im * I) + (1 / 2 : ℂ) * (L 1 + I * L I) * (↑v.re * 1 - ↑v.im * I)
      = (v.re : ℂ) * L 1 - I^2 * (v.im : ℂ) * L I := by ring
    _ = (v.re : ℂ) * L 1 - (-1) * (v.im : ℂ) * L I := by rw [I_sq]
    _ = (v.re : ℂ) * L 1 + (v.im : ℂ) * L I := by ring
  }
  
  have h_coerce1 : (v.re : ℝ) • L 1 = (v.re : ℂ) * L 1 := by { apply Complex.ext <;> simp }
  have h_coerce2 : (v.im : ℝ) • L I = (v.im : ℂ) * L I := by { apply Complex.ext <;> simp }
  
  rw [h_coerce1, h_coerce2] at h_L_v
  
  rw [h_L_v]
  exact h_alg.symm
}

/--
  The Chain Rule for paths using Sarason's ∂ and ∂̄ operators.
  If f has continuous first partial derivatives (is real-differentiable),
  and γ is a differentiable path, then the derivative of f ∘ γ is given by:
  (f ∘ γ)'(t) = f_z γ'(t) + f_z̄ \overline{γ'(t)}
-/
lemma chain_rule_path (f : ℂ → ℂ) (γ : ℝ → ℂ) (t : ℝ)
    (hf : DifferentiableAt ℝ f (γ t)) (hγ : DifferentiableAt ℝ γ t) (v : ℝ) :
    fderiv ℝ (f ∘ γ) t v = (del f (γ t)) * (fderiv ℝ γ t v) + (delBar f (γ t)) * star (fderiv ℝ γ t v) := by {
  -- By the chain rule, the derivative of the composition is the composition of derivatives.
  have h_comp : fderiv ℝ (f ∘ γ) t v = fderiv ℝ f (γ t) (fderiv ℝ γ t v) := by {
    have h1 := fderiv_comp t hf hγ
    rw [h1]
    rfl
  }
  rw [h_comp]
  -- We apply our algebraic decomposition of the real total derivative into del and delBar parts
  exact fderiv_eq_del_add_delBar f (γ t) (fderiv ℝ γ t v)
}

/--
  Bridge lemma: If a function f is conformal (preserves angles of paths),
  then its total real derivative L_z at that point is a conformal linear map.
-/
lemma conformal_linear_of_conformal (f : ℂ → ℂ) (z : ℂ)
    (hf : DifferentiableAt ℝ f z) (h_conf : conformal f z) :
    ∀ v₁ v₂ : ℂ, v₁ ≠ 0 → v₂ ≠ 0 →
    (del f z) * v₁ + (delBar f z) * star v₁ ≠ 0 →
    (del f z) * v₂ + (delBar f z) * star v₂ ≠ 0 →
    arg ((del f z) * v₂ + (delBar f z) * star v₂) - arg ((del f z) * v₁ + (delBar f z) * star v₁) = arg v₂ - arg v₁ := by {
  -- This proof requires constructing straight-line paths γ_i(t) = z + t * v_i
  -- and applying the chain_rule_path to evaluate their pathAngles under f.
  -- The definition of conformal f z guarantees these path angles are preserved.
  sorry
}

/-- 
  Helper lemma: Evaluates the complex derivative in terms of the ∂ operator. 
-/
lemma deriv_eps_eq_del (f : ℂ → ℂ) (z : ℂ) (h_diff : DifferentiableAt ℝ f z) (h_b_zero : delBar f z = 0)
    (h_holom : DifferentiableAt_eps f z) : deriv_eps f z h_holom = del f z := by {
  have h_eval1 : fderiv ℝ f z 1 = deriv_eps f z h_holom := sorry
  
  have h_decomp := fderiv_eq_del_add_delBar f z 1
  have h_star1 : star (1 : ℂ) = 1 := star_one ℂ
  rw [h_star1] at h_decomp
  rw [h_b_zero] at h_decomp
  
  have h_alg : del f z * 1 + 0 * 1 = del f z := by ring
  rw [h_alg] at h_decomp
  
  rw [← h_eval1, h_decomp]
}

/--
  Helper lemma: If f is conformal, its derivative (the ∂ operator) cannot be zero.
-/
lemma conformal_implies_del_ne_zero (f : ℂ → ℂ) (z : ℂ) (h_diff : DifferentiableAt ℝ f z) (h_conf : conformal f z) : del f z ≠ 0 := by {
  -- If del f z = 0, then the total derivative L(v) = 0 for all v,
  -- which contradicts that the angle preserving linear map must be non-zero on non-zero vectors.
  sorry
}

/--
  §II.12 BIG FINALE: Conformality implies Holomorphicity.
  If f has continuous first partial derivatives (real-differentiable) and is conformal in a domain G,
  then f is holomorphic in G, and its derivative is never zero.
-/
theorem conformal_implies_holomorphic (f : ℂ → ℂ) (G : Set ℂ)
    (h_diff : ∀ z ∈ G, DifferentiableAt ℝ f z)
    (h_conf : ∀ z ∈ G, conformal f z) :
    HolomorphicOn_eps f G ∧ (∀ z ∈ G, ∃ (h : DifferentiableAt_eps f z), deriv_eps f z h ≠ 0) := by {
  constructor
  · intro z hz
    have hd_real := h_diff z hz
    have h_conf_z := h_conf z hz
    
    -- Extract the linear conformality from path conformality
    have h_lin_conf := conformal_linear_of_conformal f z hd_real h_conf_z
    
    -- By Lemma II.12 for linear maps, angle preservation implies the \bar{z} coefficient is 0.
    have h_b_zero : delBar f z = 0 := conformal_linear_implies_b_zero (del f z) (delBar f z) h_lin_conf
    
    -- By Cauchy-Riemann (delBar = 0), f is complex differentiable.
    exact (hasComplexDerivAt_iff_delBar_eq_zero hd_real).mpr h_b_zero
    
  · intro z hz
    -- f is complex differentiable at z
    have hd_real := h_diff z hz
    have h_conf_z := h_conf z hz
    have h_lin_conf := conformal_linear_of_conformal f z hd_real h_conf_z
    have h_b_zero : delBar f z = 0 := conformal_linear_implies_b_zero (del f z) (delBar f z) h_lin_conf
    have h_holom := (hasComplexDerivAt_iff_delBar_eq_zero hd_real).mpr h_b_zero
    
    use h_holom
    
    -- The complex derivative is exactly the 'a' coefficient (del f z).
    have h_eq : deriv_eps f z h_holom = del f z := deriv_eps_eq_del f z hd_real h_b_zero h_holom
    rw [h_eq]
    
    -- By conformality, the linear map cannot send non-zero vectors to 0. Thus 'a' \neq 0.
    exact conformal_implies_del_ne_zero f z hd_real h_conf_z
}

end Sarason.Ch2

end
