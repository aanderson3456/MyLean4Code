import ComplexAnalysis.Sarason.Chapter2

open Classical

lemma conformal_linear_of_conformal_eps_test (u v : ℝ × ℝ → ℝ) (ux uy vx vy : ℝ) (z : ℂ)
  (h_diff : HasFDerivAt_R2_eps u v ux uy vx vy (z.re, z.im))
  (h_conf : conformal (fun w => u (w.re, w.im) + I * v (w.re, w.im)) z) :
  conformal (ConformalLinearMap_eps ux uy vx vy) 0 := by {
  unfold conformal
  intro γ₁ γ₂ x y p₁ t₁ p₂ t₂ f'₁ f'₂ hext₁ hext₂ hp₁_diff hp₂_diff hp₁_ne hp₂_ne hf₁_diff hf₂_diff
  let Γ₁ := translated_path z p₁
  let Γ₂ := translated_path z p₂
  have hΓ₁_ext : Γ₁.extend t₁ = z := by {
    rw [translated_path_extend, hext₁, add_zero]
  }
  have hΓ₂_ext : Γ₂.extend t₂ = z := by {
    rw [translated_path_extend, hext₂, add_zero]
  }
  have hΓ₁_diff : HasDerivAt_R_to_C_eps Γ₁.extend (pathDeriv Γ₁ t₁) t₁ := by {
    rw [translated_path_pathDeriv]
    exact translated_path_hasDerivAt_eps z p₁ t₁ _ hp₁_diff
  }
  have hΓ₂_diff : HasDerivAt_R_to_C_eps Γ₂.extend (pathDeriv Γ₂ t₂) t₂ := by {
    rw [translated_path_pathDeriv]
    exact translated_path_hasDerivAt_eps z p₂ t₂ _ hp₂_diff
  }
  have hΓ₁_ne : pathDeriv Γ₁ t₁ ≠ 0 := by {
    rw [translated_path_pathDeriv]
    exact hp₁_ne
  }
  have hΓ₂_ne : pathDeriv Γ₂ t₂ ≠ 0 := by {
    rw [translated_path_pathDeriv]
    exact hp₂_ne
  }
  have h_chain₁ := path_comp_deriv_R2 u v ux uy vx vy z h_diff Γ₁ t₁ hΓ₁_ext hΓ₁_diff
  have h_chain₂ := path_comp_deriv_R2 u v ux uy vx vy z h_diff Γ₂ t₂ hΓ₂_ext hΓ₂_diff
  
  unfold conformal at h_conf
  have h_res := h_conf (z + γ₁) (z + γ₂) (z + x) (z + y) Γ₁ t₁ Γ₂ t₂ 
    (ConformalLinearMap_eps ux uy vx vy (pathDeriv Γ₁ t₁)) 
    (ConformalLinearMap_eps ux uy vx vy (pathDeriv Γ₂ t₂)) 
    hΓ₁_ext hΓ₂_ext hΓ₁_diff hΓ₂_diff hΓ₁_ne hΓ₂_ne h_chain₁ h_chain₂

  have h_L_diff := linear_hasFDerivAt_R2_eps ux uy vx vy (0, 0)
  
  have h_chain_L₁ := path_comp_deriv_R2 (fun p => ux * p.1 + uy * p.2) (fun p => vx * p.1 + vy * p.2) ux uy vx vy 0 h_L_diff p₁ t₁ hext₁ hp₁_diff
  have h_chain_L₂ := path_comp_deriv_R2 (fun p => ux * p.1 + uy * p.2) (fun p => vx * p.1 + vy * p.2) ux uy vx vy 0 h_L_diff p₂ t₂ hext₂ hp₂_diff
  
  have h_simp₁ : (fun t => ((ux * ((p₁.extend t).re) + uy * ((p₁.extend t).im)) : ℂ) + I * ((vx * ((p₁.extend t).re) + vy * ((p₁.extend t).im)) : ℂ)) = 
                 (ConformalLinearMap_eps ux uy vx vy ∘ p₁.extend) := by {
    funext t
    unfold ConformalLinearMap_eps Function.comp
    push_cast
    ring
  }
  have h_simp₂ : (fun t => ((ux * ((p₂.extend t).re) + uy * ((p₂.extend t).im)) : ℂ) + I * ((vx * ((p₂.extend t).re) + vy * ((p₂.extend t).im)) : ℂ)) = 
                 (ConformalLinearMap_eps ux uy vx vy ∘ p₂.extend) := by {
    funext t
    unfold ConformalLinearMap_eps Function.comp
    push_cast
    ring
  }
  
  rw [h_simp₁] at h_chain_L₁
  rw [h_simp₂] at h_chain_L₂

  have h_uniq₁ : f'₁ = ConformalLinearMap_eps ux uy vx vy (pathDeriv p₁ t₁) := by {
    have h1 := (hasDerivAt_R_to_C_iff_eps _ _ _).mpr hf₁_diff
    have h2 := (hasDerivAt_R_to_C_iff_eps _ _ _).mpr h_chain_L₁
    exact HasDerivAt.unique h1 h2
  }
  
  have h_uniq₂ : f'₂ = ConformalLinearMap_eps ux uy vx vy (pathDeriv p₂ t₂) := by {
    have h1 := (hasDerivAt_R_to_C_iff_eps _ _ _).mpr hf₂_diff
    have h2 := (hasDerivAt_R_to_C_iff_eps _ _ _).mpr h_chain_L₂
    exact HasDerivAt.unique h1 h2
  }

  rcases h_res with ⟨h_res_ne₁, h_res_ne₂, h_res_eq⟩
  
  -- We need `pathAngle Γ₁ t₁ Γ₂ t₂ = pathAngle p₁ t₁ p₂ t₂`
  have h_angle_eq : pathAngle Γ₁ t₁ Γ₂ t₂ = pathAngle p₁ t₁ p₂ t₂ := by {
    unfold pathAngle
    rw [translated_path_pathDeriv, translated_path_pathDeriv]
  }
  
  rw [translated_path_pathDeriv] at h_res_eq
  rw [translated_path_pathDeriv] at h_res_eq
  
  rw [h_uniq₁, h_uniq₂]
  exact h_res_eq.trans h_angle_eq
}
