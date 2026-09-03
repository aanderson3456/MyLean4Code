import re

with open("ComplexAnalysis/Sarason/Chapter2.lean", "r") as f:
    content = f.read()

# 1. Fix conformal
content = content.replace(
"""    HasDerivAt_R_to_C_eps (f ∘ γ₁.extend) d₁ t₁ →
    HasDerivAt_R_to_C_eps (f ∘ γ₂.extend) d₂ t₂ →
    d₁ ≠ 0 →
    d₂ ≠ 0 →
    arg d₂ - arg d₁ = pathAngle γ₁ t₁ γ₂ t₂""",
"""    HasDerivAt_R_to_C_eps (f ∘ γ₁.extend) d₁ t₁ →
    HasDerivAt_R_to_C_eps (f ∘ γ₂.extend) d₂ t₂ →
    d₁ ≠ 0 ∧ d₂ ≠ 0 ∧ arg d₂ - arg d₁ = pathAngle γ₁ t₁ γ₂ t₂""")

# 2. Fix conformality_at_point
content = content.replace(
"""theorem conformality_at_point (f : ℂ → ℂ) (z₀ : ℂ) (f' : ℂ)
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
}""",
"""theorem conformality_at_point (f : ℂ → ℂ) (z₀ : ℂ) (f' : ℂ)
    (hf : HasDerivAt_eps f f' z₀)
    (hf_ne : f' ≠ 0)
    (h_arg : ∀ {x y} (γ : path_in_C x y) t, γ.extend t = z₀ → HasDerivAt_R_to_C_eps γ.extend (pathDeriv γ t) t → pathDeriv γ t ≠ 0 → arg (f' * pathDeriv γ t) = arg f' + arg (pathDeriv γ t)) :
    conformal f z₀ := by {
  unfold conformal pathAngle pathDirection
  intro x₁ y₁ x₂ y₂ γ₁ t₁ γ₂ t₂ d₁ d₂ hz₁ hz₂ hγ₁ hγ₂ hreg₁ hreg₂ hd₁ hd₂
  have hd₁_comp := path_comp_deriv γ₁ t₁ f z₀ f' hz₁ hf hγ₁
  have hd₂_comp := path_comp_deriv γ₂ t₂ f z₀ f' hz₂ hf hγ₂
  have heq₁ := HasDerivAt_R_to_C_eps_unique hd₁ hd₁_comp
  have heq₂ := HasDerivAt_R_to_C_eps_unique hd₂ hd₂_comp
  subst heq₁
  subst heq₂
  have hd1_ne : f' * pathDeriv γ₁ t₁ ≠ 0 := mul_ne_zero hf_ne hreg₁
  have hd2_ne : f' * pathDeriv γ₂ t₂ ≠ 0 := mul_ne_zero hf_ne hreg₂
  refine ⟨hd1_ne, hd2_ne, ?_⟩
  rw [h_arg γ₁ t₁ hz₁ hγ₁ hreg₁, h_arg γ₂ t₂ hz₂ hγ₂ hreg₂]
  ring
}""")

# 3. Replace conformal_implies_holomorphic
old_theorem = """theorem conformal_implies_holomorphic (f : ℂ → ℂ) (G : Set ℂ)
    (h_diff : ∀ z ∈ G, DifferentiableAt ℝ f z)
    (h_conf : ∀ z ∈ G, conformal f z) :
    HolomorphicOn_eps f G ∧ (∀ z ∈ G, ∃ (h : DifferentiableAt_eps f z), deriv_eps f z h ≠ 0) := by {
  constructor
  · intro z hz
    -- f is complex differentiable at z
    have hd_real := h_diff z hz
    have h_conf_z := h_conf z hz
    have h_lin_conf := conformal_linear_of_conformal f z hd_real h_conf_z
    have h_b_zero : delBar f z = 0 := conformal_linear_implies_b_zero (del f z) (delBar f z) h_lin_conf
    have h_holom := (hasComplexDerivAt_iff_delBar_eq_zero hd_real).mpr h_b_zero
    
    exact h_holom
    
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
}"""

new_theorem = """theorem conformal_implies_holomorphic_II_12 {G : Set ℂ} (hG : IsOpen G)
    (u v : ℂ → ℝ) (ux uy vx vy : ℂ → ℝ)
    (hu_x : ∀ z ∈ G, HasPartialDerivX_C_to_R_eps u (ux z) z)
    (hu_y : ∀ z ∈ G, HasPartialDerivY_C_to_R_eps u (uy z) z)
    (hv_x : ∀ z ∈ G, HasPartialDerivX_C_to_R_eps v (vx z) z)
    (hv_y : ∀ z ∈ G, HasPartialDerivY_C_to_R_eps v (vy z) z)
    (h_cont_ux : ContinuousOn ux G) (h_cont_uy : ContinuousOn uy G)
    (h_cont_vx : ContinuousOn vx G) (h_cont_vy : ContinuousOn vy G)
    (f : ℂ → ℂ) (hf : ∀ z, f z = u z + I * v z)
    (h_conf : ∀ z ∈ G, conformal f z) :
    HolomorphicOn_eps f G ∧ (∀ z ∈ G, ∃ (h : DifferentiableAt_eps f z), deriv_eps f z h ≠ 0) := by {
  
  -- Derive real differentiability from continuous partial derivatives (same as in II_7)
  have h_diff_real : ∀ z ∈ G, DifferentiableAt ℝ f z := by {
    intro z hz
    have hu_deriv : HasFDerivAt u (ux z • reCLM + uy z • imCLM) z :=
      hasFDerivAt_of_hasPartialDeriv hG u ux uy hu_x hu_y h_cont_ux h_cont_uy z hz
    have hv_deriv : HasFDerivAt v (vx z • reCLM + vy z • imCLM) z :=
      hasFDerivAt_of_hasPartialDeriv hG v vx vy hv_x hv_y h_cont_vx h_cont_vy z hz
    have hu_diff : DifferentiableAt ℝ u z := hu_deriv.differentiableAt
    have hv_diff : DifferentiableAt ℝ v z := hv_deriv.differentiableAt
    have hu_diff_C : DifferentiableAt ℝ (fun z => (u z : ℂ)) z := ofRealCLM.differentiableAt.comp z hu_diff
    have hv_diff_C : DifferentiableAt ℝ (fun z => (v z : ℂ)) z := ofRealCLM.differentiableAt.comp z hv_diff
    
    have h_f_eq : f = (fun z => (u z : ℂ)) + (fun z => I * (v z : ℂ)) := by {
      ext w
      rw [hf w]
      rfl
    }
    rw [h_f_eq]
    apply DifferentiableAt.add hu_diff_C
    have h_const_I : DifferentiableAt ℝ (fun _ => I) z := differentiableAt_const I
    exact DifferentiableAt.mul h_const_I hv_diff_C
  }
  
  constructor
  · intro z hz
    have hd_real := h_diff_real z hz
    have h_conf_z := h_conf z hz
    have h_lin_conf := conformal_linear_of_conformal f z hd_real h_conf_z
    have h_b_zero : delBar f z = 0 := conformal_linear_implies_b_zero (del f z) (delBar f z) h_lin_conf
    
    -- Extract CR equations from delBar f z = 0
    have h_cr : ux z = vy z ∧ uy z = -vx z := by {
      -- Algebraic extraction to be implemented along with R^2 limits.
      sorry
    }
    
    exact II_7 hG u v ux uy vx vy hu_x hu_y hv_x hv_y h_cont_ux h_cont_uy h_cont_vx h_cont_vy z hz h_cr f hf
    
  · intro z hz
    have hd_real := h_diff_real z hz
    have h_conf_z := h_conf z hz
    have h_lin_conf := conformal_linear_of_conformal f z hd_real h_conf_z
    have h_b_zero : delBar f z = 0 := conformal_linear_implies_b_zero (del f z) (delBar f z) h_lin_conf
    have h_cr : ux z = vy z ∧ uy z = -vx z := sorry
    have h_holom := II_7 hG u v ux uy vx vy hu_x hu_y hv_x hv_y h_cont_ux h_cont_uy h_cont_vx h_cont_vy z hz h_cr f hf
    
    use h_holom
    
    -- Evaluate derivative
    have h_eq : deriv_eps f z h_holom = del f z := deriv_eps_eq_del f z hd_real h_b_zero h_holom
    rw [h_eq]
    
    exact conformal_implies_del_ne_zero f z hd_real h_conf_z
}"""

content = content.replace(old_theorem, new_theorem)

with open("ComplexAnalysis/Sarason/Chapter2.lean", "w") as f:
    f.write(content)
