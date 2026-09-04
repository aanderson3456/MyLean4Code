import ComplexAnalysis.Sarason.Chapter2
import ComplexAnalysis.Sarason.Definitions

open Complex
open Sarason
open Sarason.Ch2

theorem conformal_implies_holomorphic_II_12 {G : Set ℂ} (hG : IsOpen G)
    (u v : ℝ × ℝ → ℝ) (ux uy vx vy : ℝ × ℝ → ℝ)
    (hu_diff : ∀ z ∈ G, HasFDerivAt_R2_eps u v (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) (z.re, z.im))
    (h_cont_ux : ContinuousOn (fun z : ℂ => ux (z.re, z.im)) G) (h_cont_uy : ContinuousOn (fun z : ℂ => uy (z.re, z.im)) G)
    (h_cont_vx : ContinuousOn (fun z : ℂ => vx (z.re, z.im)) G) (h_cont_vy : ContinuousOn (fun z : ℂ => vy (z.re, z.im)) G)
    (f : ℂ → ℂ) (hf : ∀ z, f z = u (z.re, z.im) + I * v (z.re, z.im))
    (h_conf : ∀ z ∈ G, conformal f z) :
    HolomorphicOn_eps f G ∧ (∀ z ∈ G, ∃ (h : DifferentiableAt_eps f z), deriv_eps f z h ≠ 0) := by {
  have hf_eq : f = fun w => u (w.re, w.im) + I * v (w.re, w.im) := funext hf
  
  have hu_x : ∀ z ∈ G, HasPartialDerivX_C_to_R_eps (fun z => u (z.re, z.im)) (ux (z.re, z.im)) z := fun z hz => (partials_of_fderiv_R2 (hu_diff z hz)).1
  have hu_y : ∀ z ∈ G, HasPartialDerivY_C_to_R_eps (fun z => u (z.re, z.im)) (uy (z.re, z.im)) z := fun z hz => (partials_of_fderiv_R2 (hu_diff z hz)).2.1
  have hv_x : ∀ z ∈ G, HasPartialDerivX_C_to_R_eps (fun z => v (z.re, z.im)) (vx (z.re, z.im)) z := fun z hz => (partials_of_fderiv_R2 (hu_diff z hz)).2.2.1
  have hv_y : ∀ z ∈ G, HasPartialDerivY_C_to_R_eps (fun z => v (z.re, z.im)) (vy (z.re, z.im)) z := fun z hz => (partials_of_fderiv_R2 (hu_diff z hz)).2.2.2
  
  constructor
  · unfold HolomorphicOn_eps
    intro z hz
    have hz_diff := hu_diff z hz
    have hz_conf_f := h_conf z hz
    have hz_conf : conformal (fun w => u (w.re, w.im) + I * v (w.re, w.im)) z := by {
      rw [← hf_eq]
      exact hz_conf_f
    }
    have h_L_conf := conformal_linear_of_conformal_eps u v (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) z hz_diff hz_conf
    have h_delBar_zero := conformal_implies_delBar_zero (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) h_L_conf
    have h_cr := cr_of_delBar_zero (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) h_delBar_zero
    
    have h_diff_at := II_7 hG (fun z => u (z.re, z.im)) (fun z => v (z.re, z.im)) (fun z => ux (z.re, z.im)) (fun z => uy (z.re, z.im)) (fun z => vx (z.re, z.im)) (fun z => vy (z.re, z.im)) hu_x hu_y hv_x hv_y h_cont_ux h_cont_uy h_cont_vx h_cont_vy z hz h_cr f hf
    exact h_diff_at
  · intro z hz
    have hz_diff := hu_diff z hz
    have hz_conf_f := h_conf z hz
    have hz_conf : conformal (fun w => u (w.re, w.im) + I * v (w.re, w.im)) z := by {
      rw [← hf_eq]
      exact hz_conf_f
    }
    have h_L_conf := conformal_linear_of_conformal_eps u v (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) z hz_diff hz_conf
    have h_del_ne_zero := conformal_implies_del_ne_zero (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) h_L_conf
    have h_delBar_zero := conformal_implies_delBar_zero (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) h_L_conf
    have h_cr := cr_of_delBar_zero (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) h_delBar_zero
    
    have h_diff_at := II_7 hG (fun z => u (z.re, z.im)) (fun z => v (z.re, z.im)) (fun z => ux (z.re, z.im)) (fun z => uy (z.re, z.im)) (fun z => vx (z.re, z.im)) (fun z => vy (z.re, z.im)) hu_x hu_y hv_x hv_y h_cont_ux h_cont_uy h_cont_vx h_cont_vy z hz h_cr f hf
    use h_diff_at
    
    have h_deriv_eq : deriv_eps f z h_diff_at = (ux (z.re, z.im) : ℂ) + I * vx (z.re, z.im) := by sorry
    have h_del_eq := deriv_eps_eq_del (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) h_cr
    
    rw [h_deriv_eq, h_del_eq]
    exact h_del_ne_zero
}
