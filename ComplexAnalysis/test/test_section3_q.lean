import Mathlib
import brennan.Section3

open Complex Set Brennan.Section2 Brennan.Section3

lemma q_eq_F_deriv2_test (F : KClass) (z : ℂ) (h1: deriv F.F z ≠ 0) (h2: DifferentiableAt ℂ (deriv F.F) z) :
  q F z = -I * (z.im : ℂ) * (deriv (deriv F.F) z) / (deriv F.F z) := by
  dsimp [q]
  have h_Q_def : (Q F.F) = (fun x => (deriv F.F x)⁻¹) := by
    ext x
    dsimp [Q]
    rw [one_div]
  rw [h_Q_def]
  have h_Q_val : (deriv F.F z)⁻¹ = 1 / deriv F.F z := by rw [one_div]
  rw [h_Q_val]
  rw [deriv_inv'' h2 h1]
  field_simp
  ring
