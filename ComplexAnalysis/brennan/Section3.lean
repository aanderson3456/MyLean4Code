import Mathlib
import brennan.Section2
import brennan.Section2_Dyadic

open Complex Set MeasureTheory Topology Filter
open scoped ComplexConjugate Topology

noncomputable section

namespace Brennan.Section3

open Brennan.Section2
open Brennan.Section2_Dyadic

/-!
PAPER: Lemma 3.2 (Moments of the logarithmic derivative). Assume ρ > 2, and let P and β be
PAPER: as in Lemma 3.1. For z = x + iy ∈ H, define
PAPER: qF (z) = iy (Q'F(z) / QF(z)) = -iy (F''(z) / F'(z)) = aF(z) + i bF(z), (3.7)
PAPER: where aF, bF are real. 
-/

-- We define q_F(z) as the normalized logarithmic derivative
def q (F : KClass) (z : ℂ) : ℂ :=
  I * (z.im : ℂ) * (deriv (Q F.F) z) / (Q F.F z)

-- Equivalently, via F'' / F'
lemma q_eq_F_deriv2 (F : KClass) (z : ℂ) (h1 : deriv F.F z ≠ 0) (h2 : DifferentiableAt ℂ (deriv F.F) z) :
  q F z = -I * (z.im : ℂ) * (deriv (deriv F.F) z) / (deriv F.F z) := by
  dsimp [q]
  have h_Q_def_2 : Q F.F = fun x => 1 / deriv F.F x := by
    ext x
    dsimp [Q]
  rw [h_Q_def_2]
  have h_deriv : deriv (fun x => 1 / deriv F.F x) z = - deriv (deriv F.F) z / (deriv F.F z)^2 := by
    have h_rw : (fun x => 1 / deriv F.F x) = (fun x => (deriv F.F x)⁻¹) := by
      ext x
      rw [one_div]
    rw [h_rw]
    exact deriv_inv'' h2 h1
  rw [h_deriv]
  field_simp

-- The real part a_F(z)
def a (F : KClass) (z : ℂ) : ℝ := (q F z).re

-- The imaginary part b_F(z)
def b (F : KClass) (z : ℂ) : ℝ := (q F z).im

/-!
PAPER: The variables qF (i) are bounded on K, and
PAPER: EaF(i) = -β / 2, EbF(i) = 0, E|qF(i)|^2 = β(β + 1) / 4. (3.8)
-/
variable [MeasurableSpace KClass]
variable (P : Measure KClass) (h_P_prob : IsProbabilityMeasure P)
variable (beta : ℝ) (h_beta : beta = Real.log rho / Real.log 2) (h_rho : rho > 2)

lemma q_bounded_on_KClass : ∃ C : ℝ, ∀ F : KClass, ‖q F I‖ ≤ C := sorry

-- We need a lemma that allows us to pass the derivative inside the integral
lemma deriv_integral_y (P : Measure KClass) (z : ℂ) (hz : z ∈ H) :
  deriv (fun y : ℝ => ∫ F, ‖Q F.F (z.re + y • I)‖^2 ∂P) z.im =
  ∫ F, deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2) z.im ∂P := sorry

lemma deriv_integral_x (P : Measure KClass) (z : ℂ) (hz : z ∈ H) :
  deriv (fun x : ℝ => ∫ F, ‖Q F.F (x + z.im • I)‖^2 ∂P) z.re =
  ∫ F, deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2) z.re ∂P := sorry

lemma E_a_eq (h_P_eigen : ∀ z ∈ H, ∫ F, ‖Q F.F z‖^2 ∂P = (z.im : ℝ) ^ (-beta)) :
  ∫ F, a F I ∂P = -beta / 2 := by
  have hz_I : I ∈ H := by dsimp [H]; simp
  have h_rhs : deriv (fun y : ℝ => y ^ (-beta)) 1 = -beta := sorry
  have h_lhs : deriv (fun y : ℝ => ∫ F, ‖Q F.F (0 + y • I)‖^2 ∂P) 1 = ∫ F, 2 * a F I ∂P := sorry
  sorry

lemma E_b_eq (h_P_eigen : ∀ z ∈ H, ∫ F, ‖Q F.F z‖^2 ∂P = (z.im : ℝ) ^ (-beta)) :
  ∫ F, b F I ∂P = 0 := by
  have hz_I : I ∈ H := by dsimp [H]; simp
  have h_rhs : deriv (fun x : ℝ => (1 : ℝ) ^ (-beta)) 0 = 0 := sorry
  have h_lhs : deriv (fun x : ℝ => ∫ F, ‖Q F.F (x + 1 • I)‖^2 ∂P) 0 = ∫ F, 2 * b F I ∂P := sorry
  sorry

lemma E_q_sq_eq (h_P_eigen : ∀ z ∈ H, ∫ F, ‖Q F.F z‖^2 ∂P = (z.im : ℝ) ^ (-beta)) :
  ∫ F, ‖q F I‖^2 ∂P = beta * (beta + 1) / 4 := by
  have hz_I : I ∈ H := by dsimp [H]; simp
  have h_rhs : deriv (deriv (fun y : ℝ => y ^ (-beta))) 1 = beta * (beta + 1) := sorry
  have h_lhs : deriv (deriv (fun y : ℝ => ∫ F, ‖Q F.F (0 + y • I)‖^2 ∂P)) 1 + 
               deriv (deriv (fun x : ℝ => ∫ F, ‖Q F.F (x + 1 • I)‖^2 ∂P)) 0 = 
               ∫ F, 4 * ‖q F I‖^2 ∂P := sorry
  sorry

/-!
PAPER: They also satisfy
PAPER: qTzF (w) = qF (z · w), z, w ∈ H. (3.9)
-/
-- Covariance of q under the affine transfer operator
lemma q_T_eq (F : KClass) (z w : ℂ) (hz : z ∈ H) (hw : w ∈ H) :
  q ⟨T z F.F, sorry, sorry, sorry⟩ w = q F (aff z w) := by
  dsimp [q]
  have hz_im : (z.im : ℂ) ≠ 0 := by
    intro h
    have h_re : (z.im : ℝ) = 0 := by exact_mod_cast h
    have hz_pos : 0 < z.im := hz
    linarith
  have h_im_aff : (aff z w).im = z.im * w.im := by dsimp [aff]; simp
  
  have h_deriv_Q : deriv (Q (T z F.F)) w = (deriv (Q F.F) (aff z w) * z.im) / Q F.F z := sorry
  have h_Q_val : Q (T z F.F) w = Q F.F (aff z w) / Q F.F z := sorry

  rw [h_deriv_Q, h_Q_val]
  rw [h_im_aff]
  push_cast
  
  have h_Q_z_ne_zero : Q F.F z ≠ 0 := sorry
  
  field_simp

/-!
PAPER: Proof. Taking Φ = 1 in (3.1) gives
PAPER: E|QF (x + iy)|^2 = y^{-β}. (3.10)
-/
-- Expected value of |Q_F(z)|^2 over KClass (Equation 3.10)
lemma E_norm_Q_sq (z : ℂ) (hz : z ∈ H) (h_P_eigen : sorry) :
  ∫ F, ‖Q F.F z‖^2 ∂P = (z.im : ℝ) ^ (-beta) := sorry

/-!
PAPER: On a compact neighborhood of any interior point, the functions QF , Q'F , Q''F are uniformly
PAPER: bounded over K, by Lemma 2.2. These bounds control the first two real derivatives of
PAPER: |QF|^2, and hence justify differentiation under expectation in (3.10).
PAPER: Holomorphicity and (3.7) give the pointwise identities
PAPER: ∂y|QF|^2 = 2aF/y |QF|^2, ∂x|QF|^2 = 2bF/y |QF|^2, ∆|QF|^2 = 4|Q'F|^2.
-/
-- Algebraic reduction of the pointwise identities using Cauchy-Riemann equations
lemma laplacian_cr_algebra (ux uy vx vy : ℝ) (hCR1 : ux = vy) (hCR2 : uy = -vx) :
  2 * (ux * ux + uy * uy + vx * vx + vy * vy) = 4 * (ux * ux + vx * vx) := by
  calc
    2 * (ux * ux + uy * uy + vx * vx + vy * vy)
      = 2 * (ux * ux + (-vx) * (-vx) + vx * vx + ux * ux) := by rw [hCR1, hCR2]
    _ = 4 * (ux * ux + vx * vx) := by ring

lemma dy_cr_algebra (u v ux uy vx vy y a normQsq : ℝ) 
  (hCR1 : ux = vy) (hCR2 : uy = -vx)
  (hy : y ≠ 0) (hnorm : normQsq ≠ 0)
  (h_a : a = y * (v * ux - u * vx) / normQsq) :
  2 * (u * uy + v * vy) = 2 * a / y * normQsq := by
  calc
    2 * (u * uy + v * vy)
      = 2 * (u * (-vx) + v * ux) := by rw [hCR1, hCR2]
    _ = 2 * (v * ux - u * vx) := by ring
    _ = 2 * (a * normQsq / y) := by
      rw [h_a]
      have hy_div : (y * (v * ux - u * vx) / normQsq) * normQsq / y = (v * ux - u * vx) := by
        rw [div_mul_cancel₀ _ hnorm]
        calc (y * (v * ux - u * vx)) / y = (v * ux - u * vx) * y / y := by ring
        _ = (v * ux - u * vx) := by rw [mul_div_cancel_right₀ _ hy]
      rw [hy_div]
    _ = 2 * a / y * normQsq := by ring

lemma dx_cr_algebra (u v ux vx y b normQsq : ℝ)
  (hy : y ≠ 0) (hnorm : normQsq ≠ 0)
  (h_b : b = - y * (u * ux + v * vx) / normQsq) :
  2 * (u * ux + v * vx) = - 2 * b / y * normQsq := by
  calc
    2 * (u * ux + v * vx)
      = - 2 * (b * normQsq / y) := by
      rw [h_b]
      have hy_div : (- y * (u * ux + v * vx) / normQsq) * normQsq / y = - (u * ux + v * vx) := by
        rw [div_mul_cancel₀ _ hnorm]
        calc (- y * (u * ux + v * vx)) / y = (- (u * ux + v * vx)) * y / y := by ring
        _ = - (u * ux + v * vx) := by rw [mul_div_cancel_right₀ _ hy]
      rw [hy_div]
      ring
    _ = - 2 * b / y * normQsq := by ring

-- Pointwise identities for |Q_F|^2
lemma dy_norm_Q_sq (F : KClass) (z : ℂ) (hz : z ∈ H) :
  deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2) z.im = 2 * a F z / z.im * ‖Q F.F z‖^2 := by
  -- Follows from dy_cr_algebra by evaluating the real/imaginary parts of Q and its derivative.
  sorry

lemma dx_norm_Q_sq (F : KClass) (z : ℂ) (hz : z ∈ H) :
  deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2) z.re = -2 * b F z / z.im * ‖Q F.F z‖^2 := by
  -- Follows from dx_cr_algebra
  sorry

lemma laplacian_norm_Q_sq (F : KClass) (z : ℂ) (hz : z ∈ H) :
  deriv (deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2)) z.re +
  deriv (deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2)) z.im =
  4 * ‖deriv (Q F.F) z‖^2 := by
  -- Follows from laplacian_cr_algebra 
  sorry

/-!
PAPER: At i we have QF(i) = 1, so the y derivative, the x derivative, and the Euclidean Laplacian
PAPER: of (3.10) give, respectively,
PAPER: 2EaF(i) = -β, 2EbF(i) = 0, 4E|qF(i)|^2 = β(β + 1).
-/
-- (This forms the proof structure for the moment equalities above)

end Brennan.Section3
