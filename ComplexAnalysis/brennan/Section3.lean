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
{
  dsimp [q]
  have h_Q_def_2 : Q F.F = fun x => 1 / deriv F.F x := by
  {
    ext x
    dsimp [Q]
  }
  rw [h_Q_def_2]
  have h_deriv : deriv (fun x => 1 / deriv F.F x) z = - deriv (deriv F.F) z / (deriv F.F z)^2 := by
  {
    have h_rw : (fun x => 1 / deriv F.F x) = (fun x => (deriv F.F x)⁻¹) := by
    {
      ext x
      rw [one_div]
    }
    rw [h_rw]
    exact deriv_inv'' h2 h1
  }
  rw [h_deriv]
  field_simp
}

-- The real part a_F(z)
def a (F : KClass) (z : ℂ) : ℝ := (q F z).re

-- The imaginary part b_F(z)
def b (F : KClass) (z : ℂ) : ℝ := (q F z).im

lemma Q_at_I (F : KClass) : Q F.F I = 1 := by
{
  simp [Q, F.norm_deriv]
}

lemma norm_Q_at_I_sq (F : KClass) : ‖Q F.F I‖^2 = 1 := by
{
  rw [Q_at_I, norm_one, one_pow]
}

lemma norm_q_at_I_sq (F : KClass) : ‖q F I‖^2 = ‖deriv (Q F.F) I‖^2 := by
{
  dsimp [q]
  simp [Q_at_I]
}

lemma hasDerivAt_Q (F : KClass) {z : ℂ} (hz : z ∈ H) :
    HasDerivAt (Q F.F) (deriv (Q F.F) z) z := by
{
  have han : AnalyticAt ℂ F.F z := F.univalent.1.analyticOnNhd isOpen_H z hz
  have hd : deriv F.F z ≠ 0 := deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz
  have h_eq : Q F.F = fun u => (deriv F.F u)⁻¹ := by
  {
    ext u
    simp [Q]
  }
  rw [h_eq]
  exact (han.deriv.differentiableAt.inv hd).hasDerivAt
}

lemma analyticAt_Q (F : KClass) {z : ℂ} (hz : z ∈ H) :
    AnalyticAt ℂ (Q F.F) z := by
{
  have h_diff : DifferentiableOn ℂ (Q F.F) H := by
  {
    intro w hw
    exact (hasDerivAt_Q F hw).differentiableAt.differentiableWithinAt
  }
  exact h_diff.analyticOnNhd isOpen_H z hz
}

lemma hasDerivAt_deriv_Q (F : KClass) {z : ℂ} (hz : z ∈ H) :
    HasDerivAt (deriv (Q F.F)) (deriv (deriv (Q F.F)) z) z := by
{
  exact (analyticAt_Q F hz).deriv.differentiableAt.hasDerivAt
}

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
{
  calc
    2 * (ux * ux + uy * uy + vx * vx + vy * vy)
      = 2 * (ux * ux + (-vx) * (-vx) + vx * vx + ux * ux) := by rw [hCR1, hCR2]
    _ = 4 * (ux * ux + vx * vx) := by ring
}

lemma dy_cr_algebra (u v ux uy vx vy y a normQsq : ℝ)
    (hCR1 : ux = vy) (hCR2 : uy = -vx)
    (hy : y ≠ 0) (hnorm : normQsq ≠ 0)
    (h_a : a = y * (v * ux - u * vx) / normQsq) :
    2 * (u * uy + v * vy) = 2 * a / y * normQsq := by
{
  calc
    2 * (u * uy + v * vy)
      = 2 * (u * (-vx) + v * ux) := by rw [hCR1, hCR2]
    _ = 2 * (v * ux - u * vx) := by ring
    _ = 2 * (a * normQsq / y) := by
    {
      rw [h_a]
      have hy_div : (y * (v * ux - u * vx) / normQsq) * normQsq / y = (v * ux - u * vx) := by
      {
        rw [div_mul_cancel₀ _ hnorm]
        calc (y * (v * ux - u * vx)) / y = (v * ux - u * vx) * y / y := by ring
        _ = (v * ux - u * vx) := by rw [mul_div_cancel_right₀ _ hy]
      }
      rw [hy_div]
    }
    _ = 2 * a / y * normQsq := by ring
}

lemma dx_cr_algebra (u v ux vx y b normQsq : ℝ)
    (hy : y ≠ 0) (hnorm : normQsq ≠ 0)
    (h_b : b = - y * (u * ux + v * vx) / normQsq) :
    2 * (u * ux + v * vx) = - 2 * b / y * normQsq := by
{
  calc
    2 * (u * ux + v * vx)
      = - 2 * (b * normQsq / y) := by
    {
      rw [h_b]
      have hy_div : (- y * (u * ux + v * vx) / normQsq) * normQsq / y = - (u * ux + v * vx) := by
      {
        rw [div_mul_cancel₀ _ hnorm]
        calc (- y * (u * ux + v * vx)) / y = (- (u * ux + v * vx)) * y / y := by ring
        _ = - (u * ux + v * vx) := by rw [mul_div_cancel_right₀ _ hy]
      }
      rw [hy_div]
      ring
    }
    _ = - 2 * b / y * normQsq := by ring
}

lemma hasDerivAt_line_x (x₀ y₀ : ℝ) :
    HasDerivAt (fun x : ℝ => (x : ℂ) + y₀ • I) 1 x₀ := by
{
  have h1 : HasDerivAt (fun x : ℝ => (x : ℂ)) 1 x₀ := Complex.ofRealCLM.hasDerivAt
  simpa using h1.add_const (y₀ • I)
}

lemma hasDerivAt_line_y (x₀ y₀ : ℝ) :
    HasDerivAt (fun y : ℝ => (x₀ : ℂ) + y • I) I y₀ := by
{
  have h1 : HasDerivAt (fun y : ℝ => (y : ℂ) * I) ((1 : ℂ) * I) y₀ :=
    Complex.ofRealCLM.hasDerivAt.mul_const I
  have h2 := h1.const_add (x₀ : ℂ)
  simpa [Complex.real_smul] using h2
}

lemma line_pt_eq (z : ℂ) : (z.re : ℂ) + z.im • I = z := by
{
  rw [Complex.real_smul]
  exact Complex.re_add_im z
}

lemma complex_line_deriv_y {g : ℂ → ℂ} {x₀ y₀ : ℝ} {d : ℂ}
    (hg : HasDerivAt g d ((x₀ : ℂ) + y₀ • I)) :
    HasDerivAt (fun y : ℝ => g ((x₀ : ℂ) + y • I)) (d * I) y₀ := by
{
  convert HasDerivAt.comp (𝕜 := ℝ) y₀ hg (hasDerivAt_line_y x₀ y₀) using 1 <;> rfl
}

lemma complex_line_deriv_x {g : ℂ → ℂ} {x₀ y₀ : ℝ} {d : ℂ}
    (hg : HasDerivAt g d ((x₀ : ℂ) + y₀ • I)) :
    HasDerivAt (fun x : ℝ => g ((x : ℂ) + y₀ • I)) (d * 1) x₀ := by
{
  convert HasDerivAt.comp (𝕜 := ℝ) x₀ hg (hasDerivAt_line_x x₀ y₀) using 1 <;> rfl
}

lemma hasDerivAt_Q_line_y (F : KClass) (z : ℂ) (hz : z ∈ H) :
    HasDerivAt (fun y : ℝ => Q F.F (z.re + y • I)) (deriv (Q F.F) z * I) z.im := by
{
  have hQ : HasDerivAt (Q F.F) (deriv (Q F.F) z) ((z.re : ℂ) + z.im • I) := by
  {
    rw [line_pt_eq z]
    exact hasDerivAt_Q F hz
  }
  exact complex_line_deriv_y hQ
}

lemma hasDerivAt_Q_line_x (F : KClass) (z : ℂ) (hz : z ∈ H) :
    HasDerivAt (fun x : ℝ => Q F.F (x + z.im • I)) (deriv (Q F.F) z * 1) z.re := by
{
  have hQ : HasDerivAt (Q F.F) (deriv (Q F.F) z) ((z.re : ℂ) + z.im • I) := by
  {
    rw [line_pt_eq z]
    exact hasDerivAt_Q F hz
  }
  exact complex_line_deriv_x hQ
}

lemma inner_Q_deriv_I_eq (F : KClass) (z : ℂ) (hz : z ∈ H) :
    2 * inner ℝ (Q F.F z) (deriv (Q F.F) z * I) = 2 * a F z / z.im * ‖Q F.F z‖^2 := by
{
  dsimp [a, q]
  have hy : z.im ≠ 0 := ne_of_gt hz
  have hQ_ne : Q F.F z ≠ 0 := one_div_ne_zero (deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz)
  rw [← Complex.normSq_eq_norm_sq]
  have hnorm : Complex.normSq (Q F.F z) ≠ 0 := by
  {
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hQ_ne)
  }
  change 2 * (deriv (Q F.F) z * I * conj (Q F.F z)).re = _
  simp only [Complex.div_re, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.conj_re, Complex.conj_im]
  field_simp
  ring
}

lemma inner_Q_deriv_one_eq (F : KClass) (z : ℂ) (hz : z ∈ H) :
    2 * inner ℝ (Q F.F z) (deriv (Q F.F) z * 1) = 2 * b F z / z.im * ‖Q F.F z‖^2 := by
{
  dsimp [b, q]
  have hy : z.im ≠ 0 := ne_of_gt hz
  have hQ_ne : Q F.F z ≠ 0 := one_div_ne_zero (deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz)
  rw [← Complex.normSq_eq_norm_sq]
  have hnorm : Complex.normSq (Q F.F z) ≠ 0 := by
  {
    rw [Complex.normSq_eq_norm_sq]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hQ_ne)
  }
  change 2 * (deriv (Q F.F) z * 1 * conj (Q F.F z)).re = _
  simp only [Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.ofReal_re, Complex.ofReal_im,
    mul_one, Complex.conj_re, Complex.conj_im]
  field_simp
  ring
}

-- Pointwise identities for |Q_F|^2
lemma dy_norm_Q_sq (F : KClass) (z : ℂ) (hz : z ∈ H) :
    deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2) z.im = 2 * a F z / z.im * ‖Q F.F z‖^2 := by
{
  have hd := (hasDerivAt_Q_line_y F z hz).norm_sq
  rw [line_pt_eq z] at hd
  rw [hd.deriv, inner_Q_deriv_I_eq F z hz]
}

lemma dx_norm_Q_sq (F : KClass) (z : ℂ) (hz : z ∈ H) :
    deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2) z.re = 2 * b F z / z.im * ‖Q F.F z‖^2 := by
{
  have hd := (hasDerivAt_Q_line_x F z hz).norm_sq
  rw [line_pt_eq z] at hd
  rw [hd.deriv, inner_Q_deriv_one_eq F z hz]
}

lemma second_deriv_norm_Q_sq_x (F : KClass) (z : ℂ) (hz : z ∈ H) :
    deriv (deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2)) z.re =
    2 * (inner ℝ (deriv (Q F.F) z * 1) (deriv (Q F.F) z * 1) +
         inner ℝ (Q F.F z) ((deriv (deriv (Q F.F)) z * 1) * 1)) := by
{
  have h_eq : deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2) =
      fun x : ℝ => 2 * inner ℝ (Q F.F (x + z.im • I)) (deriv (Q F.F) (x + z.im • I) * 1) := by
  {
    ext x
    let w : ℂ := (x : ℂ) + z.im • I
    have hw : w ∈ H := by dsimp [H, w]; simp; exact hz
    have hre : w.re = x := by simp [w, Complex.real_smul]
    have him : w.im = z.im := by simp [w, Complex.real_smul]
    have hd := (hasDerivAt_Q_line_x F w hw).norm_sq
    rw [line_pt_eq w] at hd
    simpa [w, hre, him] using hd.deriv
  }
  rw [h_eq]
  have hQ1 := hasDerivAt_Q_line_x F z hz
  have hQ2 : HasDerivAt (fun x : ℝ => deriv (Q F.F) (x + z.im • I)) (deriv (deriv (Q F.F)) z * 1) z.re := by
  {
    have hD : HasDerivAt (deriv (Q F.F)) (deriv (deriv (Q F.F)) z) ((z.re : ℂ) + z.im • I) := by
    {
      rw [line_pt_eq z]
      exact hasDerivAt_deriv_Q F hz
    }
    exact complex_line_deriv_x hD
  }
  have hd2 := ((hQ1.inner ℝ (hQ2.mul_const 1)).const_mul 2)
  rw [line_pt_eq z] at hd2
  rw [hd2.deriv, add_comm]
}

lemma second_deriv_norm_Q_sq_y (F : KClass) (z : ℂ) (hz : z ∈ H) :
    deriv (deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2)) z.im =
    2 * (inner ℝ (deriv (Q F.F) z * I) (deriv (Q F.F) z * I) +
         inner ℝ (Q F.F z) ((deriv (deriv (Q F.F)) z * I) * I)) := by
{
  have h_eq : deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2) =ᶠ[𝓝 z.im]
      fun y : ℝ => 2 * inner ℝ (Q F.F (z.re + y • I)) (deriv (Q F.F) (z.re + y • I) * I) := by
  {
    filter_upwards [isOpen_Ioi.mem_nhds hz] with y hy
    let w : ℂ := (z.re : ℂ) + y • I
    have hw : w ∈ H := by dsimp [H, w]; simp; exact hy
    have hre : w.re = z.re := by simp [w, Complex.real_smul]
    have him : w.im = y := by simp [w, Complex.real_smul]
    have hd := (hasDerivAt_Q_line_y F w hw).norm_sq
    rw [line_pt_eq w] at hd
    simpa [w, hre, him] using hd.deriv
  }
  have hQ1 := hasDerivAt_Q_line_y F z hz
  have hQ2 : HasDerivAt (fun y : ℝ => deriv (Q F.F) (z.re + y • I)) (deriv (deriv (Q F.F)) z * I) z.im := by
  {
    have hD : HasDerivAt (deriv (Q F.F)) (deriv (deriv (Q F.F)) z) ((z.re : ℂ) + z.im • I) := by
    {
      rw [line_pt_eq z]
      exact hasDerivAt_deriv_Q F hz
    }
    exact complex_line_deriv_y hD
  }
  have hd2 := ((hQ1.inner ℝ (hQ2.mul_const I)).const_mul 2).congr_of_eventuallyEq h_eq
  rw [line_pt_eq z] at hd2
  rw [hd2.deriv, add_comm]
}

lemma laplacian_norm_Q_sq (F : KClass) (z : ℂ) (hz : z ∈ H) :
    deriv (deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2)) z.re +
    deriv (deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2)) z.im =
    4 * ‖deriv (Q F.F) z‖^2 := by
{
  rw [second_deriv_norm_Q_sq_x F z hz, second_deriv_norm_Q_sq_y F z hz]
  simp only [mul_one]
  rw [real_inner_self_eq_norm_sq, real_inner_self_eq_norm_sq]
  simp only [Complex.norm_mul, Complex.norm_I, mul_one]
  have he : (deriv (deriv (Q F.F)) z * I) * I = - deriv (deriv (Q F.F)) z := by
  {
    rw [mul_assoc, Complex.I_mul_I, mul_neg_one]
  }
  rw [he, inner_neg_right]
  ring
}

/-!
PAPER: They also satisfy
PAPER: qTzF (w) = qF (z · w), z, w ∈ H. (3.9)
-/
-- Covariance of q under the affine transfer operator
lemma q_T_eq (F : KClass) (z w : ℂ) (hz : z ∈ H) (hw : w ∈ H) :
    q ⟨T z F.F, (T_KClass F z hz).1, (T_KClass F z hz).2.1, (T_KClass F z hz).2.2⟩ w = q F (aff z w) := by
{
  dsimp [q]
  have hz_im : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have h_im_aff : (aff z w).im = z.im * w.im := by dsimp [aff]; simp
  have hF_aff : DifferentiableAt ℂ F.F (aff z w) :=
    (F.univalent.1 (aff z w) (aff_mem_H hz hw)).differentiableAt (isOpen_H.mem_nhds (aff_mem_H hz hw))
  have h_Q_val : Q (T z F.F) w = Q F.F (aff z w) / Q F.F z := lemma_2_3_Q F.F z w hF_aff hz_im
  have heq : Q (T z F.F) =ᶠ[𝓝 w] (fun u => Q F.F (aff z u) / Q F.F z) := by
  {
    filter_upwards [isOpen_H.mem_nhds hw] with u hu
    have hF_u : DifferentiableAt ℂ F.F (aff z u) :=
      (F.univalent.1 (aff z u) (aff_mem_H hz hu)).differentiableAt (isOpen_H.mem_nhds (aff_mem_H hz hu))
    exact lemma_2_3_Q F.F z u hF_u hz_im
  }
  have hd_aff : HasDerivAt (aff z) (z.im : ℂ) w := by
  {
    convert (hasDerivAt_const w (z.re : ℂ)).add ((hasDerivAt_id w).const_mul (z.im : ℂ)) using 1 <;>
      first | rfl | simp
  }
  have h_deriv_Q : deriv (Q (T z F.F)) w = (deriv (Q F.F) (aff z w) * z.im) / Q F.F z :=
    ((((hasDerivAt_Q F (aff_mem_H hz hw)).comp w hd_aff).div_const (Q F.F z)).congr_of_eventuallyEq heq).deriv
  rw [h_deriv_Q, h_Q_val, h_im_aff]
  push_cast
  have h_Q_z_ne_zero : Q F.F z ≠ 0 :=
    one_div_ne_zero (deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz)
  field_simp
}

/-!
PAPER: The variables qF (i) are bounded on K, and
PAPER: EaF(i) = -β / 2, EbF(i) = 0, E|qF(i)|^2 = β(β + 1) / 4. (3.8)
-/
lemma continuous_Q_eval (w : ℂ) : Continuous (fun F : KClass => Q F.F w) := by
{
  exact (continuous_apply w).comp
    (continuous_fst.comp (continuous_snd.comp (continuous_induced_dom (f := kClassJet))))
}

lemma continuous_deriv_Q_eval (w : ℂ) : Continuous (fun F : KClass => deriv (Q F.F) w) := by
{
  exact (continuous_apply w).comp
    (continuous_fst.comp (continuous_snd.comp (continuous_snd.comp (continuous_induced_dom (f := kClassJet)))))
}

lemma continuous_deriv2_Q_eval (w : ℂ) :
    Continuous (fun F : KClass => deriv (deriv (Q F.F)) w) := by
{
  exact (continuous_apply w).comp
    (continuous_snd.comp (continuous_snd.comp (continuous_snd.comp (continuous_induced_dom (f := kClassJet)))))
}

def Q_ball_bound (z : ℂ) : ℝ :=
  (((‖z‖ + z.im / 2)^2 + (3 * z.im / 2 + 1)^2)^2) / (z.im / 2)

def Q_deriv_bound (z : ℂ) : ℝ :=
  Q_ball_bound z / (z.im / 4)

def Q_deriv2_bound (z : ℂ) : ℝ :=
  2 * Q_ball_bound z / (z.im / 4)^2

lemma closedBall_half_im_bounds {z w : ℂ} (hw : w ∈ Metric.closedBall z (z.im / 2)) :
    z.im / 2 ≤ w.im ∧ w.im ≤ 3 * z.im / 2 ∧ |w.re| ≤ ‖z‖ + z.im / 2 := by
{
  have hwz : ‖w - z‖ ≤ z.im / 2 := by simpa only [dist_eq_norm] using Metric.mem_closedBall.mp hw
  have him : |w.im - z.im| ≤ z.im / 2 := by
  {
    simpa only [Complex.sub_im] using (Complex.abs_im_le_norm (w - z)).trans hwz
  }
  obtain ⟨h1, h2⟩ := abs_le.mp him
  refine ⟨by linarith, by linarith, ?_⟩
  have hnorm : ‖w‖ ≤ ‖z‖ + z.im / 2 := by
  {
    calc ‖w‖ = ‖z + (w - z)‖ := by ring_nf
      _ ≤ ‖z‖ + ‖w - z‖ := norm_add_le _ _
      _ ≤ ‖z‖ + z.im / 2 := by linarith
  }
  exact (Complex.abs_re_le_norm w).trans hnorm
}

lemma norm_Q_le_on_closedBall (F : KClass) {z : ℂ} (hz : z ∈ H)
    {w : ℂ} (hw : w ∈ Metric.closedBall z (z.im / 2)) :
    ‖Q F.F w‖ ≤ Q_ball_bound z := by
{
  have hy : 0 < z.im := hz
  obtain ⟨hw1, hw2, hw3⟩ := closedBall_half_im_bounds hw
  have hwH : w ∈ H := by dsimp [H]; linarith
  have hgen := norm_Q_le_general F hwH
  have hre2 : w.re^2 ≤ (‖z‖ + z.im / 2)^2 := by
  {
    have hsq := (sq_le_sq₀ (abs_nonneg w.re) (by positivity)).mpr hw3
    nlinarith [sq_abs w.re]
  }
  have him2 : (w.im + 1)^2 ≤ (3 * z.im / 2 + 1)^2 := by nlinarith
  have hD2 : (w.re^2 + (w.im + 1)^2)^2 ≤ ((‖z‖ + z.im / 2)^2 + (3 * z.im / 2 + 1)^2)^2 :=
    sq_le_sq₀ (by positivity) (by positivity) |>.mpr (by linarith)
  exact hgen.trans (div_le_div₀ (by positivity) hD2 (by positivity) hw1)
}

lemma norm_iteratedDeriv_Q_le_on_closedBall (F : KClass) (n : ℕ) {z : ℂ} (hz : z ∈ H)
    {w : ℂ} (hw : w ∈ Metric.closedBall z (z.im / 4)) :
    ‖iteratedDeriv n (Q F.F) w‖ ≤ n.factorial * Q_ball_bound z / (z.im / 4) ^ n := by
{
  have hy : 0 < z.im := hz
  have hr : 0 < z.im / 4 := by positivity
  have hsub : Metric.closedBall w (z.im / 4) ⊆ Metric.closedBall z (z.im / 2) := by
  {
    intro u hu
    rw [Metric.mem_closedBall] at hu hw ⊢
    calc dist u z ≤ dist u w + dist w z := dist_triangle u w z
      _ ≤ z.im / 4 + z.im / 4 := add_le_add hu hw
      _ = z.im / 2 := by ring
  }
  have hd : DifferentiableOn ℂ (Q F.F) (Metric.closedBall w (z.im / 4)) := by
  {
    intro u hu
    have huH : u ∈ H := by
    {
      dsimp [H]
      linarith [(closedBall_half_im_bounds (hsub hu)).1]
    }
    exact (hasDerivAt_Q F huH).differentiableAt.differentiableWithinAt
  }
  have hdf : DiffContOnCl ℂ (Q F.F) (Metric.ball w (z.im / 4)) := by
  {
    apply DifferentiableOn.diffContOnCl
    rw [closure_ball w hr.ne']
    exact hd
  }
  exact Complex.norm_iteratedDeriv_le_of_forall_mem_sphere_norm_le n hr hdf
    (fun u hu => norm_Q_le_on_closedBall F hz (hsub (Metric.sphere_subset_closedBall hu)))
}

lemma norm_deriv_Q_le_on_closedBall (F : KClass) {z : ℂ} (hz : z ∈ H)
    {w : ℂ} (hw : w ∈ Metric.closedBall z (z.im / 4)) :
    ‖deriv (Q F.F) w‖ ≤ Q_deriv_bound z := by
{
  have h := norm_iteratedDeriv_Q_le_on_closedBall F 1 hz hw
  simpa [Q_deriv_bound] using h
}

lemma norm_deriv2_Q_le_on_closedBall (F : KClass) {z : ℂ} (hz : z ∈ H)
    {w : ℂ} (hw : w ∈ Metric.closedBall z (z.im / 4)) :
    ‖deriv (deriv (Q F.F)) w‖ ≤ Q_deriv2_bound z := by
{
  have h := norm_iteratedDeriv_Q_le_on_closedBall F 2 hz hw
  have hi2 : iteratedDeriv 2 (Q F.F) w = deriv (deriv (Q F.F)) w := by
  {
    rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_one]
  }
  rw [hi2, Nat.factorial_two, Nat.cast_ofNat] at h
  exact h
}

/-- Uniform bound on `‖q F I‖` over the compact class K (`OAI.Brennan.root_logarithmicJet_bounded` in `Moments.lean`). -/
theorem q_bounded_on_KClass : ∃ C : ℝ, ∀ F : KClass, ‖q F I‖ ≤ C := by
{
  have hzI : I ∈ H := by dsimp [H]; simp
  refine ⟨Q_deriv_bound I, fun F => ?_⟩
  have hq : ‖q F I‖ = ‖deriv (Q F.F) I‖ := by
  {
    dsimp [q]
    simp [Q_at_I]
  }
  rw [hq]
  exact norm_deriv_Q_le_on_closedBall F hzI (Metric.mem_closedBall_self (by dsimp; norm_num))
}

def normFirstQ (v w : ℂ) (F : KClass) : ℝ :=
  2 * inner ℝ (Q F.F w) (deriv (Q F.F) w * v)

def normSecondQ (v w : ℂ) (F : KClass) : ℝ :=
  2 * (inner ℝ (deriv (Q F.F) w * v) (deriv (Q F.F) w * v) +
       inner ℝ (Q F.F w) ((deriv (deriv (Q F.F)) w * v) * v))

lemma continuous_norm_Q_sq (w : ℂ) : Continuous (fun F : KClass => ‖Q F.F w‖^2) := by
{
  have hQ := continuous_Q_eval w
  fun_prop
}

lemma continuous_normFirstQ (v w : ℂ) : Continuous (normFirstQ v w) := by
{
  unfold normFirstQ
  have hQ := continuous_Q_eval w
  have hdQ := continuous_deriv_Q_eval w
  fun_prop
}

lemma continuous_normSecondQ (v w : ℂ) : Continuous (normSecondQ v w) := by
{
  unfold normSecondQ
  have hQ := continuous_Q_eval w
  have hdQ := continuous_deriv_Q_eval w
  have hd2Q := continuous_deriv2_Q_eval w
  fun_prop
}

lemma norm_normFirstQ_le (F : KClass) {z v w : ℂ} (hz : z ∈ H) (hv : ‖v‖ = 1)
    (hw : w ∈ Metric.closedBall z (z.im / 4)) :
    ‖normFirstQ v w F‖ ≤ 2 * Q_ball_bound z * Q_deriv_bound z := by
{
  have hw2 : w ∈ Metric.closedBall z (z.im / 2) :=
    Metric.closedBall_subset_closedBall (by linarith [show 0 < z.im from hz]) hw
  have h0 := norm_Q_le_on_closedBall F hz hw2
  have h1 := norm_deriv_Q_le_on_closedBall F hz hw
  have hB0 : 0 ≤ Q_ball_bound z := (norm_nonneg _).trans h0
  unfold normFirstQ
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2), mul_assoc]
  gcongr
  calc |inner ℝ (Q F.F w) (deriv (Q F.F) w * v)|
      ≤ ‖Q F.F w‖ * ‖deriv (Q F.F) w * v‖ := abs_real_inner_le_norm _ _
    _ = ‖Q F.F w‖ * ‖deriv (Q F.F) w‖ := by rw [norm_mul, hv, mul_one]
    _ ≤ Q_ball_bound z * Q_deriv_bound z := mul_le_mul h0 h1 (norm_nonneg _) hB0
}

lemma norm_normSecondQ_le (F : KClass) {z v w : ℂ} (hz : z ∈ H) (hv : ‖v‖ = 1)
    (hw : w ∈ Metric.closedBall z (z.im / 4)) :
    ‖normSecondQ v w F‖ ≤
      2 * (Q_deriv_bound z ^ 2 + Q_ball_bound z * Q_deriv2_bound z) := by
{
  have hw2 : w ∈ Metric.closedBall z (z.im / 2) :=
    Metric.closedBall_subset_closedBall (by linarith [show 0 < z.im from hz]) hw
  have h0 := norm_Q_le_on_closedBall F hz hw2
  have h1 := norm_deriv_Q_le_on_closedBall F hz hw
  have h2 := norm_deriv2_Q_le_on_closedBall F hz hw
  have hB0 : 0 ≤ Q_ball_bound z := (norm_nonneg _).trans h0
  have hB1 : 0 ≤ Q_deriv_bound z := (norm_nonneg _).trans h1
  unfold normSecondQ
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 2)]
  gcongr
  refine (abs_add_le _ _).trans (add_le_add ?_ ?_)
  · calc |inner ℝ (deriv (Q F.F) w * v) (deriv (Q F.F) w * v)|
        ≤ ‖deriv (Q F.F) w * v‖ * ‖deriv (Q F.F) w * v‖ := abs_real_inner_le_norm _ _
      _ = ‖deriv (Q F.F) w‖ ^ 2 := by rw [norm_mul, hv, mul_one, sq]
      _ ≤ Q_deriv_bound z ^ 2 := sq_le_sq₀ (norm_nonneg _) hB1 |>.mpr h1
  · calc |inner ℝ (Q F.F w) ((deriv (deriv (Q F.F)) w * v) * v)|
        ≤ ‖Q F.F w‖ * ‖(deriv (deriv (Q F.F)) w * v) * v‖ := abs_real_inner_le_norm _ _
      _ = ‖Q F.F w‖ * ‖deriv (deriv (Q F.F)) w‖ := by rw [norm_mul, norm_mul, hv, mul_one, mul_one]
      _ ≤ Q_ball_bound z * Q_deriv2_bound z := mul_le_mul h0 h2 (norm_nonneg _) hB0
}

lemma hasDerivAt_norm_Q_sq_along (F : KClass) {γ : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hγ : HasDerivAt γ v t) (hH : γ t ∈ H) :
    HasDerivAt (fun s => ‖Q F.F (γ s)‖^2) (normFirstQ v (γ t) F) t := by
{
  have hd : HasDerivAt (fun s => Q F.F (γ s)) (deriv (Q F.F) (γ t) * v) t := by
  {
    convert HasDerivAt.comp (𝕜 := ℝ) t (hasDerivAt_Q F hH) hγ using 1 <;> rfl
  }
  exact hd.norm_sq
}

lemma hasDerivAt_normFirstQ_along (F : KClass) {γ : ℝ → ℂ} {v : ℂ} {t : ℝ}
    (hγ : HasDerivAt γ v t) (hH : γ t ∈ H) :
    HasDerivAt (fun s => normFirstQ v (γ s) F) (normSecondQ v (γ t) F) t := by
{
  have hd1 : HasDerivAt (fun s => Q F.F (γ s)) (deriv (Q F.F) (γ t) * v) t := by
  {
    convert HasDerivAt.comp (𝕜 := ℝ) t (hasDerivAt_Q F hH) hγ using 1 <;> rfl
  }
  have hd2 : HasDerivAt (fun s => deriv (Q F.F) (γ s)) (deriv (deriv (Q F.F)) (γ t) * v) t := by
  {
    convert HasDerivAt.comp (𝕜 := ℝ) t (hasDerivAt_deriv_Q F hH) hγ using 1 <;> rfl
  }
  simpa only [normFirstQ, normSecondQ, add_comm] using
    ((hd1.inner ℝ (hd2.mul_const v)).const_mul 2)
}

lemma hasDerivAt_integral_of_uniform_bound (P : Measure KClass) [IsFiniteMeasure P]
    (Φ Φ' : ℝ → KClass → ℝ) {U : Set ℝ} {t C₀ C₁ : ℝ} (hU : U ∈ 𝓝 t) (ht : t ∈ U)
    (hΦc : ∀ s ∈ U, Continuous (Φ s))
    (hΦ'c : Continuous (Φ' t))
    (hb0 : ∀ F, ‖Φ t F‖ ≤ C₀)
    (hb1 : ∀ F, ∀ s ∈ U, ‖Φ' s F‖ ≤ C₁)
    (hd : ∀ F, ∀ s ∈ U, HasDerivAt (fun u => Φ u F) (Φ' s F) s) :
    Integrable (Φ' t) P ∧
      HasDerivAt (fun s => ∫ F, Φ s F ∂P) (∫ F, Φ' t F ∂P) t := by
{
  refine hasDerivAt_integral_of_dominated_loc_of_deriv_le hU
    ?_ ?_ hΦ'c.aestronglyMeasurable
    (Eventually.of_forall hb1) (integrable_const C₁) (Eventually.of_forall hd)
  · filter_upwards [hU] with s hs
    exact (hΦc s hs).aestronglyMeasurable
  · exact (integrable_const C₀).mono' (hΦc t ht).aestronglyMeasurable
      (Eventually.of_forall hb0)
}

lemma closedBall_quarter_subset_H {z : ℂ} (hz : z ∈ H)
    {w : ℂ} (hw : w ∈ Metric.closedBall z (z.im / 4)) : w ∈ H := by
{
  have hw2 : w ∈ Metric.closedBall z (z.im / 2) :=
    Metric.closedBall_subset_closedBall (by linarith [show 0 < z.im from hz]) hw
  dsimp [H]
  linarith [show 0 < z.im from hz, (closedBall_half_im_bounds hw2).1]
}

lemma hasDerivAt_integral_along_line (P : Measure KClass) [IsFiniteMeasure P]
    {z v : ℂ} (hz : z ∈ H) (hv : ‖v‖ = 1) {γ : ℝ → ℂ} {t₀ t : ℝ}
    (hγ : ∀ s, HasDerivAt γ v s)
    (hball : ∀ s ∈ Metric.ball t₀ (z.im / 4), γ s ∈ Metric.closedBall z (z.im / 4))
    (ht : t ∈ Metric.ball t₀ (z.im / 4)) :
    HasDerivAt (fun s => ∫ F, ‖Q F.F (γ s)‖^2 ∂P)
      (∫ F, normFirstQ v (γ t) F ∂P) t := by
{
  have hU : Metric.ball t₀ (z.im / 4) ∈ 𝓝 t := Metric.isOpen_ball.mem_nhds ht
  have hw2 : γ t ∈ Metric.closedBall z (z.im / 2) :=
    Metric.closedBall_subset_closedBall (by linarith [show 0 < z.im from hz]) (hball t ht)
  refine (hasDerivAt_integral_of_uniform_bound P
    (fun s F => ‖Q F.F (γ s)‖^2) (fun s F => normFirstQ v (γ s) F)
    (C₀ := Q_ball_bound z ^ 2) hU ht
    (fun s _ => continuous_norm_Q_sq (γ s)) (continuous_normFirstQ v (γ t))
    (fun F => ?_) (fun F s hs => norm_normFirstQ_le F hz hv (hball s hs))
    (fun F s hs => hasDerivAt_norm_Q_sq_along F (hγ s) (closedBall_quarter_subset_H hz (hball s hs)))).2
  rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  have h0 := norm_Q_le_on_closedBall F hz hw2
  exact sq_le_sq₀ (norm_nonneg _) ((norm_nonneg _).trans h0) |>.mpr h0
}

lemma deriv2_integral_along_line (P : Measure KClass) [IsFiniteMeasure P]
    {z v : ℂ} (hz : z ∈ H) (hv : ‖v‖ = 1) {γ : ℝ → ℂ} {t₀ : ℝ}
    (hγ : ∀ s, HasDerivAt γ v s)
    (hball : ∀ s ∈ Metric.ball t₀ (z.im / 4), γ s ∈ Metric.closedBall z (z.im / 4)) :
    Integrable (fun F => deriv (deriv (fun s => ‖Q F.F (γ s)‖^2)) t₀) P ∧
      deriv (deriv (fun s => ∫ F, ‖Q F.F (γ s)‖^2 ∂P)) t₀ =
        ∫ F, deriv (deriv (fun s => ‖Q F.F (γ s)‖^2)) t₀ ∂P := by
{
  have hr : 0 < z.im / 4 := by linarith [show 0 < z.im from hz]
  have ht0 : t₀ ∈ Metric.ball t₀ (z.im / 4) := Metric.mem_ball_self hr
  have hU : Metric.ball t₀ (z.im / 4) ∈ 𝓝 t₀ := Metric.isOpen_ball.mem_nhds ht0
  have hstep2 := hasDerivAt_integral_of_uniform_bound P
    (fun s F => normFirstQ v (γ s) F) (fun s F => normSecondQ v (γ s) F) hU ht0
    (fun s _ => continuous_normFirstQ v (γ s)) (continuous_normSecondQ v (γ t₀))
    (fun F => norm_normFirstQ_le F hz hv (hball t₀ ht0))
    (fun F s hs => norm_normSecondQ_le F hz hv (hball s hs))
    (fun F s hs => hasDerivAt_normFirstQ_along F (hγ s) (closedBall_quarter_subset_H hz (hball s hs)))
  have hev_int : deriv (fun s => ∫ F, ‖Q F.F (γ s)‖^2 ∂P) =ᶠ[𝓝 t₀]
      fun s => ∫ F, normFirstQ v (γ s) F ∂P := by
  {
    filter_upwards [hU] with s hs
    exact (hasDerivAt_integral_along_line P hz hv hγ hball hs).deriv
  }
  have hpt (F : KClass) : deriv (deriv (fun s => ‖Q F.F (γ s)‖^2)) t₀ = normSecondQ v (γ t₀) F := by
  {
    have hev : deriv (fun s => ‖Q F.F (γ s)‖^2) =ᶠ[𝓝 t₀] fun s => normFirstQ v (γ s) F := by
    {
      filter_upwards [hU] with s hs
      exact (hasDerivAt_norm_Q_sq_along F (hγ s) (closedBall_quarter_subset_H hz (hball s hs))).deriv
    }
    rw [hev.deriv_eq]
    exact (hasDerivAt_normFirstQ_along F (hγ t₀) (closedBall_quarter_subset_H hz (hball t₀ ht0))).deriv
  }
  simp_rw [hpt]
  exact ⟨hstep2.1, hev_int.deriv_eq.trans hstep2.2.deriv⟩
}

lemma line_y_mem_closedBall {z : ℂ} {y : ℝ} (hy : y ∈ Metric.ball z.im (z.im / 4)) :
    (z.re : ℂ) + y • I ∈ Metric.closedBall z (z.im / 4) := by
{
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hdiff : ((z.re : ℂ) + y • I) - z = ((y - z.im) : ℂ) * I := by
  {
    have hz_eq := line_pt_eq z
    simp only [Complex.real_smul] at hz_eq ⊢
    linear_combination hz_eq
  }
  rw [hdiff, norm_mul, Complex.norm_I, mul_one, ← Complex.ofReal_sub,
    Complex.norm_real, Real.norm_eq_abs]
  exact (Metric.mem_ball.mp hy).le
}

lemma line_x_mem_closedBall {z : ℂ} {x : ℝ} (hx : x ∈ Metric.ball z.re (z.im / 4)) :
    (x : ℂ) + z.im • I ∈ Metric.closedBall z (z.im / 4) := by
{
  rw [Metric.mem_closedBall, dist_eq_norm]
  have hdiff : ((x : ℂ) + z.im • I) - z = ((x - z.re) : ℂ) := by
  {
    have hz_eq := line_pt_eq z
    simp only [Complex.real_smul] at hz_eq ⊢
    linear_combination hz_eq
  }
  rw [hdiff, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  exact (Metric.mem_ball.mp hx).le
}

/-- Differentiation under the integral sign on the compact family K (`OAI.Brennan.hasDerivAt_integral_compact` in `Moments.lean`). -/
theorem deriv_integral_y (P : Measure KClass) [IsFiniteMeasure P] (z : ℂ) (hz : z ∈ H) :
    deriv (fun y : ℝ => ∫ F, ‖Q F.F (z.re + y • I)‖^2 ∂P) z.im =
    ∫ F, deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2) z.im ∂P := by
{
  have hr : 0 < z.im / 4 := by linarith [show 0 < z.im from hz]
  have hd := hasDerivAt_integral_along_line P hz Complex.norm_I (hasDerivAt_line_y z.re)
    (fun _ hy => line_y_mem_closedBall hy) (Metric.mem_ball_self hr)
  rw [hd.deriv]
  congr 1
  ext F
  have hpt := (hasDerivAt_Q_line_y F z hz).norm_sq
  simpa [normFirstQ, line_pt_eq z] using hpt.deriv.symm
}

/-- Differentiation under the integral sign wrt x on K (`OAI.Brennan.hasDerivAt_integral_compact` in `Moments.lean`). -/
theorem deriv_integral_x (P : Measure KClass) [IsFiniteMeasure P] (z : ℂ) (hz : z ∈ H) :
    deriv (fun x : ℝ => ∫ F, ‖Q F.F (x + z.im • I)‖^2 ∂P) z.re =
    ∫ F, deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2) z.re ∂P := by
{
  have hr : 0 < z.im / 4 := by linarith [show 0 < z.im from hz]
  have hd := hasDerivAt_integral_along_line P hz norm_one (fun x => hasDerivAt_line_x x z.im)
    (fun _ hx => line_x_mem_closedBall hx) (Metric.mem_ball_self hr)
  rw [hd.deriv]
  congr 1
  ext F
  have hpt := (hasDerivAt_Q_line_x F z hz).norm_sq
  simpa [normFirstQ, line_pt_eq z] using hpt.deriv.symm
}

/-- Second derivative under the integral sign on K (`OAI.Brennan.integral_normFirst_line_derivative` in `Moments.lean`). -/
theorem deriv2_integral_laplacian (P : Measure KClass) [IsFiniteMeasure P] (z : ℂ) (hz : z ∈ H) :
    deriv (deriv (fun x : ℝ => ∫ F, ‖Q F.F (x + z.im • I)‖^2 ∂P)) z.re +
    deriv (deriv (fun y : ℝ => ∫ F, ‖Q F.F (z.re + y • I)‖^2 ∂P)) z.im =
    ∫ F, (deriv (deriv (fun x : ℝ => ‖Q F.F (x + z.im • I)‖^2)) z.re +
          deriv (deriv (fun y : ℝ => ‖Q F.F (z.re + y • I)‖^2)) z.im) ∂P := by
{
  have hx := deriv2_integral_along_line P hz norm_one (fun x => hasDerivAt_line_x x z.im)
    (fun _ h => line_x_mem_closedBall h)
  have hy := deriv2_integral_along_line P hz Complex.norm_I (hasDerivAt_line_y z.re)
    (fun _ h => line_y_mem_closedBall h)
  rw [hx.2, hy.2, ← integral_add hx.1 hy.1]
}

/-!
PAPER: Proof. Taking Φ = 1 in (3.1) gives
PAPER: E|QF (x + iy)|^2 = y^{-β}. (3.10)
-/
-- Expected value of |Q_F(z)|^2 over KClass (Equation 3.10)
lemma E_norm_Q_sq (P : Measure KClass) [IsProbabilityMeasure P] (beta : ℝ) (z : ℂ) (hz : z ∈ H)
    (h_P_eigen : ∀ (w : ℂ) (hw : w ∈ H) (Phi : KClass → ℝ),
      ∫ F, A_weight w F.F * Phi ⟨T w F.F, (T_KClass F w hw).1, (T_KClass F w hw).2.1, (T_KClass F w hw).2.2⟩ ∂P =
        (w.im : ℝ) ^ (-beta) * ∫ F, Phi F ∂P) :
    ∫ F, ‖Q F.F z‖^2 ∂P = (z.im : ℝ) ^ (-beta) := by
{
  have h1 := h_P_eigen z hz (fun _ => 1)
  simp only [A_weight, mul_one, integral_const, smul_eq_mul, probReal_univ] at h1
  exact h1
}

lemma E_a_eq (P : Measure KClass) [IsFiniteMeasure P] (beta : ℝ)
    (h_P_eigen : ∀ z ∈ H, ∫ F, ‖Q F.F z‖^2 ∂P = (z.im : ℝ) ^ (-beta)) :
    ∫ F, a F I ∂P = -beta / 2 := by
{
  have hz_I : I ∈ H := by dsimp [H]; simp
  have h_ev : (fun y : ℝ => ∫ F, ‖Q F.F ((0 : ℝ) + y • I)‖^2 ∂P) =ᶠ[𝓝 1] (fun y : ℝ => y ^ (-beta)) := by
  {
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1)] with y hy
    have hyH : ((0 : ℝ) : ℂ) + y • I ∈ H := by dsimp [H]; simp; exact hy
    have h_im : (((0 : ℝ) : ℂ) + y • I).im = y := by simp [Complex.real_smul]
    rw [h_P_eigen _ hyH, h_im]
  }
  have hd_rpow : HasDerivAt (fun y : ℝ => y ^ (-beta)) (-beta * (1 : ℝ) ^ (-beta - 1)) 1 :=
    Real.hasDerivAt_rpow_const (Or.inl (by norm_num))
  have h_rhs : deriv (fun y : ℝ => ∫ F, ‖Q F.F ((0 : ℝ) + y • I)‖^2 ∂P) 1 = -beta := by
  {
    rw [h_ev.deriv_eq, hd_rpow.deriv]
    simp
  }
  have h_lhs : deriv (fun y : ℝ => ∫ F, ‖Q F.F ((0 : ℝ) + y • I)‖^2 ∂P) 1 = 2 * ∫ F, a F I ∂P := by
  {
    have h_dy := deriv_integral_y P I hz_I
    simp only [Complex.I_re, Complex.I_im] at h_dy
    rw [h_dy, ← integral_const_mul]
    congr 1
    ext F
    have h_pt := dy_norm_Q_sq F I hz_I
    simp only [Complex.I_re, Complex.I_im, norm_Q_at_I_sq, div_one, mul_one] at h_pt
    exact h_pt
  }
  linarith
}

lemma E_b_eq (P : Measure KClass) [IsFiniteMeasure P] (beta : ℝ)
    (h_P_eigen : ∀ z ∈ H, ∫ F, ‖Q F.F z‖^2 ∂P = (z.im : ℝ) ^ (-beta)) :
    ∫ F, b F I ∂P = 0 := by
{
  have hz_I : I ∈ H := by dsimp [H]; simp
  have h_eq : (fun x : ℝ => ∫ F, ‖Q F.F ((x : ℂ) + (1 : ℝ) • I)‖^2 ∂P) = (fun _ : ℝ => (1 : ℝ) ^ (-beta)) := by
  {
    ext x
    have hxH : (x : ℂ) + (1 : ℝ) • I ∈ H := by dsimp [H]; simp
    have h_im : ((x : ℂ) + (1 : ℝ) • I).im = 1 := by simp
    rw [h_P_eigen _ hxH, h_im]
  }
  have h_rhs : deriv (fun x : ℝ => ∫ F, ‖Q F.F ((x : ℂ) + (1 : ℝ) • I)‖^2 ∂P) 0 = 0 := by
  {
    rw [h_eq, deriv_const]
  }
  have h_lhs : deriv (fun x : ℝ => ∫ F, ‖Q F.F ((x : ℂ) + (1 : ℝ) • I)‖^2 ∂P) 0 = 2 * ∫ F, b F I ∂P := by
  {
    have h_dx := deriv_integral_x P I hz_I
    simp only [Complex.I_re, Complex.I_im] at h_dx
    rw [h_dx, ← integral_const_mul]
    congr 1
    ext F
    have h_pt := dx_norm_Q_sq F I hz_I
    simp only [Complex.I_re, Complex.I_im, norm_Q_at_I_sq, div_one, mul_one] at h_pt
    exact h_pt
  }
  linarith
}

lemma deriv2_rpow_at_one (beta : ℝ) :
    deriv (deriv (fun y : ℝ => y ^ (-beta))) 1 = beta * (beta + 1) := by
{
  have h_ev : deriv (fun y : ℝ => y ^ (-beta)) =ᶠ[𝓝 1] (fun y : ℝ => -beta * y ^ (-beta - 1)) := by
  {
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1)] with y hy
    exact (Real.hasDerivAt_rpow_const (p := -beta) (Or.inl (ne_of_gt hy))).deriv
  }
  have hd2 : HasDerivAt (fun y : ℝ => -beta * y ^ (-beta - 1)) (-beta * ((-beta - 1) * (1 : ℝ) ^ (-beta - 1 - 1))) 1 :=
    (Real.hasDerivAt_rpow_const (p := -beta - 1) (Or.inl (by norm_num))).const_mul (-beta)
  rw [h_ev.deriv_eq, hd2.deriv, Real.one_rpow]
  ring
}

lemma E_q_sq_eq (P : Measure KClass) [IsFiniteMeasure P] (beta : ℝ)
    (h_P_eigen : ∀ z ∈ H, ∫ F, ‖Q F.F z‖^2 ∂P = (z.im : ℝ) ^ (-beta)) :
    ∫ F, ‖q F I‖^2 ∂P = beta * (beta + 1) / 4 := by
{
  have hz_I : I ∈ H := by dsimp [H]; simp
  have h_ev_y : (fun y : ℝ => ∫ F, ‖Q F.F ((0 : ℝ) + y • I)‖^2 ∂P) =ᶠ[𝓝 1] (fun y : ℝ => y ^ (-beta)) := by
  {
    filter_upwards [isOpen_Ioi.mem_nhds (by norm_num : (0 : ℝ) < 1)] with y hy
    have hyH : ((0 : ℝ) : ℂ) + y • I ∈ H := by dsimp [H]; simp; exact hy
    have h_im : (((0 : ℝ) : ℂ) + y • I).im = y := by simp [Complex.real_smul]
    rw [h_P_eigen _ hyH, h_im]
  }
  have h_eq_x : (fun x : ℝ => ∫ F, ‖Q F.F ((x : ℂ) + (1 : ℝ) • I)‖^2 ∂P) = (fun _ : ℝ => (1 : ℝ) ^ (-beta)) := by
  {
    ext x
    have hxH : (x : ℂ) + (1 : ℝ) • I ∈ H := by dsimp [H]; simp
    have h_im : ((x : ℂ) + (1 : ℝ) • I).im = 1 := by simp
    rw [h_P_eigen _ hxH, h_im]
  }
  have h_lap := deriv2_integral_laplacian P I hz_I
  simp only [Complex.I_re, Complex.I_im] at h_lap
  have h_d2x : deriv (deriv (fun x : ℝ => ∫ F, ‖Q F.F ((x : ℂ) + (1 : ℝ) • I)‖^2 ∂P)) 0 = 0 := by
  {
    rw [h_eq_x, deriv_const', deriv_const]
  }
  have h_d2y : deriv (deriv (fun y : ℝ => ∫ F, ‖Q F.F ((0 : ℝ) + y • I)‖^2 ∂P)) 1 = beta * (beta + 1) := by
  {
    rw [(h_ev_y.deriv).deriv_eq, deriv2_rpow_at_one beta]
  }
  have h_rhs : ∫ F, (deriv (deriv (fun x : ℝ => ‖Q F.F ((x : ℂ) + (1 : ℝ) • I)‖^2)) 0 +
                     deriv (deriv (fun y : ℝ => ‖Q F.F ((0 : ℝ) + y • I)‖^2)) 1) ∂P =
               4 * ∫ F, ‖q F I‖^2 ∂P := by
  {
    rw [← integral_const_mul]
    congr 1
    ext F
    have h_pt := laplacian_norm_Q_sq F I hz_I
    simp only [Complex.I_re, Complex.I_im] at h_pt
    rw [h_pt, norm_q_at_I_sq F]
  }
  linarith
}

end Brennan.Section3
