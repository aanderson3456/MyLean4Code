import Mathlib

open Complex Set MeasureTheory Topology Filter
open scoped ComplexConjugate Topology

noncomputable section

namespace Brennan.Section2

/-- The upper half-plane $\mathbb{H}$ -/
def H : Set ℂ := {z | 0 < z.im}

/-- The Cayley transform $m(z) = \frac{z - i}{z + i}$ mapping $\mathbb{H}$ to $\mathbb{D}$ -/
def m (z : ℂ) : ℂ := (z - I) / (z + I)

/-- Univalent functions are holomorphic and injective on a domain -/
def UnivalentOn (f : ℂ → ℂ) (U : Set ℂ) : Prop :=
  DifferentiableOn ℂ f U ∧ InjOn f U

/-- The normalized compact class $\mathcal{K}$ of univalent maps on $\mathbb{H}$ -/
structure KClass where
  F : ℂ → ℂ
  univalent : UnivalentOn F H
  norm_zero : F I = 0
  norm_deriv : deriv F I = 1

/-- The inverse derivative $Q_F(z) = 1/F'(z)$ -/
def Q (F : ℂ → ℂ) (z : ℂ) : ℂ := 1 / deriv F z

/-- The affine source map $z \cdot w = x + y w$ where $z = x + iy$ -/
def aff (z w : ℂ) : ℂ := (z.re : ℂ) + (z.im : ℂ) * w

/-- The inverse affine source map $z^\# = (-x + i)/y$ -/
def aff_inv (z : ℂ) : ℂ := (-(z.re : ℂ) + I) / (z.im : ℂ)

/-- The transfer operator $T_z F(w) = \frac{F(z \cdot w) - F(z)}{y F'(z)}$ -/
def T (z : ℂ) (F : ℂ → ℂ) (w : ℂ) : ℂ :=
  (F (aff z w) - F z) / ((z.im : ℂ) * deriv F z)

/-- The positive transfer weight $|Q_F(z)|^2$ -/
def A_weight (z : ℂ) (F : ℂ → ℂ) : ℝ := ‖Q F z‖^2

/-- Action of $A_z$ on a continuous function $\Phi : \mathcal{K} \to \mathbb{C}$ -/
def A_op (z : ℂ) (Phi : (ℂ → ℂ) → ℂ) (F : ℂ → ℂ) : ℂ :=
  (A_weight z F : ℂ) * Phi (T z F)

/-- The dyadic positive operator $L = \frac{1}{2}(A_{-1/2+i/2} + A_{1/2+i/2})$ -/
def L_op (Phi : (ℂ → ℂ) → ℂ) (F : ℂ → ℂ) : ℂ :=
  (1 / 2 : ℂ) * (A_op (-1/2 + I/2) Phi F + A_op (1/2 + I/2) Phi F)

/-- Classical univalence estimates for the class S (Lemma 2.1) -/
theorem koebe_distortion (f : ℂ → ℂ) (hf : UnivalentOn f (Metric.ball 0 1))
    (h0 : f 0 = 0) (h1 : deriv f 0 = 1) (z : ℂ) (hz : ‖z‖ < 1) :
    (1 - ‖z‖) / (1 + ‖z‖)^3 ≤ ‖deriv f z‖ ∧
    ‖deriv f z‖ ≤ (1 + ‖z‖) / (1 - ‖z‖)^3 ∧
    ‖z‖ / 4 ≤ ‖f z‖ ∧
    ‖f z‖ ≤ ‖z‖ / (1 - ‖z‖)^2 := by
  sorry

/-- Koebe Quarter Theorem (Lemma 2.1) -/
theorem koebe_quarter (g : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hg : UnivalentOn g (Metric.ball z₀ R)) :
    Metric.ball (g z₀) (R * ‖deriv g z₀‖ / 4) ⊆ g '' Metric.ball z₀ R := by
  sorry

/-- Uniform local bounds for the normalized compact class (Lemma 2.2) -/
theorem lemma_2_2_bounds (F : KClass) (x y C₀ : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) (hx : |x| ≤ C₀) :
    ‖Q F.F ((x : ℂ) + (y : ℂ) * I)‖ ≤ (C₀^2 + 4)^2 / y := by
  sorry

/-- Uniform local lower bound for F (Lemma 2.2) -/
theorem lemma_2_2_lower_bound (F : KClass) (z : ℂ) (hzH : z ∈ H) (hzm : 1/2 ≤ ‖m z‖) :
    1/16 ≤ ‖F.F z‖ := by
  sorry

/-- Affine action composition -/
lemma aff_comp (z w v : ℂ) :
    aff z (aff w v) = aff (aff z w) v := by
  dsimp [aff]
  apply Complex.ext
  · simp
    ring
  · simp
    ring

lemma deriv_T (F : ℂ → ℂ) (z w : ℂ) (hF : DifferentiableAt ℂ F (aff z w)) (hz : (z.im : ℂ) ≠ 0) :
    deriv (T z F) w = deriv F (aff z w) / deriv F z := by
  unfold T
  have hd_aff : DifferentiableAt ℂ (fun w => aff z w) w := by
    unfold aff
    fun_prop
  have h_comp : deriv (fun w => F (aff z w)) w = deriv F (aff z w) * z.im := by
    change deriv (F ∘ (fun w => aff z w)) w = _
    rw [deriv_comp w hF hd_aff]
    have h_aff : deriv (fun w => aff z w) w = z.im := by
      unfold aff
      simp
    rw [h_aff]
  simp only [deriv_div_const, deriv_sub_const, h_comp]
  calc (deriv F (aff z w) * ↑z.im) / (↑z.im * deriv F z)
    _ = (deriv F (aff z w) * ↑z.im) / (deriv F z * ↑z.im) := by rw [mul_comm ↑z.im (deriv F z)]
    _ = (deriv F (aff z w) / deriv F z) := by rw [mul_div_mul_right (deriv F (aff z w)) (deriv F z) hz]

/-- Chain rule for Q under T_z -/
lemma lemma_2_3_Q (F : ℂ → ℂ) (z w : ℂ) (hF : DifferentiableAt ℂ F (aff z w)) (hz : (z.im : ℂ) ≠ 0) :
    Q (T z F) w = Q F (aff z w) / Q F z := by
  dsimp [Q]
  rw [deriv_T F z w hF hz]
  rw [one_div, inv_div]
  have h_div_div : (1 / deriv F (aff z w)) / (1 / deriv F z) = deriv F z / deriv F (aff z w) := by
    rw [div_div_eq_mul_div]
    ring
  rw [h_div_div]

/-- Composition of transfer operators T_w (T_z F) = T_{z \cdot w} F (Lemma 2.3) -/
lemma lemma_2_3_T (F : ℂ → ℂ) (z w : ℂ)
    (hz_im : (z.im : ℂ) ≠ 0)
    (hw_im : (w.im : ℂ) ≠ 0)
    (hdF_z : deriv F z ≠ 0)
    (hdF_aff : deriv F (aff z w) ≠ 0)
    (hF : DifferentiableAt ℂ F (aff z w)) :
    T w (T z F) = T (aff z w) F := by
  funext v
  dsimp [T]
  rw [deriv_T F z w hF hz_im]
  rw [aff_comp]
  have h_im : (aff z w).im = z.im * w.im := by
    dsimp [aff]
    simp
  rw [h_im]
  push_cast
  have h_num : (F (aff (aff z w) v) - F z) / (↑z.im * deriv F z) - (F (aff z w) - F z) / (↑z.im * deriv F z) =
               (F (aff (aff z w) v) - F (aff z w)) / (↑z.im * deriv F z) := by
    rw [←sub_div]
    congr 1
    ring
  rw [h_num]
  have hz_im_real : (z.im : ℂ) ≠ 0 := hz_im
  have hw_im_real : (w.im : ℂ) ≠ 0 := hw_im
  field_simp

lemma deriv_ne_zero_of_univalentOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) (hf : UnivalentOn f U) {z : ℂ} (hz : z ∈ U) : deriv f z ≠ 0 := sorry

/-- Composition of transfer operators for KClass maps on H (Lemma 2.3 Wrapper) -/
lemma lemma_2_3_KClass (F : KClass) (z w : ℂ) (hz : z ∈ H) (hw : w ∈ H) :
    T w (T z F.F) = T (aff z w) F.F := by
  -- We extract the fact that F is univalent on H
  have h_univ := F.univalent
  -- z and w are in H, so their imaginary parts are strictly positive (and thus non-zero)
  have hz_im_pos : 0 < z.im := hz
  have hw_im_pos : 0 < w.im := hw
  have hz_im_nz : (z.im : ℂ) ≠ 0 := by
    intro h
    have h_re : (z.im : ℝ) = 0 := by exact_mod_cast h
    linarith
  have hw_im_nz : (w.im : ℂ) ≠ 0 := by
    intro h
    have h_re : (w.im : ℝ) = 0 := by exact_mod_cast h
    linarith
  have H_isOpen : IsOpen H := isOpen_lt continuous_const Complex.continuous_im
  -- Since F is injective on H, its derivative is non-zero (locally univalent)
  have hdF_z : deriv F.F z ≠ 0 := deriv_ne_zero_of_univalentOn H_isOpen h_univ hz
  have h_aff_in_H : aff z w ∈ H := by
    dsimp [H] at *
    have h_im : (aff z w).im = z.im * w.im := by dsimp [aff]; simp
    rw [h_im]
    exact mul_pos hz_im_pos hw_im_pos
  have hdF_aff : deriv F.F (aff z w) ≠ 0 := deriv_ne_zero_of_univalentOn H_isOpen h_univ h_aff_in_H

  have hF_diff : DifferentiableAt ℂ F.F (aff z w) := by
    -- H is an open set, and F is DifferentiableOn H
    have h_open : IsOpen H := isOpen_lt continuous_const continuous_im
    exact (h_univ.1 (aff z w) h_aff_in_H).differentiableAt (IsOpen.mem_nhds h_open h_aff_in_H)
  exact lemma_2_3_T F.F z w hz_im_nz hw_im_nz hdF_z hdF_aff hF_diff

end Brennan.Section2
