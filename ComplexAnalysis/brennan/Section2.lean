import Mathlib
import brennan.Koebe

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
{
  exact Brennan.Koebe.koebe_distortion_theorem f ⟨hf.1, hf.2, h0, h1⟩ z hz
}

lemma deriv_ne_zero_of_univalentOn {f : ℂ → ℂ} {U : Set ℂ}
    (hU : IsOpen U) (hf : UnivalentOn f U) {a : ℂ} (ha : a ∈ U) :
    deriv f a ≠ 0 := by
{
  exact Brennan.Koebe.univalent_deriv_ne_zero hU ⟨hf.1, hf.2⟩ ha
}

/-- Koebe Quarter Theorem (Lemma 2.1) -/
theorem koebe_quarter (g : ℂ → ℂ) (z₀ : ℂ) (R : ℝ) (hR : 0 < R)
    (hg : UnivalentOn g (Metric.ball z₀ R)) :
    Metric.ball (g z₀) (R * ‖deriv g z₀‖ / 4) ⊆ g '' Metric.ball z₀ R := by
{
  have hz0 : z₀ ∈ Metric.ball z₀ R := Metric.mem_ball.mpr (by simpa using hR)
  have hn : deriv g z₀ ≠ 0 := deriv_ne_zero_of_univalentOn Metric.isOpen_ball hg hz0
  exact Brennan.Koebe.local_koebe_quarter g z₀ R hR hg.1 hg.2 hn
}

/-- Cayley transform from D to H -/
def cayley (w : ℂ) : ℂ := I * (1 + w) / (1 - w)

/-- Inverse Cayley transform from H to D -/
def inv_cayley (z : ℂ) : ℂ := (z - I) / (z + I)

/-- Normalized map for F in KClass -/
def K_to_S (F : KClass) (w : ℂ) : ℂ :=
  (F.F (cayley w)) / (2 * I)

lemma isOpen_H : IsOpen H :=
  isOpen_lt continuous_const Complex.continuous_im

lemma inv_cayley_den_ne_zero {z : ℂ} (hz : z ∈ H) : z + I ≠ 0 := by
{
  intro he
  have h_im := congrArg Complex.im he
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at h_im
  change 0 < z.im at hz
  linarith
}

lemma cayley_den_ne_zero {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) : 1 - w ≠ 0 := by
{
  intro he
  have hw' : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
  rw [← sub_eq_zero.mp he] at hw'
  norm_num at hw'
}

lemma cayley_im (w : ℂ) : (cayley w).im = (1 - ‖w‖^2) / ‖1 - w‖^2 := by
{
  simp only [cayley, Complex.div_im, Complex.mul_re, Complex.mul_im,
    Complex.I_re, Complex.I_im, Complex.add_re, Complex.add_im, Complex.one_re,
    Complex.one_im, Complex.sub_re, Complex.sub_im, Complex.sq_norm, Complex.normSq_apply]
  ring
}

lemma cayley_maps {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) : cayley w ∈ H := by
{
  have hw' : ‖w‖ < 1 := by simpa [Metric.mem_ball, dist_zero_right] using hw
  change 0 < (cayley w).im
  rw [cayley_im]
  exact div_pos (by nlinarith [norm_nonneg w])
    (sq_pos_of_ne_zero (norm_ne_zero_iff.mpr (cayley_den_ne_zero hw)))
}

lemma norm_plus_I_sq (z : ℂ) : ‖z + I‖^2 = z.re^2 + (z.im + 1)^2 := by
{
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring
}

lemma norm_minus_I_sq (z : ℂ) : ‖z - I‖^2 = z.re^2 + (z.im - 1)^2 := by
{
  rw [Complex.sq_norm]
  simp [Complex.normSq_apply]
  ring
}

lemma inv_cayley_norm_sq (z : ℂ) :
    ‖inv_cayley z‖^2 = (z.re^2 + (z.im - 1)^2) / (z.re^2 + (z.im + 1)^2) := by
{
  dsimp [inv_cayley]
  rw [norm_div, div_pow, norm_minus_I_sq, norm_plus_I_sq]
}

lemma norm_inv_cayley_lt_one (z : ℂ) (hz : z.im > 0) :
    ‖inv_cayley z‖ < 1 := by
{
  have hd : z + I ≠ 0 := inv_cayley_den_ne_zero hz
  dsimp [inv_cayley]
  rw [norm_div, div_lt_one (norm_pos_iff.mpr hd)]
  have h1 := norm_minus_I_sq z
  have h2 := norm_plus_I_sq z
  nlinarith [norm_nonneg (z + I), norm_nonneg (z - I)]
}

lemma inv_cayley_maps {z : ℂ} (hz : z ∈ H) : inv_cayley z ∈ Metric.ball (0 : ℂ) 1 := by
{
  simpa [Metric.mem_ball, dist_zero_right] using norm_inv_cayley_lt_one z hz
}

lemma cayley_inv_cayley {z : ℂ} (hz : z ∈ H) : cayley (inv_cayley z) = z := by
{
  have hd := inv_cayley_den_ne_zero hz
  have hd2 := cayley_den_ne_zero (inv_cayley_maps hz)
  dsimp [cayley, inv_cayley] at *
  field_simp
  ring_nf
}

lemma inv_cayley_cayley {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) : inv_cayley (cayley w) = w := by
{
  have hd := cayley_den_ne_zero hw
  have hd2 := inv_cayley_den_ne_zero (cayley_maps hw)
  dsimp [cayley, inv_cayley] at *
  field_simp
  ring
}

lemma hasDerivAt_cayley {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    HasDerivAt cayley (2 * I / (1 - w)^2) w := by
{
  convert (((hasDerivAt_id w).const_add 1).const_mul I).div
    ((hasDerivAt_id w).const_sub 1) (cayley_den_ne_zero hw) using 1 <;> try rfl
  simp only [id_eq, mul_one]
  ring
}

lemma hasDerivAt_inv_cayley {z : ℂ} (hz : z ∈ H) :
    HasDerivAt inv_cayley (2 * I / (z + I)^2) z := by
{
  convert ((hasDerivAt_id z).sub_const I).div
    ((hasDerivAt_id z).add_const I) (inv_cayley_den_ne_zero hz) using 1 <;> try rfl
  simp only [id_eq, mul_one, one_mul]
  ring
}

lemma hasDerivAt_K_to_S (F : KClass) {w : ℂ} (hw : w ∈ Metric.ball (0 : ℂ) 1) :
    HasDerivAt (K_to_S F) (deriv F.F (cayley w) / (1 - w)^2) w := by
{
  have hd := ((F.univalent.1 _ (cayley_maps hw)).differentiableAt
    (isOpen_H.mem_nhds (cayley_maps hw))).hasDerivAt
  convert (hd.comp w (hasDerivAt_cayley hw)).div_const (2 * I) using 1 <;> try rfl
  field_simp
}

lemma K_to_S_differentiable (F : KClass) : DifferentiableOn ℂ (K_to_S F) (Metric.ball 0 1) := by
{
  intro w hw
  exact (hasDerivAt_K_to_S F hw).differentiableAt.differentiableWithinAt
}

lemma K_to_S_injOn (F : KClass) : InjOn (K_to_S F) (Metric.ball 0 1) := by
{
  intro z hz w hw he
  have hm := F.univalent.2 (cayley_maps hz) (cayley_maps hw)
    ((div_left_inj' (by simp : (2 : ℂ) * I ≠ 0)).mp he)
  simpa only [inv_cayley_cayley hz, inv_cayley_cayley hw] using congrArg inv_cayley hm
}

lemma K_to_S_zero (F : KClass) : K_to_S F 0 = 0 := by
{
  simp [K_to_S, cayley, F.norm_zero]
}

lemma K_to_S_deriv_zero (F : KClass) : deriv (K_to_S F) 0 = 1 := by
{
  have h0 : (0 : ℂ) ∈ Metric.ball (0 : ℂ) 1 := by simp
  rw [(hasDerivAt_K_to_S F h0).deriv]
  simp [cayley, F.norm_deriv]
}

lemma lemma_2_2_bounds_S (F : KClass) : Brennan.Koebe.IsClassS (K_to_S F) := by
{
  dsimp [Brennan.Koebe.IsClassS]
  refine ⟨K_to_S_differentiable F, K_to_S_injOn F, K_to_S_zero F, K_to_S_deriv_zero F⟩
}

lemma deriv_cayley_inv_cayley (z : ℂ) (hz : z.im > 0) :
    ‖deriv cayley (inv_cayley z)‖ = (z.re^2 + (z.im + 1)^2) / 2 := by
{
  have hw : inv_cayley z ∈ Metric.ball (0 : ℂ) 1 := inv_cayley_maps hz
  rw [(hasDerivAt_cayley hw).deriv]
  have hd : z + I ≠ 0 := inv_cayley_den_ne_zero hz
  have h_one_sub : 1 - inv_cayley z = 2 * I / (z + I) := by
  {
    dsimp [inv_cayley]
    field_simp
    ring
  }
  rw [h_one_sub, norm_div, norm_mul, norm_pow, norm_div, norm_mul]
  simp only [Complex.norm_ofNat, Complex.norm_I, mul_one]
  rw [div_pow, norm_plus_I_sq]
  have h_pos : 0 < z.re^2 + (z.im + 1)^2 := by positivity
  field_simp
}

lemma F_eq_2I_S_m (F : KClass) (z : ℂ) (hzH : z ∈ H) :
    F.F z = 2 * I * K_to_S F (m z) := by
{
  have hm : m z = inv_cayley z := rfl
  dsimp [K_to_S]
  rw [hm, cayley_inv_cayley hzH]
  field_simp
}

lemma hasDerivAt_F_via_K_to_S (F : KClass) {z : ℂ} (hz : z ∈ H) :
    HasDerivAt F.F (-(4 : ℂ) * deriv (K_to_S F) (inv_cayley z) / (z + I)^2) z := by
{
  have hd := ((K_to_S_differentiable F _ (inv_cayley_maps hz)).differentiableAt
    (Metric.isOpen_ball.mem_nhds (inv_cayley_maps hz))).hasDerivAt
  have h_comp := (hd.comp z (hasDerivAt_inv_cayley hz)).const_mul (2 * I)
  have h_val : 2 * I * (deriv (K_to_S F) (inv_cayley z) * (2 * I / (z + I)^2)) =
      -(4 : ℂ) * deriv (K_to_S F) (inv_cayley z) / (z + I)^2 := by
  {
    ring_nf
    simp [Complex.I_sq]
  }
  rw [h_val] at h_comp
  apply h_comp.congr_of_eventuallyEq
  filter_upwards [isOpen_H.mem_nhds hz] with w hw
  exact F_eq_2I_S_m F w hw
}

lemma deriv_F_eq (F : KClass) (z : ℂ) (hz : z.im > 0) :
    ‖deriv F.F z‖ = 4 * ‖deriv (K_to_S F) (inv_cayley z)‖ / (z.re^2 + (z.im + 1)^2) := by
{
  rw [(hasDerivAt_F_via_K_to_S F hz).deriv, norm_div, norm_mul, norm_neg, norm_pow, norm_plus_I_sq]
  norm_num
}

lemma koebe_lower_bound_w (z : ℂ) (w : ℂ) (hw : ‖w‖ < 1)
    (hw2 : ‖w‖^2 = (z.re^2 + (z.im - 1)^2) / (z.re^2 + (z.im + 1)^2)) :
    (1 - ‖w‖) / (1 + ‖w‖)^3 ≥ z.im / (4 * (z.re^2 + (z.im + 1)^2)) := by
{
  let r := ‖w‖
  let D := z.re^2 + (z.im + 1)^2
  have hr0 : 0 ≤ r := norm_nonneg w
  have hD_nonneg : 0 ≤ D := by positivity
  by_cases hD0 : D = 0
  · have : z.im / (4 * D) = 0 := by rw [hD0, mul_zero, div_zero]
    rw [this]
    have h_num : 0 ≤ 1 - r := by linarith
    have h_den : 0 ≤ (1 + r)^3 := by positivity
    exact div_nonneg h_num h_den
  · have hD_pos : 0 < D := lt_of_le_of_ne hD_nonneg (Ne.symm hD0)
    have h_id : (1 - r^2) * D = 4 * z.im := by
    {
      have hr2 : r^2 * D = z.re^2 + (z.im - 1)^2 := (eq_div_iff hD0).mp hw2
      dsimp [D] at hr2 ⊢
      linarith
    }
    have h1 : 2 * z.im ≤ (1 - r) * D := by
    {
      have hh : 1 - r^2 ≤ 2 * (1 - r) := by nlinarith [sq_nonneg (1 - r)]
      nlinarith [mul_le_mul_of_nonneg_right hh hD_pos.le]
    }
    have h8 : (1 + r)^3 ≤ 8 := by
    {
      nlinarith [sq_nonneg (1 - r), sq_nonneg r, mul_nonneg hr0 (sq_nonneg (1 - r))]
    }
    rw [ge_iff_le, div_le_div_iff₀ (by positivity : 0 < 4 * D) (by positivity : 0 < (1 + r)^3)]
    have h_nonneg : 0 ≤ (1 - r) * D := by positivity
    nlinarith [mul_le_mul_of_nonneg_left h8 h_nonneg]
}

lemma norm_Q_le_general (F : KClass) {z : ℂ} (hz : z ∈ H) :
    ‖Q F.F z‖ ≤ (z.re^2 + (z.im + 1)^2)^2 / z.im := by
{
  have hy : 0 < z.im := hz
  have hF_deriv := deriv_F_eq F z hy
  have hw_lt_1 := norm_inv_cayley_lt_one z hy
  have hw2 := inv_cayley_norm_sq z
  have hk := (Brennan.Koebe.koebe_distortion_theorem (K_to_S F) (lemma_2_2_bounds_S F) (inv_cayley z) hw_lt_1).1
  have h_alg := koebe_lower_bound_w z (inv_cayley z) hw_lt_1 hw2
  let D := z.re^2 + (z.im + 1)^2
  have h_deriv_lb : z.im / (4 * D) ≤ ‖deriv (K_to_S F) (inv_cayley z)‖ := le_trans h_alg hk
  have hD_pos : 0 < D := by positivity
  have h_F_lb : z.im / D^2 ≤ ‖deriv F.F z‖ := by
  {
    rw [hF_deriv]
    change z.im / D^2 ≤ 4 * ‖deriv (K_to_S F) (inv_cayley z)‖ / D
    rw [div_le_div_iff₀ (sq_pos_of_pos hD_pos) hD_pos]
    have h_step := (div_le_iff₀ (by positivity : 0 < 4 * D)).mp h_deriv_lb
    nlinarith [mul_le_mul_of_nonneg_right h_step hD_pos.le]
  }
  have h_F_pos : 0 < ‖deriv F.F z‖ := lt_of_lt_of_le (div_pos hy (sq_pos_of_pos hD_pos)) h_F_lb
  dsimp [Q]
  rw [norm_div, norm_one, div_le_div_iff₀ h_F_pos hy]
  have h_mul2 := (div_le_iff₀ (sq_pos_of_pos hD_pos)).mp h_F_lb
  nlinarith
}

/-- Uniform local bounds for the normalized compact class (Lemma 2.2) -/
theorem lemma_2_2_bounds (F : KClass) (x y C₀ : ℝ) (hy : 0 < y) (hy1 : y ≤ 1) (hx : |x| ≤ C₀) :
    ‖Q F.F ((x : ℂ) + (y : ℂ) * I)‖ ≤ (C₀^2 + 4)^2 / y := by
{
  set z := (x : ℂ) + (y : ℂ) * I
  have hz_re : z.re = x := by simp [z]
  have hz_im : z.im = y := by simp [z]
  have hz : z ∈ H := by dsimp [H]; rw [hz_im]; exact hy
  have hgen := norm_Q_le_general F hz
  rw [hz_re, hz_im] at hgen
  have hC0 : 0 ≤ C₀ := le_trans (abs_nonneg x) hx
  have hx2 : x^2 ≤ C₀^2 := by nlinarith [sq_abs x, (sq_le_sq₀ (abs_nonneg x) hC0).mpr hx]
  have hD_le : x^2 + (y + 1)^2 ≤ C₀^2 + 4 := by nlinarith
  have hD2_le : (x^2 + (y + 1)^2)^2 ≤ (C₀^2 + 4)^2 :=
    sq_le_sq₀ (by positivity) (by positivity) |>.mpr hD_le
  exact hgen.trans (div_le_div_of_nonneg_right hD2_le hy.le)
}

lemma koebe_S_lower_bound_m (w : ℂ) (hwm : 1/2 ≤ ‖w‖) :
    ‖w‖ / 4 ≥ 1 / 8 := by
{
  linarith
}

/-- Uniform local lower bound for F (Lemma 2.2) -/
theorem lemma_2_2_lower_bound (F : KClass) (z : ℂ) (hzH : z ∈ H) (hzm : 1/2 ≤ ‖m z‖) :
    1/16 ≤ ‖F.F z‖ := by
{
  have hF := F_eq_2I_S_m F z hzH
  have hw_lt_1 : ‖m z‖ < 1 := norm_inv_cayley_lt_one z hzH
  have hk_lb := (Brennan.Koebe.koebe_distortion_theorem (K_to_S F) (lemma_2_2_bounds_S F) (m z) hw_lt_1).2.2.1
  have h_alg := koebe_S_lower_bound_m (m z) hzm
  have hS_lb : 1 / 8 ≤ ‖K_to_S F (m z)‖ := le_trans h_alg hk_lb
  have hF_norm : ‖F.F z‖ = 2 * ‖K_to_S F (m z)‖ := by
  {
    rw [hF, norm_mul, norm_mul, Complex.norm_ofNat, Complex.norm_I, mul_one]
  }
  linarith
}

/-- Affine action composition -/
lemma aff_comp (z w v : ℂ) :
    aff z (aff w v) = aff (aff z w) v := by
{
  dsimp [aff]
  apply Complex.ext
  · simp
    ring
  · simp
    ring
}

lemma aff_I (z : ℂ) : aff z I = z := by
{
  apply Complex.ext <;> simp [aff]
}

lemma aff_mem_H {z w : ℂ} (hz : z ∈ H) (hw : w ∈ H) : aff z w ∈ H := by
{
  change 0 < (aff z w).im
  have h_im : (aff z w).im = z.im * w.im := by dsimp [aff]; simp
  rw [h_im]
  exact mul_pos hz hw
}

lemma aff_injective {z : ℂ} (hz : z ∈ H) : Function.Injective (aff z) := by
{
  intro u v h
  dsimp [aff] at h
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  exact mul_left_cancel₀ hy (add_left_cancel h)
}

lemma deriv_T (F : ℂ → ℂ) (z w : ℂ) (hF : DifferentiableAt ℂ F (aff z w)) (hz : (z.im : ℂ) ≠ 0) :
    deriv (T z F) w = deriv F (aff z w) / deriv F z := by
{
  unfold T
  have hd_aff : DifferentiableAt ℂ (fun w => aff z w) w := by
  {
    unfold aff
    fun_prop
  }
  have h_comp : deriv (fun w => F (aff z w)) w = deriv F (aff z w) * z.im := by
  {
    change deriv (F ∘ (fun w => aff z w)) w = _
    rw [deriv_comp w hF hd_aff]
    have h_aff : deriv (fun w => aff z w) w = z.im := by
    {
      unfold aff
      simp
    }
    rw [h_aff]
  }
  simp only [deriv_div_const, deriv_sub_const, h_comp]
  calc (deriv F (aff z w) * ↑z.im) / (↑z.im * deriv F z)
    _ = (deriv F (aff z w) * ↑z.im) / (deriv F z * ↑z.im) := by rw [mul_comm ↑z.im (deriv F z)]
    _ = (deriv F (aff z w) / deriv F z) := by rw [mul_div_mul_right (deriv F (aff z w)) (deriv F z) hz]
}

/-- Chain rule for Q under T_z -/
lemma lemma_2_3_Q (F : ℂ → ℂ) (z w : ℂ) (hF : DifferentiableAt ℂ F (aff z w)) (hz : (z.im : ℂ) ≠ 0) :
    Q (T z F) w = Q F (aff z w) / Q F z := by
{
  dsimp [Q]
  rw [deriv_T F z w hF hz]
  rw [one_div, inv_div]
  have h_div_div : (1 / deriv F (aff z w)) / (1 / deriv F z) = deriv F z / deriv F (aff z w) := by
  {
    rw [div_div_eq_mul_div]
    ring
  }
  rw [h_div_div]
}

/-- Composition of transfer operators T_w (T_z F) = T_{z \cdot w} F (Lemma 2.3) -/
lemma lemma_2_3_T (F : ℂ → ℂ) (z w : ℂ)
    (hz_im : (z.im : ℂ) ≠ 0)
    (hw_im : (w.im : ℂ) ≠ 0)
    (hdF_z : deriv F z ≠ 0)
    (hdF_aff : deriv F (aff z w) ≠ 0)
    (hF : DifferentiableAt ℂ F (aff z w)) :
    T w (T z F) = T (aff z w) F := by
{
  funext v
  dsimp [T]
  rw [deriv_T F z w hF hz_im]
  rw [aff_comp]
  have h_im : (aff z w).im = z.im * w.im := by
  {
    dsimp [aff]
    simp
  }
  rw [h_im]
  push_cast
  have h_num : (F (aff (aff z w) v) - F z) / (↑z.im * deriv F z) - (F (aff z w) - F z) / (↑z.im * deriv F z) =
               (F (aff (aff z w) v) - F (aff z w)) / (↑z.im * deriv F z) := by
  {
    rw [←sub_div]
    congr 1
    ring
  }
  rw [h_num]
  field_simp
}

/-- Composition of transfer operators for KClass maps on H (Lemma 2.3 Wrapper) -/
lemma lemma_2_3_KClass (F : KClass) (z w : ℂ) (hz : z ∈ H) (hw : w ∈ H) :
    T w (T z F.F) = T (aff z w) F.F := by
{
  have h_univ := F.univalent
  have hz_im_nz : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hw_im_nz : (w.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hw)
  have hdF_z : deriv F.F z ≠ 0 := deriv_ne_zero_of_univalentOn isOpen_H h_univ hz
  have h_aff_in_H : aff z w ∈ H := aff_mem_H hz hw
  have hdF_aff : deriv F.F (aff z w) ≠ 0 := deriv_ne_zero_of_univalentOn isOpen_H h_univ h_aff_in_H
  have hF_diff : DifferentiableAt ℂ F.F (aff z w) :=
    (h_univ.1 (aff z w) h_aff_in_H).differentiableAt (isOpen_H.mem_nhds h_aff_in_H)
  exact lemma_2_3_T F.F z w hz_im_nz hw_im_nz hdF_z hdF_aff hF_diff
}

lemma T_KClass (F : KClass) (z : ℂ) (hz : z ∈ H) :
    UnivalentOn (T z F.F) H ∧ (T z F.F) I = 0 ∧ deriv (T z F.F) I = 1 := by
{
  have hy : (z.im : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt hz)
  have hdf : deriv F.F z ≠ 0 := deriv_ne_zero_of_univalentOn isOpen_H F.univalent hz
  refine ⟨⟨?_, ?_⟩, ?_, ?_⟩
  · intro w hw
    have hF_w : DifferentiableAt ℂ F.F (aff z w) :=
      (F.univalent.1 (aff z w) (aff_mem_H hz hw)).differentiableAt (isOpen_H.mem_nhds (aff_mem_H hz hw))
    have hd_aff : DifferentiableAt ℂ (fun u => aff z u) w := by
    {
      unfold aff
      fun_prop
    }
    have h_comp : DifferentiableAt ℂ (fun u => F.F (aff z u)) w := hF_w.comp w hd_aff
    exact ((h_comp.sub_const (F.F z)).div_const ((z.im : ℂ) * deriv F.F z)).differentiableWithinAt
  · intro u hu v hv h
    apply aff_injective hz
    apply F.univalent.2 (aff_mem_H hz hu) (aff_mem_H hz hv)
    have hh : F.F (aff z u) - F.F z = F.F (aff z v) - F.F z :=
      (div_left_inj' (mul_ne_zero hy hdf)).mp h
    exact sub_left_injective hh
  · simp [T, aff_I]
  · have hI_H : I ∈ H := by simp [H]
    have hF_I : DifferentiableAt ℂ F.F (aff z I) :=
      (F.univalent.1 (aff z I) (aff_mem_H hz hI_H)).differentiableAt (isOpen_H.mem_nhds (aff_mem_H hz hI_H))
    rw [deriv_T F.F z I hF_I hy, aff_I, div_self hdf]
}

end Brennan.Section2
