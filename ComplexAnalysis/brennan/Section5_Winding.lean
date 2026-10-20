import Mathlib

noncomputable section

open Set MeasureTheory Filter Function InnerProductSpace TopologicalSpace
open scoped Topology ComplexConjugate Manifold NNReal ENNReal InnerProductSpace Classical CompactlySupported

namespace Brennan.Sections4and5

/-!
# Section 5 Winding Numbers, Planar Degree, and Regular Level Curves
-/

lemma dite_eq_left {α : Sort*} {P : Prop} [Decidable P] (h : P) {a : P → α} {b : ¬ P → α} :
    dite P a b = a h := by
{
  exact dif_pos h
}

lemma ite_eq_left {α : Sort*} {P : Prop} [Decidable P] (h : P) {a b : α} :
    ite P a b = a := by
{
  exact if_pos h
}

lemma ite_eq_right {α : Sort*} {P : Prop} [Decidable P] (h : ¬ P) {a b : α} :
    ite P a b = b := by
{
  exact if_neg h
}

@[simp] lemma one_apply_eq_self {R M : Type*} [Semiring R] [AddCommMonoid M] [Module R M]
    [TopologicalSpace M] (x : M) : (1 : M →L[R] M) x = x := by
{
  rfl
}

def HasLogIncrement (γ : C(unitInterval, ℂ)) (q : ℂ) : Prop :=
  ∃ T : C(unitInterval, ℂ), (∀ t, Complex.exp (T t) = γ t) ∧ T 1 - T 0 = q

lemma HasLogIncrement.perturb {γ η : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) (hloopγ : γ 1 = γ 0) (hloopη : η 1 = η 0)
    (h : ∀ t, ‖η t - γ t‖ < ‖γ t‖) : HasLogIncrement η q := by
{
  obtain ⟨T, hT, hend⟩ := hγ
  have hn (t) : γ t ≠ 0 := (hT t ▸ Complex.exp_ne_zero (T t))
  have hratio (t) : η t / γ t ∈ Complex.slitPlane := by
  {
    have he : η t / γ t = 1 + (η t - γ t) / γ t := by field_simp [hn t]; ring
    rw [he]
    apply Complex.mem_slitPlane_of_norm_lt_one
    rw [norm_div, div_lt_one (norm_pos_iff.mpr (hn t))]
    exact h t
  }
  let R : C(unitInterval, ℂ) := ⟨fun t => Complex.log (η t / γ t),
    Continuous.clog (η.continuous.div γ.continuous hn) hratio⟩
  refine ⟨T + R, fun t => ?_, ?_⟩
  · change Complex.exp (T t + Complex.log (η t / γ t)) = η t
    rw [Complex.exp_add, hT t, Complex.exp_log (Complex.slitPlane_ne_zero (hratio t))]
    field_simp [hn t]
  · change (T 1 + Complex.log (η 1 / γ 1)) - (T 0 + Complex.log (η 0 / γ 0)) = q
    rw [hloopγ, hloopη]
    linear_combination hend
}

def circleLoop : C(unitInterval, ℂ) :=
  ⟨fun t => Complex.exp ((2 * Real.pi * (t : ℝ) : ℝ) * Complex.I), by fun_prop⟩

@[simp] lemma circleLoop_zero : circleLoop 0 = 1 := by
{
  simp [circleLoop]
}

@[simp] lemma circleLoop_one : circleLoop 1 = 1 := by
{
  simp [circleLoop, Complex.exp_two_pi_mul_I]
}

@[simp] lemma norm_circleLoop (t : unitInterval) : ‖circleLoop t‖ = 1 := by
{
  simp [circleLoop, Complex.norm_exp]
}

lemma circleLoop_logIncrement (a : ℂ) (ha : a ≠ 0) :
    HasLogIncrement (a • circleLoop) (2 * Real.pi * Complex.I) := by
{
  refine ⟨⟨fun t => Complex.log a + (2 * Real.pi * (t : ℝ) : ℝ) * Complex.I, by fun_prop⟩, ?_, ?_⟩
  · intro t
    simp [Complex.exp_add, Complex.exp_log ha, circleLoop]
  · simp
}

lemma conj_circleLoop_logIncrement (a : ℂ) (ha : a ≠ 0) :
    HasLogIncrement ⟨fun t => a * conj (circleLoop t), by fun_prop⟩ (-(2 * Real.pi * Complex.I)) := by
{
  refine ⟨⟨fun t => Complex.log a - (2 * Real.pi * (t : ℝ) : ℝ) * Complex.I, by fun_prop⟩, ?_, ?_⟩
  · intro t
    simp only [ContinuousMap.coe_mk, circleLoop, Complex.exp_sub, Complex.exp_log ha]
    rw [← Complex.exp_conj]
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I, mul_neg, Complex.exp_neg]
    rfl
  · simp
}

def linearPart (A : ℂ →L[ℝ] ℂ) : ℂ := (A 1 - Complex.I * A Complex.I) / 2

def antiLinearPart (A : ℂ →L[ℝ] ℂ) : ℂ := (A 1 + Complex.I * A Complex.I) / 2

lemma realLinear_decomposition (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    A z = linearPart A * z + antiLinearPart A * conj z := by
{
  have he : z = z.re • (1 : ℂ) + z.im • Complex.I := by simp [Complex.real_smul]
  calc
    A z = z.re • A 1 + z.im • A Complex.I := by
      conv_lhs => rw [he, map_add, map_smul, map_smul]
    _ = linearPart A * z + antiLinearPart A * conj z := by
      apply Complex.ext <;>
        simp [linearPart, antiLinearPart, Complex.mul_re, Complex.mul_im, Complex.real_smul] <;> ring
}

lemma det_complex_real_eq (A : ℂ →ₗ[ℝ] ℂ) :
    LinearMap.det A = (A 1).re * (A Complex.I).im - (A Complex.I).re * (A 1).im := by
{
  rw [← LinearMap.det_toMatrix Complex.basisOneI, Matrix.det_fin_two]
  simp [LinearMap.toMatrix_apply, Complex.coe_basisOneI, Complex.coe_basisOneI_repr]
}

lemma det_eq_linearParts (A : ℂ →L[ℝ] ℂ) :
    LinearMap.det A.toLinearMap = ‖linearPart A‖^2 - ‖antiLinearPart A‖^2 := by
{
  rw [det_complex_real_eq]
  simp only [← Complex.normSq_eq_norm_sq, linearPart, antiLinearPart,
    Complex.normSq_apply, Complex.div_re, Complex.div_im, Complex.sub_re,
    Complex.sub_im, Complex.add_re, Complex.add_im, Complex.mul_re,
    Complex.mul_im, Complex.I_re, Complex.I_im]
  norm_num
  ring
}

lemma linear_circle_logIncrement_pos (A : ℂ →L[ℝ] ℂ)
    (hA : 0 < LinearMap.det A.toLinearMap) :
    HasLogIncrement ⟨fun t => A (circleLoop t), by fun_prop⟩ (2 * Real.pi * Complex.I) := by
{
  have hn : ‖antiLinearPart A‖ < ‖linearPart A‖ := by
  {
    rw [det_eq_linearParts] at hA
    nlinarith [norm_nonneg (linearPart A), norm_nonneg (antiLinearPart A)]
  }
  have ha : linearPart A ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hn)
  apply (circleLoop_logIncrement (linearPart A) ha).perturb (by simp) (by simp)
  intro t
  simp only [ContinuousMap.coe_mk, ContinuousMap.coe_smul, Pi.smul_apply,
    smul_eq_mul, realLinear_decomposition, add_sub_cancel_left, norm_mul,
    RCLike.norm_conj, norm_circleLoop, mul_one]
  exact hn
}

lemma linear_circle_logIncrement_neg (A : ℂ →L[ℝ] ℂ)
    (hA : LinearMap.det A.toLinearMap < 0) :
    HasLogIncrement ⟨fun t => A (circleLoop t), by fun_prop⟩ (-(2 * Real.pi * Complex.I)) := by
{
  have hn : ‖linearPart A‖ < ‖antiLinearPart A‖ := by
  {
    rw [det_eq_linearParts] at hA
    nlinarith [norm_nonneg (linearPart A), norm_nonneg (antiLinearPart A)]
  }
  have ha : antiLinearPart A ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hn)
  apply (conj_circleLoop_logIncrement (antiLinearPart A) ha).perturb (by simp) (by simp)
  intro t
  simp only [ContinuousMap.coe_mk, realLinear_decomposition, add_sub_cancel_right,
    norm_mul, RCLike.norm_conj, norm_circleLoop, mul_one]
  exact hn
}

lemma HasLogIncrement.smul {γ : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) {c : ℂ} (hc : c ≠ 0) :
    HasLogIncrement (c • γ) q := by
{
  obtain ⟨T, hT, hend⟩ := hγ
  refine ⟨T + ContinuousMap.const _ (Complex.log c), fun t => ?_, ?_⟩
  · change Complex.exp (T t + Complex.log c) = c * γ t
    rw [Complex.exp_add, hT t, Complex.exp_log hc, mul_comm]
  · change (T 1 + Complex.log c) - (T 0 + Complex.log c) = q
    linear_combination hend
}

lemma norm_linear_lower_pos (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    (‖linearPart A‖ - ‖antiLinearPart A‖) * ‖z‖ ≤ ‖A z‖ := by
{
  have ht := norm_sub_norm_le (linearPart A * z) (-antiLinearPart A * conj z)
  rw [norm_mul, norm_mul, norm_neg, RCLike.norm_conj, neg_mul, sub_neg_eq_add,
    ← realLinear_decomposition] at ht
  linarith
}

lemma norm_linear_lower_neg (A : ℂ →L[ℝ] ℂ) (z : ℂ) :
    (‖antiLinearPart A‖ - ‖linearPart A‖) * ‖z‖ ≤ ‖A z‖ := by
{
  have ht := norm_sub_norm_le (antiLinearPart A * conj z) (-linearPart A * z)
  rw [norm_mul, norm_mul, norm_neg, RCLike.norm_conj, neg_mul, sub_neg_eq_add,
    add_comm, ← realLinear_decomposition] at ht
  linarith
}

lemma exists_log_lift (γ : C(unitInterval, ℂ)) (hγ : ∀ t, γ t ≠ 0) :
    ∃ T : C(unitInterval, ℂ), ∀ t, Complex.exp (T t) = γ t := by
{
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).contractibleSpace (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩)
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).locPathConnectedSpace
  obtain ⟨T, ⟨-, hT⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    γ (Complex.exp_log (hγ 0)) hγ
  exact ⟨T, fun t => congrFun hT t⟩
}

lemma log_lifts_difference_constant.{u_1} {X : Type u_1} [TopologicalSpace X] [PreconnectedSpace X]
    {A B : X → ℂ} (hA : Continuous A) (hB : Continuous B)
    (h : ∀ x, Complex.exp (A x) = Complex.exp (B x)) (x y : X) :
    A y - B y = A x - B x := by
{
  have hC : Continuous (fun z => B z + (A x - B x)) := hB.add continuous_const
  have he (z) : Complex.exp (A z) = Complex.exp (B z + (A x - B x)) := by
  {
    rw [Complex.exp_add, Complex.exp_sub, h x, div_self (Complex.exp_ne_zero _), mul_one]
    exact h z
  }
  have heq : A = fun z => B z + (A x - B x) :=
    Complex.isCoveringMap_exp.eq_of_comp_eq hA hC (by funext z; exact Subtype.ext (he z)) x (by ring)
  have hy := congrFun heq y
  linear_combination hy
}

lemma HasLogIncrement.unique {γ : C(unitInterval, ℂ)} {p q : ℂ}
    (hp : HasLogIncrement γ p) (hq : HasLogIncrement γ q) : p = q := by
{
  obtain ⟨A, hA, hp⟩ := hp
  obtain ⟨B, hB, hq⟩ := hq
  have he := log_lifts_difference_constant A.continuous B.continuous
    (fun t => (hA t).trans (hB t).symm) (0 : unitInterval) 1
  linear_combination hp.symm - hq.symm + he
}

lemma HasLogIncrement.mul {γ η : C(unitInterval, ℂ)} {p q : ℂ}
    (hγ : HasLogIncrement γ p) (hη : HasLogIncrement η q) :
    HasLogIncrement (γ * η) (p + q) := by
{
  obtain ⟨A, hA, hp⟩ := hγ
  obtain ⟨B, hB, hq⟩ := hη
  refine ⟨A + B, fun t => ?_, ?_⟩
  · change Complex.exp (A t + B t) = γ t * η t
    rw [Complex.exp_add, hA t, hB t]
  · change (A 1 + B 1) - (A 0 + B 0) = p + q
    linear_combination hp + hq
}

lemma HasLogIncrement.conj {γ : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) :
    HasLogIncrement ⟨fun t => conj (γ t), by fun_prop⟩ (conj q) := by
{
  obtain ⟨A, hA, hq⟩ := hγ
  refine ⟨⟨fun t => conj (A t), by fun_prop⟩, fun t => ?_, ?_⟩
  · exact (Complex.exp_conj _).trans (congrArg conj (hA t))
  · change conj (A 1) - conj (A 0) = conj q
    rw [← map_sub, hq]
}

lemma HasLogIncrement.of_global_log.{u_1} {X : Type u_1} [TopologicalSpace X]
    (f : C(X, ℂ)) (A : C(X, ℂ)) (hA : ∀ x, Complex.exp (A x) = f x)
    (γ : C(unitInterval, X)) (hγ : γ 1 = γ 0) :
    HasLogIncrement (f.comp γ) 0 := by
{
  refine ⟨A.comp γ, fun t => hA (γ t), ?_⟩
  change A (γ 1) - A (γ 0) = 0
  rw [hγ, sub_self]
}

lemma HasLogIncrement.integer {γ : C(unitInterval, ℂ)} {q : ℂ}
    (hγ : HasLogIncrement γ q) (hloop : γ 1 = γ 0) :
    ∃ n : ℤ, q = n * (2 * Real.pi * Complex.I) := by
{
  obtain ⟨A, hA, hq⟩ := hγ
  apply Complex.exp_eq_one_iff.mp
  rw [← hq, Complex.exp_sub, hA 1, hA 0, hloop, div_self (hA 0 ▸ Complex.exp_ne_zero _)]
}

lemma period_ne_zero : (2 * Real.pi * Complex.I : ℂ) ≠ 0 := by
{
  exact mul_ne_zero (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero))
    Complex.I_ne_zero
}

lemma integer_period_injective : Function.Injective
    (fun n : ℤ => (n : ℂ) * (2 * Real.pi * Complex.I)) := by
{
  intro n m h
  exact_mod_cast (mul_right_cancel₀ period_ne_zero h : (n : ℂ) = m)
}

lemma exists_integer_logIncrement (γ : C(unitInterval, ℂ))
    (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ≠ 0) :
    ∃ n : ℤ, HasLogIncrement γ (n * (2 * Real.pi * Complex.I)) := by
{
  obtain ⟨A, hA⟩ := exists_log_lift γ hγ
  have hi : HasLogIncrement γ (A 1 - A 0) := ⟨A, hA, rfl⟩
  obtain ⟨n, hn⟩ := hi.integer hloop
  exact ⟨n, hn ▸ hi⟩
}

def windingNumber (γ : C(unitInterval, ℂ)) : ℤ :=
  if h : γ 1 = γ 0 ∧ ∀ t, γ t ≠ 0 then
    Classical.choose (exists_integer_logIncrement γ h.1 h.2)
  else 0

lemma windingNumber_spec (γ : C(unitInterval, ℂ))
    (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ≠ 0) :
    HasLogIncrement γ ((windingNumber γ) * (2 * Real.pi * Complex.I)) := by
{
  rw [windingNumber, dite_eq_left ⟨hloop, hγ⟩]
  exact Classical.choose_spec (exists_integer_logIncrement γ hloop hγ)
}

lemma windingNumber_eq_of_logIncrement {γ : C(unitInterval, ℂ)} {n : ℤ}
    (hloop : γ 1 = γ 0) (h : HasLogIncrement γ (n * (2 * Real.pi * Complex.I))) :
    windingNumber γ = n := by
{
  have hn (t) : γ t ≠ 0 := by
  {
    obtain ⟨A, hA, -⟩ := h
    exact hA t ▸ Complex.exp_ne_zero _
  }
  exact integer_period_injective ((windingNumber_spec γ hloop hn).unique h)
}

lemma windingNumber_mul (γ η : C(unitInterval, ℂ))
    (hloopγ : γ 1 = γ 0) (hloopη : η 1 = η 0)
    (hγ : ∀ t, γ t ≠ 0) (hη : ∀ t, η t ≠ 0) :
    windingNumber (γ * η) = windingNumber γ + windingNumber η := by
{
  apply windingNumber_eq_of_logIncrement (by simp [hloopγ, hloopη])
  convert (windingNumber_spec γ hloopγ hγ).mul (windingNumber_spec η hloopη hη) using 1
  push_cast
  ring
}

lemma windingNumber_perturb {γ η : C(unitInterval, ℂ)}
    (hloopγ : γ 1 = γ 0) (hloopη : η 1 = η 0) (hγ : ∀ t, γ t ≠ 0)
    (h : ∀ t, ‖η t - γ t‖ < ‖γ t‖) : windingNumber η = windingNumber γ := by
{
  exact windingNumber_eq_of_logIncrement hloopη
    ((windingNumber_spec γ hloopγ hγ).perturb hloopγ hloopη h)
}

lemma exists_log_lift_of_simplyConnected.{u_1} {X : Type u_1} [TopologicalSpace X]
    [SimplyConnectedSpace X] [LocPathConnectedSpace X] (x : X)
    (f : C(X, ℂ)) (hf : ∀ y, f y ≠ 0) :
    ∃ A : C(X, ℂ), ∀ y, Complex.exp (A y) = f y := by
{
  obtain ⟨A, ⟨-, hA⟩, -⟩ := Complex.isCoveringMapOn_exp.existsUnique_continuousMap_lifts
    f (Complex.exp_log (hf x)) hf
  exact ⟨A, fun y => congrFun hA y⟩
}

theorem JoinedIn.prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {t : Set Y} {x₁ x₂ : X} {y₁ y₂ : Y}
    (hx : JoinedIn s x₁ x₂) (hy : JoinedIn t y₁ y₂) :
    JoinedIn (s ×ˢ t) (x₁, y₁) (x₂, y₂) := by
{
  rcases hx with ⟨γ₁, hγ₁⟩
  rcases hy with ⟨γ₂, hγ₂⟩
  exact ⟨γ₁.prod γ₂, fun t => ⟨hγ₁ t, hγ₂ t⟩⟩
}

theorem IsPathConnected.prod {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    {s : Set X} {t : Set Y} (hs : IsPathConnected s) (ht : IsPathConnected t) :
    IsPathConnected (s ×ˢ t) := by
{
  rw [isPathConnected_iff]
  refine ⟨hs.nonempty.prod ht.nonempty, fun (x₁, y₁) ⟨hx₁, hy₁⟩ (x₂, y₂) ⟨hx₂, hy₂⟩ ↦ ?_⟩
  exact JoinedIn.prod (hs.joinedIn x₁ hx₁ x₂ hx₂) (ht.joinedIn y₁ hy₁ y₂ hy₂)
}

instance Prod.locPathConnectedSpace {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    [LocPathConnectedSpace X] [LocPathConnectedSpace Y] :
    LocPathConnectedSpace (X × Y) where
  path_connected_basis := fun (x, y) ↦ Filter.hasBasis_self.mpr fun U hU ↦ by {
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.mp hU
    exact ⟨pathComponentIn u x ×ˢ pathComponentIn v y,
      prod_mem_nhds (pathComponentIn_mem_nhds hu) (pathComponentIn_mem_nhds hv),
      IsPathConnected.prod (isPathConnected_pathComponentIn (mem_of_mem_nhds hu))
        (isPathConnected_pathComponentIn (mem_of_mem_nhds hv)),
      (Set.prod_mono pathComponentIn_subset pathComponentIn_subset).trans huv⟩
  }

lemma HasLogIncrement.homotopy {H : C(unitInterval × unitInterval, ℂ)}
    (hH : ∀ p, H p ≠ 0) (hloop : ∀ s, H (s, 1) = H (s, 0)) {q : ℂ}
    (h : HasLogIncrement ⟨fun t => H (0, t), by fun_prop⟩ q) :
    HasLogIncrement ⟨fun t => H (1, t), by fun_prop⟩ q := by
{
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).contractibleSpace
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩)
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).locPathConnectedSpace
  obtain ⟨A, hA⟩ := exists_log_lift_of_simplyConnected (0, 0) H hH
  have hi : HasLogIncrement ⟨fun t => H (0, t), by fun_prop⟩ (A (0, 1) - A (0, 0)) :=
    ⟨⟨fun t => A (0, t), by fun_prop⟩, fun t => hA (0, t), rfl⟩
  have hc := log_lifts_difference_constant
    (show Continuous (fun s => A (s, 1)) by fun_prop)
    (show Continuous (fun s => A (s, 0)) by fun_prop)
    (fun s => by rw [hA, hA, hloop]) (0 : unitInterval) 1
  refine ⟨⟨fun t => A (1, t), by fun_prop⟩, fun t => hA (1, t), ?_⟩
  change A (1, 1) - A (1, 0) = q
  exact hc.trans (hi.unique h)
}

lemma windingNumber_homotopy (H : C(unitInterval × unitInterval, ℂ))
    (hH : ∀ p, H p ≠ 0) (hloop : ∀ s, H (s, 1) = H (s, 0)) :
    windingNumber ⟨fun t => H (1, t), by fun_prop⟩ =
      windingNumber ⟨fun t => H (0, t), by fun_prop⟩ := by
{
  apply windingNumber_eq_of_logIncrement (hloop 1)
  exact (windingNumber_spec ⟨fun t => H (0, t), by fun_prop⟩ (hloop 0)
    (fun t => hH (0, t))).homotopy hH hloop
}

def loopIndex (γ : C(unitInterval, ℂ)) (a : ℂ) : ℤ :=
  windingNumber ⟨fun t => γ t - a, by fun_prop⟩

lemma loopIndex_eventually_eq (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    {a : ℂ} (ha : a ∉ range γ) : ∀ᶠ b in 𝓝 a, loopIndex γ b = loopIndex γ a := by
{
  have hn (t) : γ t - a ≠ 0 := sub_ne_zero.mpr (fun h => ha ⟨t, h⟩)
  obtain ⟨d, hd, hdist⟩ := isCompact_univ.exists_forall_le'
    (show ContinuousOn (fun t : unitInterval => ‖γ t - a‖) univ by fun_prop)
    (a := 0) (fun t _ => norm_pos_iff.mpr (hn t))
  filter_upwards [Metric.ball_mem_nhds a hd] with b hb
  apply windingNumber_perturb (by simp [hloop]) (by simp [hloop]) hn
  intro t
  change ‖(γ t - b) - (γ t - a)‖ < ‖γ t - a‖
  rw [show (γ t - b) - (γ t - a) = a - b by ring, norm_sub_rev]
  exact (show ‖b - a‖ < d by simpa [Metric.mem_ball, dist_eq_norm] using hb).trans_le (hdist t (mem_univ t))
}

lemma continuousOn_loopIndex (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    ContinuousOn (loopIndex γ) (range γ)ᶜ := by
{
  intro a ha
  apply ContinuousAt.continuousWithinAt
  have he : loopIndex γ =ᶠ[𝓝 a] fun _ => loopIndex γ a :=
    loopIndex_eventually_eq γ hloop ha
  exact continuousAt_const.congr he.symm
}

lemma hasLogIncrement_constant (a : ℂ) (ha : a ≠ 0) :
    HasLogIncrement (ContinuousMap.const unitInterval a) 0 := by
{
  exact ⟨ContinuousMap.const unitInterval (Complex.log a),
    fun _ => Complex.exp_log ha, sub_self _⟩
}

lemma loopIndex_eq_zero_of_norm_lt (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    {a : ℂ} (ha : ∀ t, ‖γ t‖ < ‖a‖) : loopIndex γ a = 0 := by
{
  have hane : a ≠ 0 := norm_pos_iff.mp ((norm_nonneg (γ 0)).trans_lt (ha 0))
  apply windingNumber_eq_of_logIncrement (by simp [hloop])
  have hh : HasLogIncrement ⟨fun t => γ t - a, by fun_prop⟩ 0 :=
    (hasLogIncrement_constant (-a) (neg_ne_zero.mpr hane)).perturb rfl
      (by simp [hloop]) (fun t => by simpa using ha t)
  simpa using hh
}

lemma loopIndex_zero_outside_ball (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    ∃ R : ℝ, 0 < R ∧ ∀ a : ℂ, R ≤ ‖a‖ → loopIndex γ a = 0 := by
{
  obtain ⟨R, -, hR⟩ := (isCompact_range γ.continuous).isBounded.exists_pos_norm_lt
  refine ⟨max R 1, lt_of_lt_of_le zero_lt_one (le_max_right _ _), ?_⟩
  intro a ha
  apply loopIndex_eq_zero_of_norm_lt γ hloop
  intro t
  exact (hR (γ t) ⟨t, rfl⟩).trans_le ((le_max_left R 1).trans ha)
}

def windingInterior (γ : C(unitInterval, ℂ)) : Set ℂ :=
  {a | a ∉ range γ ∧ loopIndex γ a ≠ 0}

lemma isOpen_windingInterior (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    IsOpen (windingInterior γ) := by
{
  apply isOpen_iff_mem_nhds.mpr
  intro a ha
  have hc := (isCompact_range γ.continuous).isClosed.isOpen_compl.mem_nhds ha.1
  filter_upwards [hc, loopIndex_eventually_eq γ hloop ha.1] with b hb heq
  exact ⟨hb, heq ▸ ha.2⟩
}

lemma isBounded_windingInterior (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    Bornology.IsBounded (windingInterior γ) := by
{
  obtain ⟨R, -, hR⟩ := loopIndex_zero_outside_ball γ hloop
  apply (Metric.isBounded_ball (x := (0 : ℂ)) (r := R)).subset
  intro a ha
  rw [Metric.mem_ball, dist_zero_right]
  by_contra h
  exact ha.2 (hR a (le_of_not_gt h))
}

lemma frontier_windingInterior_subset (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) :
    frontier (windingInterior γ) ⊆ range γ := by
{
  intro a ha
  by_contra han
  have he := loopIndex_eventually_eq γ hloop han
  by_cases hi : loopIndex γ a = 0
  · have hh : (windingInterior γ)ᶜ ∈ 𝓝 a := by
    {
      filter_upwards [he] with b hb hbin
      exact hbin.2 (hb.trans hi)
    }
    exact (mem_closure_iff_nhds.1 ha.1 _ hh).elim (fun b hb => hb.1 hb.2)
  · have hnmem := ha.2
    rw [(isOpen_windingInterior γ hloop).interior_eq] at hnmem
    exact hnmem ⟨han, hi⟩
}

/-!
## Part 2: Surgery and Degree Formula (`windingNumber_finite_regular_zeros`)
-/

def orientedDifference (positive : Bool) (a z : ℂ) : ℂ :=
  if positive then z - a else conj (z - a)

@[simp] lemma norm_orientedDifference (p : Bool) (a z : ℂ) :
    ‖orientedDifference p a z‖ = ‖z - a‖ := by
{
  cases p <;> simp only [orientedDifference, Bool.false_eq_true, ↓reduceIte, RCLike.norm_conj]
}

@[simp] lemma orientedDifference_eq_zero (p : Bool) (a z : ℂ) :
    orientedDifference p a z = 0 ↔ z = a := by
{
  rw [← norm_eq_zero, norm_orientedDifference, norm_eq_zero, sub_eq_zero]
}

lemma continuous_orientedDifference (p : Bool) (a : ℂ) :
    Continuous (orientedDifference p a) := by
{
  unfold orientedDifference
  cases p <;> simp only [Bool.false_eq_true, ↓reduceIte] <;> fun_prop
}

def radialCutoff (a : ℂ) (r : ℝ) (z : ℂ) : ℝ :=
  max 0 (min 1 (2 - 2 * ‖z - a‖ / r))

lemma continuous_radialCutoff (a : ℂ) (r : ℝ) : Continuous (radialCutoff a r) := by
{
  unfold radialCutoff
  fun_prop
}

lemma radialCutoff_one {a z : ℂ} {r : ℝ} (hr : 0 < r) (hz : ‖z - a‖ ≤ r / 2) :
    radialCutoff a r z = 1 := by
{
  have hb : 2 * ‖z - a‖ / r ≤ 1 := (div_le_iff₀ hr).mpr (by linarith)
  simp [radialCutoff, min_eq_left (by linarith : 1 ≤ 2 - 2 * ‖z - a‖ / r)]
}

lemma radialCutoff_zero {a z : ℂ} {r : ℝ} (hr : 0 < r) (hz : r ≤ ‖z - a‖) :
    radialCutoff a r z = 0 := by
{
  rw [radialCutoff, max_eq_left]
  apply min_le_of_right_le
  rw [sub_nonpos, le_div_iff₀ hr]
  linarith
}

def surgeryLog (X : ℂ → ℂ) (p : Bool) (a c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  (radialCutoff a r z : ℂ) * Complex.log (X z / (c * orientedDifference p a z))

lemma continuousAt_surgeryLog {X : ℂ → ℂ} (hX : Continuous X)
    {p : Bool} {a c z : ℂ} {r : ℝ} (hr : 0 < r) (hc : c ≠ 0) (hz : z ≠ a)
    (hlocal : ∀ w : ℂ, ‖w - a‖ < 2 * r → w ≠ a →
      X w / (c * orientedDifference p a w) ∈ Complex.slitPlane) :
    ContinuousAt (surgeryLog X p a c r) z := by
{
  by_cases hb : ‖z - a‖ < 2 * r
  · apply (Complex.continuous_ofReal.comp (continuous_radialCutoff a r)).continuousAt.mul
    apply ContinuousAt.clog
    · exact hX.continuousAt.div
        (continuous_const.mul (continuous_orientedDifference p a)).continuousAt
        (mul_ne_zero hc (mt (orientedDifference_eq_zero p a z).mp hz))
    · exact hlocal z hb hz
  · have hlt : r < ‖z - a‖ := by linarith
    have he : surgeryLog X p a c r =ᶠ[𝓝 z] fun _ => 0 := by
    {
      filter_upwards [((show ContinuousAt (fun w : ℂ => ‖w - a‖) z by fun_prop).eventually
        (Ioi_mem_nhds hlt))] with w hw
      simp [surgeryLog, radialCutoff_zero hr (le_of_lt hw)]
    }
    exact continuousAt_const.congr he.symm
}

lemma surgeryLog_eq_zero_eventually {X : ℂ → ℂ} {p : Bool} {a c z : ℂ} {r : ℝ}
    (hr : 0 < r) (hz : r < ‖z - a‖) : surgeryLog X p a c r =ᶠ[𝓝 z] fun _ => 0 := by
{
  filter_upwards [((show ContinuousAt (fun w : ℂ => ‖w - a‖) z by fun_prop).eventually
    (Ioi_mem_nhds hz))] with w hw
  simp [surgeryLog, radialCutoff_zero hr (le_of_lt hw)]
}

def removeZero (X : ℂ → ℂ) (p : Bool) (a c : ℂ) (r : ℝ) (z : ℂ) : ℂ :=
  if z = a then c else X z / orientedDifference p a z *
    Complex.exp (-surgeryLog X p a c r z)

lemma removeZero_eq_const_near {X : ℂ → ℂ} {p : Bool} {a c z : ℂ} {r : ℝ}
    (hr : 0 < r) (hc : c ≠ 0) (hz : ‖z - a‖ < r / 2)
    (hlocal : ∀ w : ℂ, ‖w - a‖ < 2 * r → w ≠ a →
      X w / (c * orientedDifference p a w) ∈ Complex.slitPlane) :
    removeZero X p a c r z = c := by
{
  by_cases hza : z = a
  · simp [removeZero, hza]
  · have hd : orientedDifference p a z ≠ 0 := mt (orientedDifference_eq_zero p a z).mp hza
    have hslit := hlocal z (by linarith) hza
    have hx : X z ≠ 0 := fun hx => by simpa [hx] using Complex.slitPlane_ne_zero hslit
    simp only [removeZero, ite_eq_right hza, surgeryLog, radialCutoff_one hr hz.le,
      Complex.ofReal_one, one_mul, Complex.exp_neg,
      Complex.exp_log (Complex.slitPlane_ne_zero hslit)]
    field_simp
}

lemma continuous_removeZero {X : ℂ → ℂ} (hX : Continuous X)
    {p : Bool} {a c : ℂ} {r : ℝ} (hr : 0 < r) (hc : c ≠ 0)
    (hlocal : ∀ w : ℂ, ‖w - a‖ < 2 * r → w ≠ a →
      X w / (c * orientedDifference p a w) ∈ Complex.slitPlane) :
    Continuous (removeZero X p a c r) := by
{
  apply continuous_iff_continuousAt.mpr
  intro z
  by_cases hz : z = a
  · subst z
    have he : removeZero X p a c r =ᶠ[𝓝 a] fun _ => c := by
    {
      filter_upwards [Metric.ball_mem_nhds a (by positivity : 0 < r / 2)] with w hw
      exact removeZero_eq_const_near hr hc (by simpa [Metric.mem_ball, dist_eq_norm] using hw) hlocal
    }
    exact continuousAt_const.congr he.symm
  · have he : removeZero X p a c r =ᶠ[𝓝 z] fun w =>
        X w / orientedDifference p a w * Complex.exp (-surgeryLog X p a c r w) := by
    {
      filter_upwards [isClosed_singleton.isOpen_compl.mem_nhds hz] with w hw
      have hwn : w ≠ a := hw
      simp [removeZero, hwn]
    }
    apply ContinuousAt.congr ?_ he.symm
    exact (hX.continuousAt.div (continuous_orientedDifference p a).continuousAt
      (mt (orientedDifference_eq_zero p a z).mp hz)).mul
      ((continuousAt_surgeryLog hX hr hc hz hlocal).neg.cexp)
}

lemma removeZero_eq_zero_iff {X : ℂ → ℂ} {p : Bool} {a c z : ℂ} {r : ℝ}
    (hc : c ≠ 0) : removeZero X p a c r z = 0 ↔ X z = 0 ∧ z ≠ a := by
{
  by_cases hz : z = a
  · simp [removeZero, hz, hc]
  · simp [removeZero, hz, div_eq_zero_iff,
      mt (orientedDifference_eq_zero p a z).mp hz, Complex.exp_ne_zero]
}

lemma removeZero_factorization {X : ℂ → ℂ} {p : Bool} {a c z : ℂ} {r : ℝ}
    (hz : z ≠ a) : X z = orientedDifference p a z * removeZero X p a c r z *
      Complex.exp (surgeryLog X p a c r z) := by
{
  have hd : orientedDifference p a z ≠ 0 := mt (orientedDifference_eq_zero p a z).mp hz
  simp only [removeZero, ite_eq_right hz, Complex.exp_neg]
  field_simp
}

lemma exists_slit_radius_of_derivative {X : ℂ → ℂ} {a c : ℂ} {A : ℂ →L[ℝ] ℂ}
    {p : Bool} (hzero : X a = 0) (hd : HasFDerivAt X A a)
    {b : ℝ} (hb : b < ‖c‖)
    (herr : ∀ w : ℂ, ‖A w - c * orientedDifference p 0 w‖ ≤ b * ‖w‖) :
    ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w - a‖ < 2 * r → w ≠ a →
      X w / (c * orientedDifference p a w) ∈ Complex.slitPlane := by
{
  have hrem := (hasFDerivAt_iff_isLittleO_nhds_zero.mp hd).bound (by linarith : 0 < (‖c‖ - b) / 2)
  obtain ⟨δ, hδ, hbound⟩ := Metric.eventually_nhds_iff.mp hrem
  refine ⟨δ / 3, by positivity, fun w hw hwa => ?_⟩
  have hwn : 0 < ‖w - a‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hwa)
  have hremw := hbound (show dist (w - a) 0 < δ by simpa only [dist_zero_right] using (show ‖w - a‖ < δ by linarith))
  simp only [add_sub_cancel, hzero, sub_zero] at hremw
  have her := herr (w - a)
  rw [show orientedDifference p 0 (w - a) = orientedDifference p a w by simp [orientedDifference]] at her
  have hlt : ‖X w - c * orientedDifference p a w‖ < ‖c * orientedDifference p a w‖ := by
  {
    calc
      ‖X w - c * orientedDifference p a w‖ =
          ‖(X w - A (w - a)) + (A (w - a) - c * orientedDifference p a w)‖ := by congr 1; ring
      _ ≤ ‖X w - A (w - a)‖ + ‖A (w - a) - c * orientedDifference p a w‖ := norm_add_le _ _
      _ ≤ (‖c‖ - b) / 2 * ‖w - a‖ + b * ‖w - a‖ := add_le_add hremw her
      _ < ‖c * orientedDifference p a w‖ := by rw [norm_mul, norm_orientedDifference]; nlinarith
  }
  have hcn : c * orientedDifference p a w ≠ 0 := norm_pos_iff.mp ((norm_nonneg _).trans_lt hlt)
  have hratio : X w / (c * orientedDifference p a w) =
      1 + (X w - c * orientedDifference p a w) / (c * orientedDifference p a w) := by
  {
    field_simp [left_ne_zero_of_mul hcn, right_ne_zero_of_mul hcn]
    ring
  }
  rw [hratio]
  apply Complex.mem_slitPlane_of_norm_lt_one
  rwa [norm_div, div_lt_one (norm_pos_iff.mpr hcn)]
}

lemma exists_slit_radius_pos {X : ℂ → ℂ} {a : ℂ} {A : ℂ →L[ℝ] ℂ}
    (hzero : X a = 0) (hd : HasFDerivAt X A a)
    (hdet : 0 < LinearMap.det A.toLinearMap) :
    linearPart A ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w - a‖ < 2 * r → w ≠ a →
      X w / (linearPart A * orientedDifference true a w) ∈ Complex.slitPlane := by
{
  have hn : ‖antiLinearPart A‖ < ‖linearPart A‖ := by
  {
    rw [det_eq_linearParts] at hdet
    nlinarith [norm_nonneg (linearPart A), norm_nonneg (antiLinearPart A)]
  }
  refine ⟨norm_pos_iff.mp ((norm_nonneg _).trans_lt hn),
    exists_slit_radius_of_derivative hzero hd hn ?_⟩
  intro w
  simp [realLinear_decomposition, orientedDifference, add_sub_cancel_left]
}

lemma exists_slit_radius_neg {X : ℂ → ℂ} {a : ℂ} {A : ℂ →L[ℝ] ℂ}
    (hzero : X a = 0) (hd : HasFDerivAt X A a)
    (hdet : LinearMap.det A.toLinearMap < 0) :
    antiLinearPart A ≠ 0 ∧ ∃ r : ℝ, 0 < r ∧ ∀ w : ℂ, ‖w - a‖ < 2 * r → w ≠ a →
      X w / (antiLinearPart A * orientedDifference false a w) ∈ Complex.slitPlane := by
{
  have hn : ‖linearPart A‖ < ‖antiLinearPart A‖ := by
  {
    rw [det_eq_linearParts] at hdet
    nlinarith [norm_nonneg (linearPart A), norm_nonneg (antiLinearPart A)]
  }
  refine ⟨norm_pos_iff.mp ((norm_nonneg _).trans_lt hn),
    exists_slit_radius_of_derivative hzero hd hn ?_⟩
  intro w
  simp [realLinear_decomposition, orientedDifference, add_sub_cancel_right]
}

lemma differentiable_orientedDifference (p : Bool) (a : ℂ) :
    Differentiable ℝ (orientedDifference p a) := by
{
  unfold orientedDifference
  cases p <;> simp only [Bool.false_eq_true, ↓reduceIte]
  · exact Complex.conjCLE.differentiable.comp (differentiable_id.sub_const a)
  · exact differentiable_id.sub_const a
}

lemma hasFDerivAt_removeZero_other {X : ℂ → ℂ} {p : Bool} {a b c : ℂ} {r : ℝ}
    (hr : 0 < r) (hb : b ≠ a) (hzero : X b = 0) {A : ℂ →L[ℝ] ℂ}
    (hX : HasFDerivAt X A b)
    (hlocal : ∀ w : ℂ, ‖w - a‖ < 2 * r → w ≠ a →
      X w / (c * orientedDifference p a w) ∈ Complex.slitPlane) :
    HasFDerivAt (removeZero X p a c r) ((orientedDifference p a b)⁻¹ • A) b := by
{
  have hbfar : r < ‖b - a‖ := by
  {
    by_contra hn
    have he := Complex.slitPlane_ne_zero (hlocal b (by linarith) hb)
    simp [hzero] at he
  }
  have he : removeZero X p a c r =ᶠ[𝓝 b] fun w => X w * (orientedDifference p a w)⁻¹ := by
  {
    filter_upwards [surgeryLog_eq_zero_eventually (X := X) (p := p) (c := c) hr hbfar,
      isClosed_singleton.isOpen_compl.mem_nhds hb] with w hw hwa
    have hwn : w ≠ a := hwa
    simp [removeZero, hwn, hw, div_eq_mul_inv]
  }
  have hdn : orientedDifference p a b ≠ 0 := mt (orientedDifference_eq_zero p a b).mp hb
  have hinv := ((hasDerivAt_inv hdn).hasFDerivAt.restrictScalars ℝ).comp b
    ((differentiable_orientedDifference p a b).hasFDerivAt)
  have hm := hX.fun_mul hinv
  simp only [hzero, zero_smul, zero_add] at hm
  exact hm.congr_of_eventuallyEq he
}

lemma det_complex_smul (c : ℂ) (A : ℂ →L[ℝ] ℂ) :
    LinearMap.det (c • A).toLinearMap = ‖c‖^2 * LinearMap.det A.toLinearMap := by
{
  rw [det_complex_real_eq, det_complex_real_eq, ← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.smul_apply, smul_eq_mul,
    Complex.mul_re, Complex.mul_im, Complex.normSq_apply]
  ring
}

lemma windingNumber_orientedDifference (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    (p : Bool) (a : ℂ) (ha : ∀ t, γ t ≠ a) :
    windingNumber ⟨fun t => orientedDifference p a (γ t),
      (continuous_orientedDifference p a).comp γ.continuous⟩ =
      (if p then 1 else -1) * loopIndex γ a := by
{
  cases p
  · change windingNumber ⟨fun t => conj (γ t - a), by fun_prop⟩ = -1 * loopIndex γ a
    rw [neg_one_mul]
    apply windingNumber_eq_of_logIncrement (by simp [hloop])
    have hh := (windingNumber_spec ⟨fun t => γ t - a, by fun_prop⟩
      (by simp [hloop]) (fun t => sub_ne_zero.mpr (ha t))).conj
    convert hh using 1
    · rfl
    · change ((-windingNumber ⟨fun t => γ t - a, by fun_prop⟩ : ℤ) : ℂ) *
        (2 * Real.pi * Complex.I) = _
      simp only [Int.cast_neg, map_mul, map_intCast, map_ofNat,
        Complex.conj_ofReal, Complex.conj_I]
      ring
  · simp only [↓reduceIte, one_mul]
    rfl
}

lemma windingNumber_removeZero_add {X : ℂ → ℂ} (hX : Continuous X)
    {p : Bool} {a c : ℂ} {r : ℝ} (hr : 0 < r) (hc : c ≠ 0)
    (hlocal : ∀ w : ℂ, ‖w - a‖ < 2 * r → w ≠ a →
      X w / (c * orientedDifference p a w) ∈ Complex.slitPlane)
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    (ha : ∀ t, γ t ≠ a) (hγ : ∀ t, X (γ t) ≠ 0) :
    windingNumber ((⟨X, hX⟩ : C(ℂ, ℂ)).comp γ) =
      (if p then 1 else -1) * loopIndex γ a +
      windingNumber ((⟨removeZero X p a c r, continuous_removeZero hX hr hc hlocal⟩ : C(ℂ, ℂ)).comp γ) := by
{
  let D : C(unitInterval, ℂ) := ⟨fun t => orientedDifference p a (γ t),
    (continuous_orientedDifference p a).comp γ.continuous⟩
  let Y : C(unitInterval, ℂ) :=
    (⟨removeZero X p a c r, continuous_removeZero hX hr hc hlocal⟩ : C(ℂ, ℂ)).comp γ
  let B : C(unitInterval, ℂ) := ⟨fun t => surgeryLog X p a c r (γ t), by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (continuousAt_surgeryLog hX hr hc (ha t) hlocal).comp γ.continuous.continuousAt⟩
  let E : C(unitInterval, ℂ) := ⟨fun t => Complex.exp (B t), by fun_prop⟩
  have hE : windingNumber E = 0 := by
  {
    apply windingNumber_eq_of_logIncrement (by simp [E, B, hloop])
    simpa using (show HasLogIncrement E 0 from ⟨B, fun _ => rfl, by simp [B, hloop]⟩)
  }
  have hD : ∀ t, D t ≠ 0 := fun t => mt (orientedDifference_eq_zero p a (γ t)).mp (ha t)
  have hY : ∀ t, Y t ≠ 0 := fun t h =>
    hγ t ((removeZero_eq_zero_iff hc).mp (show removeZero X p a c r (γ t) = 0 from h)).1
  have hfact : (⟨X, hX⟩ : C(ℂ, ℂ)).comp γ = D * Y * E := by
  {
    ext t
    exact removeZero_factorization (X := X) (c := c) (r := r) (p := p) (ha t)
  }
  rw [hfact, windingNumber_mul _ _ (by simp [D, Y, hloop]) (by simp [E, B, hloop])
      (fun t => mul_ne_zero (hD t) (hY t)) (fun t => Complex.exp_ne_zero _),
    hE, add_zero, windingNumber_mul _ _ (by simp [D, hloop]) (by simp [Y, hloop]) hD hY]
  rw [show windingNumber D = (if p then 1 else -1) * loopIndex γ a from
    windingNumber_orientedDifference γ hloop p a ha]
}

lemma windingNumber_comp_zero_on_convex (X : C(ℂ, ℂ)) {K : Set ℂ}
    (hK : Convex ℝ K) (hX : ∀ z ∈ K, X z ≠ 0)
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) (hγ : ∀ t, γ t ∈ K) :
    windingNumber (X.comp γ) = 0 := by
{
  let := hK.contractibleSpace ⟨γ 0, hγ 0⟩
  let := hK.locPathConnectedSpace
  let XK : C(K, ℂ) := ⟨fun z => X z, by fun_prop⟩
  obtain ⟨B, hB⟩ := exists_log_lift_of_simplyConnected (⟨γ 0, hγ 0⟩ : K) XK
    (fun z => hX z z.property)
  apply windingNumber_eq_of_logIncrement (by simp [hloop])
  refine ⟨⟨fun t => B ⟨γ t, hγ t⟩, by fun_prop⟩, fun t => hB ⟨γ t, hγ t⟩, ?_⟩
  simp only [Int.cast_zero, zero_mul]
  change B ⟨γ 1, hγ 1⟩ - B ⟨γ 0, hγ 0⟩ = 0
  simp only [hloop, sub_self]
}

def planeIndex (A : ℂ →L[ℝ] ℂ) : ℤ :=
  if 0 < LinearMap.det A.toLinearMap then 1 else -1

lemma planeIndex_complex_smul {c : ℂ} (hc : c ≠ 0) (A : ℂ →L[ℝ] ℂ) :
    planeIndex (c • A) = planeIndex A := by
{
  have hp : 0 < ‖c‖^2 := sq_pos_of_pos (norm_pos_iff.mpr hc)
  simp only [planeIndex, det_complex_smul, mul_pos_iff_of_pos_left hp]
}

lemma exists_slit_radius_sign {X : ℂ → ℂ} {a : ℂ} {A : ℂ →L[ℝ] ℂ}
    (haz : X a = 0) (hDa : HasFDerivAt X A a) (hdet : LinearMap.det A.toLinearMap ≠ 0) :
    ∃ (p : Bool) (c : ℂ) (r : ℝ),
      0 < r ∧ c ≠ 0 ∧ (if p then (1 : ℤ) else -1) = planeIndex A ∧
      ∀ w : ℂ, ‖w - a‖ < 2 * r → w ≠ a →
        X w / (c * orientedDifference p a w) ∈ Complex.slitPlane := by
{
  rcases lt_or_gt_of_ne hdet with hn | hp
  · obtain ⟨hc, r, hr, hl⟩ := exists_slit_radius_neg haz hDa hn
    exact ⟨false, antiLinearPart A, r, hr, hc, by simp [planeIndex, not_lt.mpr hn.le], hl⟩
  · obtain ⟨hc, r, hr, hl⟩ := exists_slit_radius_pos haz hDa hp
    exact ⟨true, linearPart A, r, hr, hc, by simp [planeIndex, hp], hl⟩
}

theorem windingNumber_finite_regular_zeros {K : Set ℂ} (hK : Convex ℝ K)
    (s : Finset ℂ) (X : C(ℂ, ℂ)) (A : ℂ → ℂ →L[ℝ] ℂ)
    (hsK : ∀ z ∈ s, z ∈ K) (hzero : ∀ z ∈ K, X z = 0 ↔ z ∈ s)
    (hD : ∀ z ∈ s, HasFDerivAt X (A z) z ∧ LinearMap.det (A z).toLinearMap ≠ 0)
    (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0) (hγK : ∀ t, γ t ∈ K)
    (hγ : ∀ t, X (γ t) ≠ 0) :
    windingNumber (X.comp γ) = ∑ a ∈ s, planeIndex (A a) * loopIndex γ a := by
{
  induction s using Finset.induction_on generalizing X A with
  | empty =>
      simp only [Finset.sum_empty]
      exact windingNumber_comp_zero_on_convex X hK
        (fun z hz h => Finset.notMem_empty z ((hzero z hz).mp h)) γ hloop hγK
  | @insert a s ha ih =>
      have ham : a ∈ insert a s := Finset.mem_insert_self a s
      have haz : X a = 0 := (hzero a (hsK a ham)).mpr ham
      obtain ⟨p, c, r, hr, hc, hsign, hlocal⟩ :=
        exists_slit_radius_sign haz (hD a ham).1 (hD a ham).2
      let Y : C(ℂ, ℂ) := ⟨removeZero X p a c r, continuous_removeZero X.continuous hr hc hlocal⟩
      let D : ℂ → ℂ →L[ℝ] ℂ := fun b => (orientedDifference p a b)⁻¹ • A b
      have hbne (b : ℂ) (hb : b ∈ s) : b ≠ a := fun he => ha (he ▸ hb)
      have hdc (b : ℂ) (hb : b ∈ s) : (orientedDifference p a b)⁻¹ ≠ 0 :=
        inv_ne_zero (mt (orientedDifference_eq_zero p a b).mp (hbne b hb))
      have hsK' : ∀ z ∈ s, z ∈ K := fun z hz => hsK z (Finset.mem_insert_of_mem hz)
      have hYzero : ∀ z ∈ K, Y z = 0 ↔ z ∈ s := fun z hz => by
        change removeZero X p a c r z = 0 ↔ _
        rw [removeZero_eq_zero_iff hc, hzero z hz, Finset.mem_insert]
        exact ⟨fun ⟨h, hne⟩ => h.resolve_left hne, fun h => ⟨Or.inr h, hbne z h⟩⟩
      have hDY : ∀ z ∈ s, HasFDerivAt Y (D z) z ∧ LinearMap.det (D z).toLinearMap ≠ 0 := by
      {
        intro z hz
        obtain ⟨hDz, hdz⟩ := hD z (Finset.mem_insert_of_mem hz)
        refine ⟨hasFDerivAt_removeZero_other hr (hbne z hz)
          ((hzero z (hsK' z hz)).mpr (Finset.mem_insert_of_mem hz)) hDz hlocal, ?_⟩
        dsimp only [D]; rw [det_complex_smul]
        exact mul_ne_zero (pow_ne_zero _ (norm_ne_zero_iff.mpr (hdc z hz))) hdz
      }
      have hγa : ∀ t, γ t ≠ a := fun t ht => hγ t (ht ▸ haz)
      have hγY : ∀ t, Y (γ t) ≠ 0 := fun t ht =>
        hγ t ((removeZero_eq_zero_iff hc).mp (show removeZero X p a c r (γ t) = 0 from ht)).1
      have hi := ih Y D hsK' hYzero hDY hγY
      have hsigns : (∑ b ∈ s, planeIndex (D b) * loopIndex γ b) =
          ∑ b ∈ s, planeIndex (A b) * loopIndex γ b :=
        Finset.sum_congr rfl (fun b hb => by dsimp only [D]; rw [planeIndex_complex_smul (hdc b hb)])
      rw [Finset.sum_insert ha]
      have hrem := windingNumber_removeZero_add X.continuous hr hc hlocal γ hloop hγa hγ
      change windingNumber (X.comp γ) = (if p then (1 : ℤ) else -1) * loopIndex γ a +
        windingNumber (Y.comp γ) at hrem
      rw [hrem, hsign, hi, hsigns]
}

lemma exists_smooth_cutoff {K U : Set ℂ} (hK : IsCompact K) (hU : IsOpen U)
    (hKU : K ⊆ U) :
    ∃ χ : ℂ → ℝ, ContDiff ℝ 2 χ ∧ HasCompactSupport χ ∧ tsupport χ ⊆ U ∧
      (∀ z ∈ K, χ =ᶠ[𝓝 z] fun _ => 1) ∧ ∀ z, χ z ∈ Icc 0 1 := by
{
  obtain ⟨L, hL, hLc, hKL, hLU⟩ := exists_compact_closed_between hK hU hKU
  obtain ⟨χ, hχ1, hχ0, hχrange⟩ :=
    exists_contMDiffMap_one_nhds_of_subset_interior 𝓘(ℝ, ℂ) hK.isClosed hKL (n := 2)
  have hs : tsupport (χ : ℂ → ℝ) ⊆ L := by
  {
    apply closure_minimal _ hLc
    intro z hz
    by_contra hn
    exact hz (hχ0 z hn)
  }
  refine ⟨χ, contMDiff_iff_contDiff.mp χ.contMDiff,
    hL.of_isClosed_subset (isClosed_tsupport _) hs, hs.trans hLU, ?_, hχrange⟩
  intro z hz
  exact hχ1.filter_mono (nhds_le_nhdsSet hz)
}

lemma det_fderiv_complex {f : ℂ → ℂ} {z : ℂ} (hd : DifferentiableAt ℂ f z) :
    LinearMap.det (fderiv ℝ f z).toLinearMap = ‖deriv f z‖^2 := by
{
  rw [(hd.hasDerivAt.hasFDerivAt.restrictScalars ℝ).fderiv, det_complex_real_eq,
    ← Complex.normSq_eq_norm_sq]
  simp only [ContinuousLinearMap.coe_coe, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul, one_mul,
    Complex.I_mul, Complex.normSq_apply]
  ring
}

lemma finite_regular_zeros_on_compact {K : Set ℂ} (hK : IsCompact K)
    {X : ℂ → ℂ} (hc : ContinuousOn X K)
    (hd : ∀ z ∈ K, X z = 0 → DifferentiableAt ℝ X z ∧
      LinearMap.det (fderiv ℝ X z).toLinearMap ≠ 0) :
    {z | z ∈ K ∧ X z = 0}.Finite := by
{
  have hZ : IsCompact {z | z ∈ K ∧ X z = 0} :=
    hK.of_isClosed_subset (hc.preimage_isClosed_of_isClosed hK.isClosed isClosed_singleton)
      inter_subset_left
  apply hZ.finite
  rw [isDiscrete_iff_nhdsNE]
  intro z hz
  obtain ⟨hzD, hzd⟩ := hd z hz.1 hz.2
  let e : ℂ ≃L[ℝ] ℂ :=
    (LinearMap.equivOfIsUnitDet (isUnit_iff_ne_zero.mpr hzd)).toContinuousLinearEquiv
  have he : (e : ℂ → ℂ) = fderiv ℝ X z :=
    funext (fun w => LinearMap.equivOfIsUnitDet_apply (isUnit_iff_ne_zero.mpr hzd) w)
  have ha : ∃ C, AntilipschitzWith C (fderiv ℝ X z) := by
  {
    rw [← he]
    exact ⟨_, e.antilipschitz⟩
  }
  rw [Filter.inf_principal_eq_bot]
  filter_upwards [hzD.hasFDerivAt.eventually_ne (c := 0) ha] with w hw
  exact fun h => hw h.2
}

/-!
## Part 3: Transverse Crossing and Winding Jump (`Winding.lean`)
-/

lemma HasLogIncrement.path_trans {a b c : ℂ} {γ : Path a b} {η : Path b c}
    {p q : ℂ} (hγ : HasLogIncrement γ.toContinuousMap p)
    (hη : HasLogIncrement η.toContinuousMap q) :
    HasLogIncrement (γ.trans η).toContinuousMap (p + q) := by
{
  obtain ⟨A, hA, hp⟩ := hγ
  obtain ⟨B, hB, hq⟩ := hη
  let α : Path (A 0) (A 1) := ⟨A, rfl, rfl⟩
  let β : Path (A 1) (B 1 + A 1 - B 0) :=
    ⟨⟨fun t => B t + A 1 - B 0, by fun_prop⟩, by simp, rfl⟩
  refine ⟨(α.trans β).toContinuousMap, fun t => ?_, ?_⟩
  · change Complex.exp ((α.trans β) t) = (γ.trans η) t
    rw [Path.trans_apply, Path.trans_apply]
    split_ifs with h
    · exact hA _
    · dsimp only [β, ContinuousMap.coe_mk, Path.coe_mk_mk]
      have heA : Complex.exp (A 1) = b := (hA 1).trans γ.target
      have heB : Complex.exp (B 0) = b := (hB 0).trans η.source
      have hb : b ≠ 0 := heB ▸ Complex.exp_ne_zero (B 0)
      rw [Complex.exp_sub, Complex.exp_add, heA, heB, hB]
      exact mul_div_cancel_right₀ _ hb
  · change (α.trans β) 1 - (α.trans β) 0 = p + q
    simp only [Path.target, Path.source]
    linear_combination hp + hq
}

lemma HasLogIncrement.path_symm {a b : ℂ} {γ : Path a b} {q : ℂ}
    (hγ : HasLogIncrement γ.toContinuousMap q) :
    HasLogIncrement γ.symm.toContinuousMap (-q) := by
{
  obtain ⟨A, hA, hq⟩ := hγ
  refine ⟨⟨fun t => A (unitInterval.symm t), by fun_prop⟩, fun t => hA (unitInterval.symm t), ?_⟩
  simp only [ContinuousMap.coe_mk, unitInterval.symm_one, unitInterval.symm_zero]
  linear_combination -hq
}

lemma exists_path_logIncrement {a b : ℂ} (γ : Path a b) (hn : ∀ t, γ t ≠ 0) :
    ∃ q, HasLogIncrement γ.toContinuousMap q := by
{
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).contractibleSpace
    (show (Icc (0 : ℝ) 1).Nonempty from ⟨0, by simp⟩)
  let := (convex_Icc (𝕜 := ℝ) (0 : ℝ) 1).locPathConnectedSpace
  obtain ⟨A, hA⟩ := exists_log_lift_of_simplyConnected (0 : unitInterval) γ.toContinuousMap hn
  exact ⟨A 1 - A 0, A, hA, rfl⟩
}

lemma HasLogIncrement.of_slit (γ : C(unitInterval, ℂ))
    (hγ : ∀ t, γ t ∈ Complex.slitPlane) :
    HasLogIncrement γ (Complex.log (γ 1) - Complex.log (γ 0)) := by
{
  exact ⟨⟨fun t => Complex.log (γ t), γ.continuous.clog hγ⟩,
    fun t => Complex.exp_log (Complex.slitPlane_ne_zero (hγ t)), rfl⟩
}

lemma HasLogIncrement.of_neg_slit (γ : C(unitInterval, ℂ))
    (hγ : ∀ t, -γ t ∈ Complex.slitPlane) :
    HasLogIncrement γ (Complex.log (-γ 1) - Complex.log (-γ 0)) := by
{
  refine ⟨⟨fun t => Complex.log (-γ t) + (Real.pi : ℂ) * Complex.I,
    ((γ.continuous.neg).clog hγ).add continuous_const⟩, fun t => ?_, ?_⟩
  · simp only [ContinuousMap.coe_mk, Complex.exp_add, Complex.exp_pi_mul_I]
    rw [Complex.exp_log (Complex.slitPlane_ne_zero (hγ t))]
    ring
  · dsimp only [ContinuousMap.coe_mk]
    ring
}

lemma log_neg_of_im_neg {z : ℂ} (hi : z.im < 0) :
    Complex.log (-z) = Complex.log z + (Real.pi : ℂ) * Complex.I := by
{
  apply Complex.ext
  · simp [Complex.log_re, norm_neg]
  · simpa [Complex.log_im] using Complex.arg_neg_eq_arg_add_pi_of_im_neg hi
}

lemma log_neg_of_im_pos {z : ℂ} (hi : 0 < z.im) :
    Complex.log (-z) = Complex.log z - (Real.pi : ℂ) * Complex.I := by
{
  apply Complex.ext
  · simp [Complex.log_re, norm_neg]
  · simpa [Complex.log_im] using Complex.arg_neg_eq_arg_sub_pi_of_im_pos hi
}

def rectPath (r h : ℝ) : Path ((-r : ℂ) - (h : ℂ) * Complex.I)
    ((-r : ℂ) - (h : ℂ) * Complex.I) :=
  (((Path.segment ((-r : ℂ) - (h : ℂ) * Complex.I) ((r : ℂ) - (h : ℂ) * Complex.I)).trans
    (Path.segment ((r : ℂ) - (h : ℂ) * Complex.I) ((r : ℂ) + (h : ℂ) * Complex.I))).trans
    (Path.segment ((r : ℂ) + (h : ℂ) * Complex.I) ((-r : ℂ) + (h : ℂ) * Complex.I))).trans
    (Path.segment ((-r : ℂ) + (h : ℂ) * Complex.I) ((-r : ℂ) - (h : ℂ) * Complex.I))

lemma rectPath_logIncrement {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    HasLogIncrement (rectPath r h).toContinuousMap (2 * Real.pi * Complex.I) := by
{
  let a : ℂ := (-r : ℂ) - (h : ℂ) * Complex.I
  let b : ℂ := (r : ℂ) - (h : ℂ) * Complex.I
  let c : ℂ := (r : ℂ) + (h : ℂ) * Complex.I
  let d : ℂ := (-r : ℂ) + (h : ℂ) * Complex.I
  have hab (t : unitInterval) : (Path.segment a b) t ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (by
      simp only [Path.segment_apply, AffineMap.lineMap_apply_module, a, b, Complex.add_im,
        Complex.sub_im, Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_im]; nlinarith))
  have hbc (t : unitInterval) : (Path.segment b c) t ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by
      simp only [Path.segment_apply, AffineMap.lineMap_apply_module, b, c, Complex.add_re,
        Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im]; nlinarith))
  have hcd (t : unitInterval) : (Path.segment c d) t ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inr (by
      simp only [Path.segment_apply, AffineMap.lineMap_apply_module, c, d, Complex.add_im,
        Complex.real_smul, Complex.mul_im, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_im]; nlinarith))
  have hda (t : unitInterval) : -(Path.segment d a) t ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr (Or.inl (by
      simp only [Path.segment_apply, AffineMap.lineMap_apply_module, d, a, Complex.add_re,
        Complex.sub_re, Complex.real_smul, Complex.mul_re, Complex.ofReal_re,
        Complex.ofReal_im, Complex.I_re, Complex.I_im, Complex.neg_re]; nlinarith))
  have h₁ := HasLogIncrement.of_slit (Path.segment a b).toContinuousMap hab
  have h₂ := HasLogIncrement.of_slit (Path.segment b c).toContinuousMap hbc
  have h₃ := HasLogIncrement.of_slit (Path.segment c d).toContinuousMap hcd
  have h₄ := HasLogIncrement.of_neg_slit (Path.segment d a).toContinuousMap hda
  have he := ((h₁.path_trans h₂).path_trans h₃).path_trans h₄
  have hla := log_neg_of_im_neg (show a.im < 0 by simpa [a] using hh)
  have hld := log_neg_of_im_pos (show 0 < d.im by simpa [d] using hh)
  convert he using 1
  · rfl
  · simp only [Path.coe_toContinuousMap, Path.target, Path.source]
    rw [hla, hld]; ring
}

lemma rectPath_winding {r h : ℝ} (hr : 0 < r) (hh : 0 < h) :
    windingNumber (rectPath r h).toContinuousMap = 1 := by
{
  apply windingNumber_eq_of_logIncrement ((rectPath r h).target.trans (rectPath r h).source.symm)
  simpa only [Int.cast_one, one_mul] using rectPath_logIncrement hr hh
}

lemma windingNumber_path_symm {a b : ℂ} (γ : Path a b)
    (hc : γ 1 = γ 0) (hn : ∀ t, γ t ≠ 0) :
    windingNumber γ.symm.toContinuousMap = -windingNumber γ.toContinuousMap := by
{
  apply windingNumber_eq_of_logIncrement (by simpa using hc.symm)
  convert (windingNumber_spec γ.toContinuousMap hc hn).path_symm using 1
  push_cast
  ring
}

lemma windingNumber_four_paths {a b c d : ℂ}
    (α : Path a b) (β : Path b c) (χ : Path c d) (δ : Path d a)
    (hβc : β 1 = β 0) (hδc : δ 1 = δ 0)
    (hχ : χ.toContinuousMap = α.symm.toContinuousMap)
    (hα : ∀ t, α t ≠ 0) (hβ : ∀ t, β t ≠ 0) (hδ : ∀ t, δ t ≠ 0) :
    windingNumber (((α.trans β).trans χ).trans δ).toContinuousMap =
      windingNumber β.toContinuousMap + windingNumber δ.toContinuousMap := by
{
  obtain ⟨p, hp⟩ := exists_path_logIncrement α hα
  have hq := windingNumber_spec β.toContinuousMap hβc hβ
  have hr := windingNumber_spec δ.toContinuousMap hδc hδ
  have hs : HasLogIncrement χ.toContinuousMap (-p) := hχ ▸ hp.path_symm
  apply windingNumber_eq_of_logIncrement
    ((((α.trans β).trans χ).trans δ).target.trans
      (((α.trans β).trans χ).trans δ).source.symm)
  convert ((hp.path_trans hq).path_trans hs).path_trans hr using 1
  push_cast
  ring
}

lemma rectPath_top_eq_bottom_symm (H_fn : ℂ → ℂ) (hH : Continuous H_fn) (r h : ℝ)
    (hp : ∀ x : ℝ, H_fn ((x : ℂ) + (h : ℂ) * Complex.I) = H_fn ((x : ℂ) - (h : ℂ) * Complex.I)) :
    ((Path.segment ((r : ℂ) + (h : ℂ) * Complex.I) ((-r : ℂ) + (h : ℂ) * Complex.I)).map hH).toContinuousMap =
      ((Path.segment ((-r : ℂ) - (h : ℂ) * Complex.I) ((r : ℂ) - (h : ℂ) * Complex.I)).map hH).symm.toContinuousMap := by
{
  ext t
  simp only [Path.coe_toContinuousMap, Path.map_coe, Function.comp_apply, Path.symm_apply,
    Path.segment_apply, AffineMap.lineMap_apply_module]
  have he₁ : (1 - (t : ℝ)) • ((r : ℂ) + (h : ℂ) * Complex.I) + (t : ℝ) • ((-r : ℂ) + (h : ℂ) * Complex.I) =
      (((1 - (t : ℝ)) * r + (t : ℝ) * (-r) : ℝ) : ℂ) + (h : ℂ) * Complex.I := by
  {
    simp [Complex.real_smul]; ring
  }
  have he₂ : (1 - (unitInterval.symm t : ℝ)) • ((-r : ℂ) - (h : ℂ) * Complex.I) +
      (unitInterval.symm t : ℝ) • ((r : ℂ) - (h : ℂ) * Complex.I) =
      (((1 - (t : ℝ)) * r + (t : ℝ) * (-r) : ℝ) : ℂ) - (h : ℂ) * Complex.I := by
  {
    simp [Complex.real_smul]; ring
  }
  rw [he₁, he₂]
  exact hp _
}

lemma windingNumber_rect_map (H_fn : ℂ → ℂ) (hH : Continuous H_fn) (r h : ℝ)
    (hp : ∀ x : ℝ, H_fn ((x : ℂ) + (h : ℂ) * Complex.I) =
      H_fn ((x : ℂ) - (h : ℂ) * Complex.I))
    (hn : ∀ z ∈ range (rectPath r h), H_fn z ≠ 0) :
    windingNumber (((rectPath r h).map hH).toContinuousMap) =
      windingNumber (((Path.segment ((r : ℂ) - (h : ℂ) * Complex.I)
        ((r : ℂ) + (h : ℂ) * Complex.I)).map hH).toContinuousMap) -
      windingNumber (((Path.segment ((-r : ℂ) - (h : ℂ) * Complex.I)
        ((-r : ℂ) + (h : ℂ) * Complex.I)).map hH).toContinuousMap) := by
{
  let a : ℂ := (-r : ℂ) - (h : ℂ) * Complex.I
  let b : ℂ := (r : ℂ) - (h : ℂ) * Complex.I
  let c : ℂ := (r : ℂ) + (h : ℂ) * Complex.I
  let d : ℂ := (-r : ℂ) + (h : ℂ) * Complex.I
  let α := (Path.segment a b).map hH
  let β := (Path.segment b c).map hH
  let χ := (Path.segment c d).map hH
  let δ := (Path.segment d a).map hH
  have hβc : β 1 = β 0 := β.target.trans ((hp r).trans β.source.symm)
  have hδp : H_fn d = H_fn a := by simpa only [d, a, Complex.ofReal_neg] using hp (-r)
  have hδc : δ 1 = δ 0 := δ.target.trans (hδp.symm.trans δ.source.symm)
  have hsub : range (Path.segment a b) ∪ range (Path.segment b c) ∪
      range (Path.segment c d) ∪ range (Path.segment d a) ⊆ range (rectPath r h) := by
  {
    intro z hz
    change z ∈ range ((((Path.segment a b).trans (Path.segment b c)).trans
      (Path.segment c d)).trans (Path.segment d a))
    simpa only [Path.trans_range] using hz
  }
  have hα : ∀ t, α t ≠ 0 := fun t => hn _ (hsub (Or.inl (Or.inl (Or.inl ⟨t, rfl⟩))))
  have hβ : ∀ t, β t ≠ 0 := fun t => hn _ (hsub (Or.inl (Or.inl (Or.inr ⟨t, rfl⟩))))
  have hδ : ∀ t, δ t ≠ 0 := fun t => hn _ (hsub (Or.inr ⟨t, rfl⟩))
  have hi := windingNumber_four_paths α β χ δ hβc hδc (rectPath_top_eq_bottom_symm H_fn hH r h hp) hα hβ hδ
  have hs := windingNumber_path_symm δ hδc hδ
  have he : δ.symm.toContinuousMap = ((Path.segment a d).map hH).toContinuousMap := by
  {
    ext t; simp [δ, Path.segment_symm]
  }
  rw [he] at hs
  have hg : (((rectPath r h).map hH).toContinuousMap) =
      (((α.trans β).trans χ).trans δ).toContinuousMap := by simp only [rectPath, Path.map_trans]; rfl
  rw [hg, hi]
  change windingNumber β.toContinuousMap + windingNumber δ.toContinuousMap =
    windingNumber β.toContinuousMap - windingNumber ((Path.segment a d).map hH).toContinuousMap
  linarith
}

lemma transverse_hasFDerivAt {γ : ℝ → ℂ} {d : ℂ} (hd : HasDerivAt γ d 0) :
    HasFDerivAt (fun w : ℂ => γ w.im - γ 0 - w.re • (Complex.I * d))
      ((-Complex.I * d) • ContinuousLinearMap.id ℝ ℂ) 0 := by
{
  have h := ((hd.hasFDerivAt.comp (0 : ℂ) (Complex.imCLM.hasFDerivAt)).sub_const
    (γ 0)).sub (Complex.reCLM.hasFDerivAt.smul_const (Complex.I * d))
  have he : ContinuousLinearMap.toSpanSingleton ℝ d ∘L Complex.imCLM -
      Complex.reCLM.smulRight (Complex.I * d) =
      (-Complex.I * d) • ContinuousLinearMap.id ℝ ℂ := by
  {
    ext z
    apply Complex.ext <;> simp [Complex.real_smul] <;> ring
  }
  rwa [he] at h
}

lemma det_transverse_pos {d : ℂ} (hd : d ≠ 0) :
    0 < LinearMap.det (((-Complex.I * d) • ContinuousLinearMap.id ℝ ℂ).toLinearMap) := by
{
  rw [det_complex_smul]
  simp only [ContinuousLinearMap.coe_id, LinearMap.det_id, mul_one]
  exact sq_pos_of_pos (norm_pos_iff.mpr (mul_ne_zero (neg_ne_zero.mpr Complex.I_ne_zero) hd))
}

lemma periodic_simple_zero {γ : ℝ → ℂ} (hp : Function.Periodic γ 1)
    (hinj : InjOn γ (Ico (0 : ℝ) 1)) {t : ℝ} (ht : t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2))
    (he : γ t = γ 0) : t = 0 := by
{
  by_cases hn : 0 ≤ t
  · exact hinj ⟨hn, by linarith [ht.2]⟩ ⟨le_rfl, by norm_num⟩ he
  · have hne : t + 1 = 0 := hinj ⟨by linarith [ht.1], by linarith⟩
      ⟨le_rfl, by norm_num⟩ ((hp t).trans he)
    linarith [ht.1]
}

lemma transverse_exists_lower_bound {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {η : ℝ} (hη : 0 < η) :
    ∃ m > 0, ∀ t ∈ Icc (-(1 / 2 : ℝ)) (1 / 2), η ≤ |t| → m ≤ ‖γ t - γ 0‖ := by
{
  let K : Set ℝ := Icc (-(1 / 2 : ℝ)) (1 / 2) ∩ {t | η ≤ |t|}
  have hK : IsCompact K := isCompact_Icc.inter_right (isClosed_le continuous_const continuous_abs)
  obtain ⟨m, hm, hbound⟩ := hK.exists_forall_le' ((hc.sub continuous_const).norm.continuousOn)
    (a := (0 : ℝ)) (fun t ht => norm_pos_iff.mpr (sub_ne_zero.mpr (by
      intro he
      have he0 := periodic_simple_zero hp hinj ht.1 he
      have hb : η ≤ |t| := ht.2
      simp only [he0, abs_zero] at hb
      exact (not_le.mpr hη) hb)))
  exact ⟨m, hm, fun t ht1 ht2 => hbound t ⟨ht1, ht2⟩⟩
}

lemma transverse_unique_zero_strip {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {d : ℂ} (hd : HasDerivAt γ d 0) (hdn : d ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ w : ℂ, |w.re| ≤ δ → |w.im| ≤ 1 / 2 →
      (γ w.im - γ 0 - w.re • (Complex.I * d) = 0 ↔ w = 0) := by
{
  let H_fn : ℂ → ℂ := fun w => γ w.im - γ 0 - w.re • (Complex.I * d)
  have hH0 : H_fn 0 = 0 := by simp [H_fn]
  obtain ⟨_, r, hr, hlocal⟩ := exists_slit_radius_pos hH0 (transverse_hasFDerivAt hd)
    (det_transverse_pos hdn)
  let η := min (r / 2) (1 / 4 : ℝ)
  have hη : 0 < η := lt_min (by linarith) (by norm_num)
  obtain ⟨m, hm, hbound⟩ := transverse_exists_lower_bound hc hp hinj hη
  let δ := min (r / 2) (m / (2 * ‖d‖))
  have hδ : 0 < δ := lt_min (by linarith) (div_pos hm (by positivity))
  refine ⟨δ, hδ, fun w hre him => ⟨fun hz => ?_, fun h => by subst h; simp⟩⟩
  by_contra hwn
  by_cases hi : |w.im| < η
  · have hn : ‖w - 0‖ < 2 * r := by
    {
      simpa only [sub_zero] using calc
        ‖w‖ ≤ |w.re| + |w.im| := Complex.norm_le_abs_re_add_abs_im w
        _ < r / 2 + r / 2 := by
          have h1 : |w.re| ≤ r / 2 := hre.trans (min_le_left _ _)
          have h2 : |w.im| < r / 2 := hi.trans_le (min_le_left _ _)
          linarith
        _ < 2 * r := by linarith
    }
    exact Complex.slitPlane_ne_zero (hlocal w hn hwn) (by simp only [H_fn, hz, zero_div])
  · have hb := hbound w.im (abs_le.mp him) (not_lt.mp hi)
    have hnorm : ‖γ w.im - γ 0‖ = |w.re| * ‖d‖ := by
    {
      rw [sub_eq_zero.mp hz, norm_smul, Real.norm_eq_abs, norm_mul, Complex.norm_I, one_mul]
    }
    have hδm : δ * ‖d‖ ≤ m / 2 := by
    {
      apply (le_div_iff₀ (norm_pos_iff.mpr hdn)).mp
      convert min_le_right (r / 2) (m / (2 * ‖d‖)) using 1; field_simp
    }
    have : |w.re| * ‖d‖ ≤ m / 2 := (mul_le_mul_of_nonneg_right hre (norm_nonneg d)).trans hδm
    linarith
}

def rectRegion (r h : ℝ) : Set ℂ := {z | |z.re| ≤ r ∧ |z.im| ≤ h}

lemma convex_rectRegion (r h : ℝ) : Convex ℝ (rectRegion r h) := by
{
  have he : rectRegion r h = (Complex.reCLM ⁻¹' Icc (-r) r) ∩
      (Complex.imCLM ⁻¹' Icc (-h) h) := by
  {
    ext z
    simp [rectRegion, abs_le]
  }
  rw [he]
  exact ((convex_Icc (-r) r).linear_preimage Complex.reCLM.toLinearMap).inter
    ((convex_Icc (-h) h).linear_preimage Complex.imCLM.toLinearMap)
}

lemma rectPath_mem {r h : ℝ} (hr : 0 ≤ r) (hh : 0 ≤ h) (t : unitInterval) :
    rectPath r h t ∈ rectRegion r h := by
{
  have hs (a b : ℂ) (ha : a ∈ rectRegion r h) (hb : b ∈ rectRegion r h) :
      range (Path.segment a b) ⊆ rectRegion r h := by
  {
    rintro _ ⟨s, rfl⟩
    simpa only [Path.segment_apply, AffineMap.lineMap_apply_module] using
      (convex_rectRegion r h) ha hb (sub_nonneg.mpr s.2.2) s.2.1 (by ring)
  }
  have h₁ : ((-r : ℂ) - (h : ℂ) * Complex.I) ∈ rectRegion r h := by
    simp [rectRegion, abs_of_nonneg hr, abs_of_nonneg hh]
  have h₂ : ((r : ℂ) - (h : ℂ) * Complex.I) ∈ rectRegion r h := by
    simp [rectRegion, abs_of_nonneg hr, abs_of_nonneg hh]
  have h₃ : ((r : ℂ) + (h : ℂ) * Complex.I) ∈ rectRegion r h := by
    simp [rectRegion, abs_of_nonneg hr, abs_of_nonneg hh]
  have h₄ : ((-r : ℂ) + (h : ℂ) * Complex.I) ∈ rectRegion r h := by
    simp [rectRegion, abs_of_nonneg hr, abs_of_nonneg hh]
  have hb : range (rectPath r h) ⊆ rectRegion r h := by
  {
    simp only [rectPath, Path.trans_range]
    exact union_subset (union_subset (union_subset (hs _ _ h₁ h₂) (hs _ _ h₂ h₃))
      (hs _ _ h₃ h₄)) (hs _ _ h₄ h₁)
  }
  exact hb ⟨t, rfl⟩
}

lemma rectPath_ne_zero {r h : ℝ} (hr : 0 < r) (hh : 0 < h) (t : unitInterval) :
    rectPath r h t ≠ 0 := by
{
  obtain ⟨T, hT, _⟩ := rectPath_logIncrement hr hh
  exact (hT t ▸ Complex.exp_ne_zero (T t))
}

lemma winding_jump_centred_segments {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (d : ℂ) (r : ℝ) :
    let H_fn : C(ℂ, ℂ) := ⟨fun w => γ w.im - γ 0 - w.re • (Complex.I * d),
      ((hc.comp Complex.continuous_im).sub continuous_const).sub
        (Complex.continuous_re.smul continuous_const)⟩
    (∀ x : ℝ, H_fn ((x : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I) =
      H_fn ((x : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I)) ∧
    ((Path.segment ((r : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I)
        ((r : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)).map H_fn.continuous).toContinuousMap =
      (⟨fun t : unitInterval => γ ((t : ℝ) - 1 / 2),
          hc.comp (continuous_subtype_val.sub continuous_const)⟩ : C(unitInterval, ℂ)) -
        ContinuousMap.const _ (γ 0 + r • (Complex.I * d)) ∧
    ((Path.segment ((-r : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I)
        ((-r : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)).map H_fn.continuous).toContinuousMap =
      (⟨fun t : unitInterval => γ ((t : ℝ) - 1 / 2),
          hc.comp (continuous_subtype_val.sub continuous_const)⟩ : C(unitInterval, ℂ)) -
        ContinuousMap.const _ (γ 0 - r • (Complex.I * d)) := by
{
  dsimp only
  refine ⟨fun x => ?_, ?_, ?_⟩
  · have he : γ (1 / 2) = γ (-(1 / 2)) := by convert hp (-(1 / 2)) using 1; norm_num
    simpa only [ContinuousMap.coe_mk, Complex.add_im, Complex.sub_im, Complex.add_re,
      Complex.sub_re, Complex.mul_im, Complex.mul_re, Complex.ofReal_im, Complex.ofReal_re,
      Complex.I_re, Complex.I_im, zero_mul, mul_zero, mul_one, sub_zero, add_zero, zero_add,
      zero_sub] using congrArg (fun z : ℂ => z - γ 0 - x • (Complex.I * d)) he
  · ext t
    simp only [Path.coe_toContinuousMap, Path.map_coe, Function.comp_apply,
      Path.segment_apply, AffineMap.lineMap_apply_module, ContinuousMap.coe_mk,
      ContinuousMap.sub_apply, ContinuousMap.const_apply]
    have hre : ((1 - (t : ℝ)) • ((r : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) +
        (t : ℝ) • ((r : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)).re = r := by simp [Complex.real_smul]; ring
    have him : ((1 - (t : ℝ)) • ((r : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) +
        (t : ℝ) • ((r : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)).im = (t : ℝ) - 1 / 2 := by simp [Complex.real_smul]; ring
    rw [hre, him]; abel
  · ext t
    simp only [Path.coe_toContinuousMap, Path.map_coe, Function.comp_apply,
      Path.segment_apply, AffineMap.lineMap_apply_module, ContinuousMap.coe_mk,
      ContinuousMap.sub_apply, ContinuousMap.const_apply]
    have hre : ((1 - (t : ℝ)) • ((-r : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) +
        (t : ℝ) • ((-r : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)).re = -r := by simp [Complex.real_smul]; ring
    have him : ((1 - (t : ℝ)) • ((-r : ℂ) - ((1 / 2 : ℝ) : ℂ) * Complex.I) +
        (t : ℝ) • ((-r : ℂ) + ((1 / 2 : ℝ) : ℂ) * Complex.I)).im = (t : ℝ) - 1 / 2 := by simp [Complex.real_smul]; ring
    rw [hre, him, neg_smul]; abel
}

lemma winding_jump_centred {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {d : ℂ} (hd : HasDerivAt γ d 0) (hdn : d ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      loopIndex ⟨fun t : unitInterval => γ ((t : ℝ) - 1 / 2),
          hc.comp (continuous_subtype_val.sub continuous_const)⟩
        (γ 0 + r • (Complex.I * d)) -
      loopIndex ⟨fun t : unitInterval => γ ((t : ℝ) - 1 / 2),
          hc.comp (continuous_subtype_val.sub continuous_const)⟩
        (γ 0 - r • (Complex.I * d)) = 1 := by
{
  let H_fn : C(ℂ, ℂ) := ⟨fun w => γ w.im - γ 0 - w.re • (Complex.I * d),
    ((hc.comp Complex.continuous_im).sub continuous_const).sub
      (Complex.continuous_re.smul continuous_const)⟩
  let A : ℂ →L[ℝ] ℂ := (-Complex.I * d) • ContinuousLinearMap.id ℝ ℂ
  obtain ⟨δ, hδ, hzero⟩ := transverse_unique_zero_strip hc hp hinj hd hdn
  refine ⟨δ, hδ, fun r hr hrd => ?_⟩
  let p := rectPath r (1 / 2)
  have hp0 : ∀ t, p t ≠ 0 := rectPath_ne_zero hr (by norm_num)
  have hmem : ∀ t, p t ∈ rectRegion r (1 / 2) := rectPath_mem hr.le (by norm_num)
  have hz : ∀ z ∈ rectRegion r (1 / 2), H_fn z = 0 ↔ z ∈ ({0} : Finset ℂ) := fun z hz => by
    simpa only [Finset.mem_singleton, H_fn, ContinuousMap.coe_mk] using hzero z (hz.1.trans hrd) hz.2
  have hn : ∀ t, H_fn (p t) ≠ 0 := fun t ht => hp0 t (Finset.mem_singleton.mp ((hz _ (hmem t)).mp ht))
  have hi := windingNumber_finite_regular_zeros (convex_rectRegion r (1 / 2)) {0} H_fn
    (fun _ => A) (fun z hz => by
      simpa [Finset.mem_singleton.mp hz, rectRegion] using
        (show (0 : ℝ) ≤ r ∧ (0 : ℝ) ≤ 1 / 2 from ⟨hr.le, by norm_num⟩)) hz
    (fun z hz => by
      have he := Finset.mem_singleton.mp hz
      subst z
      exact ⟨transverse_hasFDerivAt hd, ne_of_gt (det_transverse_pos hdn)⟩)
    p.toContinuousMap (p.target.trans p.source.symm) hmem hn
  have hindex : planeIndex A = 1 := by simp only [A, planeIndex, ite_eq_left (det_transverse_pos hdn)]
  have hpindex : loopIndex p.toContinuousMap 0 = 1 := by
  {
    change windingNumber (⟨fun t => p t - 0, by fun_prop⟩ : C(unitInterval, ℂ)) = 1
    rw [show (⟨fun t => p t - 0, by fun_prop⟩ : C(unitInterval, ℂ)) = p.toContinuousMap by ext t; simp]
    exact rectPath_winding hr (by norm_num)
  }
  simp only [Finset.sum_singleton, hindex, hpindex, mul_one] at hi
  obtain ⟨hperiod, hright, hleft⟩ := winding_jump_centred_segments hc hp d r
  have hstrip := windingNumber_rect_map H_fn H_fn.continuous r (1 / 2) hperiod (by rintro _ ⟨t, rfl⟩; exact hn t)
  have hcomp : ((rectPath r (1 / 2)).map H_fn.continuous).toContinuousMap = H_fn.comp p.toContinuousMap := rfl
  rw [hcomp, hi, hright, hleft] at hstrip
  exact hstrip.symm
}

/-!
## Part 4: Periodic Regular Level Curves (`LevelCurve.lean`)
-/

def periodicLoop {γ : ℝ → ℂ} (hc : Continuous γ) (s : ℝ) : C(unitInterval, ℂ) :=
  ⟨fun t => γ ((t : ℝ) + s), hc.comp (continuous_subtype_val.add continuous_const)⟩

lemma periodicLoop_closed {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (s : ℝ) :
    periodicLoop hc s 1 = periodicLoop hc s 0 := by
{
  simpa only [periodicLoop, ContinuousMap.coe_mk,
    show ((1 : unitInterval) : ℝ) = 1 from rfl, show ((0 : unitInterval) : ℝ) = 0 from rfl,
    zero_add, add_zero, add_comm] using hp s
}

lemma periodicLoop_range {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (s : ℝ) : range (periodicLoop hc s) = range γ := by
{
  apply Subset.antisymm
  · rintro _ ⟨t, rfl⟩; exact ⟨(t : ℝ) + s, rfl⟩
  · rintro _ ⟨t, rfl⟩
    obtain ⟨u, hu, he⟩ := hp.exists_mem_Ico (by norm_num) t s
    refine ⟨⟨u - s, ⟨by linarith [hu.1], by linarith [hu.2]⟩⟩, ?_⟩
    simpa only [periodicLoop, ContinuousMap.coe_mk, sub_add_cancel] using he.symm
}

lemma loopIndex_periodic_shift {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) {a : ℂ} (ha : a ∉ range γ) (s : ℝ) :
    loopIndex (periodicLoop hc s) a = loopIndex (periodicLoop hc 0) a := by
{
  let H_fn : C(unitInterval × unitInterval, ℂ) :=
    ⟨fun p => γ ((p.2 : ℝ) + (p.1 : ℝ) * s) - a, by fun_prop⟩
  have hi := windingNumber_homotopy H_fn
    (fun p => sub_ne_zero.mpr (fun he => ha ⟨_, he⟩))
    (fun t => by
      change γ (1 + (t : ℝ) * s) - a = γ (0 + (t : ℝ) * s) - a
      simpa only [zero_add, add_zero, add_comm] using congrArg (fun z : ℂ => z - a) (hp ((t : ℝ) * s)))
  simpa only [H_fn, loopIndex, periodicLoop,
    show ((1 : unitInterval) : ℝ) = 1 from rfl, show ((0 : unitInterval) : ℝ) = 0 from rfl,
    ContinuousMap.coe_mk, one_mul, zero_mul] using hi
}

lemma transverse_displacement_not_mem {γ : ℝ → ℂ} (hp : Function.Periodic γ 1)
    {d : ℂ} {δ : ℝ}
    (hz : ∀ w : ℂ, |w.re| ≤ δ → |w.im| ≤ 1 / 2 →
      (γ w.im - γ 0 - w.re • (Complex.I * d) = 0 ↔ w = 0))
    {r : ℝ} (hr : r ≠ 0) (hrd : |r| ≤ δ) :
    γ 0 + r • (Complex.I * d) ∉ range γ := by
{
  rintro ⟨t, ht⟩
  obtain ⟨u, hu, he⟩ := hp.exists_mem_Ico (by norm_num) t (-(1 / 2))
  have hui : |u| ≤ 1 / 2 := abs_le.mpr ⟨hu.1, by linarith [hu.2]⟩
  let w : ℂ := (r : ℂ) + (u : ℂ) * Complex.I
  have hre : w.re = r := by simp [w]
  have him : w.im = u := by simp [w]
  have hw : w = 0 := (hz w (hre ▸ hrd) (him ▸ hui)).mp (by rw [hre, him, ← he, ht]; abel)
  exact hr (by simpa only [hre, Complex.zero_re] using congrArg Complex.re hw)
}

lemma winding_jump {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {d : ℂ} (hd : HasDerivAt γ d 0) (hdn : d ≠ 0) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      γ 0 + r • (Complex.I * d) ∉ range γ ∧ γ 0 - r • (Complex.I * d) ∉ range γ ∧
      loopIndex (periodicLoop hc 0) (γ 0 + r • (Complex.I * d)) -
      loopIndex (periodicLoop hc 0) (γ 0 - r • (Complex.I * d)) = 1 := by
{
  obtain ⟨δ, hδ, hjump⟩ := winding_jump_centred hc hp hinj hd hdn
  obtain ⟨ε, hε, hzero⟩ := transverse_unique_zero_strip hc hp hinj hd hdn
  refine ⟨min δ ε, lt_min hδ hε, fun r hr hre => ?_⟩
  have hn₁ := transverse_displacement_not_mem hp hzero hr.ne'
    (show |r| ≤ ε from (abs_of_pos hr).symm ▸ hre.trans (min_le_right _ _))
  have hn₂ : γ 0 - r • (Complex.I * d) ∉ range γ := by
  {
    simpa only [neg_smul, sub_eq_add_neg] using transverse_displacement_not_mem hp hzero
      (neg_ne_zero.mpr hr.ne') (show |-r| ≤ ε by rw [abs_neg, abs_of_pos hr]; exact hre.trans (min_le_right _ _))
  }
  refine ⟨hn₁, hn₂, ?_⟩
  have hj := hjump r hr (hre.trans (min_le_left _ _))
  change loopIndex (periodicLoop hc (-(1 / 2))) (γ 0 + r • (Complex.I * d)) -
    loopIndex (periodicLoop hc (-(1 / 2))) (γ 0 - r • (Complex.I * d)) = 1 at hj
  rwa [loopIndex_periodic_shift hc hp hn₁, loopIndex_periodic_shift hc hp hn₂] at hj
}

lemma loopIndex_zero_of_re_lt (γ : C(unitInterval, ℂ)) (hloop : γ 1 = γ 0)
    {a : ℂ} (ha : ∀ t, a.re < (γ t).re) : loopIndex γ a = 0 := by
{
  apply windingNumber_eq_of_logIncrement (by simp [hloop])
  have h := HasLogIncrement.of_slit (⟨fun t => γ t - a, by fun_prop⟩ : C(unitInterval, ℂ))
    (fun t => Complex.mem_slitPlane_iff.mpr (Or.inl (by simpa using sub_pos.mpr (ha t))))
  simpa only [ContinuousMap.coe_mk, hloop, sub_self, Int.cast_zero, zero_mul] using h
}

lemma winding_leftmost_normal {γ : ℝ → ℂ} (hc : Continuous γ)
    (hp : Function.Periodic γ 1) (hinj : InjOn γ (Ico (0 : ℝ) 1))
    {d : ℂ} (hd : HasDerivAt γ d 0) (hdi : d.im < 0)
    (hmin : ∀ t, (γ 0).re ≤ (γ t).re) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ r : ℝ, 0 < r → r ≤ δ →
      γ 0 + r • (Complex.I * d) ∉ range γ ∧
      loopIndex (periodicLoop hc 0) (γ 0 + r • (Complex.I * d)) = 1 := by
{
  have hdn : d ≠ 0 := fun he => by simp only [he, Complex.zero_im] at hdi; linarith
  obtain ⟨δ, hδ, hj⟩ := winding_jump hc hp hinj hd hdn
  refine ⟨δ, hδ, fun r hr hrd => ?_⟩
  obtain ⟨hn, _, hjump⟩ := hj r hr hrd
  have hzero : loopIndex (periodicLoop hc 0) (γ 0 - r • (Complex.I * d)) = 0 :=
    loopIndex_zero_of_re_lt _ (periodicLoop_closed hc hp 0) (fun t => by
      change (γ 0 - r • (Complex.I * d)).re < (γ ((t : ℝ) + 0)).re
      simp only [Complex.sub_re, Complex.smul_re, Complex.mul_re, Complex.I_re, zero_mul,
        Complex.I_im, one_mul, zero_sub, smul_eq_mul]
      nlinarith [hmin ((t : ℝ) + 0)])
  rw [hzero, sub_zero] at hjump
  exact ⟨hn, hjump⟩
}

lemma isMIntegralCurve_iff_hasDerivAt {γ : ℝ → ℂ} {v : ℂ → ℂ} :
    IsMIntegralCurve (I := 𝓘(ℝ, ℂ)) γ v ↔ ∀ t, HasDerivAt γ (v (γ t)) t := by
{
  constructor
  · intro h t
    have ht : HasFDerivAt γ ((1 : ℝ →L[ℝ] ℝ).smulRight (v (γ t))) t :=
      hasMFDerivAt_iff_hasFDerivAt.mp (h t)
    simpa only [ContinuousLinearMap.smulRight_apply, one_apply_eq_self, one_smul] using ht.hasDerivAt
  · intro h t
    exact (h t).hasFDerivAt.hasMFDerivAt
}

lemma exists_global_curve {v : ℂ → ℂ} (hv : ContDiff ℝ 1 v)
    (hc : HasCompactSupport v) (x : ℂ) :
    ∃ γ : ℝ → ℂ, γ 0 = x ∧ ∀ t, HasDerivAt γ (v (γ t)) t := by
{
  obtain ⟨K, hK⟩ := ContDiff.lipschitzWith_of_hasCompactSupport hc hv (by simp)
  obtain ⟨B, hB⟩ := hc.exists_bound_of_continuous hv.continuous
  let L : ℝ≥0 := ⟨max B 0, le_max_right _ _⟩
  have hL : ∀ z, ‖v z‖ ≤ (L : ℝ) := fun z => (hB z).trans (le_max_left _ _)
  have hm : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ)).tangent 1
      (fun z => (⟨z, v z⟩ : TangentBundle 𝓘(ℝ, ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  have he : ∀ z : ℂ, ∃ γ : ℝ → ℂ, γ 0 = z ∧
      IsMIntegralCurveOn (I := 𝓘(ℝ, ℂ)) γ v (Ioo (-1) 1) := by
  {
    intro z
    have hi : IsPicardLindelof (fun _ : ℝ => v)
        (⟨0, by norm_num⟩ : Icc (-1 : ℝ) 1) z L 0 L K :=
      ⟨fun _ _ => hK.lipschitzOnWith, fun _ _ => continuousOn_const, fun _ _ w _ => hL w, by simp⟩
    obtain ⟨γ, hγ0, hγ⟩ := hi.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
    exact ⟨γ, hγ0, fun t ht =>
      ((hγ t ⟨ht.1.le, ht.2.le⟩).hasDerivAt (Icc_mem_nhds ht.1 ht.2)).hasFDerivAt.hasMFDerivAt.hasMFDerivWithinAt⟩
  }
  obtain ⟨γ, hγ0, hγ⟩ := exists_isMIntegralCurve_of_isMIntegralCurveOn hm (by norm_num : (0 : ℝ) < 1) he x
  exact ⟨γ, hγ0, isMIntegralCurve_iff_hasDerivAt.mp hγ⟩
}

def transverseCoordinate (p : ℂ →L[ℝ] ℝ) : ℂ →L[ℝ] ℝ :=
  (-p Complex.I) • Complex.reCLM + (p 1) • Complex.imCLM

def levelChartDerivative (p : ℂ →L[ℝ] ℝ) : ℂ →L[ℝ] ℂ :=
  Complex.ofRealCLM.comp p + Complex.I • (Complex.ofRealCLM.comp (transverseCoordinate p))

lemma realFunctional_decomposition (p : ℂ →L[ℝ] ℝ) (w : ℂ) :
    p w = w.re * p 1 + w.im * p Complex.I := by
{
  have hw : w = w.re • (1 : ℂ) + w.im • Complex.I := by simp [Complex.real_smul, Complex.re_add_im]
  conv_lhs => rw [hw, map_add, map_smul, map_smul]
  simp only [smul_eq_mul]
}

lemma levelChartDerivative_det (p : ℂ →L[ℝ] ℝ) :
    LinearMap.det (levelChartDerivative p).toLinearMap = (p 1)^2 + (p Complex.I)^2 := by
{
  rw [det_complex_real_eq]
  simp [levelChartDerivative, transverseCoordinate, Complex.mul_re, Complex.mul_im]
  ring
}

lemma levelChartDerivative_det_pos {p : ℂ →L[ℝ] ℝ} (hp : p ≠ 0) :
    0 < LinearMap.det (levelChartDerivative p).toLinearMap := by
{
  rw [levelChartDerivative_det]
  have hn : p 1 ≠ 0 ∨ p Complex.I ≠ 0 := by
  {
    by_contra h
    push Not at h
    apply hp
    ext w
    rw [realFunctional_decomposition, h.1, h.2]
    simp
  }
  rcases hn with hn | hn
  · nlinarith [sq_pos_of_ne_zero hn, sq_nonneg (p Complex.I)]
  · nlinarith [sq_pos_of_ne_zero hn, sq_nonneg (p 1)]
}

lemma exists_regular_level_chart {f : ℂ → ℝ} {z : ℂ}
    (hf : ContDiffAt ℝ 1 f z) (hp : fderiv ℝ f z ≠ 0) :
    ∃ e : OpenPartialHomeomorph ℂ ℂ, z ∈ e.source ∧
      (∀ w, (e w).re = f w) ∧
      (∀ w, (e w).im = transverseCoordinate (fderiv ℝ f z) w) := by
{
  let p := fderiv ℝ f z
  let Φ : ℂ → ℂ := fun w => (f w : ℂ) + Complex.I * (transverseCoordinate p w : ℂ)
  have hc : ContDiffAt ℝ 1 Φ z :=
    (Complex.ofRealCLM.contDiff.contDiffAt.comp z hf).add
      (contDiffAt_const.mul ((Complex.ofRealCLM.comp (transverseCoordinate p)).contDiff.contDiffAt))
  have hd : HasFDerivAt Φ (levelChartDerivative p) z :=
    (Complex.ofRealCLM.hasFDerivAt.comp z (hf.differentiableAt (by simp)).hasFDerivAt).add
      (((Complex.ofRealCLM.comp (transverseCoordinate p)).hasFDerivAt).const_mul Complex.I)
  let A : ℂ ≃L[ℝ] ℂ := (LinearMap.equivOfIsUnitDet
    (isUnit_iff_ne_zero.mpr (ne_of_gt (levelChartDerivative_det_pos hp)))).toContinuousLinearEquiv
  have hA : (A : ℂ →L[ℝ] ℂ) = levelChartDerivative p :=
    ContinuousLinearMap.ext (fun w => LinearMap.equivOfIsUnitDet_apply _ w)
  rw [← hA] at hd
  refine ⟨hc.toOpenPartialHomeomorph Φ hd (by simp),
    hc.mem_toOpenPartialHomeomorph_source hd (by simp), fun w => ?_, fun w => ?_⟩
  · change (Φ w).re = f w; simp [Φ]
  · change (Φ w).im = transverseCoordinate p w; simp [Φ]
}

lemma curve_local_level_cover {f : ℂ → ℝ} {γ : ℝ → ℂ} {t : ℝ} {v : ℂ}
    (hf : ContDiffAt ℝ 1 f (γ t)) (hp : fderiv ℝ f (γ t) ≠ 0)
    (hγ : ContDiffAt ℝ 1 γ t) (hd : HasDerivAt γ v t) (hv : v ≠ 0)
    (hc : ∀ s, f (γ s) = f (γ t)) {U : Set ℝ} (hU : U ∈ 𝓝 t) :
    ∀ᶠ w in 𝓝 (γ t), f w = f (γ t) → w ∈ γ '' U := by
{
  let p := fderiv ℝ f (γ t)
  let q := transverseCoordinate p
  have hfd := (hf.differentiableAt (by simp)).hasFDerivAt
  have hpv : p v = 0 := by
  {
    have hh := hfd.comp_hasDerivAt t hd
    rw [show (f ∘ γ) = fun _ => f (γ t) from funext hc] at hh
    exact hh.unique (hasDerivAt_const t _)
  }
  have hqv : q v ≠ 0 := by
  {
    intro hq
    let A := LinearMap.equivOfIsUnitDet
      (isUnit_iff_ne_zero.mpr (ne_of_gt (levelChartDerivative_det_pos hp)))
    have hz : A v = A 0 := by
    {
      rw [show A v = levelChartDerivative p v from LinearMap.equivOfIsUnitDet_apply _ v,
        show A 0 = levelChartDerivative p 0 from LinearMap.equivOfIsUnitDet_apply _ 0]
      simp [levelChartDerivative, hpv, show transverseCoordinate p v = 0 from hq]
    }
    exact hv (A.injective hz)
  }
  let ψ : ℝ → ℝ := fun s => q (γ s)
  have hψ : HasStrictDerivAt ψ (q v) t :=
    (q.contDiff.contDiffAt.comp t hγ).hasStrictDerivAt' (q.hasFDerivAt.comp_hasDerivAt t hd) (by simp)
  let σ := hψ.localInverse ψ (q v) t hqv
  have hσ : σ (ψ t) = t := hψ.eventually_left_inverse hqv |>.self_of_nhds
  have hσc : Tendsto σ (𝓝 (ψ t)) (𝓝 t) := by
  {
    have ht : Tendsto σ (𝓝 (ψ t)) (𝓝 (σ (ψ t))) :=
      (hψ.to_localInverse hqv).hasDerivAt.continuousAt.tendsto
    rwa [hσ] at ht
  }
  obtain ⟨e, het, her, hei⟩ := exists_regular_level_chart hf hp
  have hw : ∀ᶠ w in 𝓝 (γ t), w ∈ e.source := e.open_source.mem_nhds het
  have hqc : Tendsto q (𝓝 (γ t)) (𝓝 (ψ t)) := q.continuous.continuousAt.tendsto
  filter_upwards [hw, hqc.eventually (hψ.eventually_right_inverse hqv),
    (hσc.comp hqc).eventually hU,
    (hγ.continuousAt.tendsto.comp (hσc.comp hqc)).eventually hw] with w hw hi hu hs hfwe
  refine ⟨σ (q w), hu, e.injOn hs hw ?_⟩
  dsimp only [Function.comp_apply]
  exact Complex.ext (by rw [her, her, hc, hfwe]) (by rw [hei, hei]; exact hi)
}

lemma integral_curve_contDiff_one {v : ℂ → ℂ} {γ : ℝ → ℂ}
    (hv : Continuous v) (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) :
    ContDiff ℝ 1 γ := by
{
  apply contDiff_one_iff_deriv.mpr
  have hc : Continuous γ := continuous_iff_continuousAt.mpr fun t => (hγ t).continuousAt
  refine ⟨fun t => (hγ t).differentiableAt, ?_⟩
  rw [show deriv γ = v ∘ γ from funext fun t => (hγ t).deriv]
  exact hv.comp hc
}

lemma integral_curve_first_integral {f : ℂ → ℝ} {v : ℂ → ℂ} {γ : ℝ → ℂ}
    (hf : Differentiable ℝ f) (horth : ∀ z, fderiv ℝ f z (v z) = 0)
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (s t : ℝ) : f (γ s) = f (γ t) := by
{
  have hd (t : ℝ) : HasDerivAt (fun t => f (γ t)) 0 t := by
  {
    convert (hf (γ t)).hasFDerivAt.comp_hasDerivAt t (hγ t) using 1 <;>
      first | rfl | simp only [horth]
  }
  exact is_const_of_deriv_eq_zero (fun t => (hd t).differentiableAt)
    (fun t => (hd t).deriv) s t
}

lemma integral_curves_shift_eq {v : ℂ → ℂ} {γ κ : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v)
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hκ : ∀ t, HasDerivAt κ (v (κ t)) t)
    {a b : ℝ} (he : γ a = κ b) (s : ℝ) : γ (s + a) = κ (s + b) := by
{
  have hm : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ)).tangent 1
      (fun z => (⟨z, v z⟩ : TangentBundle 𝓘(ℝ, ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  have hh := isMIntegralCurve_Ioo_eq_of_contMDiff_boundaryless (t₀ := 0) hm
    ((isMIntegralCurve_iff_hasDerivAt.mpr hγ).comp_add a)
    ((isMIntegralCurve_iff_hasDerivAt.mpr hκ).comp_add b) (by simpa using he)
  exact congrFun hh s
}

lemma curve_isOpenMap_level {f : ℂ → ℝ} {γ : ℝ → ℂ} {c : ℝ}
    (hf : ContDiff ℝ 1 f) (hp : ∀ z, f z = c → fderiv ℝ f z ≠ 0)
    (hγ : ContDiff ℝ 1 γ) (hn : ∀ t, deriv γ t ≠ 0)
    (hc : ∀ t, f (γ t) = c) :
    IsOpenMap (fun t => (⟨γ t, hc t⟩ : {z : ℂ | f z = c})) := by
{
  intro U hU
  apply isOpen_iff_mem_nhds.mpr
  rintro _ ⟨t, ht, rfl⟩
  have hh := curve_local_level_cover hf.contDiffAt (hp _ (hc t)) hγ.contDiffAt
    (hγ.differentiable (by simp) t).hasDerivAt (hn t)
    (fun s => (hc s).trans (hc t).symm) (hU.mem_nhds ht)
  have hm : Tendsto (Subtype.val : {z : ℂ | f z = c} → ℂ)
      (𝓝 ⟨γ t, hc t⟩) (𝓝 (γ t)) := continuous_subtype_val.continuousAt.tendsto
  filter_upwards [hm.eventually hh] with w hw
  obtain ⟨s, hs, heq⟩ := hw (w.property.trans (hc t).symm)
  exact ⟨s, hs, Subtype.ext heq⟩
}

lemma level_curve_range_isClosed {f : ℂ → ℝ} {v : ℂ → ℂ} {c : ℝ}
    (hf : ContDiff ℝ 1 f) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v)
    (horth : ∀ z, fderiv ℝ f z (v z) = 0)
    (hp : ∀ z, f z = c → fderiv ℝ f z ≠ 0)
    (hn : ∀ z, f z = c → v z ≠ 0)
    {γ : ℝ → ℂ} (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (hc : ∀ t, f (γ t) = c) :
    IsClosed (range (fun t => (⟨γ t, hc t⟩ : {z : ℂ | f z = c}))) := by
{
  let K := {z : ℂ | f z = c}
  apply isOpen_compl_iff.mp
  apply isOpen_iff_mem_nhds.mpr
  intro w hw
  obtain ⟨κ, hκ0, hκ⟩ := exists_global_curve hv hvc w.val
  have hκc (s : ℝ) : f (κ s) = c := by
  {
    rw [integral_curve_first_integral (hf.differentiable (by simp)) horth hκ s 0, hκ0]
    exact w.property
  }
  let Δ : ℝ → K := fun s => ⟨κ s, hκc s⟩
  have hΔo : IsOpenMap Δ := curve_isOpenMap_level hf hp
    (integral_curve_contDiff_one hv.continuous hκ)
    (fun s => by rw [(hκ s).deriv]; exact hn _ (hκc s)) hκc
  have hwΔ : w ∈ range Δ := ⟨0, Subtype.ext hκ0⟩
  apply mem_of_superset (hΔo.isOpen_range.mem_nhds hwΔ)
  rintro y ⟨s, rfl⟩ ⟨t, ht⟩
  apply hw
  have he : γ t = κ s := congrArg Subtype.val ht
  refine ⟨-s + t, Subtype.ext ?_⟩
  have hh := integral_curves_shift_eq hv hγ hκ he (-s)
  simpa only [neg_add_cancel, hκ0] using hh
}

lemma compact_regular_level_periodic {f : ℂ → ℝ} {v : ℂ → ℂ} {c : ℝ}
    (hf : ContDiff ℝ 1 f) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v)
    (horth : ∀ z, fderiv ℝ f z (v z) = 0)
    (hp : ∀ z, f z = c → fderiv ℝ f z ≠ 0)
    (hn : ∀ z, f z = c → v z ≠ 0)
    (hK : IsCompact {z : ℂ | f z = c}) {γ : ℝ → ℂ}
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t) (hγ0 : f (γ 0) = c) :
    ∃ T > 0, Periodic γ T := by
{
  let K := {z : ℂ | f z = c}
  have hc (t : ℝ) : f (γ t) = c :=
    (integral_curve_first_integral (hf.differentiable (by simp)) horth hγ t 0).trans hγ0
  let Γ : ℝ → K := fun t => ⟨γ t, hc t⟩
  have hγc := integral_curve_contDiff_one hv.continuous hγ
  have hΓo : IsOpenMap Γ := curve_isOpenMap_level hf hp hγc
    (fun t => by rw [(hγ t).deriv]; exact hn _ (hc t)) hc
  have hΓc : Continuous Γ := hγc.continuous.subtype_mk _
  have hclosed := level_curve_range_isClosed hf hv hvc horth hp hn hγ hc
  have hcompact : IsCompact (range Γ) := by
  {
    have : CompactSpace K := isCompact_iff_compactSpace.mp hK
    exact hclosed.isCompact
  }
  have hnotinj : ¬ Injective γ := by
  {
    intro hi
    have hΓi : Injective Γ := fun a b h => hi (congrArg Subtype.val h)
    have he := Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap hΓc hΓi hΓo
    apply noncompact_univ ℝ
    apply he.isEmbedding.isCompact_iff.mpr
    simpa only [image_univ] using hcompact
  }
  have hm : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ)).tangent 1
      (fun z => (⟨z, v z⟩ : TangentBundle 𝓘(ℝ, ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  exact (xor_iff_iff_not.mp
    ((isMIntegralCurve_iff_hasDerivAt.mpr hγ).periodic_xor_injective hm)).mpr hnotinj
}

lemma curve_locally_injective {γ : ℝ → ℂ} {t : ℝ}
    (hγ : ContDiffAt ℝ 1 γ t) (hn : deriv γ t ≠ 0) :
    ∃ ε > 0, InjOn γ (Metric.ball t ε) := by
{
  obtain ⟨p, hp⟩ : ∃ p : ℂ →L[ℝ] ℝ, p (deriv γ t) ≠ 0 := by
  {
    by_cases hr : (deriv γ t).re = 0
    · exact ⟨Complex.imCLM, fun hi => hn (Complex.ext hr hi)⟩
    · exact ⟨Complex.reCLM, hr⟩
  }
  have hd : HasStrictDerivAt (fun s => p (γ s)) (p (deriv γ t)) t :=
    (p.contDiff.contDiffAt.comp t hγ).hasStrictDerivAt'
      (p.hasFDerivAt.comp_hasDerivAt t (hγ.differentiableAt (by simp)).hasDerivAt) (by simp)
  obtain ⟨ε, hε, hsub⟩ := Metric.mem_nhds_iff.mp (hd.eventually_left_inverse hp)
  refine ⟨ε, hε, fun a ha b hb he => ?_⟩
  have h₁ : hd.localInverse (fun s => p (γ s)) (p (deriv γ t)) t hp (p (γ a)) = a := hsub ha
  have h₂ : hd.localInverse (fun s => p (γ s)) (p (deriv γ t)) t hp (p (γ b)) = b := hsub hb
  rw [he] at h₁
  exact h₁.symm.trans h₂
}

lemma integral_curve_simple_period {v : ℂ → ℂ} {γ : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v) (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hn : v (γ 0) ≠ 0) (hper : ∃ T > 0, Periodic γ T) :
    ∃ T > 0, Periodic γ T ∧ InjOn γ (Ico 0 T) := by
{
  have hγc := integral_curve_contDiff_one hv.continuous hγ
  obtain ⟨ε, hε, hεinj⟩ := curve_locally_injective (t := 0) hγc.contDiffAt (by rw [(hγ 0).deriv]; exact hn)
  have hlow (t : ℝ) (ht : 0 < t) (he : γ t = γ 0) : ε ≤ t := by
  {
    by_contra hh
    have hmem : t ∈ Metric.ball (0 : ℝ) ε := by
      simpa [Metric.mem_ball, Real.dist_eq, abs_of_pos ht] using lt_of_not_ge hh
    linarith [hεinj hmem (Metric.mem_ball_self hε) he]
  }
  obtain ⟨T, hT, hpT⟩ := hper
  have hTr : γ T = γ 0 := by simpa using hpT 0
  let S := Icc ε T ∩ {t | γ t = γ 0}
  have hS : IsCompact S := isCompact_Icc.inter_right (isClosed_eq hγc.continuous continuous_const)
  obtain ⟨P, hP, hmin⟩ := hS.exists_isMinOn ⟨T, ⟨⟨hlow T hT hTr, le_rfl⟩, hTr⟩⟩ continuousOn_id
  have hleast (t : ℝ) (ht : 0 < t) (he : γ t = γ 0) : P ≤ t := by
  {
    by_cases hle : t ≤ T
    · exact hmin ⟨⟨hlow t ht he, hle⟩, he⟩
    · exact hP.1.2.trans (le_of_not_ge hle)
  }
  have hm : ContMDiff 𝓘(ℝ, ℂ) (𝓘(ℝ, ℂ)).tangent 1
      (fun z => (⟨z, v z⟩ : TangentBundle 𝓘(ℝ, ℂ) ℂ)) :=
    contMDiff_vectorSpace_iff_contDiff.mpr hv
  have hi := isMIntegralCurve_iff_hasDerivAt.mpr hγ
  refine ⟨P, hε.trans_le hP.1.1, by simpa using hi.periodic_of_eq hm hP.2, fun a ha b hb he => ?_⟩
  rcases lt_trichotomy a b with hab | hab | hab
  · linarith [ha.1, hb.2, hleast (b - a) (sub_pos.mpr hab) (by simpa using (hi.periodic_of_eq hm he.symm) 0)]
  · exact hab
  · linarith [hb.1, ha.2, hleast (a - b) (sub_pos.mpr hab) (by simpa using (hi.periodic_of_eq hm he) 0)]
}

lemma integral_curves_range_eq {v : ℂ → ℂ} {γ κ : ℝ → ℂ}
    (hv : ContDiff ℝ 1 v)
    (hγ : ∀ t, HasDerivAt γ (v (γ t)) t)
    (hκ : ∀ t, HasDerivAt κ (v (κ t)) t)
    {a b : ℝ} (he : γ a = κ b) : range γ = range κ := by
{
  apply Subset.antisymm
  · rintro _ ⟨s, rfl⟩
    exact ⟨s - a + b, by simpa only [sub_add_cancel] using (integral_curves_shift_eq hv hγ hκ he (s - a)).symm⟩
  · rintro _ ⟨s, rfl⟩
    exact ⟨s - b + a, by simpa only [sub_add_cancel] using (integral_curves_shift_eq hv hκ hγ he.symm (s - b)).symm⟩
}

lemma compact_regular_level_finite_curves {f : ℂ → ℝ} {v : ℂ → ℂ} {c : ℝ}
    (hf : ContDiff ℝ 1 f) (hv : ContDiff ℝ 1 v) (hvc : HasCompactSupport v)
    (horth : ∀ z, fderiv ℝ f z (v z) = 0)
    (hp : ∀ z, f z = c → fderiv ℝ f z ≠ 0)
    (hn : ∀ z, f z = c → v z ≠ 0)
    (hK : IsCompact {z : ℂ | f z = c}) :
    ∃ C : Finset (Set ℂ), (⋃ S ∈ C, S) = {z : ℂ | f z = c} ∧
      (∀ S ∈ C, ∀ T ∈ C, S ≠ T → Disjoint S T) ∧
      ∀ S ∈ C, ∃ γ : ℝ → ℂ, ∃ P > 0,
        range γ = S ∧ (∀ t, HasDerivAt γ (v (γ t)) t) ∧
        Periodic γ P ∧ InjOn γ (Ico 0 P) := by
{
  let K := {z : ℂ | f z = c}
  choose γ hγ0 hγ using fun z : K => exists_global_curve hv hvc z.val
  have hc (z : K) (t : ℝ) : f (γ z t) = c := by
  {
    rw [integral_curve_first_integral (hf.differentiable (by simp)) horth (hγ z) t 0, hγ0 z]
    exact z.property
  }
  let Γ (z : K) : ℝ → K := fun t => ⟨γ z t, hc z t⟩
  have hΓo (z : K) : IsOpenMap (Γ z) := curve_isOpenMap_level hf hp
    (integral_curve_contDiff_one hv.continuous (hγ z))
    (fun t => by rw [(hγ z t).deriv]; exact hn _ (hc z t)) (hc z)
  have : CompactSpace K := isCompact_iff_compactSpace.mp hK
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover (fun z : K => range (Γ z))
    (fun z => (hΓo z).isOpen_range) (fun z _ => mem_iUnion.mpr ⟨z, 0, Subtype.ext (hγ0 z)⟩)
  let C := s.image (fun z => range (γ z))
  refine ⟨C, ?_, ?_, ?_⟩
  · ext w
    refine ⟨fun hw => ?_, fun hw => ?_⟩
    · obtain ⟨S, hS, hw⟩ := mem_iUnion₂.mp hw
      obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hS
      obtain ⟨t, rfl⟩ := hw
      exact hc z t
    · obtain ⟨z, hz, t, ht⟩ := mem_iUnion₂.mp (hs (mem_univ (⟨w, hw⟩ : K)))
      exact mem_iUnion₂.mpr ⟨range (γ z), Finset.mem_image.mpr ⟨z, hz, rfl⟩, t, congrArg Subtype.val ht⟩
  · intro S hS T hT hne
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨w, _, rfl⟩ := Finset.mem_image.mp hT
    exact disjoint_left.mpr (fun a ⟨s, hs⟩ ⟨t, ht⟩ =>
      hne (integral_curves_range_eq hv (hγ z) (hγ w) (hs.trans ht.symm)))
  · intro S hS
    obtain ⟨z, _, rfl⟩ := Finset.mem_image.mp hS
    obtain ⟨P, hP, hper, hinj⟩ := integral_curve_simple_period hv (hγ z) (hn _ (hc z 0))
      (compact_regular_level_periodic hf hv hvc horth hp hn hK (hγ z) (hc z 0))
    exact ⟨γ z, P, hP, rfl, hγ z, hper, hinj⟩
}

end Brennan.Sections4and5
