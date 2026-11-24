/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Built upon the Weierstrass `_eps` complex analysis and Möbius transformation foundations in `Sarason/`.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine
import Sarason.Definitions
import Sarason.Chapter1
import Sarason.Chapter2
import Sarason.Chapter3

/-!
# Conformal Disk Geometry: Clines, Symmetry, Cayley/Herglotz/Blaschke Maps, and Polar Starlike Slit Maps

Companion module extending the Möbius transformation foundations of `Sarason/Chapter3.lean` to
conformal geometry on the Riemann sphere `OnePoint ℂ` and the open unit disk `𝔻`:
1. **§1 Clines & Möbius Preservation**: Algebraic cline loci `clineLocus`, `IsCline`, preservation
   under elementary and general linear-fractional transformations (`III_9`), and the cross-ratio
   reality criterion (`cross_ratio_real_isCline`).
2. **§2 Symmetry Across Clines**: Extended conjugation `conjExt`, circle reflection `circleReflect`
   and `circleReflectExt`, cross-ratio symmetry `SymmetricWrtTriple`, and the symmetry principle
   (`III_10_symmetry_principle`).
3. **§3 Cayley Transform, Herglotz Kernel, and Disk Automorphisms**: `cayleyMap`, `cayleyInvMap`,
   `herglotzKernel` (`III_11_herglotz_properties`), `blaschkeFactor`, and `diskAut` (`III_12_blaschke_properties`).
4. **§4 Polar Coordinates, Starlike Holomorphic Maps (`_eps`), and Herglotz–Pommerenke Slit Maps**:
   `polarPoint`, `IsStarlikeDomain_theta`, `argPolarDeriv_theta`, `IsStarlikeOnDisk_theta_eps`,
   `IsStarlikeLogDeriv_eps`, `pommerenkeLogDeriv`, and the boundary slit-angle jump formulas
   (`pommerenkeSlitAngle_succ_sub_eq_sigma_mul_pi`).
-/

open Complex OnePoint MatrixGroups Matrix Sarason Sarason.Ch1 Sarason.Ch2 Sarason.Ch3

namespace ConformalDiskGeometry

/--
  §1 General algebraic locus of a circle or line (cline) in `OnePoint ℂ`:
  Given real parameters `α, γ ∈ ℝ` and a complex parameter `β ∈ ℂ` (satisfying `‖β‖ ^ 2 > α * γ`),
  - a finite point `(z : ℂ)` lies on `clineLocus α β γ` iff `α * ‖z‖ ^ 2 + 2 * (star β * z).re + γ = 0`;
  - the point `∞` lies on `clineLocus α β γ` iff `α = 0` (the Euclidean line case).
-/
def clineLocus (α : ℝ) (β : ℂ) (γ : ℝ) : Set (OnePoint ℂ) :=
  {w : OnePoint ℂ | match w with
    | ∞ => α = 0
    | (z : ℂ) => α * ‖z‖ ^ 2 + 2 * (star β * z).re + γ = 0}

/--
  §1 Predicate `IsCline S` stating that `S ⊆ OnePoint ℂ` is a non-degenerate cline
  (a circle on the Riemann sphere, corresponding in `ℂ` to either a Euclidean circle when `α ≠ 0`
  or a Euclidean line together with `∞` when `α = 0`).
-/
def IsCline (S : Set (OnePoint ℂ)) : Prop :=
  ∃ (α : ℝ) (β : ℂ) (γ : ℝ), α * γ < ‖β‖ ^ 2 ∧ S = clineLocus α β γ

/--
  §1 Every Euclidean circle `{z ∈ ℂ : ‖z - z₀‖ = r}` (`r > 0`) is a cline (`α = 1`, `β = -z₀`,
  `γ = ‖z₀‖ ^ 2 - r ^ 2`, with `‖β‖ ^ 2 - α * γ = r ^ 2 > 0`).
-/
lemma clineLocus_circle (z₀ : ℂ) (r : ℝ) (z : ℂ) :
    ((z : OnePoint ℂ) ∈ clineLocus 1 (-z₀) (‖z₀‖ ^ 2 - r ^ 2)) ↔ ‖z - z₀‖ ^ 2 = r ^ 2 := by
{
  simp only [clineLocus, Set.mem_setOf_eq]
  have h_norm : ‖z - z₀‖ ^ 2 = ‖z‖ ^ 2 + 2 * (star (-z₀) * z).re + ‖z₀‖ ^ 2 := by
  {
    simp only [Complex.sq_norm, Complex.normSq_apply, star_neg, Complex.mul_re,
      Complex.sub_re, Complex.sub_im, Complex.neg_re, Complex.neg_im, star_re, star_im]
    ring
  }
  constructor <;> intro h <;> linarith
}

/--
  §1 The extended real axis `extendedRealAxis` is a cline (`α = 0`, `β = i / 2`, `γ = 0`).
-/
lemma isCline_extendedRealAxis : IsCline extendedRealAxis := by
{
  refine ⟨0, Complex.I / 2, 0, ?_, ?_⟩
  · have h_norm : ‖Complex.I / (2 : ℂ)‖ = 1 / 2 := by simp
    rw [h_norm]
    norm_num
  · ext w
    cases w with
    | infty =>
      simp [extendedRealAxis, clineLocus]
    | coe z =>
      simp only [coe_mem_extendedRealAxis_iff, clineLocus, Set.mem_setOf_eq, zero_mul,
        zero_add, add_zero]
      have h_re : 2 * (star (Complex.I / 2) * z).re = z.im := by
      {
        simp only [Complex.mul_re, star_re, star_im, Complex.div_ofNat_re, Complex.div_ofNat_im,
          Complex.I_re, Complex.I_im]
        ring
      }
      rw [h_re]
}

/--
  §1 Key algebraic identity for inversion `w = 1 / z` on a cline locus:
  For `z ≠ 0`, `α * ‖1 / z‖ ^ 2 + 2 * (star β * (1 / z)).re + γ =
  (γ * ‖z‖ ^ 2 + 2 * (star (star β) * z).re + α) / ‖z‖ ^ 2`.
-/
lemma cline_inversion_identity (α γ : ℝ) (β z : ℂ) (hz : z ≠ 0) :
    α * ‖1 / z‖ ^ 2 + 2 * (star β * (1 / z)).re + γ =
      (γ * ‖z‖ ^ 2 + 2 * (star (star β) * z).re + α) / ‖z‖ ^ 2 := by
{
  have h_nsq : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have h_inv_re : (star β * (1 / z)).re = (star (star β) * z).re / ‖z‖ ^ 2 := by
  {
    rw [star_star, one_div]
    simp only [Complex.mul_re, Complex.inv_re, Complex.inv_im, ← Complex.sq_norm,
      star_re, star_im]
    ring
  }
  rw [norm_div, norm_one, div_pow, one_pow, h_inv_re]
  field_simp [h_nsq]
  ring
}

/--
  §1 Preimage of `clineLocus α β γ` under inversion `invLFT` (`z ↦ 1 / z`) is
  `clineLocus γ (star β) α`: inversion swaps `α ↔ γ` and conjugates `β`.
-/
lemma preimage_invLFT_clineLocus (α : ℝ) (β : ℂ) (γ : ℝ) :
    invLFT ⁻¹' (clineLocus α β γ) = clineLocus γ (star β) α := by
{
  ext w
  cases w with
  | infty =>
    simp [clineLocus, invLFT_infty]
  | coe z =>
    by_cases hz : z = 0
    · subst hz
      simp [clineLocus, invLFT_zero]
    · have h_nsq_pos : 0 < ‖z‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr hz)
      simp only [Set.mem_preimage, invLFT_coe_of_ne_zero hz, clineLocus, Set.mem_setOf_eq]
      rw [cline_inversion_identity α γ β z hz, div_eq_zero_iff]
      exact ⟨fun h => h.resolve_right h_nsq_pos.ne', fun h => Or.inl h⟩
}

/--
  §1 Preimage of a cline under `invLFT` is a cline.
-/
lemma IsCline.preimage_invLFT {S : Set (OnePoint ℂ)} (hS : IsCline S) :
    IsCline (invLFT ⁻¹' S) := by
{
  rcases hS with ⟨α, β, γ, h_disc, rfl⟩
  refine ⟨γ, star β, α, ?_, preimage_invLFT_clineLocus α β γ⟩
  rw [norm_star, mul_comm γ α]
  exact h_disc
}

/--
  §1 Preimage of `clineLocus α β γ` under complex scaling `scaleLFT a` (`a ≠ 0`) is
  `clineLocus (α * ‖a‖ ^ 2) (star a * β) γ`.
-/
lemma preimage_scaleLFT_clineLocus (α : ℝ) (β : ℂ) (γ : ℝ) {a : ℂ} (ha : a ≠ 0) :
    scaleLFT a ⁻¹' (clineLocus α β γ) = clineLocus (α * ‖a‖ ^ 2) (star a * β) γ := by
{
  ext w
  cases w with
  | infty =>
    simp [clineLocus, scaleLFT_infty, ha]
  | coe z =>
    simp only [Set.mem_preimage, scaleLFT_coe, clineLocus, Set.mem_setOf_eq]
    have h_alg : α * ‖a * z‖ ^ 2 + 2 * (star β * (a * z)).re + γ =
        (α * ‖a‖ ^ 2) * ‖z‖ ^ 2 + 2 * (star (star a * β) * z).re + γ := by
    {
      rw [norm_mul, mul_pow, star_mul, star_star]
      ring_nf
    }
    rw [h_alg]
}

/--
  §1 Preimage of a cline under `scaleLFT a` (`a ≠ 0`) is a cline.
-/
lemma IsCline.preimage_scaleLFT {S : Set (OnePoint ℂ)} (hS : IsCline S) {a : ℂ} (ha : a ≠ 0) :
    IsCline (scaleLFT a ⁻¹' S) := by
{
  rcases hS with ⟨α, β, γ, h_disc, rfl⟩
  have ha_sq : 0 < ‖a‖ ^ 2 := sq_pos_of_pos (norm_pos_iff.mpr ha)
  refine ⟨α * ‖a‖ ^ 2, star a * β, γ, ?_, preimage_scaleLFT_clineLocus α β γ ha⟩
  rw [norm_mul, norm_star, mul_pow]
  nlinarith
}

/--
  §1 Algebraic expansion for the translated cline equation at `z + b`:
  `α * ‖z + b‖ ^ 2 + 2 * (star β * (z + b)).re + γ` equals
  `α * ‖z‖ ^ 2 + 2 * (star (β + α * b) * z).re + (α * ‖b‖ ^ 2 + 2 * (star β * b).re + γ)`.
-/
lemma cline_translation_identity (α γ : ℝ) (β b z : ℂ) :
    α * ‖z + b‖ ^ 2 + 2 * (star β * (z + b)).re + γ =
      α * ‖z‖ ^ 2 + 2 * (star (β + (α : ℂ) * b) * z).re +
        (α * ‖b‖ ^ 2 + 2 * (star β * b).re + γ) := by
{
  simp only [Complex.sq_norm, Complex.normSq_apply, star_add, star_mul,
    Complex.add_re, Complex.add_im, Complex.mul_re, Complex.mul_im,
    star_re, star_im, Complex.ofReal_re, Complex.ofReal_im]
  ring
}

/--
  §1 Discriminant invariance under translation `z ↦ z + b`:
  `‖β + α * b‖ ^ 2 - α * (α * ‖b‖ ^ 2 + 2 * (star β * b).re + γ) = ‖β‖ ^ 2 - α * γ`.
-/
lemma cline_translation_discriminant (α γ : ℝ) (β b : ℂ) :
    ‖β + (α : ℂ) * b‖ ^ 2 - α * (α * ‖b‖ ^ 2 + 2 * (star β * b).re + γ) =
      ‖β‖ ^ 2 - α * γ := by
{
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, star_re, star_im,
    Complex.ofReal_re, Complex.ofReal_im]
  ring
}

/--
  §1 Preimage of a cline under `transLFT b` (`z ↦ z + b`) is a cline.
-/
lemma IsCline.preimage_transLFT {S : Set (OnePoint ℂ)} (hS : IsCline S) (b : ℂ) :
    IsCline (transLFT b ⁻¹' S) := by
{
  rcases hS with ⟨α, β, γ, h_disc, rfl⟩
  refine ⟨α, β + (α : ℂ) * b, α * ‖b‖ ^ 2 + 2 * (star β * b).re + γ, ?_, ?_⟩
  · have h_id := cline_translation_discriminant α γ β b
    linarith
  · ext w
    cases w with
    | infty =>
      simp [clineLocus, transLFT_infty]
    | coe z =>
      simp only [Set.mem_preimage, transLFT_coe, clineLocus, Set.mem_setOf_eq]
      rw [cline_translation_identity α γ β b z]
}

/--
  §1 Every map generated by the four elementary transformations (`GeneratedByFourElementary φ`)
  preserves clines under preimage (`IsCline S → IsCline (φ ⁻¹' S)`).
-/
lemma GeneratedByFourElementary.preimage_isCline {φ : OnePoint ℂ → OnePoint ℂ}
    (hφ : GeneratedByFourElementary φ) {S : Set (OnePoint ℂ)} (hS : IsCline S) :
    IsCline (φ ⁻¹' S) := by
{
  induction hφ generalizing S with
  | dilation r hr =>
    exact hS.preimage_scaleLFT (Complex.ofReal_ne_zero.mpr hr.ne')
  | rotation u hu =>
    have hu_ne : u ≠ 0 := by
    {
      intro h0
      rw [h0, norm_zero] at hu
      exact zero_ne_one hu
    }
    exact hS.preimage_scaleLFT hu_ne
  | translation β =>
    exact hS.preimage_transLFT β
  | inversion =>
    exact hS.preimage_invLFT
  | comp _ _ ihφ ihψ =>
    rw [Set.preimage_comp]
    exact ihψ (ihφ hS)
}

/--
  §1 **Theorem III_9 (Möbius Transformations Preserve Circles and Lines / Clines)**:
  For every invertible 2×2 matrix `g ∈ GL (Fin 2) ℂ` and every cline `S ⊆ OnePoint ℂ`,
  both the preimage `(g • ·) ⁻¹' S` and the forward image `(g • ·) '' S` are clines in `OnePoint ℂ`.
-/
theorem III_9 (g : GL (Fin 2) ℂ) {S : Set (OnePoint ℂ)} (hS : IsCline S) :
    IsCline ((g • ·) ⁻¹' S) ∧ IsCline ((g • ·) '' S) := by
{
  refine ⟨GeneratedByFourElementary.preimage_isCline (III_6 g) hS, ?_⟩
  -- Since g • · is a group action, the forward image under g • · is the preimage under g⁻¹ • ·
  have h_img : (g • ·) '' S = (g⁻¹ • ·) ⁻¹' S := by
  {
    ext w
    simp only [Set.mem_image, Set.mem_preimage]
    exact ⟨fun ⟨z, hz, hw⟩ => by rw [← hw, inv_smul_smul]; exact hz,
      fun hw => ⟨g⁻¹ • w, hw, smul_inv_smul g w⟩⟩
  }
  rw [h_img]
  exact GeneratedByFourElementary.preimage_isCline (III_6 g⁻¹) hS
}

/--
  §1 **Cross-Ratio Reality Criterion for Cocircularity / Collinearity**:
  Given three distinct points `z₁, z₂, z₃ ∈ OnePoint ℂ`, the set of points `z₄ ∈ OnePoint ℂ`
  whose cross-ratio `cross_ratio_Cinfty z₁ z₂ z₃ z₄` lies in `extendedRealAxis` (`ℝ ∪ {∞}`)
  is a cline passing through `z₁, z₂, z₃`.
-/
theorem cross_ratio_real_isCline {z₁ z₂ z₃ : OnePoint ℂ}
    (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃) :
    IsCline {z₄ : OnePoint ℂ | cross_ratio_Cinfty z₁ z₂ z₃ z₄ ∈ extendedRealAxis} := by
{
  obtain ⟨φ, hφ_spec, _⟩ := existsUnique_lft_infty_zero_one h12 h13 h23
  obtain ⟨g, hg⟩ := (isLinFracTrans_iff_gl2 φ).mp hφ_spec.1
  have h_set : {z₄ : OnePoint ℂ | cross_ratio_Cinfty z₁ z₂ z₃ z₄ ∈ extendedRealAxis} =
      (g • ·) ⁻¹' extendedRealAxis := by
  {
    ext z₄
    simp only [Set.mem_setOf_eq, Set.mem_preimage,
      cross_ratio_Cinfty_eq_of_maps h12 h13 h23 hφ_spec z₄, hg]
  }
  rw [h_set]
  exact (III_9 g isCline_extendedRealAxis).1
}

/-!
  §2 Symmetry Across Circles and Lines (Schwarz Reflection Preparation)
-/

/--
  §2 Extended complex conjugation `w ↦ w̄` on `OnePoint ℂ`:
  maps a finite complex number `(z : ℂ)` to `(star z : ℂ)` and fixes `∞`.
-/
def conjExt : OnePoint ℂ → OnePoint ℂ
  | ∞ => ∞
  | (z : ℂ) => (star z : ℂ)

@[simp] lemma conjExt_infty : conjExt ∞ = ∞ := rfl
@[simp] lemma conjExt_coe (z : ℂ) : conjExt (z : ℂ) = (star z : ℂ) := rfl

/--
  §2 `conjExt` is an involution on `OnePoint ℂ`: `conjExt (conjExt w) = w`.
-/
@[simp] lemma conjExt_involutive (w : OnePoint ℂ) : conjExt (conjExt w) = w := by
{
  cases w with
  | infty => rfl
  | coe z => simp
}

/--
  §2 A point `w ∈ OnePoint ℂ` is fixed by `conjExt` if and only if `w ∈ extendedRealAxis`.
-/
lemma conjExt_fixed_iff (w : OnePoint ℂ) :
    conjExt w = w ↔ w ∈ extendedRealAxis := by
{
  cases w with
  | infty =>
    simp [extendedRealAxis]
  | coe z =>
    simp only [conjExt_coe, OnePoint.coe_eq_coe, coe_mem_extendedRealAxis_iff]
    rw [Complex.ext_iff, star_re, star_im]
    exact ⟨fun ⟨_, h⟩ => by linarith, fun h => ⟨rfl, by linarith⟩⟩
}

/--
  §2 Reflection (inversion) `z* = z₀ + R² / conj(z - z₀)` across the circle
  `{z ∈ ℂ : ‖z - z₀‖ = R}` in the complex plane `ℂ`.
-/
noncomputable def circleReflect (z₀ : ℂ) (R : ℝ) (z : ℂ) : ℂ :=
  z₀ + (R ^ 2 : ℂ) / star (z - z₀)

/--
  §2 Extended reflection `z*` across the circle `{z ∈ ℂ : ‖z - z₀‖ = R}` on `OnePoint ℂ`:
  interchanges the center `(z₀ : ℂ)` and `∞`, and maps `(z : ℂ)` (`z ≠ z₀`) to
  `z₀ + R² / conj(z - z₀)`.
-/
noncomputable def circleReflectExt (z₀ : ℂ) (R : ℝ) : OnePoint ℂ → OnePoint ℂ
  | ∞ => (z₀ : ℂ)
  | (z : ℂ) => if z = z₀ then ∞ else (circleReflect z₀ R z : ℂ)

/--
  §2 For `R ≠ 0` and `z ≠ z₀`, `circleReflect z₀ R z ≠ z₀` and
  `circleReflect z₀ R (circleReflect z₀ R z) = z`.
-/
lemma circleReflect_involutive (z₀ : ℂ) {R : ℝ} (hR : R ≠ 0) {z : ℂ} (hz : z ≠ z₀) :
    circleReflect z₀ R z ≠ z₀ ∧ circleReflect z₀ R (circleReflect z₀ R z) = z := by
{
  have hR2 : (R : ℂ) ^ 2 ≠ 0 := pow_ne_zero 2 (Complex.ofReal_ne_zero.mpr hR)
  have h_sub : star (z - z₀) ≠ 0 := star_ne_zero.mpr (sub_ne_zero.mpr hz)
  have h_ne : circleReflect z₀ R z ≠ z₀ := by
  {
    unfold circleReflect
    intro h_eq
    have h0 : (R : ℂ) ^ 2 / star (z - z₀) = 0 := by linear_combination h_eq
    exact div_ne_zero hR2 h_sub h0
  }
  refine ⟨h_ne, ?_⟩
  unfold circleReflect
  have h_star_R2 : star ((R : ℂ) ^ 2) = (R : ℂ) ^ 2 := by
  {
    rw [star_pow, Complex.star_def, Complex.conj_ofReal]
  }
  rw [add_sub_cancel_left, star_div₀, star_star, h_star_R2, div_div_cancel₀ hR2, add_sub_cancel]
}

/--
  §2 For `R ≠ 0`, `circleReflectExt z₀ R` is an involution on `OnePoint ℂ`: `(z*)* = z`.
-/
theorem circleReflectExt_involutive (z₀ : ℂ) {R : ℝ} (hR : R ≠ 0) (w : OnePoint ℂ) :
    circleReflectExt z₀ R (circleReflectExt z₀ R w) = w := by
{
  cases w with
  | infty =>
    simp [circleReflectExt]
  | coe z =>
    by_cases hz : z = z₀
    · subst hz; simp [circleReflectExt]
    · obtain ⟨h_ne, h_inv⟩ := circleReflect_involutive z₀ hR hz
      change circleReflectExt z₀ R (if z = z₀ then ∞ else (circleReflect z₀ R z : OnePoint ℂ)) = (z : OnePoint ℂ)
      rw [if_neg hz]
      change (if circleReflect z₀ R z = z₀ then ∞ else (circleReflect z₀ R (circleReflect z₀ R z) : OnePoint ℂ)) = (z : OnePoint ℂ)
      rw [if_neg h_ne, h_inv]
}

/--
  §2 A finite point `z ≠ z₀` is fixed by `circleReflect z₀ R` (`R > 0`) if and only if
  `z` lies on the circle `‖z - z₀‖ = R`.
-/
theorem circleReflect_fixed_iff (z₀ z : ℂ) {R : ℝ} (hR : 0 < R) (hz : z ≠ z₀) :
    circleReflect z₀ R z = z ↔ ‖z - z₀‖ = R := by
{
  have h_sub : star (z - z₀) ≠ 0 := star_ne_zero.mpr (sub_ne_zero.mpr hz)
  unfold circleReflect
  have h_add : z₀ + (R : ℂ) ^ 2 / star (z - z₀) = z ↔ (R : ℂ) ^ 2 / star (z - z₀) = z - z₀ := by
  {
    constructor <;> intro h <;> linear_combination h
  }
  have h_mul_star : (z - z₀) * star (z - z₀) = (‖z - z₀‖ : ℂ) ^ 2 := by
  {
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
  }
  rw [h_add, div_eq_iff h_sub, h_mul_star, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    Complex.ofReal_inj]
  have h_nonneg : 0 ≤ ‖z - z₀‖ := norm_nonneg (z - z₀)
  exact ⟨fun h => by nlinarith [sq_nonneg (‖z - z₀‖ - R)], fun h => by rw [h]⟩
}

/--
  §2 **Sarason's Cross-Ratio Definition of Symmetry with Respect to a Cline**:
  Two points `z, z_star ∈ OnePoint ℂ` are symmetric with respect to the cline through three
  distinct points `z₁, z₂, z₃ ∈ OnePoint ℂ` if
  `cross_ratio_Cinfty z₁ z₂ z₃ z_star = conjExt (cross_ratio_Cinfty z₁ z₂ z₃ z)`.
-/
def SymmetricWrtTriple (z₁ z₂ z₃ z z_star : OnePoint ℂ) : Prop :=
  cross_ratio_Cinfty z₁ z₂ z₃ z_star = conjExt (cross_ratio_Cinfty z₁ z₂ z₃ z)

/--
  §2 **Theorem III_10 (The Symmetry Principle for Linear-Fractional Transformations)**:
  Every linear-fractional transformation `ψ` (`IsLinFracTrans ψ`) preserves symmetry with respect
  to clines: if `z` and `z_star` are symmetric with respect to `(z₁, z₂, z₃)`, then `ψ z` and
  `ψ z_star` are symmetric with respect to `(ψ z₁, ψ z₂, ψ z₃)`.
-/
theorem III_10_symmetry_principle (ψ : OnePoint ℂ → OnePoint ℂ) (hψ : IsLinFracTrans ψ)
    {z₁ z₂ z₃ : OnePoint ℂ} (h12 : z₁ ≠ z₂) (h13 : z₁ ≠ z₃) (h23 : z₂ ≠ z₃)
    (z z_star : OnePoint ℂ) (h_sym : SymmetricWrtTriple z₁ z₂ z₃ z z_star) :
    SymmetricWrtTriple (ψ z₁) (ψ z₂) (ψ z₃) (ψ z) (ψ z_star) := by
{
  -- By Cross-Ratio Invariance (Exercise III.5.2), ψ preserves both cross-ratios identically
  unfold SymmetricWrtTriple at *
  rw [exercise_III_5_2 ψ hψ z₁ z₂ z₃ z_star h12 h13 h23,
      exercise_III_5_2 ψ hψ z₁ z₂ z₃ z h12 h13 h23]
  exact h_sym
}

/-!
  §3 The Cayley Transform, the Herglotz Kernel, and Disk Automorphisms `Aut(𝔻)`
-/

/-- §3 The open upper half-plane `ℍ = {z ∈ ℂ : Im z > 0}`. -/
def upperHalfPlaneSet : Set ℂ := {z : ℂ | 0 < z.im}

/-- §3 The open right half-plane `{w ∈ ℂ : Re w > 0}`. -/
def rightHalfPlaneSet : Set ℂ := {w : ℂ | 0 < w.re}

/-- §3 The open unit disk `𝔻 = {z ∈ ℂ : ‖z‖ < 1}`. -/
def unitDiskSet : Set ℂ := {z : ℂ | ‖z‖ < 1}

/-- §3 The unit circle `∂𝔻 = {z ∈ ℂ : ‖z‖ = 1}`. -/
def unitCircleSet : Set ℂ := {z : ℂ | ‖z‖ = 1}

/--
  §3 **The Cayley Transform** `w = (z - i) / (z + i)` mapping the upper half-plane `ℍ`
  onto the open unit disk `𝔻`.
-/
noncomputable def cayleyMap (z : ℂ) : ℂ :=
  linFracTrans 1 (-Complex.I) 1 Complex.I z

/--
  §3 **The Inverse Cayley Transform** `z = i * (1 + w) / (1 - w)` mapping the open unit disk `𝔻`
  onto the upper half-plane `ℍ`.
-/
noncomputable def cayleyInvMap (w : ℂ) : ℂ :=
  linFracTrans Complex.I Complex.I (-1) 1 w

/--
  §3 Fundamental norm identity for the Cayley numerator and denominator:
  `‖z + i‖ ^ 2 - ‖z - i‖ ^ 2 = 4 * z.im`.
-/
lemma cayley_norm_sq_diff (z : ℂ) :
    ‖z + Complex.I‖ ^ 2 - ‖z - Complex.I‖ ^ 2 = 4 * z.im := by
{
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.add_re, Complex.add_im,
    Complex.sub_re, Complex.sub_im, Complex.I_re, Complex.I_im]
  ring
}

/--
  §3 For any `z ∈ ℂ` with `z.im ≥ 0`, the Cayley denominator `z + i` is non-zero.
-/
lemma cayley_den_ne_zero {z : ℂ} (hz : 0 ≤ z.im) : z + Complex.I ≠ 0 := by
{
  intro h0
  have him := congrArg Complex.im h0
  simp only [Complex.add_im, Complex.I_im, Complex.zero_im] at him
  linarith
}

/--
  §3 Fundamental radial identity for the Cayley transform:
  When `z + i ≠ 0`, `1 - ‖cayleyMap z‖ ^ 2 = (4 * z.im) / ‖z + i‖ ^ 2`.
-/
theorem cayleyMap_one_sub_norm_sq {z : ℂ} (h_den : z + Complex.I ≠ 0) :
    1 - ‖cayleyMap z‖ ^ 2 = (4 * z.im) / ‖z + Complex.I‖ ^ 2 := by
{
  have h_nsq : ‖z + Complex.I‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h_den)
  unfold cayleyMap linFracTrans
  have h_num : (1 : ℂ) * z + -Complex.I = z - Complex.I := by ring
  have h_den' : (1 : ℂ) * z + Complex.I = z + Complex.I := by ring
  rw [h_num, h_den', norm_div, div_pow, one_sub_div h_nsq, cayley_norm_sq_diff]
}

/--
  §3 The Cayley transform maps `ℍ` (`z.im > 0`) into `𝔻` (`‖cayleyMap z‖ < 1`),
  maps `z = i` to `0`, and maps the real axis (`z.im = 0`) into the unit circle `∂𝔻`.
-/
theorem III_11_cayley_maps :
    cayleyMap Complex.I = 0 ∧
    (∀ z ∈ upperHalfPlaneSet, cayleyMap z ∈ unitDiskSet) ∧
    (∀ x : ℝ, cayleyMap (x : ℂ) ∈ unitCircleSet) := by
{
  refine ⟨?_, ?_, ?_⟩
  · unfold cayleyMap linFracTrans
    have h_num : (1 : ℂ) * Complex.I + -Complex.I = 0 := by ring
    rw [h_num, zero_div]
  · intro z hz
    simp only [upperHalfPlaneSet, Set.mem_setOf_eq] at hz
    simp only [unitDiskSet, Set.mem_setOf_eq]
    have h_den : z + Complex.I ≠ 0 := cayley_den_ne_zero hz.le
    have h_pos : 0 < (4 * z.im) / ‖z + Complex.I‖ ^ 2 :=
      div_pos (by linarith) (sq_pos_of_pos (norm_pos_iff.mpr h_den))
    have h_id := cayleyMap_one_sub_norm_sq h_den
    have h_norm_nonneg : 0 ≤ ‖cayleyMap z‖ := norm_nonneg _
    nlinarith [sq_nonneg (1 - ‖cayleyMap z‖)]
  · intro x
    simp only [unitCircleSet, Set.mem_setOf_eq]
    have h_im : (x : ℂ).im = 0 := Complex.ofReal_im x
    have h_den : (x : ℂ) + Complex.I ≠ 0 := cayley_den_ne_zero (le_of_eq h_im.symm)
    have h_id := cayleyMap_one_sub_norm_sq h_den
    rw [h_im, mul_zero, zero_div] at h_id
    have h_norm_nonneg : 0 ≤ ‖cayleyMap (x : ℂ)‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖cayleyMap (x : ℂ)‖ - 1)]
}

/--
  §3 `cayleyInvMap` is the two-sided inverse of `cayleyMap`:
  for `z + i ≠ 0`, `cayleyInvMap (cayleyMap z) = z`, and for `1 - w ≠ 0`,
  `cayleyMap (cayleyInvMap w) = w`.
-/
theorem cayleyMap_inv {z w : ℂ} (hz : z + Complex.I ≠ 0) (hw : 1 - w ≠ 0) :
    cayleyInvMap (cayleyMap z) = z ∧ cayleyMap (cayleyInvMap w) = w := by
{
  have h2i : (2 : ℂ) * Complex.I ≠ 0 := mul_ne_zero two_ne_zero Complex.I_ne_zero
  unfold cayleyMap cayleyInvMap linFracTrans
  have hz' : (1 : ℂ) * z + Complex.I ≠ 0 := by simpa using hz
  have hw' : (-1 : ℂ) * w + 1 ≠ 0 := by
  {
    intro h0; apply hw; linear_combination h0
  }
  refine ⟨?_, ?_⟩
  · field_simp [hz', h2i]
    ring
  · have h_den2 : (1 : ℂ) * ((Complex.I * w + Complex.I) / (-1 * w + 1)) + Complex.I =
        (2 * Complex.I) / (-1 * w + 1) := by
    {
      rw [one_mul, div_add' _ _ _ hw']
      congr 1
      ring
    }
    have h_num2 : (1 : ℂ) * ((Complex.I * w + Complex.I) / (-1 * w + 1)) + -Complex.I =
        (2 * Complex.I * w) / (-1 * w + 1) := by
    {
      rw [one_mul, div_add' _ _ _ hw']
      congr 1
      ring
    }
    rw [h_num2, h_den2, div_div_div_cancel_right₀ hw', mul_div_cancel_left₀ w h2i]
}

/--
  §3 **The Herglotz Kernel** `H(ζ, z) = (ζ + z) / (ζ - z)` mapping `z ∈ 𝔻` onto the
  right half-plane `{w ∈ ℂ : Re w > 0}` for `ζ ∈ ∂𝔻`.
-/
noncomputable def herglotzKernel (ζ z : ℂ) : ℂ :=
  (ζ + z) / (ζ - z)

/--
  §3 **The Poisson Kernel Identity via the Herglotz Kernel**:
  For any `ζ ∈ ∂𝔻` (`‖ζ‖ = 1`) and `z ≠ ζ`,
  `Re ((ζ + z) / (ζ - z)) = (1 - ‖z‖ ^ 2) / ‖ζ - z‖ ^ 2`.
-/
theorem herglotzKernel_re {ζ z : ℂ} (hζ : ‖ζ‖ = 1) :
    (herglotzKernel ζ z).re = (1 - ‖z‖ ^ 2) / ‖ζ - z‖ ^ 2 := by
{
  unfold herglotzKernel
  have h_ζ_sq : ζ.re * ζ.re + ζ.im * ζ.im = 1 := by
  {
    have h1 : ‖ζ‖ ^ 2 = 1 := by rw [hζ, one_pow]
    rwa [Complex.sq_norm, Complex.normSq_apply] at h1
  }
  rw [Complex.div_re, ← Complex.sq_norm, Complex.sq_norm z, Complex.normSq_apply]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im]
  linear_combination (1 / ‖ζ - z‖ ^ 2) * h_ζ_sq
}

/--
  §3 **Properties of the Herglotz Kernel on `𝔻` and `∂𝔻`**:
  For `ζ ∈ ∂𝔻` (`‖ζ‖ = 1`):
  1. `herglotzKernel ζ 0 = 1`,
  2. For every `z ∈ 𝔻` (`‖z‖ < 1`), `Re (herglotzKernel ζ z) > 0` (maps `𝔻` into the right half-plane),
  3. For every `z ∈ ∂𝔻` (`‖z‖ = 1`), `Re (herglotzKernel ζ z) = 0` (purely imaginary on `∂𝔻 \ {ζ}`).
-/
theorem III_11_herglotz_properties {ζ : ℂ} (hζ : ‖ζ‖ = 1) :
    herglotzKernel ζ 0 = 1 ∧
    (∀ z ∈ unitDiskSet, 0 < (herglotzKernel ζ z).re) ∧
    (∀ z ∈ unitCircleSet, (herglotzKernel ζ z).re = 0) := by
{
  have hζ_ne : ζ ≠ 0 := by
  {
    intro h0; rw [h0, norm_zero] at hζ; exact zero_ne_one hζ
  }
  refine ⟨?_, ?_, ?_⟩
  · unfold herglotzKernel
    rw [add_zero, sub_zero, div_self hζ_ne]
  · intro z hz
    simp only [unitDiskSet, Set.mem_setOf_eq] at hz
    have h_ne : ζ - z ≠ 0 := by
    {
      intro h_sub
      have h_eq : ζ = z := sub_eq_zero.mp h_sub
      rw [← h_eq, hζ] at hz
      exact lt_irrefl 1 hz
    }
    rw [herglotzKernel_re hζ]
    have h_num_pos : 0 < 1 - ‖z‖ ^ 2 := by
    {
      have h_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
      nlinarith
    }
    exact div_pos h_num_pos (sq_pos_of_pos (norm_pos_iff.mpr h_ne))
  · intro z hz
    simp only [unitCircleSet, Set.mem_setOf_eq] at hz
    rw [herglotzKernel_re hζ, hz, one_pow, sub_self, zero_div]
}

/--
  §3 **Blaschke / Disk Automorphism Factor** `φ_a(z) = (z - a) / (1 - ā * z)` for `a ∈ 𝔻`.
-/
noncomputable def blaschkeFactor (a z : ℂ) : ℂ :=
  (z - a) / (1 - star a * z)

/--
  §3 General disk automorphism `diskAut λ a z = λ * (z - a) / (1 - ā * z)` for `‖λ‖ = 1` and `a ∈ 𝔻`.
-/
noncomputable def diskAut (u a z : ℂ) : ℂ :=
  u * blaschkeFactor a z

/--
  §3 **Fundamental Algebraic Identity for Disk Automorphisms**:
  `‖1 - ā * z‖ ^ 2 - ‖z - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2)`.
-/
theorem blaschke_norm_sq_diff (a z : ℂ) :
    ‖1 - star a * z‖ ^ 2 - ‖z - a‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) := by
{
  simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
    Complex.mul_re, Complex.mul_im, Complex.one_re, Complex.one_im, star_re, star_im]
  ring
}

/--
  §3 For `a ∈ 𝔻` (`‖a‖ < 1`) and `‖z‖ ≤ 1`, the denominator `1 - ā * z` is non-zero.
-/
lemma blaschke_den_ne_zero {a z : ℂ} (ha : ‖a‖ < 1) (hz : ‖z‖ ≤ 1) :
    1 - star a * z ≠ 0 := by
{
  intro h0
  have h_eq : star a * z = 1 := (sub_eq_zero.mp h0).symm
  have h_norm : ‖star a * z‖ = 1 := by rw [h_eq, norm_one]
  rw [norm_mul, norm_star] at h_norm
  have ha_nonneg : 0 ≤ ‖a‖ := norm_nonneg a
  nlinarith
}

/--
  §3 **Radial Identity for `blaschkeFactor`**:
  When `1 - ā * z ≠ 0`,
  `1 - ‖blaschkeFactor a z‖ ^ 2 = (1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2) / ‖1 - ā * z‖ ^ 2`.
-/
theorem blaschkeFactor_one_sub_norm_sq {a z : ℂ} (h_den : 1 - star a * z ≠ 0) :
    1 - ‖blaschkeFactor a z‖ ^ 2 =
      ((1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2)) / ‖1 - star a * z‖ ^ 2 := by
{
  have h_nsq : ‖1 - star a * z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr h_den)
  unfold blaschkeFactor
  rw [norm_div, div_pow, one_sub_div h_nsq, blaschke_norm_sq_diff]
}

/--
  §3 **Theorem III_12 (Properties of Disk Automorphisms `blaschkeFactor a`)**:
  For every `a ∈ 𝔻` (`‖a‖ < 1`):
  1. `blaschkeFactor a a = 0` and `blaschkeFactor a 0 = -a`,
  2. `blaschkeFactor a` maps `𝔻` (`‖z‖ < 1`) into `𝔻` (`‖blaschkeFactor a z‖ < 1`),
  3. `blaschkeFactor a` maps `∂𝔻` (`‖z‖ = 1`) into `∂𝔻` (`‖blaschkeFactor a z‖ = 1`),
  4. `blaschkeFactor (-a)` is the inverse of `blaschkeFactor a` on `{z : ‖z‖ ≤ 1}`.
-/
theorem III_12_blaschke_properties {a : ℂ} (ha : ‖a‖ < 1) :
    blaschkeFactor a a = 0 ∧
    blaschkeFactor a 0 = -a ∧
    (∀ z ∈ unitDiskSet, blaschkeFactor a z ∈ unitDiskSet) ∧
    (∀ z ∈ unitCircleSet, blaschkeFactor a z ∈ unitCircleSet) ∧
    (∀ z : ℂ, ‖z‖ ≤ 1 → blaschkeFactor (-a) (blaschkeFactor a z) = z) := by
{
  have ha_nonneg : 0 ≤ ‖a‖ := norm_nonneg a
  have ha_sq_pos : 0 < 1 - ‖a‖ ^ 2 := by nlinarith
  have ha_one_ne : (1 : ℂ) - star a * a ≠ 0 := by
  {
    rw [Complex.star_def, Complex.conj_mul', ← Complex.ofReal_one, ← Complex.ofReal_pow,
      ← Complex.ofReal_sub]
    exact Complex.ofReal_ne_zero.mpr ha_sq_pos.ne'
  }
  refine ⟨by unfold blaschkeFactor; rw [sub_self, zero_div],
          by unfold blaschkeFactor; simp, ?_, ?_, ?_⟩
  · intro z hz
    simp only [unitDiskSet, Set.mem_setOf_eq] at hz ⊢
    have h_den := blaschke_den_ne_zero ha hz.le
    have hz_nonneg : 0 ≤ ‖z‖ := norm_nonneg z
    have h_pos : 0 < ((1 - ‖a‖ ^ 2) * (1 - ‖z‖ ^ 2)) / ‖1 - star a * z‖ ^ 2 :=
      div_pos (mul_pos ha_sq_pos (by nlinarith)) (sq_pos_of_pos (norm_pos_iff.mpr h_den))
    have h_id := blaschkeFactor_one_sub_norm_sq h_den
    have h_norm_nonneg : 0 ≤ ‖blaschkeFactor a z‖ := norm_nonneg _
    nlinarith [sq_nonneg (1 - ‖blaschkeFactor a z‖)]
  · intro z hz
    simp only [unitCircleSet, Set.mem_setOf_eq] at hz ⊢
    have h_den := blaschke_den_ne_zero ha (le_of_eq hz)
    have h_id := blaschkeFactor_one_sub_norm_sq h_den
    rw [hz, one_pow, sub_self, mul_zero, zero_div] at h_id
    have h_norm_nonneg : 0 ≤ ‖blaschkeFactor a z‖ := norm_nonneg _
    nlinarith [sq_nonneg (‖blaschkeFactor a z‖ - 1)]
  · intro z hz
    have h_den := blaschke_den_ne_zero ha hz
    unfold blaschkeFactor
    rw [star_neg, sub_neg_eq_add, neg_mul, sub_neg_eq_add]
    have h_num : (z - a) / (1 - star a * z) + a =
        (z * (1 - star a * a)) / (1 - star a * z) := by
    {
      rw [div_add' _ _ _ h_den]
      congr 1
      ring
    }
    have h_den2 : 1 + star a * ((z - a) / (1 - star a * z)) =
        (1 - star a * a) / (1 - star a * z) := by
    {
      rw [mul_div_assoc', add_div' _ _ _ h_den]
      congr 1
      ring
    }
    rw [h_num, h_den2, div_div_div_cancel_right₀ h_den, mul_div_cancel_right₀ z ha_one_ne]
}

/--
  §3 Complex derivative of `blaschkeFactor a` at any `z ∈ ℂ` with `1 - ā * z ≠ 0`:
  `(d/dz) ((z - a) / (1 - ā * z)) = (1 - ‖a‖ ^ 2) / (1 - ā * z) ^ 2`.
-/
theorem blaschkeFactor_hasDerivAt (a z : ℂ) (h_den : 1 - star a * z ≠ 0) :
    HasDerivAt (blaschkeFactor a) ((1 - (‖a‖ : ℂ) ^ 2) / (1 - star a * z) ^ 2) z := by
{
  have h_eq_lft : blaschkeFactor a = linFracTrans 1 (-a) (-star a) 1 := by
  {
    ext w
    unfold blaschkeFactor linFracTrans
    ring
  }
  have h_den' : (-star a) * z + 1 ≠ 0 := by
  {
    intro h0; apply h_den; linear_combination h0
  }
  rw [h_eq_lft]
  have h_deriv := linFracTrans_hasDerivAt 1 (-a) (-star a) 1 z h_den'
  have h_num : ((1 : ℂ) * 1 - (-a) * (-star a)) / ((-star a) * z + 1) ^ 2 =
      (1 - (‖a‖ : ℂ) ^ 2) / (1 - star a * z) ^ 2 := by
  {
    have h_aa : a * star a = (‖a‖ : ℂ) ^ 2 := by
    {
      rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.ofReal_pow]
    }
    congr 1
    · linear_combination -h_aa
    · ring
  }
  rwa [h_num] at h_deriv
}

/-!
  §4 Starlike Domains and Starlike Holomorphic Maps in Terms of Polar Angle θ.
  Connecting the polar coordinate operators `polar_partial_theta` and `polar_partial_r`
  from `Sarason/Definitions.lean` and the polar Cauchy–Riemann equations (`exercise_II_6_3`)
  and argument `arg` from `Sarason/Chapter2.lean` to starlike univalent functions and
  the Herglotz–Pommerenke logarithmic derivative representation of radial slit maps.
-/

/--
  §4 Polar coordinate point `z = r cos θ + i r sin θ` in `ℂ`, matching the
  `(p.1 * Real.cos p.2, p.1 * Real.sin p.2)` parameterization of `polar_partial_r`
  and `polar_partial_theta` in `Sarason/Definitions.lean`.
-/
noncomputable def polarPoint (r θ : ℝ) : ℂ :=
  ((r * Real.cos θ : ℝ) : ℂ) + ((r * Real.sin θ : ℝ) : ℂ) * I

@[simp]
lemma polarPoint_re (r θ : ℝ) : (polarPoint r θ).re = r * Real.cos θ := by
{
  unfold polarPoint
  simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring
}

@[simp]
lemma polarPoint_im (r θ : ℝ) : (polarPoint r θ).im = r * Real.sin θ := by
{
  unfold polarPoint
  simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
    Complex.I_re, Complex.I_im]
  ring
}

lemma polarPoint_scale (t r θ : ℝ) :
    polarPoint (t * r) θ = (t : ℂ) * polarPoint r θ := by
{
  apply Complex.ext
  · simp only [polarPoint_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · simp only [polarPoint_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
}

lemma polarPoint_norm_sq (r θ : ℝ) : ‖polarPoint r θ‖ ^ 2 = r ^ 2 := by
{
  rw [← Complex.normSq_eq_norm_sq, Complex.normSq_apply, polarPoint_re, polarPoint_im]
  calc (r * Real.cos θ) * (r * Real.cos θ) + (r * Real.sin θ) * (r * Real.sin θ)
      = r ^ 2 * (Real.cos θ ^ 2 + Real.sin θ ^ 2) := by ring
    _ = r ^ 2 * 1 := by rw [Real.cos_sq_add_sin_sq θ]
    _ = r ^ 2 := by ring
}

lemma polarPoint_norm_of_nonneg {r : ℝ} (hr : 0 ≤ r) (θ : ℝ) :
    ‖polarPoint r θ‖ = r := by
{
  have h_sq := polarPoint_norm_sq r θ
  have h_sqrt := congrArg Real.sqrt h_sq
  rwa [Real.sqrt_sq (norm_nonneg _), Real.sqrt_sq hr] at h_sqrt
}

lemma polarPoint_ne_zero_of_pos {r : ℝ} (hr : 0 < r) (θ : ℝ) :
    polarPoint r θ ≠ 0 := by
{
  intro h0
  have h_norm := polarPoint_norm_of_nonneg hr.le θ
  rw [h0, norm_zero] at h_norm
  linarith
}

lemma polarPoint_mem_unitDiskSet {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (θ : ℝ) :
    polarPoint r θ ∈ unitDiskSet := by
{
  simp only [unitDiskSet, Set.mem_setOf_eq]
  rw [polarPoint_norm_of_nonneg hr0 θ]
  exact hr1
}

lemma polarPoint_one_mem_unitCircleSet (θ : ℝ) :
    polarPoint 1 θ ∈ unitCircleSet := by
{
  simp only [unitCircleSet, Set.mem_setOf_eq]
  exact polarPoint_norm_of_nonneg zero_le_one θ
}

/--
  §4 Weierstrass `HasDerivAt_R_to_C_eps` derivative of the polar circle path
  `θ ↦ polarPoint r θ` with respect to the polar angle `θ`:
  `d/dθ (r cos θ + i r sin θ) = i * polarPoint r θ₀`.
-/
theorem polarPoint_hasDerivAt_theta_eps (r θ₀ : ℝ) :
    HasDerivAt_R_to_C_eps (fun θ => polarPoint r θ) (I * polarPoint r θ₀) θ₀ := by
{
  have h_x := ComplexAnalysis.R2.polar_partial_theta_is_deriv
    (u := fun p => 1 * p.1 + 0 * p.2) (ux₀ := 1) (uy₀ := 0) (r₀ := r) (θ₀ := θ₀) (by {
      have h0 := linear_hasFDerivAt_R2_eps 1 0 0 0 (r * Real.cos θ₀, r * Real.sin θ₀)
      simpa using h0
    })
  have h_y := ComplexAnalysis.R2.polar_partial_theta_is_deriv
    (u := fun p => 0 * p.1 + 1 * p.2) (ux₀ := 0) (uy₀ := 1) (r₀ := r) (θ₀ := θ₀) (by {
      have h0 := linear_hasFDerivAt_R2_eps 0 1 0 0 (r * Real.cos θ₀, r * Real.sin θ₀)
      simpa using h0
    })
  have h_iff_x := (HasDerivAt_RtoR2_eps_iff_R_to_C_eps _ _ θ₀).mp h_x
  have h_iff_y := (HasDerivAt_RtoR2_eps_iff_R_to_C_eps _ _ θ₀).mp h_y
  rw [← hasDerivAt_R_to_C_iff_eps] at h_iff_x h_iff_y ⊢
  have hx_clean : HasDerivAt (fun θ : ℝ => ((r * Real.cos θ : ℝ) : ℂ))
      (((-r * Real.sin θ₀ : ℝ) : ℂ)) θ₀ := by
  {
    convert h_iff_x using 1
    · ext θ; apply Complex.ext <;> simp
    · apply Complex.ext <;> simp
  }
  have hy_clean : HasDerivAt (fun θ : ℝ => ((r * Real.sin θ : ℝ) : ℂ))
      (((r * Real.cos θ₀ : ℝ) : ℂ)) θ₀ := by
  {
    convert h_iff_y using 1
    · ext θ; apply Complex.ext <;> simp
    · apply Complex.ext <;> simp
  }
  have h_comb := hx_clean.add (hy_clean.mul_const I)
  have h_val :
      (((-r * Real.sin θ₀ : ℝ) : ℂ)) + (((r * Real.cos θ₀ : ℝ) : ℂ)) * I =
      I * polarPoint r θ₀ := by
  {
    apply Complex.ext
    · simp only [polarPoint_re, polarPoint_im, Complex.add_re, Complex.mul_re,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
    · simp only [polarPoint_re, polarPoint_im, Complex.add_im, Complex.mul_im,
        Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
      ring
  }
  rw [← h_val]
  exact h_comb
}

/--
  Every complex number `z` is represented in polar coordinates by its modulus `‖z‖`
  and its principal argument `arg z` (`z = polarPoint ‖z‖ (arg z)`).
-/
lemma polarPoint_norm_arg (z : ℂ) : polarPoint ‖z‖ (arg z) = z := by
{
  by_cases hz : z = 0
  · subst hz
    apply Complex.ext <;> simp [polarPoint_re, polarPoint_im]
  · have h_norm : ‖z‖ ≠ 0 := norm_ne_zero_iff.mpr hz
    apply Complex.ext
    · rw [polarPoint_re, Complex.cos_arg hz, mul_div_cancel₀ _ h_norm]
    · rw [polarPoint_im, Complex.sin_arg, mul_div_cancel₀ _ h_norm]
}

/--
  §4 Geometric definition of a starlike domain `Ω ⊆ ℂ` with respect to the origin `0`
  in terms of the polar angle `θ`: `0 ∈ Ω`, and along every ray of fixed polar angle `θ`,
  if `polarPoint r θ ∈ Ω` (`r ≥ 0`), then `polarPoint (t * r) θ ∈ Ω` for all `t ∈ [0, 1]`.
-/
def IsStarlikeDomain_theta (Ω : Set ℂ) : Prop :=
  (0 : ℂ) ∈ Ω ∧
  ∀ (r θ : ℝ), 0 ≤ r → polarPoint r θ ∈ Ω →
    ∀ t : ℝ, 0 ≤ t → t ≤ 1 → polarPoint (t * r) θ ∈ Ω

/--
  Equivalence between the polar-angle definition `IsStarlikeDomain_theta Ω` and ray
  starlikeness using `arg z`: `0 ∈ Ω` and for every `z ∈ Ω` and `t ∈ [0, 1]`,
  `polarPoint (t * ‖z‖) (arg z) ∈ Ω`.
-/
theorem isStarlikeDomain_theta_iff_arg_ray (Ω : Set ℂ) :
    IsStarlikeDomain_theta Ω ↔
      ((0 : ℂ) ∈ Ω ∧ ∀ z ∈ Ω, ∀ t : ℝ, 0 ≤ t → t ≤ 1 → polarPoint (t * ‖z‖) (arg z) ∈ Ω) := by
{
  constructor
  · rintro ⟨h0, hray⟩
    refine ⟨h0, fun z hz t ht0 ht1 => ?_⟩
    apply hray ‖z‖ (arg z) (norm_nonneg z)
    · rw [polarPoint_norm_arg]
      exact hz
    · exact ht0
    · exact ht1
  · rintro ⟨h0, harg⟩
    refine ⟨h0, fun r θ hr hmem t ht0 ht1 => ?_⟩
    have hz := harg (polarPoint r θ) hmem t ht0 ht1
    rw [polarPoint_norm_of_nonneg hr θ] at hz
    rw [polarPoint_scale, ← polarPoint_norm_arg (polarPoint r θ),
      polarPoint_norm_of_nonneg hr θ, ← polarPoint_scale]
    exact hz
}

/--
  §4 Angular rate of change `∂(arg f)/∂θ` of the image argument along the polar circle
  `p = (r, θ)` (`z = r cos θ + i r sin θ`), defined directly in terms of `polar_partial_theta`
  from `Sarason/Definitions.lean` and `Sarason/Chapter2.lean`:
  `(u * v_θ - v * u_θ) / (u² + v²)`.
-/
noncomputable def argPolarDeriv_theta (u v ux uy vx vy : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  let q : ℝ × ℝ := (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
  (u q * polar_partial_theta vx vy p - v q * polar_partial_theta ux uy p) /
    (u q ^ 2 + v q ^ 2)

/--
  Under the Cartesian Cauchy–Riemann equations at `q = (r cos θ, r sin θ)`, the complex
  polar `θ`-derivative `u_θ + i v_θ` equals `i z f'(z)`.
-/
lemma polar_partial_theta_complex_of_cr (ux uy vx vy : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (h_CR1 : ux (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = vy (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
    (h_CR2 : uy (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = -vx (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) :
    let q : ℝ × ℝ := (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
    (polar_partial_theta ux uy p : ℂ) + (polar_partial_theta vx vy p : ℂ) * I =
      I * polarPoint p.1 p.2 * ((ux q : ℂ) + (vx q : ℂ) * I) := by
{
  intro q
  unfold polar_partial_theta polarPoint
  dsimp [q]
  rw [h_CR1, h_CR2]
  apply Complex.ext
  · simp; ring
  · simp; ring
}

/--
  Using the polar Cauchy–Riemann equations (`exercise_II_6_3` from `Sarason/Chapter2.lean`),
  the angular argument derivative `argPolarDeriv_theta` equals `r * ∂(ln |f|)/∂r`, i.e.,
  `r * (u * u_r + v * v_r) / (u² + v²)`.
-/
theorem argPolarDeriv_theta_eq_polar_partial_r (u v ux uy vx vy : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (h_CR1 : ux (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = vy (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
    (h_CR2 : uy (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = -vx (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) :
    let q : ℝ × ℝ := (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
    argPolarDeriv_theta u v ux uy vx vy p =
      p.1 * (u q * polar_partial_r ux uy p + v q * polar_partial_r vx vy p) /
        (u q ^ 2 + v q ^ 2) := by
{
  intro q
  rcases exercise_II_6_3 ux uy vx vy p h_CR1 h_CR2 with ⟨h_ur, h_vr⟩
  unfold argPolarDeriv_theta
  dsimp [q]
  have h_num :
      u (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * polar_partial_theta vx vy p -
        v (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * polar_partial_theta ux uy p =
      p.1 * (u (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * polar_partial_r ux uy p +
        v (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * polar_partial_r vx vy p) := by
  {
    linear_combination
      u (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * h_ur.symm +
      v (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * h_vr.symm
  }
  rw [h_num]
}

/--
  §4 Fundamental Starlike Angle-Derivative Identity:
  Under the Cauchy–Riemann equations at `z = polarPoint r θ`, the polar angular rate of change
  `argPolarDeriv_theta` of `arg f(r e^{iθ})` with respect to `θ` equals `Re(z f'(z) / f(z))`.
-/
theorem argPolarDeriv_theta_eq_re_logDeriv (u v ux uy vx vy : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (h_CR1 : ux (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = vy (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
    (h_CR2 : uy (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = -vx (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) :
    let q : ℝ × ℝ := (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
    let f_z : ℂ := (u q : ℂ) + (v q : ℂ) * I
    let f'_z : ℂ := (ux q : ℂ) + (vx q : ℂ) * I
    argPolarDeriv_theta u v ux uy vx vy p = ((polarPoint p.1 p.2 * f'_z) / f_z).re := by
{
  intros q f_z f'_z
  unfold argPolarDeriv_theta polar_partial_theta polarPoint
  dsimp [q, f_z, f'_z]
  rw [h_CR1, h_CR2, Complex.div_re, Complex.normSq_apply]
  simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
    Complex.ofReal_re, Complex.ofReal_im, Complex.I_re, Complex.I_im]
  ring
}

/--
  Connection to `Complex.arg` from Chapter 2: for `w = (z * f') / f_z ≠ 0`,
  `Re(z f' / f_z) = ‖z f' / f_z‖ * cos(arg(z f' / f_z))`, so `Re(z f' / f_z) > 0`
  if and only if `cos(arg(z f' / f_z)) > 0`.
-/
theorem re_logDeriv_pos_iff_cos_arg_pos {z f' f_z : ℂ} (hw : (z * f') / f_z ≠ 0) :
    0 < ((z * f') / f_z).re ↔ 0 < Real.cos (arg ((z * f') / f_z)) := by
{
  have h_cos := Complex.cos_arg hw
  have h_norm_pos : 0 < ‖(z * f') / f_z‖ := norm_pos_iff.mpr hw
  rw [h_cos, div_pos_iff_of_pos_right h_norm_pos]
}

/--
  §4 Angle-based (`θ` / `polar_partial_theta`) and `_eps`-based definition of a
  starlike holomorphic function `f : ℂ → ℂ` on the unit disk `unitDiskSet`:
  1. `HolomorphicOn_eps f unitDiskSet`
  2. `f 0 = 0` and `∀ z ∈ unitDiskSet, z ≠ 0 → f z ≠ 0`
  3. On every circle of radius `0 < r < 1`, the angular argument derivative
     `argPolarDeriv_theta` with respect to `θ` is strictly positive (`∂(arg f)/∂θ > 0`).
-/
def IsStarlikeOnDisk_theta_eps (f : ℂ → ℂ) : Prop :=
  HolomorphicOn_eps f unitDiskSet ∧
  f 0 = 0 ∧
  (∀ z ∈ unitDiskSet, z ≠ 0 → f z ≠ 0) ∧
  ∀ (r θ : ℝ) (ux uy vx vy : ℝ × ℝ → ℝ),
    0 < r → r < 1 →
    HasPartialDerivX_C_to_R_eps (fun w => (f w).re) (ux (r * Real.cos θ, r * Real.sin θ)) (polarPoint r θ) →
    HasPartialDerivY_C_to_R_eps (fun w => (f w).re) (uy (r * Real.cos θ, r * Real.sin θ)) (polarPoint r θ) →
    HasPartialDerivX_C_to_R_eps (fun w => (f w).im) (vx (r * Real.cos θ, r * Real.sin θ)) (polarPoint r θ) →
    HasPartialDerivY_C_to_R_eps (fun w => (f w).im) (vy (r * Real.cos θ, r * Real.sin θ)) (polarPoint r θ) →
    0 < argPolarDeriv_theta
      (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).re)
      (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).im)
      ux uy vx vy (r, θ)

/--
  §4 Analytic logarithmic-derivative definition of a starlike holomorphic function on
  `unitDiskSet` using `HolomorphicOn_eps`, `DifferentiableAt_eps`, and `deriv_eps`:
  `Re(z * deriv_eps f z hd / f z) > 0` for all `z ∈ unitDiskSet \ {0}`.
-/
def IsStarlikeLogDeriv_eps (f : ℂ → ℂ) : Prop :=
  HolomorphicOn_eps f unitDiskSet ∧
  f 0 = 0 ∧
  (∀ z ∈ unitDiskSet, z ≠ 0 → f z ≠ 0) ∧
  ∀ (z : ℂ), z ∈ unitDiskSet → z ≠ 0 →
    ∀ (hd : DifferentiableAt_eps f z), 0 < ((z * deriv_eps f z hd) / f z).re

lemma isStarlikeLogDeriv_eps_of_theta_eps {f : ℂ → ℂ} (h : IsStarlikeOnDisk_theta_eps f) :
    IsStarlikeLogDeriv_eps f := by
{
  rcases h with ⟨h_hol, h0, hne0, h_theta⟩
  refine ⟨h_hol, h0, hne0, fun z hz hzne hd => ?_⟩
  have hr_pos : 0 < ‖z‖ := norm_pos_iff.mpr hzne
  have hz_polar : polarPoint ‖z‖ (arg z) = z := polarPoint_norm_arg z
  let f' : ℂ := deriv_eps f z hd
  have h_deriv : HasDerivAt_eps f f' (polarPoint ‖z‖ (arg z)) := by
  {
    rw [hz_polar]
    exact Classical.choose_spec hd
  }
  rcases hasDerivAt_eps_imp_cauchy_riemann h_deriv with ⟨h_ux, h_uy, h_vx, h_vy⟩
  let ux : ℝ × ℝ → ℝ := fun _ => f'.re
  let uy : ℝ × ℝ → ℝ := fun _ => -f'.im
  let vx : ℝ × ℝ → ℝ := fun _ => f'.im
  let vy : ℝ × ℝ → ℝ := fun _ => f'.re
  have h_pos := h_theta ‖z‖ (arg z) ux uy vx vy hr_pos hz h_ux h_uy h_vx h_vy
  have h_id := argPolarDeriv_theta_eq_re_logDeriv
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).re)
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).im)
    ux uy vx vy (‖z‖, arg z) rfl (by ring)
  dsimp [ux, vx] at h_id
  change argPolarDeriv_theta
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).re)
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).im)
    ux uy vx vy (‖z‖, arg z) =
    (polarPoint ‖z‖ (arg z) * ((f'.re : ℂ) + (f'.im : ℂ) * I) /
      (((f (polarPoint ‖z‖ (arg z))).re : ℂ) + ((f (polarPoint ‖z‖ (arg z))).im : ℂ) * I)).re at h_id
  rw [hz_polar, Complex.re_add_im (f z), Complex.re_add_im f'] at h_id
  rwa [← h_id]
}

lemma isStarlikeOnDisk_theta_eps_of_logDeriv_eps {f : ℂ → ℂ} (h : IsStarlikeLogDeriv_eps f) :
    IsStarlikeOnDisk_theta_eps f := by
{
  rcases h with ⟨h_hol, h0, hne0, h_log⟩
  refine ⟨h_hol, h0, hne0, fun r θ ux uy vx vy hr0 hr1 h_ux h_uy h_vx h_vy => ?_⟩
  have hz_mem : polarPoint r θ ∈ unitDiskSet := polarPoint_mem_unitDiskSet hr0.le hr1 θ
  have hz_ne : polarPoint r θ ≠ 0 := polarPoint_ne_zero_of_pos hr0 θ
  have hd : DifferentiableAt_eps f (polarPoint r θ) := h_hol (polarPoint r θ) hz_mem
  have h_deriv : HasDerivAt_eps f (deriv_eps f (polarPoint r θ) hd) (polarPoint r θ) :=
    Classical.choose_spec hd
  rcases hasDerivAt_eps_imp_cauchy_riemann h_deriv with ⟨h_ux', h_uy', h_vx', h_vy'⟩
  have h_ux_eq := partial_deriv_unique_x _ _ _ _ h_ux h_ux'
  have h_uy_eq := partial_deriv_unique_y _ _ _ _ h_uy h_uy'
  have h_vx_eq := partial_deriv_unique_x _ _ _ _ h_vx h_vx'
  have h_vy_eq := partial_deriv_unique_y _ _ _ _ h_vy h_vy'
  have h_id := argPolarDeriv_theta_eq_re_logDeriv
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).re)
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).im)
    ux uy vx vy (r, θ) (h_ux_eq.trans h_vy_eq.symm) (by rw [h_uy_eq, h_vx_eq])
  dsimp at h_id
  change argPolarDeriv_theta
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).re)
    (fun q => (f ((q.1 : ℂ) + (q.2 : ℂ) * I)).im)
    ux uy vx vy (r, θ) =
    (polarPoint r θ * ((ux (r * Real.cos θ, r * Real.sin θ) : ℂ) +
      (vx (r * Real.cos θ, r * Real.sin θ) : ℂ) * I) /
      (((f (polarPoint r θ)).re : ℂ) + ((f (polarPoint r θ)).im : ℂ) * I)).re at h_id
  rw [h_ux_eq, h_vx_eq, Complex.re_add_im, Complex.re_add_im (f (polarPoint r θ))] at h_id
  rw [h_id]
  exact h_log (polarPoint r θ) hz_mem hz_ne hd
}

/--
  Equivalence between the polar-angle (`θ` / `polar_partial_theta`) definition
  `IsStarlikeOnDisk_theta_eps f` and the logarithmic-derivative `_eps` definition
  `IsStarlikeLogDeriv_eps f`.
-/
theorem isStarlikeOnDisk_theta_eps_iff_logDeriv_eps (f : ℂ → ℂ) :
    IsStarlikeOnDisk_theta_eps f ↔ IsStarlikeLogDeriv_eps f := by
{
  exact ⟨isStarlikeLogDeriv_eps_of_theta_eps, isStarlikeOnDisk_theta_eps_of_logDeriv_eps⟩
}

/--
  §4 Single-factor Herglotz–Pommerenke identity: for `ζ ∈ unitCircleSet` (`‖ζ‖ = 1`),
  `1 + 2 * (conj ζ * z) / (1 - conj ζ * z) = herglotzKernel ζ z`.
-/
lemma pommerenke_single_term_eq_herglotz {ζ z : ℂ}
    (hζ : ζ ∈ unitCircleSet) (hne : ζ - z ≠ 0) :
    (1 : ℂ) + (2 : ℂ) * (star ζ * z) / (1 - star ζ * z) = herglotzKernel ζ z := by
{
  simp only [unitCircleSet, Set.mem_setOf_eq] at hζ
  have hζ_ne : ζ ≠ 0 := by
  {
    intro h0; rw [h0, norm_zero] at hζ; norm_num at hζ
  }
  have h_mul_conj : ζ * star ζ = 1 := by
  {
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, hζ]
    norm_num
  }
  have h_den_eq : ζ * (1 - star ζ * z) = ζ - z := by
  {
    calc ζ * (1 - star ζ * z) = ζ - (ζ * star ζ) * z := by ring
      _ = ζ - 1 * z := by rw [h_mul_conj]
      _ = ζ - z := by ring
  }
  have h_den_ne : 1 - star ζ * z ≠ 0 := by
  {
    intro h0
    apply hne
    rw [← h_den_eq, h0, mul_zero]
  }
  unfold herglotzKernel
  rw [add_div' _ _ _ h_den_ne, one_mul]
  have h_num_eq : ζ * (1 - star ζ * z + 2 * (star ζ * z)) = ζ + z := by
  {
    calc ζ * (1 - star ζ * z + 2 * (star ζ * z))
        = ζ + (ζ * star ζ) * z := by ring
      _ = ζ + 1 * z := by rw [h_mul_conj]
      _ = ζ + z := by ring
  }
  calc (1 - star ζ * z + 2 * (star ζ * z)) / (1 - star ζ * z)
      = (ζ * (1 - star ζ * z + 2 * (star ζ * z))) / (ζ * (1 - star ζ * z)) :=
          (mul_div_mul_left _ _ hζ_ne).symm
    _ = (ζ + z) / (ζ - z) := by rw [h_num_eq, h_den_eq]
}

/--
  §4 The Herglotz–Pommerenke logarithmic derivative of a starlike radial slit map
  `f(z) = z ∏_{j=1}^m (1 - conj(ζ_j) z)^{-σ_j}`:
  `z f'(z) / f(z) = ∑_{j=1}^m (σ_j / 2) * herglotzKernel (ζ_j) z`.
-/
noncomputable def pommerenkeLogDeriv {m : ℕ} (ζ : Fin m → ℂ) (σ : Fin m → ℝ) (z : ℂ) : ℂ :=
  ∑ j : Fin m, ((σ j / 2 : ℝ) : ℂ) * herglotzKernel (ζ j) z

/--
  Real part of `pommerenkeLogDeriv`:
  `Re(pommerenkeLogDeriv ζ σ z) = ∑_{j=1}^m (σ_j / 2) * Re(herglotzKernel (ζ_j) z)`.
-/
lemma pommerenkeLogDeriv_re {m : ℕ} (ζ : Fin m → ℂ) (σ : Fin m → ℝ) (z : ℂ) :
    (pommerenkeLogDeriv ζ σ z).re =
      ∑ j : Fin m, (σ j / 2) * (herglotzKernel (ζ j) z).re := by
{
  unfold pommerenkeLogDeriv
  rw [Complex.re_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [Complex.mul_re]
}

/--
  §4 Interior Starlikeness of the Pommerenke Slit Map (`∂(arg f)/∂θ > 0` on `𝔻`):
  If `m > 0`, every `ζ_j ∈ unitCircleSet`, and every channel exponent `σ_j > 0`,
  then for every `z ∈ unitDiskSet`, `0 < (pommerenkeLogDeriv ζ σ z).re`.
-/
theorem pommerenkeLogDeriv_re_pos_on_disk {m : ℕ} (hm : 0 < m)
    (ζ : Fin m → ℂ) (σ : Fin m → ℝ)
    (hζ : ∀ j, ζ j ∈ unitCircleSet)
    (hσ : ∀ j, 0 < σ j) :
    ∀ z ∈ unitDiskSet, 0 < (pommerenkeLogDeriv ζ σ z).re := by
{
  intro z hz
  rw [pommerenkeLogDeriv_re]
  haveI : Nonempty (Fin m) := Fin.pos_iff_nonempty.mp hm
  apply Finset.sum_pos
  · intro j _
    have h_herg := (III_11_herglotz_properties (hζ j)).2.1 z hz
    exact mul_pos (half_pos (hσ j)) h_herg
  · exact Finset.univ_nonempty
}

/--
  §4 Boundary Constant-Angle Slit Property (`∂(arg f)/∂θ = 0` on `∂𝔻`):
  If every `ζ_j ∈ unitCircleSet`, then for every boundary point `z ∈ unitCircleSet`,
  `(pommerenkeLogDeriv ζ σ z).re = 0`, so each boundary arc `(ζ_k, ζ_{k+1}) ⊂ ∂𝔻` maps
  to a radial slit of constant polar angle `θ_k`.
-/
theorem pommerenkeLogDeriv_re_zero_on_circle {m : ℕ}
    (ζ : Fin m → ℂ) (σ : Fin m → ℝ)
    (hζ : ∀ j, ζ j ∈ unitCircleSet) :
    ∀ z ∈ unitCircleSet, (pommerenkeLogDeriv ζ σ z).re = 0 := by
{
  intro z hz
  rw [pommerenkeLogDeriv_re]
  apply Finset.sum_eq_zero
  intro j _
  rw [(III_11_herglotz_properties (hζ j)).2.2 z hz, mul_zero]
}

/--
  §4 Equivalence between the Herglotz kernel representation `pommerenkeLogDeriv ζ σ z`
  and the product logarithmic derivative `1 + ∑_{j=1}^m σ_j conj(ζ_j) z / (1 - conj(ζ_j) z)`
  when `∑_{j=1}^m σ_j = 2`.
-/
theorem pommerenkeLogDeriv_eq_product_logDeriv {m : ℕ}
    (ζ : Fin m → ℂ) (σ : Fin m → ℝ) (z : ℂ)
    (hζ : ∀ j, ζ j ∈ unitCircleSet)
    (hne : ∀ j, ζ j - z ≠ 0)
    (hsum : ∑ j : Fin m, σ j = 2) :
    pommerenkeLogDeriv ζ σ z =
      1 + ∑ j : Fin m, (σ j : ℂ) * (star (ζ j) * z) / (1 - star (ζ j) * z) := by
{
  unfold pommerenkeLogDeriv
  have h_term : ∀ j : Fin m,
      ((σ j / 2 : ℝ) : ℂ) * herglotzKernel (ζ j) z =
        ((σ j / 2 : ℝ) : ℂ) + (σ j : ℂ) * (star (ζ j) * z) / (1 - star (ζ j) * z) := by
  {
    intro j
    rw [← pommerenke_single_term_eq_herglotz (hζ j) (hne j)]
    push_cast
    ring
  }
  simp_rw [h_term, Finset.sum_add_distrib]
  congr 1
  have h_half_sum : ∑ j : Fin m, ((σ j / 2 : ℝ) : ℂ) = (((∑ j : Fin m, σ j) / 2 : ℝ) : ℂ) := by
  {
    rw [Finset.sum_div]
    push_cast
    rfl
  }
  rw [h_half_sum, hsum]
  norm_num
}

/--
  §4 `herglotzKernel ζ` is the linear-fractional transformation `linFracTrans 1 ζ (-1) ζ`.
-/
lemma herglotzKernel_eq_linFracTrans (ζ : ℂ) :
    herglotzKernel ζ = linFracTrans 1 ζ (-1) ζ := by
{
  ext z
  unfold herglotzKernel linFracTrans
  ring
}

/--
  §4 For `ζ ∈ unitCircleSet` and `z ∈ unitDiskSet`, `ζ - z ≠ 0`.
-/
lemma unitCircle_sub_unitDisk_ne_zero {ζ z : ℂ}
    (hζ : ζ ∈ unitCircleSet) (hz : z ∈ unitDiskSet) :
    ζ - z ≠ 0 := by
{
  simp only [unitCircleSet, unitDiskSet, Set.mem_setOf_eq] at hζ hz
  intro h_sub
  have h_eq : ζ = z := sub_eq_zero.mp h_sub
  rw [← h_eq, hζ] at hz
  exact lt_irrefl 1 hz
}

/--
  §4 Weierstrass `HasDerivAt_eps` derivative of `herglotzKernel ζ`:
  at any `z₀` with `ζ - z₀ ≠ 0`, `d/dz ((ζ + z) / (ζ - z)) = 2 * ζ / (ζ - z₀) ^ 2`.
-/
theorem herglotzKernel_hasDerivAt_eps {ζ z₀ : ℂ} (hne : ζ - z₀ ≠ 0) :
    HasDerivAt_eps (herglotzKernel ζ) (2 * ζ / (ζ - z₀) ^ 2) z₀ := by
{
  have h_den : (-1 : ℂ) * z₀ + ζ ≠ 0 := by
  {
    intro h0
    apply hne
    linear_combination h0
  }
  have h_lft := linFracTrans_hasDerivAt_eps 1 ζ (-1) ζ z₀ h_den
  rw [← herglotzKernel_eq_linFracTrans ζ] at h_lft
  have h_val : ((1 : ℂ) * ζ - ζ * (-1)) / ((-1 : ℂ) * z₀ + ζ) ^ 2 = 2 * ζ / (ζ - z₀) ^ 2 := by
  {
    have h_sq : ((-1 : ℂ) * z₀ + ζ) ^ 2 = (ζ - z₀) ^ 2 := by ring
    have h_num : (1 : ℂ) * ζ - ζ * (-1) = 2 * ζ := by ring
    rw [h_sq, h_num]
  }
  rwa [h_val] at h_lft
}

/--
  §4 For every `ζ ∈ unitCircleSet`, `herglotzKernel ζ` is holomorphic on `unitDiskSet`
  in the Weierstrass `_eps` sense (`HolomorphicOn_eps (herglotzKernel ζ) unitDiskSet`).
-/
theorem herglotzKernel_holomorphicOn_eps {ζ : ℂ} (hζ : ζ ∈ unitCircleSet) :
    HolomorphicOn_eps (herglotzKernel ζ) unitDiskSet := by
{
  intro z hz
  exact ⟨2 * ζ / (ζ - z) ^ 2,
    herglotzKernel_hasDerivAt_eps (unitCircle_sub_unitDisk_ne_zero hζ hz)⟩
}

/--
  §4 Weierstrass `HasDerivAt_eps` derivative of `pommerenkeLogDeriv ζ σ` on `unitDiskSet`.
-/
theorem pommerenkeLogDeriv_hasDerivAt_eps {m : ℕ}
    (ζ : Fin m → ℂ) (σ : Fin m → ℝ)
    (hζ : ∀ j, ζ j ∈ unitCircleSet)
    {z₀ : ℂ} (hz₀ : z₀ ∈ unitDiskSet) :
    HasDerivAt_eps (pommerenkeLogDeriv ζ σ)
      (∑ j : Fin m, ((σ j / 2 : ℝ) : ℂ) * (2 * ζ j / (ζ j - z₀) ^ 2)) z₀ := by
{
  rw [← hasDerivAt_iff_eps]
  have h_sum := HasDerivAt.sum (u := Finset.univ)
    (A := fun (j : Fin m) (z : ℂ) => ((σ j / 2 : ℝ) : ℂ) * herglotzKernel (ζ j) z)
    (A' := fun (j : Fin m) => ((σ j / 2 : ℝ) : ℂ) * (2 * ζ j / (ζ j - z₀) ^ 2))
    (x := z₀) (fun j _ => by {
      have h_j := (hasDerivAt_iff_eps _ _ z₀).mpr
        (herglotzKernel_hasDerivAt_eps (unitCircle_sub_unitDisk_ne_zero (hζ j) hz₀))
      exact h_j.const_mul ((σ j / 2 : ℝ) : ℂ)
    })
  have h_fn : pommerenkeLogDeriv ζ σ =
      ∑ j ∈ Finset.univ, fun z : ℂ => ((σ j / 2 : ℝ) : ℂ) * herglotzKernel (ζ j) z := by
  {
    ext z
    simp [pommerenkeLogDeriv, Finset.sum_apply]
  }
  rw [h_fn]
  exact h_sum
}

/--
  §4 For `∀ j, ζ j ∈ unitCircleSet`, the Herglotz–Pommerenke logarithmic derivative
  `pommerenkeLogDeriv ζ σ` is holomorphic on `unitDiskSet` (`HolomorphicOn_eps`).
-/
theorem pommerenkeLogDeriv_holomorphicOn_eps {m : ℕ}
    (ζ : Fin m → ℂ) (σ : Fin m → ℝ)
    (hζ : ∀ j, ζ j ∈ unitCircleSet) :
    HolomorphicOn_eps (pommerenkeLogDeriv ζ σ) unitDiskSet := by
{
  intro z hz
  exact ⟨_, pommerenkeLogDeriv_hasDerivAt_eps ζ σ hζ hz⟩
}

/--
  §4 Squared chordal distance on the unit circle in terms of polar angles `φ` and `t`:
  `‖polarPoint 1 φ - polarPoint 1 t‖ ^ 2 = 2 * (1 - Real.cos (t - φ))`.
-/
theorem polarPoint_unitCircle_dist_sq (φ t : ℝ) :
    ‖polarPoint 1 φ - polarPoint 1 t‖ ^ 2 = 2 * (1 - Real.cos (t - φ)) := by
{
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp only [Complex.sub_re, Complex.sub_im, polarPoint_re, polarPoint_im, one_mul]
  have h_cos := Real.cos_sub t φ
  have h_φ := Real.cos_sq_add_sin_sq φ
  have h_t := Real.cos_sq_add_sin_sq t
  linear_combination h_φ + h_t + 2 * h_cos
}

/--
  §4 Boundary Cotangent Formula for the Herglotz Kernel on `∂𝔻`:
  For boundary points `ζ = polarPoint 1 φ` and `z = polarPoint 1 t` on `∂𝔻`,
  `Im(herglotzKernel (polarPoint 1 φ) (polarPoint 1 t)) = sin(t - φ) / (1 - cos(t - φ))`.
-/
theorem herglotzKernel_unitCircle_im (φ t : ℝ) :
    (herglotzKernel (polarPoint 1 φ) (polarPoint 1 t)).im =
      Real.sin (t - φ) / (1 - Real.cos (t - φ)) := by
{
  unfold herglotzKernel
  rw [Complex.div_im, ← Complex.sq_norm, polarPoint_unitCircle_dist_sq φ t]
  simp only [Complex.add_re, Complex.add_im, Complex.sub_re, Complex.sub_im,
    polarPoint_re, polarPoint_im, one_mul]
  have h_num :
      (Real.sin φ + Real.sin t) * (Real.cos φ - Real.cos t) -
        (Real.cos φ + Real.cos t) * (Real.sin φ - Real.sin t) =
      2 * Real.sin (t - φ) := by
  {
    have h_sin := Real.sin_sub t φ
    linear_combination -2 * h_sin
  }
  rw [← sub_div, h_num, mul_div_mul_left _ _ (by norm_num : (2 : ℝ) ≠ 0)]
}

/--
  §4 Imaginary part of `pommerenkeLogDeriv` on `∂𝔻`:
  At `z = polarPoint 1 t ∈ ∂𝔻` with `ζ_j = polarPoint 1 (φ j)`,
  `Im(pommerenkeLogDeriv ζ σ (polarPoint 1 t)) = ∑ j, (σ_j / 2) * sin(t - φ_j) / (1 - cos(t - φ_j))`.
-/
lemma pommerenkeLogDeriv_unitCircle_im {m : ℕ}
    (φ σ : Fin m → ℝ) (t : ℝ) :
    (pommerenkeLogDeriv (fun j => polarPoint 1 (φ j)) σ (polarPoint 1 t)).im =
      ∑ j : Fin m, (σ j / 2) * (Real.sin (t - φ j) / (1 - Real.cos (t - φ j))) := by
{
  unfold pommerenkeLogDeriv
  rw [Complex.im_sum]
  apply Finset.sum_congr rfl
  intro j _
  rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero,
    herglotzKernel_unitCircle_im]
}

/--
  §4 Boundary Slit-Tip Formula for `pommerenkeLogDeriv` on `∂𝔻`:
  At `z = polarPoint 1 t ∈ ∂𝔻` with `ζ_j = polarPoint 1 (φ j)`, the logarithmic derivative
  `pommerenkeLogDeriv ζ σ (polarPoint 1 t)` is purely imaginary and given by
  `I * ∑ j, (σ_j / 2) * sin(t - φ_j) / (1 - cos(t - φ_j))`.
-/
theorem pommerenkeLogDeriv_unitCircle_eq {m : ℕ}
    (φ σ : Fin m → ℝ) (t : ℝ) :
    pommerenkeLogDeriv (fun j => polarPoint 1 (φ j)) σ (polarPoint 1 t) =
      ((∑ j : Fin m, (σ j / 2) * (Real.sin (t - φ j) / (1 - Real.cos (t - φ j))) : ℝ) : ℂ) * I := by
{
  have h_re := pommerenkeLogDeriv_re_zero_on_circle
    (fun j => polarPoint 1 (φ j)) σ (fun j => polarPoint_one_mem_unitCircleSet (φ j))
    (polarPoint 1 t) (polarPoint_one_mem_unitCircleSet t)
  apply Complex.ext
  · rw [h_re]
    simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
  · rw [pommerenkeLogDeriv_unitCircle_im]
    simp only [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    ring
}

/--
  §4 Half-angle identities for `1 - cos α` and `sin α`:
  `1 - cos α = 2 * sin(α / 2) ^ 2` and `sin α = 2 * sin(α / 2) * cos(α / 2)`.
-/
lemma one_sub_cos_and_sin_halfAngle (α : ℝ) :
    1 - Real.cos α = 2 * Real.sin (α / 2) ^ 2 ∧
    Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
{
  have h2 : α = 2 * (α / 2) := by ring
  have h_cos : Real.cos α = Real.cos (α / 2) ^ 2 - Real.sin (α / 2) ^ 2 := by
  {
    conv_lhs => rw [h2]
    exact Real.cos_two_mul' (α / 2)
  }
  have h_sin : Real.sin α = 2 * Real.sin (α / 2) * Real.cos (α / 2) := by
  {
    conv_lhs => rw [h2]
    exact Real.sin_two_mul (α / 2)
  }
  have h_pyth := Real.cos_sq_add_sin_sq (α / 2)
  constructor
  · linear_combination -h_cos - h_pyth
  · exact h_sin
}

/--
  §4 Positive Half-Angle Polar Factorization of `1 - e^{i α}` (`0 < α < 2π`):
  `1 - polarPoint 1 α = polarPoint (2 * sin(α / 2)) ((α - π) / 2)`.
  When `t > φ_j` on `(0, 2π)`, `2 * sin((t - φ_j) / 2) > 0`, so the polar angle of
  `1 - e^{i(t - φ_j)}` is `(t - φ_j - π) / 2`.
-/
theorem one_sub_polarPoint_eq_pos_halfAngle (α : ℝ) :
    1 - polarPoint 1 α = polarPoint (2 * Real.sin (α / 2)) ((α - Real.pi) / 2) := by
{
  rcases one_sub_cos_and_sin_halfAngle α with ⟨h_cos_half, h_sin_half⟩
  have h_ang : (α - Real.pi) / 2 = α / 2 - Real.pi / 2 := by ring
  have h_c : Real.cos ((α - Real.pi) / 2) = Real.sin (α / 2) := by
  {
    rw [h_ang, Real.cos_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  }
  have h_s : Real.sin ((α - Real.pi) / 2) = -Real.cos (α / 2) := by
  {
    rw [h_ang, Real.sin_sub, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  }
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, polarPoint_re, one_mul, h_c]
    linear_combination h_cos_half
  · simp only [Complex.sub_im, Complex.one_im, polarPoint_im, one_mul, h_s]
    linear_combination -h_sin_half
}

/--
  §4 Negative Half-Angle Polar Factorization of `1 - e^{i α}` (`-2π < α < 0`):
  `1 - polarPoint 1 α = polarPoint (-2 * sin(α / 2)) ((α + π) / 2)`.
  When `t < φ_j` on `(0, 2π)`, `-2 * sin((t - φ_j) / 2) > 0`, so the polar angle of
  `1 - e^{i(t - φ_j)}` is `(t - φ_j + π) / 2`.
-/
theorem one_sub_polarPoint_eq_neg_halfAngle (α : ℝ) :
    1 - polarPoint 1 α = polarPoint (-2 * Real.sin (α / 2)) ((α + Real.pi) / 2) := by
{
  rcases one_sub_cos_and_sin_halfAngle α with ⟨h_cos_half, h_sin_half⟩
  have h_ang : (α + Real.pi) / 2 = α / 2 + Real.pi / 2 := by ring
  have h_c : Real.cos ((α + Real.pi) / 2) = -Real.sin (α / 2) := by
  {
    rw [h_ang, Real.cos_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  }
  have h_s : Real.sin ((α + Real.pi) / 2) = Real.cos (α / 2) := by
  {
    rw [h_ang, Real.sin_add, Real.cos_pi_div_two, Real.sin_pi_div_two]
    ring
  }
  apply Complex.ext
  · simp only [Complex.sub_re, Complex.one_re, polarPoint_re, one_mul, h_c]
    linear_combination h_cos_half
  · simp only [Complex.sub_im, Complex.one_im, polarPoint_im, one_mul, h_s]
    linear_combination -h_sin_half
}

/--
  §4 Boundary phase contribution of the `j`-th Pommerenke factor `(1 - e^{-i φ_j} e^{i t})^{-σ_j}`:
  - Before the pole (`t < φ_j`, `beforePole = true`): `-σ_j * (t - φ_j + π) / 2`,
  - After the pole (`t > φ_j`, `beforePole = false`): `-σ_j * (t - φ_j - π) / 2`.
-/
noncomputable def pommerenkeFactorPhase (φ_j σ_j t : ℝ) (beforePole : Bool) : ℝ :=
  -σ_j * ((t - φ_j + (if beforePole then Real.pi else -Real.pi)) / 2)

/--
  §4 Total boundary phase `arg f(e^{i t})` of `f(z) = z ∏_{j=0}^{m-1} (1 - e^{-i φ_j} z)^{-σ_j}`
  on the `k`-th boundary arc `(φ_{k-1}, φ_k)` (where `t > φ_j` for `j < k` and `t < φ_j` for `j ≥ k`).
-/
noncomputable def pommerenkeArcPhase (m k : ℕ) (φ σ : ℕ → ℝ) (t : ℝ) : ℝ :=
  t + ∑ j ∈ Finset.range m, pommerenkeFactorPhase (φ j) (σ j) t (decide (k ≤ j))

/--
  §4 The constant slit angle `θ_k` on the `k`-th boundary arc of the Pommerenke slit map:
  `θ_k = ∑_{j=0}^{m-1} σ_j (φ_j ∓ π) / 2`.
-/
noncomputable def pommerenkeSlitAngle (m k : ℕ) (φ σ : ℕ → ℝ) : ℝ :=
  pommerenkeArcPhase m k φ σ 0

/--
  §4 **Constancy of the Boundary Argument on Each Open Arc (`arg f(e^{i t}) = θ_k`):**
  When the Pommerenke exponents satisfy the starlike normalization `∑_{j=0}^{m-1} σ_j = 2`,
  the linear `t`-terms in `pommerenkeArcPhase m k φ σ t` cancel identically (`t - (∑ σ_j / 2) t = 0`),
  so `pommerenkeArcPhase m k φ σ t = pommerenkeSlitAngle m k φ σ` for all `t ∈ ℝ`.
-/
theorem pommerenkeArcPhase_eq_slitAngle (m k : ℕ) (φ σ : ℕ → ℝ)
    (h_sum : ∑ j ∈ Finset.range m, σ j = 2) (t : ℝ) :
    pommerenkeArcPhase m k φ σ t = pommerenkeSlitAngle m k φ σ := by
{
  unfold pommerenkeSlitAngle pommerenkeArcPhase pommerenkeFactorPhase
  have h_split :
      ∑ j ∈ Finset.range m,
        -σ j * ((t - φ j + (if decide (k ≤ j) then Real.pi else -Real.pi)) / 2) =
      -(t / 2) * (∑ j ∈ Finset.range m, σ j) +
      ∑ j ∈ Finset.range m,
        -σ j * ((0 - φ j + (if decide (k ≤ j) then Real.pi else -Real.pi)) / 2) := by
  {
    rw [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro j _
    ring
  }
  rw [h_split, h_sum]
  ring
}

/--
  §4 Single-factor phase jump across the `k`-th pole `φ_k`:
  For `j = k`, `decide (k + 1 ≤ k) = false` and `decide (k ≤ k) = true`, so the factor phase jumps
  by `σ_k * π`; for `j ≠ k`, `decide (k + 1 ≤ j) = decide (k ≤ j)`, so the difference vanishes.
-/
lemma pommerenkeFactorPhase_jump (k j : ℕ) (φ_j σ_j t : ℝ) :
    pommerenkeFactorPhase φ_j σ_j t (decide (k + 1 ≤ j)) -
      pommerenkeFactorPhase φ_j σ_j t (decide (k ≤ j)) =
    if j = k then σ_j * Real.pi else 0 := by
{
  by_cases hjk : j = k
  · subst hjk
    have h1 : decide (j + 1 ≤ j) = false := decide_eq_false (Nat.not_succ_le_self j)
    have h2 : decide (j ≤ j) = true := decide_eq_true ( le_rfl )
    unfold pommerenkeFactorPhase
    rw [if_pos rfl, h1, h2]
    simp only [ Bool.false_eq_true, ↓reduceIte]
    ring
  · rw [if_neg hjk]
    have h_eq : decide (k + 1 ≤ j) = decide (k ≤ j) := by
    {
      by_cases hle : k ≤ j
      · have hlt : k < j := lt_of_le_of_ne hle (Ne.symm hjk)
        rw [decide_eq_true (Nat.succ_le_of_lt hlt), decide_eq_true hle]
      · have hnot : ¬ (k + 1 ≤ j) := fun h => hle (Nat.le_of_succ_le h)
        rw [decide_eq_false hnot, decide_eq_false hle]
    }
    rw [h_eq, sub_self]
}

/--
  §4 **Derivation of the Channel Opening Angle Formula `θ_{k+1} - θ_k = σ_k π`:**
  For every `k < m`, crossing the pole `z_k = e^{i φ_k}` increases the Pommerenke slit angle
  `pommerenkeSlitAngle m k φ σ` by `σ_k * π`.
-/
theorem pommerenkeSlitAngle_succ_sub_eq_sigma_mul_pi (m k : ℕ) (φ σ : ℕ → ℝ) (hk : k < m) :
    pommerenkeSlitAngle m (k + 1) φ σ - pommerenkeSlitAngle m k φ σ =
      σ k * Real.pi := by
{
  unfold pommerenkeSlitAngle pommerenkeArcPhase
  rw [ zero_add, zero_add, ← Finset.sum_sub_distrib]
  have h_congr :
      ∑ j ∈ Finset.range m,
        (pommerenkeFactorPhase (φ j) (σ j) 0 (decide (k + 1 ≤ j)) -
         pommerenkeFactorPhase (φ j) (σ j) 0 (decide (k ≤ j))) =
      ∑ j ∈ Finset.range m, (if j = k then σ j * Real.pi else 0) := by
  {
    apply Finset.sum_congr rfl
    intro j _
    exact pommerenkeFactorPhase_jump k j (φ j) (σ j) 0
  }
  rw [h_congr, Finset.sum_ite_eq', if_pos (Finset.mem_range.mpr hk)]
}

/--
  §4 **Derived Equivalence of Monotone Channel Opening Angles and Monotone `σ_k`:**
  Directly from `pommerenkeSlitAngle_succ_sub_eq_sigma_mul_pi` (without assuming `Δθ_k = σ_k π`
  as an external axiom), for any `k + 1 < m`,
  `θ_{k+1} - θ_k ≤ θ_{k+2} - θ_{k+1} ↔ σ_k ≤ σ_{k+1}`.
-/
theorem pommerenkeSlitAngle_diff_monotone_iff_sigma_monotone
    (m k : ℕ) (φ σ : ℕ → ℝ) (hk : k + 1 < m) :
    pommerenkeSlitAngle m (k + 1) φ σ - pommerenkeSlitAngle m k φ σ ≤
      pommerenkeSlitAngle m (k + 2) φ σ - pommerenkeSlitAngle m (k + 1) φ σ ↔
      σ k ≤ σ (k + 1) := by
{
  have hk0 : k < m := Nat.lt_of_succ_lt hk
  rw [pommerenkeSlitAngle_succ_sub_eq_sigma_mul_pi m k φ σ hk0,
    pommerenkeSlitAngle_succ_sub_eq_sigma_mul_pi m (k + 1) φ σ hk]
  exact mul_le_mul_iff_of_pos_right Real.pi_pos
}


end ConformalDiskGeometry
