/-
  Brennan's Conjecture via Composition Operators (Wayne Smith 2006 & Valentin Matache–Wayne Smith 2012)
  Formalized in Lean 4 on top of our 0-axiom proof of Brennan's Conjecture (`brennan/Section6_7.lean`).
-/
import brennan.Section6_7

noncomputable section

open Complex MeasureTheory Set Filter Metric
open scoped Real ENNReal Topology

namespace Brennan.CompositionOperators

open Brennan.Section2
open Brennan.Section2_Dyadic
open Brennan.Sections6and7

/-!
  ## 1. Composition Operators and Contravariant Functoriality

  Given an analytic symbol `φ : ℂ → ℂ`, the composition operator `C_φ` acts on functions `f : ℂ → ℂ`
  by pullback: `(C_φ f)(z) = f(φ(z))`.
-/

/-- The composition operator `C_φ(f) = f ∘ φ` induced by a symbol `φ : ℂ → ℂ`. -/
def compOp (φ : ℂ → ℂ) (f : ℂ → ℂ) : ℂ → ℂ :=
  fun z => f (φ z)

/-- The identity symbol induces the identity composition operator `C_id = id`. -/
lemma compOp_id (f : ℂ → ℂ) :
    compOp id f = f := by
{
  rfl
}

/-- Contravariant functoriality of composition operators: `C_{ψ ∘ φ} = C_φ ∘ C_ψ`. -/
lemma compOp_comp (ψ φ : ℂ → ℂ) (f : ℂ → ℂ) :
    compOp (ψ ∘ φ) f = compOp φ (compOp ψ f) := by
{
  rfl
}

/-- Chain rule for the composition operator `C_φ f` at a point `z`. -/
lemma hasDerivAt_compOp {φ f : ℂ → ℂ} {z φ' f' : ℂ}
    (hf : HasDerivAt f f' (φ z)) (hφ : HasDerivAt φ φ' z) :
    HasDerivAt (compOp φ f) (f' * φ') z := by
{
  exact hf.comp z hφ
}

/-!
  ## 2. Wayne Smith's (2006) Derivative Cocycle Weight `Q_φ` and Weighted Composition Operators

  In Wayne Smith, *"Brennan's conjecture for weighted composition operators"* (Contemp. Math. 393, 2006),
  given a conformal map `τ : 𝔻 → G` and an analytic self-map `φ : 𝔻 → 𝔻`, the derivative ratio
    `Q_φ(z) = τ'(φ(z)) / τ'(z)`
  drives the weighted composition operator `(A_{φ, p} f)(z) = Q_φ(z)^p f(φ(z))` on `L²_a(𝔻)`.
-/

/--
  Wayne Smith's (2006) derivative ratio weight `Q_φ(z) = τ'(φ(z)) / τ'(z)` associated with
  a conformal map `τ : ℂ → ℂ` and an inducing symbol `φ : ℂ → ℂ`.
-/
def smithWeight (τ φ : ℂ → ℂ) (z : ℂ) : ℂ :=
  deriv τ (φ z) / deriv τ z

/--
  Modulus of Wayne Smith's weighted composition operator `|(A_{φ, p} f)(z)| = |Q_φ(z)|^p |f(φ(z))|`.
-/
def smithWeightedModulus (τ φ : ℂ → ℂ) (p : ℝ) (f : ℂ → ℂ) (z : ℂ) : ℝ :=
  (‖smithWeight τ φ z‖ ^ p) * ‖compOp φ f z‖

/-- For the identity symbol `φ = id`, Wayne Smith's weight `Q_id(z)` equals `1` wherever `τ'(z) ≠ 0`. -/
lemma smithWeight_id {τ : ℂ → ℂ} {z : ℂ} (hτ : deriv τ z ≠ 0) :
    smithWeight τ id z = 1 := by
{
  unfold smithWeight
  exact div_self hτ
}

/--
  **Wayne Smith's Multiplicative Cocycle Law**:
  For composable symbols `ψ` and `φ`, `Q_{ψ ∘ φ}(z) = Q_ψ(φ(z)) * Q_φ(z)` whenever `τ'(φ(z)) ≠ 0`.
  This cocycle identity explains why iterating or flowing along a semigroup of composition operators
  telescopes the derivative weights `τ'(φ_t(z)) / τ'(z)`.
-/
lemma smithWeight_comp (τ ψ φ : ℂ → ℂ) (z : ℂ) (hmid : deriv τ (φ z) ≠ 0) :
    smithWeight τ (ψ ∘ φ) z = smithWeight τ ψ (φ z) * smithWeight τ φ z := by
{
  unfold smithWeight
  simp only [Function.comp_apply]
  exact (div_mul_div_cancel₀ hmid).symm
}

/--
  **Loewner Semigroup Cocycle Identity**:
  When `F_s = F_t ∘ φ_{s, t}` is a Loewner chain factored through a transition self-map `φ_{s, t}`,
  the ratio `F_t'(φ_{s, t}(z)) / F_s'(z)` equals `(φ_{s, t}'(z))⁻¹`.
-/
lemma loewner_transition_cocycle {F_s F_t φ : ℂ → ℂ} {z F_t' φ' : ℂ}
    (h_chain : F_s = compOp φ F_t)
    (hFt : HasDerivAt F_t F_t' (φ z))
    (hφ : HasDerivAt φ φ' z)
    (hFt_ne : F_t' ≠ 0) :
    F_t' / deriv F_s z = φ'⁻¹ := by
{
  have hFs : HasDerivAt F_s (F_t' * φ') z := by
  {
    rw [h_chain]
    exact hasDerivAt_compOp hFt hφ
  }
  rw [hFs.deriv]
  have h_cancel := mul_div_mul_left (1 : ℂ) φ' hFt_ne
  rwa [mul_one, one_div] at h_cancel
}

/-!
  ## 3. Wayne Smith's (2006) Equivalence and Resolution via Brennan's Conjecture

  When the symbol `φ(z) = z₀ ∈ 𝔻` is constant (a rank-1 compact self-map of `𝔻`),
  `|Q_{z₀}(z)|^(2p) = |τ'(z₀)|^(2p) * |τ'(z)|^(-2p)`.
  Thus `A_{z₀, p}(1) ∈ L²(𝔻)` if and only if `∫_𝔻 |τ'(z)|^(-2p) dA(z) < ∞`.
-/

/--
  For a constant symbol `φ(z) = z₀`, the squared modulus `|A_{z₀, p}(1)(z)|²` of Wayne Smith's
  weighted composition operator on the constant function `1` is `|τ'(z₀)|^(2p) * |τ'(z)|^(-2p)`.
-/
lemma smithWeightedModulus_sq_const (τ : ℂ → ℂ) (z₀ : ℂ) (p : ℝ) (z : ℂ) :
    (smithWeightedModulus τ (fun _ => z₀) p (fun _ => 1) z) ^ (2 : ℝ) =
      (‖deriv τ z₀‖ ^ (2 * p)) * (‖deriv τ z‖ ^ (-2 * p)) := by
{
  unfold smithWeightedModulus smithWeight compOp
  simp only [norm_one, mul_one, norm_div]
  rw [← Real.rpow_mul (div_nonneg (norm_nonneg _) (norm_nonneg _))]
  rw [Real.div_rpow (norm_nonneg _) (norm_nonneg _)]
  rw [div_eq_mul_inv, ← Real.rpow_neg (norm_nonneg _)]
  ring_nf
}

/--
  **Wayne Smith's (2006) Constant-Symbol Equivalence**:
  For any univalent map `τ : 𝔻 → G`, `z₀ ∈ 𝔻`, and `p ∈ ℝ`, the squared Smith weight
  `|Q_{z₀}(z)|^(2p)` is area-integrable on `𝔻` if and only if `|τ'(z)|^(-2p)` is area-integrable on `𝔻`.
-/
theorem smith_constant_symbol_integrable_iff {τ : ℂ → ℂ} (hτ : UnivalentOn τ disk)
    {z₀ : ℂ} (hz₀ : z₀ ∈ disk) (p : ℝ) :
    IntegrableOn (fun z => (smithWeightedModulus τ (fun _ => z₀) p (fun _ => 1) z) ^ (2 : ℝ)) disk ↔
      IntegrableOn (fun z => ‖deriv τ z‖ ^ (-2 * p)) disk := by
{
  simp_rw [smithWeightedModulus_sq_const]
  have h_pos : 0 < ‖deriv τ z₀‖ :=
    norm_pos_iff.mpr (deriv_ne_zero_of_univalentOn Metric.isOpen_ball hτ hz₀)
  have hc_ne : ‖deriv τ z₀‖ ^ (2 * p) ≠ 0 := (Real.rpow_pos_of_pos h_pos (2 * p)).ne'
  constructor
  · intro h
    have h_inv : IntegrableOn
        (fun z => (‖deriv τ z₀‖ ^ (2 * p))⁻¹ * (‖deriv τ z₀‖ ^ (2 * p) * ‖deriv τ z‖ ^ (-2 * p))) disk :=
      h.const_mul ((‖deriv τ z₀‖ ^ (2 * p))⁻¹)
    refine IntegrableOn.congr_fun h_inv (fun z _ => ?_) Metric.isOpen_ball.measurableSet
    rw [← mul_assoc, inv_mul_cancel₀ hc_ne, one_mul]
  · intro h
    exact h.const_mul (‖deriv τ z₀‖ ^ (2 * p))
}

/--
  **Resolution of Wayne Smith's (2006) Weighted Composition Operator Conjecture**:
  For every univalent map `τ : 𝔻 → G`, every `z₀ ∈ 𝔻`, and every exponent `p ∈ (-1/3, 1)`,
  both the Brennan-Bergman integral `∫_𝔻 |τ'(z)|^(-2p) dA(z)` and Wayne Smith's weighted
  composition norm `∫_𝔻 |A_{z₀, p}(1)(z)|² dA(z)` are finite.
-/
theorem smith_2006_brennan_resolved {τ : ℂ → ℂ} (hτ : UnivalentOn τ disk)
    {z₀ : ℂ} (hz₀ : z₀ ∈ disk) {p : ℝ} (hp_low : -1 / 3 < p) (hp_high : p < 1) :
    IntegrableOn (fun z => ‖deriv τ z‖ ^ (-2 * p)) disk ∧
    IntegrableOn (fun z => (smithWeightedModulus τ (fun _ => z₀) p (fun _ => 1) z) ^ (2 : ℝ)) disk := by
{
  have h_brennan : IntegrableOn (fun z => ‖deriv τ z‖ ^ (-2 * p)) disk :=
    univalent_disk_area main_theorem_inverse_square hτ (by linarith) (by linarith)
  exact ⟨h_brennan, (smith_constant_symbol_integrable_iff hτ hz₀ p).mpr h_brennan⟩
}

/-!
  ## 4. Valentin Matache & Wayne Smith (2012): Spaces `L²_a(G, μ_p)` and Pullback Equivalence

  In Valentin Matache & Wayne Smith, *"Composition Operators on a Class of Analytic Function Spaces
  Related to Brennan's Conjecture"* (Complex Anal. Oper. Theory 6, 2012, 139–173), for a conformal
  map `g : G → 𝔻` (with inverse `τ = g⁻¹ : 𝔻 → G`), the measure `dμ_p(w) = |g'(w)|^(2 - 2p) dA(w)`
  defines the space `L²_a(G, μ_p)`. A constant composition operator `C_{w₀} f = f(w₀)` is bounded
  and compact on `L²_a(G, μ_p)` if and only if the constant function `1` belongs to `L²_a(G, μ_p)`,
  i.e., `∫_G |g'(w)|^(2 - 2p) dA(w) < ∞` for all `-1/3 < p < 1` (so `4/3 < 2 - 2p < 4` with `p ↦ -p`).
-/

/--
  **Resolution of the Matache–Smith (2012) `L²_a(G, μ_p)` Space Conjecture**:
  For every open simply connected domain `G ⊂ ℂ`, every conformal bijection `g : G → 𝔻`,
  and every Matache–Smith parameter `p ∈ (-1/3, 1)`, the weight `|g'(w)|^(2 + 2p)` (with exponent
  `q = 2 + 2p ∈ (4/3, 4)`) is area-integrable on `G`. Consequently, `1 ∈ L²_a(G, μ_p)` and every
  constant symbol `Φ(w) = w₀ ∈ G` induces a compact rank-1 composition operator `C_Φ` on `L²_a(G, μ_p)`.
-/
theorem matache_smith_2012_brennan_resolved {G : Set ℂ} (hG : IsOpen G)
    {g : ℂ → ℂ} (hg_diff : DifferentiableOn ℂ g G) (hg_bij : BijOn g G disk)
    {p : ℝ} (hp_low : -1 / 3 < p) (hp_high : p < 1) :
    IntegrableOn (fun w => ‖deriv g w‖ ^ (2 + 2 * p)) G := by
{
  exact conformal_domain_area main_theorem_inverse_square hG hg_diff hg_bij
    (by linarith) (by linarith)
}

end Brennan.CompositionOperators
