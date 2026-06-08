import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Complex.LogDeriv

open Complex Set MeasureTheory

/--
  Brennan's Conjecture (Statement):
  Let W be an open, simply connected proper subset of the complex plane ℂ.
  Let f : ℂ → ℂ be a conformal map (holomorphic and injective on W) 
  mapping W bijectively onto the open unit disk 𝔻 = Metric.ball 0 1.
  Then for any real p such that 4/3 < p < 4, the p-th power of the derivative
  magnitude |f'(z)|^p is integrable on W with respect to the Lebesgue measure.
-/
def BrennansConjectureStatement : Prop :=
  ∀ (W : Set ℂ) (f : ℂ → ℂ) (p : ℝ),
    IsOpen W →
    W.Nonempty →
    W ≠ univ →
    DifferentiableOn ℂ f W →
    InjOn f W →
    -- `f '' W` represents the image of set W under function f, i.e., {f(z) | z ∈ W}
    f '' W = Metric.ball (0 : ℂ) 1 →
    (4 / 3 < p ∧ p < 4) →
    IntegrableOn (fun z => ‖deriv f z‖ ^ p) W volume

/-- The Koebe slit function: K(z) = z / (1 - z)^2 -/
noncomputable def koebe (z : ℂ) : ℂ := z / (1 - z) ^ 2

/-- The Koebe slit domain W_Koebe = ℂ \ (-∞, -1/4] -/
def KoebeSlitDomain : Set ℂ := {z | z.re > -1/4 ∨ z.im ≠ 0}

/-- Define the principal complex square root -/
noncomputable def csqrt (z : ℂ) : ℂ := Complex.exp (Complex.log z / 2)

theorem csqrt_sq (z : ℂ) (hz : z ∈ slitPlane) : csqrt z ^ 2 = z := by {
  unfold csqrt
  rw [sq]
  rw [← Complex.exp_add]
  have h_add : Complex.log z / 2 + Complex.log z / 2 = Complex.log z := by ring
  rw [h_add]
  have hz_ne : z ≠ 0 := by {
    unfold slitPlane at hz
    intro h
    subst h
    simp at hz
  }
  exact Complex.exp_log hz_ne
}

theorem differentiableOn_csqrt : DifferentiableOn ℂ csqrt slitPlane := by {
  unfold csqrt
  apply DifferentiableOn.cexp
  apply DifferentiableOn.div_const
  apply DifferentiableOn.clog
  · exact differentiableOn_id
  · intro x hx
    exact hx
}

theorem koebe_domain_mapping (w : ℂ) (hw : w ∈ KoebeSlitDomain) : 4 * w + 1 ∈ slitPlane := by {
  unfold KoebeSlitDomain slitPlane at *
  rcases hw with h1 | h2
  · left
    simp only [add_re, mul_re, one_re] at *
    norm_num at *
    linarith
  · right
    simp only [add_im, mul_im, one_im] at *
    norm_num at *
    exact h2
}

/-- The inverse of the Koebe function, mapping the slit domain back to the unit disk -/
noncomputable def koebeInv (w : ℂ) : ℂ :=
  if w = 0 then 0
  else ((2 * w + 1) - csqrt (4 * w + 1)) / (2 * w)

theorem koebeInv_target_mapping (w : ℂ) (hw : w ∈ KoebeSlitDomain) : ‖koebeInv w‖ < 1 := by {
  sorry
}

theorem koebeInv_koebe (z : ℂ) (hz : ‖z‖ < 1) : koebeInv (koebe z) = z := by {
  sorry
}

theorem koebe_koebeInv (w : ℂ) (hw : w ∈ KoebeSlitDomain) : koebe (koebeInv w) = w := by {
  sorry
}

theorem differentiableOn_koebeInv : DifferentiableOn ℂ koebeInv KoebeSlitDomain := by {
  sorry
}

theorem deriv_koebeInv (w : ℂ) (hw : w ∈ KoebeSlitDomain) :
    deriv koebeInv w = (1 - koebeInv w) ^ 3 / (1 + koebeInv w) := by {
  sorry
}

theorem IntegrableOn_koebeInv_iff (p : ℝ) :
    IntegrableOn (fun z => ‖deriv koebeInv z‖ ^ p) KoebeSlitDomain volume ↔
    IntegrableOn (fun w => ‖deriv koebe w‖ ^ (2 - p)) (Metric.ball 0 1) volume := by {
  sorry
}

theorem cusp_divergence (p : ℝ) (hp : p ≥ 4) :
    ¬ IntegrableOn (fun w => ‖deriv koebe w‖ ^ (2 - p)) (Metric.ball 0 1) volume := by {
  sorry
}

theorem pole_divergence (p : ℝ) (hp : p ≤ 4 / 3) :
    ¬ IntegrableOn (fun w => ‖deriv koebe w‖ ^ (2 - p)) (Metric.ball 0 1) volume := by {
  sorry
}

/-- 
  The Koebe slit function is conformal from the unit disk to the slit domain, 
  and its inverse shows that the bounds 4/3 < p < 4 in Brennan's Conjecture are sharp.
  Specifically, if p ≥ 4 or p ≤ 4/3, the integral of |f'(z)|^p over the slit domain diverges.
-/
theorem KoebeSharpnessLimit (p : ℝ) (h : p ≥ 4 ∨ p ≤ 4/3) :
    ¬ IntegrableOn (fun z => ‖deriv koebeInv z‖ ^ p) KoebeSlitDomain volume := by {
  rw [IntegrableOn_koebeInv_iff]
  rcases h with hp | hp
  · exact cusp_divergence p hp
  · exact pole_divergence p hp
}
