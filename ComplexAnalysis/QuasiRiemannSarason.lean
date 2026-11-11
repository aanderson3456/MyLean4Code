/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.

  QuasiRiemannSarason.lean:
  Melds OpenAI's Quasi-Riemann Hypothesis formalization
  ("The Quasi-Riemann Hypothesis: A Zero-Free Half-Plane Re(s) > 7/8", OpenAI, 30 Sept 2026,
  `OAI/NumberTheory/DirichletL/`) onto Donald Sarason's Weierstrass `_eps` complex analysis
  foundation (`Sarason/Definitions.lean`, `Sarason/Chapter1.lean`, `Sarason/Chapter2.lean`,
  `Sarason/Chapter3.lean`) and the Prime Number Theorem modules (`Zeta.lean`, `Contour.lean`,
  `Newman.lean`).
-/
import Mathlib
import Sarason.Definitions
import Sarason.Chapter1
import Sarason.Chapter2
import Sarason.Chapter3
import Zeta
import Contour
import Newman

/-!
# The Quasi-Riemann Hypothesis ($\operatorname{Re}(s) > 7/8$) Melded onto Sarason's `_eps` Complex Analysis

This module bridges OpenAI's formalization of the Quasi-Riemann Hypothesis
(`OAI/NumberTheory/DirichletL/`) directly onto the Weierstrass $\varepsilon$-$\delta$ complex
analysis framework of Donald Sarason (`HolomorphicOn_eps`, `DifferentiableAt_eps`,
`HasDerivAt_eps`, `HasLimitAt_eps`, `deriv_eps`, `linFracTrans`) and the Riemann zeta / Euler
product / Newman contour modules (`Sarason.PNT`).

## Main Formalized Sections (`0` `sorry`s, `0` `omega`s)

1. **Section 1 — Sarason `_eps` Holomorphy Equivalence on Right Half-Planes & Cayley–Möbius Pullbacks**:
   - Defines `rightHalfPlane σ₀ = {s : ℂ | σ₀ < s.re}`, the Stage I half-plane $\Omega_{11/12}$,
     and the Stage II Quasi-Riemann half-plane $\Omega_{7/8}$.
   - Proves `isOpen_rightHalfPlane` (supplying the `v4.34` lemma `Complex.isOpen_re_gt`) and the
     Goursat–Weierstrass equivalence `holomorphicOn_eps_iff_analyticOnNhd` between
     `Sarason.HolomorphicOn_eps f U` and `AnalyticOnNhd ℂ f U` on any open set $U \subseteq \mathbb{C}$.
   - Constructs the shifted Cayley linear-fractional transformation (`halfPlaneToDiskLFT σ₀`)
     via `Sarason.Ch3.linFracTrans` mapping $\Omega_{\sigma_0} = \{\operatorname{Re}(s) > \sigma_0\}$
     conformally onto the unit disk $\mathbb{D}$.

2. **Section 2 — Continuation from a Common Signal (`Supremum.lean` & `Continuation.lean`, Prop. 2.1)**:
   - Formalizes the continuation margin $\varepsilon_* = \min(\beta_* - 7/8 - \omega, \sigma) > 0$,
     sentinel supremum exclusion `seven_eighths_of_uniform_margin_with_sentinel`,
     Mellin signal continuation `signalMellin_holomorphicOn_eps`, and the master
     `Sarason.HolomorphicOn_eps` common-signal nonvanishing theorem
     `nonzero_of_common_signal_eps`.

3. **Section 3 — Deleted Euler Factors & Logarithmic Control (`EulerFactors.lean` & `LogarithmicControl.lean`)**:
   - Formalizes individual Euler factors $1 - a N^{-s}$ and finite deleted products
     $\prod_{p \in S} (1 - a_p N_p^{-s})$, proving `HolomorphicOn_eps` and nonvanishing on
     $\operatorname{Re}(s) > 0$, plus holomorphic logarithms and Borel–Carathéodory bounds in
     Sarason `_eps` form.

4. **Section 4 — Zero Detector, Compensated Probe, and Stage II Parameters (`Detector.lean`, `Parameters.lean`)**:
   - Formalizes the buffered-bin pigeonhole detector (`exists_buffered_bin`), simultaneous
     saturation (`complex_simultaneous_saturation`), principal scalar normalization
     (`common_normalization_bounds`), marked geometric Euler resummation (`marked_table_resummation`),
     and the $7/8$ compensated exponent table (`compensated_geometry`).

5. **Section 5 — Eisenstein Coordinates, Two-Poisson Recursion, & Sextic Gauss Sums (`EisensteinCoordinates.lean`)**:
   - Formalizes the PID property of $\mathbb{Z}[\omega]$, Eisenstein norm multiplicativity,
     finite and complex $L^2$ row extraction, two-Poisson scale/budget/charge identities,
     and the finite-field sextic Gauss sum & cubic-theta Fourier row identities.

6. **Section 6 — Bridge to `Sarason.PNT` (`Zeta.lean`, `Newman.lean`) and Hecke-to-Dirichlet Transfer**:
   - Connects `Sarason.PNT.zeta_eps` and `Sarason.PNT.eulerProduct_eps` to `riemannZeta`,
     proves the quadratic norm-character factorization transfer from $\mathbb{Q}(\sqrt{-3})$
     Hecke $L$-functions to Dirichlet $L$-functions and $\zeta(s)$, and establishes the uniform
     $\sigma_0 = 7/8$ zero-free strip for the regularized reciprocal $(s - 1)/\zeta(s)$.
-/

noncomputable section

open Complex Filter TopologicalSpace Metric Bornology Set Asymptotics MeasureTheory
open scoped BigOperators Classical Topology
open MulChar AddChar
open Sarason Sarason.Ch1 Sarason.Ch2 Sarason.Ch3 Sarason.PNT

namespace Sarason.QuasiRiemann

/-!
## Section 1: Sarason `_eps` Holomorphy on Open Half-Planes and Möbius Pullbacks
-/

/-- The open right half-plane $\Omega_{\sigma_0} = \{s \in \mathbb{C} : \sigma_0 < \operatorname{Re}(s)\}$. -/
def rightHalfPlane (σ₀ : ℝ) : Set ℂ :=
  {s : ℂ | σ₀ < s.re}

/-- The Stage I zero-free half-plane $\Omega_{11/12} = \{s \in \mathbb{C} : 11/12 < \operatorname{Re}(s)\}$
(Theorem 3.1 of OpenAI's Quasi-Riemann paper). -/
def elevenTwelfthsHalfPlane : Set ℂ :=
  rightHalfPlane (11 / 12)

/-- The Stage II Quasi-Riemann zero-free half-plane $\Omega_{7/8} = \{s \in \mathbb{C} : 7/8 < \operatorname{Re}(s)\}$
(Theorem 1.1 of OpenAI's Quasi-Riemann paper). -/
def sevenEighthsHalfPlane : Set ℂ :=
  rightHalfPlane (7 / 8)

/-- Every open right half-plane $\{s \in \mathbb{C} : \sigma_0 < \operatorname{Re}(s)\}$ is open in $\mathbb{C}$
(providing the `v4.34` lemma `Complex.isOpen_re_gt`). -/
theorem isOpen_rightHalfPlane (σ₀ : ℝ) : IsOpen (rightHalfPlane σ₀) := by {
  exact isOpen_lt continuous_const Complex.continuous_re
}

/-- Every open right half-plane is convex. -/
theorem convex_rightHalfPlane (σ₀ : ℝ) : Convex ℝ (rightHalfPlane σ₀) := by {
  exact convex_halfSpace_re_gt σ₀
}

/-- Every open right half-plane is preconnected. -/
theorem isPreconnected_rightHalfPlane (σ₀ : ℝ) : IsPreconnected (rightHalfPlane σ₀) := by {
  exact (convex_rightHalfPlane σ₀).isPreconnected
}

/-- Monotonicity of right half-planes: if $\sigma_1 \le \sigma_2$, then $\Omega_{\sigma_2} \subseteq \Omega_{\sigma_1}$. -/
theorem rightHalfPlane_mono {σ₁ σ₂ : ℝ} (h : σ₁ ≤ σ₂) :
    rightHalfPlane σ₂ ⊆ rightHalfPlane σ₁ := by {
  intro s hs
  exact lt_of_le_of_lt h hs
}

/-- Strict nesting of the classical Euler half-plane $\Omega_1$, the Stage I half-plane $\Omega_{11/12}$,
and the Stage II Quasi-Riemann half-plane $\Omega_{7/8}$. -/
theorem halfPlane_chain_inclusions :
    rightHalfPlane 1 ⊆ elevenTwelfthsHalfPlane ∧
    elevenTwelfthsHalfPlane ⊆ sevenEighthsHalfPlane ∧
    sevenEighthsHalfPlane ⊆ rightHalfPlane (1 / 2) := by {
  refine ⟨rightHalfPlane_mono (by norm_num), ?_, ?_⟩
  · exact rightHalfPlane_mono (by norm_num)
  · exact rightHalfPlane_mono (by norm_num)
}

/-- Equivalence between Sarason's Weierstrass $\varepsilon$-$\delta$ predicate `HolomorphicOn_eps f U`
and Mathlib's `DifferentiableOn ℂ f U` on any open set $U \subseteq \mathbb{C}$. -/
theorem holomorphicOn_eps_iff_differentiableOn {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) :
    HolomorphicOn_eps f U ↔ DifferentiableOn ℂ f U := by {
  unfold HolomorphicOn_eps
  constructor
  · intro h z hz
    have hd : DifferentiableAt ℂ f z := (differentiableAt_iff_eps f z).mpr (h z hz)
    exact hd.differentiableWithinAt
  · intro h z hz
    have hd : DifferentiableAt ℂ f z := (h z hz).differentiableAt (hU.mem_nhds hz)
    exact (differentiableAt_iff_eps f z).mp hd
}

/-- Equivalence between Sarason's Weierstrass $\varepsilon$-$\delta$ predicate `HolomorphicOn_eps f U`
and `AnalyticOnNhd ℂ f U` on any open subset $U \subseteq \mathbb{C}$ (by Goursat's theorem). -/
theorem holomorphicOn_eps_iff_analyticOnNhd {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U) :
    HolomorphicOn_eps f U ↔ AnalyticOnNhd ℂ f U := by {
  rw [holomorphicOn_eps_iff_differentiableOn hU]
  exact (Complex.analyticOnNhd_iff_differentiableOn hU).symm
}

/-- Specialization of `holomorphicOn_eps_iff_analyticOnNhd` to any right half-plane $\Omega_{\sigma_0}$. -/
theorem holomorphicOn_eps_rightHalfPlane_iff (f : ℂ → ℂ) (σ₀ : ℝ) :
    HolomorphicOn_eps f (rightHalfPlane σ₀) ↔ AnalyticOnNhd ℂ f (rightHalfPlane σ₀) := by {
  exact holomorphicOn_eps_iff_analyticOnNhd (isOpen_rightHalfPlane σ₀)
}

/-- Predicate stating that $f$ is holomorphic (`HolomorphicOn_eps`) and zero-free on $G \subseteq \mathbb{C}$. -/
def IsZeroFreeOn_eps (f : ℂ → ℂ) (G : Set ℂ) : Prop :=
  HolomorphicOn_eps f G ∧ ∀ s ∈ G, f s ≠ 0

/-- If $f$ satisfies `IsZeroFreeOn_eps f U` on an open set $U$, then its reciprocal $s \mapsto (f s)⁻¹$
is holomorphic in Sarason's $\varepsilon$-$\delta$ sense (`HolomorphicOn_eps`) on $U$. -/
theorem holomorphicOn_eps_inv_of_isZeroFreeOn_eps {f : ℂ → ℂ} {U : Set ℂ}
    (h : IsZeroFreeOn_eps f U) :
    HolomorphicOn_eps (fun s => (f s)⁻¹) U := by {
  intro s hs
  have hdf : DifferentiableAt ℂ f s := (differentiableAt_iff_eps f s).mpr (h.1 s hs)
  have hd_inv : DifferentiableAt ℂ (fun z => (f z)⁻¹) s := hdf.inv (h.2 s hs)
  exact (differentiableAt_iff_eps (fun z => (f z)⁻¹) s).mp hd_inv
}

/-- Sarason `_eps` logarithmic derivative $\frac{f'(s)}{f(s)}$ extracted via `deriv_eps`. -/
noncomputable def logDeriv_eps (f : ℂ → ℂ) (s : ℂ) (hd : DifferentiableAt_eps f s) : ℂ :=
  deriv_eps f s hd / f s

/-- Shifted Cayley linear-fractional transformation (built from `Sarason.Ch3.linFracTrans`)
mapping the half-plane $\Omega_{\sigma_0} = \{\operatorname{Re}(s) > \sigma_0\}$ onto the unit disk $\mathbb{D}$:
$$\Phi_{\sigma_0}(s) = \frac{s - (\sigma_0 + 1)}{s - (\sigma_0 - 1)}.$$ -/
noncomputable def halfPlaneToDiskLFT (σ₀ : ℝ) (s : ℂ) : ℂ :=
  linFracTrans 1 (-((σ₀ + 1 : ℝ) : ℂ)) 1 ((1 - σ₀ : ℝ) : ℂ) s

/-- Algebraic expansion of `halfPlaneToDiskLFT`:
$|s + (1 - \sigma_0)|^2 - |s - (\sigma_0 + 1)|^2 = 4(\operatorname{Re}(s) - \sigma_0)$. -/
theorem halfPlaneToDiskLFT_normSq_diff (σ₀ : ℝ) (s : ℂ) :
    Complex.normSq (s + ((1 - σ₀ : ℝ) : ℂ)) - Complex.normSq (s - ((σ₀ + 1 : ℝ) : ℂ)) =
      4 * (s.re - σ₀) := by {
  simp only [Complex.normSq_apply, Complex.add_re, Complex.sub_re,
    Complex.ofReal_re, Complex.add_im, Complex.sub_im, Complex.ofReal_im]
  ring
}

/-- Exact mapping theorem: $s \in \Omega_{\sigma_0} \iff |\Phi_{\sigma_0}(s)| < 1$. -/
theorem mem_rightHalfPlane_iff_halfPlaneToDiskLFT_norm_lt_one (σ₀ : ℝ) (s : ℂ)
    (hden : s + ((1 - σ₀ : ℝ) : ℂ) ≠ 0) :
    s ∈ rightHalfPlane σ₀ ↔ ‖halfPlaneToDiskLFT σ₀ s‖ < 1 := by {
  unfold rightHalfPlane halfPlaneToDiskLFT linFracTrans
  simp only [Set.mem_setOf_eq, one_mul]
  have h_eq : s + -((σ₀ + 1 : ℝ) : ℂ) = s - ((σ₀ + 1 : ℝ) : ℂ) := by ring
  rw [h_eq, norm_div]
  have hden_pos : 0 < ‖s + ((1 - σ₀ : ℝ) : ℂ)‖ := norm_pos_iff.mpr hden
  rw [div_lt_one hden_pos, ← sq_lt_sq₀ (norm_nonneg _) (norm_nonneg _)]
  simp only [← Complex.normSq_eq_norm_sq]
  have hdiff := halfPlaneToDiskLFT_normSq_diff σ₀ s
  constructor <;> intro h <;> linarith
}

/-!
## Section 2: Continuation from a Common Signal (`Supremum.lean` & `Continuation.lean`, Prop. 2.1)
-/

/-- The uniform continuation power-saving margin $\varepsilon_* = \min(\beta - 7/8 - \omega, \sigma)$
from Section 2 (Proposition 2.1) and `OAI/NumberTheory/DirichletL/Supremum.lean`. -/
def continuationMargin (β ω σ : ℝ) : ℝ :=
  min (β - 7 / 8 - ω) σ

theorem continuationMargin_pos {β ω σ : ℝ}
    (hω : ω < β - 7 / 8) (hσ : 0 < σ) :
    0 < continuationMargin β ω σ := by {
  exact lt_min (sub_pos.mpr hω) hσ
}

theorem continuationMargin_le_gap (β ω σ : ℝ) :
    continuationMargin β ω σ ≤ β - 7 / 8 - ω := by {
  exact min_le_left _ _
}

theorem continuationMargin_le_sigma (β ω σ : ℝ) :
    continuationMargin β ω σ ≤ σ := by {
  exact min_le_right _ _
}

theorem continuation_boundary_gt {β ω σ : ℝ} (hω : 0 < ω) :
    7 / 8 < β - continuationMargin β ω σ := by {
  have h := continuationMargin_le_gap β ω σ
  linarith
}

theorem max_signal_exponents (β ω σ c : ℝ) :
    max (7 / 8 + c + ω) (β + c - σ) =
      β + c - continuationMargin β ω σ := by {
  unfold continuationMargin
  rcases le_total (β - 7 / 8 - ω) σ with h | h
  · rw [min_eq_left h, max_eq_left (by linarith)]
    linarith
  · rw [min_eq_right h, max_eq_right (by linarith)]
}

theorem max_normalized_signal_exponents (β ω σ : ℝ) :
    max (3 / 16 + ω) (β - 11 / 16 - σ) =
      β - 11 / 16 - continuationMargin β ω σ := by {
  have h : (7 / 8 : ℝ) + -(11 / 16) = 3 / 16 := by norm_num
  simpa only [sub_eq_add_neg, h] using max_signal_exponents β ω σ (-(11 / 16))
}

theorem exists_gt_supremum_sub {S : Set ℝ} (hne : S.Nonempty)
    (hbounded : BddAbove S) {ε : ℝ} (hε : 0 < ε) :
    ∃ x ∈ S, sSup S - ε < x := by {
  apply (lt_csSup_iff hbounded hne).mp
  linarith
}

theorem uniform_bound_below_supremum_false {S : Set ℝ}
    (hne : S.Nonempty) (hbounded : BddAbove S) {ε : ℝ} (hε : 0 < ε)
    (hbound : ∀ x ∈ S, x ≤ sSup S - ε) : False := by {
  obtain ⟨x, hx, hlt⟩ := exists_gt_supremum_sub hne hbounded hε
  exact (not_lt_of_ge (hbound x hx)) hlt
}

theorem exists_gt_supremum_sub_of_insert {S : Set ℝ} {a ε : ℝ}
    (hbounded : BddAbove (insert a S)) (hε : 0 < ε)
    (ha : a ≤ sSup (insert a S) - ε) :
    ∃ x ∈ S, sSup (insert a S) - ε < x := by {
  obtain ⟨x, hx, hlt⟩ :=
    exists_gt_supremum_sub (Set.insert_nonempty a S) hbounded hε
  rcases Set.mem_insert_iff.mp hx with hxa | hxS
  · subst x
    exact False.elim ((not_lt_of_ge ha) hlt)
  · exact ⟨x, hxS, hlt⟩
}

theorem seven_eighths_of_uniform_margin_with_sentinel {S : Set ℝ}
    (hbounded : BddAbove (insert (1 / 2 : ℝ) S))
    (hbound : 7 / 8 < sSup (insert (1 / 2 : ℝ) S) →
      ∃ ω σ : ℝ, 0 < ω ∧ ω < sSup (insert (1 / 2 : ℝ) S) - 7 / 8 ∧
        0 < σ ∧ ∀ x ∈ S, x ≤ sSup (insert (1 / 2 : ℝ) S) -
          continuationMargin (sSup (insert (1 / 2 : ℝ) S)) ω σ) :
    sSup (insert (1 / 2 : ℝ) S) ≤ 7 / 8 := by {
  by_contra h
  obtain ⟨ω, σ, hω0, hω, hσ, hbound⟩ := hbound (lt_of_not_ge h)
  have hε := continuationMargin_pos hω hσ
  have hboundary := continuation_boundary_gt (β := sSup (insert (1 / 2 : ℝ) S))
    (σ := σ) hω0
  have hsentinel : (1 / 2 : ℝ) ≤ sSup (insert (1 / 2 : ℝ) S) -
      continuationMargin (sSup (insert (1 / 2 : ℝ) S)) ω σ := by {
    linarith
  }
  obtain ⟨x, hx, hlt⟩ := exists_gt_supremum_sub_of_insert hbounded hε hsentinel
  exact (not_lt_of_ge (hbound x hx)) hlt
}

/-- Shifted Mellin transform $F_\eta(s) = \int_0^\infty f(Z) Z^{-(s + c)} \frac{dZ}{Z}$
from Section 2 (Equation 2.7) and `OAI/NumberTheory/DirichletL/Continuation.lean`. -/
def signalMellin (f : ℝ → ℂ) (c : ℝ) (s : ℂ) : ℂ :=
  mellin f (-(s + (c : ℂ)))

/-- Rapid power decay at zero: $f(x) = O(x^B)$ as $x \downarrow 0$ for every $B \in \mathbb{R}$. -/
def RapidDecayAtZero (f : ℝ → ℂ) : Prop :=
  ∀ B : ℝ, f =O[𝓝[>] (0 : ℝ)] (fun x : ℝ => x ^ B)

theorem rpow_isBigO_atTop_of_le {a b : ℝ} (h : a ≤ b) :
    (fun x : ℝ => x ^ a) =O[atTop] (fun x : ℝ => x ^ b) := by {
  apply Asymptotics.IsBigO.of_bound 1
  filter_upwards [eventually_ge_atTop (1 : ℝ)] with x hx
  simpa only [one_mul, Real.norm_eq_abs,
    abs_of_nonneg (Real.rpow_nonneg (by linarith : 0 ≤ x) _)] using
    Real.rpow_le_rpow_of_exponent_le hx h
}

theorem common_signal_bound (J f : ℝ → ℂ) (a b : ℝ)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ a))
    (herror : (fun x => J x - f x) =O[atTop] (fun x : ℝ => x ^ b)) :
    f =O[atTop] (fun x : ℝ => x ^ max a b) := by {
  have h₁ := hJ.trans (rpow_isBigO_atTop_of_le (le_max_left a b))
  have h₂ := herror.trans (rpow_isBigO_atTop_of_le (le_max_right a b))
  simpa only [sub_sub_cancel] using h₁.sub h₂
}

theorem common_signal_bound_with_margin (J f : ℝ → ℂ) (β ω σ c : ℝ)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (7 / 8 + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ))) :
    f =O[atTop] (fun x : ℝ =>
      x ^ (β + c - continuationMargin β ω σ)) := by {
  simpa only [max_signal_exponents] using
    common_signal_bound J f (7 / 8 + c + ω) (β + c - σ) hJ herror
}

theorem signalMellin_convergent (f : ℝ → ℂ) (a c : ℝ)
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f) {s : ℂ} (hs : a < s.re) :
    MellinConvergent f (-(s + (c : ℂ))) := by {
  apply mellinConvergent_of_isBigO_rpow (a := -(a + c))
    (b := (-(s + (c : ℂ))).re - 1) hlocal
  · simpa only [neg_neg] using htop
  · simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
    linarith
  · exact hzero _
  · linarith
}

/-- **Sarason `_eps` Holomorphy of the Shifted Mellin Signal (`signalMellin_holomorphicOn_eps`)**:
If $f$ is locally integrable on $(0, \infty)$, has rapid decay at $0$, and satisfies
$f(x) = O(x^{a+c})$ as $x \to \infty$, then `signalMellin f c` is holomorphic in Sarason's
$\varepsilon$-$\delta$ sense (`HolomorphicOn_eps`) on the half-plane $\Omega_a = \{\operatorname{Re}(s) > a\}$. -/
theorem signalMellin_holomorphicOn_eps (f : ℝ → ℂ) (a c : ℝ)
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f) :
    HolomorphicOn_eps (signalMellin f c) (rightHalfPlane a) := by {
  intro s hs
  have hd : DifferentiableAt ℂ (mellin f) (-(s + (c : ℂ))) := by {
    apply mellin_differentiableAt_of_isBigO_rpow (a := -(a + c))
      (b := (-(s + (c : ℂ))).re - 1) hlocal
    · simpa only [neg_neg] using htop
    · simp only [Complex.neg_re, Complex.add_re, Complex.ofReal_re]
      change a < s.re at hs
      linarith
    · exact hzero _
    · linarith
  }
  have hcomp : DifferentiableAt ℂ (signalMellin f c) s :=
    hd.comp s ((differentiableAt_id.add_const (c : ℂ)).neg)
  exact (differentiableAt_iff_eps (signalMellin f c) s).mp hcomp
}

theorem signalMellin_analytic (f : ℝ → ℂ) (a c : ℝ)
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f) :
    AnalyticOnNhd ℂ (signalMellin f c) (rightHalfPlane a) := by {
  exact (holomorphicOn_eps_rightHalfPlane_iff (signalMellin f c) a).mp
    (signalMellin_holomorphicOn_eps f a c hlocal htop hzero)
}

/-- Identity theorem on right half-planes expressed via `Sarason.HolomorphicOn_eps`. -/
theorem product_identity_on_halfPlane_eps (a b : ℝ) (L M W : ℂ → ℂ)
    (hL : HolomorphicOn_eps L (rightHalfPlane a))
    (hM : HolomorphicOn_eps M (rightHalfPlane a))
    (hW : HolomorphicOn_eps W (rightHalfPlane a))
    (heq : ∀ s : ℂ, max a b < s.re → L s * M s = W s) :
    Set.EqOn (fun s => L s * M s) W (rightHalfPlane a) := by {
  have hLa := (holomorphicOn_eps_rightHalfPlane_iff L a).mp hL
  have hMa := (holomorphicOn_eps_rightHalfPlane_iff M a).mp hM
  have hWa := (holomorphicOn_eps_rightHalfPlane_iff W a).mp hW
  let z : ℂ := (max a b + 1 : ℝ)
  have hz : a < z.re := by { dsimp [z]; linarith [le_max_left a b] }
  have hz' : max a b < z.re := by { dsimp [z]; simp }
  have hev : (fun s => L s * M s) =ᶠ[𝓝 z] W := by {
    filter_upwards [(isOpen_rightHalfPlane (max a b)).mem_nhds hz'] with s hs
    exact heq s hs
  }
  exact (hLa.mul hMa).eqOn_of_preconnected_of_eventuallyEq hWa
    (isPreconnected_rightHalfPlane a) hz hev
}

theorem nonzero_of_regularized_signal_eps (a b c : ℝ)
    (L Lregular R W : ℂ → ℂ) (f : ℝ → ℂ)
    (hL : HolomorphicOn_eps Lregular (rightHalfPlane a))
    (hR : HolomorphicOn_eps R (rightHalfPlane a))
    (hW : HolomorphicOn_eps W (rightHalfPlane a))
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (htop : f =O[atTop] (fun x : ℝ => x ^ (a + c)))
    (hzero : RapidDecayAtZero f)
    (heq : ∀ s : ℂ, max a b < s.re →
      Lregular s * signalMellin f c s = R s * W s)
    {ρ : ℂ} (hρ : a < ρ.re)
    (hregular : Lregular ρ = R ρ * L ρ)
    (hRρ : R ρ ≠ 0) (hWρ : W ρ ≠ 0) : L ρ ≠ 0 := by {
  have hRW : HolomorphicOn_eps (fun s => R s * W s) (rightHalfPlane a) := by {
    have hRa := (holomorphicOn_eps_rightHalfPlane_iff R a).mp hR
    have hWa := (holomorphicOn_eps_rightHalfPlane_iff W a).mp hW
    exact (holomorphicOn_eps_rightHalfPlane_iff _ a).mpr (hRa.mul hWa)
  }
  have hid := product_identity_on_halfPlane_eps a b Lregular (signalMellin f c)
    (fun s => R s * W s) hL (signalMellin_holomorphicOn_eps f a c hlocal htop hzero)
    hRW heq hρ
  intro hz
  change Lregular ρ * signalMellin f c ρ = R ρ * W ρ at hid
  rw [hregular, hz, mul_zero, zero_mul] at hid
  exact (mul_ne_zero hRρ hWρ) hid.symm
}

theorem multiplier_ne_zero {H : ℂ → ℂ} {s : ℂ}
    (h : ‖H s - 1‖ ≤ (1 / 2 : ℝ)) : H s ≠ 0 := by {
  intro hz
  simp [hz] at h
  norm_num at h
}

/-- The Gaussian-weighted Euler correction multiplier $e^{(s - 5/6)^2} H(s)$ from Equation (2.4). -/
def gaussianMultiplier (H : ℂ → ℂ) (s : ℂ) : ℂ :=
  Complex.exp ((s - 5 / 6) ^ 2) * H s

theorem gaussianMultiplier_holomorphicOn_eps {H : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hH : HolomorphicOn_eps H U) : HolomorphicOn_eps (gaussianMultiplier H) U := by {
  have hHa := (holomorphicOn_eps_iff_analyticOnNhd hU).mp hH
  have hGa : AnalyticOnNhd ℂ (gaussianMultiplier H) U :=
    ((analyticOnNhd_id.sub analyticOnNhd_const).pow 2).cexp.mul hHa
  exact (holomorphicOn_eps_iff_analyticOnNhd hU).mpr hGa
}

theorem gaussianMultiplier_ne_zero {H : ℂ → ℂ} {s : ℂ}
    (hH : ‖H s - 1‖ ≤ (1 / 2 : ℝ)) : gaussianMultiplier H s ≠ 0 := by {
  exact mul_ne_zero (Complex.exp_ne_zero _) (multiplier_ne_zero hH)
}

/-- **Master Common-Signal Continuation Theorem in Sarason `_eps` Form (`Proposition 2.1`)**:
If $L_{\mathrm{reg}}$, $R$, and $H$ satisfy `Sarason.HolomorphicOn_eps` on their half-planes,
$|H(s) - 1| \le 1/2$ on $\Omega_{7/8}$, and the probe $J$ satisfies the low bound
$J(x) = O(x^{7/8 + c + \omega})$ and high-expansion approximation
$J(x) - f(x) = O(x^{\beta + c - \sigma})$, then $L(\rho) \neq 0$ across the shifted half-plane
$\operatorname{Re}(\rho) > \beta - \operatorname{continuationMargin}(\beta, \omega, \sigma)$. -/
theorem nonzero_of_common_signal_eps (β ω σ c : ℝ) (hω : 0 < ω)
    (L Lregular R H : ℂ → ℂ) (J f : ℝ → ℂ)
    (hL : HolomorphicOn_eps Lregular
      (rightHalfPlane (β - continuationMargin β ω σ)))
    (hR : HolomorphicOn_eps R
      (rightHalfPlane (β - continuationMargin β ω σ)))
    (hH : HolomorphicOn_eps H sevenEighthsHalfPlane)
    (hcontract : ∀ s : ℂ, 7 / 8 < s.re → ‖H s - 1‖ ≤ (1 / 2 : ℝ))
    (hlocal : LocallyIntegrableOn f (Set.Ioi 0))
    (hzero : RapidDecayAtZero f)
    (hJ : J =O[atTop] (fun x : ℝ => x ^ (7 / 8 + c + ω)))
    (herror : (fun x => J x - f x) =O[atTop]
      (fun x : ℝ => x ^ (β + c - σ)))
    (heq : ∀ s : ℂ, max (β - continuationMargin β ω σ) 1 < s.re →
      Lregular s * signalMellin f c s = R s * gaussianMultiplier H s)
    {ρ : ℂ} (hρ : β - continuationMargin β ω σ < ρ.re)
    (hregular : Lregular ρ = R ρ * L ρ) (hRρ : R ρ ≠ 0) : L ρ ≠ 0 := by {
  have hboundary := continuation_boundary_gt (β := β) (σ := σ) hω
  have hH' : HolomorphicOn_eps H (rightHalfPlane (β - continuationMargin β ω σ)) :=
    fun s hs => hH s (lt_trans hboundary hs)
  have htop : f =O[atTop] (fun x : ℝ =>
      x ^ ((β - continuationMargin β ω σ) + c)) := by {
    have hexp : (β - continuationMargin β ω σ) + c =
        β + c - continuationMargin β ω σ := by ring
    simpa only [hexp] using common_signal_bound_with_margin J f β ω σ c hJ herror
  }
  exact nonzero_of_regularized_signal_eps _ 1 c L Lregular R (gaussianMultiplier H) f
    hL hR (gaussianMultiplier_holomorphicOn_eps (isOpen_rightHalfPlane _) hH')
    hlocal htop hzero heq hρ hregular
    hRρ (gaussianMultiplier_ne_zero (hcontract ρ (lt_trans hboundary hρ)))
}

/-!
## Section 3: Deleted Euler Factors & Logarithmic Control (`EulerFactors.lean` & `LogarithmicControl.lean`)
-/

/-- Local Euler factor $1 - a N^{-s}$ (`OAI.SevenEighths.EulerFactors.factor`). -/
def eulerFactor (N : ℝ) (a s : ℂ) : ℂ :=
  1 - a * (N : ℂ) ^ (-s)

theorem norm_eulerTerm_lt_one {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : ‖a * (N : ℂ) ^ (-s)‖ < 1 := by {
  rw [norm_mul, Complex.norm_cpow_eq_rpow_re_of_pos (by linarith : 0 < N),
    Complex.neg_re]
  calc
    ‖a‖ * N ^ (-s.re) ≤ 1 * N ^ (-s.re) :=
      mul_le_mul_of_nonneg_right ha (Real.rpow_nonneg (by linarith) _)
    _ < 1 := by simpa using Real.rpow_lt_one_of_one_lt_of_neg hN (neg_neg_of_pos hs)
}

theorem eulerFactor_ne_zero {N : ℝ} (hN : 1 < N) {a s : ℂ}
    (ha : ‖a‖ ≤ 1) (hs : 0 < s.re) : eulerFactor N a s ≠ 0 := by {
  intro h
  have heq : a * (N : ℂ) ^ (-s) = 1 := (sub_eq_zero.mp h).symm
  have hlt := norm_eulerTerm_lt_one hN ha hs
  rw [heq, norm_one] at hlt
  exact (lt_irrefl _ hlt)
}

theorem differentiable_eulerFactor {N : ℝ} (hN : 0 < N) (a : ℂ) :
    Differentiable ℂ (eulerFactor N a) := by {
  exact (differentiable_const (1 : ℂ)).sub ((differentiable_const a).mul
    (differentiable_id.neg.const_cpow (Or.inl (Complex.ofReal_ne_zero.mpr hN.ne'))))
}

/-- Every local Euler factor $1 - a N^{-s}$ ($N > 1$, $|a| \le 1$) is both `HolomorphicOn_eps` and
zero-free (`IsZeroFreeOn_eps`) on the open right half-plane $\Omega_0 = \{\operatorname{Re}(s) > 0\}$. -/
theorem isZeroFreeOn_eps_eulerFactor {N : ℝ} (hN : 1 < N) {a : ℂ} (ha : ‖a‖ ≤ 1) :
    IsZeroFreeOn_eps (eulerFactor N a) (rightHalfPlane 0) := by {
  constructor
  · intro s _
    exact (differentiableAt_iff_eps _ s).mp
      (differentiable_eulerFactor (by linarith : 0 < N) a s)
  · intro s hs
    exact eulerFactor_ne_zero hN ha hs
}

/-- Finite product of deleted Euler factors $\prod_{p \in S} (1 - a_p N_p^{-s})$. -/
def deletedEulerProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ) (a : ι → ℂ)
    (s : ℂ) : ℂ :=
  ∏ p ∈ S, eulerFactor (N p) (a p) s

theorem deletedEulerProduct_ne_zero {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {s : ℂ} (hs : 0 < s.re) : deletedEulerProduct S N a s ≠ 0 := by {
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact eulerFactor_ne_zero (hN p hp) (ha p hp) hs
}

theorem differentiable_deletedEulerProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 0 < N p) :
    Differentiable ℂ (deletedEulerProduct S N a) := by {
  classical
  induction S using Finset.induction_on with
  | empty =>
    change Differentiable ℂ (fun _ : ℂ => (1 : ℂ))
    exact differentiable_const _
  | @insert p S hp ih =>
    have hpN := hN p (Finset.mem_insert_self p S)
    have hSN : ∀ q ∈ S, 0 < N q := fun q hq => hN q (Finset.mem_insert_of_mem hq)
    have heq : deletedEulerProduct (insert p S) N a =
        fun s => eulerFactor (N p) (a p) s * deletedEulerProduct S N a s := by {
      funext s
      simp only [deletedEulerProduct, Finset.prod_insert hp]
    }
    rw [heq]
    exact (differentiable_eulerFactor hpN (a p)).mul (ih hSN)
}

/-- Every finite deleted Euler product is `IsZeroFreeOn_eps` on $\Omega_0 = \{\operatorname{Re}(s) > 0\}$,
so deleting finitely many Euler factors neither creates nor removes zeros in $\operatorname{Re}(s) > 0$. -/
theorem isZeroFreeOn_eps_deletedEulerProduct {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1) :
    IsZeroFreeOn_eps (deletedEulerProduct S N a) (rightHalfPlane 0) := by {
  constructor
  · intro s _
    have hN0 : ∀ p ∈ S, 0 < N p := fun p hp => lt_trans zero_lt_one (hN p hp)
    exact (differentiableAt_iff_eps _ s).mp (differentiable_deletedEulerProduct S N a hN0 s)
  · intro s hs
    exact deletedEulerProduct_ne_zero S N a hN ha hs
}

theorem deleted_eq_zero_iff {ι : Type*} (S : Finset ι) (N : ι → ℝ)
    (a : ι → ℂ) (hN : ∀ p ∈ S, 1 < N p) (ha : ∀ p ∈ S, ‖a p‖ ≤ 1)
    {L Ldeleted : ℂ → ℂ} {s : ℂ} (hs : 0 < s.re)
    (hidentity : Ldeleted s = deletedEulerProduct S N a s * L s) :
    Ldeleted s = 0 ↔ L s = 0 := by {
  rw [hidentity, mul_eq_zero]
  exact or_iff_right (deletedEulerProduct_ne_zero S N a hN ha hs)
}

/-- Borel–Carathéodory theorem on closed disks expressed for a function satisfying
`Sarason.HolomorphicOn_eps g (ball c R)` (`OAI.SevenEighths.LogarithmicControl.borel_caratheodory_closedBall`). -/
theorem borel_caratheodory_closedBall_eps {g : ℂ → ℂ} {c : ℂ} {r R M A : ℝ}
    (hr : 0 ≤ r) (hrR : r < R) (hM : 0 < M) (hA : 0 ≤ A)
    (hg : HolomorphicOn_eps g (ball c R))
    (hRe : ∀ z ∈ ball c R, (g z).re ≤ M) (hc : ‖g c‖ ≤ A)
    {z : ℂ} (hz : z ∈ closedBall c r) :
    ‖g z‖ ≤ 2 * M * r / (R - r) + A * (R + r) / (R - r) := by {
  have hR : 0 < R := lt_of_le_of_lt hr hrR
  have hgd : DifferentiableOn ℂ g (ball c R) :=
    (holomorphicOn_eps_iff_differentiableOn isOpen_ball).mp hg
  have hzn : ‖z - c‖ ≤ r := by simpa [mem_closedBall, dist_eq_norm] using hz
  have hzR : ‖z - c‖ < R := hzn.trans_lt hrR
  have hg' : DifferentiableOn ℂ (fun w ↦ g (c + w)) (ball 0 R) := by {
    apply hgd.comp ((differentiable_const c).add differentiable_id).differentiableOn
    intro w hw
    simpa [mem_ball, dist_eq_norm] using hw
  }
  have hb := Complex.borelCaratheodory hM hg' (fun w hw ↦ hRe _ (by
    simpa [mem_ball, dist_eq_norm] using hw)) (hr.trans_lt hrR)
    (show z - c ∈ ball 0 R by simpa using hzR)
  simp only [add_sub_cancel, add_zero] at hb
  refine hb.trans ?_
  apply add_le_add
  · gcongr
  · gcongr
}

/-!
## Section 4: Zero Detector, Compensated Probe, and Stage II Parameters (`Detector.lean`, `Parameters.lean`)
-/

theorem exists_small_increment (M : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {lo hi e : ℝ} (hlo : lo ≤ M 0) (hhi : M n ≤ hi)
    (hwidth : hi - lo ≤ n * e) :
    ∃ i < n, M (i + 1) - M i ≤ e := by {
  by_contra h
  have hinc : ∀ i ∈ Finset.range n, e < M (i + 1) - M i := by {
    intro i hi
    exact lt_of_not_ge (fun hle => h ⟨i, Finset.mem_range.mp hi, hle⟩)
  }
  have hs := Finset.sum_lt_sum_of_nonempty
    (Finset.nonempty_range_iff.mpr (Nat.ne_of_gt hn)) hinc
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    Finset.sum_range_sub] at hs
  linarith
}

theorem exists_grid_rounding {base x e : ℝ} (he : 0 < e) (hx : base ≤ x) :
    ∃ k : ℕ, base + e * k ≤ x ∧ x < base + e * k + e := by {
  let k := ⌊(x - base) / e⌋₊
  have hnonneg : 0 ≤ (x - base) / e := div_nonneg (sub_nonneg.mpr hx) he.le
  have hlo := Nat.floor_le hnonneg
  have hhi := Nat.lt_floor_add_one ((x - base) / e)
  have hlo' := (le_div_iff₀ he).mp hlo
  have hhi' := (div_lt_iff₀ he).mp hhi
  refine ⟨k, ?_, ?_⟩ <;> dsimp [k] <;> nlinarith
}

/-- Buffered-bin zero detector selection lemma (`OAI.SevenEighths.Detector.exists_buffered_bin`). -/
theorem exists_buffered_bin (M : ℕ → ℝ) {n : ℕ} (hn : 0 < n)
    {e : ℝ} (he : 0 < e)
    (hbound : ∀ j ≤ n, (51 / 100 : ℝ) ≤ M j ∧ M j ≤ 1)
    (hwidth : (49 / 100 : ℝ) ≤ n * e) :
    ∃ i < n, ∃ k : ℕ,
      let a : ℝ := 51 / 100 + e * k
      a ≤ 1 ∧ a ≤ M i ∧ M i < a + e ∧ M (i + 1) < a + 2 * e := by {
  obtain ⟨i, hi, hstep⟩ := exists_small_increment M hn (e := e)
    (hbound 0 (Nat.zero_le _)).1 (hbound n le_rfl).2 (by linarith)
  obtain ⟨k, hklo, hkhi⟩ := exists_grid_rounding he (hbound i hi.le).1
  refine ⟨i, hi, k, ?_, hklo, hkhi, ?_⟩
  · exact hklo.trans (hbound i hi.le).2
  · linarith
}

/-- Simultaneous saturation of inverse and plain Dirichlet polynomials
(`OAI.SevenEighths.Detector.simultaneous_saturation`, Section 8.2 of the paper). -/
theorem simultaneous_saturation {U δ r m ε A B : ℝ}
    (hU : 1 < U) (hδ : (1 / 50 : ℝ) ≤ δ) (hε : 0 ≤ ε)
    (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hprod : U ^ (δ * (r + m) - ε) ≤ A * B)
    (hupperA : A ≤ U ^ (δ * r + ε))
    (hupperB : B ≤ U ^ (δ * min m (1 - m) + ε)) :
    m ≤ 1 / 2 + 75 * ε ∧
      U ^ (δ * r - 2 * ε) ≤ A ∧ U ^ (δ * m - 2 * ε) ≤ B := by {
  have hU0 : 0 < U := by linarith
  have hδ0 : 0 ≤ δ := by linarith
  have hBcoarse : B ≤ U ^ (δ * m + ε) := by {
    apply hupperB.trans
    exact Real.rpow_le_rpow_of_exponent_le hU.le
      (by have h := mul_le_mul_of_nonneg_left (min_le_left m (1 - m)) hδ0; linarith)
  }
  have hpupper : A * B ≤ U ^ (δ * r + ε + (δ * min m (1 - m) + ε)) := by {
    rw [Real.rpow_add hU0]
    exact mul_le_mul hupperA hupperB hB (Real.rpow_nonneg hU0.le _)
  }
  have hexp := (Real.rpow_le_rpow_left_iff hU).mp (hprod.trans hpupper)
  have hlength : m ≤ 1 / 2 + 75 * ε := by {
    by_cases hm : m ≤ 1 / 2
    · linarith
    · have hmin : min m (1 - m) = 1 - m := min_eq_right (by linarith)
      rw [hmin] at hexp
      have hm0 : 0 ≤ m - 1 / 2 := by linarith
      have hmul := mul_le_mul_of_nonneg_right hδ hm0
      nlinarith
  }
  have hlowerA : U ^ (δ * r - 2 * ε) ≤ A := by {
    have hp : U ^ (δ * r - 2 * ε) * U ^ (δ * m + ε) ≤ A * U ^ (δ * m + ε) := by {
      calc
        _ = U ^ (δ * (r + m) - ε) := by { rw [← Real.rpow_add hU0]; congr 1; ring }
        _ ≤ A * B := hprod
        _ ≤ _ := mul_le_mul_of_nonneg_left hBcoarse hA
    }
    have hpos := Real.rpow_pos_of_pos hU0 (δ * m + ε)
    nlinarith
  }
  have hlowerB : U ^ (δ * m - 2 * ε) ≤ B := by {
    have hp : U ^ (δ * m - 2 * ε) * U ^ (δ * r + ε) ≤ B * U ^ (δ * r + ε) := by {
      calc
        _ = U ^ (δ * (r + m) - ε) := by { rw [← Real.rpow_add hU0]; congr 1; ring }
        _ ≤ A * B := hprod
        _ ≤ _ := by simpa [mul_comm] using mul_le_mul_of_nonneg_right hupperA hB
    }
    have hpos := Real.rpow_pos_of_pos hU0 (δ * r + ε)
    nlinarith
  }
  exact ⟨hlength, hlowerA, hlowerB⟩
}

theorem complex_simultaneous_saturation {U δ r m ε : ℝ} {M S : ℂ}
    (hU : 1 < U) (hδ : (1 / 50 : ℝ) ≤ δ) (hε : 0 ≤ ε)
    (hprod : U ^ (δ * (r + m) - ε) ≤ ‖M * S‖ ^ 2)
    (hupperM : ‖M‖ ^ 2 ≤ U ^ (δ * r + ε))
    (hupperS : ‖S‖ ^ 2 ≤ U ^ (δ * min m (1 - m) + ε)) :
    m ≤ 1 / 2 + 75 * ε ∧
      U ^ (δ * r - 2 * ε) ≤ ‖M‖ ^ 2 ∧
      U ^ (δ * m - 2 * ε) ≤ ‖S‖ ^ 2 := by {
  apply simultaneous_saturation hU hδ hε (sq_nonneg _) (sq_nonneg _)
    _ hupperM hupperS
  simpa only [norm_mul, mul_pow] using hprod
}

/-- Normalized probe $J_\eta(Z) = I(Z) / (c A(Z))$ (`OAI.SevenEighths.Probe.normalizedProbe`). -/
def normalizedProbe (I A : ℝ → ℂ) (c : ℂ) (Z : ℝ) : ℂ :=
  I Z / (c * A Z)

theorem norm_div_bound {I B : ℂ} {Z C D a ε : ℝ} (hZ : 0 < Z)
    (hI : ‖I‖ ≤ C * Z ^ a) (hB : ‖B⁻¹‖ ≤ D * Z ^ ε) :
    ‖I / B‖ ≤ (C * D) * Z ^ (a + ε) := by {
  rw [div_eq_mul_inv, norm_mul, Real.rpow_add hZ]
  calc
    ‖I‖ * ‖B⁻¹‖ ≤ (C * Z ^ a) * (D * Z ^ ε) :=
      mul_le_mul hI hB (norm_nonneg _) ((norm_nonneg _).trans hI)
    _ = C * D * (Z ^ a * Z ^ ε) := by ring
}

theorem common_normalization_bounds (I A f : ℝ → ℂ) {c : ℂ}
    {Z C_low C_high D a b ε : ℝ} (hZ : 0 < Z)
    (hc : c ≠ 0) (hA : A Z ≠ 0)
    (hrecip : ‖(c * A Z)⁻¹‖ ≤ D * Z ^ ε)
    (hlow : ‖I Z‖ ≤ C_low * Z ^ a)
    (hhigh : ‖I Z - (c * A Z) * f Z‖ ≤ C_high * Z ^ b) :
    ‖normalizedProbe I A c Z‖ ≤ (C_low * D) * Z ^ (a + ε) ∧
    ‖normalizedProbe I A c Z - f Z‖ ≤ (C_high * D) * Z ^ (b + ε) := by {
  constructor
  · exact norm_div_bound hZ hlow hrecip
  · have herr : normalizedProbe I A c Z - f Z =
        (I Z - (c * A Z) * f Z) / (c * A Z) := by {
      unfold normalizedProbe
      field_simp
    }
    rw [herr]
    exact norm_div_bound hZ hhigh hrecip
}

/-- Stage II compensated exponent geometry (`OAI.SevenEighths.Parameters.compensated_geometry`). -/
theorem compensated_geometry {d : ℝ} (_hd0 : 0 ≤ d) (hd1 : d ≤ 1 / 6) :
    (1 / 2 : ℝ) ≤ 5 / 6 - 2 * d ∧
    3 / 16 ≤ 17 / 48 - d ∧
    5 / 16 ≤ 23 / 48 - d ∧
    1 / 12 ≤ 23 / 48 - d - 11 * (1 / 8) / 6 ∧
    (17 / 48 : ℝ) / 2 + (1 / 8) / 12 = 3 / 16 := by {
  refine ⟨by linarith, by linarith, by linarith, by linarith, by norm_num⟩
}

/-!
## Section 5: Eisenstein Coordinates, Two-Poisson Recursion, & Sextic Gauss Sums (`EisensteinCoordinates.lean`)
-/

/-- The ring of integers $\mathcal{O} = \mathbb{Z}[\omega]$ of $\mathbb{Q}(\sqrt{-3}) = \mathbb{Q}(\zeta_3)$
is a principal ideal domain (`OAI.ShortDraft.eisenstein_ring_pid`). -/
theorem eisenstein_ring_pid :
    IsPrincipalIdealRing (NumberField.RingOfIntegers (CyclotomicField 3 ℚ)) := by {
  let : IsCyclotomicExtension {3} ℚ (CyclotomicField 3 ℚ) :=
    CyclotomicField.isCyclotomicExtension 3 ℚ
  exact IsCyclotomicExtension.Rat.three_pid (CyclotomicField 3 ℚ)
}

abbrev EisensteinCoordinates := ℤ × ℤ

def eisensteinMul (x y : EisensteinCoordinates) : EisensteinCoordinates :=
  (x.1 * y.1 - x.2 * y.2, x.1 * y.2 + x.2 * y.1 - x.2 * y.2)

def eisensteinConj (x : EisensteinCoordinates) : EisensteinCoordinates :=
  (x.1 - x.2, -x.2)

def eisensteinNorm (x : EisensteinCoordinates) : ℤ :=
  x.1 ^ 2 - x.1 * x.2 + x.2 ^ 2

theorem eisenstein_norm_mul (x y : EisensteinCoordinates) :
    eisensteinNorm (eisensteinMul x y) = eisensteinNorm x * eisensteinNorm y := by {
  rcases x with ⟨a, b⟩
  rcases y with ⟨c, d⟩
  dsimp [eisensteinNorm, eisensteinMul]
  ring
}

theorem eisenstein_norm_conj (x : EisensteinCoordinates) :
    eisensteinNorm (eisensteinConj x) = eisensteinNorm x := by {
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm, eisensteinConj]
  ring
}

theorem eisenstein_mul_conj (x : EisensteinCoordinates) :
    eisensteinMul x (eisensteinConj x) = (eisensteinNorm x, 0) := by {
  rcases x with ⟨a, b⟩
  apply Prod.ext <;> dsimp [eisensteinNorm, eisensteinConj, eisensteinMul] <;> ring
}

theorem eisenstein_norm_nonneg (x : EisensteinCoordinates) :
    0 ≤ eisensteinNorm x := by {
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm]
  nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
}

theorem eisenstein_norm_eq_zero_iff (x : EisensteinCoordinates) :
    eisensteinNorm x = 0 ↔ x = (0, 0) := by {
  rcases x with ⟨a, b⟩
  dsimp [eisensteinNorm]
  constructor
  · intro h
    have hb : b = 0 := by nlinarith [sq_nonneg (2 * a - b), sq_nonneg b]
    have ha : a = 0 := by { subst b; nlinarith [sq_nonneg a] }
    simp [ha, hb]
  · intro h
    simp_all
}

theorem cube_index_filter (b : ℕ) :
    (∑ h ∈ b.divisors, (ArithmeticFunction.moebius h : ℤ)) =
      if b = 1 then 1 else 0 := by {
  have h := congrArg (fun f : ArithmeticFunction ℤ => f b)
    ArithmeticFunction.moebius_mul_coe_zeta
  rw [ArithmeticFunction.coe_mul_zeta_apply] at h
  rw [ArithmeticFunction.one_apply] at h
  simpa using h
}

private lemma square_le_two_squares {x y e : ℝ}
    (hx : 0 ≤ x) (hy : 0 ≤ y) (he : 0 ≤ e) (h : x ≤ y + e) :
    x ^ 2 ≤ 2 * y ^ 2 + 2 * e ^ 2 := by {
  have h₁ : 0 ≤ y + e - x := sub_nonneg.mpr h
  have h₂ : 0 ≤ y + e + x := by nlinarith
  have h₃ := mul_nonneg h₁ h₂
  have h₄ := sq_nonneg (y - e)
  nlinarith
}

theorem finite_row_extraction {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (a : α → ℝ) (a₀ error bound : ℝ)
    (ha₀ : 0 ≤ a₀) (ha : ∀ u, 0 ≤ a u) (herror : 0 ≤ error)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes, a₀ ≤ a (row p) + error)
    (hmean : (∑ u ∈ rows, (a u) ^ 2) ≤ bound) :
    (primes.card : ℝ) * a₀ ^ 2 ≤
      2 * bound + 2 * (primes.card : ℝ) * error ^ 2 := by {
  have hselected : (∑ p ∈ primes, (a (row p)) ^ 2) ≤ bound := by {
    calc
      (∑ p ∈ primes, (a (row p)) ^ 2) =
          ∑ u ∈ primes.image row, (a u) ^ 2 := by rw [Finset.sum_image hinj]
      _ ≤ ∑ u ∈ rows, (a u) ^ 2 :=
        Finset.sum_le_sum_of_subset_of_nonneg hrows (fun _ _ _ => by positivity)
      _ ≤ bound := hmean
  }
  have hpoint (p : β) (hp : p ∈ primes) :
      a₀ ^ 2 ≤ 2 * (a (row p)) ^ 2 + 2 * error ^ 2 :=
    square_le_two_squares ha₀ (ha _) herror (happrox p hp)
  have hsum :
      (∑ p ∈ primes, a₀ ^ 2) ≤
        ∑ p ∈ primes, (2 * (a (row p)) ^ 2 + 2 * error ^ 2) :=
    Finset.sum_le_sum hpoint
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum,
    Finset.sum_const, nsmul_eq_mul] at hsum
  nlinarith
}

theorem complex_row_extraction {α β : Type*} [DecidableEq α] [DecidableEq β]
    (rows : Finset α) (primes : Finset β) (row : β → α)
    (A : α → ℂ) (untwisted : α) (error bound : ℝ)
    (herror : 0 ≤ error)
    (hrows : primes.image row ⊆ rows)
    (hinj : Set.InjOn row (primes : Set β))
    (happrox : ∀ p ∈ primes, ‖A untwisted - A (row p)‖ ≤ error)
    (hmean : (∑ u ∈ rows, ‖A u‖ ^ 2) ≤ bound) :
    (primes.card : ℝ) * ‖A untwisted‖ ^ 2 ≤
      2 * bound + 2 * (primes.card : ℝ) * error ^ 2 := by {
  apply finite_row_extraction rows primes row (fun u ↦ ‖A u‖)
    ‖A untwisted‖ error bound (norm_nonneg _) (fun u ↦ norm_nonneg _) herror
    hrows hinj ?_ hmean
  intro p hp
  calc
    ‖A untwisted‖ = ‖(A untwisted - A (row p)) + A (row p)‖ := by rw [sub_add_cancel]
    _ ≤ ‖A untwisted - A (row p)‖ + ‖A (row p)‖ := norm_add_le _ _
    _ ≤ ‖A (row p)‖ + error := by linarith [happrox p hp]
}

/-- **Zero-Free Half-Plane from Analytic Identity in Sarason `_eps` Form**
(`OAI.ShortDraft.zero_free_of_analytic_identity`):
If $L, M, W$ satisfy `Sarason.HolomorphicOn_eps` on $\Omega_\sigma$ ($\sigma < 1$) and
$L(s) M(s) = W(s)$ on the Euler half-plane $\operatorname{Re}(s) > 1$, then $W(\rho) \neq 0$
implies $L(\rho) \neq 0$ for every $\rho \in \Omega_\sigma$. -/
theorem zero_free_of_analytic_identity_eps
    (σ : ℝ) (_hσ : σ < 1) (L M W : ℂ → ℂ)
    (hL : HolomorphicOn_eps L (rightHalfPlane σ))
    (hM : HolomorphicOn_eps M (rightHalfPlane σ))
    (hW : HolomorphicOn_eps W (rightHalfPlane σ))
    (heq : ∀ s : ℂ, 1 < s.re → L s * M s = W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hWρ : W ρ ≠ 0) : L ρ ≠ 0 := by {
  have hident : Set.EqOn (fun s : ℂ => L s * M s) W (rightHalfPlane σ) :=
    product_identity_on_halfPlane_eps σ 1 L M W hL hM hW
      (fun s hs => heq s ((le_max_right σ 1).trans_lt hs))
  intro hLρ
  have hρeq := hident hρ
  change L ρ * M ρ = W ρ at hρeq
  rw [hLρ, zero_mul] at hρeq
  exact hWρ hρeq.symm
}

theorem zero_free_of_regularized_analytic_identity_eps
    (σ : ℝ) (hσ : σ < 1) (L Lregular M W : ℂ → ℂ)
    (hLregular : HolomorphicOn_eps Lregular (rightHalfPlane σ))
    (hM : HolomorphicOn_eps M (rightHalfPlane σ))
    (hW : HolomorphicOn_eps W (rightHalfPlane σ))
    (hregular : ∀ s : ℂ, σ < s.re → s ≠ 1 →
      Lregular s = (s - 1) * L s)
    (heq : ∀ s : ℂ, 1 < s.re →
      Lregular s * M s = (s - 1) * W s)
    (ρ : ℂ) (hρ : σ < ρ.re) (hρone : ρ ≠ 1)
    (hWρ : W ρ ≠ 0) : L ρ ≠ 0 := by {
  have hWa := (holomorphicOn_eps_rightHalfPlane_iff W σ).mp hW
  have hWregular : HolomorphicOn_eps (fun s : ℂ => (s - 1) * W s) (rightHalfPlane σ) :=
    (holomorphicOn_eps_rightHalfPlane_iff _ σ).mpr
      ((analyticOnNhd_id.sub analyticOnNhd_const).mul hWa)
  have hWregularρ : (ρ - 1) * W ρ ≠ 0 :=
    mul_ne_zero (sub_ne_zero.mpr hρone) hWρ
  have hLregularρ := zero_free_of_analytic_identity_eps σ hσ Lregular M
    (fun s : ℂ => (s - 1) * W s) hLregular hM hWregular heq
    ρ hρ hWregularρ
  rw [hregular ρ hρ hρone] at hLregularρ
  exact (mul_ne_zero_iff.mp hLregularρ).2
}

theorem two_poisson_scale_substitution
    (K X F B L A C d t J Y g e ge v Li K' X' F' Δ : ℝ)
    (hK : K ≠ 0) (hB : B ≠ 0) (hF : F ≠ 0)
    (hA : A ≠ 0) (hC : C ≠ 0) (hd : d ≠ 0)
    (ht : t ≠ 0) (hJ : J ≠ 0) (he : e ≠ 0)
    (hge : ge ≠ 0) (hv : v ≠ 0) (hL0 : L ≠ 0)
    (hL : L = X / B ^ 3)
    (hLi : Li = L / (A * C * t))
    (hg : g = e * ge)
    (hY : Y = L ^ 2 * B ^ 4 * F ^ 2 * d / (K * C ^ 2 * J))
    (hK' : K' = d * e ^ 2 * Li ^ 2 / (Y * g ^ 2))
    (hX' : X' = Li / (g * v))
    (hF' : F' = J * C * e * v)
    (hΔ : Δ = B * F * A * t * ge) :
    K' = K * J / (Δ ^ 2 * B ^ 2) ∧
      X' * F' = X * F * J / (Δ * B ^ 2) := by {
  constructor
  · rw [hK', hLi, hg, hY, hΔ]
    field_simp
  · rw [hX', hF', hLi, hL, hg, hΔ]
    field_simp
}

theorem two_poisson_budget
    (K X F R B J Δ K' childColumnMass R' : ℝ)
    (hK : 0 ≤ K) (hX : 0 < X) (hF : 0 < F)
    (hB : 0 < B) (hJpos : 0 < J) (hΔpos : 0 < Δ)
    (hJ : J ≤ B ^ 2) (hΔ : B * F ≤ Δ)
    (hK' : K' = K * J / (Δ ^ 2 * B ^ 2))
    (hM' : childColumnMass = X * F * J / (Δ * B ^ 2))
    (hR' : R' ≤ R * Δ) :
    K' * R' / childColumnMass ≤ K * R / (X * F) ∧
      K' ≤ K / (B * F) ^ 2 ∧
      childColumnMass ≤ X * F / (B * F) ∧
      (Δ * B ^ 2 / J) * childColumnMass = X * F := by {
  have hB2 : 0 < B ^ 2 := sq_pos_of_pos hB
  have hBF : 0 < B * F := mul_pos hB hF
  have hXF : 0 < X * F := mul_pos hX hF
  have hMpos : 0 < childColumnMass := by { rw [hM']; positivity }
  have hK'nonneg : 0 ≤ K' := by { rw [hK']; positivity }
  refine ⟨?_, ?_, ?_, ?_⟩
  · apply (div_le_div_iff₀ hMpos hXF).2
    calc
      K' * R' * (X * F) ≤ K' * (R * Δ) * (X * F) := by gcongr
      _ = (K * R / (X * F)) * childColumnMass * (X * F) := by { rw [hK', hM']; field_simp }
      _ = K * R * childColumnMass := by field_simp
  · rw [hK']
    apply (div_le_div_iff₀ (mul_pos (sq_pos_of_pos hΔpos) hB2) (sq_pos_of_pos hBF)).2
    have hΔ2 : (B * F) ^ 2 ≤ Δ ^ 2 := by
      nlinarith [mul_nonneg (sub_nonneg.mpr hΔ) (show 0 ≤ Δ + B * F by positivity)]
    nlinarith [mul_nonneg hK (sub_nonneg.mpr hJ),
      mul_nonneg (mul_nonneg hK (le_of_lt hB2)) (sub_nonneg.mpr hΔ2)]
  · rw [hM']
    apply (div_le_div_iff₀ (mul_pos hΔpos hB2) hBF).2
    nlinarith [mul_nonneg (le_of_lt hXF) (sub_nonneg.mpr hJ),
      mul_nonneg (mul_nonneg (le_of_lt hXF) (le_of_lt hB2)) (sub_nonneg.mpr hΔ)]
  · rw [hM']
    field_simp
}

/-! Finite-field Gauss sum helper lemmas (`gaussSum_one_one`, `gaussSum_one_right`, `gaussSum_one_left`
from Mathlib `v4.34`) proved directly in `v4.31.0-rc1`. -/
section SexticGaussSums

variable {F : Type*} [Field F] [Fintype F]

theorem gaussSum_one_one_local :
    gaussSum (1 : MulChar F ℂ) (1 : AddChar F ℂ) = Fintype.card Fˣ := by {
  classical
  simp [gaussSum, MulChar.sum_one_eq_card_units]
}

theorem gaussSum_one_right_local {χ : MulChar F ℂ} (hχ : χ ≠ 1) :
    gaussSum χ (1 : AddChar F ℂ) = 0 := by {
  simpa [gaussSum] using MulChar.sum_eq_zero_of_ne_one hχ
}

theorem gaussSum_eq_units_sum (χ : MulChar F ℂ) (ψ : AddChar F ℂ) :
    gaussSum χ ψ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by {
  classical
  have hzero : χ (0 : F) * ψ (0 : F) = 0 := by simp
  calc
    gaussSum χ ψ = ∑ x ∈ (Finset.univ : Finset F).erase 0, χ x * ψ x := by
      simpa only [gaussSum, hzero, add_zero] using
        (Finset.sum_erase_add (Finset.univ : Finset F)
          (fun x => χ x * ψ x) (Finset.mem_univ (0 : F))).symm
    _ = ∑ x : {x : F // x ≠ 0}, χ x * ψ x := by {
      apply Finset.sum_subtype
      intro x
      simp
    }
    _ = ∑ y : Fˣ, χ (y : F) * ψ (y : F) := by {
      apply (Fintype.sum_equiv (unitsEquivNeZero : Fˣ ≃ {x : F // x ≠ 0})
        (fun y : Fˣ => χ (y : F) * ψ (y : F))
        (fun x : {x : F // x ≠ 0} => χ x * ψ x) ?_).symm
      intro y
      rfl
    }
}

theorem gaussSum_one_left_local {ψ : AddChar F ℂ} (hψ : ψ ≠ 1) :
    gaussSum (1 : MulChar F ℂ) ψ = -1 := by {
  classical
  have hsum_all : ∑ x : F, ψ x = 0 := AddChar.sum_eq_zero_of_ne_one hψ
  have hsplit := Finset.sum_erase_add (Finset.univ : Finset F) (fun x : F => ψ x) (Finset.mem_univ (0 : F))
  rw [hsum_all, map_zero_eq_one] at hsplit
  have h_erase : gaussSum (1 : MulChar F ℂ) ψ = ∑ x ∈ (Finset.univ : Finset F).erase 0, ψ x := by {
    have hzero : (1 : MulChar F ℂ) (0 : F) * ψ (0 : F) = 0 := by simp
    rw [gaussSum, ← Finset.sum_erase_add (Finset.univ : Finset F) _ (Finset.mem_univ (0 : F)),
      hzero, add_zero]
    apply Finset.sum_congr rfl
    intro x hx
    have hx0 : x ≠ 0 := Finset.ne_of_mem_erase hx
    have hu : IsUnit x := isUnit_iff_ne_zero.mpr hx0
    rcases hu with ⟨u, rfl⟩
    simp
  }
  rw [h_erase]
  linear_combination hsplit
}

omit [Fintype F] in
theorem sextic_character_exponent (χ : MulChar F ℂ) (hχ : χ ^ 6 = 1) :
    χ⁻¹ * χ⁻¹ ^ 2 = χ ^ 3 := by {
  calc
    χ⁻¹ * χ⁻¹ ^ 2 = χ ^ (-3 : ℤ) := by group
    _ = χ ^ ((-3 : ℤ) + 6) := by rw [zpow_add, zpow_ofNat, hχ, mul_one]
    _ = χ ^ 3 := by group
}

theorem gaussSum_mulShift_any (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (a : F) :
    gaussSum χ (ψ.mulShift a) = χ⁻¹ a * gaussSum χ ψ := by {
  classical
  by_cases ha : a = 0
  · subst a
    have hshift : ψ.mulShift (0 : F) = 1 := by { ext x; simp }
    rw [hshift, gaussSum_one_right_local hχ]
    simp
  · have hu : IsUnit a := isUnit_iff_ne_zero.mpr ha
    simpa [hu.unit_spec] using gaussSum_mulShift_eq χ ψ hu.unit
}

omit [Fintype F] in
theorem sextic_character_quadratic (χ : MulChar F ℂ) (hχ : χ ^ 6 = 1) :
    (χ ^ 3)⁻¹ = χ ^ 3 := by {
  calc
    (χ ^ 3)⁻¹ = χ ^ (-3 : ℤ) := by group
    _ = χ ^ ((-3 : ℤ) + 6) := by rw [zpow_add, zpow_ofNat, hχ, mul_one]
    _ = χ ^ 3 := by group
}

theorem sextic_inversion_sum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (a : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ (a * ((h⁻¹ : Fˣ) : F))) =
      ∑ y : Fˣ, (χ ^ 3) y * ψ (a * (y : F)) := by {
  classical
  calc
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ (a * ((h⁻¹ : Fˣ) : F))) =
        ∑ y : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) (y⁻¹) * ψ (a * (y : F)) := by {
          apply Fintype.sum_equiv (Equiv.inv Fˣ)
          intro y
          simp
        }
    _ = ∑ y : Fˣ, (χ ^ 3) y * ψ (a * (y : F)) := by {
      congr 1
      funext y
      rw [sextic_character_exponent χ hχ]
      have hy := sextic_character_quadratic χ hχ
      have hval : (χ ^ 3) ((y⁻¹ : Fˣ) : F) = (χ ^ 3) (y : F) := by {
        calc
          (χ ^ 3) ((y⁻¹ : Fˣ) : F) = (χ ^ 3)⁻¹ (y : F) := by
            rw [MulChar.inv_apply', Units.val_inv_eq_inv_val]
          _ = (χ ^ 3) (y : F) := by rw [hy]
      }
      rw [← Units.val_inv_eq_inv_val y, hval]
    }
}

theorem sextic_inversion_gaussSum (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (a : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ (a * ((h⁻¹ : Fˣ) : F))) =
      gaussSum (χ ^ 3) (ψ.mulShift a) := by {
  rw [sextic_inversion_sum χ ψ hχ a, gaussSum_eq_units_sum]
  simp only [AddChar.mulShift_apply]
}

theorem sextic_local_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hχ₃ : χ ^ 3 ≠ 1) (ε x : F) :
    (∑ h : Fˣ, (χ⁻¹ * χ⁻¹ ^ 2) h * ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      (χ ^ 3) ε * gaussSum (χ ^ 3) ψ * (χ ^ 3) x := by {
  rw [sextic_inversion_gaussSum χ ψ hχ (ε * x)]
  rw [gaussSum_mulShift_any (χ ^ 3) ψ hχ₃ (ε * x)]
  rw [sextic_character_quadratic χ hχ, map_mul]
  ring
}

theorem nontrivial_fourier_coefficient (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ≠ 1) (h : F) :
    (∑ t : F, χ t * ψ (-(h * t))) =
      χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) := by {
  calc
    (∑ t : F, χ t * ψ (-(h * t))) =
        gaussSum χ ((ψ.mulShift (-1)).mulShift h) := by {
          simp only [gaussSum, AddChar.mulShift_apply]
          congr 1
          funext t
          congr 1
          ring_nf
        }
    _ = χ⁻¹ h * gaussSum χ (ψ.mulShift (-1)) :=
      gaussSum_mulShift_any χ (ψ.mulShift (-1)) hχ h
}

/-- Sextic Fourier–theta local row identity (`OAI.ShortDraftLocal.sextic_fourier_theta_row`). -/
theorem sextic_fourier_theta_row (χ : MulChar F ℂ) (ψ : AddChar F ℂ)
    (hχ : χ ^ 6 = 1) (hχ₃ : χ ^ 3 ≠ 1)
    (σ : Fˣ) (ε x : F) :
    (Fintype.card F : ℂ)⁻¹ *
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
      ((χ⁻¹) ^ 2) σ *
      ((Fintype.card F : ℂ)⁻¹ *
        gaussSum χ (ψ.mulShift (-1)) * gaussSum (χ ^ 3) ψ * (χ ^ 3) ε) *
      (χ ^ 3) x := by {
  classical
  have hχ₁ : χ ≠ 1 := by {
    intro heq
    exact hχ₃ (by simp [heq])
  }
  have hsum :
      (∑ h : Fˣ,
        (∑ t : F, χ t * ψ (-(h * t))) *
        (((χ⁻¹) ^ 2) (σ * h)) *
        ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) =
        ((χ⁻¹) ^ 2) σ * gaussSum χ (ψ.mulShift (-1)) *
          (∑ h : Fˣ,
            (χ⁻¹ * (χ⁻¹) ^ 2) h *
              ψ ((ε * x) * ((h⁻¹ : Fˣ) : F))) := by {
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro h _
    rw [nontrivial_fourier_coefficient χ ψ hχ₁, map_mul]
    simp only [MulChar.mul_apply]
    ring
  }
  rw [hsum, sextic_local_row χ ψ hχ hχ₃ ε x]
  ring
}

end SexticGaussSums

/-!
## Section 6: Melding onto `Sarason.PNT` (`Zeta.lean`, `Newman.lean`) and Hecke-to-Dirichlet Transfer
-/

/-- The Stage II Quasi-Riemann Hypothesis predicate (`OAI.Nonvanishing`):
every Dirichlet $L$-function $L(s, \chi)$ is nonvanishing on $\Omega_{7/8} = \{\operatorname{Re}(s) > 7/8\}$
away from the principal pole $(\chi = 1, s = 1)$. -/
def DirichletQuasiRiemannTarget : Prop :=
  ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
    s ∈ sevenEighthsHalfPlane → ¬ (χ = 1 ∧ s = 1) →
      DirichletCharacter.LFunction χ s ≠ 0

/-- Classical nonvanishing on $\operatorname{Re}(s) \ge 1$ (`OAI.ShortDraft.dirichlet_target_of_one_le_re`). -/
theorem dirichlet_ne_zero_of_one_le_re
    (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ)
    (hs : 1 ≤ s.re) (hprincipal : ¬ (χ = 1 ∧ s = 1)) :
    DirichletCharacter.LFunction χ s ≠ 0 := by {
  exact χ.LFunction_ne_zero_of_one_le_re (not_and_or.mp hprincipal) hs
}

/-- Equivalence between `DirichletQuasiRiemannTarget` on $\operatorname{Re}(s) > 7/8$ and
nonvanishing on the open critical strip $7/8 < \operatorname{Re}(s) < 1$. -/
theorem dirichletQuasiRiemannTarget_iff_open_strip :
    DirichletQuasiRiemannTarget ↔
      ∀ (q : ℕ) [NeZero q] (χ : DirichletCharacter ℂ q) (s : ℂ),
        (7 / 8 : ℝ) < s.re → s.re < 1 →
          DirichletCharacter.LFunction χ s ≠ 0 := by {
  constructor
  · intro h q _ χ s h78 _
    apply h q χ s h78
    intro ⟨_, hs⟩
    simp [hs] at *
  · intro h q _ χ s h78 hprincipal
    by_cases hs : s.re < 1
    · exact h q χ s h78 hs
    · exact dirichlet_ne_zero_of_one_le_re q χ s (le_of_not_gt hs) hprincipal
}

/-- **Hecke-to-Dirichlet Quadratic Norm-Factorization Transfer**
(`OAI.SevenEighths.HeckeDirichlet.dirichlet_seven_eighths_of_hecke`, Section 1, p. 6):
Because the base-change Hecke $L$-function over $F = \mathbb{Q}(\sqrt{-3})$ factors as
$L_F(s, \chi \circ N_{F/\mathbb{Q}}) = L(s, \chi)\,L(s, \chi \chi_{-3})$, nonvanishing of
$L_F(s, \chi \circ N_{F/\mathbb{Q}})$ on $\Omega_{7/8}$ immediately implies $L(s, \chi) \neq 0$. -/
theorem dirichlet_ne_zero_of_hecke_factorization
    {L_hecke L_dir L_twist : ℂ → ℂ} {s : ℂ}
    (h_factor : L_hecke s = L_dir s * L_twist s)
    (h_hecke_nz : L_hecke s ≠ 0) :
    L_dir s ≠ 0 := by {
  rw [h_factor] at h_hecke_nz
  exact (mul_ne_zero_iff.mp h_hecke_nz).1
}

/-- Deduction of `riemannZeta s ≠ 0` on $\Omega_{7/8}$ from `DirichletQuasiRiemannTarget`
(`OAI.SevenEighths.HeckeDirichlet.zeta_seven_eighths_of_hecke`). -/
theorem riemannZeta_ne_zero_of_dirichletQuasiRiemannTarget
    (hQ : DirichletQuasiRiemannTarget) {s : ℂ} (hs : s ∈ sevenEighthsHalfPlane) :
    riemannZeta s ≠ 0 := by {
  by_cases h1 : s = 1
  · simpa [h1] using riemannZeta_one_ne_zero
  · have h := hQ 1 (1 : DirichletCharacter ℂ 1) s hs (by simp [h1])
    simpa only [DirichletCharacter.LFunction_modOne_eq] using h
}

/-- **Sarason `_eps` Bridge to `Sarason.PNT.zeta_eps` and `Sarason.PNT.eulerProduct_eps` (`Zeta.lean`)**:
On the Euler half-plane $\Omega_1 = \{\operatorname{Re}(s) > 1\}$, `Sarason.PNT.zeta_eps s`
equals Mathlib's `riemannZeta s`, and under `DirichletQuasiRiemannTarget` both `zeta_eps s`
and `eulerProduct_eps s` are strictly nonzero! -/
theorem zeta_eps_eq_riemannZeta_on_eulerHalfPlane {s : ℂ} (hs : 1 < s.re) :
    zeta_eps s = riemannZeta s := by {
  have h_lim := zeta_eps_limit s hs
  have h_val : IsZetaAt_eps s (zeta_eps s) := by {
    dsimp [zeta_eps]
    rw [dif_pos h_lim]
    exact Classical.choose_spec h_lim
  }
  have h_tendsto_eps : Tendsto (fun N => zetaPartialSum N s) atTop (nhds (zeta_eps s)) := by {
    rw [Metric.tendsto_atTop]
    intro ε hε
    rcases h_val ε hε with ⟨N₀, hN₀⟩
    exact ⟨N₀, fun N hN => by simpa [dist_eq_norm] using hN₀ N hN⟩
  }
  have hs_div : HasSum (fun n : ℕ => 1 / (n : ℂ) ^ s) (riemannZeta s) :=
    ( zeta_eq_tsum_one_div_nat_cpow hs ).symm ▸
      (Complex.summable_one_div_nat_cpow.mpr hs).hasSum
  have hs_ne_zero : s ≠ 0 := by { intro h; rw [h] at hs; norm_num at hs }
  have h_congr : (fun n : ℕ => if n = 0 then (0 : ℂ) else (n : ℂ) ^ (-s)) =
      (fun n : ℕ => 1 / (n : ℂ) ^ s) := by {
    ext n
    by_cases hn : n = 0
    · subst hn; simp [hs_ne_zero]
    · rw [if_neg hn, one_div, cpow_neg]
  }
  have h_tendsto_zeta : Tendsto (fun N => zetaPartialSum N s) atTop (nhds (riemannZeta s)) := by {
    unfold zetaPartialSum
    simpa only [h_congr] using hs_div.tendsto_sum_nat
  }
  exact tendsto_nhds_unique h_tendsto_eps h_tendsto_zeta
}

theorem zeta_eps_and_eulerProduct_eps_ne_zero
    (hQ : DirichletQuasiRiemannTarget) {s : ℂ} (hs : 1 < s.re) :
    zeta_eps s ≠ 0 ∧ eulerProduct_eps s ≠ 0 := by {
  have hs78 : s ∈ sevenEighthsHalfPlane := by {
    change (7 / 8 : ℝ) < s.re
    linarith
  }
  have h_zeta_nz : zeta_eps s ≠ 0 := by {
    rw [zeta_eps_eq_riemannZeta_on_eulerHalfPlane hs]
    exact riemannZeta_ne_zero_of_dirichletQuasiRiemannTarget hQ hs78
  }
  refine ⟨h_zeta_nz, ?_⟩
  rw [← zeta_eq_eulerProduct s hs]
  exact h_zeta_nz
}

/-- **Sarason `_eps` Quasi-Riemann Holomorphic Reciprocal Continuation (`QuasiRiemannSarasonBridge_eps`)**:
Under `DirichletQuasiRiemannTarget`, for any function $L_{\mathrm{reg}}$ that is
`HolomorphicOn_eps` on $\Omega_{7/8}$ and satisfies $L_{\mathrm{reg}}(s) = (s - 1)\zeta(s)$ for
$s \neq 1$ with $L_{\mathrm{reg}}(1) = 1$, $L_{\mathrm{reg}}$ satisfies `IsZeroFreeOn_eps` on the
entire half-plane $\Omega_{7/8} = \{\operatorname{Re}(s) > 7/8\}$, and its reciprocal
$s \mapsto (L_{\mathrm{reg}}(s))⁻¹$ is `HolomorphicOn_eps` on $\Omega_{7/8}$ (and hence on the
shifted Newman half-plane $\operatorname{Re}(z) > -1/8$ via $s = z + 1$)! -/
theorem isZeroFreeOn_eps_regularized_zeta_of_quasiRiemann
    (hQ : DirichletQuasiRiemannTarget)
    (L_reg : ℂ → ℂ)
    (hHol : HolomorphicOn_eps L_reg sevenEighthsHalfPlane)
    (hEq : ∀ s ∈ sevenEighthsHalfPlane, s ≠ 1 → L_reg s = (s - 1) * riemannZeta s)
    (hOne : L_reg 1 = 1) :
    IsZeroFreeOn_eps L_reg sevenEighthsHalfPlane ∧
    HolomorphicOn_eps (fun s => (L_reg s)⁻¹) sevenEighthsHalfPlane := by {
  have hZF : IsZeroFreeOn_eps L_reg sevenEighthsHalfPlane := by {
    refine ⟨hHol, ?_⟩
    intro s hs
    by_cases hs1 : s = 1
    · rw [hs1, hOne]
      exact one_ne_zero
    · rw [hEq s hs hs1]
      exact mul_ne_zero (sub_ne_zero.mpr hs1)
        (riemannZeta_ne_zero_of_dirichletQuasiRiemannTarget hQ hs)
  }
  exact ⟨hZF, holomorphicOn_eps_inv_of_isZeroFreeOn_eps hZF⟩
}

/-!
## Section 7: Sharpness of $7/8$, the V-Curve Law $\sigma_{\mathrm{II}}(\ell)$, High-Side Slack, and Reaching $6/7$

In OpenAI's paper (`brennanOAI/preprints/The-Quasi-Riemann-Hypothesis-September-30-2026/build/paper.tex`,
Equations (5.1), (5.4), (5.6), (5.10)–(5.11), and Lemma `lem:balanced-endpoint`), the Stage II
parameter tuple $(b, h, \ell, l_x, l_y)$ satisfies:
- $l_x = 1 + \ell - h$ (reflected $X$-scale exponent),
- $l_y = l_x + b$ (reflected $Y$-scale exponent, with asymmetry $b = l_y - l_x$),
- $M = l_x + l_y$ and $M + \ell = 1$ (completed cubic-theta scale conservation),
- Principal Mellin shift: $C(s) = \frac{l_x}{2} + s - 1 + \frac{h}{6}$,
- Low-side probe exponent (Proposition `prop:probe-low`, Eq. 5.10):
  $$E_{\mathrm{low}}(\ell, b) = \frac{l_x}{2} + \frac{b}{12} + \frac{\max(0, \ell - 1/6)}{2},$$
  where $\frac{b}{12}$ comes from the sixth-power exceptional Gram frequencies $P_a^{1/6} = Z^{b/6}$
  after Cauchy–Schwarz (`prop:probe-gram`, Eq. 5.6) and $\frac{\max(0, \ell - 1/6)}{2}$ comes from
  the completed-row reflected energy $M' + ((d - 1/6)/4)_+$ (`lem:probe-row-norm`, Eq. 5.4).

In this section we prove:
1. **Asymmetry Cancellation Law (`zeroFreeThreshold_eq_of_scale_conservation`)**:
   Equating $C(\sigma_0) = E_{\mathrm{low}}$ cancels both $l_x/2$ and the asymmetry $b = l_y - l_x$
   identically whenever $l_x + l_y + \ell = 1$, leaving the closed-form V-curve:
   $$\sigma_{\mathrm{II}}(\ell) = \frac{11}{12} - \frac{\ell}{4} + \frac{\max(0, \ell - 1/6)}{2}.$$
2. **Sharpness of $7/8$ (`seven_eighths_sharp_v_curve_min`)**:
   $\sigma_{\mathrm{II}}(0) = \frac{11}{12}$ (Stage I), $\sigma_{\mathrm{II}}(1/6) = \frac{7}{8}$ (Stage II),
   and $\sigma_{\mathrm{II}}(\ell) \ge \frac{7}{8}$ for all $\ell \in \mathbb{R}$, with unique minimum
   $\sigma_{\mathrm{II}}(\ell) = \frac{7}{8} \iff \ell = \frac{1}{6}$.
3. **Strict High-Side Slack Certificate (`high_side_endpoint_sos_certificate` & `high_side_endpoint_margin`)**:
   At $(b, h, \ell) = (1/8, 13/16, 1/6)$, the high-side Poisson/moment inequality is **not** tight:
   by OpenAI's sum-of-squares identity (Eq. 16041), $-E_* \ge \frac{49}{440640} > \frac{1}{10000} > 0$.
4. **Exact Generalized Threshold for $7/8 - \varepsilon$ and $6/7$ (`generalizedZeroFreeThreshold` & `six_sevenths_criterion`)**:
   Improving the reflected-energy cutoff from $1/6$ to $1/6 + \delta_\ell$ and/or the sixth-power
   Gram exponent from $1/6$ to $1/6 - \delta_{\mathrm{Gram}}$ yields the threshold
   $$\sigma_0 = \frac{7}{8} - \frac{\delta_\ell}{4} - \frac{\delta_{\mathrm{Gram}}\, b}{2},$$
   reaching $\sigma_0 = \frac{6}{7}$ whenever $\frac{\delta_\ell}{4} + \frac{\delta_{\mathrm{Gram}}\, b}{2} = \frac{1}{56}$
   (in particular at $\ell = \frac{5}{21}$, i.e., $\delta_\ell = \frac{1}{14}$).
-/

/-- The Stage II zero-free threshold $\sigma_{\mathrm{II}}(\ell)$ as a function of the total prime
compensation length $\ell$, incorporating the reflected-energy kink $\frac{1}{2}\max(0, \ell - 1/6)$
from `lem:probe-row-norm` (Eq. 5.4 of `paper.tex`). -/
def stageIIVThreshold (ℓ : ℝ) : ℝ :=
  11 / 12 - ℓ / 4 + max 0 (ℓ - 1 / 6) / 2

/-- **Asymmetry Cancellation Law (`zeroFreeThreshold_eq_of_scale_conservation`)**:
Under the Stage II scale relations $l_x = 1 + \ell - h$, $l_y = l_x + b$, and $l_x + l_y + \ell = 1$,
the root $\sigma_0$ of the continuation balance equation
$$\frac{l_x}{2} + \sigma_0 - 1 + \frac{h}{6} = \frac{l_x}{2} + \frac{b}{12} + \frac{\max(0, \ell - 1/6)}{2}$$
is independent of the scale asymmetry $b = l_y - l_x$ and equals `stageIIVThreshold ℓ`. -/
theorem zeroFreeThreshold_eq_of_scale_conservation
    {b h ℓ lx ly σ₀ : ℝ}
    (hlx : lx = 1 + ℓ - h)
    (hly : ly = lx + b)
    (hM : lx + ly + ℓ = 1)
    (hbal : lx / 2 + σ₀ - 1 + h / 6 = lx / 2 + b / 12 + max 0 (ℓ - 1 / 6) / 2) :
    σ₀ = stageIIVThreshold ℓ := by {
  unfold stageIIVThreshold
  linarith
}

/-- At $\ell = 0$ (no prime compensation) the V-curve reproduces the Stage I threshold $\frac{11}{12}$,
and at $\ell = \frac{1}{6}$ it reproduces the Stage II Quasi-Riemann threshold $\frac{7}{8}$. -/
theorem stageIIVThreshold_special_values :
    stageIIVThreshold 0 = 11 / 12 ∧
    stageIIVThreshold (1 / 6) = 7 / 8 := by {
  unfold stageIIVThreshold
  constructor
  · rw [max_eq_left (by norm_num)]
    norm_num
  · rw [max_eq_left (by norm_num)]
    norm_num
}

/-- **Sharpness of the $7/8$ Barrier (`seven_eighths_sharp_v_curve_min`)**:
For every real compensation length $\ell \in \mathbb{R}$, $\sigma_{\mathrm{II}}(\ell) \ge 7/8$,
with equality if and only if $\ell = 1/6$. -/
theorem seven_eighths_sharp_v_curve_min (ℓ : ℝ) :
    (7 / 8 : ℝ) ≤ stageIIVThreshold ℓ ∧
    (stageIIVThreshold ℓ = 7 / 8 ↔ ℓ = 1 / 6) := by {
  unfold stageIIVThreshold
  rcases le_total (ℓ - 1 / 6) 0 with hle | hge
  · rw [max_eq_left hle]
    constructor
    · linarith
    · constructor <;> intro h <;> linarith
  · rw [max_eq_right hge]
    constructor
    · linarith
    · constructor <;> intro h <;> linarith
}

/-- **Short-Witness Crossing Identity (`prop:detector-counts`, Eq. 15410)**:
The convex combination of the marked-inverse count $A_I(r) = 1 - \delta(x + (1 - x)r)$ (with weight
$2 - 8x/9$) and the plain fourth-moment count $S_t(r) = 1 - \delta(4x/9 + (2 - 8x/9)(t - r))$
(with weight $1 - x$) eliminates the unknown witness length $r$ identically and equals $R_{\mathrm{short}}(t)$. -/
theorem detector_short_crossing_identity (δ x t r : ℝ) :
    let Dx : ℝ := 3 - 17 * x / 9
    let Px : ℝ := (2 - 8 * x / 9) * (1 - x)
    let AI : ℝ := 1 - δ * (x + (1 - x) * r)
    let St : ℝ := 1 - δ * (4 * x / 9 + (2 - 8 * x / 9) * (t - r))
    (2 - 8 * x / 9) * AI + (1 - x) * St =
      Dx * (1 - δ) + δ * Px * (3 / 2 - t) := by {
  dsimp only
  ring
}

/-- **Minimax Detector Cutoff Balance (`eq:target-cutoff`, Eq. 15963–15986)**:
At the optimal witness-length cutoff $t_* = 1 + \frac{\delta P_x}{2\mathcal{J}}$ with
$\mathcal{J} = (\alpha - \delta)D_x + \delta P_x$, the short-witness count $R_{\mathrm{short}}(t_*)$
and the sixth-power amplified long-witness count $L(t_*)$ coincide at $R_* = 1 - \delta + \frac{(\alpha - \delta)\delta P_x}{2\mathcal{J}}$. -/
theorem detector_minimax_cutoff_balance {α δ Dx Px J : ℝ}
    (hDx : Dx ≠ 0) (hJ : J ≠ 0)
    (hJ_def : J = (α - δ) * Dx + δ * Px) :
    let t_star : ℝ := 1 + (δ * Px) / (2 * J)
    let R_star : ℝ := 1 - δ + ((α - δ) * δ * Px) / (2 * J)
    1 - δ + (δ * Px / Dx) * (3 / 2 - t_star) = R_star ∧
    1 - δ + (α - δ) * (t_star - 1) = R_star := by {
  dsimp only
  constructor
  · field_simp [hDx, hJ]
    rw [hJ_def]
    ring
  · field_simp [hJ]
    ring
}

/-- **High-Side Bin Quadratic Expansion (`lem:balanced-endpoint`, Eq. 16021–16037)**:
Substituting $y = 1/2 - x$, $D_x = \frac{37 + 34y}{18}$, $P_x = \frac{7 + 18y + 8y^2}{9}$,
and $\mathcal{J} = \frac{j_y}{108}$ into $-E_* = \frac{1 + (3 + 8y)\delta}{48} - \frac{13}{32}\frac{(5/6 - \delta)\delta P_x}{\mathcal{J}}$
yields the exact quadratic in $\delta$ with leading prefactor $10368 = 2^7 \times 3^4$. -/
theorem high_bin_quadratic_expansion (y δ : ℝ) :
    let py : ℝ := 7 + 18 * y + 8 * y ^ 2
    let jy : ℝ := 185 + 170 * y + (-138 + 12 * y + 96 * y ^ 2) * δ
    let Dx : ℝ := (37 + 34 * y) / 18
    let Px : ℝ := py / 9
    let J : ℝ := jy / 108
    (J = (5 / 6 - δ) * Dx + δ * Px) ∧
    (10368 * (jy / 108 * ((1 + (3 + 8 * y) * δ) / 48) -
      (13 / 32) * (5 / 6 - δ) * δ * Px) =
      2 * jy * (1 + (3 + 8 * y) * δ) - 468 * (5 / 6 - δ) * δ * py) ∧
    (2 * jy * (1 + (3 + 8 * y) * δ) - 468 * (5 / 6 - δ) * δ * py =
      10 * (37 + 34 * y) - 8 * (237 + 377 * y + 26 * y ^ 2) * δ +
        48 * (51 + 131 * y + 94 * y ^ 2 + 32 * y ^ 3) * δ ^ 2) := by {
  dsimp only
  refine ⟨by ring, by ring, by ring⟩
}

/-- **Arithmetic Factorization of $\frac{49}{440640}$ (`lem:balanced-endpoint`, Eq. 16068)**:
- The numerator $49 = 7^2 = 6290 - 79^2$ is the positive discriminant gap at $y = 0$ ($v = 51$, $\delta = 79/204$).
- The denominator $440640 = 10368 \times 17 \times \frac{5}{2} = 176256 \times \frac{5}{2} = 2^6 \times 3^4 \times 5 \times 17$. -/
theorem fraction_49_440640_arithmetic_anatomy :
    (6290 - 79 ^ 2 : ℤ) = 49 ∧
    (10368 * 17 : ℕ) = 176256 ∧
    (176256 * (5 / 2 : ℝ)) = 440640 ∧
    (2 ^ 6 * 3 ^ 4 * 5 * 17 : ℕ) = 440640 := by {
  refine ⟨by norm_num, by norm_num, by norm_num, by norm_num⟩
}

/-- **OpenAI's High-Side Sum-of-Squares Endpoint Identity (`lem:balanced-endpoint`, Eq. 16041)**:
At the Stage II geometry $(b, h, \ell) = (1/8, 13/16, 1/6)$, the high-side polynomial
$10368 \mathcal{J} (-E_*)$ multiplied by $v = 51 + 41y$ factors into an explicit sum of positive squares. -/
theorem high_side_endpoint_sos_certificate (y δ : ℝ) :
    let v : ℝ := 51 + 41 * y
    let py : ℝ := 7 + 18 * y + 8 * y ^ 2
    let jy : ℝ := 185 + 170 * y + (-138 + 12 * y + 96 * y ^ 2) * δ
    v * (2 * jy * (1 + (3 + 8 * y) * δ) - 468 * (5 / 6 - δ) * δ * py) =
      (3 + 5 * y) * ((4 * v * δ - 79) ^ 2 + 49) +
        4 * y * (4 * v * δ * ((1 + 3 * y) * (15 + 32 * y) * δ + (9 - 13 * y)) +
          265 + 3485 * y) := by {
  dsimp only
  ring
}

/-- **Strict High-Side Slack Bound (`lem:balanced-endpoint`, Eq. 16068)**:
For all $y \in [0, 1/2]$ and $\delta \in [0, 5/6]$ with $0 < \mathcal{J} \le 5/2$, the high-side
exponent $-E_*$ has a uniform strictly positive margin $-E_* \ge \frac{49}{440640} > \frac{1}{10000}$. -/
theorem high_side_endpoint_margin {y δ J negE : ℝ}
    (hy0 : 0 ≤ y) (hy1 : y ≤ 1 / 2) (hδ0 : 0 ≤ δ)
    (hJ0 : 0 < J) (hJ1 : J ≤ 5 / 2)
    (hcert : 10368 * (51 + 41 * y) * J * negE =
      (3 + 5 * y) * ((4 * (51 + 41 * y) * δ - 79) ^ 2 + 49) +
        4 * y * (4 * (51 + 41 * y) * δ * ((1 + 3 * y) * (15 + 32 * y) * δ + (9 - 13 * y)) +
          265 + 3485 * y)) :
    (49 / 440640 : ℝ) ≤ negE ∧ (1 / 10000 : ℝ) < negE := by {
  set v : ℝ := 51 + 41 * y
  have hv_pos : 0 < v := by { dsimp [v]; linarith }
  have hv_le : v ≤ 17 * (3 + 5 * y) := by { dsimp [v]; linarith }
  have hsq : 0 ≤ (4 * v * δ - 79) ^ 2 := sq_nonneg _
  have hquad_pos : 0 ≤ (1 + 3 * y) * (15 + 32 * y) := by positivity
  have hlin_pos : 0 ≤ (1 + 3 * y) * (15 + 32 * y) * δ + (9 - 13 * y) := by {
    have h1 : 0 ≤ (1 + 3 * y) * (15 + 32 * y) * δ := mul_nonneg hquad_pos hδ0
    linarith
  }
  have hterm2 : 0 ≤ 4 * y * (4 * v * δ * ((1 + 3 * y) * (15 + 32 * y) * δ + (9 - 13 * y)) +
      265 + 3485 * y) := by positivity
  have h_lhs_ge : 49 * (3 + 5 * y) ≤ 10368 * v * J * negE := by {
    nlinarith [hcert, mul_nonneg (show (0 : ℝ) ≤ 3 + 5 * y by linarith) hsq, hterm2]
  }
  have hnegE_nonneg : 0 ≤ negE := by {
    have hpos : 0 < 10368 * v * J := by positivity
    nlinarith
  }
  have h_upper : 10368 * v * J * negE ≤ 440640 * (3 + 5 * y) * negE := by {
    nlinarith [mul_nonneg hv_pos.le (sub_nonneg.mpr hJ1),
      mul_nonneg (sub_nonneg.mpr hv_le) hnegE_nonneg]
  }
  have h35 : 0 < 3 + 5 * y := by linarith
  have hmain : (49 / 440640 : ℝ) ≤ negE := by nlinarith
  exact ⟨hmain, by linarith⟩
}

/-- **Generalized Zero-Free Threshold (`generalizedZeroFreeThreshold`)**:
If the reflected-energy cutoff $1/6$ is extended by $\delta_\ell \ge 0$ (so $\ell = 1/6 + \delta_\ell$)
and the sixth-power Gram exponent $1/6$ is reduced by $\delta_{\mathrm{Gram}} \ge 0$, the resulting
zero-free half-plane threshold is:
$$\sigma_0(\delta_\ell, \delta_{\mathrm{Gram}}, b) = \frac{7}{8} - \frac{\delta_\ell}{4} - \frac{\delta_{\mathrm{Gram}}\, b}{2}.$$ -/
def generalizedZeroFreeThreshold (δ_ℓ δ_Gram b : ℝ) : ℝ :=
  7 / 8 - δ_ℓ / 4 - δ_Gram * b / 2

/-- Any positive saving $\delta_\ell > 0$ in the reflected-energy cutoff or $\delta_{\mathrm{Gram}} > 0$
in the sixth-power Gram exponent strictly breaks the $7/8$ barrier ($\sigma_0 < 7/8$), and reaches
$\sigma_0 = 6/7$ (a gain of $\frac{7}{8} - \frac{6}{7} = \frac{1}{56}$) whenever
$\frac{\delta_\ell}{4} + \frac{\delta_{\mathrm{Gram}}\, b}{2} = \frac{1}{56}$
(in particular at $\delta_\ell = \frac{1}{14}$, i.e., $\ell = \frac{5}{21}$, with $\delta_{\mathrm{Gram}} = 0$). -/
theorem six_sevenths_criterion (δ_ℓ δ_Gram b : ℝ) :
    (generalizedZeroFreeThreshold δ_ℓ δ_Gram b = 6 / 7 ↔
      δ_ℓ / 4 + δ_Gram * b / 2 = 1 / 56) ∧
    generalizedZeroFreeThreshold (1 / 14) 0 b = 6 / 7 ∧
    generalizedZeroFreeThreshold (1 / 6) 0 b = 5 / 6 := by {
  unfold generalizedZeroFreeThreshold
  refine ⟨?_, by norm_num, by norm_num⟩
  constructor <;> intro h <;> linarith
}

end Sarason.QuasiRiemann
