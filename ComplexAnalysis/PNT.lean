import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.NumberTheory.PrimeCounting
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Contour

open Complex Filter TopologicalSpace Metric Bornology Classical MeasureTheory

/-!
# The Prime Number Theorem
Following Newman's Analytic Proof (1980)

This file contains the formalization of the Prime Number Theorem, 
breaking down the proof into modular 50-line lemmas.
-/

/-- Chebyshev's theta function ϑ(x) = ∑_{p ≤ x} log p -/
noncomputable def chebyshevTheta (x : ℝ) : ℝ :=
  ∑ p ∈ (Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime, Real.log (p : ℝ)

/-- The target function for the Laplace transform: f(t) = ϑ(e^t)e^{-t} - 1 -/
noncomputable def pntTargetFunc (t : ℝ) : ℝ :=
  chebyshevTheta (Real.exp t) * Real.exp (-t) - 1

lemma chebyshevTheta_mono {x y : ℝ} (hxy : x ≤ y) : chebyshevTheta x ≤ chebyshevTheta y := by
{
  dsimp [chebyshevTheta]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    rw [Finset.mem_filter] at hp ⊢
    rcases hp with ⟨hpr, hp_prime⟩
    rw [Finset.mem_range] at hpr ⊢
    refine ⟨?_, hp_prime⟩
    have h_floor : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono hxy
    linarith
  · intro p hp _
    rw [Finset.mem_filter] at hp
    have hp2 : 2 ≤ p := hp.2.two_le
    have hp2_real : (2:ℝ) ≤ (p:ℝ) := by exact_mod_cast hp2
    apply Real.log_nonneg
    linarith
}

/-- Newman's Tauberian Theorem (1980) -/
theorem newmans_tauberian_theorem (f : ℝ → ℝ) (hf_bound : ∃ M, ∀ t ≥ 0, |f t| ≤ M)
    (hf_loc_int : ∀ T > 0, IntervalIntegrable f volume 0 T) :
    let g := fun (z : ℂ) => ∫ t in Set.Ici (0:ℝ), (f t : ℂ) * Complex.exp (-z * (t : ℂ))
    (AnalyticOnNhd ℂ g {z : ℂ | z.re ≥ 0}) →
    Tendsto (fun T => ∫ t in (0:ℝ)..T, f t) atTop (nhds (g 0).re) := by
{
  sorry
}

/-- The Prime Number Theorem (expressed via Chebyshev's theta function) -/
theorem prime_number_theorem_theta : 
    Tendsto (fun x => chebyshevTheta x / x) atTop (nhds 1) := by
{
  sorry
}

lemma pntTargetFunc_lower_bound {x L t : ℝ} (_ : 1 < L) (hx_pos : 0 < x) 
    (ht : t ∈ Set.Icc (Real.log x) (Real.log (L * x)))
    (h_theta : L * x < chebyshevTheta x) :
    L * x * Real.exp (-t) - 1 < pntTargetFunc t := by
{
  dsimp [pntTargetFunc]
  have ht_exp_ge : x ≤ Real.exp t := by
  {
    have h1 := ht.1
    rw [← Real.exp_le_exp] at h1
    rw [Real.exp_log hx_pos] at h1
    exact h1
  }
  have h_mono := chebyshevTheta_mono ht_exp_ge
  have h_strict : L * x < chebyshevTheta (Real.exp t) := lt_of_lt_of_le h_theta h_mono
  have h_exp_pos : 0 < Real.exp (-t) := Real.exp_pos (-t)
  nlinarith
}
lemma pntTargetFunc_integral_lower_bound {x L : ℝ} (hL : 1 < L) (hx_pos : 0 < x)
    (h_theta : L * x < chebyshevTheta x)
    (hf_int : IntervalIntegrable pntTargetFunc volume (Real.log x) (Real.log (L * x))) :
    L - 1 - Real.log L ≤ ∫ t in (Real.log x)..(Real.log (L * x)), pntTargetFunc t := by
{
  let g := fun (t : ℝ) => L * x * Real.exp (-t) - 1
  have h_le : ∀ t ∈ Set.Icc (Real.log x) (Real.log (L * x)), g t ≤ pntTargetFunc t := by
  {
    intro t ht
    exact le_of_lt (pntTargetFunc_lower_bound hL hx_pos ht h_theta)
  }
  have hg_int : IntervalIntegrable g volume (Real.log x) (Real.log (L * x)) := by
  {
    have h_cont : Continuous g := by
    {
      apply Continuous.sub
      · apply Continuous.mul continuous_const
        exact Real.continuous_exp.comp continuous_neg
      · exact continuous_const
    }
    exact Continuous.intervalIntegrable h_cont _ _
  }
  have h_log_le : Real.log x ≤ Real.log (L * x) := by
  {
    apply Real.log_le_log hx_pos
    have h_one : 1 * x < L * x := by exact mul_lt_mul_of_pos_right hL hx_pos
    rw [one_mul] at h_one
    exact le_of_lt h_one
  }
  have h_int_le : ∫ t in (Real.log x)..(Real.log (L * x)), g t ≤ ∫ t in (Real.log x)..(Real.log (L * x)), pntTargetFunc t := by
  {
    exact intervalIntegral.integral_mono_on h_log_le hg_int hf_int h_le
  }
  have h_int_g : ∫ t in (Real.log x)..(Real.log (L * x)), g t = L - 1 - Real.log L := by
  {
    have h_deriv : ∀ t ∈ Set.uIcc (Real.log x) (Real.log (L * x)),
      HasDerivAt (fun t => -L * x * Real.exp (-t) - t) (g t) t := by
    {
      intro t ht
      have h0 := HasDerivAt.exp (hasDerivAt_neg t)
      have h1 : HasDerivAt (fun x => Real.exp (-x)) (-Real.exp (-t)) t := by
      {
        have eq : Real.exp (-t) * -1 = -Real.exp (-t) := by ring
        exact HasDerivAt.congr_deriv h0 eq
      }
      have h2 : HasDerivAt (fun t => -L * x * Real.exp (-t)) (-L * x * -Real.exp (-t)) t := by
      {
        exact HasDerivAt.const_mul (-L * x) h1
      }
      have h3 : HasDerivAt (fun t => -L * x * Real.exp (-t) - t) (-L * x * -Real.exp (-t) - 1) t := by
      {
        exact HasDerivAt.sub h2 (hasDerivAt_id t)
      }
      have h_eq : -L * x * -Real.exp (-t) - 1 = g t := by
      {
        dsimp [g]
        ring
      }
      rw [← h_eq]
      exact h3
    }
    have h_eval : ∫ t in (Real.log x)..(Real.log (L * x)), g t
      = (-L * x * Real.exp (-Real.log (L * x)) - Real.log (L * x)) - (-L * x * Real.exp (-Real.log x) - Real.log x) := by
    {
      exact intervalIntegral.integral_eq_sub_of_hasDerivAt h_deriv hg_int
    }
    rw [h_eval]
    have h_exp1 : Real.exp (-Real.log (L * x)) = (L * x)⁻¹ := by
    {
      rw [Real.exp_neg, Real.exp_log (mul_pos (by linarith) hx_pos)]
    }
    have h_exp2 : Real.exp (-Real.log x) = x⁻¹ := by
    {
      rw [Real.exp_neg, Real.exp_log hx_pos]
    }
    have h_log_mul : Real.log (L * x) = Real.log L + Real.log x := by
    {
      exact Real.log_mul (by linarith) (ne_of_gt hx_pos)
    }
    rw [h_exp1, h_exp2, h_log_mul]
    have h_Lx_inv : (L * x)⁻¹ = L⁻¹ * x⁻¹ := mul_inv (L) (x)
    rw [h_Lx_inv]
    have hL0 : L ≠ 0 := by linarith
    have hx0 : x ≠ 0 := by linarith
    calc
      (-L * x * (L⁻¹ * x⁻¹) - (Real.log L + Real.log x)) - (-L * x * x⁻¹ - Real.log x)
        = (- (L * L⁻¹) * (x * x⁻¹) - Real.log L - Real.log x) - (-L * (x * x⁻¹) - Real.log x) := by ring
      _ = (-1 * 1 - Real.log L - Real.log x) - (-L * 1 - Real.log x) := by
      {
        rw [mul_inv_cancel₀ hL0, mul_inv_cancel₀ hx0]
      }
      _ = L - 1 - Real.log L := by ring
  }
  rw [h_int_g] at h_int_le
  exact h_int_le
}

lemma integral_cauchy_of_converges {f : ℝ → ℝ} {I : ℝ}
    (h_conv : Tendsto (fun T => ∫ t in (0:ℝ)..T, f t) atTop (nhds I))
    (hf_int : ∀ T > 0, IntervalIntegrable f volume 0 T)
    (seq_a seq_b : ℕ → ℝ)
    (ha : Tendsto seq_a atTop atTop)
    (ha_pos : ∀ n, 0 < seq_a n)
    (hb : Tendsto seq_b atTop atTop)
    (hb_pos : ∀ n, 0 < seq_b n) :
    Tendsto (fun n => ∫ t in seq_a n..seq_b n, f t) atTop (nhds 0) := by
{
  have h_split : ∀ n, ∫ t in seq_a n..seq_b n, f t = (∫ t in (0:ℝ)..seq_b n, f t) - (∫ t in (0:ℝ)..seq_a n, f t) := by
  {
    intro n
    have h1 := hf_int (seq_a n) (ha_pos n)
    have h2 := hf_int (seq_b n) (hb_pos n)
    have h3 := intervalIntegral.integral_add_adjacent_intervals h1.symm h2
    rw [intervalIntegral.integral_symm] at h3
    linarith
  }
  have h_eq : (fun n => ∫ t in seq_a n..seq_b n, f t) = (fun n => (∫ t in (0:ℝ)..seq_b n, f t) - (∫ t in (0:ℝ)..seq_a n, f t)) := by
  {
    ext n
    exact h_split n
  }
  rw [h_eq]
  have h_tendsto_b : Tendsto (fun n => ∫ t in (0:ℝ)..seq_b n, f t) atTop (nhds I) := Tendsto.comp h_conv hb
  have h_tendsto_a : Tendsto (fun n => ∫ t in (0:ℝ)..seq_a n, f t) atTop (nhds I) := Tendsto.comp h_conv ha
  have h_sub := Tendsto.sub h_tendsto_b h_tendsto_a
  have h_zero : I - I = 0 := sub_self I
  rw [h_zero] at h_sub
  exact h_sub
}

lemma pnt_limsup_contradiction {I : ℝ}
    (hf_conv : Tendsto (fun T => ∫ t in (0:ℝ)..T, pntTargetFunc t) atTop (nhds I))
    (hf_int : ∀ T > 0, IntervalIntegrable pntTargetFunc volume 0 T)
    (h_limsup : ∃ L > 1, ∃ seq : ℕ → ℝ, (∀ n, 1 < seq n) ∧ Tendsto seq atTop atTop ∧ ∀ n, L * seq n < chebyshevTheta (seq n)) :
    False := by
{
  rcases h_limsup with ⟨L, hL, seq, hseq_gt_1, hseq_tendsto, hseq_theta⟩
  
  let seq_a := fun n => Real.log (seq n)
  let seq_b := fun n => Real.log (L * seq n)
  
  have ha_tendsto : Tendsto seq_a atTop atTop := Tendsto.comp Real.tendsto_log_atTop hseq_tendsto
  
  have h_L_pos : 0 < L := by linarith
  have ht : Tendsto (fun n => L * seq n) atTop atTop := Tendsto.const_mul_atTop h_L_pos hseq_tendsto
  have hb_tendsto : Tendsto seq_b atTop atTop := Tendsto.comp Real.tendsto_log_atTop ht
  
  have ha_pos : ∀ n, 0 < seq_a n := by
  {
    intro n
    exact Real.log_pos (hseq_gt_1 n)
  }
  have hb_pos : ∀ n, 0 < seq_b n := by
  {
    intro n
    have h_prod : 1 < L * seq n := by nlinarith [hseq_gt_1 n]
    exact Real.log_pos h_prod
  }
  
  have h_cauchy := integral_cauchy_of_converges hf_conv hf_int seq_a seq_b ha_tendsto ha_pos hb_tendsto hb_pos
  
  have h_lower : ∀ n, L - 1 - Real.log L ≤ ∫ t in seq_a n..seq_b n, pntTargetFunc t := by
  {
    intro n
    have hx_pos : 0 < seq n := by linarith [hseq_gt_1 n]
    have hf_int_n : IntervalIntegrable pntTargetFunc volume (seq_a n) (seq_b n) := by
    {
      have h1 := hf_int (seq_a n) (ha_pos n)
      have h2 := hf_int (seq_b n) (hb_pos n)
      exact h1.symm.trans h2
    }
    exact pntTargetFunc_integral_lower_bound hL hx_pos (hseq_theta n) hf_int_n
  }
  
  have hc : 0 < L - 1 - Real.log L := by
  {
    have h_le : Real.log L < L - 1 := Real.log_lt_sub_one_of_pos (by linarith) (by linarith)
    linarith
  }
  
  -- The sequence of integrals tends to 0, so it must eventually be < hc
  -- But it's bounded below by hc, contradiction!
  have h_ge : 0 ≥ L - 1 - Real.log L := ge_of_tendsto h_cauchy (Eventually.of_forall h_lower)
  linarith
}
