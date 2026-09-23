import Mathlib.Topology.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.Analysis.Calculus.Deriv.Slope

namespace ComplexAnalysis.R2
open Complex Filter Topology

noncomputable def sqNorm (x : ℝ × ℝ) : ℝ := x.1^2 + x.2^2

noncomputable def sqDist (x y : ℝ × ℝ) : ℝ :=
  (x.1 - y.1)^2 + (x.2 - y.2)^2

noncomputable def euclideanNorm (x : ℝ × ℝ) : ℝ :=
  Real.sqrt (sqNorm x)

noncomputable def euclideanDist (x y : ℝ × ℝ) : ℝ :=
  Real.sqrt (sqDist x y)

def LimitRtoR2 (f : ℝ → ℝ × ℝ) (a : ℝ) (L : ℝ × ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → euclideanDist (f x) L < ε

def LimitR2toR (f : ℝ × ℝ → ℝ) (a : ℝ × ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ × ℝ, 0 < euclideanDist x a ∧ euclideanDist x a < δ → |f x - L| < ε

lemma euclideanNorm_nonneg (x : ℝ × ℝ) : 0 ≤ euclideanNorm x := Real.sqrt_nonneg _

def LimitR2toR2 (f : ℝ × ℝ → ℝ × ℝ) (a : ℝ × ℝ) (L : ℝ × ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ × ℝ, 0 < euclideanDist x a ∧ euclideanDist x a < δ → euclideanDist (f x) L < ε

def ConvergesR2 (seq : ℕ → ℝ × ℝ) (L : ℝ × ℝ): Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, euclideanDist (seq n) L < ε

def HasFDerivAt_R2_eps (u v : ℝ × ℝ → ℝ) (ux₀ uy₀ vx₀ vy₀ : ℝ) (a : ℝ × ℝ) : Prop :=
  LimitR2toR (fun h =>
    euclideanNorm (
      (u (a.1 + h.1, a.2 + h.2) - u a) - (ux₀ * h.1 + uy₀ * h.2),
      (v (a.1 + h.1, a.2 + h.2) - v a) - (vx₀ * h.1 + vy₀ * h.2)
    ) / euclideanNorm h
  ) (0, 0) 0

def DifferentiableAt_R2_eps (u v : ℝ × ℝ → ℝ) (a : ℝ × ℝ) : Prop :=
  ∃ (ux₀ uy₀ vx₀ vy₀ : ℝ), HasFDerivAt_R2_eps u v ux₀ uy₀ vx₀ vy₀ a

def HasPartialDerivX_R2_eps (u : ℝ × ℝ → ℝ) (ux₀ : ℝ) (p₀ : ℝ × ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - p₀.1| ∧ |x - p₀.1| < δ →
    |(u (x, p₀.2) - u p₀) / (x - p₀.1) - ux₀| < ε

def HasPartialDerivY_R2_eps (u : ℝ × ℝ → ℝ) (uy₀ : ℝ) (p₀ : ℝ × ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ y : ℝ, 0 < |y - p₀.2| ∧ |y - p₀.2| < δ →
    |(u (p₀.1, y) - u p₀) / (y - p₀.2) - uy₀| < ε

lemma tendsto_nhds_iff_eps_R (f : ℝ → ℝ) (L x₀ : ℝ) :
    Tendsto f (nhdsWithin x₀ {x₀}ᶜ) (nhds L) ↔
    (∀ ε > 0, ∃ δ > 0, ∀ x, 0 < |x - x₀| ∧ |x - x₀| < δ → |f x - L| < ε) := by {
  rw [Metric.tendsto_nhdsWithin_nhds]
  simp only [Set.mem_compl_iff, Set.mem_singleton_iff, dist_eq_norm, Real.norm_eq_abs]
  apply Iff.intro
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x hx
    have h_ne : x ≠ x₀ := by {
      intro contra
      rw [contra, sub_self, abs_zero] at hx
      exact (lt_irrefl 0 hx.1).elim
    }
    exact hδ h_ne hx.2
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x hx1 hx2
    have h_pos : 0 < |x - x₀| := abs_pos.mpr (sub_ne_zero.mpr hx1)
    exact hδ x ⟨h_pos, hx2⟩
}

lemma hasDerivAt_iff_hasPartialDerivX_R2_eps (u : ℝ × ℝ → ℝ) (ux₀ : ℝ) (p₀ : ℝ × ℝ) :
    HasDerivAt (fun x ↦ u (x, p₀.2)) ux₀ p₀.1 ↔ HasPartialDerivX_R2_eps u ux₀ p₀ := by {
  unfold HasPartialDerivX_R2_eps
  rw [hasDerivAt_iff_tendsto_slope]
  unfold slope
  rw [tendsto_nhds_iff_eps_R]
  apply Iff.intro
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x hx
    have h_eq : (x - p₀.1)⁻¹ • ((fun x_1 => u (x_1, p₀.2)) x -ᵥ (fun x => u (x, p₀.2)) p₀.1) = (u (x, p₀.2) - u p₀) / (x - p₀.1) := by {
      simp only [vsub_eq_sub, smul_eq_mul]
      have h_eq2 : u (p₀.1, p₀.2) = u p₀ := rfl
      rw [h_eq2, div_eq_mul_inv, mul_comm]
    }
    have hδx := hδ x hx
    rw [h_eq] at hδx
    exact hδx
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x hx
    have h_eq : (x - p₀.1)⁻¹ • ((fun x_1 => u (x_1, p₀.2)) x -ᵥ (fun x => u (x, p₀.2)) p₀.1) = (u (x, p₀.2) - u p₀) / (x - p₀.1) := by {
      simp only [vsub_eq_sub, smul_eq_mul]
      have h_eq2 : u (p₀.1, p₀.2) = u p₀ := rfl
      rw [h_eq2, div_eq_mul_inv, mul_comm]
    }
    have hδx := hδ x hx
    rw [← h_eq] at hδx
    exact hδx
}

lemma hasDerivAt_iff_hasPartialDerivY_R2_eps (u : ℝ × ℝ → ℝ) (uy₀ : ℝ) (p₀ : ℝ × ℝ) :
    HasDerivAt (fun y ↦ u (p₀.1, y)) uy₀ p₀.2 ↔ HasPartialDerivY_R2_eps u uy₀ p₀ := by {
  unfold HasPartialDerivY_R2_eps
  rw [hasDerivAt_iff_tendsto_slope]
  unfold slope
  rw [tendsto_nhds_iff_eps_R]
  apply Iff.intro
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x hx
    have h_eq : (x - p₀.2)⁻¹ • ((fun y => u (p₀.1, y)) x -ᵥ (fun y => u (p₀.1, y)) p₀.2) = (u (p₀.1, x) - u p₀) / (x - p₀.2) := by {
      simp only [vsub_eq_sub, smul_eq_mul]
      have h_eq2 : u (p₀.1, p₀.2) = u p₀ := rfl
      rw [h_eq2, div_eq_mul_inv, mul_comm]
    }
    have hδx := hδ x hx
    rw [h_eq] at hδx
    exact hδx
  · intro h ε hε
    rcases h ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x hx
    have h_eq : (x - p₀.2)⁻¹ • ((fun y => u (p₀.1, y)) x -ᵥ (fun y => u (p₀.1, y)) p₀.2) = (u (p₀.1, x) - u p₀) / (x - p₀.2) := by {
      simp only [vsub_eq_sub, smul_eq_mul]
      have h_eq2 : u (p₀.1, p₀.2) = u p₀ := rfl
      rw [h_eq2, div_eq_mul_inv, mul_comm]
    }
    have hδx := hδ x hx
    rw [← h_eq] at hδx
    exact hδx
}

lemma hasFDerivAt_of_continuous_partials_eps
    (u ux uy : ℝ × ℝ → ℝ) (G : Set (ℝ × ℝ)) (p : ℝ × ℝ)
    (hG : IsOpen G) (hp : p ∈ G)
    (h_ux : ∀ p ∈ G, HasPartialDerivX_R2_eps u (ux p) p)
    (h_uy : ∀ p ∈ G, HasPartialDerivY_R2_eps u (uy p) p)
    (h_cont_ux : ContinuousOn ux G)
    (h_cont_uy : ContinuousOn uy G) :
    HasFDerivAt u (
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (ux p)).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (uy p)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)
    ) p := by
{
  let f1 : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun x y => ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (ux (x, y))
  let f2 : ℝ → ℝ → ℝ →L[ℝ] ℝ := fun x y => ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (uy (x, y))
  have hf1 : ∀ᶠ q in 𝓝 p, HasFDerivAt (fun x => u (x, q.2)) (f1 q.1 q.2) q.1 := by {
    apply Filter.eventually_of_mem (hG.mem_nhds hp)
    intro q hq
    have h_deriv : HasDerivAt (fun x => u (x, q.2)) (ux q) q.1 :=
      (hasDerivAt_iff_hasPartialDerivX_R2_eps u (ux q) q).mpr (h_ux q hq)
    exact h_deriv.hasFDerivAt
  }
  have hf2 : ∀ᶠ q in 𝓝 p, HasFDerivAt (fun y => u (q.1, y)) (f2 q.1 q.2) q.2 := by {
    apply Filter.eventually_of_mem (hG.mem_nhds hp)
    intro q hq
    have h_deriv : HasDerivAt (fun y => u (q.1, y)) (uy q) q.2 :=
      (hasDerivAt_iff_hasPartialDerivY_R2_eps u (uy q) q).mpr (h_uy q hq)
    exact h_deriv.hasFDerivAt
  }
  have hc1 : ContinuousAt ↿f1 p := by {
    have h_cont_ux_p : ContinuousAt ux p := (ContinuousOn.continuousAt h_cont_ux (hG.mem_nhds hp))
    have h_smul : Continuous (fun (c : ℝ) => ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) c) :=
      (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (ContinuousLinearMap.id ℝ ℝ)).continuous
    exact h_smul.continuousAt.comp h_cont_ux_p
  }
  have hc2 : ContinuousAt ↿f2 p := by {
    have h_cont_uy_p : ContinuousAt uy p := (ContinuousOn.continuousAt h_cont_uy (hG.mem_nhds hp))
    have h_smul : Continuous (fun (c : ℝ) => ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) c) :=
      (ContinuousLinearMap.smulRightL ℝ ℝ ℝ (ContinuousLinearMap.id ℝ ℝ)).continuous
    exact h_smul.continuousAt.comp h_cont_uy_p
  }
  have h_strict := hasStrictFDerivAt_uncurry_coprod (u := p) (f := fun x y => u (x, y)) (f₁ := f1) (f₂ := f2) hf1 hf2 hc1 hc2
  exact h_strict.hasFDerivAt
}

lemma contDiffAt_one_of_continuous_partials_eps
    (u ux uy : ℝ × ℝ → ℝ) (G : Set (ℝ × ℝ)) (p : ℝ × ℝ)
    (hG : IsOpen G) (hp : p ∈ G)
    (h_ux : ∀ q ∈ G, HasPartialDerivX_R2_eps u (ux q) q)
    (h_uy : ∀ q ∈ G, HasPartialDerivY_R2_eps u (uy q) q)
    (h_cont_ux : ContinuousOn ux G)
    (h_cont_uy : ContinuousOn uy G) :
    ContDiffAt ℝ 1 u p := by {
  let f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ := fun q =>
    ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) (ux q) +
    ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) (uy q)
  rw [contDiffAt_one_iff]
  use f'
  have h_nhd : G ∈ 𝓝 p := hG.mem_nhds hp
  refine ⟨G, h_nhd, ?_, ?_⟩
  · have h_smul1 : Continuous (fun (c : ℝ) => ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) c) := 
      (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ (ContinuousLinearMap.fst ℝ ℝ ℝ)).continuous
    have h_smul2 : Continuous (fun (c : ℝ) => ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) c) := 
      (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ (ContinuousLinearMap.snd ℝ ℝ ℝ)).continuous
    have h_comp1 : ContinuousOn (fun q => ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) (ux q)) G := h_smul1.comp_continuousOn h_cont_ux
    have h_comp2 : ContinuousOn (fun q => ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) (uy q)) G := h_smul2.comp_continuousOn h_cont_uy
    exact h_comp1.add h_comp2
  · intro q hq
    have H : f' q = 
      ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (ux q)).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (uy q)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by {
      apply ContinuousLinearMap.ext
      intro v
      simp only [f', ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    }
    rw [H]
    exact hasFDerivAt_of_continuous_partials_eps u ux uy G q hG hq h_ux h_uy h_cont_ux h_cont_uy
}

lemma contDiffAt_two_of_continuous_second_partials_eps
    (u ux uy uxx uxy uyx uyy : ℝ × ℝ → ℝ) (G : Set (ℝ × ℝ)) (p : ℝ × ℝ)
    (hG : IsOpen G) (hp : p ∈ G)
    (h_ux : ∀ q ∈ G, HasPartialDerivX_R2_eps u (ux q) q)
    (h_uy : ∀ q ∈ G, HasPartialDerivY_R2_eps u (uy q) q)
    (h_uxx : ∀ q ∈ G, HasPartialDerivX_R2_eps ux (uxx q) q)
    (h_uxy : ∀ q ∈ G, HasPartialDerivY_R2_eps ux (uxy q) q)
    (h_uyx : ∀ q ∈ G, HasPartialDerivX_R2_eps uy (uyx q) q)
    (h_uyy : ∀ q ∈ G, HasPartialDerivY_R2_eps uy (uyy q) q)
    (h_cont_ux : ContinuousOn ux G)
    (h_cont_uy : ContinuousOn uy G)
    (h_cont_uxx : ContinuousOn uxx G)
    (h_cont_uxy : ContinuousOn uxy G)
    (h_cont_uyx : ContinuousOn uyx G)
    (h_cont_uyy : ContinuousOn uyy G) :
    ContDiffAt ℝ 2 u p := by {
  let f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ := fun q =>
    ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) (ux q) +
    ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) (uy q)
  change ContDiffAt ℝ (↑(1 : ℕ) + 1) u p
  rw [contDiffAt_succ_iff_hasFDerivAt]
  use f'
  constructor
  · have h_nhd : G ∈ 𝓝 p := hG.mem_nhds hp
    use G, h_nhd
    intro q hq
    have H : f' q = 
      ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (ux q)).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (uy q)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by {
      apply ContinuousLinearMap.ext
      intro v
      simp only [f', ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    }
    rw [H]
    exact hasFDerivAt_of_continuous_partials_eps u ux uy G q hG hq h_ux h_uy h_cont_ux h_cont_uy
  · have H1 : ContDiffAt ℝ 1 ux p := 
      contDiffAt_one_of_continuous_partials_eps ux uxx uxy G p hG hp h_uxx h_uxy h_cont_uxx h_cont_uxy
    have H2 : ContDiffAt ℝ 1 uy p := 
      contDiffAt_one_of_continuous_partials_eps uy uyx uyy G p hG hp h_uyx h_uyy h_cont_uyx h_cont_uyy
    have h_L1 : ContDiff ℝ 1 (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ (ContinuousLinearMap.fst ℝ ℝ ℝ)) := 
      (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ (ContinuousLinearMap.fst ℝ ℝ ℝ)).contDiff
    have H1' : ContDiffAt ℝ 1 (fun q => ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) (ux q)) p := 
      h_L1.contDiffAt.comp p H1
    have h_L2 : ContDiff ℝ 1 (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ (ContinuousLinearMap.snd ℝ ℝ ℝ)) := 
      (ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ (ContinuousLinearMap.snd ℝ ℝ ℝ)).contDiff
    have H2' : ContDiffAt ℝ 1 (fun q => ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) (uy q)) p := 
      h_L2.contDiffAt.comp p H2
    exact H1'.add H2'
}

lemma mixed_partials_eq_eps
    (u ux uy uxx uxy uyx uyy : ℝ × ℝ → ℝ) (G : Set (ℝ × ℝ)) (p : ℝ × ℝ)
    (hG : IsOpen G) (hp : p ∈ G)
    (h_ux : ∀ q ∈ G, HasPartialDerivX_R2_eps u (ux q) q)
    (h_uy : ∀ q ∈ G, HasPartialDerivY_R2_eps u (uy q) q)
    (h_uxx : ∀ q ∈ G, HasPartialDerivX_R2_eps ux (uxx q) q)
    (h_uxy : ∀ q ∈ G, HasPartialDerivY_R2_eps ux (uxy q) q)
    (h_uyx : ∀ q ∈ G, HasPartialDerivX_R2_eps uy (uyx q) q)
    (h_uyy : ∀ q ∈ G, HasPartialDerivY_R2_eps uy (uyy q) q)
    (h_cont_ux : ContinuousOn ux G)
    (h_cont_uy : ContinuousOn uy G)
    (h_cont_uxx : ContinuousOn uxx G)
    (h_cont_uxy : ContinuousOn uxy G)
    (h_cont_uyx : ContinuousOn uyx G)
    (h_cont_uyy : ContinuousOn uyy G) :
    uxy p = uyx p := by {
  have H := contDiffAt_two_of_continuous_second_partials_eps u ux uy uxx uxy uyx uyy G p hG hp h_ux h_uy h_uxx h_uxy h_uyx h_uyy h_cont_ux h_cont_uy h_cont_uxx h_cont_uxy h_cont_uyx h_cont_uyy
  have Hsymm := H.isSymmSndFDerivAt (by norm_num)
  have H_eq := Hsymm.eq (0, 1) (1, 0)
  let f' : ℝ × ℝ → ℝ × ℝ →L[ℝ] ℝ := fun q =>
    ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) (ux q) +
    ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) (uy q)
  have h_fderiv_eq : ∀ q ∈ G, fderiv ℝ u q = f' q := by {
    intro q hq
    have H_fderiv := hasFDerivAt_of_continuous_partials_eps u ux uy G q hG hq h_ux h_uy h_cont_ux h_cont_uy
    -- we need f' q to match exactly the map in H_fderiv
    have H_map : f' q = 
      ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (ux q)).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (uy q)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by {
      apply ContinuousLinearMap.ext
      intro v
      simp only [f', ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    }
    rw [H_map]
    exact H_fderiv.fderiv
  }
  have h_eventually_eq : fderiv ℝ u =ᶠ[𝓝 p] f' := Filter.eventuallyEq_iff_exists_mem.mpr ⟨G, hG.mem_nhds hp, h_fderiv_eq⟩
  have H_fderiv2 : fderiv ℝ (fderiv ℝ u) p = fderiv ℝ f' p := Filter.EventuallyEq.fderiv_eq h_eventually_eq
  
  let f_ux' : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) (uxx p) + ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) (uxy p)
  let f_uy' : ℝ × ℝ →L[ℝ] ℝ := ContinuousLinearMap.smulRight (ContinuousLinearMap.fst ℝ ℝ ℝ) (uyx p) + ContinuousLinearMap.smulRight (ContinuousLinearMap.snd ℝ ℝ ℝ) (uyy p)
  
  have H_ux_deriv := hasFDerivAt_of_continuous_partials_eps ux uxx uxy G p hG hp h_uxx h_uxy h_cont_uxx h_cont_uxy
  have H_uy_deriv := hasFDerivAt_of_continuous_partials_eps uy uyx uyy G p hG hp h_uyx h_uyy h_cont_uyx h_cont_uyy
  
  have H_ux_deriv2 : HasFDerivAt ux f_ux' p := by {
    have H_map : f_ux' = 
      ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (uxx p)).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (uxy p)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by {
      apply ContinuousLinearMap.ext
      intro v
      simp only [f_ux', ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    }
    rw [H_map]
    exact H_ux_deriv
  }
  have H_uy_deriv2 : HasFDerivAt uy f_uy' p := by {
    have H_map : f_uy' = 
      ((ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (uyx p)).comp (ContinuousLinearMap.fst ℝ ℝ ℝ) +
      (ContinuousLinearMap.smulRight (ContinuousLinearMap.id ℝ ℝ) (uyy p)).comp (ContinuousLinearMap.snd ℝ ℝ ℝ)) := by {
      apply ContinuousLinearMap.ext
      intro v
      simp only [f_uy', ContinuousLinearMap.add_apply, ContinuousLinearMap.smulRight_apply,
        ContinuousLinearMap.comp_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
    }
    rw [H_map]
    exact H_uy_deriv
  }
  let L1 : ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ) := ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ (ContinuousLinearMap.fst ℝ ℝ ℝ)
  let L2 : ℝ →L[ℝ] (ℝ × ℝ →L[ℝ] ℝ) := ContinuousLinearMap.smulRightL ℝ (ℝ × ℝ) ℝ (ContinuousLinearMap.snd ℝ ℝ ℝ)
  
  have h_L1_deriv : HasFDerivAt L1 L1 (ux p) := L1.hasFDerivAt
  have h_L2_deriv : HasFDerivAt L2 L2 (uy p) := L2.hasFDerivAt
  
  have H_f1_deriv : HasFDerivAt (fun q => L1 (ux q)) (L1.comp f_ux') p := 
    HasFDerivAt.comp p h_L1_deriv H_ux_deriv2
  have H_f2_deriv : HasFDerivAt (fun q => L2 (uy q)) (L2.comp f_uy') p := 
    HasFDerivAt.comp p h_L2_deriv H_uy_deriv2
    
  have H_f'_deriv : HasFDerivAt f' (L1.comp f_ux' + L2.comp f_uy') p := 
    HasFDerivAt.add H_f1_deriv H_f2_deriv
    
  have H_fderiv3 : fderiv ℝ f' p = (L1.comp f_ux' + L2.comp f_uy') := H_f'_deriv.fderiv
  
  -- Now we evaluate both sides of H_eq at (0, 1) and (1, 0)
  have H_val1 : fderiv ℝ (fderiv ℝ u) p (0, 1) (1, 0) = uxy p := by {
    rw [H_fderiv2, H_fderiv3]
    change (1 : ℝ) * ((0 : ℝ) * uxx p + (1 : ℝ) * uxy p) + (0 : ℝ) * ((0 : ℝ) * uyx p + (1 : ℝ) * uyy p) = uxy p
    ring
  }
  have H_val2 : fderiv ℝ (fderiv ℝ u) p (1, 0) (0, 1) = uyx p := by {
    rw [H_fderiv2, H_fderiv3]
    change (0 : ℝ) * ((1 : ℝ) * uxx p + (0 : ℝ) * uxy p) + (1 : ℝ) * ((1 : ℝ) * uyx p + (0 : ℝ) * uyy p) = uyx p
    ring
  }
  rw [H_val1, H_val2] at H_eq
  exact H_eq
}

/-- A real-valued function of two real variables is harmonic on an open set G
if its first and second partial derivatives are continuous and satisfy Laplace's equation. -/
def Harmonic_R2_eps (u : ℝ × ℝ → ℝ) (G : Set (ℝ × ℝ)) : Prop :=
  IsOpen G ∧
  ∃ (ux uy uxx uxy uyx uyy : ℝ × ℝ → ℝ),
    (∀ p ∈ G, HasPartialDerivX_R2_eps u (ux p) p) ∧
    (∀ p ∈ G, HasPartialDerivY_R2_eps u (uy p) p) ∧
    (ContinuousOn ux G) ∧
    (ContinuousOn uy G) ∧
    (∀ p ∈ G, HasPartialDerivX_R2_eps ux (uxx p) p) ∧
    (∀ p ∈ G, HasPartialDerivY_R2_eps ux (uxy p) p) ∧
    (∀ p ∈ G, HasPartialDerivX_R2_eps uy (uyx p) p) ∧
    (∀ p ∈ G, HasPartialDerivY_R2_eps uy (uyy p) p) ∧
    (ContinuousOn uxx G) ∧
    (ContinuousOn uxy G) ∧
    (ContinuousOn uyx G) ∧
    (ContinuousOn uyy G) ∧
    (∀ p ∈ G, uxx p + uyy p = 0)

lemma HasFDerivAt_R2_eps_iff (u v : ℝ × ℝ → ℝ) (ux₀ uy₀ vx₀ vy₀ : ℝ) (a : ℝ × ℝ) :
  HasFDerivAt_R2_eps u v ux₀ uy₀ vx₀ vy₀ a ↔
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ × ℝ,
    0 < euclideanDist x a ∧ euclideanDist x a < δ →
    euclideanNorm (u x - u a - (ux₀ * (x.1 - a.1) + uy₀ * (x.2 - a.2)),
                   v x - v a - (vx₀ * (x.1 - a.1) + vy₀ * (x.2 - a.2))) < ε * euclideanDist x a := by
{
  unfold HasFDerivAt_R2_eps LimitR2toR
  apply Iff.intro
  · intro h_lim ε hε
    rcases h_lim ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro x hx
    let h := (x.1 - a.1, x.2 - a.2)
    have h_h_dist : euclideanDist h (0,0) = euclideanDist x a := by {
      dsimp [euclideanDist, sqDist, sqNorm, h]
      congr 1
      ring_nf
    }
    have h_norm_h : euclideanNorm h = euclideanDist x a := by {
      dsimp [euclideanNorm, sqNorm, euclideanDist, sqDist, h]
    }
    have hx_h : 0 < euclideanDist h (0,0) ∧ euclideanDist h (0,0) < δ := by {
      rw [h_h_dist]
      exact hx
    }
    have h_limit := hδ h hx_h
    dsimp only at h_limit
    have h_err_x : a.1 + h.1 = x.1 := by { dsimp [h]; ring }
    have h_err_y : a.2 + h.2 = x.2 := by { dsimp [h]; ring }
    have h_err : euclideanNorm ((u (a.1 + h.1, a.2 + h.2) - u a) - (ux₀ * h.1 + uy₀ * h.2), (v (a.1 + h.1, a.2 + h.2) - v a) - (vx₀ * h.1 + vy₀ * h.2)) = euclideanNorm (u x - u a - (ux₀ * (x.1 - a.1) + uy₀ * (x.2 - a.2)), v x - v a - (vx₀ * (x.1 - a.1) + vy₀ * (x.2 - a.2))) := by {
      rw [h_err_x, h_err_y]
    }
    rw [h_err, h_norm_h] at h_limit
    have h_norm_nonneg : 0 ≤ euclideanNorm (u x - u a - (ux₀ * (x.1 - a.1) + uy₀ * (x.2 - a.2)), v x - v a - (vx₀ * (x.1 - a.1) + vy₀ * (x.2 - a.2))) / euclideanDist x a := by {
      have h1 : 0 ≤ euclideanNorm (u x - u a - (ux₀ * (x.1 - a.1) + uy₀ * (x.2 - a.2)), v x - v a - (vx₀ * (x.1 - a.1) + vy₀ * (x.2 - a.2))) := euclideanNorm_nonneg _
      have h2 : 0 < euclideanDist x a := hx.1
      exact div_nonneg h1 (le_of_lt h2)
    }
    rw [sub_zero, abs_of_nonneg h_norm_nonneg] at h_limit
    have h_pos : 0 < euclideanDist x a := hx.1
    exact (div_lt_iff₀ h_pos).mp h_limit
  · intro h_eps ε hε
    rcases h_eps ε hε with ⟨δ, hδ_pos, hδ⟩
    use δ, hδ_pos
    intro h hh
    let x := (a.1 + h.1, a.2 + h.2)
    have h_x_dist : euclideanDist x a = euclideanDist h (0,0) := by {
      dsimp [euclideanDist, sqDist, sqNorm, x]
      congr 1
      ring_nf
    }
    have h_norm_h : euclideanNorm h = euclideanDist h (0,0) := by {
      dsimp [euclideanNorm, sqNorm, euclideanDist, sqDist, x]
      congr 1
      ring_nf
    }
    have hh_x : 0 < euclideanDist x a ∧ euclideanDist x a < δ := by {
      rw [h_x_dist]
      exact hh
    }
    have h_eps_bound := hδ x hh_x
    have h_err_x : x.1 - a.1 = h.1 := by { dsimp [x]; ring }
    have h_err_y : x.2 - a.2 = h.2 := by { dsimp [x]; ring }
    have h_err : euclideanNorm (u x - u a - (ux₀ * (x.1 - a.1) + uy₀ * (x.2 - a.2)), v x - v a - (vx₀ * (x.1 - a.1) + vy₀ * (x.2 - a.2))) = euclideanNorm ((u (a.1 + h.1, a.2 + h.2) - u a) - (ux₀ * h.1 + uy₀ * h.2), (v (a.1 + h.1, a.2 + h.2) - v a) - (vx₀ * h.1 + vy₀ * h.2)) := by {
      rw [h_err_x, h_err_y]
    }
    rw [h_err, h_x_dist, ← h_norm_h] at h_eps_bound
    have h_pos : 0 < euclideanNorm h := by {
      rw [h_norm_h]
      exact hh.1
    }
    have h_div := (div_lt_iff₀ h_pos).mpr h_eps_bound
    have h_norm_nonneg : 0 ≤ euclideanNorm ((u (a.1 + h.1, a.2 + h.2) - u a) - (ux₀ * h.1 + uy₀ * h.2), (v (a.1 + h.1, a.2 + h.2) - v a) - (vx₀ * h.1 + vy₀ * h.2)) / euclideanNorm h := by {
      have h1 : 0 ≤ euclideanNorm ((u (a.1 + h.1, a.2 + h.2) - u a) - (ux₀ * h.1 + uy₀ * h.2), (v (a.1 + h.1, a.2 + h.2) - v a) - (vx₀ * h.1 + vy₀ * h.2)) := euclideanNorm_nonneg _
      exact div_nonneg h1 (le_of_lt h_pos)
    }
    rw [sub_zero, abs_of_nonneg h_norm_nonneg]
    exact h_div
}

def HasDerivAt_RtoR2_eps (f : ℝ → ℝ × ℝ) (f'₀ : ℝ × ℝ) (t₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 < |t - t₀| ∧ |t - t₀| < δ →
    euclideanDist (f t) (f t₀ + (f'₀.1 * (t - t₀), f'₀.2 * (t - t₀))) < ε * |t - t₀|

lemma euclideanNorm_eq_norm (x : ℝ × ℝ) :
  euclideanNorm x = ‖Complex.mk x.1 x.2‖ := by {
  unfold euclideanNorm sqNorm
  have h_norm : ‖Complex.mk x.1 x.2‖ = Real.sqrt (x.1^2 + x.2^2) := by {
    rw [Complex.norm_def]
    unfold normSq
    dsimp
    congr 1
    ring
  }
  rw [h_norm]
}

lemma euclideanNormTriangle (x y : ℝ × ℝ) :
  euclideanNorm (x.1 + y.1, x.2 + y.2) ≤ euclideanNorm x + euclideanNorm y := by {
  rw [euclideanNorm_eq_norm, euclideanNorm_eq_norm x, euclideanNorm_eq_norm y]
  have h_add : Complex.mk (x.1 + y.1) (x.2 + y.2) = Complex.mk x.1 x.2 + Complex.mk y.1 y.2 := by {
    apply Complex.ext <;> simp
  }
  rw [h_add]
  exact norm_add_le (Complex.mk x.1 x.2) (Complex.mk y.1 y.2)
}

lemma euclideanDistTriangle (x y z : ℝ × ℝ) :
    euclideanDist x z ≤ euclideanDist x y + euclideanDist y z := by {
  unfold euclideanDist sqDist
  have h1 : x.1 - z.1 = x.1 - y.1 + (y.1 - z.1) := by ring
  have h2 : x.2 - z.2 = x.2 - y.2 + (y.2 - z.2) := by ring
  have h_norm := euclideanNormTriangle (x.1 - y.1, x.2 - y.2) (y.1 - z.1, y.2 - z.2)
  unfold euclideanNorm sqNorm at h_norm
  dsimp at h_norm
  rw [h1, h2]
  exact h_norm
}

lemma euclideanDist_nonneg (x y : ℝ × ℝ) : 0 ≤ euclideanDist x y := by {
  unfold euclideanDist sqDist
  exact Real.sqrt_nonneg _
}

lemma locally_lipschitz_of_hasDerivAt_RtoR2_eps {γ : ℝ → ℝ × ℝ} {γ' : ℝ × ℝ} {t₀ : ℝ}
    (hγ_diff : HasDerivAt_RtoR2_eps γ γ' t₀) :
    ∃ K > 0, ∃ δ > 0, ∀ t : ℝ, |t - t₀| < δ →
      euclideanDist (γ t) (γ t₀) ≤ K * |t - t₀| := by {
  unfold HasDerivAt_RtoR2_eps at hγ_diff
  have h1 := hγ_diff 1 (by norm_num)
  rcases h1 with ⟨δ, hδ_pos, hδ⟩

  -- We'll use K = euclideanNorm γ' + 1
  set K := euclideanNorm γ' + 1
  have hK_pos : K > 0 := by {
    have h_norm_nonneg : 0 ≤ euclideanNorm γ' := by {
      unfold euclideanNorm sqNorm
      exact Real.sqrt_nonneg _
    }
    linarith
  }

  use K, hK_pos, δ, hδ_pos
  intro t ht

  by_cases ht_eq : t = t₀
  · rw [ht_eq]
    have h_dist_0 : euclideanDist (γ t₀) (γ t₀) = 0 := by {
      unfold euclideanDist sqDist
      simp
    }
    rw [h_dist_0, sub_self, abs_zero, mul_zero]

  · have ht_pos : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr ht_eq)
    have h_bound := hδ t ⟨ht_pos, ht⟩

    have h_triangle : euclideanDist (γ t) (γ t₀) ≤ euclideanDist (γ t) (γ t₀ + (γ'.1 * (t - t₀), γ'.2 * (t - t₀))) + euclideanDist (γ t₀ + (γ'.1 * (t - t₀), γ'.2 * (t - t₀))) (γ t₀) := euclideanDistTriangle _ _ _

    have h_dist_L : euclideanDist (γ t₀ + (γ'.1 * (t - t₀), γ'.2 * (t - t₀))) (γ t₀) = euclideanNorm γ' * |t - t₀| := by {
      unfold euclideanDist sqDist euclideanNorm sqNorm
      dsimp
      have h1 : (γ t₀).1 + γ'.1 * (t - t₀) - (γ t₀).1 = γ'.1 * (t - t₀) := by ring
      have h2 : (γ t₀).2 + γ'.2 * (t - t₀) - (γ t₀).2 = γ'.2 * (t - t₀) := by ring
      rw [h1, h2]
      have h3 : (γ'.1 * (t - t₀))^2 = γ'.1^2 * (t - t₀)^2 := by ring
      have h4 : (γ'.2 * (t - t₀))^2 = γ'.2^2 * (t - t₀)^2 := by ring
      rw [h3, h4]
      have h5 : γ'.1^2 * (t - t₀)^2 + γ'.2^2 * (t - t₀)^2 = (γ'.1^2 + γ'.2^2) * (t - t₀)^2 := by ring
      rw [h5]
      rw [Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_sq_eq_abs]
    }

    have h_bound2 : euclideanDist (γ t) (γ t₀ + (γ'.1 * (t - t₀), γ'.2 * (t - t₀))) + euclideanDist (γ t₀ + (γ'.1 * (t - t₀), γ'.2 * (t - t₀))) (γ t₀) < 1 * |t - t₀| + euclideanNorm γ' * |t - t₀| := by {
      rw [h_dist_L]
      linarith
    }

    have h_bound3 : 1 * |t - t₀| + euclideanNorm γ' * |t - t₀| = K * |t - t₀| := by {
      calc 1 * |t - t₀| + euclideanNorm γ' * |t - t₀|
        _ = (1 + euclideanNorm γ') * |t - t₀| := by ring
        _ = K * |t - t₀| := by {
          congr 1
          change 1 + euclideanNorm γ' = euclideanNorm γ' + 1
          ring
        }
    }

    rw [h_bound3] at h_bound2
    exact le_of_lt (lt_of_le_of_lt h_triangle h_bound2)
}

lemma abs_le_euclideanNorm_1 (x y : ℝ) : |x| ≤ euclideanNorm (x, y) := by {
  unfold euclideanNorm sqNorm
  have h1 : x^2 ≤ x^2 + y^2 := by {
    have h_y_sq : 0 ≤ y^2 := sq_nonneg y
    linarith
  }
  have h2 : Real.sqrt (x^2) ≤ Real.sqrt (x^2 + y^2) := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq_eq_abs] at h2
  exact h2
}

lemma abs_le_euclideanNorm_2 (x y : ℝ) : |y| ≤ euclideanNorm (x, y) := by {
  unfold euclideanNorm sqNorm
  have h1 : y^2 ≤ x^2 + y^2 := by {
    have h_x_sq : 0 ≤ x^2 := sq_nonneg x
    linarith
  }
  have h2 : Real.sqrt (y^2) ≤ Real.sqrt (x^2 + y^2) := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq_eq_abs] at h2
  exact h2
}

lemma euclideanNorm_le_abs_add (x y : ℝ) : euclideanNorm (x, y) ≤ |x| + |y| := by {
  unfold euclideanNorm sqNorm
  have h1 : x^2 + y^2 ≤ (|x| + |y|)^2 := by {
    have h_expand : (|x| + |y|)^2 = |x|^2 + 2 * |x| * |y| + |y|^2 := by ring
    have h_x_sq : |x|^2 = x^2 := sq_abs x
    have h_y_sq : |y|^2 = y^2 := sq_abs y
    rw [h_expand, h_x_sq, h_y_sq]
    have h_nonneg : 0 ≤ 2 * |x| * |y| := by positivity
    linarith
  }
  have h2 : Real.sqrt (x^2 + y^2) ≤ Real.sqrt ((|x| + |y|)^2) := Real.sqrt_le_sqrt h1
  have h_abs_nonneg : 0 ≤ |x| + |y| := by positivity
  rw [Real.sqrt_sq h_abs_nonneg] at h2
  exact h2
}

lemma matrix_bound (ux₀ uy₀ vx₀ vy₀ x y : ℝ) :
  euclideanNorm (ux₀ * x + uy₀ * y, vx₀ * x + vy₀ * y) ≤
  (|ux₀| + |uy₀| + |vx₀| + |vy₀|) * euclideanNorm (x, y) := by {
  have h1 := euclideanNorm_le_abs_add (ux₀ * x + uy₀ * y) (vx₀ * x + vy₀ * y)
  have h2 : |ux₀ * x + uy₀ * y| ≤ |ux₀ * x| + |uy₀ * y| := abs_add_le _ _
  have h3 : |vx₀ * x + vy₀ * y| ≤ |vx₀ * x| + |vy₀ * y| := abs_add_le _ _
  have h_mul1 : |ux₀ * x| = |ux₀| * |x| := abs_mul _ _
  have h_mul2 : |uy₀ * y| = |uy₀| * |y| := abs_mul _ _
  have h_mul3 : |vx₀ * x| = |vx₀| * |x| := abs_mul _ _
  have h_mul4 : |vy₀ * y| = |vy₀| * |y| := abs_mul _ _
  rw [h_mul1, h_mul2] at h2
  rw [h_mul3, h_mul4] at h3

  have hx_le := abs_le_euclideanNorm_1 x y
  have hy_le := abs_le_euclideanNorm_2 x y

  have h_term1 : |ux₀| * |x| ≤ |ux₀| * euclideanNorm (x, y) := mul_le_mul_of_nonneg_left hx_le (abs_nonneg _)
  have h_term2 : |uy₀| * |y| ≤ |uy₀| * euclideanNorm (x, y) := mul_le_mul_of_nonneg_left hy_le (abs_nonneg _)
  have h_term3 : |vx₀| * |x| ≤ |vx₀| * euclideanNorm (x, y) := mul_le_mul_of_nonneg_left hx_le (abs_nonneg _)
  have h_term4 : |vy₀| * |y| ≤ |vy₀| * euclideanNorm (x, y) := mul_le_mul_of_nonneg_left hy_le (abs_nonneg _)

  have h_sum_le : |ux₀ * x + uy₀ * y| + |vx₀ * x + vy₀ * y| ≤ |ux₀| * euclideanNorm (x, y) + |uy₀| * euclideanNorm (x, y) + |vx₀| * euclideanNorm (x, y) + |vy₀| * euclideanNorm (x, y) := by {
    linarith
  }

  have h_distrib : |ux₀| * euclideanNorm (x, y) + |uy₀| * euclideanNorm (x, y) + |vx₀| * euclideanNorm (x, y) + |vy₀| * euclideanNorm (x, y) = (|ux₀| + |uy₀| + |vx₀| + |vy₀|) * euclideanNorm (x, y) := by ring
  rw [h_distrib] at h_sum_le

  exact le_trans h1 h_sum_le
}

lemma chain_rule_R2 {u v : ℝ × ℝ → ℝ} {ux₀ uy₀ vx₀ vy₀ : ℝ} {a : ℝ × ℝ}
    (h_diff : HasFDerivAt_R2_eps u v ux₀ uy₀ vx₀ vy₀ a)
    (γ : ℝ → ℝ × ℝ) (t₀ : ℝ) (hγ_a : γ t₀ = a)
    (γ' : ℝ × ℝ) (hγ_diff : HasDerivAt_RtoR2_eps γ γ' t₀) :
    HasDerivAt_RtoR2_eps (fun t => (u (γ t), v (γ t)))
      (ux₀ * γ'.1 + uy₀ * γ'.2, vx₀ * γ'.1 + vy₀ * γ'.2) t₀ := by {
  unfold HasDerivAt_RtoR2_eps at *
  intro ε hε

  -- The matrix operator norm is M.
  set M := |ux₀| + |uy₀| + |vx₀| + |vy₀| + 1
  have hM_pos : M > 0 := by {
    have h1 : 0 ≤ |ux₀| + |uy₀| + |vx₀| + |vy₀| := by positivity
    linarith
  }

  -- K is the Lipschitz constant of γ near t₀.
  have h_lip := locally_lipschitz_of_hasDerivAt_RtoR2_eps hγ_diff
  rcases h_lip with ⟨K, hK_pos, δ_lip, hδ_lip_pos, hδ_lip⟩

  -- We'll split ε into ε / (2 * K) for u, v and ε / (2 * M) for γ.
  have hε1_pos : ε / (2 * K) > 0 := div_pos hε (mul_pos (by norm_num) hK_pos)
  have hε2_pos : ε / (2 * M) > 0 := div_pos hε (mul_pos (by norm_num) hM_pos)

  rw [HasFDerivAt_R2_eps_iff] at h_diff
  rcases h_diff (ε / (2 * K)) hε1_pos with ⟨δ1, hδ1_pos, hδ1⟩
  rcases hγ_diff (ε / (2 * M)) hε2_pos with ⟨δ2, hδ2_pos, hδ2⟩

  -- We also need δ so that K * |t - t₀| < δ1. Let δ3 = δ1 / K.
  set δ3 := δ1 / K
  have hδ3_pos : δ3 > 0 := div_pos hδ1_pos hK_pos

  -- Our final δ is the min of δ_lip, δ2, and δ3.
  set δ := min (min δ_lip δ2) δ3
  have hδ_pos : δ > 0 := lt_min (lt_min hδ_lip_pos hδ2_pos) hδ3_pos

  use δ, hδ_pos
  intro t ht

  have h_target : euclideanDist ((fun t => (u (γ t), v (γ t))) t)
      ((fun t => (u (γ t), v (γ t))) t₀ +
        ((ux₀ * γ'.1 + uy₀ * γ'.2, vx₀ * γ'.1 + vy₀ * γ'.2).1 * (t - t₀),
          (ux₀ * γ'.1 + uy₀ * γ'.2, vx₀ * γ'.1 + vy₀ * γ'.2).2 * (t - t₀))) =
      euclideanDist (u (γ t), v (γ t)) (u a + (ux₀ * γ'.1 + uy₀ * γ'.2) * (t - t₀), v a + (vx₀ * γ'.1 + vy₀ * γ'.2) * (t - t₀)) := by {
    dsimp
    rw [hγ_a]
  }
  rw [h_target]

  have ht_lip : |t - t₀| < δ_lip := by {
    have h1 : δ ≤ min δ_lip δ2 := min_le_left _ _
    have h2 : min δ_lip δ2 ≤ δ_lip := min_le_left _ _
    linarith
  }
  have ht2 : |t - t₀| < δ2 := by {
    have h1 : δ ≤ min δ_lip δ2 := min_le_left _ _
    have h2 : min δ_lip δ2 ≤ δ2 := min_le_right _ _
    linarith
  }
  have ht3 : |t - t₀| < δ3 := by {
    have h1 : δ ≤ δ3 := min_le_right _ _
    linarith
  }

  have h_lip_bound := hδ_lip t ht_lip
  have h_γ_bound := hδ2 t ⟨ht.1, ht2⟩

  -- error terms
  set err_γ := (γ t).1 - ((γ t₀).1 + γ'.1 * (t - t₀))
  set err_γ_2 := (γ t).2 - ((γ t₀).2 + γ'.2 * (t - t₀))

  -- The linear terms in γ error
  have h_err_γ : err_γ = (γ t).1 - a.1 - γ'.1 * (t - t₀) := by { dsimp [err_γ]; rw [hγ_a]; ring }
  have h_err_γ_2 : err_γ_2 = (γ t).2 - a.2 - γ'.2 * (t - t₀) := by { dsimp [err_γ_2]; rw [hγ_a]; ring }

  have h_γ_diff_norm : euclideanNorm (err_γ, err_γ_2) = euclideanDist (γ t) (γ t₀ + (γ'.1 * (t - t₀), γ'.2 * (t - t₀))) := by {
    unfold euclideanDist sqDist euclideanNorm sqNorm
    dsimp
  }

  have h_γ_bound2 : euclideanNorm (err_γ, err_γ_2) < (ε / (2 * M)) * |t - t₀| := by {
    rw [h_γ_diff_norm]
    exact h_γ_bound
  }

  -- We split into two cases: γ t = a and γ t ≠ a.
  by_cases h_dist_0 : euclideanDist (γ t) (γ t₀) = 0
  · -- If γ t = γ t₀, then γ t = a.
    have h_γ_eq : γ t = a := by {
      have h1 : euclideanDist (γ t) (γ t₀) = 0 := h_dist_0
      unfold euclideanDist sqDist at h1
      rw [Real.sqrt_eq_zero] at h1
      · have h2 : (γ t).1 - (γ t₀).1 = 0 := by {
          have h_sq1 : 0 ≤ ((γ t).1 - (γ t₀).1)^2 := sq_nonneg _
          have h_sq2 : 0 ≤ ((γ t).2 - (γ t₀).2)^2 := sq_nonneg _
          have h3 : ((γ t).1 - (γ t₀).1)^2 = 0 := by linarith
          exact sq_eq_zero_iff.mp h3
        }
        have h3 : (γ t).2 - (γ t₀).2 = 0 := by {
          have h_sq1 : 0 ≤ ((γ t).1 - (γ t₀).1)^2 := sq_nonneg _
          have h_sq2 : 0 ≤ ((γ t).2 - (γ t₀).2)^2 := sq_nonneg _
          have h3 : ((γ t).2 - (γ t₀).2)^2 = 0 := by linarith
          exact sq_eq_zero_iff.mp h3
        }
        ext
        · exact sub_eq_zero.mp h2 ▸ (congrArg Prod.fst hγ_a)
        · exact sub_eq_zero.mp h3 ▸ (congrArg Prod.snd hγ_a)
      · positivity
    }
    have h_u_eq : u (γ t) = u a := by rw [h_γ_eq]
    have h_v_eq : v (γ t) = v a := by rw [h_γ_eq]

    have h_total_norm : euclideanDist (u (γ t), v (γ t)) (u a + (ux₀ * γ'.1 + uy₀ * γ'.2) * (t - t₀), v a + (vx₀ * γ'.1 + vy₀ * γ'.2) * (t - t₀)) = euclideanNorm (-(ux₀ * γ'.1 + uy₀ * γ'.2) * (t - t₀), -(vx₀ * γ'.1 + vy₀ * γ'.2) * (t - t₀)) := by {
      unfold euclideanDist sqDist euclideanNorm sqNorm
      dsimp
      congr 1
      have h1 : u a - (u a + (ux₀ * γ'.1 + uy₀ * γ'.2) * (t - t₀)) = -(ux₀ * γ'.1 + uy₀ * γ'.2) * (t - t₀) := by ring
      have h2 : v a - (v a + (vx₀ * γ'.1 + vy₀ * γ'.2) * (t - t₀)) = -(vx₀ * γ'.1 + vy₀ * γ'.2) * (t - t₀) := by ring
      rw [h_u_eq, h_v_eq, h1, h2]
    }

    have h_total_norm2 : euclideanNorm (-(ux₀ * γ'.1 + uy₀ * γ'.2) * (t - t₀), -(vx₀ * γ'.1 + vy₀ * γ'.2) * (t - t₀)) = euclideanNorm ((ux₀ * γ'.1 + uy₀ * γ'.2) * (t - t₀), (vx₀ * γ'.1 + vy₀ * γ'.2) * (t - t₀)) := by {
      unfold euclideanNorm sqNorm
      dsimp
      congr 1
      ring
    }

    rw [h_total_norm, h_total_norm2]

    have h_err_γ_zero : err_γ = - γ'.1 * (t - t₀) := by {
      dsimp [err_γ]
      rw [h_γ_eq, hγ_a]
      ring
    }
    have h_err_γ_2_zero : err_γ_2 = - γ'.2 * (t - t₀) := by {
      dsimp [err_γ_2]
      rw [h_γ_eq, hγ_a]
      ring
    }

    have h_matrix_zero : euclideanNorm ((ux₀ * γ'.1 + uy₀ * γ'.2) * (t - t₀), (vx₀ * γ'.1 + vy₀ * γ'.2) * (t - t₀)) = euclideanNorm (ux₀ * err_γ + uy₀ * err_γ_2, vx₀ * err_γ + vy₀ * err_γ_2) := by {
      unfold euclideanNorm sqNorm
      dsimp
      congr 1
      rw [h_err_γ_zero, h_err_γ_2_zero]
      ring
    }

    rw [h_matrix_zero]

    have h_matrix := matrix_bound ux₀ uy₀ vx₀ vy₀ err_γ err_γ_2

    have h_bound_mat : (|ux₀| + |uy₀| + |vx₀| + |vy₀|) * euclideanNorm (err_γ, err_γ_2) ≤ (|ux₀| + |uy₀| + |vx₀| + |vy₀|) * ((ε / (2 * M)) * |t - t₀|) := by {
      have h1 : 0 ≤ |ux₀| + |uy₀| + |vx₀| + |vy₀| := by positivity
      exact mul_le_mul_of_nonneg_left (le_of_lt h_γ_bound2) h1
    }

    have h_bound_mat2 : (|ux₀| + |uy₀| + |vx₀| + |vy₀|) * ((ε / (2 * M)) * |t - t₀|) < (ε / 2) * |t - t₀| := by {
      have h_strict : (|ux₀| + |uy₀| + |vx₀| + |vy₀|) < M := by {
        dsimp [M]
        linarith
      }
      have h_pos : 0 < (ε / (2 * M)) * |t - t₀| := mul_pos hε2_pos ht.1
      have h1 : (|ux₀| + |uy₀| + |vx₀| + |vy₀|) * ((ε / (2 * M)) * |t - t₀|) < M * ((ε / (2 * M)) * |t - t₀|) := mul_lt_mul_of_pos_right h_strict h_pos
      have h2 : M * ((ε / (2 * M)) * |t - t₀|) = (ε / 2) * |t - t₀| := by {
        calc M * ((ε / (2 * M)) * |t - t₀|)
          _ = M * (ε / (2 * M)) * |t - t₀| := by ring
          _ = M * (1 / M) * (ε / 2) * |t - t₀| := by ring
          _ = (M * (1 / M)) * (ε / 2) * |t - t₀| := by ring
          _ = 1 * (ε / 2) * |t - t₀| := by {
            congr 2
            exact mul_one_div_cancel (ne_of_gt hM_pos)
          }
          _ = (ε / 2) * |t - t₀| := by ring
      }
      rw [h2] at h1
      exact h1
    }

    have h_bound_mat3 : euclideanNorm (ux₀ * err_γ + uy₀ * err_γ_2, vx₀ * err_γ + vy₀ * err_γ_2) < (ε / 2) * |t - t₀| := by {
      exact lt_of_le_of_lt h_matrix (lt_of_le_of_lt h_bound_mat h_bound_mat2)
    }

    have h_half_lt_full : (ε / 2) * |t - t₀| < ε * |t - t₀| := by {
      have h_half : ε / 2 < ε := by linarith
      exact mul_lt_mul_of_pos_right h_half ht.1
    }

    exact lt_of_lt_of_le h_bound_mat3 (le_of_lt h_half_lt_full)


  · -- If γ t ≠ a
    have h_dist_pos : 0 < euclideanDist (γ t) a := by {
      have h1 : euclideanDist (γ t) a ≠ 0 := by {
        intro h_contra
        rw [← hγ_a] at h_contra
        exact h_dist_0 h_contra
      }
      exact lt_of_le_of_ne (euclideanDist_nonneg _ _) h1.symm
    }

    have h_dist_bound : euclideanDist (γ t) a < δ1 := by {
      rw [← hγ_a]
      have h1 : euclideanDist (γ t) (γ t₀) ≤ K * |t - t₀| := h_lip_bound
      have h2 : K * |t - t₀| < K * δ3 := by {
        exact mul_lt_mul_of_pos_left ht3 hK_pos
      }
      have h3 : K * δ3 = δ1 := mul_div_cancel₀ _ (ne_of_gt hK_pos)
      rw [h3] at h2
      exact lt_of_le_of_lt h1 h2
    }

    have h_u_bound := hδ1 (γ t) ⟨h_dist_pos, h_dist_bound⟩

    let dx := (γ t).1 - a.1
    let dy := (γ t).2 - a.2

    let err_u := u (γ t) - u a - (ux₀ * dx + uy₀ * dy)
    let err_v := v (γ t) - v a - (vx₀ * dx + vy₀ * dy)

    have h_total_err_x : u (γ t) - (u a + ((ux₀ * γ'.1 + uy₀ * γ'.2) * (t - t₀))) = err_u + (ux₀ * err_γ + uy₀ * err_γ_2) := by {
      rw [h_err_γ, h_err_γ_2]
      dsimp [err_u, dx, dy]
      ring
    }
    have h_total_err_y : v (γ t) - (v a + ((vx₀ * γ'.1 + vy₀ * γ'.2) * (t - t₀))) = err_v + (vx₀ * err_γ + vy₀ * err_γ_2) := by {
      rw [h_err_γ, h_err_γ_2]
      dsimp [err_v, dx, dy]
      ring
    }

    have h_total_norm : euclideanDist (u (γ t), v (γ t)) (u a + (ux₀ * γ'.1 + uy₀ * γ'.2) * (t - t₀), v a + (vx₀ * γ'.1 + vy₀ * γ'.2) * (t - t₀)) = euclideanNorm (u (γ t) - (u a + ((ux₀ * γ'.1 + uy₀ * γ'.2) * (t - t₀))), v (γ t) - (v a + ((vx₀ * γ'.1 + vy₀ * γ'.2) * (t - t₀)))) := by {
      unfold euclideanDist sqDist euclideanNorm sqNorm
      dsimp
    }

    have h_triangle_norm := euclideanNormTriangle (err_u, err_v) (ux₀ * err_γ + uy₀ * err_γ_2, vx₀ * err_γ + vy₀ * err_γ_2)

    have h_bound_uv : euclideanNorm (err_u, err_v) < (ε / (2 * K)) * euclideanDist (γ t) a := h_u_bound

    have h_dist_le : (ε / (2 * K)) * euclideanDist (γ t) a ≤ (ε / (2 * K)) * (K * |t - t₀|) := by {
      have h1 : euclideanDist (γ t) (γ t₀) ≤ K * |t - t₀| := h_lip_bound
      rw [hγ_a] at h1
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt hε1_pos)
    }

    have h_bound_uv2 : euclideanNorm (err_u, err_v) < (ε / 2) * |t - t₀| := by {
      have h1 : (ε / (2 * K)) * (K * |t - t₀|) = (ε / 2) * |t - t₀| := by {
        calc (ε / (2 * K)) * (K * |t - t₀|)
          _ = (ε / 2) * (1 / K) * K * |t - t₀| := by ring
          _ = (ε / 2) * ((1 / K) * K) * |t - t₀| := by ring
          _ = (ε / 2) * 1 * |t - t₀| := by {
            congr 2
            exact one_div_mul_cancel (ne_of_gt hK_pos)
          }
          _ = (ε / 2) * |t - t₀| := by ring
      }
      rw [h1] at h_dist_le
      exact lt_of_lt_of_le h_bound_uv h_dist_le
    }

    have h_matrix := matrix_bound ux₀ uy₀ vx₀ vy₀ err_γ err_γ_2

    have h_bound_mat : (|ux₀| + |uy₀| + |vx₀| + |vy₀|) * euclideanNorm (err_γ, err_γ_2) ≤ (|ux₀| + |uy₀| + |vx₀| + |vy₀|) * ((ε / (2 * M)) * |t - t₀|) := by {
      have h1 : 0 ≤ |ux₀| + |uy₀| + |vx₀| + |vy₀| := by positivity
      exact mul_le_mul_of_nonneg_left (le_of_lt h_γ_bound2) h1
    }

    have h_bound_mat2 : (|ux₀| + |uy₀| + |vx₀| + |vy₀|) * ((ε / (2 * M)) * |t - t₀|) < (ε / 2) * |t - t₀| := by {
      have h_strict : (|ux₀| + |uy₀| + |vx₀| + |vy₀|) < M := by {
        dsimp [M]
        linarith
      }
      have h_pos : 0 < (ε / (2 * M)) * |t - t₀| := mul_pos hε2_pos ht.1
      have h1 : (|ux₀| + |uy₀| + |vx₀| + |vy₀|) * ((ε / (2 * M)) * |t - t₀|) < M * ((ε / (2 * M)) * |t - t₀|) := mul_lt_mul_of_pos_right h_strict h_pos
      have h2 : M * ((ε / (2 * M)) * |t - t₀|) = (ε / 2) * |t - t₀| := by {
        calc M * ((ε / (2 * M)) * |t - t₀|)
          _ = M * (ε / (2 * M)) * |t - t₀| := by ring
          _ = M * (1 / M) * (ε / 2) * |t - t₀| := by ring
          _ = (M * (1 / M)) * (ε / 2) * |t - t₀| := by ring
          _ = 1 * (ε / 2) * |t - t₀| := by {
            congr 2
            exact mul_one_div_cancel (ne_of_gt hM_pos)
          }
          _ = (ε / 2) * |t - t₀| := by ring
      }
      rw [h2] at h1
      exact h1
    }

    have h_bound_mat3 : euclideanNorm (ux₀ * err_γ + uy₀ * err_γ_2, vx₀ * err_γ + vy₀ * err_γ_2) < (ε / 2) * |t - t₀| := by {
      exact lt_of_le_of_lt h_matrix (lt_of_le_of_lt h_bound_mat h_bound_mat2)
    }

    have h_final : euclideanNorm (err_u, err_v) + euclideanNorm (ux₀ * err_γ + uy₀ * err_γ_2, vx₀ * err_γ + vy₀ * err_γ_2) < ε * |t - t₀| := by {
      have h1 : (ε / 2) * |t - t₀| + (ε / 2) * |t - t₀| = ε * |t - t₀| := by ring
      rw [← h1]
      exact add_lt_add h_bound_uv2 h_bound_mat3
    }

    have h_final_bound : euclideanNorm (err_u + (ux₀ * err_γ + uy₀ * err_γ_2), err_v + (vx₀ * err_γ + vy₀ * err_γ_2)) < ε * |t - t₀| := lt_of_le_of_lt h_triangle_norm h_final

    rw [h_total_norm, h_total_err_x, h_total_err_y]
    exact h_final_bound
}

end ComplexAnalysis.R2
