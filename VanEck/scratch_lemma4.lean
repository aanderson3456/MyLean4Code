import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

open Finset
open Complex

lemma geom_sum_zero_of_pow_one {x : ℂ} {n : ℕ} (h_ne_one : x ≠ 1) (h_pow_one : x ^ n = 1) :
    ∑ k ∈ range n, x ^ k = 0 := by {
  have h_geom := geom_sum_eq h_ne_one n
  rw [h_pow_one] at h_geom
  have h_sub : (1 : ℂ) - 1 = 0 := sub_self 1
  rw [h_sub, zero_div] at h_geom
  exact h_geom
}

lemma primitive_root_pow_ne_one {D_max d : ℕ} {ζ : ℂ} (h_prim : IsPrimitiveRoot ζ D_max)
    (h_pos : 0 < d) (h_lt : d < D_max) : ζ ^ d ≠ 1 := by {
  intro h_eq
  have h_dvd := IsPrimitiveRoot.dvd_of_pow_eq_one h_prim d h_eq
  have h_le := Nat.le_of_dvd h_pos h_dvd
  omega
}

open Classical

lemma evaluate_geometric_sum_contradiction (P : ℕ) (S : Finset ℕ)
    (h_min : ∀ X ∈ S, X ≥ 3)
    (cover : ℕ → Finset (Fin P))
    (h_partition : ∀ k : Fin P, ∃! X, X ∈ S ∧ k ∈ cover X)
    (h_ap : ∀ X ∈ S, ∃ start : Fin P, cover X = Finset.univ.filter (fun (k : Fin P) => ∃ i : ℕ, k.val = (start.val + i * X) % P))
    (D_max : ℕ) (h_Dmax_in : D_max ∈ S)
    (h_max : ∀ d ∈ S, d ≠ D_max → d < D_max)
    (ζ : ℂ) (h_prim : IsPrimitiveRoot ζ D_max) :
    False := by {
  -- Step 1: The total sum over the whole group Fin P evaluated at ζ is 0.
  have h_left_zero : ∑ k : Fin P, ζ ^ k.val = 0 := by {
    have h_zeta_pow : ζ ^ P = 1 := sorry 
    
    have h_zeta_ne : ζ ≠ 1 := by {
      have h_Dmax_ge_3 : D_max ≥ 3 := h_min D_max h_Dmax_in
      have h_Dmax_ge_2 : 2 ≤ D_max := by omega
      exact IsPrimitiveRoot.ne_one h_prim h_Dmax_ge_2
    }
    
    have h_equiv : ∑ k : Fin P, ζ ^ k.val = ∑ k ∈ range P, ζ ^ k := by
      exact Fin.sum_univ_eq_sum_range (fun k => ζ ^ k) P
      
    rw [h_equiv]
    exact geom_sum_zero_of_pow_one h_zeta_ne h_zeta_pow
  }
  
  -- Step 2: For any step size X < D_max, the sum over its progression is 0.
  have h_parts_zero : ∀ X ∈ S, X ≠ D_max → ∑ k ∈ cover X, ζ ^ k.val = 0 := by {
    intro X hX_in hX_ne
    have hX_ge_3 : X ≥ 3 := h_min X hX_in
    have hX_lt : X < D_max := h_max X hX_in hX_ne
    have hX_pos : 0 < X := by omega
    
    have h_step_ne_one : ζ ^ X ≠ 1 := primitive_root_pow_ne_one h_prim hX_pos hX_lt
    
    have ⟨start, h_cover_eq⟩ := h_ap X hX_in
    
    have ⟨L, h_pow_one, h_prog_sum⟩ : ∃ L : ℕ, (ζ ^ X) ^ L = 1 ∧ ∑ k ∈ cover X, ζ ^ k.val = ζ ^ start.val * ∑ i ∈ range L, (ζ ^ X) ^ i := sorry
    
    rw [h_prog_sum]
    have h_zero : ∑ i ∈ range L, (ζ ^ X) ^ i = 0 := geom_sum_zero_of_pow_one h_step_ne_one h_pow_one
    rw [h_zero, mul_zero]
  }
  
  -- Step 3: For the max step size D_max, the sum over its progression is NON-ZERO.
  have h_max_nonzero : ∑ k ∈ cover D_max, ζ ^ k.val ≠ 0 := by {
    have ⟨start_max, h_cover_max⟩ := h_ap D_max h_Dmax_in
    have ⟨L_max, h_L_pos, h_prog_sum_max⟩ : ∃ L_max : ℕ, L_max > 0 ∧ ∑ k ∈ cover D_max, ζ ^ k.val = ζ ^ start_max.val * ∑ i ∈ range L_max, (ζ ^ D_max) ^ i := sorry
    
    rw [h_prog_sum_max]
    
    have h_pow_one : ζ ^ D_max = 1 := IsPrimitiveRoot.pow_eq_one h_prim
    have h_sum_ones : ∑ i ∈ range L_max, (ζ ^ D_max) ^ i = L_max := by {
      rw [h_pow_one]
      simp
    }
    rw [h_sum_ones]
    
    have h_D_max_ne_zero : D_max ≠ 0 := by {
      have := h_min D_max h_Dmax_in
      omega
    }
    have h_zeta_ne_zero : ζ ≠ 0 := IsPrimitiveRoot.ne_zero h_prim h_D_max_ne_zero
    have h_start_pow_ne_zero : ζ ^ start_max.val ≠ 0 := pow_ne_zero start_max.val h_zeta_ne_zero
    have h_L_ne_zero : (L_max : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt h_L_pos)
    exact mul_ne_zero h_start_pow_ne_zero h_L_ne_zero
  }
  
  -- Step 4: By the exact cover property, the total sum equals the sum of the parts.
  have h_sum_split : ∑ k : Fin P, ζ ^ k.val = ∑ X ∈ S, ∑ k ∈ cover X, ζ ^ k.val := by {
    choose f hf using h_partition
    have h_maps_to : ∀ k ∈ (Finset.univ : Finset (Fin P)), f k ∈ S := by
      intro k _
      exact (hf k).1.1
    have h_fiber : ∀ X ∈ S, ∀ k : Fin P, k ∈ cover X ↔ f k = X := by
      intro X hX k
      constructor
      · intro hk
        exact ((hf k).2 X ⟨hX, hk⟩).symm
      · intro hk
        rw [← hk]
        exact (hf k).1.2
    
    have hs := Finset.sum_fiberwise_of_maps_to h_maps_to (fun k => ζ ^ k.val)
    rw [← hs]
    apply Finset.sum_congr rfl
    intro X hX
    apply Finset.sum_congr
    · ext k
      simp [h_fiber X hX k]
    · intro _ _
      rfl
  }
  
  -- Step 5: But 0 = 0 + non-zero is a contradiction!
  have h_split_eval : ∑ X ∈ S, ∑ k ∈ cover X, ζ ^ k.val = ∑ k ∈ cover D_max, ζ ^ k.val := by {
    have h_eq := Finset.sum_eq_single D_max (by {
      intro X hX_in hX_ne
      exact h_parts_zero X hX_in hX_ne
    }) (by {
      intro h_not_in
      exact False.elim (h_not_in h_Dmax_in)
    })
    exact h_eq
  }
  
  rw [h_split_eval] at h_sum_split
  rw [h_left_zero] at h_sum_split
  exact h_max_nonzero h_sum_split.symm
}
