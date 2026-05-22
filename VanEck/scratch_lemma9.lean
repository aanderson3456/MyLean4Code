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
open Classical

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

lemma zeta_pow_mod_eq (P n : ℕ) (ζ : ℂ) (h_pow : ζ ^ P = 1) :
    ζ ^ (n % P) = ζ ^ n := by {
  have h_div : n = P * (n / P) + n % P := Nat.div_add_mod n P |>.symm
  conv => right; rw [h_div, pow_add, pow_mul, h_pow, one_pow, one_mul]
}

lemma sum_progression_eq_geom_sum_mod (P X L start : ℕ) (ζ : ℂ) (h_pow : ζ ^ P = 1) (hL : P = X * L) :
    ∑ i ∈ range L, ζ ^ ((start + i * X) % P) = ζ ^ start * ∑ i ∈ range L, (ζ ^ X) ^ i := by {
  have h_pull : ∀ i : ℕ, ζ ^ ((start + i * X) % P) = ζ ^ start * (ζ ^ X) ^ i := by
    intro i
    rw [zeta_pow_mod_eq P _ ζ h_pow]
    calc ζ ^ (start + i * X)
      _ = ζ ^ start * ζ ^ (i * X) := by rw [pow_add]
      _ = ζ ^ start * ζ ^ (X * i) := by rw [mul_comm i X]
      _ = ζ ^ start * (ζ ^ X) ^ i := by rw [pow_mul]
  have h_sum : ∑ i ∈ range L, ζ ^ ((start + i * X) % P) = ∑ i ∈ range L, ζ ^ start * (ζ ^ X) ^ i := by
    apply sum_congr rfl
    intro i _
    exact h_pull i
  rw [h_sum, ← mul_sum]
}

lemma prog_sum_extraction (P X L : ℕ) (start : Fin P) (ζ : ℂ)
    (h_pow : ζ ^ P = 1) (hL : P = X * L)
    (cover_X : Finset (Fin P))
    (h_ap : cover_X = Finset.univ.filter (fun (k : Fin P) => ∃ i : ℕ, k.val = (start.val + i * X) % P)) :
    ∑ k ∈ cover_X, ζ ^ k.val = ζ ^ start.val * ∑ i ∈ range L, (ζ ^ X) ^ i := by {
  have h_bij : ∑ k ∈ cover_X, ζ ^ k.val = ∑ i ∈ range L, ζ ^ ((start.val + i * X) % P) := sorry
  rw [h_bij]
  exact sum_progression_eq_geom_sum_mod P X L start.val ζ h_pow hL
}

lemma evaluate_geometric_sum_contradiction (P : ℕ) (S : Finset ℕ)
    (h_min : ∀ X ∈ S, X ≥ 3)
    (cover : ℕ → Finset (Fin P))
    (h_partition : ∀ k : Fin P, ∃! X, X ∈ S ∧ k ∈ cover X)
    (h_ap : ∀ X ∈ S, ∃ start : Fin P, cover X = Finset.univ.filter (fun (k : Fin P) => ∃ i : ℕ, k.val = (start.val + i * X) % P))
    (h_div : ∀ X ∈ S, X ∣ P)
    (D_max : ℕ) (h_Dmax_in : D_max ∈ S)
    (h_max : ∀ d ∈ S, d ≠ D_max → d < D_max)
    (ζ : ℂ) (h_prim : IsPrimitiveRoot ζ D_max) :
    False := by {
  have h_zeta_pow : ζ ^ P = 1 := by {
    have h_Dmax_div : D_max ∣ P := h_div D_max h_Dmax_in
    rcases h_Dmax_div with ⟨k_div, rfl⟩
    have h1 : ζ ^ D_max = 1 := IsPrimitiveRoot.pow_eq_one h_prim
    calc ζ ^ (D_max * k_div)
      _ = (ζ ^ D_max) ^ k_div := by rw [pow_mul]
      _ = 1 ^ k_div := by rw [h1]
      _ = 1 := by simp
  }

  have h_left_zero : ∑ k : Fin P, ζ ^ k.val = 0 := by {
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
  
  have h_parts_zero : ∀ X ∈ S, X ≠ D_max → ∑ k ∈ cover X, ζ ^ k.val = 0 := by {
    intro X hX_in hX_ne
    have hX_ge_3 : X ≥ 3 := h_min X hX_in
    have hX_lt : X < D_max := h_max X hX_in hX_ne
    have hX_pos : 0 < X := by omega
    
    have h_step_ne_one : ζ ^ X ≠ 1 := primitive_root_pow_ne_one h_prim hX_pos hX_lt
    have ⟨start, h_cover_eq⟩ := h_ap X hX_in
    have h_X_div : X ∣ P := h_div X hX_in
    rcases h_X_div with ⟨L, hL⟩
    
    have h_prog_sum : ∑ k ∈ cover X, ζ ^ k.val = ζ ^ start.val * ∑ i ∈ range L, (ζ ^ X) ^ i := 
      prog_sum_extraction P X L start ζ h_zeta_pow hL (cover X) h_cover_eq
    
    have h_pow_one : (ζ ^ X) ^ L = 1 := by {
      calc (ζ ^ X) ^ L
        _ = ζ ^ (X * L) := by rw [← pow_mul]
        _ = ζ ^ P := by rw [← hL]
        _ = 1 := h_zeta_pow
    }
    
    rw [h_prog_sum]
    have h_zero : ∑ i ∈ range L, (ζ ^ X) ^ i = 0 := geom_sum_zero_of_pow_one h_step_ne_one h_pow_one
    rw [h_zero, mul_zero]
  }
  
  have h_max_nonzero : ∑ k ∈ cover D_max, ζ ^ k.val ≠ 0 := by {
    have ⟨start_max, h_cover_max⟩ := h_ap D_max h_Dmax_in
    have h_D_max_div : D_max ∣ P := h_div D_max h_Dmax_in
    rcases h_D_max_div with ⟨L_max, hL_max⟩
    
    have h_D_max_ne_zero : D_max ≠ 0 := by {
      have := h_min D_max h_Dmax_in
      omega
    }
    
    have h_L_pos : L_max > 0 := by {
      have h_P_pos : P > 0 := by {
        -- If P = 0, D_max | 0 which is true, but what if P = 0?
        -- Oh, we didn't add P > 0 to this theorem!
        sorry
      }
      -- Let's ignore this for the scratch test and see if it's the only failure.
      sorry
    }

    have h_prog_sum_max : ∑ k ∈ cover D_max, ζ ^ k.val = ζ ^ start_max.val * ∑ i ∈ range L_max, (ζ ^ D_max) ^ i := 
      prog_sum_extraction P D_max L_max start_max ζ h_zeta_pow hL_max (cover D_max) h_cover_max
    
    rw [h_prog_sum_max]
    
    have h_pow_one : ζ ^ D_max = 1 := IsPrimitiveRoot.pow_eq_one h_prim
    have h_sum_ones : ∑ i ∈ range L_max, (ζ ^ D_max) ^ i = L_max := by {
      rw [h_pow_one]
      simp
    }
    rw [h_sum_ones]
    
    have h_zeta_ne_zero : ζ ≠ 0 := IsPrimitiveRoot.ne_zero h_prim h_D_max_ne_zero
    have h_start_pow_ne_zero : ζ ^ start_max.val ≠ 0 := pow_ne_zero start_max.val h_zeta_ne_zero
    have h_L_ne_zero : (L_max : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt h_L_pos)
    exact mul_ne_zero h_start_pow_ne_zero h_L_ne_zero
  }
  
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
