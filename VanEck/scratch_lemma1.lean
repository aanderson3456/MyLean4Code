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

lemma step2 (X D_max : ℕ) (hX_pos : 0 < X) (hX_lt : X < D_max) (ζ : ℂ) (h_prim : IsPrimitiveRoot ζ D_max)
    (cover_X : Finset ℕ) (start_val : ℕ) :
    (∃ L : ℕ, (ζ ^ X) ^ L = 1 ∧ ∑ k ∈ cover_X, ζ ^ (k : ℕ) = ζ ^ start_val * ∑ i ∈ range L, (ζ ^ X) ^ i) →
    ∑ k ∈ cover_X, ζ ^ (k : ℕ) = 0 := by {
  intro h
  rcases h with ⟨L, h_pow_one, h_prog_sum⟩
  have h_step_ne_one : ζ ^ X ≠ 1 := primitive_root_pow_ne_one h_prim hX_pos hX_lt
  rw [h_prog_sum]
  have h_zero : ∑ i ∈ range L, (ζ ^ X) ^ i = 0 := geom_sum_zero_of_pow_one h_step_ne_one h_pow_one
  rw [h_zero, mul_zero]
}
