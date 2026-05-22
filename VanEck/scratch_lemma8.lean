import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.GeomSum

open Finset
open Complex
open Classical

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
