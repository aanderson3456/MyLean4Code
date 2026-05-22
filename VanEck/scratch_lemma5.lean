import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

open Complex

lemma step1_zeta_pow (P D_max : ℕ) (ζ : ℂ) (h_prim : IsPrimitiveRoot ζ D_max) (h_div : D_max ∣ P) :
    ζ ^ P = 1 := by {
  rcases h_div with ⟨k, rfl⟩
  have h1 : ζ ^ D_max = 1 := IsPrimitiveRoot.pow_eq_one h_prim
  calc ζ ^ (D_max * k)
    _ = (ζ ^ D_max) ^ k := by rw [pow_mul]
    _ = 1 ^ k := by rw [h1]
    _ = 1 := by simp
}
