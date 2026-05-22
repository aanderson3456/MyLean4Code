import Mathlib.Data.Complex.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

open Complex

lemma check_ne_zero (k : ℕ) (hk : k > 0) (ζ : ℂ) (h_prim : IsPrimitiveRoot ζ k) : ζ ≠ 0 := by
  exact IsPrimitiveRoot.ne_zero h_prim (by omega)
