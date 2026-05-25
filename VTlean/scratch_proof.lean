import Mathlib
import VTlean.Cuculiere

open Nat Finset

lemma VTCode_zero_is_max_proof (n a : Nat) :
  Finset.card (Finset.VTCode n a) ≤ Finset.card (Finset.VTCode n 0) := by {
  rw [card_VTCode_eq_cuculiere n a]
  rw [card_VTCode_eq_cuculiere n 0]
  rw [cuculiere_mod_sum_eq_gen n a]
  rw [cuculiere_mod_sum_eq_gen n 0]
  exact cuculiere_mod_sum_gen_max n n a (Nat.le_refl n)
}
