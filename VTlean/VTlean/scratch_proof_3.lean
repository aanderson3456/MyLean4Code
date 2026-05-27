import Mathlib
import VTlean.VTCode
import VTlean.Cuculiere
import VTlean.NumOsNumIs

open Nat Finset B

def list_to_subset (X : List B) : Finset Nat :=
  (Finset.range (X.length + 1)).filter (fun i => i ≠ 0 ∧ X.getD (i - 1) B.O = B.I)

lemma list_to_subset_card (X : List B) :
  (list_to_subset X).card = List.num_Is X := by {
  induction X with
  | nil => 
    simp [list_to_subset, List.num_Is]
  | cons x xs ih =>
    sorry
}
