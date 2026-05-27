import Mathlib
import VTlean.VTCode
import VTlean.Cuculiere
import VTlean.NumOsNumIs

open Nat Finset B

def vector_to_subset (n : Nat) (X : List.Vector B n) : Finset (Fin (n + 1)) :=
  (Finset.univ).filter (fun (i : Fin (n + 1)) => i.val ≠ 0 ∧ X.val.getD (i.val - 1) B.O = B.I)

def subset_to_vector (n : Nat) (s : Finset (Fin (n + 1))) : List.Vector B n :=
  ⟨List.ofFn (fun (i : Fin n) => if Fin.mk (i.val + 1) (by omega) ∈ s then B.I else B.O), by simp⟩

lemma vector_to_subset_card (n : Nat) (X : List.Vector B n) :
  (vector_to_subset n X).card = wt X := by {
  sorry
}

lemma vector_to_subset_sum (n : Nat) (X : List.Vector B n) :
  (vector_to_subset n X).sum (fun i => i.val) = List.Vector.moment X := by {
  sorry
}
