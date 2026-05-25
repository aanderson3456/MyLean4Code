import Mathlib
import VTlean.VTCode
import VTlean.Cuculiere

open Nat Finset

lemma vector_card_split_test (n : Nat) (P : List.Vector B (n + 1) → Prop) [DecidablePred P] :
  Finset.card (Finset.filter P univ) = 
  Finset.card (Finset.filter (fun v => P (List.Vector.push v B.O)) univ) + 
  Finset.card (Finset.filter (fun v => P (List.Vector.push v B.I)) univ) := by {
  sorry
}
