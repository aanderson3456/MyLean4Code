import VTlean.B
import VTlean.VTCode
import VTlean.Dream

open Finset List.Vector

variable {n : Nat}

lemma card_vector_B_eq (m : Nat) : Fintype.card (List.Vector B m) = 2^m := by
  sorry

theorem volume_constraint_test (C : Finset (List.Vector B n)) (hC : is_OptimalCodeCandidate C) :
  ∑ x ∈ C, (dS x).card ≤ 2^(n - 1) := by
  have h_disj : (C : Set (List.Vector B n)).PairwiseDisjoint dS := by
    intro x hx y hy hne
    exact hC x hx y hy hne
  have h_sum := Finset.card_biUnion h_disj
  rw [← h_sum]
  have h_sub : C.biUnion dS ⊆ (univ : Finset (List.Vector B (n - 1))) := subset_univ _
  have h_le := Finset.card_le_card h_sub
  have h_card := card_vector_B_eq (n - 1)
  have h_univ_card : (univ : Finset (List.Vector B (n - 1))).card = Fintype.card (List.Vector B (n - 1)) := Finset.card_univ
  rw [h_univ_card, h_card] at h_le
  exact h_le
