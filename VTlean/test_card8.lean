import VTlean.Dream
open B

lemma perfect_code_volume_eq (n : Nat) (C : Finset (List.Vector B n)) (hC : is_PerfectCodeCandidate C) :
  ∑ x ∈ C, (dS x).card = 2^(n - 1) := by {
    have h_disj : (C : Set (List.Vector B n)).PairwiseDisjoint dS := by {
      intro x hx y hy hne
      exact hC.1 x hx y hy hne
    }
    have h_sum := Finset.card_biUnion h_disj
    rw [← h_sum]
    rw [hC.2]
    have h_univ_card : (Finset.univ : Finset (List.Vector B (n - 1))).card = Fintype.card (List.Vector B (n - 1)) := Finset.card_univ
    rw [h_univ_card]
    exact card_vector_B_eq (n - 1)
}
