import Mathlib.Data.Finset.Basic

lemma exists_subset_card_le {α : Type} (s : Finset α) (k : Nat) (hk : k ≤ s.card) :
  ∃ s' ⊆ s, s'.card = k := Finset.exists_subset_card_eq hk
