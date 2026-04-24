import Mathlib

lemma test {α : Type} [DecidableEq α] (s : Finset α) (k : Nat) (h : k ≤ s.card) : ∃ s' ⊆ s, s'.card = k := by
  exact Finset.exists_smaller_set s k h
