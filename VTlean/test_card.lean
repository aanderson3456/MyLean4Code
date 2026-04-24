import Mathlib.Data.Finset.Card

open Finset
variable {α : Type} [DecidableEq α] {s : Finset α} {a : α}

example (h : a ∈ s) : card (erase s a) = card s - 1 := by
  exact?
