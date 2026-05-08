import Mathlib
example (a b c : ℕ) (h : a + b = c) : b = c - a := by
  exact Nat.eq_sub_of_add_eq' h
