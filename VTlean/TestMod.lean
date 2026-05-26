import Mathlib
lemma mod_add_cancel_right {a b k m : Nat} (h : (a + k) % m = (b + k) % m) : a % m = b % m := by
  have h1 : a + k ≡ b + k [MOD m] := h
  exact Nat.ModEq.add_right_cancel h1
