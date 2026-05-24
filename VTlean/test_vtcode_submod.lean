import VTlean.VTCode

open Nat Finset B

namespace List
variable {n a : Nat} (X : List B) (m : Nat)

def sub_mod (m a : Nat) (X : List B) : Nat :=
  if moment X < a then (a - moment X) % m 
  else (m - (moment X - a) % m) % m

lemma sub_mod_zero (m : Nat) (X : List B) :
    sub_mod m 0 X = (m - (moment X) % m) % m := by {
  unfold sub_mod
  rw [if_neg]
  · rw [Nat.sub_zero]
  · apply Nat.not_lt_of_ge
    exact Nat.zero_le _
}

lemma sub_mod_mod_self (m : Nat) (X : List B) :
  sub_mod m m X = sub_mod m 0 X := by {
  rw [sub_mod, sub_mod_zero]
  cases Decidable.em (moment X < m) with
  | inl hlt =>
    rw [if_pos hlt]
    rw [Nat.mod_eq_of_lt hlt]
  | inr hnlt =>
    rw [if_neg hnlt]
    rw [Nat.mod_eq_sub_mod]
    exact Nat.le_of_not_lt hnlt
}

end List
