import VTlean.VTCode

open Nat Finset B

namespace List
variable {n a : Nat} (X : List B) (m : Nat)

def sub_mod2 (m a : Nat) (X : List B) : Nat :=
  if moment X < a then (a - moment X) % m 
  else (m - (moment X - a) % m) % m

lemma sub_mod2_zero (m : Nat) (X : List B) :
    sub_mod2 m 0 X = (m - (moment X) % m) % m := by {
  unfold sub_mod2
  rw [if_neg]
  · rfl -- wait, is a - moment X % m? No, it's (moment X - 0) % m
    -- actually rw [Nat.sub_zero]
}

end List
