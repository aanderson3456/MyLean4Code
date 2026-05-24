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
  · rfl
  · exact Nat.not_lt_zero _
}

lemma sub_mod2_mod_self (m : Nat) (X : List B) :
  sub_mod2 m m X = sub_mod2 m 0 X := by {
  rw [sub_mod2, sub_mod2_zero]
  cases Decidable.em (moment X < m) with
  | inl hlt =>
    rw [if_pos hlt]
    have h1 : moment X % m = moment X := Nat.mod_eq_of_lt hlt
    rw [h1]
  | inr hnlt =>
    rw [if_neg hnlt]
    have h1 : moment X % m = (moment X - m) % m := Nat.mod_eq_sub_mod (Nat.le_of_not_lt hnlt)
    rw [← h1]
}

lemma sub_mod2_nil (m : Nat) (a : Nat) :
    sub_mod2 m a [] = a % m := by {
  cases a with
  | zero =>
    rw [sub_mod2_zero]
    rw [List.moment_nil]
    rw [Nat.zero_mod, Nat.sub_zero, Nat.mod_self]
  | succ a =>
    unfold sub_mod2
    rw [List.moment_nil]
    rw [if_pos (Nat.zero_lt_succ _)]
    rw [Nat.sub_zero]
}

lemma sub_mod2_add (m : Nat) (a : Nat) (X : List B) :
  sub_mod2 m (a + m) X = sub_mod2 m a X := by {
  induction a using Nat.case_strong_induction_on with
  | hz =>
    rw [Nat.zero_add]
    rw [sub_mod2_mod_self]
  | hi a IHa =>
    unfold sub_mod2
    cases Decidable.em (moment X < a + 1) with
    | inl hlt =>
      rw [if_pos hlt]
      rw [if_pos]
      · rw [Nat.add_comm (a + 1)]
        rw [Nat.add_sub_assoc]
        · rw [Nat.add_mod_right]
        · exact Nat.le_of_lt hlt
      · exact Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _)
    | inr hnlt =>
      rw [if_neg hnlt]
      cases Decidable.em (moment X < a + 1 + m) with
      | inl hlt' =>
        rw [if_pos hlt']
        have H1 : (moment X - (a + 1)) % m = moment X - (a + 1) := Nat.mod_eq_of_lt (by {
          -- rw nat.sub_lt_left_iff_lt_add hnlt, apply hlt'
          sorry
        })
        rw [H1]
        -- rw sub_sub_eq_add_sub hnlt, rw add_comm
        sorry
      | inr hnlt' =>
        rw [if_neg hnlt']
        -- rw ← nat.sub_sub, rw ← mod_eq_sub_mod
        sorry
}

end List
