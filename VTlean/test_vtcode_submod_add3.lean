import VTlean.VTCode

open Nat Finset B

namespace List

lemma sub_mod_add3 (m : Nat) (a : Nat) (X : List B) :
  sub_mod m (a + m) X = sub_mod m a X := by {
  induction a using Nat.case_strong_induction_on with
  | hz =>
    rw [Nat.zero_add]
    rw [sub_mod_mod_self]
  | hi a IHa =>
    unfold sub_mod
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
      have hnlt2 : a + 1 ≤ moment X := Nat.le_of_not_lt hnlt
      cases Decidable.em (moment X < a + 1 + m) with
      | inl hlt' =>
        rw [if_pos hlt']
        have H1 : (moment X - (a + 1)) % m = moment X - (a + 1) := Nat.mod_eq_of_lt (by {
          exact Nat.sub_lt_left_of_lt_add hnlt2 hlt'
        })
        rw [H1]
        have H2 : (a + 1 + m - moment X) = m - (moment X - (a + 1)) := by {
          rw [Nat.add_comm (a + 1)]
          rw [Nat.sub_sub_eq_add_sub hnlt2]
          rfl
        }
        rw [H2]
      | inr hnlt' =>
        rw [if_neg hnlt']
        have hnlt'2 : a + 1 + m ≤ moment X := Nat.le_of_not_lt hnlt'
        have H3 : moment X - (a + 1 + m) = moment X - (a + 1) - m := by {
          rw [Nat.sub_sub]
        }
        rw [H3]
        have H4 : (moment X - (a + 1) - m) % m = (moment X - (a + 1)) % m := by {
          have h_le : m ≤ moment X - (a + 1) := by {
            rw [Nat.le_sub_iff_add_le hnlt2]
            rw [Nat.add_comm m]
            exact hnlt'2
          }
          exact Eq.symm (Nat.mod_eq_sub_mod h_le)
        }
        rw [H4]
}

end List
