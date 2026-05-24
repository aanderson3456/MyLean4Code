import re

with open('VTlean/VTCode.lean', 'r') as f:
    content = f.read()

# Fix sub_mod_add
old_sub_mod_add = """  | hi a IHa =>
    unfold sub_mod
    cases Decidable.em (moment X < a + 1) with
    | inl hlt =>
      rw [if_pos hlt]
      have hlt_add : moment X < a + 1 + m := Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _)
      rw [if_pos hlt_add]
      rw [Nat.add_comm (a + 1)]
      rw [Nat.add_sub_assoc]
      · rw [Nat.add_comm m, Nat.add_mod_right]
      · exact Nat.le_of_lt hlt
    | inr hnlt =>
      rw [if_neg hnlt]
      have hnlt2 : ¬ moment X < a + 1 := hnlt
      rw [Nat.not_lt] at hnlt
      cases Decidable.em (moment X < a + 1 + m) with
      | inl hlt' =>
        rw [if_pos hlt']
        -- rw @mod_eq_of_lt ((ρ X) - (a + 1))
        -- rw sub_sub_eq_add_sub hnlt, rw add_comm
        -- rw nat.sub_lt_left_iff_lt_add hnlt, apply hlt'
        sorry
      | inr hnlt' =>
        rw [if_neg hnlt']
        -- rw ← nat.sub_sub, rw ← mod_eq_sub_mod
        -- rw ge, rw nat.le_sub_left_iff_add_le hnlt, apply hnlt'
        sorry
}"""
new_sub_mod_add = """  | hi a IHa =>
    unfold sub_mod
    cases Decidable.em (moment X < a + 1) with
    | inl hlt =>
      rw [if_pos hlt]
      have hlt_add : moment X < a + 1 + m := Nat.lt_of_lt_of_le hlt (Nat.le_add_right _ _)
      rw [if_pos hlt_add]
      rw [Nat.add_comm (a + 1)]
      rw [Nat.add_sub_assoc]
      · rw [Nat.add_comm m, Nat.add_mod_right]
      · exact Nat.le_of_lt hlt
    | inr hnlt =>
      rw [if_neg hnlt]
      have hnlt2 : ¬ moment X < a + 1 := hnlt
      rw [Nat.not_lt] at hnlt
      cases Decidable.em (moment X < a + 1 + m) with
      | inl hlt' =>
        rw [if_pos hlt']
        rw [Nat.mod_eq_of_lt]
        · have h1 : a + 1 + m - moment X = m - (moment X - (a + 1)) := by omega
          rw [h1]
        · omega
      | inr hnlt' =>
        rw [if_neg hnlt']
        have h1 : a + 1 + m - moment X = a + 1 - moment X + m := by omega
        rw [h1, Nat.add_comm, Nat.add_mod_right]
}"""
content = content.replace(old_sub_mod_add, new_sub_mod_add)

old_sub_mod_mod = """      | inr hnle =>
        -- rw mod_eq_sub_mod (le_of_not_ge hnle), rw IHa
        -- rw sub_mod_sub _ _ _ (le_of_not_ge hnle)
        -- rw succ_sub_succ, apply nat.sub_le
        sorry
}"""
new_sub_mod_mod = """      | inr hnle =>
        rw [Nat.not_le] at hnle
        have hle : m + 1 ≤ a + 1 := Nat.le_of_lt hnle
        have hle2 : m ≤ a := Nat.le_of_succ_le_succ hle
        have h_mod : (a + 1) % (m + 1) = (a + 1 - (m + 1)) % (m + 1) := by {
          rw [Nat.mod_eq_sub_mod hle]
        }
        have h_sub : a + 1 - (m + 1) = a - m := by omega
        rw [h_mod, h_sub]
        rw [IHa (a - m) (by omega)]
        rw [← sub_mod_sub m X hle2]
}"""
content = content.replace(old_sub_mod_mod, new_sub_mod_mod)

with open('VTlean/VTCode.lean', 'w') as f:
    f.write(content)
