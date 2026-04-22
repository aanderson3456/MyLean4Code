import VTlean.InsDel

open Finset List.Vector

variable {n : Nat}

lemma mem_IS_le (x : List.Vector B n) (k : Nat) (y : List.Vector B (n + 1)) :
  y ∈ IS_le x k ↔ ∃ i : Nat, ∃ b : B, i ≤ k ∧ y = sIns x i b :=
by {
  induction k with
  | zero =>
    apply Iff.intro
    · intro hy
      unfold IS_le at hy
      cases hy with
      | head _ => 
        use 0, B.O
      | tail _ hy =>
        cases hy with
        | head _ => 
          use 0, B.I
        | tail _ hy => contradiction
    · intro hy
      rcases hy with ⟨i, b, hi, rfl⟩
      have hi0 : i = 0 := Nat.eq_zero_of_le_zero hi
      rw [hi0]
      cases b
      · exact List.Mem.head _
      · apply List.Mem.tail; exact List.Mem.head _
  | succ k ih =>
    apply Iff.intro
    · intro hy
      unfold IS_le at hy
      cases hy with
      | head _ => 
        use k + 1, B.O
      | tail _ hy =>
        cases hy with
        | head _ => 
          use k + 1, B.I
        | tail _ hy =>
          have hy' := ih.mp hy
          rcases hy' with ⟨i, b, hi, hyib⟩
          use i, b
          exact ⟨Nat.le_trans hi (Nat.le_succ _), hyib⟩
    · intro hy
      rcases hy with ⟨i, b, hi, hyib⟩
      unfold IS_le
      cases Classical.em (i = k + 1) with
      | inl heq =>
        cases b
        · rw [hyib, heq]; exact List.Mem.head _
        · rw [hyib, heq]; apply List.Mem.tail; exact List.Mem.head _
      | inr hneq =>
        apply List.Mem.tail; apply List.Mem.tail
        apply ih.mpr
        use i, b
        exact ⟨Nat.le_of_lt_succ (Nat.lt_of_le_of_ne hi hneq), hyib⟩
}

lemma mem_IS_list (x : List.Vector B n) (y : List.Vector B (n + 1)) :
  y ∈ IS_list x ↔ ∃ i : Nat, ∃ b : B, y = sIns x i b :=
by {
  unfold IS_list
  have H := mem_IS_le x n y
  cases n with
  | zero =>
    apply Iff.intro
    · intro hy
      have hy' := H.mp hy
      rcases hy' with ⟨i, b, hi, rfl⟩
      use i, b
    · rintro ⟨i, b, rfl⟩
      apply H.mpr
      have h_len : x.val.length = 0 := x.property
      have h1 : x.val.length ≤ i := Nat.le_trans (Nat.le_of_eq h_len) (Nat.zero_le i)
      have h2 : x.val.length ≤ 0 := Nat.le_of_eq h_len
      have heq : sIns x i b = sIns x 0 b := by {
        apply Subtype.ext
        change List.sIns x.val i b = List.sIns x.val 0 b
        rw [List.sIns_of_ovrlen _ _ _ h1, List.sIns_of_ovrlen _ _ _ h2]
      }
      exact ⟨0, b, Nat.le_refl 0, heq⟩
  | succ m =>
    apply Iff.intro
    · intro hy
      have hy' := H.mp hy
      rcases hy' with ⟨i, b, hi, rfl⟩
      use i, b
    · rintro ⟨i, b, rfl⟩
      apply H.mpr
      cases Classical.em (i < Nat.succ (Nat.succ m)) with
      | inl hlt =>
        use i, b
        exact ⟨Nat.le_of_lt_succ hlt, rfl⟩
      | inr hnlt =>
        have h_len : x.val.length = Nat.succ m := x.property
        have h1 : x.val.length ≤ i := by {
          rw [h_len]
          exact Nat.le_trans (Nat.le_succ _) (Nat.le_of_not_lt hnlt)
        }
        have h2 : x.val.length ≤ Nat.succ m := Nat.le_of_eq h_len
        have h_eq : sIns x i b = sIns x (Nat.succ m) b := by {
          apply Subtype.ext
          change List.sIns x.val i b = List.sIns x.val (Nat.succ m) b
          rw [List.sIns_of_ovrlen _ _ _ h1, List.sIns_of_ovrlen _ _ _ h2]
        }
        exact ⟨Nat.succ m, b, Nat.le_refl _, h_eq⟩
}

lemma mem_IS (x : List.Vector B n) (y : List.Vector B (n + 1)) :
  y ∈ IS x ↔ ∃ i : Nat, ∃ b : B, y = sIns x i b :=
by {
  unfold IS
  rw [List.mem_toFinset]
  exact mem_IS_list x y
}
