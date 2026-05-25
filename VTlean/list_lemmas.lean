lemma eq_rep0_of_num_Is (H : num_Is X = 0) : X = replicate X.length B.O := by
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · have h : num_Is X' = 0 := H
      have hx : X' = replicate X'.length B.O := ih h
      nth_rw 1 [hx]
      rfl
    · change num_Is X' + 1 = 0 at H
      contradiction

lemma sDel_of_num_Is_0 (H : num_Is X = 0) (i : Nat) : sDel X i = replicate (X.length - 1) B.O := by
  have hx := eq_rep0_of_num_Is X H
  rw [hx]
  rw [sDel_replicate]
  rw [List.length_replicate]

lemma sDel_of_num_Is_1 (H : num_Is X = 1) : ∃ i : Nat, sDel X i = replicate (X.length - 1) B.O ∨ num_Is (sDel X i) = 1 := by
  sorry

lemma sDel_of_num_Is_le (H : num_Is X ≤ 1) : ∃ i : Nat, sDel X i = replicate (X.length - 1) B.O := by
  sorry

lemma eq_rep1_of_num_Is (H : num_Is X = X.length) : X = replicate X.length B.I := by
  sorry

lemma sDel_of_num_Is_n (H : num_Is X = X.length) (i : Nat) : sDel X i = replicate (X.length - 1) B.I := by
  sorry

lemma sDel_of_num_Is_n_sub (H : num_Is X = X.length - 1) : ∃ i : Nat, sDel X i = replicate (X.length - 1) B.I := by
  sorry

lemma sDel_of_le_num_Is (H : X.length - 1 ≤ num_Is X) : ∃ i : Nat, sDel X i = replicate (X.length - 1) B.I := by
  sorry

