import VTlean.B
import VTlean.InsDel
import VTlean.NumOsNumIs

namespace List
variable (X Y : List B) (i j : Nat) (b : B)

lemma num_Os_cons (x : B) (X : List B) : num_Os (x::X) = num_Os [x] + num_Os X := by
  cases x
  · change num_Os X + 1 = 1 + num_Os X
    rw [Nat.add_comm]
  · change num_Os X = 0 + num_Os X
    rw [Nat.zero_add]

lemma num_Os_le_cons (x : B) (X : List B) : num_Os X ≤ num_Os (x::X) := by
  cases x
  · change num_Os X ≤ num_Os X + 1
    apply Nat.le_succ
  · change num_Os X ≤ num_Os X
    apply Nat.le_refl

lemma num_Os_cons_le (x : B) (X : List B) : num_Os (x::X) ≤ num_Os X + 1 := by
  cases x
  · change num_Os X + 1 ≤ num_Os X + 1
    apply Nat.le_refl
  · change num_Os X ≤ num_Os X + 1
    apply Nat.le_succ

lemma num_Os_le_length (X : List B) : num_Os X ≤ length X := by
  induction X with
  | nil => exact Nat.le_refl 0
  | cons x X' ih =>
    cases x
    · change num_Os X' + 1 ≤ length X' + 1
      apply Nat.succ_le_succ ih
    · change num_Os X' ≤ length X' + 1
      apply Nat.le_succ_of_le ih

lemma num_Os_sDel_le (X : List B) (i : Nat) : num_Os (sDel X i) ≤ num_Os X := by
  revert i
  induction X with
  | nil => intro i; exact Nat.le_refl 0
  | cons x X' ih =>
    intro i
    cases X' with
    | nil =>
      rw [sDel_singleton]
      exact Nat.zero_le _
    | cons x' X'' =>
      cases i with
      | zero =>
        rw [sDel_zero]
        apply num_Os_le_cons
      | succ i' =>
        change num_Os (x :: sDel (x'::X'') i') ≤ num_Os (x :: x' :: X'')
        cases x
        · change num_Os (sDel (x'::X'') i') + 1 ≤ num_Os (x'::X'') + 1
          apply Nat.succ_le_succ (ih i')
        · change num_Os (sDel (x'::X'') i') ≤ num_Os (x'::X'')
          apply ih i'

lemma num_Os_sDel_le_length (X : List B) (i : Nat) : num_Os (sDel X i) ≤ length X - 1 := by
  have h1 : num_Os (sDel X i) ≤ length (sDel X i) := num_Os_le_length _
  have h2 : length (sDel X i) = length X - 1 := length_sDel X i
  rw [h2] at h1
  exact h1

lemma num_Os_sIns_zero (X : List B) (i : Nat) : num_Os (sIns X i B.O) = num_Os X + 1 := by
  revert i
  induction X with
  | nil =>
    intro i
    cases i with | zero => rfl | succ _ => rfl
  | cons x X' ih =>
    intro i
    cases i with
    | zero =>
      change num_Os (B.O :: x :: X') = num_Os (x :: X') + 1
      rfl
    | succ i' =>
      change num_Os (x :: sIns X' i' B.O) = num_Os (x :: X') + 1
      cases x
      · change num_Os (sIns X' i' B.O) + 1 = num_Os X' + 1 + 1
        rw [ih i']
      · change num_Os (sIns X' i' B.O) = num_Os X' + 1
        rw [ih i']

lemma num_Os_sIns_one (X : List B) (i : Nat) : num_Os (sIns X i B.I) = num_Os X := by
  revert i
  induction X with
  | nil =>
    intro i
    cases i with | zero => rfl | succ _ => rfl
  | cons x X' ih =>
    intro i
    cases i with
    | zero =>
      change num_Os (B.I :: x :: X') = num_Os (x :: X')
      rfl
    | succ i' =>
      change num_Os (x :: sIns X' i' B.I) = num_Os (x :: X')
      cases x
      · change num_Os (sIns X' i' B.I) + 1 = num_Os X' + 1
        rw [ih i']
      · change num_Os (sIns X' i' B.I) = num_Os X'
        rw [ih i']

lemma num_Os_le_sIns (X : List B) (i : Nat) (a : B) : num_Os X ≤ num_Os (sIns X i a) := by
  cases a
  · rw [num_Os_sIns_zero]
    apply Nat.le_add_right
  · rw [num_Os_sIns_one]

lemma num_Is_cons (x : B) (X : List B) : num_Is (x::X) = num_Is [x] + num_Is X := by
  cases x
  · change num_Is X = 0 + num_Is X
    rw [Nat.zero_add]
  · change num_Is X + 1 = 1 + num_Is X
    rw [Nat.add_comm]

lemma num_Is_le_cons (x : B) (X : List B) : num_Is X ≤ num_Is (x::X) := by
  cases x
  · change num_Is X ≤ num_Is X
    apply Nat.le_refl
  · change num_Is X ≤ num_Is X + 1
    apply Nat.le_succ

lemma num_Is_cons_le (x : B) (X : List B) : num_Is (x::X) ≤ num_Is X + 1 := by
  cases x
  · change num_Is X ≤ num_Is X + 1
    apply Nat.le_succ
  · change num_Is X + 1 ≤ num_Is X + 1
    apply Nat.le_refl

lemma num_Is_le_length (X : List B) : num_Is X ≤ length X := by
  induction X with
  | nil => exact Nat.le_refl 0
  | cons x X' ih =>
    cases x
    · change num_Is X' ≤ length X' + 1
      apply Nat.le_succ_of_le ih
    · change num_Is X' + 1 ≤ length X' + 1
      apply Nat.succ_le_succ ih

lemma num_Is_sDel_le (X : List B) (i : Nat) : num_Is (sDel X i) ≤ num_Is X := by
  revert i
  induction X with
  | nil => intro i; exact Nat.le_refl 0
  | cons x X' ih =>
    intro i
    cases X' with
    | nil =>
      rw [sDel_singleton]
      exact Nat.zero_le _
    | cons x' X'' =>
      cases i with
      | zero =>
        rw [sDel_zero]
        apply num_Is_le_cons
      | succ i' =>
        change num_Is (x :: sDel (x'::X'') i') ≤ num_Is (x :: x' :: X'')
        cases x
        · change num_Is (sDel (x'::X'') i') ≤ num_Is (x'::X'')
          apply ih i'
        · change num_Is (sDel (x'::X'') i') + 1 ≤ num_Is (x'::X'') + 1
          apply Nat.succ_le_succ (ih i')

lemma num_Is_sDel_le_length (X : List B) (i : Nat) : num_Is (sDel X i) ≤ length X - 1 := by
  have h1 : num_Is (sDel X i) ≤ length (sDel X i) := num_Is_le_length _
  have h2 : length (sDel X i) = length X - 1 := length_sDel X i
  rw [h2] at h1
  exact h1

lemma num_Is_le_sDel (X : List B) (i : Nat) : num_Is X - 1 ≤ num_Is (sDel X i) := by
  revert i
  induction X with
  | nil => intro i; exact Nat.le_refl 0
  | cons x X' ih =>
    intro i
    cases X' with
    | nil =>
      cases x
      · exact Nat.le_refl 0
      · exact Nat.le_refl 0
    | cons x' X'' =>
      cases i with
      | zero =>
        rw [sDel_zero]
        cases x
        · change num_Is (x' :: X'') - 1 ≤ num_Is (x' :: X'')
          apply Nat.sub_le
        · change num_Is (x' :: X'') + 1 - 1 ≤ num_Is (x' :: X'')
          rw [Nat.add_sub_cancel]
      | succ i' =>
        change num_Is (x :: x' :: X'') - 1 ≤ num_Is (x :: sDel (x'::X'') i')
        cases x
        · change num_Is (x' :: X'') - 1 ≤ num_Is (sDel (x'::X'') i')
          apply ih i'
        · change num_Is (x' :: X'') + 1 - 1 ≤ num_Is (sDel (x'::X'') i') + 1
          rw [Nat.add_sub_cancel]
          have h_ih := ih i'
          cases h_num : num_Is (x' :: X'') with
          | zero => exact Nat.zero_le _
          | succ n =>
            rw [h_num] at h_ih
            change n ≤ num_Is (sDel (x'::X'') i') at h_ih
            apply Nat.succ_le_succ h_ih

lemma num_Is_sIns_zero (X : List B) (i : Nat) : num_Is (sIns X i B.O) = num_Is X := by
  revert i
  induction X with
  | nil =>
    intro i
    cases i with | zero => rfl | succ _ => rfl
  | cons x X' ih =>
    intro i
    cases i with
    | zero =>
      change num_Is (B.O :: x :: X') = num_Is (x :: X')
      rfl
    | succ i' =>
      change num_Is (x :: sIns X' i' B.O) = num_Is (x :: X')
      cases x
      · change num_Is (sIns X' i' B.O) = num_Is X'
        rw [ih i']
      · change num_Is (sIns X' i' B.O) + 1 = num_Is X' + 1
        rw [ih i']

lemma num_Is_sIns_one (X : List B) (i : Nat) : num_Is (sIns X i B.I) = num_Is X + 1 := by
  revert i
  induction X with
  | nil =>
    intro i
    cases i with | zero => rfl | succ _ => rfl
  | cons x X' ih =>
    intro i
    cases i with
    | zero =>
      change num_Is (B.I :: x :: X') = num_Is (x :: X') + 1
      rfl
    | succ i' =>
      change num_Is (x :: sIns X' i' B.I) = num_Is (x :: X') + 1
      cases x
      · change num_Is (sIns X' i' B.I) = num_Is X' + 1
        rw [ih i']
      · change num_Is (sIns X' i' B.I) + 1 = num_Is X' + 1 + 1
        rw [ih i']

lemma num_Is_le_sIns (X : List B) (i : Nat) (a : B) : num_Is X ≤ num_Is (sIns X i a) := by
  cases a
  · rw [num_Is_sIns_zero]
  · rw [num_Is_sIns_one]
    apply Nat.le_add_right

lemma eq_rep0_of_num_Is (H : num_Is X = 0) : X = replicate (length X) B.O := by
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · change B.O :: X' = replicate (length X' + 1) B.O
      have h1 : replicate (length X' + 1) B.O = B.O :: replicate (length X') B.O := rfl
      rw [h1]
      congr 1
      change num_Is X' = 0 at H
      apply ih H
    · change num_Is X' + 1 = 0 at H
      contradiction

lemma sDel_of_num_Is_0 (H : num_Is X = 0) (i : Nat) : sDel X i = replicate (length X - 1) B.O := by
  have eq := eq_rep0_of_num_Is X H
  have h1 : sDel X i = sDel (replicate (length X) B.O) i := by congr 1
  rw [h1, sDel_replicate]

lemma sDel_of_num_Is_1 (H : num_Is X = 1) : ∃ i : Nat, sDel X i = replicate (length X - 1) B.O := by
  induction X with
  | nil =>
    exact ⟨0, rfl⟩
  | cons x X' ih =>
    cases X' with
    | nil =>
      exact ⟨0, rfl⟩
    | cons x' X'' =>
      cases x
      · change num_Is (x' :: X'') = 1 at H
        cases ih H with
        | intro i' hi' =>
          exact ⟨i' + 1, by {
            change B.O :: sDel (x' :: X'') i' = B.O :: replicate (length (x' :: X'') - 1) B.O
            rw [hi']
          }⟩
      · change num_Is (x' :: X'') + 1 = 1 at H
        have H' : num_Is (x' :: X'') = 0 := Nat.add_right_cancel H
        exact ⟨0, by {
            change sDel (B.I :: x' :: X'') 0 = replicate (length (B.I :: x' :: X'') - 1) B.O
            change x' :: X'' = replicate (length (x' :: X'')) B.O
            exact eq_rep0_of_num_Is _ H'
        }⟩

lemma sDel_of_num_Is_le (H : num_Is X ≤ 1) : ∃ i : Nat, sDel X i = replicate (length X - 1) B.O := by
  cases Classical.em (num_Is X = 1) with
  | inl h => exact sDel_of_num_Is_1 X h
  | inr h =>
    have h0 : num_Is X = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ (Nat.lt_of_le_of_ne H h))
    exact ⟨0, sDel_of_num_Is_0 X h0 0⟩

lemma eq_rep1_of_num_Is (H : num_Is X = length X) : X = replicate (length X) B.I := by
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · change num_Is X' = length X' + 1 at H
      have hl := num_Is_le_length X'
      rw [H] at hl
      have hc : ¬ (length X' + 1 ≤ length X') := Nat.not_succ_le_self _
      contradiction
    · change num_Is X' + 1 = length X' + 1 at H
      have H' : num_Is X' = length X' := Nat.add_right_cancel H
      change B.I :: X' = replicate (length X' + 1) B.I
      have h1 : replicate (length X' + 1) B.I = B.I :: replicate (length X') B.I := rfl
      rw [h1]
      congr 1
      apply ih H'

lemma sDel_of_num_Is_n (H : num_Is X = length X) (i : Nat) : sDel X i = replicate (length X - 1) B.I := by
  have eq := eq_rep1_of_num_Is X H
  have h1 : sDel X i = sDel (replicate (length X) B.I) i := by congr 1
  rw [h1, sDel_replicate]

lemma sDel_of_num_Is_n_sub (H : num_Is X = length X - 1) : ∃ i : Nat, sDel X i = replicate (length X - 1) B.I := by
  induction X with
  | nil => exact ⟨0, rfl⟩
  | cons x X' ih =>
    cases X' with
    | nil => exact ⟨0, rfl⟩
    | cons x' X'' =>
      cases x
      · change num_Is (x' :: X'') = length (x' :: X'') + 1 - 1 at H
        have h_sub : length (x' :: X'') + 1 - 1 = length (x' :: X'') := rfl
        rw [h_sub] at H
        exact ⟨0, by {
          change x' :: X'' = replicate (length (x' :: X'')) B.I
          exact eq_rep1_of_num_Is _ H
        }⟩
      · change num_Is (x' :: X'') + 1 = length (x' :: X'') + 1 - 1 at H
        have h_sub : length (x' :: X'') + 1 - 1 = length (x' :: X'') := rfl
        rw [h_sub] at H
        have H' : num_Is (x' :: X'') = length (x' :: X'') - 1 := by {
          rw [← H]
          exact rfl
        }
        cases ih H' with
        | intro i' hi' =>
          exact ⟨i' + 1, by {
            change B.I :: sDel (x' :: X'') i' = B.I :: replicate (length (x' :: X'') - 1) B.I
            rw [hi']
          }⟩

lemma sDel_of_le_num_Is (H : length X - 1 ≤ num_Is X) : ∃ i : Nat, sDel X i = replicate (length X - 1) B.I := by
  cases Classical.em (num_Is X = length X) with
  | inl h => exact ⟨0, sDel_of_num_Is_n X h 0⟩
  | inr h =>
    have H' : num_Is X = length X - 1 := by {
      have hl := num_Is_le_length X
      have hlt : num_Is X < length X := Nat.lt_of_le_of_ne hl h
      have hle2 : num_Is X ≤ length X - 1 := Nat.le_sub_one_of_lt hlt
      exact Nat.le_antisymm hle2 H
    }
    exact sDel_of_num_Is_n_sub X H'

lemma num_Os_eq_len_sub (X : List B) : num_Os X = length X - num_Is X := by
  have h := num_Os_add_num_Is_eq_length X
  omega

lemma num_Is_eq_len_sub (X : List B) : num_Is X = length X - num_Os X := by
  have h := num_Os_add_num_Is_eq_length X
  omega

def num_LOs : List B → Nat → Nat
| [], _ => 0
| _ :: _, 0 => 0
| B.O :: X, n + 1 => num_LOs X n + 1
| B.I :: X, n + 1 => num_LOs X n

lemma num_LOs_zero (X : List B) : num_LOs X 0 = 0 := by
  cases X with
  | nil => rfl
  | cons x X' => rfl

lemma num_LOs_le (X : List B) (i : Nat) : num_LOs X i ≤ i := by
  revert X
  induction i with
  | zero =>
    intro X
    rw [num_LOs_zero]
  | succ i' ih =>
    intro X
    cases X with
    | nil => exact Nat.zero_le _
    | cons x X' =>
      cases x
      · change num_LOs X' i' + 1 ≤ i' + 1
        apply Nat.succ_le_succ (ih X')
      · change num_LOs X' i' ≤ i' + 1
        apply Nat.le_succ_of_le (ih X')

lemma num_LOs_le_num_Os (X : List B) (i : Nat) : num_LOs X i ≤ num_Os X := by
  revert X
  induction i with
  | zero =>
    intro X
    rw [num_LOs_zero]
    exact Nat.zero_le _
  | succ i' ih =>
    intro X
    cases X with
    | nil => exact Nat.zero_le _
    | cons x X' =>
      cases x
      · change num_LOs X' i' + 1 ≤ num_Os X' + 1
        apply Nat.succ_le_succ (ih X')
      · change num_LOs X' i' ≤ num_Os X'
        apply ih X'

lemma num_LOs_of_ovrlen (X : List B) (i : Nat) (H : length X ≤ i) : num_LOs X i = num_Os X := by
  revert i
  induction X with
  | nil =>
    intro i H
    rfl
  | cons x X' ih =>
    intro i H
    cases i with
    | zero => contradiction
    | succ i' =>
      cases x
      · change num_LOs X' i' + 1 = num_Os X' + 1
        rw [ih i' (Nat.le_of_succ_le_succ H)]
      · change num_LOs X' i' = num_Os X'
        rw [ih i' (Nat.le_of_succ_le_succ H)]

lemma num_LOs_le_length (X : List B) (i : Nat) (H : i + 1 ≤ length X) : num_LOs X i ≤ length X - 1 := by
  revert i
  induction X with
  | nil =>
    intro i H
    contradiction
  | cons x X' ih =>
    intro i H
    cases i with
    | zero =>
      rw [num_LOs_zero]
      exact Nat.zero_le _
    | succ i' =>
      cases x
      · change num_LOs X' i' + 1 ≤ length X' + 1 - 1
        have h1 : length X' + 1 - 1 = length X' := rfl
        rw [h1]
        have h_pos : 0 < length X' := Nat.lt_of_lt_of_le (Nat.zero_lt_succ _) (Nat.le_of_succ_le_succ H)
        have h2 : length X' = length X' - 1 + 1 := (Nat.sub_add_cancel h_pos).symm
        rw [h2]
        apply Nat.succ_le_succ
        apply ih i' (Nat.le_of_succ_le_succ H)
      · change num_LOs X' i' ≤ length X' + 1 - 1
        have h1 : length X' + 1 - 1 = length X' := rfl
        rw [h1]
        apply Nat.le_trans (ih i' (Nat.le_of_succ_le_succ H))
        apply Nat.sub_le

lemma num_LOs_le_sDel (X : List B) (i : Nat) (H : i + 1 ≤ length X) : num_LOs X i ≤ num_Os (sDel X i) := by
  revert X
  induction i with
  | zero =>
    intro X H
    rw [num_LOs_zero]
    exact Nat.zero_le _
  | succ i' ih =>
    intro X H
    cases X with
    | nil => exact Nat.zero_le _
    | cons x X' =>
      cases X' with
      | nil =>
        change i' + 2 ≤ 1 at H
        contradiction
      | cons x' X'' =>
        cases x
        · change num_LOs (x' :: X'') i' + 1 ≤ num_Os (B.O :: sDel (x' :: X'') i')
          change num_LOs (x' :: X'') i' + 1 ≤ num_Os (sDel (x' :: X'') i') + 1
          apply Nat.succ_le_succ (ih _ (Nat.le_of_succ_le_succ H))
        · change num_LOs (x' :: X'') i' ≤ num_Os (B.I :: sDel (x' :: X'') i')
          change num_LOs (x' :: X'') i' ≤ num_Os (sDel (x' :: X'') i')
          apply ih _ (Nat.le_of_succ_le_succ H)

lemma num_LOs_sIns (X : List B) (i : Nat) (b : B) (H : i + 1 ≤ length X) : num_LOs (sIns X i b) i = num_LOs X i := by
  revert X
  induction i with
  | zero =>
    intro X H
    rw [num_LOs_zero, num_LOs_zero]
  | succ i' ih =>
    intro X H
    cases X with
    | nil => contradiction
    | cons x X' =>
      cases x
      · change num_LOs (sIns X' i' b) i' + 1 = num_LOs X' i' + 1
        rw [ih X' (Nat.le_of_succ_le_succ H)]
      · change num_LOs (sIns X' i' b) i' = num_LOs X' i'
        rw [ih X' (Nat.le_of_succ_le_succ H)]

lemma num_LOs_sIns_one (X : List B) (i : Nat) (H : length X ≤ i) : num_LOs (sIns X i B.I) i = num_Os X := by
  revert X
  induction i with
  | zero =>
    intro X H
    have H' : length X = 0 := Nat.eq_zero_of_le_zero H
    have hX : X = [] := List.eq_nil_of_length_eq_zero H'
    rw [hX]
    rfl
  | succ i' ih =>
    intro X H
    cases X with
    | nil => rfl
    | cons x X' =>
      cases x
      · change num_LOs (sIns X' i' B.I) i' + 1 = num_Os X' + 1
        rw [ih X' (Nat.le_of_succ_le_succ H)]
      · change num_LOs (sIns X' i' B.I) i' = num_Os X'
        rw [ih X' (Nat.le_of_succ_le_succ H)]

lemma head_of_num_LOs (x : B) (X : List B) (i : Nat) (H : num_LOs (x::X) (i + 1) = 0) : x = B.I := by
  cases x
  · change num_LOs X i + 1 = 0 at H
    contradiction
  · rfl

lemma sIns_one_of_num_LOs (X : List B) (i j : Nat) (H : num_LOs X i = num_LOs X j) : sIns X i B.I = sIns X j B.I := by
  revert i j
  induction X with
  | nil =>
    intro i j H
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' => rfl
    | succ i' =>
      cases j with
      | zero => rfl
      | succ j' => rfl
  | cons x X' ih =>
    intro i j H
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        rw [num_LOs_zero] at H
        have hx : x = B.I := head_of_num_LOs x X' j' H.symm
        rw [hx]
        change B.I :: B.I :: X' = B.I :: sIns X' j' B.I
        congr 1
        rw [hx] at H
        change 0 = num_LOs X' j' at H
        have H' : num_LOs X' 0 = num_LOs X' j' := by { rw [num_LOs_zero]; exact H }
        rw [← ih 0 j' H']
        rw [sIns_zero]
    | succ i' =>
      cases j with
      | zero =>
        rw [num_LOs_zero] at H
        have hx : x = B.I := head_of_num_LOs x X' i' H
        rw [hx]
        change B.I :: sIns X' i' B.I = B.I :: B.I :: X'
        congr 1
        rw [hx] at H
        change num_LOs X' i' = 0 at H
        have H' : num_LOs X' i' = num_LOs X' 0 := by { rw [num_LOs_zero]; exact H }
        rw [ih i' 0 H']
        rw [sIns_zero]
      | succ j' =>
        change x :: sIns X' i' B.I = x :: sIns X' j' B.I
        congr 1
        cases x
        · change num_LOs X' i' + 1 = num_LOs X' j' + 1 at H
          have H' := Nat.succ.inj H
          exact ih i' j' H'
        · change num_LOs X' i' = num_LOs X' j' at H
          exact ih i' j' H

def num_RIs : List B → Nat → Nat
| [], _ => 0
| x :: X, 0 => num_Is (x :: X)
| _ :: X, n + 1 => num_RIs X n

lemma num_RIs_zero (X : List B) : num_RIs X 0 = num_Is X := by
  cases X
  · rfl
  · rfl

lemma num_RIs_le_cons (x : B) (X : List B) (i : Nat) : num_RIs X i ≤ num_RIs (x::X) i := by
  revert x i
  induction X with
  | nil =>
    intro x i
    exact Nat.zero_le _
  | cons x' X' ih =>
    intro x i
    cases i with
    | zero => exact num_Is_le_cons _ _
    | succ i' => exact ih _ _

lemma num_RIs_succ_le (X : List B) (i : Nat) : num_RIs X (i + 1) ≤ num_RIs X i := by
  revert i
  induction X with
  | nil =>
    intro i
    exact Nat.zero_le _
  | cons x X' ih =>
    intro i
    cases i with
    | zero =>
      change num_RIs X' 0 ≤ num_Is (x :: X')
      rw [num_RIs_zero]
      exact num_Is_le_cons _ _
    | succ i' =>
      exact ih i'

lemma num_RIs_le (X : List B) (i : Nat) : num_RIs X i ≤ length X - i := by
  revert i
  induction X with
  | nil =>
    intro i
    exact Nat.zero_le _
  | cons x X' ih =>
    intro i
    cases i with
    | zero =>
      rw [num_RIs_zero, Nat.sub_zero]
      exact num_Is_le_length _
    | succ i' =>
      change num_RIs X' i' ≤ length (x :: X') - (i' + 1)
      have h1 := ih i'
      have h2 : length (x :: X') = length X' + 1 := rfl
      omega

lemma num_RIs_le_num_Is (X : List B) (i : Nat) : num_RIs X i ≤ num_Is X := by
  revert i
  induction X with
  | nil =>
    intro i
    exact Nat.zero_le _
  | cons x X' ih =>
    intro i
    cases i with
    | zero =>
      change num_Is (x :: X') ≤ num_Is (x :: X')
      exact Nat.le_refl _
    | succ i' =>
      exact Nat.le_trans (ih i') (num_Is_le_cons x X')

lemma num_RIs_of_ovrlen (X : List B) (i : Nat) (H : length X ≤ i) : num_RIs X i = 0 := by
  revert i
  induction X with
  | nil =>
    intro i H
    rfl
  | cons x X' ih =>
    intro i H
    cases i with
    | zero => contradiction
    | succ i' =>
      change num_RIs X' i' = 0
      exact ih i' (Nat.le_of_succ_le_succ H)

lemma num_RIs_sIns_zero (X : List B) (i : Nat) : num_RIs (sIns X i B.O) i = num_RIs X i := by
  revert i
  induction X with
  | nil =>
    intro i
    rw [sIns_nil]
    cases i <;> rfl
  | cons x X' ih =>
    intro i
    cases i with
    | zero => rfl
    | succ i' =>
      change num_RIs (sIns X' i' B.O) i' = num_RIs X' i'
      exact ih i'

lemma num_RIs_sIns (X : List B) (i : Nat) (b : B) (H : length X + 1 ≤ i) : num_RIs (sIns X i b) i = num_RIs X i := by
  revert i
  induction X with
  | nil =>
    intro i H
    rw [sIns_nil]
    cases i
    · contradiction
    · rfl
  | cons x X' ih =>
    intro i H
    cases i with
    | zero => contradiction
    | succ i' =>
      change num_RIs (sIns X' i' b) i' = num_RIs X' i'
      exact ih i' (Nat.le_of_succ_le_succ H)

lemma head_of_num_RIs (x : B) (X : List B) (i : Nat) (H : num_RIs (x::X) (i + 1) = num_Is (x::X)) : x = B.O := by
  cases x
  · rfl
  · change num_RIs X i = num_Is X + 1 at H
    have hle := num_RIs_le_num_Is X i
    omega

lemma sIns_zero_of_num_RIs (X : List B) (i j : Nat) (H : num_RIs X i = num_RIs X j) : sIns X i B.O = sIns X j B.O := by
  revert i j
  induction X with
  | nil =>
    intro i j H
    cases i <;> cases j <;> rfl
  | cons x X' ih =>
    intro i j H
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        rw [num_RIs_zero] at H
        have hx : x = B.O := head_of_num_RIs x X' j' H.symm
        rw [hx]
        change B.O :: B.O :: X' = B.O :: sIns X' j' B.O
        congr 1
        rw [hx] at H
        change num_Is X' = num_RIs X' j' at H
        have H' : num_RIs X' 0 = num_RIs X' j' := by { rw [num_RIs_zero]; exact H }
        rw [← ih 0 j' H']
        rw [sIns_zero]
    | succ i' =>
      cases j with
      | zero =>
        rw [num_RIs_zero] at H
        have hx : x = B.O := head_of_num_RIs x X' i' H
        rw [hx]
        change B.O :: sIns X' i' B.O = B.O :: B.O :: X'
        congr 1
        rw [hx] at H
        change num_RIs X' i' = num_Is X' at H
        have H' : num_RIs X' i' = num_RIs X' 0 := by { rw [num_RIs_zero]; exact H }
        rw [ih i' 0 H']
        rw [sIns_zero]
      | succ j' =>
        change x :: sIns X' i' B.O = x :: sIns X' j' B.O
        congr 1
        change num_RIs X' i' = num_RIs X' j' at H
        exact ih i' j' H

lemma num_Is_sDel_lt_sub_mod (X : List B) (i : Nat) : num_Is (sDel X i) < num_RIs X i + i + 1 := by
  revert i
  induction X with
  | nil =>
    intro i
    exact Nat.zero_lt_succ _
  | cons x X' ih =>
    intro i
    cases X' with
    | nil =>
      rw [sDel_singleton]
      exact Nat.zero_lt_succ _
    | cons x' X'' =>
      cases i with
      | zero =>
        rw [sDel_zero, num_RIs_zero]
        have h1 := num_Is_le_cons x (x' :: X'')
        omega
      | succ i' =>
        change num_Is (x :: sDel (x' :: X'') i') < num_RIs (x' :: X'') i' + (i' + 1) + 1
        have h1 := num_Is_cons_le x (sDel (x' :: X'') i')
        have h2 := ih i'
        omega

end List
