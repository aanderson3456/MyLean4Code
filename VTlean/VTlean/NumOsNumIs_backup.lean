import VTlean.B
import VTlean.InsDel
import Mathlib.Data.Finset.Basic

namespace List
variable (X : List B)

def num_Os : List B → Nat
| [] => 0
| B.O :: tail => num_Os tail + 1
| B.I :: tail => num_Os tail

def num_Is : List B → Nat
| [] => 0
| B.O :: tail => num_Is tail
| B.I :: tail => num_Is tail + 1

lemma num_Os_cons (x : B) (X : List B) : num_Os (x::X) = num_Os [x] + num_Os X := by
  cases x
  · change num_Os X + 1 = 1 + num_Os X
    rw [Nat.add_comm]
  · change num_Os X = 0 + num_Os X
    rw [Nat.zero_add]

lemma num_Os_le_cons (x : B) (X : List B) : num_Os X ≤ num_Os (x::X) := by
  cases x
  · exact Nat.le_succ _
  · exact Nat.le_refl _

lemma num_Os_cons_le (x : B) (X : List B) : num_Os (x::X) ≤ num_Os X + 1 := by
  cases x
  · exact Nat.le_refl _
  · exact Nat.le_succ _

lemma num_Os_le_length (X : List B) : num_Os X ≤ X.length := by
  induction X with
  | nil => exact Nat.le_refl 0
  | cons x X' ih =>
    cases x
    · change num_Os X' + 1 ≤ X'.length + 1
      exact Nat.succ_le_succ ih
    · change num_Os X' ≤ X'.length + 1
      exact Nat.le_trans ih (Nat.le_succ _)

lemma num_Os_sDel_le (X : List B) (i : Nat) : num_Os (sDel X i) ≤ num_Os X := by
  revert i
  induction X with
  | nil => intro i; rfl
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
        exact num_Os_le_cons x (x'::X'')
      | succ i' =>
        change num_Os (x :: sDel (x'::X'') i') ≤ num_Os (x :: x' :: X'')
        cases x
        · change num_Os (sDel (x'::X'') i') + 1 ≤ num_Os (x'::X'') + 1
          exact Nat.succ_le_succ (ih i')
        · change num_Os (sDel (x'::X'') i') ≤ num_Os (x'::X'')
          exact ih i'

lemma num_Os_sDel_le_length (X : List B) (i : Nat) : num_Os (sDel X i) ≤ X.length - 1 := by
  apply Nat.le_trans (num_Os_le_length (sDel X i))
  have h := length_sDel X i
  rw [h]

lemma num_Os_sIns_zero (X : List B) (i : Nat) : num_Os (sIns X i B.O) = num_Os X + 1 := by
  revert X
  induction i with
  | zero =>
    intro X
    cases X
    · rfl
    · change num_Os (B.O :: _ :: _) = num_Os (_ :: _) + 1
      rfl
  | succ i' ih =>
    intro X
    cases X with
    | nil => rfl
    | cons x X' =>
      change num_Os (x :: sIns X' i' B.O) = num_Os (x :: X') + 1
      cases x
      · change num_Os (sIns X' i' B.O) + 1 = num_Os X' + 1 + 1
        rw [ih X']
      · change num_Os (sIns X' i' B.O) = num_Os X' + 1
        rw [ih X']

lemma num_Os_sIns_one (X : List B) (i : Nat) : num_Os (sIns X i B.I) = num_Os X := by
  revert X
  induction i with
  | zero =>
    intro X
    cases X
    · rfl
    · change num_Os (B.I :: _ :: _) = num_Os (_ :: _)
      rfl
  | succ i' ih =>
    intro X
    cases X with
    | nil => rfl
    | cons x X' =>
      change num_Os (x :: sIns X' i' B.I) = num_Os (x :: X')
      cases x
      · change num_Os (sIns X' i' B.I) + 1 = num_Os X' + 1
        rw [ih X']
      · change num_Os (sIns X' i' B.I) = num_Os X'
        rw [ih X']

lemma num_Os_le_sIns (X : List B) (i : Nat) (a : B) : num_Os X ≤ num_Os (sIns X i a) := by
  cases a
  · rw [num_Os_sIns_zero]
    exact Nat.le_succ _
  · rw [num_Os_sIns_one]

lemma num_Os_append (X Y : List B) : num_Os (X ++ Y) = num_Os X + num_Os Y := by
  induction X with
  | nil => exact (Nat.zero_add _).symm
  | cons x X' ih =>
    cases x
    · change num_Os (X' ++ Y) + 1 = (num_Os X' + 1) + num_Os Y
      rw [ih, Nat.add_right_comm]
    · change num_Os (X' ++ Y) = num_Os X' + num_Os Y
      exact ih

lemma num_Os_repO (n : Nat) : num_Os (replicate n B.O) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change num_Os (replicate n B.O) + 1 = n + 1
    rw [ih]

lemma num_Os_repI (n : Nat) : num_Os (replicate n B.I) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change num_Os (replicate n B.I) = 0
    exact ih

lemma num_Is_cons (x : B) (X : List B) : num_Is (x::X) = num_Is [x] + num_Is X := by
  cases x
  · change num_Is X = 0 + num_Is X
    rw [Nat.zero_add]
  · change num_Is X + 1 = 1 + num_Is X
    rw [Nat.add_comm]

lemma num_Is_le_cons (x : B) (X : List B) : num_Is X ≤ num_Is (x::X) := by
  cases x
  · exact Nat.le_refl _
  · exact Nat.le_succ _

lemma num_Is_cons_le (x : B) (X : List B) : num_Is (x::X) ≤ num_Is X + 1 := by
  cases x
  · exact Nat.le_succ _
  · exact Nat.le_refl _

lemma num_Is_le_length (X : List B) : num_Is X ≤ X.length := by
  induction X with
  | nil => exact Nat.le_refl 0
  | cons x X' ih =>
    cases x
    · change num_Is X' ≤ X'.length + 1
      exact Nat.le_trans ih (Nat.le_succ _)
    · change num_Is X' + 1 ≤ X'.length + 1
      exact Nat.succ_le_succ ih

lemma num_Is_sDel_le (X : List B) (i : Nat) : num_Is (sDel X i) ≤ num_Is X := by
  revert i
  induction X with
  | nil => intro i; rfl
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
        exact num_Is_le_cons x (x'::X'')
      | succ i' =>
        change num_Is (x :: sDel (x'::X'') i') ≤ num_Is (x :: x' :: X'')
        cases x
        · change num_Is (sDel (x'::X'') i') ≤ num_Is (x'::X'')
          exact ih i'
        · change num_Is (sDel (x'::X'') i') + 1 ≤ num_Is (x'::X'') + 1
          exact Nat.succ_le_succ (ih i')

lemma num_Is_sDel_le_length (X : List B) (i : Nat) : num_Is (sDel X i) ≤ X.length - 1 := by
  apply Nat.le_trans (num_Is_le_length (sDel X i))
  have h := length_sDel X i
  rw [h]

lemma num_Is_le_sDel (X : List B) (i : Nat) : num_Is X - 1 ≤ num_Is (sDel X i) := by
  revert i
  induction X with
  | nil => intro i; rfl
  | cons x X' ih =>
    intro i
    cases X' with
    | nil =>
      cases x
      · rfl
      · rfl
    | cons x' X'' =>
      cases i with
      | zero =>
        cases x
        · change num_Is (x'::X'') - 1 ≤ num_Is (x'::X'')
          exact Nat.sub_le _ _
        · change num_Is (x'::X'') + 1 - 1 ≤ num_Is (x'::X'')
          rw [Nat.add_sub_cancel]
      | succ i' =>
        cases x
        · change num_Is (x'::X'') - 1 ≤ num_Is (sDel (x'::X'') i')
          exact ih i'
        · change num_Is (x'::X'') + 1 - 1 ≤ num_Is (sDel (x'::X'') i') + 1
          have h_ih := ih i'
          omega

lemma num_Is_sIns_zero (X : List B) (i : Nat) : num_Is (sIns X i B.O) = num_Is X := by
  revert X
  induction i with
  | zero =>
    intro X
    cases X
    · rfl
    · change num_Is (B.O :: _ :: _) = num_Is (_ :: _)
      rfl
  | succ i' ih =>
    intro X
    cases X with
    | nil => rfl
    | cons x X' =>
      change num_Is (x :: sIns X' i' B.O) = num_Is (x :: X')
      cases x
      · change num_Is (sIns X' i' B.O) = num_Is X'
        rw [ih X']
      · change num_Is (sIns X' i' B.O) + 1 = num_Is X' + 1
        rw [ih X']

lemma num_Is_sIns_one (X : List B) (i : Nat) : num_Is (sIns X i B.I) = num_Is X + 1 := by
  revert X
  induction i with
  | zero =>
    intro X
    cases X
    · rfl
    · change num_Is (B.I :: _ :: _) = num_Is (_ :: _) + 1
      rfl
  | succ i' ih =>
    intro X
    cases X with
    | nil => rfl
    | cons x X' =>
      change num_Is (x :: sIns X' i' B.I) = num_Is (x :: X') + 1
      cases x
      · change num_Is (sIns X' i' B.I) = num_Is X' + 1
        rw [ih X']
      · change num_Is (sIns X' i' B.I) + 1 = num_Is X' + 1 + 1
        rw [ih X']

lemma num_Is_le_sIns (X : List B) (i : Nat) (b : B) : num_Is X ≤ num_Is (sIns X i b) := by
  cases b
  · rw [num_Is_sIns_zero]
  · rw [num_Is_sIns_one]
    exact Nat.le_succ _

lemma num_Is_append (X Y : List B) : num_Is (X ++ Y) = num_Is X + num_Is Y := by
  induction X with
  | nil => exact (Nat.zero_add _).symm
  | cons x X' ih =>
    cases x
    · change num_Is (X' ++ Y) = num_Is X' + num_Is Y
      exact ih
    · change num_Is (X' ++ Y) + 1 = (num_Is X' + 1) + num_Is Y
      rw [ih, Nat.add_right_comm]

lemma num_Is_repO (n : Nat) : num_Is (replicate n B.O) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change num_Is (replicate n B.O) = 0
    exact ih

lemma num_Is_repI (n : Nat) : num_Is (replicate n B.I) = n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    change num_Is (replicate n B.I) + 1 = n + 1
    rw [ih]

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

lemma sDel_of_num_Is_1 (H : num_Is X = 1) : ∃ i : Nat, sDel X i = replicate (X.length - 1) B.O := by
  induction X with
  | nil => contradiction
  | cons x X' ih =>
    cases X' with
    | nil =>
      exists 0
    | cons x' X'' =>
      cases x
      · have H' : num_Is (x' :: X'') = 1 := H
        cases ih H' with
        | intro i ih_i =>
          exists (i + 1)
          have h_sDel : sDel (B.O :: x' :: X'') (i + 1) = B.O :: sDel (x' :: X'') i := rfl
          rw [h_sDel, ih_i]
          have h_len : (B.O :: x' :: X'').length - 1 = (x' :: X'').length := rfl
          rw [h_len]
          exact List.replicate_succ.symm
      · exists 0
        have h_sDel : sDel (B.I :: x' :: X'') 0 = x' :: X'' := rfl
        rw [h_sDel]
        have h : num_Is (x' :: X'') = 0 := by
          change num_Is (x' :: X'') + 1 = 1 at H
          exact Nat.succ.inj H
        have hx := eq_rep0_of_num_Is (x' :: X'') h
        nth_rw 1 [hx]
        have hl : (B.I :: x' :: X'').length - 1 = (x' :: X'').length := by rfl
        rw [hl]

lemma sDel_of_num_Is_le (H : num_Is X ≤ 1) : ∃ i : Nat, sDel X i = replicate (X.length - 1) B.O := by
  cases Nat.eq_or_lt_of_le H with
  | inl h_eq =>
    exact sDel_of_num_Is_1 _ h_eq
  | inr h_lt =>
    have h_zero : num_Is X = 0 := by omega
    exists 0
    exact sDel_of_num_Is_0 X h_zero 0

lemma eq_rep1_of_num_Is (H : num_Is X = X.length) : X = replicate X.length B.I := by
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · have hnum : num_Is (B.O :: X') = num_Is X' := rfl
      have hlen : (B.O :: X').length = X'.length + 1 := rfl
      rw [hnum, hlen] at H
      have hl : num_Is X' ≤ X'.length := num_Is_le_length X'
      omega
    · have hnum : num_Is (B.I :: X') = num_Is X' + 1 := rfl
      have hlen : (B.I :: X').length = X'.length + 1 := rfl
      rw [hnum, hlen] at H
      have h : num_Is X' = X'.length := by omega
      have hx := ih h
      nth_rw 1 [hx]
      rfl

lemma sDel_of_num_Is_n (H : num_Is X = X.length) (i : Nat) : sDel X i = replicate (X.length - 1) B.I := by
  have hx := eq_rep1_of_num_Is X H
  rw [hx]
  rw [sDel_replicate]
  rw [List.length_replicate]

lemma sDel_of_num_Is_n_sub (H : num_Is X = X.length - 1) : ∃ i : Nat, sDel X i = replicate (X.length - 1) B.I := by
  induction X with
  | nil =>
    exists 0
  | cons x X' ih =>
    cases X' with
    | nil =>
      exists 0
    | cons x' X'' =>
      cases x
      · exists 0
        have h_sDel : sDel (B.O :: x' :: X'') 0 = x' :: X'' := rfl
        rw [h_sDel]
        have hlen : (B.O :: x' :: X'').length = (x' :: X'').length + 1 := rfl
        have hnum : num_Is (B.O :: x' :: X'') = num_Is (x' :: X'') := rfl
        rw [hlen, hnum] at H
        have h : num_Is (x' :: X'') = (x' :: X'').length := by omega
        have hx := eq_rep1_of_num_Is (x' :: X'') h
        nth_rw 1 [hx]
        have hl : (B.O :: x' :: X'').length - 1 = (x' :: X'').length := by rfl
        rw [hl]
      · have hlen : (B.I :: x' :: X'').length = (x' :: X'').length + 1 := rfl
        have hnum : num_Is (B.I :: x' :: X'') = num_Is (x' :: X'') + 1 := rfl
        rw [hlen, hnum] at H
        have H' : num_Is (x' :: X'') = (x' :: X'').length - 1 := by omega
        cases ih H' with
        | intro i ih_i =>
          exists (i + 1)
          have h_sDel : sDel (B.I :: x' :: X'') (i + 1) = B.I :: sDel (x' :: X'') i := rfl
          rw [h_sDel, ih_i]
          have h_len : (B.I :: x' :: X'').length - 1 = (x' :: X'').length := rfl
          rw [h_len]
          exact List.replicate_succ.symm

lemma sDel_of_le_num_Is (H : X.length - 1 ≤ num_Is X) : ∃ i : Nat, sDel X i = replicate (X.length - 1) B.I := by
  cases Nat.eq_or_lt_of_le H with
  | inl h_eq =>
    exact sDel_of_num_Is_n_sub _ h_eq.symm
  | inr h_lt =>
    have h_eq : num_Is X = X.length := by
      have hl := num_Is_le_length X
      omega
    exists 0
    exact sDel_of_num_Is_n X h_eq 0


lemma num_Os_add_num_Is (X : List B) : num_Os X + num_Is X = X.length := by
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · change (num_Os X' + 1) + num_Is X' = X'.length + 1
      rw [Nat.add_right_comm, ih]
    · change num_Os X' + (num_Is X' + 1) = X'.length + 1
      rw [← Nat.add_assoc, ih]

lemma num_Os_eq_len_sub (X : List B) : num_Os X = X.length - num_Is X := by
  have h := num_Os_add_num_Is X
  omega

lemma num_Is_eq_len_sub (X : List B) : num_Is X = X.length - num_Os X := by
  have h := num_Os_add_num_Is X
  omega

lemma num_Is_flip_eq_num_Os (X : List B) : num_Is (B.List.flip X) = num_Os X := by
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · change num_Is (B.List.flip X') + 1 = num_Os X' + 1
      rw [ih]
    · change num_Is (B.List.flip X') = num_Os X'
      rw [ih]

lemma num_Is_flip (X : List B) : num_Is (B.List.flip X) = X.length - num_Is X := by
  rw [num_Is_flip_eq_num_Os]
  exact num_Os_eq_len_sub X

def num_LOs : List B → Nat → Nat
  | [], _ => 0
  | _::_, 0 => 0
  | B.O::X, n+1 => num_LOs X n + 1
  | B.I::X, n+1 => num_LOs X n

lemma num_LOs_zero (X : List B) (i : Nat) : num_LOs X 0 = 0 := by
  cases X
  · rfl
  · rfl

lemma num_LOs_le (X : List B) (i : Nat) : num_LOs X i ≤ i := by
  induction X generalizing i with
  | nil =>
    cases i
    · rfl
    · change 0 ≤ _ + 1
      omega
  | cons x X' ih =>
    cases i with
    | zero => rfl
    | succ i' =>
      cases x
      · change num_LOs X' i' + 1 ≤ i' + 1
        have h := ih i'
        omega
      · change num_LOs X' i' ≤ i' + 1
        have h := ih i'
        omega

lemma num_LOs_le_num_Os (X : List B) (i : Nat) : num_LOs X i ≤ num_Os X := by
  induction X generalizing i with
  | nil =>
    cases i <;> exact Nat.zero_le _
  | cons x X' ih =>
    cases i with
    | zero => exact Nat.zero_le _
    | succ i' =>
      cases x
      · change num_LOs X' i' + 1 ≤ num_Os X' + 1
        have h := ih i'
        omega
      · change num_LOs X' i' ≤ num_Os X'
        have h := ih i'
        omega

lemma num_LOs_of_ovrlen (X : List B) (i : Nat) (H : X.length ≤ i) : num_LOs X i = num_Os X := by
  induction X generalizing i with
  | nil =>
    cases i
    · rfl
    · change 0 = 0; rfl
  | cons x X' ih =>
    cases i with
    | zero => contradiction
    | succ i' =>
      have H' : X'.length ≤ i' := Nat.le_of_succ_le_succ H
      cases x
      · change num_LOs X' i' + 1 = num_Os X' + 1
        have h := ih i' H'
        omega
      · change num_LOs X' i' = num_Os X'
        have h := ih i' H'
        omega

lemma num_LOs_le_length (X : List B) (i : Nat) (H : i + 1 ≤ X.length) : num_LOs X i ≤ X.length - 1 := by
  have h := num_LOs_le X i
  omega

lemma num_LOs_le_sDel (X : List B) (i : Nat) (H : i + 1 ≤ X.length) : num_LOs X i ≤ num_Os (sDel X i) := by
  revert H
  revert X
  induction i with
  | zero =>
    intro X H
    exact Nat.zero_le _
  | succ k ih =>
    intro X H
    cases X with
    | nil => exact Nat.zero_le _
    | cons x X' =>
      cases X' with
      | nil =>
        have h_absurd : k + 2 ≤ 1 := H
        contradiction
      | cons x' X'' =>
        cases x
        · apply Nat.succ_le_succ
          exact ih (x'::X'') (Nat.le_of_succ_le_succ H)
        · exact ih (x'::X'') (Nat.le_of_succ_le_succ H)

lemma num_LOs_sIns (X : List B) (i : Nat) (b : B) (H : i + 1 ≤ X.length) : num_LOs (sIns X i b) i = num_LOs X i := by
  revert H
  revert X
  induction i with
  | zero =>
    intro X H
    rfl
  | succ k ih =>
    intro X H
    cases X with
    | nil =>
      have h_absurd : k + 2 ≤ 0 := H
      contradiction
    | cons x X' =>
      cases x
      · have ih_res := ih X' (Nat.le_of_succ_le_succ H)
        exact congrArg (· + 1) ih_res
      · exact ih X' (Nat.le_of_succ_le_succ H)

lemma num_LOs_sIns_one (X : List B) (i : Nat) (H : X.length ≤ i) : num_LOs (sIns X i B.I) i = num_Os X := by
  induction i generalizing X with
  | zero =>
    have h : X = [] := by
      cases X
      · rfl
      · contradiction
    rw [h]
    rfl
  | succ k ih =>
    cases X with
    | nil => rfl
    | cons x X' =>
      cases x
      · change num_LOs (sIns X' k B.I) k + 1 = num_Os X' + 1
        rw [ih X' (Nat.le_of_succ_le_succ H)]
      · change num_LOs (sIns X' k B.I) k = num_Os X'
        rw [ih X' (Nat.le_of_succ_le_succ H)]

lemma head_of_num_LOs (X : List B) (x : B) (i : Nat) (H : num_LOs (x::X) (i + 1) = 0) : x = B.I := by
  cases x
  · change num_LOs X i + 1 = 0 at H
    contradiction
  · rfl

lemma sIns_one_of_num_LOs (X : List B) (i j : Nat) (H : num_LOs X i = num_LOs X j) : sIns X i B.I = sIns X j B.I := by
  revert i j
  induction X with
  | nil =>
    intro i j _
    rfl
  | cons x X' ih =>
    intro i j H
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        have h1 : num_LOs (x::X') 0 = 0 := rfl
        rw [h1] at H
        have hx := head_of_num_LOs X' x j' H.symm
        subst hx
        apply congrArg
        have H' : num_LOs X' 0 = num_LOs X' j' := by exact H
        exact ih 0 j' H'
    | succ i' =>
      cases j with
      | zero =>
        have h1 : num_LOs (x::X') 0 = 0 := rfl
        rw [h1] at H
        have hx := head_of_num_LOs X' x i' H
        subst hx
        apply congrArg
        have H' : num_LOs X' i' = num_LOs X' 0 := by exact H
        exact ih i' 0 H'
      | succ j' =>
        cases x
        · apply congrArg
          exact ih i' j' (Nat.succ.inj H)
        · apply congrArg
          exact ih i' j' H

def num_RIs : List B → Nat → Nat
  | [], _ => 0
  | x::X, 0 => num_Is (x::X)
  | _::X, n+1 => num_RIs X n

lemma num_RIs_zero (X : List B) : num_RIs X 0 = num_Is X := by
  cases X
  · rfl
  · rfl

lemma num_RIs_le_cons (x : B) (X : List B) (i : Nat) : num_RIs X i ≤ num_RIs (x::X) i := by
  revert x i
  induction X with
  | nil =>
    intro x i
    cases i
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  | cons x' X' ih =>
    intro x i
    cases i with
    | zero =>
      exact num_Is_le_cons x (x'::X')
    | succ i' =>
      exact Nat.le_refl _

lemma num_RIs_succ_le (X : List B) (i : Nat) : num_RIs X (i + 1) ≤ num_RIs X i := by
  induction X generalizing i with
  | nil => exact Nat.le_refl _
  | cons x X' ih =>
    cases i with
    | zero =>
      change num_RIs X' 0 ≤ num_Is (x::X')
      rw [num_RIs_zero]
      exact num_Is_le_cons x X'
    | succ i' =>
      change num_RIs X' (i' + 1) ≤ num_RIs X' i'
      exact ih i'

lemma num_RIs_le (X : List B) (i : Nat) : num_RIs X i ≤ X.length - i := by
  revert i
  induction X with
  | nil =>
    intro i
    exact Nat.zero_le _
  | cons x X' ih =>
    intro i
    cases i with
    | zero =>
      rw [num_RIs_zero]
      exact num_Is_le_length (x::X')
    | succ i' =>
      exact ih i'

lemma num_RIs_le_num_Is (X : List B) (i : Nat) : num_RIs X i ≤ num_Is X := by
  induction X generalizing i with
  | nil => exact Nat.zero_le _
  | cons x X' ih =>
    cases i with
    | zero => exact Nat.le_refl _
    | succ i' =>
      change num_RIs X' i' ≤ num_Is (x::X')
      have h1 := ih i'
      have h2 := num_Is_le_cons x X'
      exact Nat.le_trans h1 h2

lemma num_RIs_of_ovrlen (X : List B) (i : Nat) (H : X.length ≤ i) : num_RIs X i = 0 := by
  induction X generalizing i with
  | nil =>
    cases i
    · rfl
    · rfl
  | cons x X' ih =>
    cases i with
    | zero => contradiction
    | succ i' =>
      change num_RIs X' i' = 0
      exact ih i' (Nat.le_of_succ_le_succ H)

lemma num_RIs_sIns_zero (X : List B) (i : Nat) : num_RIs (sIns X i B.O) i = num_RIs X i := by
  induction X generalizing i with
  | nil =>
    cases i
    · rfl
    · rfl
  | cons x X' ih =>
    cases i with
    | zero =>
      change num_Is (B.O::x::X') = num_Is (x::X')
      rfl
    | succ i' =>
      change num_RIs (sIns X' i' B.O) i' = num_RIs X' i'
      exact ih i'

lemma num_RIs_sIns (X : List B) (i : Nat) (b : B) (H : X.length + 1 ≤ i) : num_RIs (sIns X i b) i = num_RIs X i := by
  induction X generalizing i with
  | nil =>
    cases i
    · contradiction
    · rfl
  | cons x X' ih =>
    cases i with
    | zero => contradiction
    | succ i' =>
      change num_RIs (sIns X' i' b) i' = num_RIs X' i'
      exact ih i' (Nat.le_of_succ_le_succ H)

lemma head_of_num_RIs (X : List B) (x : B) (i : Nat) (H : num_RIs (x::X) (i + 1) = num_Is (x::X)) : x = B.O := by
  cases x
  · rfl
  · have h1 : num_RIs (B.I::X) (i + 1) ≤ num_Is (B.I::X) := num_RIs_le_num_Is _ _
    change num_RIs X i = num_Is X + 1 at H
    have h2 : num_RIs X i ≤ num_Is X := num_RIs_le_num_Is _ _
    omega

lemma sIns_zero_of_num_RIs (X : List B) (i j : Nat) (H : num_RIs X i = num_RIs X j) : sIns X i B.O = sIns X j B.O := by
  revert i j
  induction X with
  | nil => 
    intro i j _
    rfl
  | cons x X' ih =>
    intro i j H
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        have h1 : num_RIs (x::X') 0 = num_Is (x::X') := rfl
        rw [h1] at H
        have H_symm : num_RIs (x::X') (j' + 1) = num_Is (x::X') := H.symm
        have hx := head_of_num_RIs X' x j' H_symm
        subst hx
        apply congrArg
        have H' : num_RIs X' 0 = num_RIs X' j' := by exact H
        exact ih 0 j' H'
    | succ i' =>
      cases j with
      | zero =>
        have h1 : num_RIs (x::X') 0 = num_Is (x::X') := rfl
        rw [h1] at H
        have hx := head_of_num_RIs X' x i' H
        subst hx
        apply congrArg
        have H' : num_RIs X' i' = num_RIs X' 0 := by exact H
        exact ih i' 0 H'
      | succ j' =>
        apply congrArg
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
      have h1 : num_Is (sDel [x] i) = 0 := by cases i <;> rfl
      have h2 : num_RIs [x] i + i + 1 ≥ 1 := by omega
      omega
    | cons x' X'' =>
      cases i with
      | zero =>
        have h := num_Is_le_cons x (x'::X'')
        omega
      | succ i' =>
        have h1 := num_Is_cons_le x (sDel (x'::X'') i')
        have h2 := ih i'
        omega

end List
