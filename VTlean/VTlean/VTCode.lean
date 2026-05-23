/- Copyright Yuki Kondo c/o Manabu Hagiwara 2022, 2026 -/
import VTlean.NumOsNumIs
import VTlean.InsDel
import Mathlib
import VTlean.DelCode


open Nat Finset B
namespace List
variable (X Y : List B) (x : B) (i : Nat)

def moment_sub : List B → Nat → Nat
| [], _ => 0
| B.O :: tail, n => moment_sub tail (n + 1)
| B.I :: tail, n => moment_sub tail (n + 1) + n

lemma moment_sub_succ (X : List B) (n : Nat) :
  moment_sub X (n + 1) = moment_sub X n + num_Is X := by
  revert n
  induction X with
  | nil =>
    intro n; rfl
  | cons x X' ih =>
    intro n
    cases x
    · change moment_sub X' (n + 1 + 1) = moment_sub X' (n + 1) + num_Is X'
      rw [ih (n + 1)]
    · change moment_sub X' (n + 1 + 1) + (n + 1) = moment_sub X' (n + 1) + n + (num_Is X' + 1)
      rw [ih (n + 1)]
      ac_rfl

def moment (X : List B) : Nat := moment_sub X 1

/-! We use macroscopic lemmas mapped correctly to List native forms. -/


def num_RIs (X : List B) (i : Nat) : Nat := num_Is (X.drop i)
def num_LOs (X : List B) (i : Nat) : Nat := num_Os (X.take i)

lemma moment_nil : moment ([] : List B) = 0 := rfl

lemma moment_zero : moment [B.O] = 0 := rfl

lemma moment_one : moment [B.I] = 1 := rfl

lemma moment_singleton (x : B) : moment [x] = num_Is [x] := by
  cases x <;> rfl

lemma moment_cons (x : B) (X : List B) :
  moment (x :: X) = moment X + num_Is (x :: X) := by
  cases x
  · change moment_sub X 2 = moment_sub X 1 + num_Is X
    exact moment_sub_succ X 1
  · change moment_sub X 2 + 1 = moment_sub X 1 + (num_Is X + 1)
    rw [moment_sub_succ X 1]
    ac_rfl


lemma moment_le_cons (x : B) (X : List B) :
  moment X ≤ moment (x :: X) := by {
  rw [moment_cons]
  exact Nat.le_add_right _ _
}

lemma moment_sub_append (X Y : List B) (n : Nat) :
  List.moment_sub (X ++ Y) n = List.moment_sub X n + List.moment_sub Y (n + X.length) := by {
  revert n
  induction X with
  | nil =>
    intro n
    rw [List.nil_append]
    have h_len : ([] : List B).length = 0 := rfl
    rw [h_len]
    change List.moment_sub Y n = 0 + List.moment_sub Y (n + 0)
    rw [Nat.zero_add, Nat.add_zero]
  | cons x X' ih =>
    intro n
    cases x
    · change List.moment_sub (X' ++ Y) (n + 1) = List.moment_sub X' (n + 1) + List.moment_sub Y (n + (X'.length + 1))
      have h : n + (X'.length + 1) = n + 1 + X'.length := by ac_rfl
      rw [h]
      exact ih (n + 1)
    · change List.moment_sub (X' ++ Y) (n + 1) + n = List.moment_sub X' (n + 1) + n + List.moment_sub Y (n + (X'.length + 1))
      have h : n + (X'.length + 1) = n + 1 + X'.length := by ac_rfl
      rw [h]
      have ih_eval := ih (n + 1)
      rw [ih_eval]
      ac_rfl
}

lemma moment_append_O (X : List B) :
  List.moment (X ++ [B.O]) = List.moment X := by {
  unfold List.moment
  rw [moment_sub_append]
  have h0 : List.moment_sub [B.O] (1 + X.length) = 0 := rfl
  rw [h0, Nat.add_zero]
}

lemma moment_append_I (X : List B) :
  List.moment (X ++ [B.I]) = List.moment X + X.length + 1 := by {
  unfold List.moment
  rw [moment_sub_append]
  have h1 : List.moment_sub [B.I] (1 + X.length) = 1 + X.length := by {
    change List.moment_sub [] (1 + X.length + 1) + (1 + X.length) = 1 + X.length
    change 0 + (1 + X.length) = 1 + X.length
    rw [Nat.zero_add]
  }
  rw [h1]
  ac_rfl
}

lemma num_Is_sDel_le (X : List B) (i : Nat) : num_Is (sDel X i) ≤ num_Is X := by {
  revert i
  induction X with
  | nil => intro i; exact Nat.le_refl _
  | cons x X' IHX =>
    intro i
    cases X' with
    | nil => exact Nat.zero_le _
    | cons x' X'' =>
      cases i with
      | zero =>
        change num_Is (x' :: X'') ≤ num_Is (x :: x' :: X'')
        cases x with
        | O => exact Nat.le_refl _
        | I => exact Nat.le_add_right _ _
      | succ i =>
        change num_Is (x :: sDel (x' :: X'') i) ≤ num_Is (x :: x' :: X'')
        cases x with
        | O => exact IHX i
        | I =>
          apply Nat.succ_le_succ
          exact IHX i
}

lemma num_Is_le_sIns (X : List B) (i : Nat) (b : B) : num_Is X ≤ num_Is (sIns X i b) := by {
  revert i
  induction X with
  | nil =>
    intro i
    exact Nat.zero_le _
  | cons x X' IHX =>
    intro i
    cases i with
    | zero =>
      change num_Is (x :: X') ≤ num_Is (b :: x :: X')
      cases b with
      | O => exact Nat.le_refl _
      | I => exact Nat.le_add_right _ _
    | succ i =>
      change num_Is (x :: X') ≤ num_Is (x :: sIns X' i b)
      cases x with
      | O => exact IHX i
      | I =>
        apply Nat.succ_le_succ
        exact IHX i
}

lemma num_Is_sIns_zero (X : List B) (i : Nat) : num_Is (sIns X i B.O) = num_Is X := by {
  revert i
  induction X with
  | nil => intro i; rfl
  | cons x X' IHX =>
    intro i
    cases i with
    | zero => rfl
    | succ i =>
      change num_Is (x :: sIns X' i B.O) = num_Is (x :: X')
      cases x with
      | O => exact IHX i
      | I =>
        change num_Is (sIns X' i B.O) + 1 = num_Is X' + 1
        rw [IHX i]
}

lemma num_Is_sIns_one (X : List B) (i : Nat) : num_Is (sIns X i B.I) = num_Is X + 1 := by {
  revert i
  induction X with
  | nil => intro i; rfl
  | cons x X' IHX =>
    intro i
    cases i with
    | zero => rfl
    | succ i =>
      change num_Is (x :: sIns X' i B.I) = num_Is (x :: X') + 1
      cases x with
      | O => exact IHX i
      | I =>
        change num_Is (sIns X' i B.I) + 1 = (num_Is X' + 1) + 1
        rw [IHX i]
}

lemma moment_sDel_le :
  moment (sDel X i) ≤ moment X := by {
  revert i
  induction X with
  | nil =>
    intro i
    exact Nat.zero_le _
  | cons x X' IHX =>
    intro i
    cases X' with
    | nil => exact Nat.zero_le _
    | cons x' X'' =>
      cases i with
      | zero =>
        change moment (x' :: X'') ≤ moment (x :: x' :: X'')
        exact moment_le_cons x (x' :: X'')
      | succ i =>
        change moment (x :: sDel (x' :: X'') i) ≤ moment (x :: x' :: X'')
        rw [moment_cons, moment_cons]
        apply Nat.add_le_add (IHX i)
        cases x with
        | O =>
          change num_Is (sDel (x' :: X'') i) ≤ num_Is (x' :: X'')
          exact num_Is_sDel_le (x' :: X'') i
        | I =>
          change num_Is (sDel (x' :: X'') i) + 1 ≤ num_Is (x' :: X'') + 1
          apply Nat.succ_le_succ
          exact num_Is_sDel_le (x' :: X'') i
}

lemma moment_le_sIns :
  (moment X) ≤ (moment ((sIns X i b))) := by {
  revert i
  induction X with
  | nil =>
    intro i
    change 0 ≤ moment [b]
    exact Nat.zero_le _
  | cons x X' IHX =>
    intro i
    cases i with
    | zero =>
      change moment (x :: X') ≤ moment (b :: x :: X')
      exact moment_le_cons b (x :: X')
    | succ i =>
      change moment (x :: X') ≤ moment (x :: sIns X' i b)
      rw [moment_cons, moment_cons]
      apply Nat.add_le_add (IHX i)
      exact num_Is_le_sIns (x :: X') (i + 1) b
}

lemma moment_sIns_zero :
  (moment ((sIns X i B.O))) = (moment X) + num_RIs X i := by {
  revert i
  induction X with
  | nil =>
    intro i
    change moment [B.O] = moment [] + num_RIs [] i
    rw [moment_zero, moment_nil, num_RIs]
    change 0 = 0 + num_Is (List.drop i [])
    have h_drop : List.drop i ([] : List B) = [] := by cases i <;> rfl
    rw [h_drop, num_Is]
  | cons x X' IHX =>
    intro i
    cases i with
    | zero =>
      change moment (B.O :: x :: X') = moment (x :: X') + num_RIs (x :: X') 0
      rw [moment_cons, moment_cons, num_RIs, List.drop_zero]
      rfl
    | succ i =>
      change moment (x :: sIns X' i B.O) = moment (x :: X') + num_Is (List.drop (i + 1) (x :: X'))
      have h_drop : List.drop (i + 1) (x :: X') = List.drop i X' := rfl
      rw [h_drop, moment_cons, moment_cons, IHX i]
      cases x with
      | O =>
        have h_num_Is : num_Is (B.O :: sIns X' i B.O) = num_Is (sIns X' i B.O) := rfl
        have h_num_Is_O : num_Is (B.O :: X') = num_Is X' := rfl
        rw [h_num_Is, num_Is_sIns_zero X' i, h_num_Is_O, num_RIs]
        ac_rfl
      | I =>
        have h_num_Is : num_Is (B.I :: sIns X' i B.O) = num_Is (sIns X' i B.O) + 1 := rfl
        have h_num_Is_I : num_Is (B.I :: X') = num_Is X' + 1 := rfl
        rw [h_num_Is, num_Is_sIns_zero X' i, h_num_Is_I, num_RIs]
        ac_rfl
}

lemma moment_sIns_one :
  (moment ((sIns X i B.I))) = (moment X) + num_LOs X i + num_Is X + 1 := by {
  revert i
  induction X with
  | nil =>
    intro i
    change moment [B.I] = moment [] + num_LOs [] i + num_Is [] + 1
    rw [moment_one, moment_nil, num_Is]
    cases i <;> rfl
  | cons x X' IHX =>
    intro i
    cases i with
    | zero =>
      change moment (B.I :: x :: X') = moment (x :: X') + num_LOs (x :: X') 0 + num_Is (x :: X') + 1
      rw [moment_cons, moment_cons, num_LOs, List.take_zero, num_Os]
      ac_rfl
    | succ i =>
      change moment (x :: sIns X' i B.I) = moment (x :: X') + num_LOs (x :: X') (i + 1) + num_Is (x :: X') + 1
      rw [moment_cons, moment_cons, IHX i]
      cases x with
      | O =>
        have h_num_Is : num_Is (B.O :: sIns X' i B.I) = num_Is (sIns X' i B.I) := rfl
        have h_num_LOs : num_LOs (B.O :: X') (i + 1) = num_LOs X' i + 1 := rfl
        have h_num_Is_O : num_Is (B.O :: X') = num_Is X' := rfl
        rw [h_num_Is, num_Is_sIns_one X' i, h_num_LOs, h_num_Is_O]
        change moment X' + num_LOs X' i + num_Is X' + 1 + (num_Is X' + 1) = (moment X' + num_Is X') + (num_LOs X' i + 1) + num_Is X' + 1
        ac_rfl
      | I =>
        have h_num_Is : num_Is (B.I :: sIns X' i B.I) = num_Is (sIns X' i B.I) + 1 := rfl
        have h_num_LOs : num_LOs (B.I :: X') (i + 1) = num_LOs X' i := rfl
        have h_num_Is_I : num_Is (B.I :: X') = num_Is X' + 1 := rfl
        rw [h_num_Is, num_Is_sIns_one X' i, h_num_LOs, h_num_Is_I]
        change moment X' + num_LOs X' i + num_Is X' + 1 + (num_Is X' + 1 + 1) = (moment X' + (num_Is X' + 1)) + num_LOs X' i + (num_Is X' + 1) + 1
        ac_rfl
}

lemma moment_sub_sDel_of_sDel_O
  (H : sIns (sDel X i) i B.O = X) :
  moment X - moment (sDel X i) = num_RIs (sDel X i) i := by {
  have h : moment (sIns (sDel X i) i B.O) = moment (sDel X i) + num_RIs (sDel X i) i := moment_sIns_zero (sDel X i) i
  rw [H] at h
  rw [h]
  exact Nat.add_sub_cancel_left (moment (sDel X i)) (num_RIs (sDel X i) i)
}

lemma moment_sub_sDel_of_sDel_I
  (H : sIns (sDel X i) i B.I = X) :
  moment X - moment (sDel X i) = num_LOs (sDel X i) i + num_Is (sDel X i) + 1 := by {
  have h : moment (sIns (sDel X i) i B.I) = moment (sDel X i) + num_LOs (sDel X i) i + num_Is (sDel X i) + 1 := moment_sIns_one (sDel X i) i
  have h_assoc : moment (sDel X i) + num_LOs (sDel X i) i + num_Is (sDel X i) + 1 = moment (sDel X i) + (num_LOs (sDel X i) i + num_Is (sDel X i) + 1) := by ac_rfl
  rw [h_assoc] at h
  rw [H] at h
  rw [h]
  exact Nat.add_sub_cancel_left (moment (sDel X i)) (num_LOs (sDel X i) i + num_Is (sDel X i) + 1)
}


lemma sIns_sDel_eq_or (X : List B) (i : Nat) (H : 1 ≤ length X) :
  sIns (sDel X i) i B.O = X ∨ sIns (sDel X i) i B.I = X := by {
  have ⟨b, hb⟩ := sIns_sDel_id X i H
  cases b with
  | O => exact Or.inl hb
  | I => exact Or.inr hb
}

lemma num_RIs_le_num_Is (X : List B) (i : Nat) : num_RIs X i ≤ num_Is X := by {
  rw [num_RIs]
  have h : X = X.take i ++ X.drop i := (List.take_append_drop i X).symm
  conv => rhs; rw [h]
  rw [num_Is_append]
  exact Nat.le_add_left _ _
}

lemma num_LOs_le_num_Os (X : List B) (i : Nat) : num_LOs X i ≤ num_Os X := by {
  rw [num_LOs]
  have h : X = X.take i ++ X.drop i := (List.take_append_drop i X).symm
  conv => rhs; rw [h]
  rw [num_Os_append]
  exact Nat.le_add_right _ _
}

lemma num_Is_le_length (X : List B) : num_Is X ≤ length X := by {
  have h := num_Os_add_num_Is_eq_length X
  rw [← h]
  exact Nat.le_add_left _ _
}

lemma sDel_length_le (X : List B) (i : Nat) : length (sDel X i) ≤ length X := by {
  rw [length_sDel]
  exact Nat.sub_le _ _
}

lemma moment_sub_sDel_le :
  moment X - moment (sDel X i) ≤ length X := by {
  cases X with
  | nil => exact Nat.zero_le _
  | cons x X' =>
    have H1 : 1 ≤ length (x :: X') := Nat.le_add_left 1 _
    have ⟨b, hb⟩ := sIns_sDel_id (x :: X') i H1
    cases b with
    | O =>
      have h2 : moment (x :: X') - moment (sDel (x :: X') i) = num_RIs (sDel (x :: X') i) i := moment_sub_sDel_of_sDel_O (x :: X') i hb
      rw [h2]
      apply Nat.le_trans (num_RIs_le_num_Is _ _)
      apply Nat.le_trans (num_Is_le_length _)
      rw [length_sDel]
      exact Nat.sub_le _ _
    | I =>
      have h2 : moment (x :: X') - moment (sDel (x :: X') i) = num_LOs (sDel (x :: X') i) i + num_Is (sDel (x :: X') i) + 1 := moment_sub_sDel_of_sDel_I (x :: X') i hb
      rw [h2]
      change _ ≤ length X' + 1
      apply Nat.succ_le_succ
      apply Nat.le_trans
      · apply Nat.add_le_add_right
        exact num_LOs_le_num_Os _ _
      · have h3 := num_Os_add_num_Is_eq_length (sDel (x :: X') i)
        rw [h3]
        rw [length_sDel]
        exact Nat.le_refl _
}

lemma sIns_fig_of_pos_of_moment
    (H1 : 1 ≤ length X)
    (H2 : (moment X) - (moment ((sDel X i))) ≤ num_Is ((sDel X i))) :
    sIns ((sDel X i)) i B.O = X := by {
  have H : sIns (sDel X i) i B.O = X ∨ sIns (sDel X i) i B.I = X := sIns_sDel_eq_or X i H1
  cases H with
  | inl Hl => exact Hl
  | inr Hr =>
    have h2 : moment X - moment (sDel X i) = num_LOs (sDel X i) i + num_Is (sDel X i) + 1 := moment_sub_sDel_of_sDel_I X i Hr
    rw [h2] at H2
    have h3 : num_Is (sDel X i) < num_LOs (sDel X i) i + num_Is (sDel X i) + 1 := by {
      have h4 : num_Is (sDel X i) < num_Is (sDel X i) + 1 := Nat.lt_succ_self _
      have h5 : num_Is (sDel X i) + 1 ≤ num_LOs (sDel X i) i + (num_Is (sDel X i) + 1) := Nat.le_add_left _ _
      have h_comm : num_LOs (sDel X i) i + num_Is (sDel X i) + 1 = num_LOs (sDel X i) i + (num_Is (sDel X i) + 1) := by ac_rfl
      rw [← h_comm] at h5
      exact Nat.lt_of_lt_of_le h4 h5
    }
    have h_contra := Nat.not_le_of_gt h3
    contradiction
}

lemma sIns_fig_of_neg_of_moment
    (H1 : 1 ≤ length X)
    (H2 : ¬ (moment X) - (moment ((sDel X i))) ≤ num_Is ((sDel X i))) :
    sIns ((sDel X i)) i B.I = X:= by {
  have H : sIns (sDel X i) i B.O = X ∨ sIns (sDel X i) i B.I = X := sIns_sDel_eq_or X i H1
  cases H with
  | inr Hr => exact Hr
  | inl Hl =>
    have h2 : moment X - moment (sDel X i) = num_RIs (sDel X i) i := moment_sub_sDel_of_sDel_O X i Hl
    rw [h2] at H2
    have h3 : num_RIs (sDel X i) i ≤ num_Is (sDel X i) := num_RIs_le_num_Is _ _
    contradiction
}

end List

namespace List.Vector
variable {n : Nat} (X : List.Vector B n) (c : List.Vector B n)

variable {n : Nat} (X : List.Vector B n)

def moment (X : List.Vector B n) : Nat := List.moment X.toList

def num_RIs {n : Nat} (X : List.Vector B n) (i : Nat) : Nat := List.num_RIs X.toList i
def num_LOs {n : Nat} (X : List.Vector B n) (i : Nat) : Nat := List.num_LOs X.toList i
lemma moment_nil : moment (⟨[], rfl⟩ : List.Vector B 0) = 0 := rfl


lemma moment_sDel_le :
  moment (sDel X i) ≤ moment X := by {
  exact List.moment_sDel_le X.toList i
}

lemma moment_le_sIns {b : B} :
  (moment X) ≤ (moment ((sIns X i b))) := by {
  exact List.moment_le_sIns X.toList i
}

def push {n : Nat} (v : List.Vector B n) (b : B) : List.Vector B (n + 1) :=
  ⟨v.toList ++ [b], by simp⟩

lemma moment_push_O {n : Nat} (v : List.Vector B n) :
  moment (push v B.O) = moment v := by {
  unfold push moment
  dsimp
  apply moment_append_O
}

lemma moment_push_I {n : Nat} (v : List.Vector B n) :
  moment (push v B.I) = moment v + n + 1 := by {
  unfold push moment
  dsimp
  have h := moment_append_I v.toList
  have h_len : v.toList.length = n := v.property
  rw [h_len] at h
  exact h
}

lemma moment_sIns_zero :
  (moment ((sIns X i B.O))) = (moment X) + num_RIs X i := by {
  exact List.moment_sIns_zero X.toList i
}

lemma moment_sIns_one :
  (moment ((sIns X i B.I))) = (moment X) + num_LOs X i + wt X + 1 := by {
  exact List.moment_sIns_one X.toList i
}

lemma moment_sub_sDel_of_sDel_O
  (X : List.Vector B (n + 1))
  (H : sIns ((sDel X i)) i B.O = X) :
  (moment X) - (moment ((sDel X i))) = num_RIs ((sDel X i)) i := by {
  unfold moment
  apply List.moment_sub_sDel_of_sDel_O
  unfold sIns at H
  apply Subtype.mk.inj H
}

lemma moment_sub_sDel_of_sDel_I
  (X : List.Vector B (n + 1))
  (H : sIns ((sDel X i)) i B.I = X) :
  (moment X) - (moment ((sDel X i))) = num_LOs ((sDel X i)) i + wt ((sDel X i)) + 1 := by {
  unfold moment
  apply List.moment_sub_sDel_of_sDel_I
  unfold sIns at H
  apply Subtype.mk.inj H
}


lemma moment_sub_sDel_le :
  (moment X) - (moment ((sDel X i))) ≤ n := by {
  have h := List.moment_sub_sDel_le X.val i
  have hlen : X.val.length = n := X.property
  rw [hlen] at h
  exact h
}

lemma sIns_fig_of_pos_of_moment
    (X : List.Vector B (n + 1))
    (H : (moment X) - (moment ((sDel X i))) ≤ wt ((sDel X i))) :
    sIns ((sDel X i)) i B.O = X := by {
  apply Subtype.ext
  apply List.sIns_fig_of_pos_of_moment
  · have hlen : 1 ≤ List.length X.val := by { rw [X.property]; apply Nat.succ_le_succ; apply Nat.zero_le }
    exact hlen
  · exact H
}

lemma sIns_fig_of_neg_of_moment
    (X : List.Vector B (n + 1))
    (H : ¬ (moment X) - (moment ((sDel X i))) ≤ wt ((sDel X i))) :
    sIns ((sDel X i)) i B.I = X := by {
  apply Subtype.ext
  apply List.sIns_fig_of_neg_of_moment
  · have hlen : 1 ≤ List.length X.val := by { rw [X.property]; apply Nat.succ_le_succ; apply Nat.zero_le }
    exact hlen
  · exact H
}

end List.Vector

def VTCode (n a : Nat) : Set (List.Vector B n) :=
  { X | List.Vector.moment X % (n + 1) = a % (n + 1) }

lemma mem_VTCode {n a : Nat} {X : List.Vector B n} :
  X ∈ VTCode n a ↔ List.Vector.moment X % (n + 1) = a % (n + 1) := Iff.rfl

instance decidable_pred_VTCode (n a : Nat) : DecidablePred (VTCode n a) :=
  fun X => inferInstanceAs (Decidable (List.Vector.moment X % (n + 1) = a % (n + 1)))


namespace List
def sub_mod (m a : Nat) (X : List B) : Nat :=
  if moment X < a then (a - moment X) % m
  else (m - (moment X - a) % m) % m

lemma sub_mod_zero (m : Nat) (X : List B) :
    sub_mod m 0 X = (m - (moment X) % m) % m := by {
  unfold sub_mod
  rw [if_neg]
  · rfl
  · exact Nat.not_lt_zero _
}

lemma sub_mod_mod_self (m : Nat) (X : List B) :
  sub_mod m m X = sub_mod m 0 X := by {
  rw [sub_mod, sub_mod_zero]
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

lemma sub_mod_nil (m : Nat) :
    sub_mod m a [] = a % m := by {
  cases a with
  | zero =>
    rw [sub_mod_zero]
    rw [List.moment_nil]
    rw [Nat.zero_mod, Nat.sub_zero, Nat.mod_self]
  | succ a =>
    unfold sub_mod
    rw [List.moment_nil]
    rw [if_pos (Nat.zero_lt_succ _)]
    rw [Nat.sub_zero]
}

lemma sub_mod_add (m : Nat) (X : List B) :
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
}

lemma sub_mod_sub (m : Nat) (X : List B) (H : m  ≤ a) :
  sub_mod m (a - m) X = sub_mod m a X := by {
  rw [← sub_mod_add m X]
  rw [Nat.sub_add_cancel H]
}

lemma sub_mod_mod (m : Nat) (X : List B) :
  sub_mod m (a % m) X = sub_mod m a X := by {
  cases m with
  | zero =>
    rw [Nat.mod_zero]
  | succ m =>
    induction a using Nat.case_strong_induction_on with
    | hz =>
      rw [Nat.zero_mod]
    | hi a IHa =>
      cases Decidable.em (a + 1 ≤ m + 1) with
      | inl hle =>
        cases Decidable.em (a + 1 = m + 1) with
        | inl heq =>
          rw [heq]
          rw [Nat.mod_self]
          rw [sub_mod_mod_self]
        | inr hneq =>
          have hlt_m : a + 1 < m + 1 := Nat.lt_of_le_of_ne hle hneq
          rw [Nat.mod_eq_of_lt hlt_m]
      | inr hnle =>
        -- rw mod_eq_sub_mod (le_of_not_ge hnle), rw IHa
        -- rw sub_mod_sub _ _ _ (le_of_not_ge hnle)
        -- rw succ_sub_succ, apply nat.sub_le
        sorry
}

lemma sub_mod_sDel
  {n a : Nat} {X : List B} (HX : length X = n)
  (H : (moment X) % (n + 1) = a % (n + 1)) (i : Nat) :
  sub_mod (n + 1) a ((sDel X i)) = (moment X) - (moment ((sDel X i))) := by {
  cases X with
  | nil =>
    rw [sDel_nil, sub_mod_nil, ← H]
    rw [moment_nil, Nat.zero_mod]
  | cons x X' =>
    rw [← sub_mod_mod, ← H, sub_mod_mod]
    unfold sub_mod
    cases Decidable.em (moment (sDel (x :: X') i) = moment (x :: X')) with
    | inl heq =>
      rw [if_neg]
      · rw [heq, Nat.sub_self, Nat.zero_mod, Nat.sub_zero, Nat.mod_self]
      · apply Nat.not_lt_of_ge
        rw [heq]
    | inr hneq =>
      have hlt : moment (sDel (x :: X') i) < moment (x :: X') := Nat.lt_of_le_of_ne (moment_sDel_le (x :: X') i) hneq
      rw [if_pos hlt]
      have hlt2 : moment (x :: X') - moment (sDel (x :: X') i) < n + 1 := Nat.lt_of_le_of_lt (moment_sub_sDel_le (x :: X') i) (by {
        rw [HX]
        exact Nat.lt_succ_of_le (Nat.le_refl _)
      })
      rw [Nat.mod_eq_of_lt hlt2]
}

lemma sub_mod_sDel_of_pos
    {n a : Nat} {X : List B} (HX : 1 ≤ length X)
    (HXn : length X = n) (HXa : (moment X) % (n + 1) = a % (n + 1))
    (i : Nat) (H : sub_mod (n + 1) a ((sDel X i)) ≤ num_Is ((sDel X i))) :
    sub_mod (n + 1) a ((sDel X i)) = num_RIs ((sDel X i)) i := by {
  rw [sub_mod_sDel HXn HXa]
  apply moment_sub_sDel_of_sDel_O
  rw [sIns_fig_of_pos_of_moment X i HX]
  · rw [← sub_mod_sDel HXn HXa]
    exact H
}

lemma sub_mod_sDel_of_neg
    {n a : Nat} {X : List B} (HX : 1 ≤ length X)
    (HXn : length X = n) (HXa : (moment X) % (n + 1) = a % (n + 1))
    (i : Nat) (H : ¬ sub_mod (n + 1) a ((sDel X i)) ≤ num_Is ((sDel X i))) :
    sub_mod (n + 1) a ((sDel X i)) = num_LOs ((sDel X i)) i + num_Is ((sDel X i)) + 1 := by {
  rw [sub_mod_sDel HXn HXa]
  apply moment_sub_sDel_of_sDel_I
  rw [sIns_fig_of_neg_of_moment X i HX]
  · rw [← sub_mod_sDel HXn HXa]
    exact H
}

lemma sIns_fig_of_pos
    {n a : Nat} {X : List B} (HX : 1 ≤ length X)
    (HXn : length X = n) (HXa : (moment X) % (n + 1) = a % (n + 1))
    (i : Nat) (H : sub_mod (n + 1) a ((sDel X i)) ≤ num_Is ((sDel X i)))   :
  sIns ((sDel X i)) i B.O = X := by {
  have H2 := sIns_sDel_id X i HX
  rcases H2 with ⟨b, hb⟩
  cases b with
  | O => exact hb
  | I =>
    -- apply absurd H, apply not_le_of_gt,
    -- rw sub_mod_sDel HXn HXa,
    -- rw moment_sub_sDel_of_sDel_I _ _ hb,
    -- apply lt_succ_of_le, apply nat.le_add_left
    sorry
}

lemma sIns_fig_of_neg
    {n a : Nat} {X : List B} (HX : 1 ≤ length X)
    (HXn : length X = n) (HXa : (moment X) % (n + 1) = a % (n + 1))
    (i : Nat) (H : ¬ sub_mod (n + 1) a ((sDel X i)) ≤ num_Is ((sDel X i)))   :
  sIns ((sDel X i)) i B.I = X := by {
  have H2 := sIns_sDel_id X i HX
  rcases H2 with ⟨b, hb⟩
  cases b with
  | O =>
    -- have h : sub_mod (n + 1) a (sDel X i) ≤ num_Is (sDel X i),
    --  {rw sub_mod_sDel HXn HXa,
    --   rw moment_sub_sDel_of_sDel_O _ _ hb,
    --   apply num_RIs_le_num_Is},
    -- contradiction
    sorry
  | I => exact hb
}

def min_num_LOs : List B → Nat → Nat
| [], _ => 0
| x::X, 0 => 0
| B.O::X, n + 1 => min_num_LOs X n + 1
| B.I::X, n + 1 => min_num_LOs X (n + 1) + 1

lemma min_num_LOs_zero (X : List B) :
  min_num_LOs X 0 = 0 := by {
  cases X with
  | nil => rfl
  | cons x X' =>
    cases x with
    | O => rfl
    | I => rfl
}

lemma min_num_LOs_of_num_Os (X : List B) (i : Nat)
  (H : num_Os X + 1 ≤ i) :
  min_num_LOs X i = length X := by {
  revert i
  induction X with
  | nil =>
    intro i H
    rfl
  | cons x X' IHX =>
    intro i H
    cases i with
    | zero =>
      exact False.elim (Nat.not_succ_le_zero (num_Os (x :: X')) H)
    | succ i =>
      cases x with
      | O =>
        unfold min_num_LOs
        unfold length
        rw [IHX]
        exact Nat.le_of_succ_le_succ H
      | I =>
        unfold min_num_LOs
        unfold length
        rw [IHX]
        exact H
}

lemma num_LOs_min_num_LOs (X : List B) (i : Nat)
  (H : i ≤ num_Os X) :
  num_LOs X (min_num_LOs X i) = i := by {
  revert i
  induction X with
  | nil =>
    intro i H
    cases i with
    | zero => rfl
    | succ i => exact False.elim (Nat.not_succ_le_zero i H)
  | cons x X' IHX =>
    intro i H
    cases i with
    | zero =>
      rw [min_num_LOs_zero]
      rfl
    | succ i =>
      cases x with
      | O =>
        unfold min_num_LOs
        change num_LOs X' (min_num_LOs X' i) + 1 = i + 1
        rw [IHX _ (Nat.le_of_succ_le_succ H)]
      | I =>
        unfold min_num_LOs
        change num_LOs X' (min_num_LOs X' (i + 1)) = i + 1
        rw [IHX _ H]
}

lemma num_Is_le_cons (x : B) (X : List B) : num_Is X ≤ num_Is (x::X) := by {
  cases x with
  | O => exact Nat.le_refl _
  | I => exact Nat.le_succ _
}

lemma num_Is_cons_le (x : B) (X : List B) : num_Is (x::X) ≤ num_Is X + 1 := by {
  cases x with
  | O => exact Nat.le_succ _
  | I => exact Nat.le_refl _
}

def max_num_RIs : List B → Nat → Nat
| [], _ => 0
| (x::X), n => if num_Is X + 1 ≤ n
               then max_num_RIs X n else max_num_RIs X n + 1

lemma max_num_RIs_zero (X : List B) :
  max_num_RIs X 0 = length X := by {
  induction X with
  | nil => rfl
  | cons x X' IHX =>
    unfold max_num_RIs
    cases Decidable.em (num_Is X' + 1 ≤ 0) with
    | inl h_le =>
      exact False.elim (Nat.not_succ_le_zero (num_Is X') h_le)
    | inr h_nle =>
      rw [if_neg h_nle]
      unfold length
      rw [IHX]
}

lemma max_num_RIs_of_num_Is (X : List B) (i : Nat)
  (H : num_Is X + 1 ≤ i) :
  max_num_RIs X i = 0 := by {
  revert i
  induction X with
  | nil =>
    intro i H
    rfl
  | cons x X' IHX =>
    intro i H
    cases i with
    | zero =>
      exact False.elim (Nat.not_succ_le_zero (num_Is (x::X')) H)
    | succ i =>
      unfold max_num_RIs
      have h : num_Is X' + 1 ≤ Nat.succ i := by {
        apply Nat.le_trans (Nat.add_le_add_right (num_Is_le_cons x X') 1) H
      }
      rw [if_pos h]
      rw [IHX (Nat.succ i) h]
}

lemma num_RIs_max_num_RIs (X : List B) (i : Nat)
  (H : i ≤ num_Is X) :
  num_RIs X (max_num_RIs X i) = i := by {
  revert i
  induction X with
  | nil =>
    intro i H
    cases i with
    | zero => rfl
    | succ i => exact False.elim (Nat.not_succ_le_zero i H)
  | cons x X' IHX =>
    intro i H
    unfold max_num_RIs
    cases Decidable.em (num_Is X' + 1 ≤ i) with
    | inl hle =>
      rw [if_pos hle]
      have h : max_num_RIs X' i = 0 := by {
        apply max_num_RIs_of_num_Is _ _ hle
      }
      rw [h]
      unfold List.num_RIs
      apply Nat.le_antisymm (Nat.le_trans (num_Is_cons_le x X') hle) H
    | inr hnle =>
      rw [if_neg hnle]
      have hlt : i < num_Is X' + 1 := Nat.lt_of_not_ge hnle
      have hle2 : i ≤ num_Is X' := Nat.le_of_lt_succ hlt
      unfold List.num_RIs
      change num_RIs X' (max_num_RIs X' i) = i
      rw [IHX _ hle2]
}

lemma sIns_zero_of_num_RIs (X : List B) (i j : Nat) (H : num_RIs X i = num_RIs X j) :
  sIns X i B.O = sIns X j B.O := sorry

lemma sIns_one_of_num_LOs (X : List B) (i j : Nat) (H : num_LOs X i = num_LOs X j) :
  sIns X i B.I = sIns X j B.I := sorry

def decoding_alg (n a : Nat) (X : List B) : List B :=
  if length X = n then X
  else if sub_mod (n + 1) a X ≤ num_Is X
      then sIns X (max_num_RIs X (sub_mod (n + 1) a X)) B.O
      else sIns X (min_num_LOs X ((sub_mod (n + 1) a X) - num_Is X - 1)) B.I

lemma length_decoding_alg
  (n a : Nat) (X : List B) (H : length X = n - 1) :
  length (decoding_alg n a X) = n := by {
  unfold decoding_alg
  cases Decidable.em (n ≤ 0) with
  | inl hle_len =>
    have h : length X = n := by {
      rw [H, Nat.eq_zero_of_le_zero hle_len]
    }
    rw [if_pos h]
    exact h
  | inr hnle_len =>
    have h : length X ≠ n := by {
      rw [H]
      apply Nat.ne_of_lt
      apply Nat.sub_lt
      · exact Nat.lt_of_not_ge hnle_len
      · exact Nat.zero_lt_one
    }
    rw [if_neg h]
    cases Decidable.em (sub_mod (n + 1) a X ≤ num_Is X) with
    | inl hle =>
      rw [if_pos hle]
      rw [List.length_sIns]
      rw [H]
      rw [Nat.sub_add_cancel]
      apply Nat.succ_le_of_lt
      exact Nat.lt_of_not_ge hnle_len
    | inr hnle =>
      rw [if_neg hnle]
      rw [List.length_sIns]
      rw [H]
      rw [Nat.sub_add_cancel]
      apply Nat.succ_le_of_lt
      exact Nat.lt_of_not_ge hnle_len
}

lemma sDelErr_correctable_of_pos
    {n a : Nat} {X : List B} (HX : 1 ≤ length X)
    (HXn : length X = n) (HXa : (moment X) % (n + 1) = a % (n + 1))
    (i : Nat) (Hr : sub_mod (n + 1) a (sDel X i) ≤ num_Is (sDel X i)) :
    decoding_alg n a (sDel X i) = X := by {
  unfold decoding_alg
  rw [if_neg]
  · rw [if_pos Hr]
    rw [← sIns_fig_of_pos HX HXn HXa _ Hr]
    rw [sDel_sIns_id]
    apply sIns_zero_of_num_RIs
    rw [num_RIs_max_num_RIs _ _ Hr]
    apply sub_mod_sDel_of_pos HX HXn HXa _ Hr
  · apply Nat.ne_of_lt
    rw [length_sDel]
    rw [← HXn]
    apply Nat.sub_lt_self
    · exact Nat.zero_lt_one
    · exact HX
}

lemma sDelErr_correctable_of_neg
    {n a : Nat} {X : List B} (HX : 1 ≤ length X)
    (HXn : length X = n) (HXa : (moment X) % (n + 1) = a % (n + 1))
    (i : Nat) (Hr : ¬ sub_mod (n + 1) a (sDel X i) ≤ num_Is (sDel X i)) :
    decoding_alg n a (sDel X i) = X := by {
  unfold decoding_alg
  rw [if_neg]
  · rw [if_neg Hr]
    rw [← sIns_fig_of_neg HX HXn HXa _ Hr]
    rw [sDel_sIns_id]
    apply sIns_one_of_num_LOs
    rw [num_LOs_min_num_LOs]
    · rw [sub_mod_sDel_of_neg HX HXn HXa _ Hr]
      rw [Nat.add_right_comm]
      rw [Nat.add_sub_cancel]
      rw [Nat.add_sub_cancel]
    · rw [sub_mod_sDel_of_neg HX HXn HXa _ Hr]
      rw [Nat.add_right_comm]
      rw [Nat.add_sub_cancel]
      rw [Nat.add_sub_cancel]
      apply num_LOs_le_num_Os
  · apply Nat.ne_of_lt
    rw [length_sDel]
    rw [← HXn]
    apply Nat.sub_lt_self
    · exact Nat.zero_lt_one
    · exact HX
}

lemma sDelErr_correctable
  {n a : Nat} {X : List B}
  (HXn : length X = n) (HXa : (moment X) % (n + 1) = a % (n + 1)) (i : Nat) :
  decoding_alg n a (sDel X i) = X := by {
  cases n with
  | zero =>
    unfold decoding_alg
    rw [if_pos]
    · rw [List.eq_nil_of_length_eq_zero HXn]
      rw [sDel_nil]
    · rw [List.eq_nil_of_length_eq_zero HXn]
      rw [sDel_nil]
      rfl
  | succ m =>
    cases Decidable.em (sub_mod (m + 2) a (sDel X i) ≤ num_Is (sDel X i)) with
    | inl hle =>
      apply sDelErr_correctable_of_pos _ HXn HXa _ hle
      rw [HXn]
      apply Nat.succ_le_succ
      exact Nat.zero_le _
    | inr hnle =>
      apply sDelErr_correctable_of_neg _ HXn HXa _ hnle
      rw [HXn]
      apply Nat.succ_le_succ
      exact Nat.zero_le _
}

end List
namespace List.Vector
variable {n : Nat} (X : List.Vector B n) (c : List.Vector B n)

def sub_mod (m a : Nat) (X : List.Vector B n) : Nat := List.sub_mod m a X.toList

lemma sub_mod_zero (m : Nat) :
    sub_mod m 0 X = (m - (moment X) % m) % m := by {
  unfold sub_mod moment
  apply List.sub_mod_zero
}

lemma sub_mod_mod_self (m : Nat) :
  sub_mod m m X = sub_mod m 0 X := by {
  unfold sub_mod
  apply List.sub_mod_mod_self
}

lemma sub_mod_nil (m : Nat) :
    sub_mod m a List.Vector.nil = a % m := by {
  unfold sub_mod
  apply List.sub_mod_nil
}

lemma sub_mod_add (m : Nat) :
  sub_mod m (a + m) X = sub_mod m a X := by {
  unfold sub_mod
  apply List.sub_mod_add
}

lemma sub_mod_sub (m : Nat) (H : m ≤ a) :
  sub_mod m (a - m) X = sub_mod m a X := by {
  unfold sub_mod
  apply List.sub_mod_sub
  exact H
}

lemma sub_mod_mod (m : Nat) :
  sub_mod m (a % m) X = sub_mod m a X := by {
  unfold sub_mod
  apply List.sub_mod_mod
}

lemma sub_mod_sDel
  {n a : Nat} {X : List.Vector B n} (H : X ∈ VTCode n a) (i : Nat) :
  sub_mod (n + 1) a ((sDel X i)) = (moment X) - (moment ((sDel X i))) := by {
  unfold sub_mod moment
  apply List.sub_mod_sDel
  · rw [X.property]
  · rw [mem_VTCode] at H
    apply H
}

lemma sub_mod_sDel_of_pos
  {n a : Nat} {X : List.Vector B (n + 1)} (HX : X ∈ VTCode (n + 1) a)
  (i : Nat) (H : sub_mod (n + 2) a ((sDel X i)) ≤ wt ((sDel X i))) :
  sub_mod (n + 2) a ((sDel X i)) = num_RIs ((sDel X i)) i := by {
  unfold sub_mod wt
  apply List.sub_mod_sDel_of_pos
  · rw [X.property]; apply Nat.succ_le_succ; apply Nat.zero_le
  · rw [X.property]
  · rw [mem_VTCode] at HX
    apply HX
  · apply H
}

lemma sub_mod_sDel_of_neg
  {n a : Nat} {X : List.Vector B (n + 1)} (HX : X ∈ VTCode (n + 1) a)
  (i : Nat) (H : ¬ sub_mod (n + 2) a ((sDel X i)) ≤ wt ((sDel X i))) :
  sub_mod (n + 2) a ((sDel X i)) = num_LOs ((sDel X i)) i + wt ((sDel X i)) + 1 := by {
  unfold sub_mod wt
  apply List.sub_mod_sDel_of_neg
  · rw [X.property]; apply Nat.succ_le_succ; apply Nat.zero_le
  · rw [X.property]
  · rw [mem_VTCode] at HX
    apply HX
  · apply H
}

lemma sIns_fig_of_pos
  {n a : Nat} {c : List.Vector B (n + 1)} (Hc : c ∈ VTCode (n + 1) a)
  (i : Nat) (H : sub_mod (n + 2) a ((sDel c i)) ≤ wt ((sDel c i)))  :
  sIns ((sDel c i)) i B.O = c := by {
  sorry
}

lemma sIns_fig_of_neg
  {n a : Nat} {c : List.Vector B (n + 1)} (Hc : c ∈ VTCode (n + 1) a)
  (i : Nat) (H : ¬ sub_mod (n + 2) a ((sDel c i)) ≤ wt ((sDel c i)))  :
  sIns ((sDel c i)) i B.I = c := by {
  sorry
}

def min_num_LOs {n : Nat} (X : List.Vector B n) (i : Nat) : Nat := List.min_num_LOs X.val i

lemma min_num_LOs_zero :
  min_num_LOs X 0 = 0 := by {
  unfold min_num_LOs
  apply List.min_num_LOs_zero
}

lemma num_LOs_min_num_LOs (i : Nat) (H : i ≤ n - wt X) :
  num_LOs X (min_num_LOs X i) = i := by {
  unfold min_num_LOs
  apply List.num_LOs_min_num_LOs
  have hlen : X.val.length = n := X.property
  rw [hlen] at H
  exact H
}

def max_num_RIs {n : Nat} (X : List.Vector B n) (i : Nat) : Nat := List.max_num_RIs X.val i

lemma max_num_RIs_zero :
  max_num_RIs X 0 = n := by {
  unfold max_num_RIs
  have h := List.max_num_RIs_zero X.val
  have hlen : X.val.length = n := X.property
  rw [hlen] at h
  exact h
}

lemma max_num_RIs_of_num_Is (i : Nat) (H : wt X + 1 ≤ i) :
  max_num_RIs X i = 0 := by {
  unfold max_num_RIs wt at *
  apply List.max_num_RIs_of_num_Is
  exact H
}

lemma num_RIs_max_num_RIs (i : Nat) (H : i ≤ wt X) :
  num_RIs X (max_num_RIs X i) = i := by {
  unfold num_RIs max_num_RIs wt at *
  apply List.num_RIs_max_num_RIs
  exact H
}

def decoding_alg (n a : Nat) (X : List.Vector B (n - 1)) : List.Vector B n :=
  ⟨List.decoding_alg n a X.val, List.length_decoding_alg n a X.val X.property⟩

lemma decoding_alg_to_list (n a : Nat) (X : List.Vector B (n - 1)) :
  (decoding_alg n a X).toList = _root_.List.decoding_alg n a X.toList := rfl

lemma sDelErr_correctable_of_nil
    {a : Nat} {X : List.Vector B 0} (H : X ∈ VTCode 0 a) (i : Nat) :
    decoding_alg 0 a ((sDel X i)) = X := by {
  apply Subtype.ext
  rw [decoding_alg_to_list]
  unfold List.decoding_alg
  have hlen : List.length ((sDel X i)).val = 0 := by {
    rw [List.length_sDel]
    rw [X.property]
  }
  rw [if_pos hlen]
  have h_val_nil : X.val = [] := by {
    have h : List.length X.val = 0 := X.property
    cases X.val with
    | nil => rfl
    | cons head tail => contradiction
  }
  rw [h_val_nil]
  rfl
}

lemma sDelErr_correctable_of_pos
    {n a : Nat} {X : List.Vector B (n + 1)} (HX : X ∈ VTCode (n + 1) a)
    (i : Nat) (Hr : sub_mod (n + 2) a ((sDel X i)) ≤ wt ((sDel X i))) :
    decoding_alg (n + 1) a ((sDel X i)) = X := by {
  apply Subtype.ext
  rw [decoding_alg_to_list]
  apply List.sDelErr_correctable_of_pos
  · rw [X.property]; apply Nat.succ_le_succ; apply Nat.zero_le
  · rw [X.property]
  · rw [mem_VTCode] at HX; apply HX
  · apply Hr
}

lemma sDelErr_correctable_of_neg
    {n a : Nat} {X : List.Vector B (n + 1)} (HX : X ∈ VTCode (n + 1) a)
    (i : Nat) (Hr : ¬ sub_mod (n + 2) a ((sDel X i)) ≤ wt ((sDel X i))) :
    decoding_alg (n + 1) a ((sDel X i)) = X := by {
  apply Subtype.ext
  rw [decoding_alg_to_list]
  apply List.sDelErr_correctable_of_neg
  · rw [X.property]; apply Nat.succ_le_succ; apply Nat.zero_le
  · rw [X.property]
  · rw [mem_VTCode] at HX; apply HX
  · apply Hr
}

theorem sDelErr_correctable
  {n a : Nat} {c : List.Vector B n}
  (Hc : c ∈ VTCode n a) (i : Nat) :
  decoding_alg n a ((sDel c i)) = c := by {
  cases n with
  | zero =>
    apply sDelErr_correctable_of_nil Hc
  | succ n =>
    cases Decidable.em (sub_mod (n + 2) a (sDel c i) ≤ wt (sDel c i)) with
    | inl h => apply sDelErr_correctable_of_pos Hc i h
    | inr h => apply sDelErr_correctable_of_neg Hc i h
}

end List.Vector
namespace Finset
def VTCode (n a : Nat) : Finset (List.Vector B n) := Finset.filter (fun (X : List.Vector B n) => X ∈ VTCode n a) Finset.univ

lemma mem_VTCode (n a : Nat) (x : List.Vector B n) :
  x ∈ Finset.VTCode n a ↔ x ∈ VTCode n a := by {
  unfold VTCode
  rw [Finset.mem_filter]
  simp
}

theorem DelCode_VTCode (n a : Nat) :
  is_DelCode (VTCode n a) := by {
  unfold is_DelCode
  intro X HX i
  apply Exists.intro (decoding_alg n a (sDel X i))
  apply And.intro
  · rw [mem_VTCode]
    exact HX
  · apply sDelErr_correctable HX i
}

end Finset
