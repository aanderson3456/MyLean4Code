import Mathlib

inductive B : Type
| O : B
| I : B
deriving Repr, DecidableEq, Inhabited, Fintype

namespace B

@[simp] lemma card_B : Fintype.card B = 2 := rfl

def toNat : B → Nat
| O => 0
| I => 1

def flip : B → B
| O => I
| I => O

lemma eq_of_flip_eq (x y : B) (H : flip x = flip y) : x = y := by
  cases x <;> cases y <;> first | rfl | contradiction

lemma flip_eq_flip_iff (x y : B) : flip x = flip y ↔ x = y :=
  ⟨eq_of_flip_eq x y, fun h => by rw [h]⟩

lemma flip_flip (x : B) : flip (flip x) = x := by
  cases x <;> rfl

lemma flip_eq_iff (x y : B) : flip x = y ↔ x = flip y := by
  constructor
  · intro h; rw [← h, flip_flip]
  · intro h; rw [h, flip_flip]

lemma flip_ne_self (x : B) : x ≠ flip x := by
  cases x <;> intro h <;> contradiction

lemma flip_of_ne {x x' : B} (Hne : x ≠ x') : flip x = x' := by
  cases x <;> cases x' <;> first | rfl | contradiction

namespace List
variable (X Y : List B) (i : Nat)

def toNat : List B → Nat
| [] => 0
| x :: X => 2 * toNat X + B.toNat x

def flip : List B → List B
| [] => []
| x :: X => B.flip x :: flip X

lemma flip_nil : flip ([] : List B) = [] := rfl

lemma eq_of_flip_eq_list {X Y : List B} (H : flip X = flip Y) : X = Y := by
  induction X generalizing Y with
  | nil =>
    cases Y with
    | nil => rfl
    | cons y Y' => contradiction
  | cons x X' ih =>
    cases Y with
    | nil => contradiction
    | cons y Y' =>
      injection H with h1 h2
      have hx_eq_y := B.eq_of_flip_eq x y h1
      have hX_eq_Y := ih h2
      rw [hx_eq_y, hX_eq_Y]

lemma flip_eq_flip_iff_list {X Y : List B} : flip X = flip Y ↔ X = Y :=
  ⟨eq_of_flip_eq_list, fun h => by rw [h]⟩

lemma flip_flip_list (X : List B) : flip (flip X) = X := by
  induction X with
  | nil => rfl
  | cons x X' ih =>
    change B.flip (B.flip x) :: flip (flip X') = x :: X'
    rw [B.flip_flip, ih]

lemma flip_eq_iff_list {X Y : List B} : flip X = Y ↔ X = flip Y := by
  constructor
  · intro h; rw [← h, flip_flip_list]
  · intro h; rw [h, flip_flip_list]

lemma length_flip (X : List B) : (flip X).length = X.length := by
  induction X with
  | nil => rfl
  | cons x X' ih =>
    change (B.flip x :: flip X').length = (x :: X').length
    simp [ih]

end List

namespace Vector
variable {n : Nat}

-- We wrap the definitions exactly as Vector.
def flip (X : Vector B n) : Vector B n :=
  ⟨(List.flip X.toList).toArray, by simp [List.length_flip]⟩

lemma flip_flip (X : Vector B n) : flip (flip X) = X := by
  rw [← Vector.toList_inj]
  change (List.flip ((List.flip X.toList).toArray.toList)).toArray.toList = X.toList
  simp [List.flip_flip_list]

end Vector

end B
