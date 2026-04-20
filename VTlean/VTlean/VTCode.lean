import VTlean.NumOsNumIs
import Mathlib

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

end List

namespace Vector
variable {n : Nat} (X : Vector B n)

def moment (X : Vector B n) : Nat := List.moment X.toList

lemma moment_nil : moment (⟨#[], rfl⟩ : Vector B 0) = 0 := rfl

end Vector

def VTCode (n a : Nat) : Set (Vector B n) :=
  { X | Vector.moment X % (n + 1) = a % (n + 1) }

lemma mem_VTCode {n a : Nat} {X : Vector B n} :
  X ∈ VTCode n a ↔ Vector.moment X % (n + 1) = a % (n + 1) := Iff.rfl

instance decidable_pred_VTCode (n a : Nat) : DecidablePred (VTCode n a) :=
  fun X => inferInstanceAs (Decidable (Vector.moment X % (n + 1) = a % (n + 1)))
