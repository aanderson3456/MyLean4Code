import Mathlib

namespace Nat

lemma ne_of_lt {a b : Nat} (H : a < b) : a ≠ b :=
  fun h => le_lt_antisymm (le_of_eq h.symm) H |>.elim

lemma ne_of_gt {a b : Nat} (H : b < a) : a ≠ b :=
  fun h => le_lt_antisymm (le_of_eq h) H |>.elim

lemma sub_eq_self_iff {n m : Nat} :
  n - m = n ↔ n = 0 ∨ m = 0 := by
  cases n with
  | zero =>
    apply Iff.intro
    · intro; exact Or.inl rfl
    · intro; rw [Nat.zero_sub]
  | succ n =>
    cases m with
    | zero =>
      apply Iff.intro
      · intro; exact Or.inr rfl
      · intro; rw [Nat.sub_zero]
    | succ m =>
      apply Iff.intro
      · intro h
        apply False.elim
        apply ne_of_lt (a := Nat.succ n - Nat.succ m)
        · apply Nat.sub_lt_self
          · apply Nat.zero_lt_succ
          · apply Nat.zero_lt_succ
        · exact h
      · intro h
        cases h with
        | inl h => apply False.elim; apply ne_of_gt (Nat.zero_lt_succ _) h
        | inr h => apply False.elim; apply ne_of_gt (Nat.zero_lt_succ _) h
end Nat
