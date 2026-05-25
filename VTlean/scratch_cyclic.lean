import Mathlib
import VTlean.VTCode

open Nat Finset B List

lemma num_Is_append_O (X : List B) : num_Is (X ++ [O]) = num_Is X := by {
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · change num_Is (X' ++ [O]) = num_Is X'
      exact ih
    · change num_Is (X' ++ [O]) + 1 = num_Is X' + 1
      rw [ih]
}

lemma num_Is_append_I (X : List B) : num_Is (X ++ [I]) = num_Is X + 1 := by {
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · change num_Is (X' ++ [I]) = num_Is X' + 1
      exact ih
    · change num_Is (X' ++ [I]) + 1 = num_Is X' + 1 + 1
      rw [ih]
}

lemma moment_cyclicShift_list (X : List B) (b : B) (n : Nat) (h_len : X.length + 1 = n) :
  moment (b :: X) ≡ moment (X ++ [b]) + num_Is (X ++ [b]) [MOD n] := by {
  cases b
  · rw [moment_append_O, num_Is_append_O]
    have hc := moment_cons O X
    have h1 : num_Is (O :: X) = num_Is X := rfl
    rw [h1] at hc
    rw [hc]
    exact Nat.ModEq.refl _
  · rw [moment_append_I, num_Is_append_I]
    have hc := moment_cons I X
    have h1 : num_Is (I :: X) = num_Is X + 1 := rfl
    rw [h1] at hc
    have heq : moment X + X.length + 1 + (num_Is X + 1) = moment (I :: X) + n := by {
      rw [hc]
      omega
    }
    rw [heq]
    have heq2 : (moment (I :: X) + n) % n = moment (I :: X) % n := by {
      rw [Nat.add_mod_right]
    }
    exact heq2.symm
}
