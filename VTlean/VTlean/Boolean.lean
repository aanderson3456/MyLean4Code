import Mathlib

/-!
# Mathgod.org Style Binary Strings

This file demonstrates an alternative formalization of binary strings
and 1-deletions using standard Mathlib `List Bool` and `take`/`drop`,
as presented by mathgod.org.

This is strictly for comparative study and equivalence proofs, and does
not replace the custom `List.Vector B n` used in the main codebase.
-/

abbrev BinString := List Bool

/-- Removes the `i`-th bit from a binary string. -/
def deleteIdx (s : BinString) (i : Nat) : BinString :=
  s.take i ++ s.drop (i + 1)

/-- Example: Deleting the 0th element of `[true, false]` yields `[false]`. -/
example : deleteIdx [true, false] 0 = [false] := by rfl

/-- Example: Deleting an out-of-bounds index leaves the string unchanged. -/
example : deleteIdx [true, false] 5 = [true, false] := by rfl

/-- The length of a string after a valid deletion decreases by 1. -/
theorem length_deleteIdx_of_lt {s : BinString} {i : Nat} (h : i < s.length) :
    (deleteIdx s i).length = s.length - 1 := by
  dsimp [deleteIdx]
  rw [List.length_append, List.length_take, List.length_drop]
  omega

/-- Deleting from an empty string yields an empty string. -/
theorem deleteIdx_nil (i : Nat) : deleteIdx [] i = [] := by
  dsimp [deleteIdx]
  rw [List.take_nil, List.drop_nil, List.nil_append]

/-- Deleting the first element of a cons list yields the tail. -/
theorem deleteIdx_zero (x : Bool) (xs : BinString) : deleteIdx (x :: xs) 0 = xs := by
  rfl

/-- Deleting at index `i+1` of a cons list is equivalent to keeping the head
and deleting at `i` in the tail. -/
theorem deleteIdx_succ (x : Bool) (xs : BinString) (i : Nat) :
    deleteIdx (x :: xs) (i + 1) = x :: deleteIdx xs i := by
  rfl

/-
Equivalence Note: Notice how `deleteIdx_zero` and `deleteIdx_succ`
together perfectly mirror the inductive definition of the custom `sDel`!
This shows that structurally, `take i ++ drop (i+1)` simplifies under
the hood to exactly the recursive cases manually written in `InsDel.lean`.
-/
