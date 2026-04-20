import Mathlib.Data.Vector.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import VTlean.Lemma

namespace Vector

variable {α : Type} [DecidableEq α]

/-- Vector-based single deletion -/
def sDel {n : Nat} (X : Vector α n) (i : Nat) : Vector α (n - 1) :=
  sorry

/-- Vector-based single insertion -/
def sIns {n : Nat} (X : Vector α n) (i : Nat) (b : α) : Vector α (n + 1) :=
  sorry

open Finset
variable [Fintype α]

/-- Deletion sphere -/
def dS {n : Nat} (X : Vector α (n + 1)) : Finset (Vector α n) :=
  sorry

/-- Insertion sphere -/
def IS {n : Nat} (X : Vector α n) : Finset (Vector α (n + 1)) :=
  sorry

lemma mem_dS {n : Nat} {X : Vector α (n + 1)} {Y : Vector α n} :
  Y ∈ dS X ↔ ∃ i ≤ n, Y = sDel X i :=
  sorry

lemma mem_IS {n : Nat} {X : Vector α n} {Y : Vector α (n + 1)} :
  Y ∈ IS X ↔ ∃ i ≤ n, ∃ b, Y = sIns X i b :=
  sorry

end Vector
