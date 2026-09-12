import VTlean.B
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.List

open B

lemma card_vector_B_eq_test (m : Nat) : Fintype.card { l : List B // l.length = m } = 2^m := by {
  have h_card : Fintype.card B = 2 := rfl
  -- exact? 
  simp
}
