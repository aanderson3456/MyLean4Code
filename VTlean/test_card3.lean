import VTlean.Dream
open B

lemma card_vector_B_eq_test (m : Nat) : Fintype.card (List.Vector B m) = 2^m := by {
  have h1 : Fintype.card B = 2 := rfl
  -- Let's try rw [Fintype.card_vector]
  -- Vector is defined as Mathlib.Vector, let's see if List.Vector works.
  -- Vector isn't imported perhaps? 
  exact sorry
}
#check Fintype.card_vector
