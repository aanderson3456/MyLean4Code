import VTlean.Dream
open B

lemma card_vector_B_eq_test (m : Nat) : Fintype.card (List.Vector B m) = 2^m := by {
  have h1 : Fintype.card (List.Vector B m) = Fintype.card (Fin m → B) :=
    Fintype.card_congr (Equiv.vectorEquivFin B m)
  have h2 : Fintype.card (Fin m → B) = Fintype.card B ^ Fintype.card (Fin m) := Fintype.card_fun
  have h3 : Fintype.card B = 2 := B.card_B
  have h4 : Fintype.card (Fin m) = m := Fintype.card_fin m
  rw [h1, h2, h3, h4]
}
