import VTlean.DelCode

open Nat List.Vector Finset B

variable {n : Nat}

lemma eq_replicate_O_of_wt_zero (X : List.Vector B n) (HX : wt X = 0) :
  X = List.Vector.replicate n O := by
  sorry

lemma eq_replicate_I_of_wt_n (X : List.Vector B n) (HX : wt X = n) :
  X = List.Vector.replicate n I := by
  sorry

lemma sDel_replicate_O (i : Fin n) :
  List.Vector.sDel (List.Vector.replicate n O) i = List.Vector.replicate (n - 1) O := by
  sorry

lemma sDel_replicate_I (i : Fin n) :
  List.Vector.sDel (List.Vector.replicate n I) i = List.Vector.replicate (n - 1) I := by
  sorry

