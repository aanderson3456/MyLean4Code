import VTlean.NumOsNumIs

namespace List
variable (X Y : List B) (x y : B) (i j : Nat)

lemma num_Os_add_num_Is_proof (X : List B) : num_Os X + num_Is X = X.length := by
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · change num_Os X' + 1 + num_Is X' = X'.length + 1
      omega
    · change num_Os X' + (num_Is X' + 1) = X'.length + 1
      omega

lemma num_Os_eq_len_sub_proof (X : List B) : num_Os X = X.length - num_Is X := by
  have h := num_Os_add_num_Is_proof X
  omega

lemma num_Is_eq_len_sub_proof (X : List B) : num_Is X = X.length - num_Os X := by
  have h := num_Os_add_num_Is_proof X
  omega

lemma num_Is_flip_eq_num_Os_proof (X : List B) : num_Is (flip X) = num_Os X := by
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · change num_Is (flip X') + 1 = num_Os X' + 1
      omega
    · change num_Is (flip X') = num_Os X'
      omega

end List
