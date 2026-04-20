import VTlean.B

namespace List
variable (X : List B)

def num_Is : List B → Nat
| [] => 0
| B.O :: tail => num_Is tail
| B.I :: tail => num_Is tail + 1

def num_Os : List B → Nat
| [] => 0
| B.O :: tail => num_Os tail + 1
| B.I :: tail => num_Os tail

lemma num_Os_add_num_Is_eq_length (X : List B) : num_Os X + num_Is X = X.length := by
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · change (num_Os X' + 1) + num_Is X' = X'.length + 1
      rw [Nat.add_right_comm, ih]
    · change num_Os X' + (num_Is X' + 1) = X'.length + 1
      rw [← Nat.add_assoc, ih]

end List

namespace Vector
variable {n : Nat}

def num_Is (X : Vector B n) : Nat := List.num_Is X.toList

def num_Os (X : Vector B n) : Nat := List.num_Os X.toList

end Vector
