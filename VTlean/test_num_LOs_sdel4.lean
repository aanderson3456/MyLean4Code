import VTlean.NumOsNumIs

namespace List
variable (X : List B) (i : Nat)

lemma num_LOs_le_sDel_proof (X : List B) (i : Nat) : num_LOs X i ≤ num_LOs (sDel X i) i + 1 := by
  induction X generalizing i with
  | nil =>
    cases i <;> exact Nat.zero_le _
  | cons x X' ih =>
    cases i with
    | zero =>
      cases x <;> exact Nat.zero_le _
    | succ i' =>
      cases X'
      · cases x <;> exact Nat.le_refl _
      · rename_i y Y
        cases x
        · change num_LOs (y::Y) i' + 1 ≤ num_LOs (B.O :: sDel (y::Y) i') (i' + 1) + 1
          change num_LOs (y::Y) i' + 1 ≤ num_LOs (sDel (y::Y) i') i' + 1 + 1
          have h := ih i'
          omega
        · change num_LOs (y::Y) i' ≤ num_LOs (B.I :: sDel (y::Y) i') (i' + 1) + 1
          change num_LOs (y::Y) i' ≤ num_LOs (sDel (y::Y) i') i' + 1
          have h := ih i'
          omega

end List
