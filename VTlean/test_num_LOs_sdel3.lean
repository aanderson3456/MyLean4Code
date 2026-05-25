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
      cases x
      · change num_LOs X' i' + 1 ≤ num_LOs (sDel (B.O :: X') (i' + 1)) (i' + 1) + 1
        unfold sDel
        change num_LOs X' i' + 1 ≤ num_LOs (sDel X' i') i' + 1 + 1
        have h := ih i'
        omega
      · change num_LOs X' i' ≤ num_LOs (sDel (B.I :: X') (i' + 1)) (i' + 1) + 1
        unfold sDel
        change num_LOs X' i' ≤ num_LOs (sDel X' i') i' + 1
        have h := ih i'
        omega

end List
