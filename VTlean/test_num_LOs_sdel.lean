import VTlean.NumOsNumIs

namespace List
variable (X : List B) (i : Nat)

lemma num_LOs_le_sDel_proof (X : List B) (i : Nat) : num_LOs X i ≤ num_LOs (sDel X i) i + 1 := by
  induction X generalizing i with
  | nil =>
    cases i
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  | cons x X' ih =>
    cases i with
    | zero =>
      cases x
      · exact Nat.zero_le _
      · exact Nat.zero_le _
    | succ i' =>
      cases x
      · have h := ih i'
        dsimp [num_LOs, sDel]
        omega
      · have h := ih i'
        dsimp [num_LOs, sDel]
        omega

end List
