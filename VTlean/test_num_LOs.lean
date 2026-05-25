import VTlean.NumOsNumIs

namespace List
variable (X : List B) (i : Nat)

lemma num_LOs_le_num_Os_proof (X : List B) (i : Nat) : num_LOs X i ≤ num_Os X := by
  induction X generalizing i with
  | nil =>
    cases i <;> exact Nat.zero_le _
  | cons x X' ih =>
    cases i with
    | zero => exact Nat.zero_le _
    | succ i' =>
      cases x
      · change num_LOs X' i' + 1 ≤ num_Os X' + 1
        have h := ih i'
        omega
      · change num_LOs X' i' ≤ num_Os X'
        have h := ih i'
        omega

lemma num_LOs_of_ovrlen_proof (X : List B) (i : Nat) (H : X.length ≤ i) : num_LOs X i = num_Os X := by
  induction X generalizing i with
  | nil =>
    cases i
    · rfl
    · change 0 = 0; rfl
  | cons x X' ih =>
    cases i with
    | zero => contradiction
    | succ i' =>
      have H' : X'.length ≤ i' := Nat.le_of_succ_le_succ H
      cases x
      · change num_LOs X' i' + 1 = num_Os X' + 1
        have h := ih i' H'
        omega
      · change num_LOs X' i' = num_Os X'
        have h := ih i' H'
        omega

lemma num_LOs_le_length_proof (X : List B) (i : Nat) (H : i + 1 ≤ X.length) : num_LOs X i ≤ X.length - 1 := by
  have h := num_LOs_le X i
  omega

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
      · change num_LOs X' i' + 1 ≤ num_LOs (sDel X' i') i' + 1 + 1
        have h := ih i'
        omega
      · change num_LOs X' i' ≤ num_LOs (sDel X' i') i' + 1
        have h := ih i'
        omega

end List
