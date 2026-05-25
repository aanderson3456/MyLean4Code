import re

with open('scratch_numos.lean', 'r') as f:
    content = f.read()

# Fix num_LOs_le_sDel
content = re.sub(r'lemma num_LOs_le_sDel.*?(?=lemma num_LOs_sIns )',
'''lemma num_LOs_le_sDel (X : List B) (i : Nat) (H : i + 1 ≤ X.length) : num_LOs X i ≤ num_Os (sDel X i) := by
  revert H
  revert X
  induction i with
  | zero =>
    intro X H
    exact Nat.zero_le _
  | succ k ih =>
    intro X H
    cases X with
    | nil => exact Nat.zero_le _
    | cons x X' =>
      cases X' with
      | nil =>
        have h_absurd : k + 2 ≤ 1 := H
        contradiction
      | cons x' X'' =>
        cases x
        · apply Nat.succ_le_succ
          exact ih (x'::X'') (Nat.le_of_succ_le_succ H)
        · exact ih (x'::X'') (Nat.le_of_succ_le_succ H)

''', content, flags=re.DOTALL)

# Fix num_LOs_sIns
content = re.sub(r'lemma num_LOs_sIns \(X : List B\) \(i : Nat\) \(b : B\) \(H : i \+ 1 ≤ X.length\).*?(?=lemma num_LOs_sIns_one)',
'''lemma num_LOs_sIns (X : List B) (i : Nat) (b : B) (H : i + 1 ≤ X.length) : num_LOs (sIns X i b) i = num_LOs X i := by
  revert H
  revert X
  induction i with
  | zero =>
    intro X H
    rfl
  | succ k ih =>
    intro X H
    cases X with
    | nil =>
      have h_absurd : k + 2 ≤ 0 := H
      contradiction
    | cons x X' =>
      cases x
      · have ih_res := ih X' (Nat.le_of_succ_le_succ H)
        exact congrArg (· + 1) ih_res
      · exact ih X' (Nat.le_of_succ_le_succ H)

''', content, flags=re.DOTALL)

# Fix sIns_one_of_num_LOs
content = re.sub(r'lemma sIns_one_of_num_LOs.*?(?=def num_RIs)',
'''lemma sIns_one_of_num_LOs (X : List B) (i j : Nat) (H : num_LOs X i = num_LOs X j) : sIns X i B.I = sIns X j B.I := by
  revert i j
  induction X with
  | nil =>
    intro i j _
    rfl
  | cons x X' ih =>
    intro i j H
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        have h1 : num_LOs (x::X') 0 = 0 := rfl
        rw [h1] at H
        have hx := head_of_num_LOs X' x j' H.symm
        subst hx
        apply congrArg
        have H' : num_LOs X' 0 = num_LOs X' j' := by exact H
        exact ih 0 j' H'
    | succ i' =>
      cases j with
      | zero =>
        have h1 : num_LOs (x::X') 0 = 0 := rfl
        rw [h1] at H
        have hx := head_of_num_LOs X' x i' H
        subst hx
        apply congrArg
        have H' : num_LOs X' i' = num_LOs X' 0 := by exact H
        exact ih i' 0 H'
      | succ j' =>
        cases x
        · apply congrArg
          exact ih i' j' (Nat.succ.inj H)
        · apply congrArg
          exact ih i' j' H

''', content, flags=re.DOTALL)

# Fix num_RIs_le_cons
content = re.sub(r'lemma num_RIs_le_cons.*?(?=lemma num_RIs_succ_le)',
'''lemma num_RIs_le_cons (x : B) (X : List B) (i : Nat) : num_RIs X i ≤ num_RIs (x::X) i := by
  revert x i
  induction X with
  | nil =>
    intro x i
    cases i
    · exact Nat.zero_le _
    · exact Nat.zero_le _
  | cons x' X' ih =>
    intro x i
    cases i with
    | zero =>
      exact num_Is_le_cons x (x'::X')
    | succ i' =>
      exact Nat.le_refl _

''', content, flags=re.DOTALL)

# Fix num_RIs_le
content = re.sub(r'lemma num_RIs_le \(X : List B\) \(i : Nat\) : num_RIs X i ≤ X\.length - i := by.*?exact ih i\'',
'''lemma num_RIs_le (X : List B) (i : Nat) : num_RIs X i ≤ X.length - i := by
  revert i
  induction X with
  | nil =>
    intro i
    exact Nat.zero_le _
  | cons x X' ih =>
    intro i
    cases i with
    | zero =>
      rw [num_RIs_zero]
      exact num_Is_le_length (x::X')
    | succ i' =>
      exact ih i\'''', content, flags=re.DOTALL)

# Fix sIns_zero_of_num_RIs
content = re.sub(r'lemma sIns_zero_of_num_RIs.*?(?=lemma num_Is_sDel_lt_sub_mod)',
'''lemma sIns_zero_of_num_RIs (X : List B) (i j : Nat) (H : num_RIs X i = num_RIs X j) : sIns X i B.O = sIns X j B.O := by
  revert i j
  induction X with
  | nil => 
    intro i j _
    rfl
  | cons x X' ih =>
    intro i j H
    cases i with
    | zero =>
      cases j with
      | zero => rfl
      | succ j' =>
        have h1 : num_RIs (x::X') 0 = num_Is (x::X') := rfl
        rw [h1] at H
        have H_symm : num_RIs (x::X') (j' + 1) = num_Is (x::X') := H.symm
        have hx := head_of_num_RIs X' x j' H_symm
        subst hx
        apply congrArg
        have H' : num_RIs X' 0 = num_RIs X' j' := by exact H
        exact ih 0 j' H'
    | succ i' =>
      cases j with
      | zero =>
        have h1 : num_RIs (x::X') 0 = num_Is (x::X') := rfl
        rw [h1] at H
        have hx := head_of_num_RIs X' x i' H
        subst hx
        apply congrArg
        have H' : num_RIs X' i' = num_RIs X' 0 := by exact H
        exact ih i' 0 H'
      | succ j' =>
        apply congrArg
        exact ih i' j' H

''', content, flags=re.DOTALL)

# Fix num_Is_sDel_lt_sub_mod
content = re.sub(r'lemma num_Is_sDel_lt_sub_mod.*?(?=end List)',
'''lemma num_Is_sDel_lt_sub_mod (X : List B) (i : Nat) : num_Is (sDel X i) < num_RIs X i + i + 1 := by
  revert i
  induction X with
  | nil =>
    intro i
    exact Nat.zero_lt_succ _
  | cons x X' ih =>
    intro i
    cases X' with
    | nil =>
      have h1 : num_Is (sDel [x] i) = 0 := by cases i <;> rfl
      have h2 : num_RIs [x] i + i + 1 ≥ 1 := by omega
      omega
    | cons x' X'' =>
      cases i with
      | zero =>
        have h := num_Is_le_cons x (x'::X'')
        omega
      | succ i' =>
        have h1 := num_Is_cons_le x (sDel (x'::X'') i')
        have h2 := ih i'
        omega

''', content, flags=re.DOTALL)

with open('scratch_numos.lean', 'w') as f:
    f.write(content)

