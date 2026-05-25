import re

with open('scratch_numos.lean', 'r') as f:
    content = f.read()

content = re.sub(r'lemma sIns_one_of_num_LOs.*?lemma num_RIs_zero',
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
        have hx := head_of_num_LOs X' x j' H.symm
        subst hx
        change B.I :: sIns X' 0 B.I = B.I :: sIns X' j' B.I
        have H' : num_LOs X' 0 = num_LOs X' j' := by
          rw [num_LOs_zero X' 0]
          exact H
        exact congrArg (fun L => B.I :: L) (ih 0 j' H')
    | succ i' =>
      cases j with
      | zero =>
        have hx := head_of_num_LOs X' x i' H
        subst hx
        change B.I :: sIns X' i' B.I = B.I :: sIns X' 0 B.I
        have H' : num_LOs X' i' = num_LOs X' 0 := by
          rw [num_LOs_zero X' 0]
          exact H
        exact congrArg (fun L => B.I :: L) (ih i' 0 H')
      | succ j' =>
        cases x
        · exact congrArg (fun L => B.O :: L) (ih i' j' (Nat.succ.inj H))
        · exact congrArg (fun L => B.I :: L) (ih i' j' H)

def num_RIs : List B → Nat → Nat
  | [], _ => 0
  | x::X, 0 => num_Is (x::X)
  | _::X, n+1 => num_RIs X n

lemma num_RIs_zero''', content, flags=re.DOTALL)

content = re.sub(r'lemma num_RIs_le \(X : List B\) \(i : Nat\) : num_RIs X i ≤ X\.length - i := by.*?lemma num_RIs_le_num_Is',
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
      have h1 : num_RIs (x::X') (i'+1) = num_RIs X' i' := rfl
      rw [h1]
      have h2 : (x::X').length - (i'+1) = X'.length - i' := rfl
      rw [h2]
      exact ih i'

lemma num_RIs_le_num_Is''', content, flags=re.DOTALL)

content = re.sub(r'lemma sIns_zero_of_num_RIs.*?lemma num_Is_sDel_lt_sub_mod',
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
        have hx := head_of_num_RIs X' x j' H.symm
        subst hx
        change B.O :: sIns X' 0 B.O = B.O :: sIns X' j' B.O
        have H' : num_RIs X' 0 = num_RIs X' j' := by
          rw [num_RIs_zero X']
          exact H
        exact congrArg (fun L => B.O :: L) (ih 0 j' H')
    | succ i' =>
      cases j with
      | zero =>
        have hx := head_of_num_RIs X' x i' H
        subst hx
        change B.O :: sIns X' i' B.O = B.O :: sIns X' 0 B.O
        have H' : num_RIs X' i' = num_RIs X' 0 := by
          rw [num_RIs_zero X']
          exact H
        exact congrArg (fun L => B.O :: L) (ih i' 0 H')
      | succ j' =>
        exact congrArg (fun L => x :: L) (ih i' j' H)

''', content, flags=re.DOTALL)

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
      rw [h1]
      omega
    | cons x' X'' =>
      cases i with
      | zero =>
        have h_sDel : sDel (x::x'::X'') 0 = x'::X'' := rfl
        have h_numRIs : num_RIs (x::x'::X'') 0 = num_Is (x::x'::X'') := rfl
        rw [h_sDel, h_numRIs]
        have h3 := num_Is_le_cons x (x'::X'')
        omega
      | succ i' =>
        have h_sDel : sDel (x::x'::X'') (i'+1) = x :: sDel (x'::X'') i' := rfl
        have h_numRIs : num_RIs (x::x'::X'') (i'+1) = num_RIs (x'::X'') i' := rfl
        rw [h_sDel, h_numRIs]
        have h3 := num_Is_cons_le x (sDel (x'::X'') i')
        have h4 := ih i'
        omega

''', content, flags=re.DOTALL)

with open('scratch_numos.lean', 'w') as f:
    f.write(content)
