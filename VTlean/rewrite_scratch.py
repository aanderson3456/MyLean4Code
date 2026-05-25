import re

with open('scratch_numos.lean', 'r') as f:
    content = f.read()

content = re.sub(
    r'change B\.I :: sIns X\' 0 B\.I = B\.I :: sIns X\' \(j\' \+ 1\) B\.I',
    'change B.I :: B.I :: X\' = B.I :: sIns X\' j\' B.I',
    content
)
content = re.sub(
    r'change B\.I :: sIns X\' \(i\' \+ 1\) B\.I = B\.I :: sIns X\' 0 B\.I',
    'change B.I :: sIns X\' i\' B.I = B.I :: B.I :: X\'',
    content
)

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
      exact ih x' i'

''', content, flags=re.DOTALL)

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
      have h1 : num_RIs (x::X') (i'+1) = num_RIs X' i' := rfl
      have h2 : (x::X').length = X'.length + 1 := rfl
      have h3 := ih i'
      omega\'''', content, flags=re.DOTALL)

content = re.sub(
    r'change B\.O :: sIns X\' 0 B\.O = B\.O :: sIns X\' \(j\' \+ 1\) B\.O',
    'change B.O :: B.O :: X\' = B.O :: sIns X\' j\' B.O',
    content
)
content = re.sub(
    r'change B\.O :: sIns X\' \(i\' \+ 1\) B\.O = B\.O :: sIns X\' 0 B\.O',
    'change B.O :: sIns X\' i\' B.O = B.O :: B.O :: X\'',
    content
)

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
        have h1 : num_Is (sDel (x::x'::X'') 0) = num_Is (x'::X'') := rfl
        have h2 : num_RIs (x::x'::X'') 0 = num_Is (x::x'::X'') := rfl
        have h3 := num_Is_le_cons x (x'::X'')
        omega
      | succ i' =>
        have h1 : num_Is (sDel (x::x'::X'') (i'+1)) = num_Is (x :: sDel (x'::X'') i') := rfl
        have h2 : num_RIs (x::x'::X'') (i'+1) = num_RIs (x'::X'') i' := rfl
        have h3 := num_Is_cons_le x (sDel (x'::X'') i')
        have h4 := ih i'
        omega

''', content, flags=re.DOTALL)

with open('scratch_numos.lean', 'w') as f:
    f.write(content)

