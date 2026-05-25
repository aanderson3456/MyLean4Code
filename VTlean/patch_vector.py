import re

with open('VTlean/NumOsNumIs.lean', 'r') as f:
    content = f.read()

# find where namespace Vector starts
ns_idx = content.find("namespace Vector")

new_vector_content = """namespace Vector
variable {n : Nat}

def wt (X : List.Vector B n) : Nat := List.num_Is X.val

lemma wt_sDel_le (X : List.Vector B (n + 1)) (i : Nat) : wt (List.Vector.sDel X i) ≤ wt X := by
  change List.num_Is (List.Vector.sDel X i).val ≤ List.num_Is X.val
  have h : (List.Vector.sDel X i).val = List.sDel X.val i := rfl
  rw [h]
  exact List.num_Is_sDel_le X.val i

lemma wt_le_sDel (X : List.Vector B (n + 1)) (i : Nat) : wt X - 1 ≤ wt (List.Vector.sDel X i) := by
  change List.num_Is X.val - 1 ≤ List.num_Is (List.Vector.sDel X i).val
  have h : (List.Vector.sDel X i).val = List.sDel X.val i := rfl
  rw [h]
  exact List.num_Is_le_sDel X.val i

lemma sDel_of_wt_le (X : List.Vector B (n + 1)) (H : wt X ≤ 1) : ∃ i : Nat, List.Vector.sDel X i = List.Vector.replicate (n + 1 - 1) B.O := by
  have H' : List.num_Is X.val ≤ 1 := H
  cases List.sDel_of_num_Is_le X.val H' with
  | intro i hi =>
    exists i
    apply Subtype.ext
    change List.sDel X.val i = List.replicate ((n + 1) - 1) B.O
    have hX_len : X.val.length = n + 1 := X.2
    have h_replicate : List.replicate (X.val.length - 1) B.O = List.replicate ((n + 1) - 1) B.O := by
      rw [hX_len]
    rw [← h_replicate]
    exact hi

lemma sDel_of_le_wt (X : List.Vector B (n + 1)) (H : (n + 1) - 1 ≤ wt X) : ∃ i : Nat, List.Vector.sDel X i = List.Vector.replicate (n + 1 - 1) B.I := by
  have H' : (n + 1) - 1 ≤ List.num_Is X.val := H
  have hX_len : X.val.length = n + 1 := X.2
  have H'' : X.val.length - 1 ≤ List.num_Is X.val := by
    rw [hX_len]
    exact H'
  cases List.sDel_of_le_num_Is X.val H'' with
  | intro i hi =>
    exists i
    apply Subtype.ext
    change List.sDel X.val i = List.replicate ((n + 1) - 1) B.I
    have h_replicate : List.replicate (X.val.length - 1) B.I = List.replicate ((n + 1) - 1) B.I := by
      rw [hX_len]
    rw [← h_replicate]
    exact hi

def num_LOs (X : List.Vector B n) (i : Nat) : Nat :=
  List.num_LOs X.val i

lemma num_LOs_zero (X : List.Vector B n) : num_LOs X 0 = 0 := by
  exact List.num_LOs_zero X.val 0

lemma num_LOs_le (X : List.Vector B n) (i : Nat) : num_LOs X i ≤ i := by
  exact List.num_LOs_le X.val i

lemma num_LOs_le_length (X : List.Vector B n) (i : Nat) (H : i + 1 ≤ n) : num_LOs X i ≤ n - 1 := by
  have H' : i + 1 ≤ X.val.length := by
    have hX_len : X.val.length = n := X.2
    rw [hX_len]
    exact H
  have h := List.num_LOs_le_length X.val i H'
  have hX_len : X.val.length = n := X.2
  rw [hX_len] at h
  exact h

lemma num_LOs_sIns (X : List.Vector B n) (i : Nat) (b : B) (H : i + 1 ≤ n) : num_LOs (List.Vector.sIns X i b) i = num_LOs X i := by
  have H' : i + 1 ≤ X.val.length := by
    have hX_len : X.val.length = n := X.2
    rw [hX_len]
    exact H
  exact List.num_LOs_sIns X.val i b H'

lemma sIns_one_of_num_LOs (X : List.Vector B n) (i j : Nat) (H : num_LOs X i = num_LOs X j) : List.Vector.sIns X i B.I = List.Vector.sIns X j B.I := by
  apply Subtype.ext
  change List.sIns X.val i B.I = List.sIns X.val j B.I
  exact List.sIns_one_of_num_LOs X.val i j H

def num_RIs (X : List.Vector B n) (i : Nat) : Nat :=
  List.num_RIs X.val i

lemma num_RIs_zero (X : List.Vector B n) : num_RIs X 0 = wt X := by
  exact List.num_RIs_zero X.val

lemma num_RIs_le (X : List.Vector B n) (i : Nat) : num_RIs X i ≤ n - i := by
  have h := List.num_RIs_le X.val i
  have hX_len : X.val.length = n := X.2
  rw [hX_len] at h
  exact h

lemma num_RIs_le_wt (X : List.Vector B n) (i : Nat) : num_RIs X i ≤ wt X := by
  exact List.num_RIs_le_num_Is X.val i

lemma num_RIs_of_ovrlen (X : List.Vector B n) (i : Nat) (H : n ≤ i) : num_RIs X i = 0 := by
  have H' : X.val.length ≤ i := by
    have hX_len : X.val.length = n := X.2
    rw [hX_len]
    exact H
  exact List.num_RIs_of_ovrlen X.val i H'

lemma num_RIs_sIns_zero (X : List.Vector B n) (i : Nat) : num_RIs (List.Vector.sIns X i B.O) i = num_RIs X i := by
  exact List.num_RIs_sIns_zero X.val i

lemma num_RIs_sIns (X : List.Vector B n) (i : Nat) (b : B) (H : n + 1 ≤ i) : num_RIs (List.Vector.sIns X i b) i = num_RIs X i := by
  have H' : X.val.length + 1 ≤ i := by
    have hX_len : X.val.length = n := X.2
    rw [hX_len]
    exact H
  exact List.num_RIs_sIns X.val i b H'

lemma sIns_zero_of_num_RIs (X : List.Vector B n) (i j : Nat) (H : num_RIs X i = num_RIs X j) : List.Vector.sIns X i B.O = List.Vector.sIns X j B.O := by
  apply Subtype.ext
  change List.sIns X.val i B.O = List.sIns X.val j B.O
  exact List.sIns_zero_of_num_RIs X.val i j H

lemma num_Is_sDel_lt_sub_mod (X : List.Vector B (n + 1)) (i : Nat) : wt (List.Vector.sDel X i) < num_RIs X i + i + 1 := by
  change List.num_Is (List.sDel X.val i) < List.num_RIs X.val i + i + 1
  exact List.num_Is_sDel_lt_sub_mod X.val i

lemma wt_flip (X : List.Vector B n) : wt (B.Vector.flip X) = n - wt X := by
  change List.num_Is (B.List.flip X.val) = n - List.num_Is X.val
  have h := List.num_Is_flip X.val
  have hX_len : X.val.length = n := X.2
  rw [hX_len] at h
  exact h

def Iic_wt (a : Nat) (X : List.Vector B n) := wt X ≤ a

instance decidable_pred_Iic_wt (a : Nat) : DecidablePred (Iic_wt (n:=n) a) := by
  intro s; unfold Iic_wt; exact inferInstance

def Icc_wt (a b : Nat) (X : List.Vector B n) := a ≤ wt X ∧ wt X ≤ b

instance decidable_pred_Icc_wt (a b : Nat) : DecidablePred (Icc_wt (n:=n) a b) := by
  intro s; unfold Icc_wt; exact inferInstance

lemma Icc_wt_self (a : Nat) (X : List.Vector B n) : Icc_wt a a X ↔ wt X = a := by
  apply Iff.intro
  · intro h
    unfold Icc_wt at h
    omega
  · intro h
    unfold Icc_wt
    omega

def Ici_wt (a : Nat) (X : List.Vector B n) := a ≤ wt X

instance decidable_pred_Ici_wt (a : Nat) : DecidablePred (Ici_wt (n:=n) a) := by
  intro s; unfold Ici_wt; exact inferInstance

end Vector
"""

with open('VTlean/NumOsNumIs.lean', 'w') as f:
    f.write(content[:ns_idx] + new_vector_content)

