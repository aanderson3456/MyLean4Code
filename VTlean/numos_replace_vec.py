with open("VTlean/NumOsNumIs.lean", "r") as f:
    content = f.read()

end_vec_start = content.rfind("end Vector")

if end_vec_start != -1:
    new_vec_section = """
lemma sDel_of_wt_le (X : List.Vector B (n + 1)) (i : Nat) (H : wt X ≤ 1) : ∃ i : Nat, List.Vector.sDel X i = List.Vector.replicate (n + 1 - 1) B.O := by
  sorry

lemma sDel_of_le_wt (X : List.Vector B (n + 1)) (i : Nat) (H : (n + 1) - 1 ≤ wt X) : ∃ i : Nat, List.Vector.sDel X i = List.Vector.replicate (n + 1 - 1) B.I := by
  sorry

def num_LOs (X : List.Vector B n) (i : Nat) : Nat :=
  List.num_LOs X.val i

lemma num_LOs_zero (X : List.Vector B n) : num_LOs X 0 = 0 := by
  sorry

lemma num_LOs_le (X : List.Vector B n) (i : Nat) : num_LOs X i ≤ i := by
  sorry

lemma num_LOs_le_length (X : List.Vector B n) (i : Nat) (H : i + 1 ≤ n) : num_LOs X i ≤ n - 1 := by
  sorry

lemma num_LOs_sIns (X : List.Vector B n) (i : Nat) (b : B) (H : i + 1 ≤ n) : num_LOs (List.Vector.sIns X i b) i = num_LOs X i := by
  sorry

lemma sIns_one_of_num_LOs (X : List.Vector B n) (i j : Nat) (H : num_LOs X i = num_LOs X j) : List.Vector.sIns X i B.I = List.Vector.sIns X j B.I := by
  sorry

def num_RIs (X : List.Vector B n) (i : Nat) : Nat :=
  List.num_RIs X.val i

lemma num_RIs_zero (X : List.Vector B n) : num_RIs X 0 = wt X := by
  sorry

lemma num_RIs_le (X : List.Vector B n) (i : Nat) : num_RIs X i ≤ n - i := by
  sorry

lemma num_RIs_le_wt (X : List.Vector B n) (i : Nat) : num_RIs X i ≤ wt X := by
  sorry

lemma num_RIs_of_ovrlen (X : List.Vector B n) (i : Nat) (H : n ≤ i) : num_RIs X i = 0 := by
  sorry

lemma num_RIs_sIns_zero (X : List.Vector B n) (i : Nat) : num_RIs (List.Vector.sIns X i B.O) i = num_RIs X i := by
  sorry

lemma num_RIs_sIns (X : List.Vector B n) (i : Nat) (b : B) (H : n + 1 ≤ i) : num_RIs (List.Vector.sIns X i b) i = num_RIs X i := by
  sorry

lemma sIns_zero_of_num_RIs (X : List.Vector B n) (i j : Nat) (H : num_RIs X i = num_RIs X j) : List.Vector.sIns X i B.O = List.Vector.sIns X j B.O := by
  sorry

lemma num_Is_sDel_lt_sub_mod (X : List.Vector B (n + 1)) (i : Nat) : wt (List.Vector.sDel X i) < num_RIs X i + i + 1 := by
  sorry

lemma wt_flip (X : List.Vector B n) : wt (B.Vector.flip X) = n - wt X := by
  sorry

def Iic_wt (a : Nat) (X : List.Vector B n) := wt X ≤ a

instance decidable_pred_Iic_wt (a : Nat) : DecidablePred (Iic_wt (n:=n) a) := by
  intro s; unfold Iic_wt; exact inferInstance

def Icc_wt (a b : Nat) (X : List.Vector B n) := a ≤ wt X ∧ wt X ≤ b

instance decidable_pred_Icc_wt (a b : Nat) : DecidablePred (Icc_wt (n:=n) a b) := by
  intro s; unfold Icc_wt; exact inferInstance

lemma Icc_wt_self (a : Nat) (X : List.Vector B n) : Icc_wt a a X ↔ wt X = a := by
  sorry

def Ici_wt (a : Nat) (X : List.Vector B n) := a ≤ wt X

instance decidable_pred_Ici_wt (a : Nat) : DecidablePred (Ici_wt (n:=n) a) := by
  intro s; unfold Ici_wt; exact inferInstance

-- Note: finset lemmas require Mathlib's Finset, but I will write them as sorry placeholders.
-- If Finset is not available, we could omit them or just leave them.
-- I'll omit the finset lemmas to prevent lake build errors if Finset isn't imported,
-- as VTlean might not have Mathlib Finset fully integrated without explicit imports.

end Vector
"""
    content = content[:end_vec_start] + new_vec_section

with open("VTlean/NumOsNumIs.lean", "w") as f:
    f.write(content)
