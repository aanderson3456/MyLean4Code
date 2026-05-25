with open("VTlean/NumOsNumIs.lean", "r") as f:
    content = f.read()

ri_start = content.find("def num_RIs")
vec_start = content.find("namespace Vector")

if ri_start != -1 and vec_start != -1:
    new_ri_section = """def num_RIs : List B → Nat → Nat
  | [], _ => 0
  | x::X, 0 => num_Is (x::X)
  | _::X, n+1 => num_RIs X n

lemma num_RIs_zero (X : List B) : num_RIs X 0 = num_Is X := by
  cases X
  · rfl
  · rfl

lemma num_RIs_le_cons (x : B) (X : List B) (i : Nat) : num_RIs (x::X) (i + 1) ≤ num_RIs (x::X) i := by
  sorry

lemma num_RIs_succ_le (X : List B) (i : Nat) : num_RIs X (i + 1) ≤ num_RIs X i := by
  sorry

lemma num_RIs_le (X : List B) (i j : Nat) (H : i ≤ j) : num_RIs X j ≤ num_RIs X i := by
  sorry

lemma num_RIs_le_num_Is (X : List B) (i : Nat) : num_RIs X i ≤ num_Is X := by
  sorry

lemma num_RIs_of_ovrlen (X : List B) (i : Nat) (H : X.length ≤ i) : num_RIs X i = 0 := by
  sorry

lemma num_RIs_sIns_zero (X : List B) (b : B) : num_RIs (sIns X 0 b) 0 = num_Is (sIns X 0 b) := by
  sorry

lemma num_RIs_sIns (X : List B) (i j : Nat) (b : B) (H : i ≤ j) : num_RIs (sIns X j b) i = num_RIs X i + num_Is [b] := by
  sorry

lemma head_of_num_RIs (X : List B) (x : B) (i : Nat) (H : num_RIs (x::X) i = num_RIs (x::X) (i + 1) + 1) : x = B.I := by
  sorry

lemma sIns_zero_of_num_RIs (X : List B) (i j : Nat) (H : num_RIs X i = num_RIs X j) : sIns X i B.O = sIns X j B.O := by
  sorry

lemma num_Is_sDel_lt_sub_mod (X : List B) (i : Nat) (H : i + 1 ≤ X.length) : num_Is (sDel X i) < num_Is X ↔ num_RIs X i = num_RIs X (i + 1) + 1 := by
  sorry

"""
    content = content[:ri_start] + new_ri_section + content[vec_start:]

with open("VTlean/NumOsNumIs.lean", "w") as f:
    f.write(content)
