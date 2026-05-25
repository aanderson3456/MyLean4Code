with open("VTlean/NumOsNumIs.lean", "r") as f:
    content = f.read()

# Replace num_LOs section
lo_start = content.find("def num_LOs")
ri_start = content.find("def num_RIs")

if lo_start != -1 and ri_start != -1:
    new_lo_section = """def num_LOs : List B → Nat → Nat
  | [], _ => 0
  | _::_, 0 => 0
  | B.O::X, n+1 => num_LOs X n + 1
  | B.I::X, n+1 => num_LOs X n

lemma num_LOs_zero (X : List B) : num_LOs X 0 = 0 := by
  cases X
  · rfl
  · rfl

lemma num_LOs_le (X : List B) (i : Nat) : num_LOs X i ≤ i := by
  revert X
  induction i with
  | zero =>
    intro X
    rw [num_LOs_zero]
  | succ k ih =>
    intro X
    cases X with
    | nil => exact Nat.zero_le _
    | cons x X' =>
      cases x
      · change num_LOs X' k + 1 ≤ k + 1
        exact Nat.add_le_add_right (ih X') 1
      · change num_LOs X' k ≤ k + 1
        exact Nat.le_trans (ih X') (Nat.le_succ _)

lemma num_LOs_le_num_Os (X : List B) (i : Nat) : num_LOs X i ≤ num_Os X := by
  sorry

lemma num_LOs_of_ovrlen (X : List B) (i : Nat) (H : X.length ≤ i) : num_LOs X i = num_Os X := by
  sorry

lemma num_LOs_le_length (X : List B) (i : Nat) (H : i + 1 ≤ X.length) : num_LOs X i ≤ X.length - 1 := by
  sorry

lemma num_LOs_le_sDel (X : List B) (i : Nat) (H : i + 1 ≤ X.length) : num_LOs X i ≤ num_Os (sDel X i) := by
  sorry

lemma num_LOs_sIns (X : List B) (i : Nat) (b : B) (H : i + 1 ≤ X.length) : num_LOs (sIns X i b) i = num_LOs X i := by
  sorry

lemma num_LOs_sIns_one (X : List B) (i : Nat) (H : X.length ≤ i) : num_LOs (sIns X i B.I) i = num_Os X := by
  sorry

lemma head_of_num_LOs (X : List B) (x : B) (i : Nat) (H : num_LOs (x::X) (i + 1) = 0) : x = B.I := by
  sorry

lemma sIns_one_of_num_LOs (X : List B) (i j : Nat) (H : num_LOs X i = num_LOs X j) : sIns X i B.I = sIns X j B.I := by
  sorry

"""
    content = content[:lo_start] + new_lo_section + content[ri_start:]

with open("VTlean/NumOsNumIs.lean", "w") as f:
    f.write(content)
