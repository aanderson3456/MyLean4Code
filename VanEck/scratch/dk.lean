import InfiniteTwos

lemma d_k_bound (P k v : ℕ) (hP : P > 0) (hk : k < P) (hv1 : 1 ≤ v) (hvP : v ≤ P) :
  (k + 1 + P - v) / P ≤ 1 := by
  have h1 : k + 1 + P - v ≤ k + P := Nat.sub_le_of_le_add (by
    calc k + 1 + P = k + P + 1 := by omega
         _ ≤ k + P + v := Nat.add_le_add_left hv1 _
  )
  have h2 : k + P < 2 * P := by omega
  have h3 : k + 1 + P - v < 2 * P := Nat.lt_of_le_of_lt h1 h2
  exact Nat.div_le_of_le_mul (by omega)

lemma d_k_eq_one_iff (P k v : ℕ) (hP : P > 0) (hk : k < P) (hv1 : 1 ≤ v) (hvP : v ≤ P) :
  (k + 1 + P - v) / P = 1 ↔ v ≤ k + 1 := by
  constructor
  · intro h
    have h1 : P * 1 ≤ k + 1 + P - v := Nat.le_of_div_eq h
    omega
  · intro h
    have h1 : P ≤ k + 1 + P - v := by omega
    have h2 : k + 1 + P - v < 2 * P := by omega
    have h3 : (k + 1 + P - v) / P ≥ 1 := Nat.le_div_iff_mul_le hP |>.mpr (by omega)
    have h4 : (k + 1 + P - v) / P ≤ 1 := d_k_bound P k v hP hk hv1 hvP
    omega
