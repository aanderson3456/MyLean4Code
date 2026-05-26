import VTlean.B
import VTlean.InsDel
import VTlean.DelCode
import VTlean.VTCode
import Mathlib

open B List.Vector Finset List

lemma moment_sIns {n : Nat} (X : List.Vector B n) {i : Nat} (b : B) :
  moment (sIns X i b) = moment X + match b with
    | B.O => num_RIs X i
    | B.I => num_LOs X i + wt X + 1 := by
  cases b
  · exact moment_sIns_zero X
  · have h := moment_sIns_one X (i:=i)
    dsimp
    omega

lemma mod_helper {A m : Nat} (hm : 0 < m) : (A + m - A % m) % m = 0 := by
  have h_div : A = m * (A / m) + A % m := (Nat.div_add_mod A m).symm
  nth_rewrite 1 [h_div]
  have h_rw : m * (A / m) + A % m + m - A % m = m * (A / m) + m := by omega
  rw [h_rw]
  have h_mul : m * (A / m) + m = m * (A / m + 1) := by ring
  rw [h_mul]
  exact Nat.mul_mod_right m _

lemma sub_mod_add_moment_helper {A a m : Nat} (hm : 0 < m) :
  (A + (a + (m - A % m) % m)) % m = a % m := by
  have h1 : (a + (m - A % m) % m) % m = (a + (m - A % m)) % m := by
    rw [Nat.add_mod, Nat.mod_mod, ←Nat.add_mod]
  have h2 : (A + (a + (m - A % m) % m)) % m = (A + (a + (m - A % m))) % m := by
    rw [Nat.add_mod, h1, ←Nat.add_mod]
  rw [h2]
  have h_lt : A % m < m := Nat.mod_lt A hm
  have h3 : A + (a + (m - A % m)) = a + (A + m - A % m) := by omega
  rw [h3, Nat.add_mod, mod_helper hm, Nat.add_zero, Nat.mod_mod]

lemma sub_mod_add_moment_eq_a_mod (m a : Nat) (hm : 0 < m) (X : List B) :
  (List.moment X + List.sub_mod m a X) % m = a % m := by
  unfold List.sub_mod
  cases Decidable.em (List.moment X < a) with
  | inl hlt =>
    rw [if_pos hlt]
    rw [Nat.add_mod_mod]
    rw [Nat.add_sub_of_le (Nat.le_of_lt hlt)]
  | inr hnlt =>
    rw [if_neg hnlt]
    have h_sub : List.moment X = List.moment X - a + a := by
      exact (Nat.sub_add_cancel (Nat.ge_of_not_lt hnlt)).symm
    nth_rewrite 1 [h_sub]
    rw [Nat.add_assoc]
    exact sub_mod_add_moment_helper hm

lemma sub_mod_lt (m a : Nat) (X : List B) (hm : 0 < m) : List.sub_mod m a X < m := by
  unfold List.sub_mod
  cases Decidable.em (List.moment X < a) with
  | inl hlt =>
    rw [if_pos hlt]
    exact Nat.mod_lt _ hm
  | inr hnlt =>
    rw [if_neg hnlt]
    exact Nat.mod_lt _ hm

lemma moment_decoding_alg (n a : Nat) (y : List.Vector B (n - 1)) (hn : 0 < n) :
  moment (Vector.decoding_alg n a y) % (n + 1) = a % (n + 1) := by
  unfold Vector.decoding_alg Vector.moment
  change List.moment (List.decoding_alg n a y.val) % (n + 1) = a % (n + 1)
  unfold List.decoding_alg
  cases Decidable.em (List.length y.val = n) with
  | inl hlen =>
    have h_len : List.length y.val = n - 1 := y.property
    omega
  | inr hnlen =>
    rw [if_neg hnlen]
    cases Decidable.em (List.sub_mod (n + 1) a y.val ≤ num_Is y.val) with
    | inl hle =>
      rw [if_pos hle]
      rw [List.moment_sIns_zero]
      rw [List.num_RIs_max_num_RIs y.val _ hle]
      apply sub_mod_add_moment_eq_a_mod (n + 1) a (by omega)
    | inr hnle =>
      rw [if_neg hnle]
      rw [List.moment_sIns_one]
      have h_bound : List.sub_mod (n + 1) a y.val - num_Is y.val - 1 ≤ num_Os y.val := by
        have h_sub_mod := sub_mod_lt (n + 1) a y.val (by omega)
        have h_num_Os : num_Os y.val = n - 1 - num_Is y.val := by
          have h1 : num_Os y.val + num_Is y.val = List.length y.val := List.num_Os_add_num_Is y.val
          have h2 : List.length y.val = n - 1 := y.property
          omega
        omega
      rw [List.num_LOs_min_num_LOs y.val _ h_bound]
      have h_eq : List.moment y.val + (List.sub_mod (n + 1) a y.val - num_Is y.val - 1) + num_Is y.val + 1 = List.moment y.val + List.sub_mod (n + 1) a y.val := by
        have h_gt : num_Is y.val < List.sub_mod (n + 1) a y.val := Nat.lt_of_not_ge hnle
        omega
      rw [h_eq]
      apply sub_mod_add_moment_eq_a_mod (n + 1) a (by omega)

lemma max_num_RIs_le_length (X : List B) (i : Nat) : List.max_num_RIs X i ≤ length X := by
  induction X generalizing i with
  | nil =>
    unfold List.max_num_RIs
    exact Nat.le_refl _
  | cons x xs ih =>
    unfold List.max_num_RIs
    have h_len : length (x :: xs) = length xs + 1 := rfl
    cases x
    · split
      · have h := ih i; omega
      · have h := ih i; omega
    · split
      · have h := ih i; omega
      · have h := ih i; omega

lemma min_num_LOs_le_length (X : List B) (i : Nat) : List.min_num_LOs X i ≤ length X := by
  induction X generalizing i with
  | nil =>
    unfold List.min_num_LOs
    exact Nat.zero_le _
  | cons x xs ih =>
    have h_len : length (x :: xs) = length xs + 1 := rfl
    cases x
    · cases i with
      | zero => exact Nat.zero_le _
      | succ n =>
        unfold List.min_num_LOs
        have h := ih n
        omega
    · cases i with
      | zero => exact Nat.zero_le _
      | succ n =>
        unfold List.min_num_LOs
        have h := ih (n + 1)
        omega

lemma decoding_alg_is_insertion (n a : Nat) (y : List.Vector B (n - 1)) (hn : 0 < n) :
  y ∈ dS (Vector.decoding_alg n a y) := by
  unfold Vector.decoding_alg
  rw [mem_dS]
  cases Decidable.em (List.length y.val = n) with
  | inl hlen =>
    have h_len : List.length y.val = n - 1 := y.property
    omega
  | inr hnlen =>
    cases Decidable.em (List.sub_mod (n + 1) a y.val ≤ num_Is y.val) with
    | inl hle =>
      use List.max_num_RIs y.val (List.sub_mod (n + 1) a y.val)
      constructor
      · have h_bound := max_num_RIs_le_length y.val (List.sub_mod (n + 1) a y.val)
        have h_len : List.length y.val = n - 1 := y.property
        omega
      · apply Subtype.ext
        change y.val = List.sDel (List.decoding_alg n a y.val) _
        unfold List.decoding_alg
        rw [if_neg hnlen, if_pos hle]
        exact (List.sDel_sIns_id _ _ _).symm
    | inr hnle =>
      use List.min_num_LOs y.val (List.sub_mod (n + 1) a y.val - num_Is y.val - 1)
      constructor
      · have h_bound := min_num_LOs_le_length y.val (List.sub_mod (n + 1) a y.val - num_Is y.val - 1)
        have h_len : List.length y.val = n - 1 := y.property
        omega
      · apply Subtype.ext
        change y.val = List.sDel (List.decoding_alg n a y.val) _
        unfold List.decoding_alg
        rw [if_neg hnlen, if_neg hnle]
        exact (List.sDel_sIns_id _ _ _).symm
