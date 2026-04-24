import VTlean.Optimal

open List.Vector B Finset List

lemma replicate_append_singleton {α : Type} (n : Nat) (a : α) :
  List.replicate n a ++ [a] = List.replicate (n + 1) a := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    change a :: (List.replicate n' a ++ [a]) = a :: List.replicate (n' + 1) a
    rw [ih]

lemma sDel_IOIO_O_test (n k : Nat) :
  List.sDel (mkIOIO n k) k = mkIO (n - 1) (k + 1) := by
  unfold mkIOIO mkIO
  have h_len : List.length (List.replicate k I) = k := by rw [List.length_replicate]
  have h_ge : List.length (List.replicate k I) ≤ k := by rw [h_len]
  have h_ne : O :: I :: List.replicate (n - k - 2) O ≠ [] := by intro h; contradiction
  have H_rw := List.sDel_append_of_ge (List.replicate k I) (O :: I :: List.replicate (n - k - 2) O) k h_ge h_ne
  rw [H_rw]
  have h_sub : k - List.length (List.replicate k I) = 0 := by rw [h_len, Nat.sub_self]
  rw [h_sub]
  have h_sDel_0 : List.sDel (O :: I :: List.replicate (n - k - 2) O) 0 = I :: List.replicate (n - k - 2) O := by
    rw [List.sDel_zero]
  rw [h_sDel_0]
  have h_assoc : List.replicate k I ++ I :: List.replicate (n - k - 2) O = (List.replicate k I ++ [I]) ++ List.replicate (n - k - 2) O := by
    change List.replicate k I ++ ([I] ++ List.replicate (n - k - 2) O) = _
    rw [List.append_assoc]
  rw [h_assoc]
  rw [replicate_append_singleton]
  have h_n_1 : n - 1 - (k + 1) = n - k - 2 := by
    have H1 : 1 + (k + 1) = k + 2 := by rw [Nat.add_comm 1 (k + 1)]; rfl
    rw [Nat.sub_sub, H1, ← Nat.sub_sub]
  rw [h_n_1]

lemma sDel_IOIO_I_test (n k : Nat) (Hk : k + 2 ≤ n) :
  List.sDel (mkIOIO n k) (k + 1) = mkIO (n - 1) k := by
  unfold mkIOIO mkIO
  have h_len : List.length (List.replicate k I) = k := by rw [List.length_replicate]
  have h_ge : List.length (List.replicate k I) ≤ k + 1 := by rw [h_len]; exact Nat.le_succ _
  have h_ne : O :: I :: List.replicate (n - k - 2) O ≠ [] := by intro h; contradiction
  have H_rw := List.sDel_append_of_ge (List.replicate k I) (O :: I :: List.replicate (n - k - 2) O) (k + 1) h_ge h_ne
  rw [H_rw]
  have h_sub : k + 1 - List.length (List.replicate k I) = 1 := by rw [h_len, Nat.add_sub_cancel_left]
  rw [h_sub]
  have h_sDel_1 : List.sDel (O :: I :: List.replicate (n - k - 2) O) 1 = O :: List.replicate (n - k - 2) O := by
    change List.sDel (O :: (I :: List.replicate (n - k - 2) O)) (0 + 1) = _
    rw [List.sDel_cons]
    · rw [List.sDel_zero]
    · intro h; contradiction
  rw [h_sDel_1]
  have h_replicate_O : O :: List.replicate (n - k - 2) O = List.replicate (n - 1 - k) O := by
    have h_eq : n - k - 2 + 1 = n - 1 - k := by
      have H2 : 2 ≤ n - k := Nat.le_sub_of_add_le (Nat.add_comm 2 k ▸ Hk)
      have H3 : n - k - 2 + 1 = n - k - 1 := by
        have H4 : n - k = n - k - 2 + 2 := (Nat.sub_add_cancel H2).symm
        rw [H4]
        change n - k - 2 + 1 = n - k - 2 + 1 + 1 - 1
        rw [Nat.add_sub_cancel]
      rw [H3]
      exact Nat.sub_right_comm n k 1
    have h_rep_succ : O :: List.replicate (n - k - 2) O = List.replicate (n - k - 2 + 1) O := rfl
    rw [h_rep_succ, h_eq]
  rw [h_replicate_O]
