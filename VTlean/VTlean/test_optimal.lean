import VTlean.Optimal

open List.Vector B Finset List

lemma length_IOIO_test (n k : Nat) (Hk : k + 2 ≤ n) :
    List.length (mkIOIO n k) = n := by
  unfold mkIOIO
  rw [List.length_append, List.length_replicate, List.length_cons, List.length_cons, List.length_replicate]
  have h1 : n - k - 2 + 1 + 1 = n - k := by
    have H : n - k - 2 + 2 = n - k := Nat.sub_add_cancel (Nat.le_sub_of_add_le (Nat.add_comm 2 k ▸ Hk))
    exact H
  rw [h1]
  have h_k_le_n : k ≤ n := Nat.le_trans (Nat.le_add_right k 2) Hk
  exact Nat.add_sub_cancel' h_k_le_n

lemma num_Os_IOIO_test (n k : Nat) :
  List.num_Os (mkIOIO n k) = n - k - 2 + 1 := by
  unfold mkIOIO
  rw [List.num_Os_append, List.num_Os_replicate_I, Nat.zero_add]
  change List.num_Os (I :: List.replicate (n - k - 2) O) + 1 = _
  change List.num_Os (List.replicate (n - k - 2) O) + 1 = _
  rw [List.num_Os_replicate_O]

lemma num_Is_IOIO_test (n k : Nat) :
  List.num_Is (mkIOIO n k) = k + 1 := by
  unfold mkIOIO
  rw [List.num_Is_append, List.num_Is_replicate_I]
  change k + List.num_Is (I :: List.replicate (n - k - 2) O) = _
  change k + (List.num_Is (List.replicate (n - k - 2) O) + 1) = _
  rw [List.num_Is_replicate_O, Nat.zero_add]

lemma length_IOIO'_test (n k : Nat) (Hk : n ≤ k + 2) :
    List.length (mkIOIO n k) = k + 2 := by
  unfold mkIOIO
  rw [List.length_append, List.length_replicate, List.length_cons, List.length_cons, List.length_replicate]
  have h1 : n - k - 2 = 0 := by
    rw [Nat.sub_sub]
    exact Nat.sub_eq_zero_of_le Hk
  rw [h1]

lemma length_OI_test (n k : Nat) (Hnk : k ≤ n) :
  List.length (mkOI n k) = n := by
  unfold mkOI
  rw [List.length_append, List.length_replicate, List.length_replicate]
  exact Nat.add_sub_cancel' Hnk

lemma length_OI'_test (n k : Nat) :
  List.length (mkOI n k) = k + (n - k) := by
  unfold mkOI
  rw [List.length_append, List.length_replicate, List.length_replicate]

lemma num_Os_OI_test (n k : Nat) :
  List.num_Os (mkOI n k) = k := by
  unfold mkOI
  rw [List.num_Os_append, List.num_Os_replicate_O, List.num_Os_replicate_I, Nat.add_zero]

lemma num_Is_OI_test (n k : Nat) :
  List.num_Is (mkOI n k) = n - k := by
  unfold mkOI
  rw [List.num_Is_append, List.num_Is_replicate_O, List.num_Is_replicate_I, Nat.zero_add]

