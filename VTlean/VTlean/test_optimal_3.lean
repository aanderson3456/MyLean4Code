import VTlean.Optimal

open List.Vector B Finset List

lemma drop_one_replicate_pos {α : Type} (k : Nat) (hk : 0 < k) (a : α) (L : List α) :
  List.drop 1 (List.replicate k a ++ L) = List.replicate (k - 1) a ++ L := by
  cases k with
  | zero => contradiction
  | succ k' =>
    change List.drop 1 (a :: (List.replicate k' a ++ L)) = _
    rw [List.drop]
    rfl

lemma head_replicate_pos {α : Type} (k : Nat) (hk : 0 < k) (a : α) (L : List α) :
  List.head? (List.replicate k a ++ L) = some a := by
  cases k with
  | zero => contradiction
  | succ k' => rfl

lemma head_replicate_pos_only {α : Type} (k : Nat) (hk : 0 < k) (a : α) :
  List.head? (List.replicate k a) = some a := by
  cases k with
  | zero => contradiction
  | succ k' => rfl

lemma drop_replicate_append {α : Type} (k : Nat) (a : α) (L : List α) :
  List.drop k (List.replicate k a ++ L) = L := by
  induction k with
  | zero => rfl
  | succ k' ih => exact ih

lemma OI_ne_IOIO_test (n k₁ k₂ : Nat) (H : 3 ≤ n) :
  mkOI n k₁ ≠ mkIOIO n k₂ := by
  intro h
  by_cases hk1 : k₁ = 0
  · subst hk1
    have h_drop : List.drop k₂ (mkOI n 0) = List.drop k₂ (mkIOIO n k₂) := by rw [h]
    unfold mkOI mkIOIO at h_drop
    rw [drop_replicate_append] at h_drop
    rw [List.drop_replicate] at h_drop
    have h_head : List.head? (List.replicate (n - k₂) I) = List.head? (O :: I :: List.replicate (n - k₂ - 2) O) := by rw [h_drop]
    by_cases h_sub : n - k₂ = 0
    · rw [h_sub] at h_head
      change none = some O at h_head
      contradiction
    · have h_sub_pos : 0 < n - k₂ := Nat.pos_of_ne_zero h_sub
      rw [head_replicate_pos_only (n - k₂) h_sub_pos I] at h_head
      change some I = some O at h_head
      contradiction
  · have hk1_pos : 0 < k₁ := Nat.pos_of_ne_zero hk1
    by_cases hk2 : k₂ = 0
    · subst hk2
      have h_drop : List.drop 1 (mkOI n k₁) = List.drop 1 (mkIOIO n 0) := by rw [h]
      unfold mkOI mkIOIO at h_drop
      rw [drop_one_replicate_pos k₁ hk1_pos O (List.replicate (n - k₁) I)] at h_drop
      change List.replicate (k₁ - 1) O ++ List.replicate (n - k₁) I = I :: List.replicate (n - 2) O at h_drop
      by_cases hk1_eq_1 : k₁ - 1 = 0
      · have h_os : List.num_Os (List.replicate (k₁ - 1) O ++ List.replicate (n - k₁) I) =
                    List.num_Os (I :: List.replicate (n - 2) O) := by rw [h_drop]
        rw [hk1_eq_1] at h_os
        change List.num_Os (List.replicate (n - k₁) I) = List.num_Os (List.replicate (n - 2) O) at h_os
        rw [List.num_Os_replicate_I, List.num_Os_replicate_O] at h_os
        have h_n_2 : n - 2 = 0 := h_os.symm
        have h_n_le_2 : n ≤ 2 := Nat.le_of_sub_eq_zero h_n_2
        have h_contra : 3 ≤ 2 := Nat.le_trans H h_n_le_2
        contradiction
      · have hk1_sub_pos : 0 < k₁ - 1 := Nat.pos_of_ne_zero hk1_eq_1
        have h_head : List.head? (List.replicate (k₁ - 1) O ++ List.replicate (n - k₁) I) =
                      List.head? (I :: List.replicate (n - 2) O) := by rw [h_drop]
        rw [head_replicate_pos (k₁ - 1) hk1_sub_pos O (List.replicate (n - k₁) I)] at h_head
        change some O = some I at h_head
        contradiction
    · have hk2_pos : 0 < k₂ := Nat.pos_of_ne_zero hk2
      have h_head : List.head? (mkOI n k₁) = List.head? (mkIOIO n k₂) := by rw [h]
      unfold mkOI mkIOIO at h_head
      rw [head_replicate_pos k₁ hk1_pos O (List.replicate (n - k₁) I)] at h_head
      rw [head_replicate_pos k₂ hk2_pos I (O :: I :: List.replicate (n - k₂ - 2) O)] at h_head
      contradiction

lemma IO_ne_OIOI_test (n k₁ k₂ : Nat) (H : 3 ≤ n) :
  mkIO n k₁ ≠ mkOIOI n k₂ := by
  intro h
  by_cases hk1 : k₁ = 0
  · subst hk1
    -- mkIO n 0 = replicate n O
    have h_drop : List.drop k₂ (mkIO n 0) = List.drop k₂ (mkOIOI n k₂) := by rw [h]
    unfold mkIO mkOIOI at h_drop
    rw [drop_replicate_append] at h_drop
    rw [List.drop_replicate] at h_drop
    have h_head : List.head? (List.replicate (n - k₂) O) = List.head? (I :: O :: List.replicate (n - k₂ - 2) I) := by rw [h_drop]
    by_cases h_sub : n - k₂ = 0
    · rw [h_sub] at h_head
      change none = some I at h_head
      contradiction
    · have h_sub_pos : 0 < n - k₂ := Nat.pos_of_ne_zero h_sub
      rw [head_replicate_pos_only (n - k₂) h_sub_pos O] at h_head
      change some O = some I at h_head
      contradiction
  · have hk1_pos : 0 < k₁ := Nat.pos_of_ne_zero hk1
    by_cases hk2 : k₂ = 0
    · subst hk2
      have h_drop : List.drop 1 (mkIO n k₁) = List.drop 1 (mkOIOI n 0) := by rw [h]
      unfold mkIO mkOIOI at h_drop
      rw [drop_one_replicate_pos k₁ hk1_pos I (List.replicate (n - k₁) O)] at h_drop
      change List.replicate (k₁ - 1) I ++ List.replicate (n - k₁) O = O :: List.replicate (n - 2) I at h_drop
      by_cases hk1_eq_1 : k₁ - 1 = 0
      · have h_is : List.num_Is (List.replicate (k₁ - 1) I ++ List.replicate (n - k₁) O) =
                    List.num_Is (O :: List.replicate (n - 2) I) := by rw [h_drop]
        rw [hk1_eq_1] at h_is
        change List.num_Is (List.replicate (n - k₁) O) = List.num_Is (List.replicate (n - 2) I) at h_is
        rw [List.num_Is_replicate_O, List.num_Is_replicate_I] at h_is
        -- 0 = n - 2
        have h_n_2 : n - 2 = 0 := h_is.symm
        have h_n_le_2 : n ≤ 2 := Nat.le_of_sub_eq_zero h_n_2
        have h_contra : 3 ≤ 2 := Nat.le_trans H h_n_le_2
        contradiction
      · have hk1_sub_pos : 0 < k₁ - 1 := Nat.pos_of_ne_zero hk1_eq_1
        have h_head : List.head? (List.replicate (k₁ - 1) I ++ List.replicate (n - k₁) O) =
                      List.head? (O :: List.replicate (n - 2) I) := by rw [h_drop]
        rw [head_replicate_pos (k₁ - 1) hk1_sub_pos I (List.replicate (n - k₁) O)] at h_head
        change some I = some O at h_head
        contradiction
    · have hk2_pos : 0 < k₂ := Nat.pos_of_ne_zero hk2
      have h_head : List.head? (mkIO n k₁) = List.head? (mkOIOI n k₂) := by rw [h]
      unfold mkIO mkOIOI at h_head
      rw [head_replicate_pos k₁ hk1_pos I (List.replicate (n - k₁) O)] at h_head
      rw [head_replicate_pos k₂ hk2_pos O (I :: O :: List.replicate (n - k₂ - 2) I)] at h_head
      contradiction
