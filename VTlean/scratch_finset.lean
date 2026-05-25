import VTlean.B
import VTlean.InsDel
import VTlean.NumOsNumIs
import Mathlib.Data.Finset.Basic

open Finset B.Finset Vector

variable {n : Nat}

lemma ne_of_wt_lt {X Y : List.Vector B n} (H : wt X < wt Y) : X ≠ Y := by
  intro h
  rw [h] at H
  omega

lemma ne_of_wt_gt {X Y : List.Vector B n} (H : wt Y < wt X) : X ≠ Y := by
  intro h
  rw [h] at H
  omega

lemma wt_repO : wt (List.Vector.replicate n B.O) = 0 := by
  exact List.num_Is_repO n

lemma wt_repI : wt (List.Vector.replicate n B.I) = n := by
  exact List.num_Is_repI n

lemma wt_le_length (X : List.Vector B n) : wt X ≤ n := by
  have h := List.num_Is_le_length X.val
  have hX_len : X.val.length = n := X.2
  rw [hX_len] at h
  exact h

lemma not_mem_filter_Icc_wt_of_lt 
  (C : Finset (List.Vector B n)) (a b : Nat) (X : List.Vector B n) (H : wt X < a) :
  X ∉ filter (Icc_wt (n:=n) a b) C := by
  intro h
  rw [mem_filter] at h
  have h2 : a ≤ wt X := h.right.left
  omega

lemma not_mem_filter_Icc_wt_of_gt 
  (C : Finset (List.Vector B n)) (a b : Nat) (X : List.Vector B n) (H : b < wt X) :
  X ∉ filter (Icc_wt (n:=n) a b) C := by
  intro h
  rw [mem_filter] at h
  have h2 : wt X ≤ b := h.right.right
  omega

lemma div_Iic_Icc_Ici (a b : Nat) (C : Finset (List.Vector B n)) :
  filter (Iic_wt (n:=n) a) C ∪ filter (Icc_wt (n:=n) (a + 1) (b - 1)) C ∪ filter (Ici_wt (n:=n) b) C = C := by
  ext x
  apply Iff.intro
  · intro hx
    repeat rw [mem_union] at hx
    cases hx with
    | inl hx_left =>
      cases hx_left with
      | inl hx1 =>
        rw [mem_filter] at hx1
        exact hx1.left
      | inr hx2 =>
        rw [mem_filter] at hx2
        exact hx2.left
    | inr hx3 =>
      rw [mem_filter] at hx3
      exact hx3.left
  · intro hx
    repeat rw [mem_union]
    by_cases hle : wt x ≤ a
    · apply Or.inl
      apply Or.inl
      rw [mem_filter]
      exact ⟨hx, hle⟩
    · by_cases hle' : wt x ≤ b - 1
      · apply Or.inl
        apply Or.inr
        rw [mem_filter]
        have h1 : a + 1 ≤ wt x := by omega
        exact ⟨hx, ⟨h1, hle'⟩⟩
      · apply Or.inr
        rw [mem_filter]
        have h1 : b ≤ wt x := by omega
        exact ⟨hx, h1⟩

lemma filter_wt_eq_inter_of_ne
  (C : Finset (List.Vector B n)) (a b : Nat) (H : a ≠ b) :
  filter (fun x => wt x = a) C ∩ filter (fun x => wt x = b) C = ∅ := by
  ext x
  rw [mem_inter]
  apply Iff.intro
  · intro hx
    have h1 : wt x = a := by
      have h' := hx.left
      rw [mem_filter] at h'
      exact h'.right
    have h2 : wt x = b := by
      have h' := hx.right
      rw [mem_filter] at h'
      exact h'.right
    omega
  · intro hx
    exfalso
    simp at hx

lemma filter_wt_eq_inter_Icc_of_lt
  (C : Finset (List.Vector B n)) (a b c : Nat) (H : a + 1 ≤ b) :
  filter (fun x => wt x = a) C ∩ filter (Icc_wt (n:=n) b c) C = ∅ := by
  ext x
  rw [mem_inter]
  apply Iff.intro
  · intro hx
    have h1 : wt x = a := by
      have h' := hx.left
      rw [mem_filter] at h'
      exact h'.right
    have h2 : b ≤ wt x := by
      have h' := hx.right
      rw [mem_filter] at h'
      exact h'.right.left
    omega
  · intro hx
    exfalso
    simp at hx

lemma filter_wt_eq_inter_Icc_of_gt
  (C : Finset (List.Vector B n)) (a b c : Nat) (H : c + 1 ≤ a) :
  filter (fun x => wt x = a) C ∩ filter (Icc_wt (n:=n) b c) C = ∅ := by
  ext x
  rw [mem_inter]
  apply Iff.intro
  · intro hx
    have h1 : wt x = a := by
      have h' := hx.left
      rw [mem_filter] at h'
      exact h'.right
    have h2 : wt x ≤ c := by
      have h' := hx.right
      rw [mem_filter] at h'
      exact h'.right.right
    omega
  · intro hx
    exfalso
    simp at hx

lemma flip_filter_subset_swap (C : Finset (List.Vector B n)) (a b : Nat) : 
  flipCode (filter (Icc_wt (n:=n) a b) C) ⊆ filter (Icc_wt (n:=n) (n - b) (n - a)) (flipCode C) := by
  intro x hx
  rw [mem_flipCode] at hx
  rcases hx with ⟨y, hy, hxy⟩
  rw [mem_filter] at hy
  rw [mem_filter]
  apply And.intro
  · rw [mem_flipCode]
    exists y
    exact ⟨hy.left, hxy⟩
  · unfold Icc_wt
    have hy_icc := hy.right
    unfold Icc_wt at hy_icc
    have hy1 := hy_icc.left
    have hy2 := hy_icc.right
    have h_flip : wt x = n - wt y := by
      have h : x = B.Vector.flip y := by exact hxy.symm
      rw [h, wt_flip y]
    have h_wt_y : wt y ≤ n := wt_le_length y
    omega

lemma filter_flip_subset_swap (C : Finset (List.Vector B n)) (a b : Nat) : 
  filter (Icc_wt (n:=n) a b) (flipCode C) ⊆ flipCode (filter (Icc_wt (n:=n) (n - b) (n - a)) C) := by
  intro x hx
  rw [mem_filter] at hx
  have hx1 := hx.left
  have hx2 := hx.right
  rw [mem_flipCode] at hx1
  rcases hx1 with ⟨y, hy, hxy⟩
  rw [mem_flipCode]
  exists y
  apply And.intro
  · rw [mem_filter]
    apply And.intro hy
    unfold Icc_wt
    have h_flip : wt x = n - wt y := by
      have h : x = B.Vector.flip y := by exact hxy.symm
      rw [h, wt_flip y]
    have h_wt_y : wt y ≤ n := wt_le_length y
    unfold Icc_wt at hx2
    omega
  · exact hxy

lemma flip_filter_swap (C : Finset (List.Vector B n)) (a b : Nat) (Ha : a ≤ n) (Hb : b ≤ n) : 
  flipCode (filter (Icc_wt (n:=n) a b) C) = filter (Icc_wt (n:=n) (n - b) (n - a)) (flipCode C) := by
  ext x
  apply Iff.intro
  · intro h
    rw [mem_flipCode] at h
    rcases h with ⟨y, hy, hxy⟩
    rw [mem_filter] at hy
    rw [mem_filter]
    apply And.intro
    · rw [mem_flipCode]
      exists y
      exact ⟨hy.left, hxy⟩
    · unfold Icc_wt
      have hy2 := hy.right
      unfold Icc_wt at hy2
      have h_flip : wt x = n - wt y := by
        have h_symm : x = B.Vector.flip y := by exact hxy.symm
        rw [h_symm, wt_flip y]
      have h_wt_y : wt y ≤ n := wt_le_length y
      omega
  · intro h
    rw [mem_filter] at h
    have h_left := h.left
    have h_wt := h.right
    rw [mem_flipCode] at h_left
    rcases h_left with ⟨y, hy, hxy⟩
    rw [mem_flipCode]
    exists y
    apply And.intro
    · rw [mem_filter]
      apply And.intro hy
      unfold Icc_wt at h_wt
      unfold Icc_wt
      have h_flip : wt x = n - wt y := by
        have h_symm : x = B.Vector.flip y := by exact hxy.symm
        rw [h_symm, wt_flip y]
      have h_wt_y : wt y ≤ n := wt_le_length y
      omega
    · exact hxy

lemma filter_flip_swap (C : Finset (List.Vector B n)) (a b : Nat) (Ha : a ≤ n) (Hb : b ≤ n) : 
  filter (Icc_wt (n:=n) a b) (flipCode C) = flipCode (filter (Icc_wt (n:=n) (n - b) (n - a)) C) := by
  ext x
  apply Iff.intro
  · intro h
    rw [mem_filter] at h
    have h_left := h.left
    have h_wt := h.right
    rw [mem_flipCode] at h_left
    rcases h_left with ⟨y, hy, hxy⟩
    rw [mem_flipCode]
    exists y
    apply And.intro
    · rw [mem_filter]
      apply And.intro hy
      unfold Icc_wt at h_wt
      unfold Icc_wt
      have h_flip : wt x = n - wt y := by
        have h_symm : x = B.Vector.flip y := by exact hxy.symm
        rw [h_symm, wt_flip y]
      have h_wt_y : wt y ≤ n := wt_le_length y
      omega
    · exact hxy
  · intro h
    rw [mem_flipCode] at h
    rcases h with ⟨y, hy, hxy⟩
    rw [mem_filter] at hy
    rw [mem_filter]
    apply And.intro
    · rw [mem_flipCode]
      exists y
      exact ⟨hy.left, hxy⟩
    · unfold Icc_wt
      have hy2 := hy.right
      unfold Icc_wt at hy2
      have h_flip : wt x = n - wt y := by
        have h_symm : x = B.Vector.flip y := by exact hxy.symm
        rw [h_symm, wt_flip y]
      have h_wt_y : wt y ≤ n := wt_le_length y
      omega
