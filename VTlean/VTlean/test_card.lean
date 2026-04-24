import Mathlib
import VTlean.DelCode

open List.Vector B

variable {n : Nat}

lemma length_dS_le {α : Type} [DecidableEq α] (X : List.Vector α n) (k : Nat) : (dS_le X k).length = k + 1 := by {
  induction k with
  | zero => rfl
  | succ k ih => exact congrArg Nat.succ ih
}

lemma card_dS (x : List.Vector B n) : card (dS x) ≤ n - 1 + 1 := by {
  unfold dS dS_list
  have h1 : (List.toFinset (dS_le x (n - 1))).card ≤ (dS_le x (n - 1)).length := List.toFinset_card_le _
  have h2 : (dS_le x (n - 1)).length = n - 1 + 1 := length_dS_le x (n - 1)
  rw [h2] at h1
  exact h1
}

lemma mul_card_dS_wt_le_eq_test
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) (w r : Nat) :
  mul_card_dS_wt_le C w r = card (union_dS_wt (Cwr_le C w r) w) :=
by {
  induction r with
  | zero =>
    rw [mul_card_dS_wt_le_zero]
    rw [card_union_dS_wt_Cwr_le_zero C]
  | succ r ihr =>
    unfold mul_card_dS_wt_le
    rw [mul_card_dS_wt_eq _ HC, ihr]
    rw [Cwr_le_succ, union_dS_wt_union]
    have h_disj : Disjoint (union_dS_wt (Cwr_le C w r) w) (union_dS_wt (Cwr C w (r + 1)) w) := by {
      rw [Finset.disjoint_iff_inter_eq_empty]
      rw [← Finset.subset_empty]
      apply Finset.Subset.trans
      · apply Finset.inter_subset_inter
        · exact union_dS_wt_subset _ _
        · exact union_dS_wt_subset _ _
      · have h_inter := union_dS_inter_of_DelCode HC (Cwr_le_subset C w r) (Cwr_subset C w (r + 1)) (Cwr_le_inter_eq C w r)
        rw [h_inter]
        exact Finset.Subset.refl _
    }
    rw [Finset.card_union_of_disjoint h_disj]
    rw [Nat.add_comm]
}

lemma card_Cwr_le_add_ge_test (C : Finset (List.Vector B n)) (w r : Nat) :
  card (Cwr_le C w r) + card (Cwr_ge C w (r + 1)) = card C :=
by {
  have h := Finset.card_union_of_disjoint (by {
    rw [Finset.disjoint_iff_inter_eq_empty]
    exact Cwr_le_inter_ge C w r
  })
  rw [Cwr_le_union_ge] at h
  exact h.symm
}
