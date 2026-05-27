import Mathlib
import VTlean.VTCode
import VTlean.NumOsNumIs
import VTlean.DelCode

open Nat Finset B List.Vector

def vector_to_subset (n : Nat) (X : List.Vector B n) : Finset (Fin (n + 1)) :=
  (Finset.univ).filter (fun (i : Fin (n + 1)) => i.val ≠ 0 ∧ X.val.getD (i.val - 1) B.O = B.I)

def subset_to_vector (n : Nat) (s : Finset (Fin (n + 1))) : List.Vector B n :=
  ⟨List.ofFn (fun (i : Fin n) => if Fin.mk (i.val + 1) (by omega) ∈ s then B.I else B.O), by simp⟩

lemma vector_to_subset_inj (n : Nat) (X1 X2 : List.Vector B n) 
  (h_eq : vector_to_subset n X1 = vector_to_subset n X2) : X1 = X2 := by
  apply Subtype.ext
  apply List.ext_get
  · rw [X1.property, X2.property]
  · intro i h1 h2
    have h_len1 : X1.val.length = n := X1.property
    have h_len2 : X2.val.length = n := X2.property
    have hi_fin : i < n := by omega
    have hi_fin_2 : i + 1 < n + 1 := by omega
    have h_mem1 : Fin.mk (i + 1) hi_fin_2 ∈ vector_to_subset n X1 ↔ Fin.mk (i + 1) hi_fin_2 ∈ vector_to_subset n X2 := by rw [h_eq]
    simp only [vector_to_subset, mem_filter, mem_univ, true_and] at h_mem1
    have h_not_zero : (Fin.mk (i + 1) hi_fin_2).val ≠ 0 := by omega
    have h_idx : (Fin.mk (i + 1) hi_fin_2).val - 1 = i := by omega
    have h_mem1_simplified : (X1.val.getD i B.O = B.I) ↔ (X2.val.getD i B.O = B.I) := by
      have h1_s := h_mem1
      have hnz : (i + 1) ≠ 0 := by omega
      change (i + 1 ≠ 0 ∧ X1.val.getD (i + 1 - 1) B.O = B.I) ↔ (i + 1 ≠ 0 ∧ X2.val.getD (i + 1 - 1) B.O = B.I) at h1_s
      have h1_s2 : (True ∧ X1.val.getD i B.O = B.I) ↔ (True ∧ X2.val.getD i B.O = B.I) := by
        have h1_s3 : i + 1 - 1 = i := by omega
        rw [h1_s3] at h1_s
        have h_true_1 : i + 1 ≠ 0 ↔ True := iff_true_intro hnz
        rw [h_true_1] at h1_s
        exact h1_s
      simp only [true_and] at h1_s2
      exact h1_s2
    have h_get1 : X1.val.getD i B.O = X1.val.get ⟨i, h1⟩ := List.getD_eq_getElem _ _ _
    have h_get2 : X2.val.getD i B.O = X2.val.get ⟨i, h2⟩ := List.getD_eq_getElem _ _ _
    rw [h_get1, h_get2] at h_mem1_simplified
    cases h_X1_i : X1.val.get ⟨i, h1⟩
    · cases h_X2_i : X2.val.get ⟨i, h2⟩
      · rfl
      · rw [h_X1_i, h_X2_i] at h_mem1_simplified
        simp at h_mem1_simplified
    · cases h_X2_i : X2.val.get ⟨i, h2⟩
      · rw [h_X1_i, h_X2_i] at h_mem1_simplified
        simp at h_mem1_simplified
      · rfl

