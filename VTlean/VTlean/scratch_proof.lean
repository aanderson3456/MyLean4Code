import Mathlib
import VTlean.VTCode
import VTlean.Cuculiere
import VTlean.NumOsNumIs

open Nat Finset B

def vector_to_subset (n : Nat) (X : List.Vector B n) : Finset (Fin (n + 1)) :=
  (Finset.univ).filter (fun (i : Fin (n + 1)) => i.val ≠ 0 ∧ X.val.getD (i.val - 1) B.O = B.I)

def subset_to_vector (n : Nat) (s : Finset (Fin (n + 1))) : List.Vector B n :=
  ⟨List.ofFn (fun (i : Fin n) => if Fin.mk (i.val + 1) (by omega) ∈ s then B.I else B.O), by simp⟩

lemma vector_to_subset_not_zero (n : Nat) (X : List.Vector B n) :
  ∀ i ∈ vector_to_subset n X, i.val ≠ 0 := by {
  intro i hi
  unfold vector_to_subset at hi
  simp only [mem_filter, mem_univ, true_and] at hi
  exact hi.left
}

lemma vector_to_subset_card (n : Nat) (X : List.Vector B n) :
  (vector_to_subset n X).card = Vector.wt X := by {
  sorry
}

lemma vector_to_subset_sum (n : Nat) (X : List.Vector B n) :
  (vector_to_subset n X).sum (fun i => i.val) = moment X := by {
  sorry
}

lemma vector_to_subset_mem_T_set (n a k : Nat) (X : List.Vector B n) (h_vt : X ∈ VTCode n a) (h_wt : Vector.wt X = k) :
  vector_to_subset n X ∈ T_set n a k := by {
  unfold T_set
  rw [mem_filter, mem_powersetLen]
  constructor
  · constructor
    · intro i hi
      rw [mem_erase, mem_univ, and_true]
      have h_nz := vector_to_subset_not_zero n X i hi
      intro h_eq_0
      have h_val : i.val = 0 := by {
        have h_eq_0_val := congrArg Fin.val h_eq_0
        exact h_eq_0_val
      }
      contradiction
    · rw [vector_to_subset_card, h_wt]
  · rw [vector_to_subset_sum]
    rw [VTCode, mem_filter] at h_vt
    exact h_vt.right
}
