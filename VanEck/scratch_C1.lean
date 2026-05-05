import Mathlib
import VanEck
import ImpossiblePatterns

open Finset

lemma C_eq_1_impossible (n_1 n_2 K P : ℕ) (h_P_pos2 : P ≥ 1) 
    (h_K_large : K ≥ P + 3)
    (h_P_def : P = n_2 - n_1)
    (h_n1_lt : n_1 < n_2)
    (v_fn : Fin P → ℕ)
    (hv_fn_def : ∀ k : Fin P, v_fn k = vanEckNthTerm (n_2 + k.val + 1))
    (hv1 : ∀ k, 1 ≤ v_fn k) (h_sum : ∑ k : Fin P, v_fn k = P) 
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k)) : False := by {
  
  -- v k - 1 >= 0
  have h_sub_sum : ∑ k : Fin P, (v_fn k - 1) = 0 := by {
    have h1 : ∑ k : Fin P, (v_fn k - 1) + ∑ k : Fin P, 1 = ∑ k : Fin P, v_fn k := by {
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      exact Nat.sub_add_cancel (hv1 x)
    }
    have h2 : ∑ k : Fin P, 1 = P := by {
      have hz : ∑ k : Fin P, 1 = (Finset.card (Finset.univ : Finset (Fin P))) * 1 := Finset.sum_const 1
      have hc : Finset.card (Finset.univ : Finset (Fin P)) = P := Fintype.card_fin P
      omega
    }
    omega
  }

  have h_all_zero : ∀ k : Fin P, v_fn k - 1 = 0 := by {
    intro k
    -- Since sum of Nat is 0, each element is 0
    have hs := Finset.sum_eq_zero_iff_of_nonneg (fun x _ => Nat.zero_le (v_fn x - 1))
    have hs2 := hs.mp h_sub_sum
    exact hs2 k (Finset.mem_univ k)
  }

  have h_v_all_1 : ∀ k : Fin P, v_fn k = 1 := by {
    intro k
    have h1 := h_all_zero k
    have h2 := hv1 k
    omega
  }

  have h_v0_1 : vanEckNthTerm (n_2 + 1) = 1 := by {
    have h0 := h_v_all_1 ⟨0, h_P_pos2⟩
    have hdef := hv_fn_def ⟨0, h_P_pos2⟩
    omega
  }

  have h_v1_1 : vanEckNthTerm (n_2 + 2) = 1 := by {
    by_cases hp_eq_1 : P = 1
    · have h_n2_eq : n_2 = n_1 + 1 := by omega
      have h_per_2 : vanEckNthTerm (n_1 + 2) = vanEckNthTerm (n_2 + 2) := h_per 2 (by omega)
      have h_n1_2 : n_1 + 2 = n_2 + 1 := by omega
      rw [h_n1_2] at h_per_2
      rw [← h_per_2]
      exact h_v0_1
    · have h_p_ge_2 : P ≥ 2 := by omega
      have h_v1 := h_v_all_1 ⟨1, h_p_ge_2⟩
      have hdef := hv_fn_def ⟨1, h_p_ge_2⟩
      omega
  }

  have h_no_cons := vanEck_no_consecutive_ones (n_2 + 1)
  have h_cons : vanEckNthTerm (n_2 + 1) = 1 ∧ vanEckNthTerm (n_2 + 1 + 1) = 1 := by {
    constructor
    · exact h_v0_1
    · exact h_v1_1
  }
  exact h_no_cons h_cons
}
