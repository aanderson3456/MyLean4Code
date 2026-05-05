import Mathlib
import VanEck.VanEck

lemma local_periodicity_impossible_P_le (n_1 n_2 K : ℕ) 
    (hn1_lt_n2 : n_1 < n_2)
    (h_K_large : K ≥ n_2 - n_1 + 3)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k))
    (k : ℕ) (hk1 : 1 ≤ k) (hkP : k ≤ n_2 - n_1) :
    vanEckNthTerm (n_2 + k) ≤ n_2 - n_1 := by {
  let P := n_2 - n_1
  have h_P_pos : P ≥ 1 := Nat.succ_le_of_lt hn1_lt_n2
  have h_eq : vanEckNthTerm (n_2 + k - 1) = vanEckNthTerm (n_2 + k - 1 - P) := by {
    have h1 : n_2 + k - 1 - P = n_1 + k - 1 := by omega
    rw [h1]
    exact (h_per (k - 1) (by omega)).symm
  }
  
  have hm := vanEck_term_is_matchSearch (n_2 + k) (by omega)
  have hsub : n_2 + k - 1 + 1 = n_2 + k := by omega
  rw [← hsub] at hm
  
  have hd : listNth (vanEck (n_2 + k - 1)) (n_2 + k - 1) = vanEckNthTerm (n_2 + k - 1) := rfl
  have hm2 : listNth (vanEck (n_2 + k - 1)) (n_2 + k - 1 - P) = vanEckNthTerm (n_2 + k - 1 - P) := by {
    exact VanEck_deterministic (n_2 + k - 1) (n_2 + k - 1 - P) (by omega)
  }
  
  have h_match : listNth (vanEck (n_2 + k - 1)) (n_2 + k - 1) = listNth (vanEck (n_2 + k - 1)) (n_2 + k - 1 - P) := by {
    rw [hd, hm2]
    exact h_eq
  }
  
  have h_len : (vanEck (n_2 + k - 1)).length - 1 = n_2 + k - 1 := by {
    have hl := vanEckLength (n_2 + k - 1)
    omega
  }
  rw [← h_len] at h_match
  
  by_cases h_z : vanEckNthTerm (n_2 + k - 1) = 0
  · sorry
  · have h_neq : matchSearch (vanEck (n_2 + k - 1)) (n_2 + k - 1) ≠ 0 := by {
      intro hc
      have h_match_rule := matchSearch_matches (vanEck (n_2 + k - 1)) (n_2 + k - 1) hc
      rw [h_len] at h_match_rule
      rw [hc] at h_match_rule
      have hz2 : listNth (vanEck (n_2 + k - 1)) 0 = 0 := list_nth_VanEck_zero_eq_zero _
      rw [hz2] at h_match_rule
      rw [hd] at h_match_rule
      exact h_z h_match_rule
    }
    have h_first := matchSearch_first (vanEck (n_2 + k - 1)) (n_2 + k - 1) (n_2 + k - 1 - P) h_neq (by omega) h_match
    rw [h_len] at h_first
    rw [← hm] at h_first
    omega
}
