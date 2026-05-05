import Mathlib
import VanEck
import ImpossiblePatterns

-- Just using the lemma we defined in InfiniteTwos.lean
axiom mod_eq_cases (A B P : ℕ) (hA : A < 2 * P) (hB : B < 2 * P) (hc : A % P = B % P) :
    A = B ∨ A + P = B ∨ B + P = A

lemma f_inj (n_1 n_2 P K : ℕ) (hn1_lt_n2 : n_1 < n_2) (h_P : P = n_2 - n_1)
    (h_no_zero : ∀ k, 1 ≤ k → k ≤ K → vanEckNthTerm (n_2 + k) ≠ 0)
    (h_val_le_P : ∀ k, 1 ≤ k → k ≤ K → vanEckNthTerm (n_2 + k) ≤ P)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k))
    (h_P_pos : P ≥ 1) (h_PK : P ≤ K) :
    ∀ i j, 1 ≤ i → i ≤ P → 1 ≤ j → j ≤ P → i < j →
      (i + P - vanEckNthTerm (n_2 + i)) % P ≠ (j + P - vanEckNthTerm (n_2 + j)) % P := by {
  intro i j hi1 hiP hj1 hjP hij hc
  
  have hiK : i ≤ K := Nat.le_trans hiP h_PK
  have hjK : j ≤ K := Nat.le_trans hjP h_PK
  
  have h_vi_le := h_val_le_P i hi1 hiK
  have h_vj_le := h_val_le_P j hj1 hjK
  have h_vi_pos : vanEckNthTerm (n_2 + i) > 0 := Nat.pos_of_ne_zero (h_no_zero i hi1 hiK)
  have h_vj_pos : vanEckNthTerm (n_2 + j) > 0 := Nat.pos_of_ne_zero (h_no_zero j hj1 hjK)
  
  let A := i + P - vanEckNthTerm (n_2 + i)
  let B := j + P - vanEckNthTerm (n_2 + j)
  
  have hA_lt : A < 2 * P := by {
    change i + P - vanEckNthTerm (n_2 + i) < 2 * P
    have h1 : i + P < 2 * P + 1 := by omega
    omega
  }
  have hB_lt : B < 2 * P := by {
    change j + P - vanEckNthTerm (n_2 + j) < 2 * P
    have h1 : j + P < 2 * P + 1 := by omega
    omega
  }
  
  have h_cases := mod_eq_cases A B P hA_lt hB_lt hc
  
  rcases h_cases with h1 | h2 | h3
  · -- Case A = B
    have heq : n_2 + i - vanEckNthTerm (n_2 + i) = n_2 + j - vanEckNthTerm (n_2 + j) := by {
      change i + P - vanEckNthTerm (n_2 + i) = j + P - vanEckNthTerm (n_2 + j) at h1
      omega
    }
    have h_unique := vanEck_idx_sub_val_unique (n_2 + i) (n_2 + j) h_vi_pos (by omega)
    exact h_unique heq
  · -- Case A + P = B
    have heq : n_2 + i - vanEckNthTerm (n_2 + i) = n_1 + j - vanEckNthTerm (n_1 + j) := by {
      change i + P - vanEckNthTerm (n_2 + i) + P = j + P - vanEckNthTerm (n_2 + j) at h2
      have h_vj_eq : vanEckNthTerm (n_1 + j) = vanEckNthTerm (n_2 + j) := h_per j hjK
      omega
    }
    have h_n1j_pos : vanEckNthTerm (n_1 + j) > 0 := by {
      have h_vj_eq : vanEckNthTerm (n_1 + j) = vanEckNthTerm (n_2 + j) := h_per j hjK
      rw [h_vj_eq]
      exact h_vj_pos
    }
    have h_lt : n_1 + j < n_2 + i := by omega
    have h_unique := vanEck_idx_sub_val_unique (n_1 + j) (n_2 + i) h_n1j_pos h_lt
    exact h_unique heq.symm
  · -- Case B + P = A
    change j + P - vanEckNthTerm (n_2 + j) + P = i + P - vanEckNthTerm (n_2 + i) at h3
    omega
}
