import Mathlib
import VanEck

lemma matchSearch_upper_bound_of_match (L : List ℕ) (n : ℕ) (start : ℕ) 
  (h_match : listNth L (L.length - 1) = listNth L start)
  (h_start_lt : start < n) :
  matchSearch L n ≤ L.length - 1 - start := by {
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases h : listNth L (L.length - 1) = listNth L n
    · rw [matchSearch_ite_tt L n h]
      have h1 : start ≤ n := Nat.le_of_lt_succ h_start_lt
      exact Nat.sub_le_sub_left h1 (L.length - 1)
    · rw [matchSearch_ite_ff L n h]
      have h1 : start < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h_start_lt) (by 
        intro heq
        rw [heq] at h_match
        exact h h_match
      )
      exact ih h1
}

lemma h_val_le_P_test (n_1 n_2 P k : ℕ) 
    (hn1_lt_n2 : n_1 < n_2)
    (h_P : P = n_2 - n_1)
    (hk : k ≥ 1)
    (h_per : vanEckNthTerm (n_1 + k - 1) = vanEckNthTerm (n_2 + k - 1)) :
    vanEckNthTerm (n_2 + k) ≤ P := by {
  have h_gap := vanEck_term_is_matchSearch (n_2 + k) (Nat.le_trans hk (Nat.le_add_left k n_2))
  rw [h_gap]
  
  -- The list L is vanEck (n_2 + k - 1).
  -- L.length is n_2 + k.
  -- L.length - 1 is n_2 + k - 1.
  -- start is n_1 + k - 1.
  -- We want matchSearch L (n_2 + k - 1) <= P.
  
  have h_match : listNth (vanEck (n_2 + k - 1)) ((vanEck (n_2 + k - 1)).length - 1) = 
                 listNth (vanEck (n_2 + k - 1)) (n_1 + k - 1) := by {
    have hl : (vanEck (n_2 + k - 1)).length = n_2 + k := by {
      have hlen := vanEckLength (n_2 + k - 1)
      have h_sub_add : n_2 + k - 1 + 1 = n_2 + k := Nat.sub_add_cancel (Nat.le_trans hk (Nat.le_add_left k n_2))
      rw [h_sub_add] at hlen
      exact hlen
    }
    have hl_sub_1 : (vanEck (n_2 + k - 1)).length - 1 = n_2 + k - 1 := by {
      rw [hl]
      exact rfl
    }
    rw [hl_sub_1]
    have h_left : listNth (vanEck (n_2 + k - 1)) (n_2 + k - 1) = vanEckNthTerm (n_2 + k - 1) := rfl
    have h_right : listNth (vanEck (n_2 + k - 1)) (n_1 + k - 1) = vanEckNthTerm (n_1 + k - 1) := by {
      apply VanEck_deterministic (n_2 + k - 1) (n_1 + k - 1)
      have h1 : n_1 + k ≤ n_2 + k := Nat.add_le_add_right (Nat.le_of_lt hn1_lt_n2) k
      exact Nat.sub_le_sub_right h1 1
    }
    rw [h_left, h_right]
    exact h_per.symm
  }
  
  have h_start_lt : n_1 + k - 1 < n_2 + k - 1 := by {
    have h1 : n_1 + k < n_2 + k := Nat.add_lt_add_right hn1_lt_n2 k
    have h2 : n_1 + k - 1 < n_2 + k - 1 := Nat.sub_lt_sub_right_of_lt_add (Nat.le_trans hk (Nat.le_add_left k n_2)) (by exact h1)
    exact h2
  }
  
  have h_bound := matchSearch_upper_bound_of_match (vanEck (n_2 + k - 1)) (n_2 + k - 1) (n_1 + k - 1) h_match h_start_lt
  
  have hl : (vanEck (n_2 + k - 1)).length = n_2 + k := by {
    have hlen := vanEckLength (n_2 + k - 1)
    have h_sub_add : n_2 + k - 1 + 1 = n_2 + k := Nat.sub_add_cancel (Nat.le_trans hk (Nat.le_add_left 1 _))
    rw [h_sub_add] at hlen
    exact hlen
  }
  have hl_sub_1 : (vanEck (n_2 + k - 1)).length - 1 = n_2 + k - 1 := by {
    rw [hl]
    exact rfl
  }
  rw [hl_sub_1] at h_bound
  
  have h_sub : n_2 + k - 1 - (n_1 + k - 1) = P := by {
    have hs1 : n_2 + k - 1 = n_2 + (k - 1) := Nat.add_sub_assoc hk n_2
    have hs2 : n_1 + k - 1 = n_1 + (k - 1) := Nat.add_sub_assoc hk n_1
    rw [hs1, hs2]
    have hs3 : n_2 + (k - 1) - (n_1 + (k - 1)) = n_2 - n_1 := Nat.add_sub_add_right n_2 n_1 (k - 1)
    rw [hs3]
    exact h_P.symm
  }
  rw [h_sub] at h_bound
  
  exact h_bound
}
