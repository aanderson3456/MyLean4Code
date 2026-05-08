import VanEck.Basic
import VanEck

open List

lemma new_number_implies_next_zero (n : ℕ) (h : (vanEck n).count (vanEckNthTerm n) = 1) : 
    vanEckNextTerm (vanEck n) = 0 := by {
  cases n with
  | zero => rfl
  | succ m =>
    have h_append : vanEck (m + 1) = vanEck m ++ [vanEckNextTerm (vanEck m)] := rfl
    have h_term : vanEckNextTerm (vanEck m) = vanEckNthTerm (m + 1) := by {
      unfold vanEckNthTerm
      have hlen : (vanEck (m + 1)).length = m + 2 := vanEckLength _
      rw [h_append]
      have hlen2 : (vanEck m).length = m + 1 := vanEckLength _
      rw [← hlen2]
      exact listNth_last _ _
    }
    rw [h_term] at h_append
    rw [h_append] at h
    rw [count_append] at h
    have hsimp : [vanEckNthTerm (m + 1)].count (vanEckNthTerm (m + 1)) = 1 := by simp
    rw [hsimp] at h
    have h_count_zero : (vanEck m).count (vanEckNthTerm (m + 1)) = 0 := by omega
    
    have h_not_mem : vanEckNthTerm (m + 1) ∉ vanEck m := by {
      intro h_mem
      have h_pos : (vanEck m).count (vanEckNthTerm (m + 1)) > 0 := by {
        apply count_pos_iff_mem.mpr
        exact h_mem
      }
      omega
    }
    
    have h_rhs : ∀ k < m + 1, vanEckNthTerm k ≠ vanEckNthTerm (m + 1) := by {
      intro k hk h_eq
      have h_mem : vanEckNthTerm k ∈ vanEck m := by {
        have h_eq2 : vanEckNthTerm k = listNth (vanEck m) k := (VanEck_deterministic m k hk).symm
        rw [h_eq2]
        apply listNth_mem
        rw [vanEckLength]
        exact hk
      }
      rw [h_eq] at h_mem
      exact h_not_mem h_mem
    }
    
    have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new m
    have h_zero : vanEckNthTerm (m + 2) = 0 := h_iff.mpr h_rhs
    
    have h_next : vanEckNthTerm (m + 2) = vanEckNextTerm (vanEck (m + 1)) := by {
      unfold vanEckNthTerm
      have h_append2 : vanEck (m + 2) = vanEck (m + 1) ++ [vanEckNextTerm (vanEck (m + 1))] := rfl
      rw [h_append2]
      have hlen3 : (vanEck (m + 1)).length = m + 2 := vanEckLength _
      rw [← hlen3]
      exact listNth_last _ _
    }
    
    rw [← h_next]
    exact h_zero
}
