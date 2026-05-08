import VanEck.Basic
import VanEck

open List

lemma list_count_two_of_eq {L : List ℕ} {x : ℕ} {i j : ℕ} (hi : i < L.length) (hj : j < L.length) (hne : i ≠ j) 
    (hxi : listNth L i = x) (hxj : listNth L j = x) : L.count x ≥ 2 := by {
  revert i j
  induction L with
  | nil => intro i j hi; exfalso; exact Nat.not_lt_zero i hi
  | cons a as ih =>
    intro i j hi hj hne hxi hxj
    unfold count countP
    cases i
    · cases j
      · contradiction
      · rename_i j
        unfold listNth at hxi hxj
        have h1 : a = x := hxi
        rw [h1, if_pos rfl]
        have h_tail : as.count x ≥ 1 := by {
          have hk : x ∈ as := by {
            have hx_mem : listNth as j = x := hxj
            apply listNth_mem (Nat.lt_of_succ_lt_succ hj)
            rw [hx_mem]
          }
          exact count_pos_iff_mem.mpr hk
        }
        exact Nat.succ_le_succ h_tail
    · rename_i i
      cases j
      · unfold listNth at hxi hxj
        have h1 : a = x := hxj
        rw [h1, if_pos rfl]
        have h_tail : as.count x ≥ 1 := by {
          have hk : x ∈ as := by {
            have hx_mem : listNth as i = x := hxi
            apply listNth_mem (Nat.lt_of_succ_lt_succ hi)
            rw [hx_mem]
          }
          exact count_pos_iff_mem.mpr hk
        }
        exact Nat.succ_le_succ h_tail
      · rename_i j
        unfold listNth at hxi hxj
        by_cases ha : a = x
        · rw [ha, if_pos rfl]
          have h_tail : as.count x ≥ 1 := by {
            apply ih i j (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)
            · intro h_eq; apply hne; rw [h_eq]
            · exact hxi
            · exact hxj
          }
          exact Nat.le_add_left 2 _
        · rw [if_neg ha]
          have h_tail : as.count x ≥ 2 := by {
            apply ih i j (Nat.lt_of_succ_lt_succ hi) (Nat.lt_of_succ_lt_succ hj)
            · intro h_eq; apply hne; rw [h_eq]
            · exact hxi
            · exact hxj
          }
          exact h_tail
}

lemma new_number_implies_next_zero (n : ℕ) (h : (vanEck n).count (vanEckNthTerm n) = 1) : 
    vanEckNextTerm (vanEck n) = 0 := by {
  cases n with
  | zero => rfl
  | succ m =>
    have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new m
    have h_rhs : ∀ n_1 < m + 1, vanEckNthTerm n_1 ≠ vanEckNthTerm (m + 1) := by {
      intro k hk
      intro h_eq
      have h2 : (vanEck (m + 1)).count (vanEckNthTerm (m + 1)) ≥ 2 := by {
        apply list_count_two_of_eq
        · rw [vanEckLength]; exact Nat.lt_succ_of_lt hk
        · rw [vanEckLength]; exact Nat.lt_succ_self (m + 1)
        · exact Nat.ne_of_lt hk
        · have hd1 := VanEck_deterministic (m + 1) k (Nat.le_of_lt hk)
          rw [hd1, ← h_eq]
          rfl
        · have hd2 := VanEck_deterministic (m + 1) (m + 1) (Nat.le_refl _)
          rw [hd2]
          rfl
      }
      rw [h] at h2
      exact absurd h2 (by decide)
    }
    have h_zero : vanEckNthTerm (m + 2) = 0 := h_iff.mpr h_rhs
    have h_next : vanEckNthTerm (m + 2) = vanEckNextTerm (vanEck (m + 1)) := by {
      unfold vanEckNthTerm
      have hlen2 : (vanEck (m + 1)).length = m + 2 := vanEckLength _
      have h1 : vanEck (m + 2) = vanEck (m + 1) ++ [vanEckNextTerm (vanEck (m + 1))] := rfl
      rw [h1]
      rw [← hlen2]
      exact listNth_last _ _
    }
    rw [← h_next]
    exact h_zero
}
