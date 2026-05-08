import VanEck.Basic
import VanEck

open List

lemma count_eq_one_and_mem_last {L : List ℕ} {x : ℕ} (h_count : L.count x = 1) 
    (h_last : listNth L (L.length - 1) = x) : 
    matchSearch L (L.length - 1) = 0 := by
  sorry

lemma new_number_implies_next_zero (n : ℕ) (h : (vanEck n).count (vanEckNthTerm n) = 1) : 
    vanEckNextTerm (vanEck n) = 0 := by
  unfold vanEckNextTerm
  have h_last : listNth (vanEck n) ((vanEck n).length - 1) = vanEckNthTerm n := by
    rw [vanEckLength]
    have h1 : n + 1 - 1 = n := rfl
    rw [h1]
    rfl
  exact count_eq_one_and_mem_last h h_last

