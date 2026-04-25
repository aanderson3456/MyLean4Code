import VanEck
import Mathlib

open Finset

def zerosCount : ℕ → ℕ
  | 0 => 1
  | m + 1 => if vanEckNthTerm (m + 1) = 0 then zerosCount m + 1 else zerosCount m

lemma zerosCount_eq_card (m : ℕ) : 
    zerosCount m = ((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)).card + 1 := by
  induction m with
  | zero =>
    unfold zerosCount
    have h : Finset.range 0 = ∅ := rfl
    rw [h, Finset.filter_empty, Finset.card_empty, Nat.zero_add]
  | succ m ih =>
    unfold zerosCount
    have h_range : Finset.range (m + 1) = insert m (Finset.range m) := Finset.range_add_one
    rw [h_range]
    rw [Finset.filter_insert]
    split
    · rename_i hz
      rw [Finset.card_insert_of_notMem]
      · rw [ih]
        -- we need to show ih + 1 = card + 1 + 1. 
        -- Actually, rw ih replaces zerosCount m with card + 1
        -- so zerosCount m + 1 = card + 1 + 1
        -- Wait, Finset.card_insert_of_not_mem replaces card (insert) with card + 1
        -- So LHS is card_m + 1 + 1, RHS is (card_m + 1) + 1. 
        exact rfl
      · intro h_mem
        have h_lt : m < m := by
          have h_mem2 : m ∈ Finset.range m := Finset.mem_filter.mp h_mem |>.1
          exact Finset.mem_range.mp h_mem2
        exact Nat.lt_irrefl m h_lt
    · rename_i hz
      have h_eq : (if vanEckNthTerm (m + 1) = 0 then insert m (filter (fun i => vanEckNthTerm (i + 1) = 0) (range m)) else filter (fun i => vanEckNthTerm (i + 1) = 0) (range m)) = filter (fun i => vanEckNthTerm (i + 1) = 0) (range m) := by
        rw [if_neg hz]
      rw [h_eq]
      exact ih
