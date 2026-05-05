import Mathlib
import VanEck.VanEck.Basic
import VanEck.LimSup
import VanEck.InfiniteTwos
import VanEck.ImpossiblePatterns

lemma alternating_pair_implies_two (i : ℕ) (h : vanEckNthTerm i = vanEckNthTerm (i + 2)) :
    vanEckNthTerm (i + 3) = 2 := by {
  by_cases h_eq1 : vanEckNthTerm (i + 1) = vanEckNthTerm (i + 2)
  · have h_trip : vanEckNthTerm i = vanEckNthTerm (i + 2) ∧ vanEckNthTerm (i + 1) = vanEckNthTerm (i + 2) ∧ vanEckNthTerm (i + 2) = vanEckNthTerm (i + 2) := ⟨h, h_eq1, rfl⟩
    have hc := vanEck_triple_impossible i (vanEckNthTerm (i + 2))
    exfalso
    exact hc h_trip
  · have hm := vanEck_term_is_matchSearch (i + 3) (by decide)
    have hsub : i + 3 - 1 = i + 2 := rfl
    rw [hsub] at hm
    
    have hlen : (vanEck (i + 2)).length = i + 3 := vanEckLength (i + 2)
    have hd_last : listNth (vanEck (i + 2)) (i + 2) = vanEckNthTerm (i + 2) := by
      exact VanEck_deterministic (i + 2) (i + 2) (Nat.le_refl _)
    have hd_1 : listNth (vanEck (i + 2)) (i + 1) = vanEckNthTerm (i + 1) := by
      exact VanEck_deterministic (i + 2) (i + 1) (Nat.le_succ _)
    have hd_0 : listNth (vanEck (i + 2)) i = vanEckNthTerm i := by
      exact VanEck_deterministic (i + 2) i (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
      
    rw [matchSearch, hlen] at hm
    have hsub2 : i + 3 - 1 = i + 2 := rfl
    have hsub3 : i + 3 - 2 = i + 1 := rfl
    
    -- need to evaluate matchSearchAux
    sorry
}

