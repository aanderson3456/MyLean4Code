import Mathlib
import VanEck.VanEck
import VanEck.ImpossiblePatterns

lemma test_no_alt (i : ℕ) (h_eq : vanEckNthTerm i = vanEckNthTerm (i + 2)) :
    vanEckNthTerm (i + 3) = 2 := by {
  have hpos : 0 < i + 3 := Nat.zero_lt_succ _
  have hm := vanEck_term_is_matchSearch (i + 3) hpos
  have hsub : i + 3 - 1 = i + 2 := rfl
  rw [hsub] at hm
  
  have hlen : (vanEck (i + 2)).length = i + 3 := vanEckLength (i + 2)
  have hd_2_list : listNth (vanEck (i + 2)) (i + 2) = vanEckNthTerm (i + 2) := VanEck_deterministic (i + 2) (i + 2) (Nat.le_refl _)
  have hd_1_list : listNth (vanEck (i + 2)) (i + 1) = vanEckNthTerm (i + 1) := VanEck_deterministic (i + 2) (i + 1) (Nat.le_succ _)
  have hd_0_list : listNth (vanEck (i + 2)) i = vanEckNthTerm i := VanEck_deterministic (i + 2) i (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
  
  by_cases h_eq1 : vanEckNthTerm (i + 1) = vanEckNthTerm (i + 2)
  · have hc := vanEck_triple_impossible i (vanEckNthTerm (i + 2))
    have h_trip : vanEckNthTerm i = vanEckNthTerm (i + 2) ∧ vanEckNthTerm (i + 1) = vanEckNthTerm (i + 2) ∧ vanEckNthTerm (i + 2) = vanEckNthTerm (i + 2) := ⟨h_eq, h_eq1, rfl⟩
    exfalso
    exact hc h_trip
  · have h_ite_1 : matchSearch (vanEck (i + 2)) (i + 2) = matchSearch (vanEck (i + 2)) (i + 1) := by {
      have h_neq2 : listNth (vanEck (i + 2)) ((vanEck (i + 2)).length - 1) ≠ listNth (vanEck (i + 2)) (i + 1) := by {
        rw [hlen]
        have hsub2 : i + 3 - 1 = i + 2 := rfl
        rw [hsub2, hd_2_list, hd_1_list]
        intro hc
        exact h_eq1 hc.symm
      }
      have h_ff := matchSearch_ite_ff (vanEck (i + 2)) (i + 1) h_neq2
      have hi2 : i + 1 + 1 = i + 2 := rfl
      rw [hi2] at h_ff
      exact h_ff
    }
    have h_ite_2 : matchSearch (vanEck (i + 2)) (i + 1) = 2 := by {
      have h_eq2 : listNth (vanEck (i + 2)) ((vanEck (i + 2)).length - 1) = listNth (vanEck (i + 2)) i := by {
        rw [hlen]
        have hsub2 : i + 3 - 1 = i + 2 := rfl
        rw [hsub2, hd_2_list, hd_0_list]
        exact h_eq.symm
      }
      have h_tt := matchSearch_ite_tt (vanEck (i + 2)) i h_eq2
      have hi1 : i + 1 = i + 1 := rfl
      rw [hi1] at h_tt
      rw [h_tt, hlen]
      have hsub2 : i + 3 - 1 = i + 2 := rfl
      rw [hsub2]
      exact Nat.add_sub_cancel_left i 2
    }
    rw [h_ite_1, h_ite_2] at hm
    exact hm
}
