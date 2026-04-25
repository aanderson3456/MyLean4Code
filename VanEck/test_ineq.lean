import VanEck
import LimSup
import Mathlib

lemma test_bound (n : ℕ) (hn : vanEckNthTerm n = 0) (hn_pos : n > 0) :
    ∃ m ≤ n + 1, vanEckNthTerm m * vanEckNthTerm m + 2 * vanEckNthTerm m + 1 ≥ n := by
  -- Let v be the maximum value up to n+1.
  let v := vanEckPrefixMax (n + 1)
  have h_bound_all : ∀ i ≤ n + 1, vanEckNthTerm i ≤ v := fun i hi => vanEckNthTerm_le_prefixMax (n + 1) i hi
  -- By zerosCount_le_bound: zerosCount n <= v + 2
  have h_zc : zerosCount n ≤ v + 2 := zerosCount_le_bound n (n+1) v (Nat.le_succ n) h_bound_all
  -- By lastZero_le_gaps: lastZero n <= (zerosCount n - 1) * v
  have h_lz : lastZero n ≤ (zerosCount n - 1) * v := lastZero_le_gaps n v h_bound_all
  -- Since a(n) = 0, lastZero n = n
  have h_lz_eq : lastZero n = n := by
    unfold lastZero
    -- wait, lastZero is recursive. n > 0, so n = n' + 1
    sorry
  
  sorry
