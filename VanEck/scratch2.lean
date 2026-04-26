import VanEck
import ImpossiblePatterns

lemma matchSearch_neq_zero_of_match (L : List ℕ) (n k : ℕ) (hk : k < n)
    (h_match : listNth L (L.length - 1) = listNth L k) : matchSearch L n ≠ 0 := by
  induction n with
  | zero => exfalso; exact Nat.not_lt_zero k hk
  | succ n ih =>
    by_cases h_eq : listNth L (L.length - 1) = listNth L n
    · rw [matchSearch_ite_tt L n h_eq]
      intro h0
      -- L.length - 1 - n = 0 implies L.length - 1 <= n. 
      -- This depends on L.length > n, which is true.
      sorry
    · rw [matchSearch_ite_ff L n h_eq]
      have hkn : k < n := by
        have h1 : k ≤ n := Nat.le_of_lt_succ hk
        exact lt_of_le_of_ne h1 (fun h_k_eq_n => h_eq (by rw [← h_k_eq_n]; exact h_match))
      exact ih hkn
