import Mathlib
import VanEck
import ImpossiblePatterns

-- Test: direct P ≤ 2 contradiction from periodicity + no-twos.
-- P=1: consecutive equal → next = 1 → consecutive 1s.
-- P=2: val(k)=val(k+2) contradicts no-alternating-pairs (which forces val(k+3)=2).

-- For P ≥ 3 with C ≥ 2:
-- Each within-period gap ≠ 2. Each value x's cyclic distances ≠ 2.
-- Consider the "1-chain": wherever val(k)=val(k+1), val(k+2)=1.
-- After a 1 at position k+2, val(k+3) = gap to prev 1.
-- No consecutive 1s, so gap ≥ 2. But gap ≠ 2, so gap ≥ 3.
-- val(k+3) ≥ 3. Then val(k+3) is a "large" gap pointing far back.
-- The value val(k+2) = 1 and val(k+4) = gap to prev match of val(k+3).
-- Since val(k+3) ≥ 3 and ≤ P, this gap is ≤ P.
-- No immediate contradiction. Need full algebraic argument.

-- STRATEGY: Prove P ≤ 2 gives contradiction directly.
-- Then prove P ≥ 3 with C ≥ 2 also gives contradiction using
-- the fact that within-period distances ≠ 2 combined with the
-- bijection f force every value to have all its within-fiber
-- distances = 1 or ≥ 3, and the sum constraint CP with C ≥ 2
-- is incompatible.

-- Actually, simplest path: just handle P = 1 and P = 2 inline,
-- and for P ≥ 3, show that the no-alternating-pairs constraint
-- applied WITHIN the periodic block (cyclically) combined with
-- h_C_ge_2 forces a specific gap = 2 somewhere.

-- Let me test P ≤ 2 cases.
example (n_1 n_2 K : ℕ) (hn1_lt : n_1 < n_2) (P : ℕ)
    (hP : P = n_2 - n_1) (hP1 : P = 1)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k))
    (hK : K ≥ 4) : False := by {
  -- P=1 means n_2 = n_1 + 1.
  -- h_per at k=0: v(n_1) = v(n_2) = v(n_1+1). Consecutive equal.
  have h0 : vanEckNthTerm n_1 = vanEckNthTerm (n_1 + 1) := by {
    have hp0 := h_per 0 (Nat.zero_le K)
    simp at hp0
    have h_n2 : n_2 = n_1 + 1 := by omega
    rw [h_n2] at hp0
    exact hp0
  }
  -- Consecutive equal → next = 1.
  have h1 : vanEckNthTerm (n_1 + 2) = 1 :=
    vanEck_consecutive_eq_implies_next_one n_1 h0
  -- By periodicity at k=2: v(n_1+2) = v(n_2+2) = v(n_1+3).
  have h2 : vanEckNthTerm (n_1 + 2) = vanEckNthTerm (n_1 + 3) := by {
    have hp2 := h_per 2 (by omega)
    have h_n2 : n_2 = n_1 + 1 := by omega
    rw [h_n2] at hp2
    have : n_1 + 1 + 2 = n_1 + 3 := by omega
    rw [this] at hp2
    exact hp2
  }
  -- So v(n_1+3) = 1. Combined with v(n_1+2) = 1: consecutive 1s.
  have h3 : vanEckNthTerm (n_1 + 3) = 1 := by rw [← h2]; exact h1
  have h_cons : vanEckNthTerm (n_1 + 2) = 1 ∧ vanEckNthTerm (n_1 + 2 + 1) = 1 := by {
    constructor
    · exact h1
    · have : n_1 + 2 + 1 = n_1 + 3 := by omega
      rw [this]; exact h3
  }
  exact vanEck_no_consecutive_ones (n_1 + 2) h_cons
}

-- P = 2 case
example (n_1 n_2 K : ℕ) (hn1_lt : n_1 < n_2) (P : ℕ)
    (hP : P = n_2 - n_1) (hP2 : P = 2)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k))
    (h_no_twos : ∀ m > n_1, vanEckNthTerm m ≠ 2)
    (hK : K ≥ 5) : False := by {
  -- P=2: v(n_1+k) = v(n_2+k) = v(n_1+2+k).
  -- So v(n_1+k) = v(n_1+k+2) for all k ≤ K.
  have h_alt : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_1 + k + 2) := by {
    intro k hk
    have hp := h_per k hk
    have h_n2 : n_2 = n_1 + 2 := by omega
    rw [h_n2] at hp
    have : n_1 + 2 + k = n_1 + k + 2 := by omega
    rw [this] at hp
    exact hp
  }
  -- v(n_1+1) = v(n_1+3). Two cases:
  -- Case 1: v(n_1+2) = v(n_1+3). Then consecutive equal → v(n_1+4) = 1.
  --   Also v(n_1+2) = v(n_1+4) (from periodicity). So v(n_1+2) = 1.
  --   Then v(n_1+2) = v(n_1+3) = 1 → consecutive 1s. Contradiction.
  -- Case 2: v(n_1+2) ≠ v(n_1+3). Then v(n_1+1) = v(n_1+3) with
  --   v(n_1+2) ≠ v(n_1+3). This is an alternating pair, so v(n_1+4) = 2.
  --   Contradiction with h_no_twos.
  have h13 := h_alt 1 (by omega)
  have h24 := h_alt 2 (by omega)
  by_cases heq : vanEckNthTerm (n_1 + 2) = vanEckNthTerm (n_1 + 3)
  · -- Case 1: consecutive equal at n_1+2, n_1+3
    have h_next := vanEck_consecutive_eq_implies_next_one (n_1 + 2) heq
    -- v(n_1+4) = 1. But v(n_1+2) = v(n_1+4) by periodicity.
    have : n_1 + 2 + 2 = n_1 + 4 := by omega
    rw [this] at h_next
    -- So v(n_1+2) = 1.
    have hv2_1 : vanEckNthTerm (n_1 + 2) = 1 := by rw [h24]; exact h_next
    -- And v(n_1+3) = 1.
    have hv3_1 : vanEckNthTerm (n_1 + 3) = 1 := by rw [← heq]; exact hv2_1
    -- Consecutive 1s at n_1+2, n_1+3.
    have h_cons : vanEckNthTerm (n_1 + 2) = 1 ∧ vanEckNthTerm (n_1 + 2 + 1) = 1 := by {
      constructor; exact hv2_1
      have : n_1 + 2 + 1 = n_1 + 3 := by omega
      rw [this]; exact hv3_1
    }
    exact vanEck_no_consecutive_ones (n_1 + 2) h_cons
  · -- Case 2: v(n_1+1) = v(n_1+3) but v(n_1+2) ≠ v(n_1+3).
    -- This is an alternating pair. From dense_block_without_twos logic:
    -- v(n_1+1) = v(n_1+3) and v(n_1+2) ≠ v(n_1+3) → v(n_1+4) = 2.
    -- We use the same matchSearch argument as in dense_block_without_twos.
    have h_eq : vanEckNthTerm (n_1 + 1) = vanEckNthTerm (n_1 + 1 + 2) := by {
      have : n_1 + 1 + 2 = n_1 + 3 := by omega
      rw [this]; exact h13
    }
    -- Following the dense_block_without_twos_has_no_alternating_pairs proof:
    let i := n_1 + 1
    have h_eq_i : vanEckNthTerm i = vanEckNthTerm (i + 2) := h_eq
    have h_eq1 : vanEckNthTerm (i + 1) ≠ vanEckNthTerm (i + 2) := by {
      have : i + 1 = n_1 + 2 := by omega
      have : i + 2 = n_1 + 3 := by omega
      rw [‹i + 1 = n_1 + 2›, ‹i + 2 = n_1 + 3›]
      exact heq
    }
    -- Now v(i+3) = 2 by the standard matchSearch argument.
    -- This is exactly what dense_block_without_twos proves.
    -- v(i+3) = 2 contradicts h_no_twos since i+3 = n_1+4 > n_1.
    sorry -- need to instantiate the matchSearch calculation for v(i+3)=2
}
