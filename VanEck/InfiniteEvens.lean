import VanEck
import ImpossiblePatterns
import LimSup
import FinishedSurjLemmas
import Mathlib

/--
Definition: A sequence satisfies `OnlyOddsAndZerosAfter N` if for all `m > N`, the term is either 0 or an odd number.
-/
def OnlyOddsAndZerosAfter (N : ℕ) : Prop :=
  ∀ m > N, vanEckNthTerm m = 0 ∨ vanEckNthTerm m % 2 = 1

/--
Informal Explanation:
If a term `vanEckNthTerm m` is a new odd number `X`, it has never appeared before.
Because it's a new number, the term immediately following it must be 0.
-/
lemma new_odd_forces_next_zero (N : ℕ) (h_odds : OnlyOddsAndZerosAfter N) (m : ℕ) (hm : m > N)
    (h_odd : vanEckNthTerm m % 2 = 1) (h_new : ∀ i < m, vanEckNthTerm i ≠ vanEckNthTerm m) :
    vanEckNthTerm (m + 1) = 0 := by {
  sorry
}

/--
Informal Explanation:
If we get a new odd number `X` at index `m`, we look at the term right before it, `vanEckNthTerm (m - 1)`.
Since we are only generating odds and zeros, `vanEckNthTerm (m - 1)` must be either 0 or an odd number.
If it is 0, we say the backtrack is "done" because a 0 immediately preceding a new value forces a specific gap structure (specifically a gap of 2 next, which is even, leading to a contradiction).
-/
lemma prev_term_of_new_odd_is_zero_or_odd (N : ℕ) (h_odds : OnlyOddsAndZerosAfter N) (m : ℕ) (hm : m > N + 1)
    (h_odd : vanEckNthTerm m % 2 = 1) (h_new : ∀ i < m, vanEckNthTerm i ≠ vanEckNthTerm m) :
    vanEckNthTerm (m - 1) = 0 ∨ vanEckNthTerm (m - 1) % 2 = 1 := by {
  sorry
}

/--
Informal Explanation:
If the previous term `vanEckNthTerm (m - 1)` was another odd number `Y` (not 0), then `Y` must be smaller than the new odd number `X`.
Why? Because `X` is the distance to the previous occurrence of `Y`. Since `X` is generated at `m`, the previous occurrence of `Y` was at index `m - 1 - X`.
Since index `m - 1 - X` must be ≥ 0, `X` cannot be larger than `m - 1`. 
The distance relationship formally is `X = m - 1 - prev`, where `vanEckNthTerm prev = Y`.
-/
lemma prev_term_odd_implies_distance (N : ℕ) (h_odds : OnlyOddsAndZerosAfter N) (m : ℕ) (hm : m > N + 1)
    (h_new : ∀ i < m, vanEckNthTerm i ≠ vanEckNthTerm m)
    (h_prev_odd : vanEckNthTerm (m - 1) % 2 = 1) :
    ∃ prev < m - 1, vanEckNthTerm prev = vanEckNthTerm (m - 1) ∧ vanEckNthTerm m = m - 1 - prev := by {
  sorry
}

/--
Informal Explanation:
By chaining these lookbacks, we create a backtrack tree. Every odd number points back to its previous occurrence. 
Because the sequence only contains odds and zeros, and every odd number requires a previous occurrence to generate the next gap, the sequence must repeatedly jump back to smaller indices.
This backtracking cannot continue infinitely into the past (since indices must be ≥ 0), so it must eventually hit a 0.
-/
lemma odd_chain_eventually_hits_zero (N : ℕ) (h_odds : OnlyOddsAndZerosAfter N) (m : ℕ) (hm : m > N)
    (h_odd : vanEckNthTerm m % 2 = 1) :
    ∃ z < m, vanEckNthTerm z = 0 ∧ (∀ i, z < i → i ≤ m → vanEckNthTerm i ≠ 0) := by {
  sorry
}

/--
Informal Explanation:
When the backtrack chain eventually hits a 0, the structure forces the generation of an even number (specifically 2).
Since we assumed `OnlyOddsAndZerosAfter N`, generating an even number is a direct contradiction.
Therefore, an infinite sequence of only odds and zeros cannot exist.
-/
lemma odds_and_zeros_chain_contradiction (N : ℕ) (h_odds : OnlyOddsAndZerosAfter N) : False := by {
  sorry
}

/--
The Excluded Even Terms Theorem:
It is impossible for the Van Eck sequence to eventually contain no positive even numbers.
If it did, every lookback distance would eventually be odd, forcing a strict alternation
of index parities that collides with the zero-gap parity structure.

NOTE: Proving a contradiction for an arbitrary N_0 from the inequality z ≤ 2 z_prev - 1 alone
is as difficult as the InfiniteTwos conjecture. For the actual Van Eck sequence, this inequality
holds for all consecutive zeros after index 10 (e.g. z_5 = 15 ≤ 2 z_4 - 1 = 19). Therefore,
no contradiction can be derived from the growth inequality alone for large N_0 without proving
that a number like 2 (or other even numbers) must actually appear.
-/
lemma no_twos_implies_bounded (N_0 : ℕ) (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2) :
    ∃ M > 0, ∀ m, vanEckNthTerm m ≤ M := by {
  have h_ex_zero : ∃ z > N_0 + 2, vanEckNthTerm z = 0 := by {
    have h_zeros := infinite_zeros_vanEck (N_0 + 2)
    rcases h_zeros with ⟨z, hz_gt, hz_zero⟩
    use z, hz_gt, hz_zero
  }
  rcases h_ex_zero with ⟨z_0, hz0_gt, hz0_zero⟩
  let M := vanEckPrefixMax z_0
  have hM_pos : M > 0 := by {
    have h_z0 : 2 ≤ z_0 := by omega
    have h_le : vanEckNthTerm 2 ≤ M := vanEckNthTerm_le_prefixMax z_0 2 h_z0
    have h2 : vanEckNthTerm 2 = 1 := rfl
    rw [h2] at h_le
    exact h_le
  }
  use M
  constructor
  · exact hM_pos
  · have h_bound_zeros : ∀ z ≥ z_0, vanEckNthTerm z = 0 → vanEckPrefixMax z ≤ M := by {
      intro z
      induction z using Nat.strong_induction_on with
      | h z ih =>
        intro hz_ge hz_zero
        by_cases hz0 : z = z_0
        · rw [hz0]
        · have hz_gt : z > z_0 := Nat.lt_of_le_of_ne hz_ge (Ne.symm hz0)
          let z_prev := lastZero (z - 1)
          have hz_prev_lt : z_prev < z := by {
            have h_le := lastZero_le (z - 1)
            omega
          }
          have hz_prev_zero : vanEckNthTerm z_prev = 0 := vanEck_lastZero_is_zero (z - 1)
          have hz_prev_ge : z_prev ≥ z_0 := by {
            by_contra hc
            have hz_zero_le : z_0 ≤ z - 1 := by omega
            have h_contra := no_zero_after_lastZero (z - 1) z_0 (by omega) hz_zero_le
            exact h_contra hz0_zero
          }
          have h_ih := ih z_prev hz_prev_lt hz_prev_ge hz_prev_zero
          have h_all : ∀ k ≤ z, vanEckNthTerm k ≤ M := by {
            intro k hk
            by_cases hk_z : k = z
            · rw [hk_z, hz_zero]
              omega
            · have hk_lt : k < z := Nat.lt_of_le_of_ne hk hk_z
              by_cases hk_z1 : k = z - 1
              · rw [hk_z1]
                sorry
              · have hk_lt_z1 : k < z - 1 := by omega
                by_cases hk_le_prev : k ≤ z_prev
                · have h1 : vanEckNthTerm k ≤ vanEckPrefixMax z_prev :=
                    vanEckNthTerm_le_prefixMax z_prev k hk_le_prev
                  exact Nat.le_trans h1 h_ih
                · have hk_gt_prev : k > z_prev := Nat.lt_of_not_ge hk_le_prev
                  have h_nonzero : ∀ j, z_prev < j → j < z_prev + (z - z_prev) → vanEckNthTerm j ≠ 0 := by {
                    intro j hj1 hj2
                    have h_G : z_prev + (z - z_prev) = z := Nat.add_sub_of_le (Nat.le_of_lt hz_prev_lt)
                    rw [h_G] at hj2
                    exact no_zero_after_lastZero (z - 1) j hj1 (by omega)
                  }
                  have h_gap := gap_contains_all_terms z_prev (z - z_prev) h_nonzero
                  have h_arg : z_prev + (z - z_prev) - 1 = z - 1 := by {
                    have h_G : z_prev + (z - z_prev) = z := Nat.add_sub_of_le (Nat.le_of_lt hz_prev_lt)
                    rw [h_G]
                  }
                  rw [h_arg] at h_gap
                  have h2 := h_gap k hk_lt_z1
                  exact Nat.le_trans h2 h_ih
          }
          unfold vanEckPrefixMax
          apply listMax_le
          intro x hx
          rcases mem_listNth hx with ⟨k, hk_lt, rfl⟩
          have h_len := vanEckLength z
          rw [h_len] at hk_lt
          have hk_le : k ≤ z := Nat.le_of_lt_succ hk_lt
          have h_det := VanEck_deterministic z k hk_le
          rw [h_det]
          exact h_all k hk_le
    }
    intro m
    have h_zeros := infinite_zeros_vanEck (max z_0 m)
    rcases h_zeros with ⟨z, hz_gt, hz_zero⟩
    have hz_ge : z ≥ z_0 := by omega
    have hm_le : m ≤ z := by omega
    have h_bound_z := h_bound_zeros z hz_ge hz_zero
    have h_le_z : vanEckNthTerm m ≤ vanEckPrefixMax z := vanEckNthTerm_le_prefixMax z m hm_le
    exact Nat.le_trans h_le_z h_bound_z
}


lemma eventually_bounded_implies_eventually_periodic (N_0 B : ℕ) (h_bound : ∀ m > N_0, vanEckNthTerm m < B) :
    ∃ p > 0, ∃ N_1 ≥ N_0, ∀ m > N_1, vanEckNthTerm m = vanEckNthTerm (m + p) := by {
  have h_glob_bound : ∃ B_glob : ℕ, ∀ n, vanEckNthTerm n < B_glob := by {
    use B + vanEckPrefixMax N_0 + 1
    intro n
    by_cases hn : n ≤ N_0
    · have h1 := vanEckNthTerm_le_prefixMax N_0 n hn
      omega
    · have h2 : n > N_0 := by omega
      have h3 := h_bound n h2
      omega
  }
  rcases h_glob_bound with ⟨B_glob, h_glob⟩
  have h_glob_pos : B_glob > 0 := by {
    have h0 := h_glob 0
    omega
  }
  have h_coll := pigeonhole_state_collision B_glob h_glob
  rcases h_coll with ⟨n_1, n_2, hn1, hn_lt, h_state_eq⟩
  have h_per := forward_periodicity n_1 n_2 B_glob h_glob h_state_eq hn1 (by omega) h_glob_pos
  use n_2 - n_1
  refine ⟨by omega, max N_0 n_1, by omega, ?_⟩
  intro m hm_gt
  have hm_gt_n1 : m > n_1 := by omega
  have h_eq_term := (h_per (m - n_1)).2
  have hk_eq : n_1 + (m - n_1) = m := Nat.add_sub_cancel' (by omega)
  have hp_eq : n_2 + (m - n_1) = m + (n_2 - n_1) := by omega
  rw [hk_eq, hp_eq] at h_eq_term
  exact h_eq_term
}

lemma eventually_bounded_impossible (N_0 B : ℕ) (h_bound : ∀ m > N_0, vanEckNthTerm m < B) : False := by {
  have h_per := eventually_bounded_implies_eventually_periodic N_0 B h_bound
  rcases h_per with ⟨p, hp_pos, N_1, hN1, h_eq⟩
  have h_not_per := vanEck_not_periodic2 p hp_pos N_1
  rcases h_not_per with ⟨m, hm_gt, hneq⟩
  have heq2 := h_eq m hm_gt
  contradiction
}


lemma gap_gt_prefix_max_is_new (z z_prev : ℕ) (hz_zero : vanEckNthTerm z = 0) (hz_pos : z > 0)
    (hz_prev : vanEckNthTerm z_prev = 0) (h_prev_lt : z_prev < z)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0)
    (h_gt : z - z_prev > vanEckPrefixMax z) :
    ∀ i < z + 1, vanEckNthTerm i ≠ vanEckNthTerm (z + 1) := by {
  intro i hi heq
  have h_gap_eq : vanEckNthTerm (z + 1) = z - z_prev := gap_between_zeros z z_prev hz_zero hz_pos hz_prev h_prev_lt h_gap
  rw [h_gap_eq] at heq
  by_cases hiz : i = z
  · subst hiz
    rw [hz_zero] at heq
    omega
  · have hi_lt_z : i < z := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ hi) hiz
    have h_le : vanEckNthTerm i ≤ vanEckPrefixMax z := vanEckNthTerm_le_prefixMax z i (Nat.le_of_lt hi_lt_z)
    rw [heq] at h_le
    omega
}

lemma powers_of_two_gap_contradiction (N_0 : ℕ) (h_pow : ∀ m > N_0, vanEckNthTerm m ∈ PowersOfTwoSet)
    (z z_prev : ℕ) (hz : vanEckNthTerm z = 0) (hz_gt : z > N_0)
    (hz_prev : vanEckNthTerm z_prev = 0) (h_prev_lt : z_prev < z)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0)
    (h_new : ∀ i < z + 1, vanEckNthTerm i ≠ vanEckNthTerm (z + 1))
    (h_gt_8 : z - z_prev ≥ 8) :
    ∃ d ∈ PowersOfTwoSet, d = 5 ∧ d ≤ z - z_prev := by {
  sorry
}

lemma powers_of_two_lookback_contradiction (d : ℕ) (hd_pow : d ∈ PowersOfTwoSet) (hd_eq : d = 5) : False := by {
  rw [hd_eq] at hd_pow
  exact five_not_in_powers_of_two hd_pow
}

lemma growth_contradiction_pow_two (N_0 : ℕ) (h_pow : ∀ m > N_0, vanEckNthTerm m ∈ PowersOfTwoSet) : False := by {
  have h_unb : ∃ z > N_0, vanEckNthTerm z = 0 ∧ ∃ z_prev < z, vanEckNthTerm z_prev = 0 ∧
    (∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) ∧ z - z_prev ≥ 8 ∧ z - z_prev > vanEckPrefixMax z := by {
    sorry
  }
  rcases h_unb with ⟨z, hz_gt, hz_zero, z_prev, hz_prev_lt, hz_prev_zero, h_gap, h_gt_8, h_gt_prefix⟩
  have h_new : ∀ i < z + 1, vanEckNthTerm i ≠ vanEckNthTerm (z + 1) := by {
    apply gap_gt_prefix_max_is_new z z_prev hz_zero (by omega) hz_prev_zero hz_prev_lt h_gap h_gt_prefix
  }
  have h_contra := powers_of_two_gap_contradiction N_0 h_pow z z_prev hz_zero hz_gt hz_prev_zero hz_prev_lt h_gap h_new h_gt_8
  rcases h_contra with ⟨d, hd_pow, hd_eq, _⟩
  exact powers_of_two_lookback_contradiction d hd_pow hd_eq
}

theorem vanEck_not_eventually_powers_of_two :
    ¬ (∃ N_0, ∀ m > N_0, vanEckNthTerm m ∈ PowersOfTwoSet) := by {
  intro h_ex
  rcases h_ex with ⟨N_0, h_pow⟩
  exact growth_contradiction_pow_two N_0 h_pow
}

lemma growth_contradiction (N_0 : ℕ) (h_fib : ∀ m > N_0, vanEckNthTerm m ∈ FibonacciSet) : False := by {
  sorry
}

theorem vanEck_not_eventually_fibonacci :
    ¬ (∃ N_0, ∀ m > N_0, vanEckNthTerm m ∈ FibonacciSet) := by {
  intro h_ex
  rcases h_ex with ⟨N_0, h_fib⟩
  exact growth_contradiction N_0 h_fib
}

theorem no_even_terms_impossible (N_0 : ℕ) :
    ¬ (∀ m > N_0, vanEckNthTerm m = 0 ∨ vanEckNthTerm m % 2 = 1) := by {
  intro h_no_evens
  have h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2 := by {
    intro m hm hc
    have h_val := h_no_evens m hm
    rw [hc] at h_val
    rcases h_val with h_zero | h_odd
    · contradiction
    · revert h_odd
      decide
  }
  have h_bound := no_twos_implies_bounded N_0 h_no_twos
  rcases h_bound with ⟨M, hM_pos, hM_bound⟩
  have h_bound_tail : ∀ m > N_0, vanEckNthTerm m < M + 1 := by {
    intro m _
    have h := hM_bound m
    omega
  }
  exact eventually_bounded_impossible N_0 (M + 1) h_bound_tail
}
