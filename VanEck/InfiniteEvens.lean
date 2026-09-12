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
  have hm_pos : m ≥ 1 := by omega
  have h_m1 : m - 1 + 2 = m + 1 := by omega
  have h_m2 : m - 1 + 1 = m := by omega
  rw [← h_m1]
  apply (vanEck_mth_term_eq_zero_iff_prev_term_new (m - 1)).mpr
  rw [h_m2]
  exact h_new
}

/--
Informal Explanation:
If we get a new odd number `X` at index `m`, we look at the term right before it, `vanEckNthTerm (m - 1)`.
Since we are only generating odds and zeros, `vanEckNthTerm (m - 1)` must be either 0 or an odd number.
If it is 0, we say the backtrack is "done" because a 0 immediately preceding a new value forces a specific gap structure (specifically a gap of 2 next, which is even, leading to a contradiction).
-/
lemma lookback_step (m X : ℕ) (h_X : vanEckNthTerm m = X) (h_X_odd : X % 2 = 1) 
    (h_prev_nz : vanEckNthTerm (m - 1) ≠ 0) :
    ∃ prev < m - 1, vanEckNthTerm prev = vanEckNthTerm (m - 1) ∧ prev % 2 = m % 2 := by {
  have hX_pos : X ≠ 0 := by omega
  have hm_pos : m > 0 := by
    by_contra hc
    have h0 : m = 0 := by omega
    rw [h0] at h_X
    have hv0 : vanEckNthTerm 0 = 0 := rfl
    rw [hv0] at h_X
    omega
  have hm_sub : m - 1 + 1 = m := Nat.sub_add_cancel hm_pos
  have hk : m - 1 ≥ 1 := by
    by_contra hc
    have hm1 : m - 1 = 0 := by omega
    have hm1_eq : m = 1 := by omega
    rw [hm1_eq] at h_X
    have hv1 : vanEckNthTerm 1 = 0 := rfl
    rw [hv1] at h_X
    omega
  have ht := gap_determines_value (m - 1) hk X (by decide) (by rw [hm_sub]; exact h_X) hX_pos
  have hX_le : X ≤ m := by
    have h_gap := vanEck_is_gap m hm_pos
    rw [h_X] at h_gap
    have h_ms := matchSearch_le_length (vanEck (m - 1)) (m - 1)
    rw [← h_gap] at h_ms
    have h_len := vanEckLength (m - 1)
    rw [h_len] at h_ms
    have hm_len_sub : m - 1 + 1 = m := Nat.sub_add_cancel hm_pos
    rw [hm_len_sub] at h_ms
    exact h_ms
  have hX_lt : X < m := by
    by_contra hc
    have heq : X = m := by omega
    have ht2 : vanEckNthTerm (m - 1) = vanEckNthTerm (m - 1 - m) := by
      rw [heq] at ht
      exact ht
    have h0 : m - 1 - m = 0 := by omega
    rw [h0] at ht2
    have hv0 : vanEckNthTerm 0 = 0 := rfl
    rw [hv0] at ht2
    exact h_prev_nz ht2
  have h_X_ge_1 : X ≥ 1 := by omega
  have hm1_pos : m - 1 > 0 := hk
  have h_lt : m - 1 - X < m - 1 := Nat.sub_lt hm1_pos h_X_ge_1
  have h_par : (m - 1 - X) % 2 = m % 2 := by
    have ⟨k, hk_X⟩ : ∃ k, X = 2 * k + 1 := ⟨X / 2, by omega⟩
    have h_eq : m = (m - 1 - X) + 2 * (k + 1) := by omega
    rw [h_eq]
    omega
  exact ⟨m - 1 - X, h_lt, ht.symm, h_par⟩
}

lemma lookback_hits_even (m : ℕ) (h_odd : vanEckNthTerm m % 2 = 1) :
    ∃ curr_k ≤ m, curr_k % 2 = m % 2 ∧ vanEckNthTerm (curr_k - 1) % 2 = 0 := by {
  induction' m using Nat.strong_induction_on with m ih
  by_cases h0 : vanEckNthTerm (m - 1) % 2 = 0
  · exact ⟨m, Nat.le_refl m, rfl, h0⟩
  · have h1 : vanEckNthTerm (m - 1) % 2 = 1 := by omega
    have h_nz : vanEckNthTerm (m - 1) ≠ 0 := by omega
    have h_step := lookback_step m (vanEckNthTerm m) rfl h_odd h_nz
    rcases h_step with ⟨prev, h_prev_lt, h_prev_val, h_prev_par⟩
    have h_prev_odd : vanEckNthTerm prev % 2 = 1 := by
      rw [h_prev_val]
      exact h1
    have h_prev_lt_m : prev < m := by omega
    have h_ih := ih prev h_prev_lt_m h_prev_odd
    rcases h_ih with ⟨curr_k, h_curr_le, h_curr_par, h_curr_even⟩
    have h_le : curr_k ≤ m := by omega
    have h_par : curr_k % 2 = m % 2 := by
      rw [h_curr_par, h_prev_par]
    exact ⟨curr_k, h_le, h_par, h_curr_even⟩
}

lemma zero_gap_even (N : ℕ) (h_odds : OnlyOddsAndZerosAfter N) 
    (z_a z_b : ℕ) (hz_a : vanEckNthTerm z_a = 0) (hz_b : vanEckNthTerm z_b = 0)
    (hz_lt : z_a < z_b) (h_between : ∀ i, z_a < i → i < z_b → vanEckNthTerm i ≠ 0)
    (h_bounds : N < z_a) :
    z_b % 2 = z_a % 2 := by {
  sorry
}

lemma zero_gap_odd (N : ℕ) (h_odds : OnlyOddsAndZerosAfter N) 
    (z_a z_b : ℕ) (hz_a : vanEckNthTerm z_a = 0) (hz_b : vanEckNthTerm z_b = 0)
    (hz_lt : z_a < z_b) (h_between : ∀ i, z_a < i → i < z_b → vanEckNthTerm i ≠ 0)
    (h_bounds : N < z_a) :
    z_b % 2 ≠ z_a % 2 := by {
  have h_match : listNth (vanEck z_b) ((vanEck z_b).length - 1) = listNth (vanEck z_b) z_a := by
    have h_len : (vanEck z_b).length = z_b + 1 := vanEckLength z_b
    have h_len1 : (vanEck z_b).length - 1 = z_b := by omega
    rw [h_len1]
    have hd_zb : listNth (vanEck z_b) z_b = vanEckNthTerm z_b := rfl
    have hd_za : listNth (vanEck z_b) z_a = vanEckNthTerm z_a := by
      exact VanEck_deterministic z_b z_a (Nat.le_of_lt hz_lt)
    rw [hd_zb, hd_za, hz_b, hz_a]
  have h_fail : ∀ k, 1 ≤ k → k ≤ z_b - z_a - 1 → listNth (vanEck z_b) ((vanEck z_b).length - 1) ≠ listNth (vanEck z_b) (z_a + k) := by
    intro k hk1 h_le
    have h_len1 : (vanEck z_b).length - 1 = z_b := by
      have h_len : (vanEck z_b).length = z_b + 1 := vanEckLength z_b
      omega
    rw [h_len1]
    have hd_zb : listNth (vanEck z_b) z_b = vanEckNthTerm z_b := rfl
    have hd_zak : listNth (vanEck z_b) (z_a + k) = vanEckNthTerm (z_a + k) := by
      exact VanEck_deterministic z_b (z_a + k) (by omega)
    rw [hd_zb, hd_zak, hz_b]
    exact fun h => h_between (z_a + k) (by omega) (by omega) h.symm
  have h_ms := matchSearch_eq_dist (vanEck z_b) z_a (z_b - z_a - 1) h_match h_fail
  have hz_sub : z_a + (z_b - z_a - 1) + 1 = z_b := by omega
  rw [hz_sub] at h_ms
  have h_gap := vanEck_is_gap (z_b + 1) (by omega)
  have h_len2 : (vanEck z_b).length - 1 - z_a = z_b - z_a := by
    have h_len : (vanEck z_b).length = z_b + 1 := vanEckLength z_b
    omega
  rw [h_len2] at h_ms
  have h_sub_zb : z_b + 1 - 1 = z_b := rfl
  rw [h_sub_zb] at h_gap
  rw [h_ms] at h_gap
  have h_val : vanEckNthTerm (z_b + 1) = z_b - z_a := h_gap
  
  have h_zb1_gt_N : z_b + 1 > N := by omega
  have h_or := h_odds (z_b + 1) h_zb1_gt_N
  have h_odd : (z_b - z_a) % 2 = 1 := by
    cases h_or with
    | inl h_is_zero => 
      have hc : z_b - z_a = 0 := by
        have hz_eq : vanEckNthTerm (z_b + 1) = 0 := h_is_zero
        rw [h_val] at hz_eq
        exact hz_eq
      omega
    | inr h_is_odd => 
      rw [← h_val]
      exact h_is_odd
  omega
}

lemma parity_alternation (N : ℕ) (h_odds : OnlyOddsAndZerosAfter N)
    (X curr prev : ℕ) (h_curr : vanEckNthTerm curr = X) (h_prev : vanEckNthTerm prev = X)
    (h_lt : prev < curr) (h_between : ∀ i, prev < i → i < curr → vanEckNthTerm i ≠ X)
    (h_curr_gt : N < curr) :
    curr % 2 ≠ prev % 2 := by {
  have h_match : listNth (vanEck curr) ((vanEck curr).length - 1) = listNth (vanEck curr) prev := by
    have h_len : (vanEck curr).length = curr + 1 := vanEckLength curr
    have h_len1 : (vanEck curr).length - 1 = curr := by omega
    rw [h_len1]
    have hd_curr : listNth (vanEck curr) curr = vanEckNthTerm curr := rfl
    have hd_prev : listNth (vanEck curr) prev = vanEckNthTerm prev := by
      exact VanEck_deterministic curr prev (Nat.le_of_lt h_lt)
    rw [hd_curr, hd_prev, h_curr, h_prev]
  
  have h_fail : ∀ k, 1 ≤ k → k ≤ curr - prev - 1 → listNth (vanEck curr) ((vanEck curr).length - 1) ≠ listNth (vanEck curr) (prev + k) := by
    intro k hk1 h_le
    have h_len1 : (vanEck curr).length - 1 = curr := by
      have h_len : (vanEck curr).length = curr + 1 := vanEckLength curr
      omega
    rw [h_len1]
    have hd_curr : listNth (vanEck curr) curr = vanEckNthTerm curr := rfl
    have hd_prevk : listNth (vanEck curr) (prev + k) = vanEckNthTerm (prev + k) := by
      exact VanEck_deterministic curr (prev + k) (by omega)
    rw [hd_curr, hd_prevk, h_curr]
    exact fun h => h_between (prev + k) (by omega) (by omega) h.symm
  
  have h_ms := matchSearch_eq_dist (vanEck curr) prev (curr - prev - 1) h_match h_fail
  have h_sub : prev + (curr - prev - 1) + 1 = curr := by omega
  rw [h_sub] at h_ms
  have h_gap := vanEck_is_gap (curr + 1) (by omega)
  have h_len2 : (vanEck curr).length - 1 - prev = curr - prev := by
    have h_len : (vanEck curr).length = curr + 1 := vanEckLength curr
    omega
  rw [h_len2] at h_ms
  have h_sub_c : curr + 1 - 1 = curr := rfl
  rw [h_sub_c] at h_gap
  rw [h_ms] at h_gap
  have h_val : vanEckNthTerm (curr + 1) = curr - prev := h_gap
  
  have h_curr1_gt : curr + 1 > N := by omega
  have h_or := h_odds (curr + 1) h_curr1_gt
  have h_odd : (curr - prev) % 2 = 1 := by
    cases h_or with
    | inl h_zero =>
      have hc : curr - prev = 0 := by
        rw [← h_val]
        exact h_zero
      omega
    | inr h_is_odd =>
      rw [← h_val]
      exact h_is_odd
  omega
}

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
