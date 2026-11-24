import VanEck
import ImpossiblePatterns
import LimSup
import FinishedSurjLemmas
import SurjectivityLemmas
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

/-!
Lemma `zero_gap_even` is mathematically false under the current assumptions and cannot be proved.
It is therefore removed (commented out) to preserve consistency of the development.
-/

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

/--
Inductive step for prefix exhaustion: since `m ↦ m - a(m)` is injective on positive
terms (`vanEck_idx_sub_val_unique`), at most one index `m > N_B` can have `m - a(m) = B + 2`.
-/
lemma lookback_prefix_exhaustion_step (B N_B : ℕ) (hNB_gt : N_B > B)
    (hNB : ∀ m > N_B, vanEckNthTerm m = 0 ∨ (m - 1) - vanEckNthTerm m > B) :
    ∃ N' > B + 1, ∀ m > N', vanEckNthTerm m = 0 ∨ (m - 1) - vanEckNthTerm m > B + 1 := by {
  by_cases h_ex : ∃ m₀ > N_B, vanEckNthTerm m₀ > 0 ∧ m₀ - vanEckNthTerm m₀ = B + 2
  · rcases h_ex with ⟨m₀, hm₀_gt, hm₀_pos, hm₀_eq⟩
    refine ⟨m₀ + 1, ?_, ?_⟩
    · omega
    · intro m hm
      by_cases hz : vanEckNthTerm m = 0
      · exact Or.inl hz
      · right
        have h_gt_B : (m - 1) - vanEckNthTerm m > B := by {
          rcases hNB m (by { omega }) with h0 | hgt
          · exact False.elim (hz h0)
          · exact hgt
        }
        have h_neq := vanEck_idx_sub_val_unique m₀ m hm₀_pos (by { omega })
        rw [hm₀_eq] at h_neq
        omega
  · refine ⟨N_B + 1, ?_, ?_⟩
    · omega
    · intro m hm
      by_cases hz : vanEckNthTerm m = 0
      · exact Or.inl hz
      · right
        have hm_pos : vanEckNthTerm m > 0 := Nat.pos_of_ne_zero hz
        have h_gt_B : (m - 1) - vanEckNthTerm m > B := by {
          rcases hNB m (by { omega }) with h0 | hgt
          · exact False.elim (hz h0)
          · exact hgt
        }
        have h_le : vanEckNthTerm m ≤ m - 1 := a_le_idx_minus_one (by { omega }) hm_pos
        have h_not_eq : m - vanEckNthTerm m ≠ B + 2 := by {
          intro hc
          exact h_ex ⟨m, by { omega }, hm_pos, hc⟩
        }
        omega
}

/--
Unconditional Prefix-Exhaustion Theorem: for any bound `B`, there exists `N' > B` such
that every positive term `a(m)` after `N'` looks back strictly past `B`.
-/
lemma lookback_prefix_exhaustion (B : ℕ) :
    ∃ N' > B, ∀ m > N', vanEckNthTerm m = 0 ∨ (m - 1) - vanEckNthTerm m > B := by {
  induction B with
  | zero =>
    refine ⟨2, ?_, ?_⟩
    · decide
    · intro m hm
      by_cases hz : vanEckNthTerm m = 0
      · exact Or.inl hz
      · right
        have hm_pos : vanEckNthTerm m > 0 := Nat.pos_of_ne_zero hz
        have h_le : vanEckNthTerm m ≤ m - 1 := a_le_idx_minus_one (by { omega }) hm_pos
        have h2_pos : vanEckNthTerm 2 > 0 := by { decide }
        have h_neq := vanEck_idx_sub_val_unique 2 m h2_pos hm
        have h2_val : 2 - vanEckNthTerm 2 = 1 := rfl
        rw [h2_val] at h_neq
        omega
  | succ B ih =>
    rcases ih with ⟨N_B, hNB_gt, hNB⟩
    exact lookback_prefix_exhaustion_step B N_B hNB_gt hNB
}

/--
Under `OnlyOddsAndZerosAfter N`, the lookback predecessor `(m - 1) - a(m)` of every
nonzero term `a(m)` (`m > N`) has the exact same index parity as `m`.
-/
lemma only_odds_lookback_parity (N m : ℕ) (h_odds : OnlyOddsAndZerosAfter N)
    (hm_gt : N < m) (hm_nz : vanEckNthTerm m ≠ 0) :
    ((m - 1) - vanEckNthTerm m) % 2 = m % 2 := by {
  have hm_ge_two : m ≥ 2 := by {
    by_contra hc
    interval_cases m
    · exact hm_nz rfl
    · exact hm_nz rfl
  }
  have hm_odd : vanEckNthTerm m % 2 = 1 := by {
    rcases h_odds m hm_gt with h0 | h1
    · exact False.elim (hm_nz h0)
    · exact h1
  }
  have hm_pos : vanEckNthTerm m > 0 := Nat.pos_of_ne_zero hm_nz
  have h_le : vanEckNthTerm m ≤ m - 1 := a_le_idx_minus_one hm_ge_two hm_pos
  omega
}

/--
Under `OnlyOddsAndZerosAfter N`, consecutive zeros `0 < z_a < z_b` past `N` are separated
by an odd distance of at least `3`.
-/
lemma only_odds_zero_gap_ge_three (N : ℕ) (h_odds : OnlyOddsAndZerosAfter N)
    (z_a z_b : ℕ) (hz_a_pos : z_a > 0) (hz_a : vanEckNthTerm z_a = 0)
    (hz_b : vanEckNthTerm z_b = 0) (hz_lt : z_a < z_b)
    (h_between : ∀ i, z_a < i → i < z_b → vanEckNthTerm i ≠ 0)
    (h_bounds : N < z_a) :
    z_b - z_a ≥ 3 ∧ (z_b - z_a) % 2 = 1 := by {
  have h_par := zero_gap_odd N h_odds z_a z_b hz_a hz_b hz_lt h_between h_bounds
  have h_odd : (z_b - z_a) % 2 = 1 := by { omega }
  have h_ne_one : z_b - z_a ≠ 1 := by {
    intro h1
    have hzb_eq : z_b = (z_a - 1) + 2 := by { omega }
    have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new (z_a - 1)
    rw [← hzb_eq] at h_iff
    have h_new := h_iff.mp hz_b
    have h_sub : z_a - 1 + 1 = z_a := by { omega }
    rw [h_sub] at h_new
    have h0_neq := h_new 0 hz_a_pos
    have h0_zero : vanEckNthTerm 0 = 0 := rfl
    rw [h0_zero, hz_a] at h0_neq
    exact h0_neq rfl
  }
  exact ⟨by { omega }, h_odd⟩
}

/--
Birth-Parity Trap: under `OnlyOddsAndZerosAfter N`, the brand-new value `a(z_1 - 1)`
preceding any zero `z_1 > N` (`z_1 ≥ 2`) must make its second appearance `r` at the
same index parity as `z_1` (`r % 2 = z_1 % 2`).
-/
lemma only_odds_new_val_second_occ_parity (N z_1 r : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz1_ge : z_1 ≥ 2)
    (hz1_gt : N < z_1) (hz1_zero : vanEckNthTerm z_1 = 0)
    (hr_gt : z_1 - 1 < r) (hr_eq : vanEckNthTerm r = vanEckNthTerm (z_1 - 1))
    (h_between : ∀ i, z_1 - 1 < i → i < r → vanEckNthTerm i ≠ vanEckNthTerm (z_1 - 1)) :
    r % 2 = z_1 % 2 := by {
  have hz1_prev_ne_zero : vanEckNthTerm (z_1 - 1) ≠ 0 := by {
    intro hc
    have h_eq : z_1 = (z_1 - 2) + 2 := by { omega }
    have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new (z_1 - 2)
    rw [← h_eq] at h_iff
    have h_new := h_iff.mp hz1_zero
    have h_sub : z_1 - 2 + 1 = z_1 - 1 := by { omega }
    rw [h_sub] at h_new
    have h0_neq := h_new 0 (by { omega })
    have h0_zero : vanEckNthTerm 0 = 0 := rfl
    rw [h0_zero, hc] at h0_neq
    exact h0_neq rfl
  }
  have hr_ne_z1 : r ≠ z_1 := by {
    intro hc
    rw [hc, hz1_zero] at hr_eq
    exact hz1_prev_ne_zero hr_eq.symm
  }
  have hr_gt_N : N < r := by { omega }
  have h_alt := parity_alternation N h_odds (vanEckNthTerm (z_1 - 1)) r (z_1 - 1)
    hr_eq rfl hr_gt h_between hr_gt_N
  omega
}

/--
Exact lookback gap evaluation between any two consecutive occurrences `prev < curr`
of the same value in the Van Eck sequence.
-/
lemma strict_occurrence_gap_eq (prev curr : ℕ)
    (h_eq : vanEckNthTerm curr = vanEckNthTerm prev) (h_lt : prev < curr)
    (h_between : ∀ i, prev < i → i < curr → vanEckNthTerm i ≠ vanEckNthTerm curr) :
    vanEckNthTerm (curr + 1) = curr - prev := by {
  have h_len : (vanEck curr).length = curr + 1 := vanEckLength curr
  have h_len1 : (vanEck curr).length - 1 = curr := by { omega }
  have h_match : listNth (vanEck curr) ((vanEck curr).length - 1) =
      listNth (vanEck curr) prev := by {
    rw [h_len1]
    have hd_curr : listNth (vanEck curr) curr = vanEckNthTerm curr := rfl
    have hd_prev : listNth (vanEck curr) prev = vanEckNthTerm prev :=
      VanEck_deterministic curr prev (Nat.le_of_lt h_lt)
    rw [hd_curr, hd_prev, h_eq]
  }
  have h_fail : ∀ k, 1 ≤ k → k ≤ curr - prev - 1 →
      listNth (vanEck curr) ((vanEck curr).length - 1) ≠
        listNth (vanEck curr) (prev + k) := by {
    intro k hk1 hk_le
    rw [h_len1]
    have hd_curr : listNth (vanEck curr) curr = vanEckNthTerm curr := rfl
    have hd_prevk : listNth (vanEck curr) (prev + k) = vanEckNthTerm (prev + k) :=
      VanEck_deterministic curr (prev + k) (by { omega })
    rw [hd_curr, hd_prevk]
    exact fun h => h_between (prev + k) (by { omega }) (by { omega }) h.symm
  }
  have h_ms := matchSearch_eq_dist (vanEck curr) prev (curr - prev - 1) h_match h_fail
  have h_sub : prev + (curr - prev - 1) + 1 = curr := by { omega }
  have h_len2 : (vanEck curr).length - 1 - prev = curr - prev := by { omega }
  rw [h_sub, h_len2] at h_ms
  have h_gap := vanEck_is_gap (curr + 1) (by { omega })
  have h_sub_c : curr + 1 - 1 = curr := rfl
  rw [h_sub_c, h_ms] at h_gap
  exact h_gap
}

/--
Double Gap-3 Forcing Lemma: two consecutive zero-gaps of `3` (`z_1 = z_0 + 3` and
`z_2 = z_1 + 3`) deterministically force `[3, 3, 1]` at `(z_2 + 1, z_2 + 2, z_2 + 3)`.
-/
lemma double_gap_three_forces_double_three_one (z_0 z_1 z_2 : ℕ)
    (hz0 : vanEckNthTerm z_0 = 0) (hz1 : vanEckNthTerm z_1 = 0)
    (hz2 : vanEckNthTerm z_2 = 0) (h_g1 : z_1 = z_0 + 3) (h_g2 : z_2 = z_1 + 3)
    (h_bet1 : ∀ i, z_0 < i → i < z_1 → vanEckNthTerm i ≠ 0)
    (h_bet2 : ∀ i, z_1 < i → i < z_2 → vanEckNthTerm i ≠ 0) :
    vanEckNthTerm (z_2 + 1) = 3 ∧
      vanEckNthTerm (z_2 + 2) = 3 ∧
      vanEckNthTerm (z_2 + 3) = 1 := by {
  have ha_z1_1 : vanEckNthTerm (z_1 + 1) = 3 := by {
    have hg := gap_between_zeros z_1 z_0 hz1 (by { omega }) hz0 (by { omega }) h_bet1
    omega
  }
  have ha_z2_1 : vanEckNthTerm (z_2 + 1) = 3 := by {
    have hg := gap_between_zeros z_2 z_1 hz2 (by { omega }) hz1 (by { omega }) h_bet2
    omega
  }
  have ha_z1_2_ne : vanEckNthTerm (z_1 + 2) ≠ 3 := by {
    have hz2_eq : z_2 = (z_1 + 1) + 2 := by { omega }
    have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new (z_1 + 1)
    rw [← hz2_eq] at h_iff
    have h_new := h_iff.mp hz2 (z_1 + 1) (by { omega })
    rw [ha_z1_1] at h_new
    exact Ne.symm h_new
  }
  have h_between_3 : ∀ i, z_1 + 1 < i → i < z_2 + 1 →
      vanEckNthTerm i ≠ vanEckNthTerm (z_2 + 1) := by {
    intro i hi1 hi2
    rw [ha_z2_1]
    rcases (by { omega } : i = z_1 + 2 ∨ i = z_2) with rfl | rfl
    · exact ha_z1_2_ne
    · rw [hz2]
      decide
  }
  have ha_z2_2 : vanEckNthTerm (z_2 + 2) = 3 := by {
    have h_dist := strict_occurrence_gap_eq (z_1 + 1) (z_2 + 1)
      (by { rw [ha_z2_1, ha_z1_1] }) (by { omega }) h_between_3
    have h_idx : z_2 + 1 + 1 = z_2 + 2 := rfl
    rw [h_idx] at h_dist
    rw [h_dist]
    omega
  }
  have ha_z2_3 : vanEckNthTerm (z_2 + 3) = 1 :=
    vanEck_consecutive_eq_implies_next_one (z_2 + 1) (by { rw [ha_z2_1, ha_z2_2] })
  exact ⟨ha_z2_1, ha_z2_2, ha_z2_3⟩
}

/--
Under `OnlyOddsAndZerosAfter N`, three consecutive zero-gaps of `3` are impossible:
after two consecutive zero-gaps of `3`, the next zero-gap is at least `5`.
-/
lemma only_odds_no_triple_gap_three (N z_0 z_1 z_2 z_3 : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz0_gt : N < z_0)
    (hz0 : vanEckNthTerm z_0 = 0) (hz1 : vanEckNthTerm z_1 = 0)
    (hz2 : vanEckNthTerm z_2 = 0) (hz3 : vanEckNthTerm z_3 = 0)
    (h_g1 : z_1 = z_0 + 3) (h_g2 : z_2 = z_1 + 3) (hz2_lt : z_2 < z_3)
    (h_bet1 : ∀ i, z_0 < i → i < z_1 → vanEckNthTerm i ≠ 0)
    (h_bet2 : ∀ i, z_1 < i → i < z_2 → vanEckNthTerm i ≠ 0)
    (h_bet3 : ∀ i, z_2 < i → i < z_3 → vanEckNthTerm i ≠ 0) :
    z_3 - z_2 ≥ 5 := by {
  have h_double := double_gap_three_forces_double_three_one z_0 z_1 z_2
    hz0 hz1 hz2 h_g1 h_g2 h_bet1 h_bet2
  have h_gap3 := only_odds_zero_gap_ge_three N h_odds z_2 z_3
    (by { omega }) hz2 hz3 hz2_lt h_bet3 (by { omega })
  have hz3_ne : z_3 ≠ z_2 + 3 := by {
    intro hc
    rw [hc] at hz3
    rw [h_double.2.2] at hz3
    exact Nat.one_ne_zero hz3
  }
  omega
}

/--
Across two consecutive zero-gaps of `3` (`z_0 ≥ 4`, `z_1 = z_0 + 3`, `z_2 = z_1 + 3`),
the value `1` cannot appear anywhere in the 10-term window `[z_0 - 1, z_2 + 2]`.
-/
lemma double_gap_three_no_one_in_window (z_0 z_1 z_2 : ℕ)
    (hz0_ge : z_0 ≥ 4) (hz0 : vanEckNthTerm z_0 = 0)
    (hz1 : vanEckNthTerm z_1 = 0) (hz2 : vanEckNthTerm z_2 = 0)
    (h_g1 : z_1 = z_0 + 3) (h_g2 : z_2 = z_1 + 3)
    (h_bet1 : ∀ i, z_0 < i → i < z_1 → vanEckNthTerm i ≠ 0)
    (h_bet2 : ∀ i, z_1 < i → i < z_2 → vanEckNthTerm i ≠ 0) :
    ∀ k, z_0 - 1 ≤ k → k ≤ z_2 + 2 → vanEckNthTerm k ≠ 1 := by {
  have h_double := double_gap_three_forces_double_three_one z_0 z_1 z_2
    hz0 hz1 hz2 h_g1 h_g2 h_bet1 h_bet2
  have ha_z1_1 : vanEckNthTerm (z_1 + 1) = 3 := by {
    have hg := gap_between_zeros z_1 z_0 hz1 (by { omega }) hz0 (by { omega }) h_bet1
    omega
  }
  have ha_z0_1 : vanEckNthTerm (z_0 + 1) ≥ 2 := by {
    let zp := lastZero (z_0 - 1)
    have hzp_zero : vanEckNthTerm zp = 0 := vanEck_lastZero_is_zero (z_0 - 1)
    have hzp_le : zp ≤ z_0 - 1 := lastZero_le (z_0 - 1)
    have h_bet0 : ∀ i, zp < i → i < z_0 → vanEckNthTerm i ≠ 0 :=
      fun i hi1 hi2 => no_zero_after_lastZero (z_0 - 1) i hi1 (by { omega })
    have hg0 := gap_between_zeros z_0 zp hz0 (by { omega }) hzp_zero (by { omega }) h_bet0
    by_cases hzp0 : zp = 0
    · omega
    · have h_ge2 := consecutive_zeros_gap_ge_two z_0 zp (by { omega }) hz0 hzp_zero (by { omega })
      omega
  }
  intro k hk_lo hk_hi
  by_cases hk0 : k = z_0 - 1
  · rw [hk0]
    exact pre_zero_ne_prior_val z_0 2 hz0 (by { omega }) (by { omega })
  · by_cases hk1 : k = z_1 - 1
    · rw [hk1]
      exact pre_zero_ne_prior_val z_1 2 hz1 (by { omega }) (by { omega })
    · by_cases hk2 : k = z_2 - 1
      · rw [hk2]
        exact pre_zero_ne_prior_val z_2 2 hz2 (by { omega }) (by { omega })
      · rcases (by { omega } : k = z_0 ∨ k = z_0 + 1 ∨ k = z_1 ∨ k = z_1 + 1 ∨
            k = z_2 ∨ k = z_2 + 1 ∨ k = z_2 + 2) with
          rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> omega
}

/--
After two consecutive zero-gaps of `3` (`z_0 ≥ 4`, `z_1 = z_0 + 3`, `z_2 = z_1 + 3`),
the term `a(z_2 + 4)` immediately following `[3, 3, 1]` is unconditionally at least `11`.
-/
lemma double_gap_three_fourth_term_ge_eleven (z_0 z_1 z_2 : ℕ)
    (hz0_ge : z_0 ≥ 4) (hz0 : vanEckNthTerm z_0 = 0)
    (hz1 : vanEckNthTerm z_1 = 0) (hz2 : vanEckNthTerm z_2 = 0)
    (h_g1 : z_1 = z_0 + 3) (h_g2 : z_2 = z_1 + 3)
    (h_bet1 : ∀ i, z_0 < i → i < z_1 → vanEckNthTerm i ≠ 0)
    (h_bet2 : ∀ i, z_1 < i → i < z_2 → vanEckNthTerm i ≠ 0) :
    vanEckNthTerm (z_2 + 4) ≥ 11 := by {
  have h_double := double_gap_three_forces_double_three_one z_0 z_1 z_2
    hz0 hz1 hz2 h_g1 h_g2 h_bet1 h_bet2
  have h_no_one := double_gap_three_no_one_in_window z_0 z_1 z_2
    hz0_ge hz0 hz1 hz2 h_g1 h_g2 h_bet1 h_bet2
  have h_nz : vanEckNthTerm (z_2 + 4) ≠ 0 := by {
    intro hc
    have h_ne := pre_zero_ne_prior_val (z_2 + 4) 2 hc (by { omega }) (by { omega })
    have h_idx : z_2 + 4 - 1 = z_2 + 3 := rfl
    rw [h_idx, h_double.2.2] at h_ne
    exact h_ne rfl
  }
  have h_pos : vanEckNthTerm (z_2 + 4) > 0 := Nat.pos_of_ne_zero h_nz
  have h_gap :=
    pos_value_implies_gap (z_2 + 4) (vanEckNthTerm (z_2 + 4)) (by { omega }) rfl h_pos
  have h_sub : z_2 + 4 - 1 = z_2 + 3 := rfl
  rw [h_sub, h_double.2.2] at h_gap
  by_contra h_lt
  exact h_no_one (z_2 + 3 - vanEckNthTerm (z_2 + 4)) (by { omega }) (by { omega }) h_gap.2
}

/--
Under `OnlyOddsAndZerosAfter N` (`z_0 ≥ 2`, `N < z_0`), after two zero-gaps of `3`,
birth-parity excludes the first newly born value `a(z_1 - 1)` from the entire 8-term
block `[z_1, z_2 + 4]`.
-/
lemma only_odds_double_gap_three_first_birth_excluded (N z_0 z_1 z_2 : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz0_ge : z_0 ≥ 2) (hz0_gt : N < z_0)
    (hz0 : vanEckNthTerm z_0 = 0) (hz1 : vanEckNthTerm z_1 = 0)
    (hz2 : vanEckNthTerm z_2 = 0) (h_g1 : z_1 = z_0 + 3) (h_g2 : z_2 = z_1 + 3)
    (h_bet1 : ∀ i, z_0 < i → i < z_1 → vanEckNthTerm i ≠ 0)
    (h_bet2 : ∀ i, z_1 < i → i < z_2 → vanEckNthTerm i ≠ 0) :
    ∀ i, z_1 - 1 < i → i ≤ z_2 + 4 → vanEckNthTerm i ≠ vanEckNthTerm (z_1 - 1) := by {
  have h_double := double_gap_three_forces_double_three_one z_0 z_1 z_2
    hz0 hz1 hz2 h_g1 h_g2 h_bet1 h_bet2
  have ha_z1_1 : vanEckNthTerm (z_1 + 1) = 3 := by {
    have hg := gap_between_zeros z_1 z_0 hz1 (by { omega }) hz0 (by { omega }) h_bet1
    omega
  }
  have hu1_ne0 : vanEckNthTerm (z_1 - 1) ≠ 0 :=
    pre_zero_ne_prior_val z_1 0 hz1 (by { omega }) (by { omega })
  have hu1_ne1 : vanEckNthTerm (z_1 - 1) ≠ 1 :=
    pre_zero_ne_prior_val z_1 2 hz1 (by { omega }) (by { omega })
  have hu1_ne3 : vanEckNthTerm (z_1 - 1) ≠ 3 := by {
    intro hc
    have h_par := only_odds_new_val_second_occ_parity N z_1 (z_1 + 1) h_odds
      (by { omega }) (by { omega }) hz1 (by { omega }) (by { rw [ha_z1_1, hc] })
      (by { intro j hj1 hj2; have hj : j = z_1 := by { omega }; rw [hj, hz1, hc]; decide })
    omega
  }
  have hu2_ne_u1 : vanEckNthTerm (z_2 - 1) ≠ vanEckNthTerm (z_1 - 1) :=
    pre_zero_ne_prior_val z_2 (z_1 - 1) hz2 (by { omega }) (by { omega })
  have h_le3 : ∀ j, z_1 - 1 < j → j ≤ z_2 + 3 →
      vanEckNthTerm j ≠ vanEckNthTerm (z_1 - 1) := by {
    intro j hj1 hj2
    by_cases hj_u2 : j = z_2 - 1
    · rw [hj_u2]
      exact hu2_ne_u1
    · rcases (by { omega } : j = z_1 ∨ j = z_1 + 1 ∨ j = z_2 ∨ j = z_2 + 1 ∨
          j = z_2 + 2 ∨ j = z_2 + 3) with rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  }
  intro i hi1 hi2
  by_cases hi_le3 : i ≤ z_2 + 3
  · exact h_le3 i hi1 hi_le3
  · intro hc
    have hi_eq : i = z_2 + 4 := by { omega }
    rw [hi_eq] at hc
    have h_par := only_odds_new_val_second_occ_parity N z_1 (z_2 + 4) h_odds
      (by { omega }) (by { omega }) hz1 (by { omega }) hc
      (fun j hj1 hj2 => h_le3 j hj1 (by { omega }))
    omega
}

/--
Unconditional second-birth lookback after two zero-gaps of `3`: `a(z_2 - 1)` is excluded
from `[z_2, z_2 + 3]`, and if `a(z_2 + 4) = a(z_2 - 1)` then `strict_occurrence_gap_eq`
deterministically forces `a(z_2 + 5) = 5`.
-/
lemma double_gap_three_second_birth_forces_five (z_0 z_1 z_2 : ℕ)
    (hz0 : vanEckNthTerm z_0 = 0) (hz1 : vanEckNthTerm z_1 = 0)
    (hz2 : vanEckNthTerm z_2 = 0) (h_g1 : z_1 = z_0 + 3) (h_g2 : z_2 = z_1 + 3)
    (h_bet1 : ∀ i, z_0 < i → i < z_1 → vanEckNthTerm i ≠ 0)
    (h_bet2 : ∀ i, z_1 < i → i < z_2 → vanEckNthTerm i ≠ 0) :
    (∀ i, z_2 - 1 < i → i ≤ z_2 + 3 → vanEckNthTerm i ≠ vanEckNthTerm (z_2 - 1)) ∧
      (vanEckNthTerm (z_2 + 4) = vanEckNthTerm (z_2 - 1) →
        vanEckNthTerm (z_2 + 5) = 5) := by {
  have h_double := double_gap_three_forces_double_three_one z_0 z_1 z_2
    hz0 hz1 hz2 h_g1 h_g2 h_bet1 h_bet2
  have ha_z1_1 : vanEckNthTerm (z_1 + 1) = 3 := by {
    have hg := gap_between_zeros z_1 z_0 hz1 (by { omega }) hz0 (by { omega }) h_bet1
    omega
  }
  have hu2_ne0 : vanEckNthTerm (z_2 - 1) ≠ 0 :=
    pre_zero_ne_prior_val z_2 0 hz2 (by { omega }) (by { omega })
  have hu2_ne1 : vanEckNthTerm (z_2 - 1) ≠ 1 :=
    pre_zero_ne_prior_val z_2 2 hz2 (by { omega }) (by { omega })
  have hu2_ne3 : vanEckNthTerm (z_2 - 1) ≠ 3 := by {
    have h_ne := pre_zero_ne_prior_val z_2 (z_1 + 1) hz2 (by { omega }) (by { omega })
    rw [ha_z1_1] at h_ne
    exact h_ne
  }
  have h_excl : ∀ i, z_2 - 1 < i → i ≤ z_2 + 3 →
      vanEckNthTerm i ≠ vanEckNthTerm (z_2 - 1) := by {
    intro i hi1 hi2
    rcases (by { omega } : i = z_2 ∨ i = z_2 + 1 ∨ i = z_2 + 2 ∨ i = z_2 + 3) with
      rfl | rfl | rfl | rfl <;> omega
  }
  refine ⟨h_excl, ?_⟩
  intro h_hit
  have h_dist := strict_occurrence_gap_eq (z_2 - 1) (z_2 + 4) h_hit (by { omega })
    (fun i hi1 hi2 => by { rw [h_hit]; exact h_excl i hi1 (by { omega }) })
  have h_idx : z_2 + 4 + 1 = z_2 + 5 := rfl
  rw [h_idx] at h_dist
  omega
}

/--
Second-birth tracking after two zero-gaps of `3`: under `OnlyOddsAndZerosAfter N`, if
`a(z_2 + 4) = a(z_2 - 1)` then `a(z_2 + 5) = 5` and the next zero gap is at least `7`.
-/
lemma only_odds_double_gap_three_second_birth_step (N z_0 z_1 z_2 z_3 : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz0_gt : N < z_0)
    (hz0 : vanEckNthTerm z_0 = 0) (hz1 : vanEckNthTerm z_1 = 0)
    (hz2 : vanEckNthTerm z_2 = 0) (hz3 : vanEckNthTerm z_3 = 0)
    (h_g1 : z_1 = z_0 + 3) (h_g2 : z_2 = z_1 + 3) (hz2_lt : z_2 < z_3)
    (h_bet1 : ∀ i, z_0 < i → i < z_1 → vanEckNthTerm i ≠ 0)
    (h_bet2 : ∀ i, z_1 < i → i < z_2 → vanEckNthTerm i ≠ 0)
    (h_bet3 : ∀ i, z_2 < i → i < z_3 → vanEckNthTerm i ≠ 0) :
    (∀ i, z_2 - 1 < i → i ≤ z_2 + 3 → vanEckNthTerm i ≠ vanEckNthTerm (z_2 - 1)) ∧
      (vanEckNthTerm (z_2 + 4) = vanEckNthTerm (z_2 - 1) →
        vanEckNthTerm (z_2 + 5) = 5 ∧ z_3 - z_2 ≥ 7) := by {
  have h_base := double_gap_three_second_birth_forces_five z_0 z_1 z_2
    hz0 hz1 hz2 h_g1 h_g2 h_bet1 h_bet2
  refine ⟨h_base.1, ?_⟩
  intro h_hit
  have ha_z2_5 : vanEckNthTerm (z_2 + 5) = 5 := h_base.2 h_hit
  have h_ge5 := only_odds_no_triple_gap_three N z_0 z_1 z_2 z_3 h_odds hz0_gt
    hz0 hz1 hz2 hz3 h_g1 h_g2 hz2_lt h_bet1 h_bet2 h_bet3
  have h_odd := (only_odds_zero_gap_ge_three N h_odds z_2 z_3
    (by { omega }) hz2 hz3 hz2_lt h_bet3 (by { omega })).2
  have hz3_ne5 : z_3 ≠ z_2 + 5 := by {
    intro hc
    rw [hc, ha_z2_5] at hz3
    omega
  }
  exact ⟨ha_z2_5, by { omega }⟩
}

/--
After zero-gap pattern `(5, 3, 3)` (`z_0 = z_prev + 5`, `z_1 = z_0 + 3`, `z_2 = z_1 + 3`,
`z_0 ≥ 13`, `N < z_0`), `a(z_2 + 4)` cannot equal `a(z_2 - 1)`, since otherwise
`a(z_2 + 5) = 5` would match `a(z_0 + 1) = 5` at even distance `10`.
-/
lemma only_odds_five_three_three_excludes_second_birth (N z_prev z_0 z_1 z_2 : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz0_ge : z_0 ≥ 13) (hz0_gt : N < z_0)
    (hzp : vanEckNthTerm z_prev = 0) (hz0 : vanEckNthTerm z_0 = 0)
    (hz1 : vanEckNthTerm z_1 = 0) (hz2 : vanEckNthTerm z_2 = 0)
    (h_g0 : z_0 = z_prev + 5) (h_g1 : z_1 = z_0 + 3) (h_g2 : z_2 = z_1 + 3)
    (h_bet0 : ∀ i, z_prev < i → i < z_0 → vanEckNthTerm i ≠ 0)
    (h_bet1 : ∀ i, z_0 < i → i < z_1 → vanEckNthTerm i ≠ 0)
    (h_bet2 : ∀ i, z_1 < i → i < z_2 → vanEckNthTerm i ≠ 0) :
    vanEckNthTerm (z_2 + 4) ≠ vanEckNthTerm (z_2 - 1) := by {
  intro h_hit
  have h_double := double_gap_three_forces_double_three_one z_0 z_1 z_2
    hz0 hz1 hz2 h_g1 h_g2 h_bet1 h_bet2
  have ha_z0_1 : vanEckNthTerm (z_0 + 1) = 5 := by {
    have hg := gap_between_zeros z_0 z_prev hz0 (by { omega }) hzp (by { omega }) h_bet0
    omega
  }
  have ha_z1_1 : vanEckNthTerm (z_1 + 1) = 3 := by {
    have hg := gap_between_zeros z_1 z_0 hz1 (by { omega }) hz0 (by { omega }) h_bet1
    omega
  }
  have ha11 : vanEckNthTerm 11 = 5 := by { decide +kernel }
  have hu1_ne5 : vanEckNthTerm (z_1 - 1) ≠ 5 := by {
    rw [← ha11]
    exact pre_zero_ne_prior_val z_1 11 hz1 (by { omega }) (by { omega })
  }
  have hu2_ne5 : vanEckNthTerm (z_2 - 1) ≠ 5 := by {
    rw [← ha11]
    exact pre_zero_ne_prior_val z_2 11 hz2 (by { omega }) (by { omega })
  }
  have ha_z2_5 : vanEckNthTerm (z_2 + 5) = 5 :=
    (double_gap_three_second_birth_forces_five z_0 z_1 z_2
      hz0 hz1 hz2 h_g1 h_g2 h_bet1 h_bet2).2 h_hit
  have h_no5 : ∀ i, z_0 + 1 < i → i < z_2 + 5 →
      vanEckNthTerm i ≠ vanEckNthTerm (z_2 + 5) := by {
    intro i hi1 hi2
    rw [ha_z2_5]
    by_cases hi_u1 : i = z_1 - 1
    · rw [hi_u1]
      exact hu1_ne5
    · by_cases hi_u2 : i = z_2 - 1
      · rw [hi_u2]
        exact hu2_ne5
      · by_cases hi_4 : i = z_2 + 4
        · rw [hi_4, h_hit]
          exact hu2_ne5
        · rcases (by { omega } : i = z_1 ∨ i = z_1 + 1 ∨ i = z_2 ∨
              i = z_2 + 1 ∨ i = z_2 + 2 ∨ i = z_2 + 3) with
            rfl | rfl | rfl | rfl | rfl | rfl <;> omega
  }
  have ha_z2_6 : vanEckNthTerm (z_2 + 6) = 10 := by {
    have h_dist := strict_occurrence_gap_eq (z_0 + 1) (z_2 + 5)
      (by { rw [ha_z2_5, ha_z0_1] }) (by { omega }) h_no5
    have h_idx : z_2 + 5 + 1 = z_2 + 6 := rfl
    rw [h_idx] at h_dist
    omega
  }
  rcases h_odds (z_2 + 6) (by { omega }) with h0 | hodd <;> omega
}

/--
Post-`(3, 3)` Gap Birth-Parity Exclusion: under `OnlyOddsAndZerosAfter N` (`z_0 ≥ 2`,
`N < z_0`), if `a(z_1 - 1)` does not occur in `(z_2 + 4, z_3 - 1)`, then the next zero
gap `z_3 - z_2` cannot equal `a(z_1 - 1)`.
-/
lemma only_odds_post_double_three_gap_ne_first_birth (N z_0 z_1 z_2 z_3 : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz0_ge : z_0 ≥ 2) (hz0_gt : N < z_0)
    (hz0 : vanEckNthTerm z_0 = 0) (hz1 : vanEckNthTerm z_1 = 0)
    (hz2 : vanEckNthTerm z_2 = 0) (hz3 : vanEckNthTerm z_3 = 0)
    (h_g1 : z_1 = z_0 + 3) (h_g2 : z_2 = z_1 + 3) (hz2_lt : z_2 < z_3)
    (h_bet1 : ∀ i, z_0 < i → i < z_1 → vanEckNthTerm i ≠ 0)
    (h_bet2 : ∀ i, z_1 < i → i < z_2 → vanEckNthTerm i ≠ 0)
    (h_bet3 : ∀ i, z_2 < i → i < z_3 → vanEckNthTerm i ≠ 0)
    (h_no_u1 : ∀ i, z_2 + 4 < i → i < z_3 - 1 →
      vanEckNthTerm i ≠ vanEckNthTerm (z_1 - 1)) :
    z_3 - z_2 ≠ vanEckNthTerm (z_1 - 1) := by {
  intro h_gap_eq
  have h_ge5 := only_odds_no_triple_gap_three N z_0 z_1 z_2 z_3 h_odds hz0_gt
    hz0 hz1 hz2 hz3 h_g1 h_g2 hz2_lt h_bet1 h_bet2 h_bet3
  have h_odd := (only_odds_zero_gap_ge_three N h_odds z_2 z_3
    (by { omega }) hz2 hz3 hz2_lt h_bet3 (by { omega })).2
  have ha_z3_1 : vanEckNthTerm (z_3 + 1) = vanEckNthTerm (z_1 - 1) := by {
    rw [gap_between_zeros z_3 z_2 hz3 (by { omega }) hz2 hz2_lt h_bet3]
    exact h_gap_eq
  }
  have h_excl := only_odds_double_gap_three_first_birth_excluded N z_0 z_1 z_2
    h_odds hz0_ge hz0_gt hz0 hz1 hz2 h_g1 h_g2 h_bet1 h_bet2
  have hu1_ne0 : vanEckNthTerm (z_1 - 1) ≠ 0 :=
    pre_zero_ne_prior_val z_1 0 hz1 (by { omega }) (by { omega })
  have h_bet_u1 : ∀ i, z_1 - 1 < i → i < z_3 + 1 →
      vanEckNthTerm i ≠ vanEckNthTerm (z_1 - 1) := by {
    intro i hi1 hi2
    by_cases hi_le : i ≤ z_2 + 4
    · exact h_excl i hi1 hi_le
    · by_cases hi_lt : i < z_3 - 1
      · exact h_no_u1 i (by { omega }) hi_lt
      · by_cases hi_z31 : i = z_3 - 1
        · rw [hi_z31]
          exact pre_zero_ne_prior_val z_3 (z_1 - 1) hz3 (by { omega }) (by { omega })
        · have hi_z3 : i = z_3 := by { omega }
          rw [hi_z3, hz3]
          exact Ne.symm hu1_ne0
  }
  have h_par := only_odds_new_val_second_occ_parity N z_1 (z_3 + 1) h_odds
    (by { omega }) (by { omega }) hz1 (by { omega }) ha_z3_1 h_bet_u1
  omega
}

/--
Post-`(3, 3)` Second-Birth Gap Forcing: if the gap `z_3 - z_2` equals `a(z_2 - 1)` and
`a(z_2 - 1)` does not appear in `(z_2 + 3, z_3 - 1)`, then `a(z_3 + 2) = (z_3 - z_2) + 2`.
-/
lemma only_odds_post_double_three_second_birth_gap (N z_0 z_1 z_2 z_3 : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz0_gt : N < z_0)
    (hz0 : vanEckNthTerm z_0 = 0) (hz1 : vanEckNthTerm z_1 = 0)
    (hz2 : vanEckNthTerm z_2 = 0) (hz3 : vanEckNthTerm z_3 = 0)
    (h_g1 : z_1 = z_0 + 3) (h_g2 : z_2 = z_1 + 3) (hz2_lt : z_2 < z_3)
    (h_bet1 : ∀ i, z_0 < i → i < z_1 → vanEckNthTerm i ≠ 0)
    (h_bet2 : ∀ i, z_1 < i → i < z_2 → vanEckNthTerm i ≠ 0)
    (h_bet3 : ∀ i, z_2 < i → i < z_3 → vanEckNthTerm i ≠ 0)
    (h_no_u2 : ∀ i, z_2 + 3 < i → i < z_3 - 1 →
      vanEckNthTerm i ≠ vanEckNthTerm (z_2 - 1))
    (h_gap_u2 : z_3 - z_2 = vanEckNthTerm (z_2 - 1)) :
    vanEckNthTerm (z_3 + 2) = (z_3 - z_2) + 2 := by {
  have h_ge5 := only_odds_no_triple_gap_three N z_0 z_1 z_2 z_3 h_odds hz0_gt
    hz0 hz1 hz2 hz3 h_g1 h_g2 hz2_lt h_bet1 h_bet2 h_bet3
  have h_step2 := only_odds_double_gap_three_second_birth_step N z_0 z_1 z_2 z_3
    h_odds hz0_gt hz0 hz1 hz2 hz3 h_g1 h_g2 hz2_lt h_bet1 h_bet2 h_bet3
  have ha_z3_1 : vanEckNthTerm (z_3 + 1) = vanEckNthTerm (z_2 - 1) := by {
    rw [gap_between_zeros z_3 z_2 hz3 (by { omega }) hz2 hz2_lt h_bet3]
    exact h_gap_u2
  }
  have hu2_ne0 : vanEckNthTerm (z_2 - 1) ≠ 0 :=
    pre_zero_ne_prior_val z_2 0 hz2 (by { omega }) (by { omega })
  have h_bet_u2 : ∀ i, z_2 - 1 < i → i < z_3 + 1 →
      vanEckNthTerm i ≠ vanEckNthTerm (z_3 + 1) := by {
    intro i hi1 hi2
    rw [ha_z3_1]
    by_cases hi_le : i ≤ z_2 + 3
    · exact h_step2.1 i hi1 hi_le
    · by_cases hi_lt : i < z_3 - 1
      · exact h_no_u2 i (by { omega }) hi_lt
      · by_cases hi_z31 : i = z_3 - 1
        · rw [hi_z31]
          exact pre_zero_ne_prior_val z_3 (z_2 - 1) hz3 (by { omega }) (by { omega })
        · have hi_z3 : i = z_3 := by { omega }
          rw [hi_z3, hz3]
          exact Ne.symm hu2_ne0
  }
  have h_dist := strict_occurrence_gap_eq (z_2 - 1) (z_3 + 1) ha_z3_1 (by { omega }) h_bet_u2
  have h_idx : z_3 + 1 + 1 = z_3 + 2 := rfl
  rw [h_idx] at h_dist
  omega
}

/--
Unconditional constraints when a gap of `5` (`z_3 = z_2 + 5`) follows two gaps of `3`
under `OnlyOddsAndZerosAfter N` (`z_0 ≥ 2`, `N < z_0`): `a(z_1 - 1) ≠ 5`,
`a(z_2 + 4) ≠ a(z_2 - 1)`, and `a(z_2 - 1) = 5 → a(z_3 + 2) = 7`.
-/
lemma only_odds_post_double_three_gap_five_constraints (N z_0 z_1 z_2 z_3 : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz0_ge : z_0 ≥ 2) (hz0_gt : N < z_0)
    (hz0 : vanEckNthTerm z_0 = 0) (hz1 : vanEckNthTerm z_1 = 0)
    (hz2 : vanEckNthTerm z_2 = 0) (hz3 : vanEckNthTerm z_3 = 0)
    (h_g1 : z_1 = z_0 + 3) (h_g2 : z_2 = z_1 + 3) (h_g3 : z_3 = z_2 + 5)
    (h_bet1 : ∀ i, z_0 < i → i < z_1 → vanEckNthTerm i ≠ 0)
    (h_bet2 : ∀ i, z_1 < i → i < z_2 → vanEckNthTerm i ≠ 0)
    (h_bet3 : ∀ i, z_2 < i → i < z_3 → vanEckNthTerm i ≠ 0) :
    vanEckNthTerm (z_1 - 1) ≠ 5 ∧
      vanEckNthTerm (z_2 + 4) ≠ vanEckNthTerm (z_2 - 1) ∧
      (vanEckNthTerm (z_2 - 1) = 5 → vanEckNthTerm (z_3 + 2) = 7) := by {
  have h_ne_u1 := only_odds_post_double_three_gap_ne_first_birth N z_0 z_1 z_2 z_3
    h_odds hz0_ge hz0_gt hz0 hz1 hz2 hz3 h_g1 h_g2 (by { omega })
    h_bet1 h_bet2 h_bet3 (by { intro i hi1 hi2; omega })
  have h_step2 := only_odds_double_gap_three_second_birth_step N z_0 z_1 z_2 z_3
    h_odds hz0_gt hz0 hz1 hz2 hz3 h_g1 h_g2 (by { omega }) h_bet1 h_bet2 h_bet3
  have h_ne_hit : vanEckNthTerm (z_2 + 4) ≠ vanEckNthTerm (z_2 - 1) := by {
    intro hc
    have h_ge7 := (h_step2.2 hc).2
    omega
  }
  refine ⟨by { omega }, h_ne_hit, ?_⟩
  intro hu2_eq5
  have h_u2_gap := only_odds_post_double_three_second_birth_gap N z_0 z_1 z_2 z_3
    h_odds hz0_gt hz0 hz1 hz2 hz3 h_g1 h_g2 (by { omega }) h_bet1 h_bet2 h_bet3
    (by { intro i hi1 hi2; omega }) (by { omega })
  omega
}

/--
When a gap of `7` (`z_3 = z_2 + 7`) follows two gaps of `3` under `OnlyOddsAndZerosAfter N`
(`z_0 ≥ 18`, `N < z_0`), birth-parity and second-occurrence together force
`a(z_1 - 1) ≠ 7` (otherwise `a(z_2 + 5) = 7` forces `a(z_2 + 6) = 9 = a(23)` before `z_3`).
-/
lemma only_odds_post_double_three_gap_seven_ne_first_birth (N z_0 z_1 z_2 z_3 : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz0_ge : z_0 ≥ 18) (hz0_gt : N < z_0)
    (hz0 : vanEckNthTerm z_0 = 0) (hz1 : vanEckNthTerm z_1 = 0)
    (hz2 : vanEckNthTerm z_2 = 0) (hz3 : vanEckNthTerm z_3 = 0)
    (h_g1 : z_1 = z_0 + 3) (h_g2 : z_2 = z_1 + 3) (h_g3 : z_3 = z_2 + 7)
    (h_bet1 : ∀ i, z_0 < i → i < z_1 → vanEckNthTerm i ≠ 0)
    (h_bet2 : ∀ i, z_1 < i → i < z_2 → vanEckNthTerm i ≠ 0)
    (h_bet3 : ∀ i, z_2 < i → i < z_3 → vanEckNthTerm i ≠ 0) :
    vanEckNthTerm (z_1 - 1) ≠ 7 := by {
  intro hu1_7
  by_cases ha5 : vanEckNthTerm (z_2 + 5) = vanEckNthTerm (z_1 - 1)
  · have h_excl := only_odds_double_gap_three_first_birth_excluded N z_0 z_1 z_2
      h_odds (by { omega }) hz0_gt hz0 hz1 hz2 h_g1 h_g2 h_bet1 h_bet2
    have h_dist := strict_occurrence_gap_eq (z_1 - 1) (z_2 + 5) ha5 (by { omega })
      (fun i hi1 hi2 => by { rw [ha5]; exact h_excl i hi1 (by { omega }) })
    have h_idx : z_2 + 5 + 1 = z_3 - 1 := by { omega }
    rw [h_idx] at h_dist
    have ha_z2_6 : vanEckNthTerm (z_3 - 1) = 9 := by { omega }
    have ha23 : vanEckNthTerm 23 = 9 := by { decide +kernel }
    have h_ne9 := pre_zero_ne_prior_val z_3 23 hz3 (by { omega }) (by { omega })
    rw [ha_z2_6, ha23] at h_ne9
    exact h_ne9 rfl
  · have h_ne := only_odds_post_double_three_gap_ne_first_birth N z_0 z_1 z_2 z_3
      h_odds (by { omega }) hz0_gt hz0 hz1 hz2 hz3 h_g1 h_g2 (by { omega })
      h_bet1 h_bet2 h_bet3
      (by { intro i hi1 hi2; have hi : i = z_2 + 5 := by { omega }; rw [hi]; exact ha5 })
    omega
}

/--
Concrete witness (`N_0 = 22, z_0 = 30, z = 35`) showing that in a `2`-free window
`[23, 38]`, `vanEckNthTerm (z - 1) = 15 > 14 = vanEckPrefixMax z_0`, refuting any
purely local inductive proof of the `k = z - 1` branch in `no_twos_implies_bounded`.
-/
lemma prefixMax_jump_in_two_free_window :
    (∀ m ≤ 38, 22 < m → vanEckNthTerm m ≠ 2) ∧
    vanEckNthTerm 30 = 0 ∧
    vanEckNthTerm 35 = 0 ∧
    lastZero 34 = 30 ∧
    vanEckPrefixMax 30 = 14 ∧
    vanEckNthTerm 34 = 15 := by {
  decide +kernel
}

/--
Lookback anatomy of the `(z_prev = 30, z = 35)` prefix-maximum jump witness: the bounded
generator `a(33) = 5 ≤ 14 = vanEckPrefixMax 30` was completely dormant across `[19, 32]`,
with prior occurrence `p = 18 < 29 = z_prev - 1` yielding `a(34) = 33 - 18 = 15`.
-/
lemma prefixMax_jump_witness_lookback :
    vanEckNthTerm 33 = 5 ∧
      vanEckNthTerm 18 = 5 ∧
      (∀ j < 33, 18 < j → vanEckNthTerm j ≠ 5) ∧
      vanEckNthTerm 34 = 33 - 18 ∧
      vanEckPrefixMax 35 = 15 := by {
  decide +kernel
}

/--
Under `OnlyOddsAndZerosAfter N`, for consecutive zeros `0 < z_prev < z` (`N < z_prev`),
both the newly created value `a(z - 1)` and its generator `a(z - 2)` are odd, and the
generator's strictly most recent prior occurrence `p = z - 2 - a(z - 1)` lies at index
parity `p % 2 = (z - 1) % 2` (opposite to `z` and `z - 2`).
-/
lemma only_odds_pre_zero_prior_occurrence_parity (N z z_prev : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz_prev_gt : N < z_prev)
    (hz_prev_pos : z_prev > 0) (hz : vanEckNthTerm z = 0)
    (hz_prev : vanEckNthTerm z_prev = 0) (h_prev_lt : z_prev < z)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) :
    vanEckNthTerm (z - 1) % 2 = 1 ∧
      vanEckNthTerm (z - 2) % 2 = 1 ∧
      z - 2 - vanEckNthTerm (z - 1) < z - 2 ∧
      (z - 2 - vanEckNthTerm (z - 1)) % 2 = (z - 1) % 2 ∧
      vanEckNthTerm (z - 2 - vanEckNthTerm (z - 1)) = vanEckNthTerm (z - 2) ∧
      ∀ j, z - 2 - vanEckNthTerm (z - 1) < j → j < z - 2 →
        vanEckNthTerm j ≠ vanEckNthTerm (z - 2) := by {
  have h_zgap := only_odds_zero_gap_ge_three N h_odds z_prev z
    hz_prev_pos hz_prev hz h_prev_lt h_gap hz_prev_gt
  have h_spec := pre_zero_new_value_prior_occurrence_spec z hz (by { omega })
  have hz1_nz : vanEckNthTerm (z - 1) ≠ 0 := h_gap (z - 1) (by { omega }) (by { omega })
  have hz2_nz : vanEckNthTerm (z - 2) ≠ 0 := h_gap (z - 2) (by { omega }) (by { omega })
  have hz1_odd : vanEckNthTerm (z - 1) % 2 = 1 := by {
    rcases h_odds (z - 1) (by { omega }) with h0 | h1
    · exact False.elim (hz1_nz h0)
    · exact h1
  }
  have hz2_odd : vanEckNthTerm (z - 2) % 2 = 1 := by {
    rcases h_odds (z - 2) (by { omega }) with h0 | h1
    · exact False.elim (hz2_nz h0)
    · exact h1
  }
  exact ⟨hz1_odd, hz2_odd, h_spec.2.2.1, by { omega }, h_spec.2.2.2.2.1, h_spec.2.2.2.2.2⟩
}

/--
`OnlyOddsAndZerosAfter N` excludes `2` from the entire tail `m > N`.
-/
lemma only_odds_implies_no_twos (N : ℕ) (h_odds : OnlyOddsAndZerosAfter N) :
    ∀ m > N, vanEckNthTerm m ≠ 2 := by {
  intro m hm_gt hc
  rcases h_odds m hm_gt with h0 | h1 <;> omega
}

/--
Dormant-Generator Jump Theorem under `OnlyOddsAndZerosAfter N`: for any anchor floor `B`,
index horizon `K`, and value floor `V`, there exist consecutive zeros `z_prev < z` with
`max N K < z_prev` and `V < vanEckPrefixMax z_prev < vanEckPrefixMax z = a(z - 1)`,
driven by a bounded odd generator `a(z - 2) ≤ vanEckPrefixMax z_prev` whose strictly most
recent prior occurrence `p = z - 2 - a(z - 1)` satisfies `B < p`, `p + 1 < z_prev`, and
`p % 2 = (z - 1) % 2`.
-/
theorem only_odds_infinite_dormant_generator_jumps (N B K V : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) :
    ∃ z_prev z, N < z_prev ∧ K < z_prev ∧ z_prev < z ∧
      vanEckNthTerm z_prev = 0 ∧ vanEckNthTerm z = 0 ∧
      (∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) ∧
      z - z_prev ≥ 3 ∧ (z - z_prev) % 2 = 1 ∧ z - z_prev ≤ vanEckPrefixMax z_prev ∧
      V < vanEckPrefixMax z_prev ∧
      vanEckPrefixMax z_prev < vanEckPrefixMax z ∧
      vanEckPrefixMax z = vanEckNthTerm (z - 1) ∧
      vanEckNthTerm (z - 1) % 2 = 1 ∧
      vanEckNthTerm (z - 2) % 2 = 1 ∧
      1 ≤ vanEckNthTerm (z - 2) ∧ vanEckNthTerm (z - 2) ≤ vanEckPrefixMax z_prev ∧
      B < z - 2 - vanEckNthTerm (z - 1) ∧
      (z - 2 - vanEckNthTerm (z - 1)) + 1 < z_prev ∧
      (z - 2 - vanEckNthTerm (z - 1)) % 2 = (z - 1) % 2 ∧
      vanEckNthTerm (z - 2 - vanEckNthTerm (z - 1)) = vanEckNthTerm (z - 2) ∧
      (∀ j, z - 2 - vanEckNthTerm (z - 1) < j → j < z - 2 →
        vanEckNthTerm j ≠ vanEckNthTerm (z - 2)) ∧
      vanEckNthTerm (z - 1) =
        (z - z_prev - 2) + (z_prev - (z - 2 - vanEckNthTerm (z - 1))) := by {
  have h_no_twos := only_odds_implies_no_twos N h_odds
  rcases lookback_prefix_exhaustion B with ⟨N_B, _, hNB⟩
  rcases no_twos_infinite_dormant_generator_jumps N (max K N_B) V h_no_twos with
    ⟨z_prev, z, hN_lt, hKNB_lt, hz_lt, hzp_zero, hz_zero, h_gap, hV_lt, h_jump, _⟩
  have h_bounds := no_twos_zero_gap_and_predecessor_bounds N z z_prev h_no_twos
    (by { omega }) hz_zero (by { omega }) hzp_zero hz_lt h_gap
  have h_zgap := only_odds_zero_gap_ge_three N h_odds z_prev z
    (by { omega }) hzp_zero hz_zero hz_lt h_gap hN_lt
  have h_dorm := no_twos_prefixMax_jump_requires_dormant_generator N z z_prev h_no_twos
    (by { omega }) hz_zero (by { omega }) hzp_zero hz_lt h_gap h_jump
  have h_par := only_odds_pre_zero_prior_occurrence_parity N z z_prev h_odds
    hN_lt (by { omega }) hz_zero hzp_zero hz_lt h_gap
  have h_p_gt_B : B < z - 2 - vanEckNthTerm (z - 1) := by {
    rcases hNB (z - 1) (by { omega }) with hz1_0 | hgt
    · omega
    · have h_sub : z - 1 - 1 = z - 2 := by { omega }
      rw [h_sub] at hgt
      exact hgt
  }
  exact ⟨z_prev, z, hN_lt, by { omega }, hz_lt, hzp_zero, hz_zero, h_gap, h_zgap.1,
    h_zgap.2, h_bounds.2.1, hV_lt, h_jump, h_dorm.1, h_par.1, h_par.2.1, h_dorm.2.1,
    h_dorm.2.2.1, h_p_gt_B, h_dorm.2.2.2.1, h_par.2.2.2.1, h_par.2.2.2.2.1,
    h_par.2.2.2.2.2, h_dorm.2.2.2.2.2.1⟩
}

/--
Birth-Return Dichotomy under `OnlyOddsAndZerosAfter N`: for any zero `z_1 > N + 1`, the
brand-new odd value `a(z_1 - 1)` avoids `z_2` and `z_2 - 1` for every later zero `z_2`,
and either never reappears after `z_1 - 1` or has a strictly earliest second occurrence
`r > z_1` satisfying `r % 2 = z_1 % 2` and `a(r + 1) = r - (z_1 - 1)`.
-/
lemma only_odds_birth_return_dichotomy (N z_1 : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz1_gt : N + 1 < z_1)
    (hz1 : vanEckNthTerm z_1 = 0) :
    vanEckNthTerm (z_1 - 1) % 2 = 1 ∧
      (∀ i < z_1 - 1, vanEckNthTerm i ≠ vanEckNthTerm (z_1 - 1)) ∧
      (∀ z_2 > z_1, vanEckNthTerm z_2 = 0 →
        vanEckNthTerm z_2 ≠ vanEckNthTerm (z_1 - 1) ∧
          vanEckNthTerm (z_2 - 1) ≠ vanEckNthTerm (z_1 - 1)) ∧
      ((∀ m > z_1 - 1, vanEckNthTerm m ≠ vanEckNthTerm (z_1 - 1)) ∨
        ∃ r > z_1, vanEckNthTerm r = vanEckNthTerm (z_1 - 1) ∧
          (∀ i, z_1 - 1 < i → i < r → vanEckNthTerm i ≠ vanEckNthTerm (z_1 - 1)) ∧
          r % 2 = z_1 % 2 ∧
          vanEckNthTerm (r + 1) = r - (z_1 - 1)) := by {
  have h_spec := pre_zero_new_value_prior_occurrence_spec z_1 hz1 (by { omega })
  have hu1_odd : vanEckNthTerm (z_1 - 1) % 2 = 1 := by {
    rcases h_odds (z_1 - 1) (by { omega }) with h0 | h1
    · omega
    · exact h1
  }
  have h_avoid_zeros : ∀ z_2 > z_1, vanEckNthTerm z_2 = 0 →
      vanEckNthTerm z_2 ≠ vanEckNthTerm (z_1 - 1) ∧
        vanEckNthTerm (z_2 - 1) ≠ vanEckNthTerm (z_1 - 1) := by {
    intro z_2 hz2_gt hz2
    exact ⟨by { omega }, pre_zero_ne_prior_val z_2 (z_1 - 1) hz2 (by { omega }) (by { omega })⟩
  }
  refine ⟨hu1_odd, h_spec.2.1, h_avoid_zeros, ?_⟩
  by_cases h_ex : ∃ m, m > z_1 - 1 ∧ vanEckNthTerm m = vanEckNthTerm (z_1 - 1)
  · right
    let r := Nat.find h_ex
    have hr_spec : r > z_1 - 1 ∧ vanEckNthTerm r = vanEckNthTerm (z_1 - 1) :=
      Nat.find_spec h_ex
    have hr_min : ∀ i, z_1 - 1 < i → i < r →
        vanEckNthTerm i ≠ vanEckNthTerm (z_1 - 1) :=
      fun i hi1 hi2 hc => Nat.find_min h_ex hi2 ⟨hi1, hc⟩
    have hr_ne_z1 : r ≠ z_1 := by {
      intro hc
      have hr_eq := hr_spec.2
      rw [hc, hz1] at hr_eq
      omega
    }
    have hr_par := only_odds_new_val_second_occ_parity N z_1 r h_odds
      (by { omega }) (by { omega }) hz1 hr_spec.1 hr_spec.2 hr_min
    have hr_gap := strict_occurrence_gap_eq (z_1 - 1) r hr_spec.2 hr_spec.1
      (fun i hi1 hi2 => by { rw [hr_spec.2]; exact hr_min i hi1 hi2 })
    exact ⟨r, by { omega }, hr_spec.2, hr_min, hr_par, hr_gap⟩
  · left
    exact fun m hm hc => h_ex ⟨m, hm, hc⟩
}

/--
Coupling of Birth Dichotomy (#5) and Dormant Generators (#1): an unreturned birth `a(z_1 - 1)`
can never serve as a later zero's generator `a(z - 2)`. If `a(z - 2) = a(z_1 - 1)` for
`N + 1 < z_1 < z`, then `z_1 + 3 ≤ z` and `a(z_1 - 1)` returned at some earliest `r > z_1`,
either directly at `r = z - 2` (`z % 2 = z_1 % 2` and `a(z - 1) = z - z_1 - 1`) or earlier at
`r ≤ z - 2 - a(z - 1)` (`a(z - 1) ≤ (z - 2) - r`).
-/
lemma only_odds_birth_as_generator_cases (N z_1 z : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz1_gt : N + 1 < z_1) (h_lt : z_1 < z)
    (hz1 : vanEckNthTerm z_1 = 0) (hz : vanEckNthTerm z = 0)
    (h_gen : vanEckNthTerm (z - 2) = vanEckNthTerm (z_1 - 1)) :
    z_1 + 3 ≤ z ∧
      ((z % 2 = z_1 % 2 ∧
        z - 2 - vanEckNthTerm (z - 1) = z_1 - 1 ∧
        vanEckNthTerm (z - 1) = z - z_1 - 1 ∧
        ∀ i, z_1 - 1 < i → i < z - 2 → vanEckNthTerm i ≠ vanEckNthTerm (z_1 - 1)) ∨
      ∃ r, z_1 < r ∧ r ≤ z - 2 - vanEckNthTerm (z - 1) ∧
        vanEckNthTerm r = vanEckNthTerm (z_1 - 1) ∧
        (∀ i, z_1 - 1 < i → i < r → vanEckNthTerm i ≠ vanEckNthTerm (z_1 - 1)) ∧
        r % 2 = z_1 % 2 ∧
        vanEckNthTerm (r + 1) = r - (z_1 - 1) ∧
        vanEckNthTerm (z - 1) ≤ (z - 2) - r) := by {
  have h_dist := birth_as_later_generator_min_dist z_1 z (by { omega }) h_lt hz1 hz h_gen
  have h_sz := pre_zero_new_value_prior_occurrence_spec z hz (by { omega })
  have h_dich := only_odds_birth_return_dichotomy N z_1 h_odds hz1_gt hz1
  rcases h_dich.2.2.2 with h_never | ⟨r, hr_gt, hr_eq, hr_min, hr_par, hr_gap⟩
  · exact False.elim (h_never (z - 2) (by { omega }) h_gen)
  · have hr_le : r ≤ z - 2 := by {
      by_contra h_gt
      exact hr_min (z - 2) (by { omega }) (by { omega }) h_gen
    }
    refine ⟨h_dist.1, ?_⟩
    by_cases hr_eq_z2 : r = z - 2
    · left
      have hp_val : vanEckNthTerm (z - 2 - vanEckNthTerm (z - 1)) =
          vanEckNthTerm (z_1 - 1) := by { rw [h_sz.2.2.2.2.1, h_gen] }
      have hp_le : z - 2 - vanEckNthTerm (z - 1) ≤ z_1 - 1 := by {
        by_contra hp_gt
        exact hr_min (z - 2 - vanEckNthTerm (z - 1)) (by { omega })
          (by { have := h_sz.2.2.1; omega }) hp_val
      }
      have hp_eq : z - 2 - vanEckNthTerm (z - 1) = z_1 - 1 := by { omega }
      have hz1_val := h_sz.2.2.2.1
      exact ⟨by { omega }, hp_eq, by { omega }, fun i hi1 hi2 => hr_min i hi1 (by { omega })⟩
    · right
      have hp_ge_r : r ≤ z - 2 - vanEckNthTerm (z - 1) := by {
        by_contra hp_lt_r
        have hr_ne := h_sz.2.2.2.2.2 r (by { omega }) (by { omega })
        rw [h_gen] at hr_ne
        exact hr_ne hr_eq
      }
      have hz1_val := h_sz.2.2.2.1
      exact ⟨r, hr_gt, hp_ge_r, hr_eq, hr_min, hr_par, hr_gap, by { omega }⟩
}

/--
First-Return Budget Bound: each birth zero `z_b ∈ [A_b, B_b]` can supply at most one
first-return firing (`z - 2 - a(z - 1) = z_b - 1`). For any finite set `F` of zeros `z ≥ 2`
whose anchor `p(z) = z - 2 - a(z - 1)` is a birth slot (`a(p(z) + 1) = 0`) with
`p(z) + 1 ∈ [A_b, B_b]`, `F.card` is bounded by the count of zeros in `[A_b, B_b]`.
-/
lemma first_return_jumps_le_birth_zeros (F : Finset ℕ) (A_b B_b : ℕ)
    (hF : ∀ z ∈ F, z ≥ 2 ∧ vanEckNthTerm z = 0 ∧
      A_b ≤ z - 2 - vanEckNthTerm (z - 1) + 1 ∧
      z - 2 - vanEckNthTerm (z - 1) + 1 ≤ B_b ∧
      vanEckNthTerm (z - 2 - vanEckNthTerm (z - 1) + 1) = 0) :
    F.card ≤ ((Finset.Icc A_b B_b).filter (fun z_b => vanEckNthTerm z_b = 0)).card := by {
  let g : ℕ → ℕ := fun z => z - 2 - vanEckNthTerm (z - 1) + 1
  have h_inj : Set.InjOn g (F : Set ℕ) := by {
    intro z hz z' hz' heq
    rcases lt_trichotomy z z' with hlt | h_eq | hgt
    · exfalso
      exact pre_zero_prior_anchor_unique z z' (hF z hz).1 hlt
        (hF z hz).2.1 (hF z' hz').2.1 (Nat.add_right_cancel heq)
    · exact h_eq
    · exfalso
      exact pre_zero_prior_anchor_unique z' z (hF z' hz').1 hgt
        (hF z' hz').2.1 (hF z hz).2.1 (Nat.add_right_cancel heq).symm
  }
  have h_sub : F.image g ⊆ (Finset.Icc A_b B_b).filter (fun z_b => vanEckNthTerm z_b = 0) := by {
    intro z_b hzb
    rcases Finset.mem_image.mp hzb with ⟨z, hz, rfl⟩
    have hp := hF z hz
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hp.2.2.1, hp.2.2.2.1⟩, hp.2.2.2.2⟩
  }
  rw [← Finset.card_image_of_injOn h_inj]
  exact Finset.card_le_card h_sub
}

/--
Jump Birth-Return Tripartition under `OnlyOddsAndZerosAfter N`: for every prefix-maximum jump
`(z_prev, z)` past `N`, the odd generator `a(z - 2)` has a unique birth zero `z_b` (`3 ≤ z_b`,
`z_b + 3 ≤ z`, `a(z_b) = 0`, `a(z_b - 1) = a(z - 2)`) and falls into one of three regimes:
(1) finite pre-`N` palette (`z_b ≤ N + 1` and `1 ≤ a(z - 2) ≤ vanEckPrefixMax N`),
(2) post-`N` first-return firing (`N + 1 < z_b`, `z % 2 = z_b % 2`, `p = z_b - 1`,
`vanEckPrefixMax z = a(z - 1) = z - z_b - 1`), or
(3) post-`N` later-return firing (`N + 1 < z_b`, earliest return `z_b < r ≤ p < z - 2` with
`r % 2 = z_b % 2`, `a(r + 1) = r - (z_b - 1)`, and `vanEckPrefixMax z_prev < a(z - 1) ≤ z - 2 - r`).
-/
theorem only_odds_jump_birth_tripartition (N z_prev z : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N)
    (hN_lt : N < z_prev) (h_prev_lt : z_prev < z)
    (hz_prev : vanEckNthTerm z_prev = 0) (hz : vanEckNthTerm z = 0)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0)
    (h_jump : vanEckPrefixMax z_prev < vanEckPrefixMax z) :
    ∃ z_b, 3 ≤ z_b ∧ z_b + 3 ≤ z ∧ vanEckNthTerm z_b = 0 ∧
      vanEckNthTerm (z_b - 1) = vanEckNthTerm (z - 2) ∧
      ((z_b ≤ N + 1 ∧ 1 ≤ vanEckNthTerm (z - 2) ∧ vanEckNthTerm (z - 2) ≤ vanEckPrefixMax N) ∨
        (N + 1 < z_b ∧ z % 2 = z_b % 2 ∧
          z - 2 - vanEckNthTerm (z - 1) = z_b - 1 ∧
          vanEckPrefixMax z = z - z_b - 1 ∧
          ∀ i, z_b - 1 < i → i < z - 2 → vanEckNthTerm i ≠ vanEckNthTerm (z_b - 1)) ∨
        (N + 1 < z_b ∧ ∃ r, z_b < r ∧ r ≤ z - 2 - vanEckNthTerm (z - 1) ∧
          vanEckNthTerm r = vanEckNthTerm (z_b - 1) ∧
          (∀ i, z_b - 1 < i → i < r → vanEckNthTerm i ≠ vanEckNthTerm (z_b - 1)) ∧
          r % 2 = z_b % 2 ∧
          vanEckNthTerm (r + 1) = r - (z_b - 1) ∧
          vanEckPrefixMax z_prev < vanEckNthTerm (z - 1) ∧
          vanEckNthTerm (z - 1) ≤ (z - 2) - r)) := by {
  have h_no_twos := only_odds_implies_no_twos N h_odds
  have h_dorm := no_twos_prefixMax_jump_requires_dormant_generator N z z_prev h_no_twos
    (by { omega }) hz (by { omega }) hz_prev h_prev_lt h_gap h_jump
  rcases pos_generator_has_unique_birth_zero z (by { omega }) hz h_dorm.2.1 with
    ⟨z_b, hzb_ge, hzb_dist, hzb_zero, hzb_eq, _, _⟩
  refine ⟨z_b, hzb_ge, hzb_dist, hzb_zero, hzb_eq, ?_⟩
  by_cases hzb_le : z_b ≤ N + 1
  · left
    have h_le_max : vanEckNthTerm (z_b - 1) ≤ vanEckPrefixMax N :=
      vanEckNthTerm_le_prefixMax N (z_b - 1) (by { omega })
    rw [hzb_eq] at h_le_max
    exact ⟨hzb_le, h_dorm.2.1, h_le_max⟩
  · have hzb_gt : N + 1 < z_b := by { omega }
    have h_cases := only_odds_birth_as_generator_cases N z_b z h_odds hzb_gt
      (by { omega }) hzb_zero hz hzb_eq.symm
    rcases h_cases.2 with h_first | ⟨r, hr_gt, hr_le_p, hr_eq, hr_min, hr_par, hr_gap, hr_ub⟩
    · right
      left
      exact ⟨hzb_gt, h_first.1, h_first.2.1, h_dorm.1.trans h_first.2.2.1, h_first.2.2.2⟩
    · right
      right
      exact ⟨hzb_gt, r, hr_gt, hr_le_p, hr_eq, hr_min, hr_par, hr_gap,
        h_jump.trans_eq h_dorm.1, hr_ub⟩
}

/--
Cardinality bounds on the odd palette `Odd ∩ [1, H]` (`≤ (H + 1) / 2`) and the `{0, odd}`
palette `({0} ∪ Odd) ∩ [0, H]` (`≤ (H + 1) / 2 + 1`).
-/
lemma odd_Icc_filter_card_le (H : ℕ) :
    ((Finset.Icc 1 H).filter (fun v => v % 2 = 1)).card ≤ (H + 1) / 2 ∧
      ((Finset.Icc 0 H).filter (fun v => v = 0 ∨ v % 2 = 1)).card ≤ (H + 1) / 2 + 1 := by {
  let S1 := (Finset.Icc 1 H).filter (fun v => v % 2 = 1)
  have h_inj : Set.InjOn (fun v => v / 2) (S1 : Set ℕ) := by {
    intro u hu v hv heq
    dsimp at heq
    have hu' := (Finset.mem_filter.mp hu).2
    have hv' := (Finset.mem_filter.mp hv).2
    omega
  }
  have h_sub1 : S1.image (fun v => v / 2) ⊆ Finset.range ((H + 1) / 2) := by {
    intro k hk
    rcases Finset.mem_image.mp hk with ⟨v, hv, rfl⟩
    rcases Finset.mem_filter.mp hv with ⟨hv_icc, hv_odd⟩
    have hv_b := Finset.mem_Icc.mp hv_icc
    exact Finset.mem_range.mpr (by { omega })
  }
  have h1 : S1.card ≤ (H + 1) / 2 := by {
    have h_le := Finset.card_le_card h_sub1
    rw [Finset.card_image_of_injOn h_inj, Finset.card_range] at h_le
    exact h_le
  }
  let S0 := (Finset.Icc 0 H).filter (fun v => v = 0 ∨ v % 2 = 1)
  have h_sub0 : S0 ⊆ insert 0 S1 := by {
    intro v hv
    rcases Finset.mem_filter.mp hv with ⟨hv_icc, hv_or⟩
    have hv_b := Finset.mem_Icc.mp hv_icc
    rcases hv_or with rfl | hv_odd
    · exact Finset.mem_insert_self 0 S1
    · exact Finset.mem_insert_of_mem
        (Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by { omega }, hv_b.2⟩, hv_odd⟩)
  }
  have h0 : S0.card ≤ (H + 1) / 2 + 1 := by {
    calc S0.card ≤ (insert 0 S1).card := Finset.card_le_card h_sub0
      _ ≤ S1.card + 1 := Finset.card_insert_le 0 S1
      _ ≤ (H + 1) / 2 + 1 := Nat.add_le_add_right h1 1
  }
  exact ⟨h1, h0⟩
}

/--
Large-Birth Zero Demand under `OnlyOddsAndZerosAfter N`: at most `(H + 1) / 2` zeros `z > N + 1`
can ever have `a(z - 1) ≤ H`; every remaining zero in `Z` must emit `H < a(z - 1)`.
-/
lemma only_odds_large_birth_zero_demand (N H : ℕ) (Z : Finset ℕ)
    (h_odds : OnlyOddsAndZerosAfter N)
    (hZ : ∀ z ∈ Z, N + 1 < z ∧ vanEckNthTerm z = 0) :
    (Z.filter (fun z => vanEckNthTerm (z - 1) ≤ H)).card ≤ (H + 1) / 2 ∧
      Z.card ≤ (Z.filter (fun z => H < vanEckNthTerm (z - 1))).card + (H + 1) / 2 := by {
  let Zs := Z.filter (fun z => vanEckNthTerm (z - 1) ≤ H)
  have h_inj : Set.InjOn (fun z => vanEckNthTerm (z - 1)) (Zs : Set ℕ) := by {
    intro z hz z' hz' heq
    have hzp := hZ z (Finset.mem_filter.mp hz).1
    have hz'p := hZ z' (Finset.mem_filter.mp hz').1
    by_contra hne
    have h_ne_val := zero_predecessors_inj (i := z - 1) (j := z' - 1)
      (by { have h : z - 1 + 1 = z := by { omega }; rw [h]; exact hzp.2 })
      (by { have h : z' - 1 + 1 = z' := by { omega }; rw [h]; exact hz'p.2 })
      (by { omega })
    exact h_ne_val heq
  }
  have h_sub : Zs.image (fun z => vanEckNthTerm (z - 1)) ⊆
      (Finset.Icc 1 H).filter (fun v => v % 2 = 1) := by {
    intro v hv
    rcases Finset.mem_image.mp hv with ⟨z, hz, rfl⟩
    rcases Finset.mem_filter.mp hz with ⟨hzZ, hz_le⟩
    have hzp := hZ z hzZ
    have h_pos := (pre_zero_new_value_prior_occurrence_spec z hzp.2 (by { omega })).1
    have h_odd : vanEckNthTerm (z - 1) % 2 = 1 := by {
      rcases h_odds (z - 1) (by { omega }) with h0 | h1 <;> omega
    }
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by { omega }, hz_le⟩, h_odd⟩
  }
  have h_small : Zs.card ≤ (H + 1) / 2 := by {
    calc Zs.card = (Zs.image (fun z => vanEckNthTerm (z - 1))).card :=
          (Finset.card_image_of_injOn h_inj).symm
      _ ≤ ((Finset.Icc 1 H).filter (fun v => v % 2 = 1)).card := Finset.card_le_card h_sub
      _ ≤ (H + 1) / 2 := (odd_Icc_filter_card_le H).1
  }
  have h_part := Finset.card_filter_add_card_filter_not
    (s := Z) (fun z => vanEckNthTerm (z - 1) ≤ H)
  have h_neg : Z.filter (fun z => ¬ vanEckNthTerm (z - 1) ≤ H) =
      Z.filter (fun z => H < vanEckNthTerm (z - 1)) :=
    Finset.filter_congr (fun _ _ => not_le)
  rw [h_neg] at h_part
  change Zs.card + (Z.filter (fun z => H < vanEckNthTerm (z - 1))).card = Z.card at h_part
  exact ⟨h_small, by { omega }⟩
}

/--
Any `T : Finset ℕ` satisfies `T.card ^ 2 ≤ ∑_{x ∈ T} (2 * x + 1)`.
-/
lemma sum_two_mul_add_one_ge_sq (T : Finset ℕ) :
    T.card ^ 2 ≤ ∑ x ∈ T, (2 * x + 1) := by {
  suffices h : ∀ n (S : Finset ℕ), S.card = n → n ^ 2 ≤ ∑ x ∈ S, (2 * x + 1) from
    h T.card T rfl
  intro n
  induction n with
  | zero =>
    intro S _hS
    simp
  | succ k ih =>
    intro S hS
    have hne : S.Nonempty := Finset.card_pos.mp (by { omega })
    let m := S.max' hne
    have hm_mem : m ∈ S := Finset.max'_mem S hne
    have h_er_card : (S.erase m).card = k := by {
      rw [Finset.card_erase_of_mem hm_mem, hS]
      rfl
    }
    have h_er_sub : S.erase m ⊆ Finset.range m := by {
      intro x hx
      have hx_le : x ≤ m := Finset.le_max' S x (Finset.mem_of_mem_erase hx)
      have hx_ne : x ≠ m := Finset.ne_of_mem_erase hx
      exact Finset.mem_range.mpr (lt_of_le_of_ne hx_le hx_ne)
    }
    have hk_le_m : k ≤ m := by {
      have h_le := Finset.card_le_card h_er_sub
      rw [h_er_card, Finset.card_range] at h_le
      exact h_le
    }
    have h_ih := ih (S.erase m) h_er_card
    have h_sum := (Finset.sum_erase_add S (fun x => 2 * x + 1) hm_mem).symm
    rw [h_sum]
    nlinarith
}

/--
Quadratic Birth-Sum Demand under `OnlyOddsAndZerosAfter N`: any finite set `Z` of post-`N` zeros
(`N + 1 < z`) demands total new-value dormancy `Z.card ^ 2 ≤ ∑_{z ∈ Z} a(z - 1)`.
-/
lemma only_odds_zero_predecessor_sum_ge_sq (N : ℕ) (Z : Finset ℕ)
    (h_odds : OnlyOddsAndZerosAfter N)
    (hZ : ∀ z ∈ Z, N + 1 < z ∧ vanEckNthTerm z = 0) :
    Z.card ^ 2 ≤ ∑ z ∈ Z, vanEckNthTerm (z - 1) := by {
  let c : ℕ → ℕ := fun z => vanEckNthTerm (z - 1) / 2
  have hc_odd : ∀ z ∈ Z, vanEckNthTerm (z - 1) = 2 * c z + 1 := by {
    intro z hz
    have hzp := hZ z hz
    have h_pos := (pre_zero_new_value_prior_occurrence_spec z hzp.2 (by { omega })).1
    have h_odd : vanEckNthTerm (z - 1) % 2 = 1 := by {
      rcases h_odds (z - 1) (by { omega }) with h0 | h1 <;> omega
    }
    dsimp [c]
    omega
  }
  have h_inj : Set.InjOn c (Z : Set ℕ) := by {
    intro z hz z' hz' heq
    have heq_val : vanEckNthTerm (z - 1) = vanEckNthTerm (z' - 1) := by {
      rw [hc_odd z hz, hc_odd z' hz', heq]
    }
    have hzp := hZ z hz
    have hz'p := hZ z' hz'
    by_contra hne
    have h_ne_val := zero_predecessors_inj (i := z - 1) (j := z' - 1)
      (by { have h : z - 1 + 1 = z := by { omega }; rw [h]; exact hzp.2 })
      (by { have h : z' - 1 + 1 = z' := by { omega }; rw [h]; exact hz'p.2 })
      (by { omega })
    exact h_ne_val heq_val
  }
  have h_sq := sum_two_mul_add_one_ge_sq (Z.image c)
  rw [Finset.card_image_of_injOn h_inj, Finset.sum_image h_inj] at h_sq
  have h_sum_eq : (∑ z ∈ Z, (2 * c z + 1)) = ∑ z ∈ Z, vanEckNthTerm (z - 1) :=
    Finset.sum_congr rfl (fun z hz => (hc_odd z hz).symm)
  rw [h_sum_eq] at h_sq
  exact h_sq
}

/--
Half-Capacity Zero Count Bound under `OnlyOddsAndZerosAfter N`: because post-`N` zero predecessors
must be distinct odd numbers, `zerosCount m ≤ (vanEckPrefixMax m + 1) / 2 + (N + 2)`.
-/
lemma only_odds_zerosCount_le_half_max (N m : ℕ) (h_odds : OnlyOddsAndZerosAfter N) :
    zerosCount m ≤ (vanEckPrefixMax m + 1) / 2 + (N + 2) := by {
  rw [zerosCount_eq_card m]
  let F := (Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)
  change F.card + 1 ≤ (vanEckPrefixMax m + 1) / 2 + (N + 2)
  have h_part := Finset.card_filter_add_card_filter_not (s := F) (fun i => i ≤ N)
  have h_pre : (F.filter (fun i => i ≤ N)).card ≤ N + 1 := by {
    have h_sub : F.filter (fun i => i ≤ N) ⊆ Finset.range (N + 1) :=
      fun i hi => Finset.mem_range.mpr (Nat.lt_succ_of_le (Finset.mem_filter.mp hi).2)
    have h_le := Finset.card_le_card h_sub
    rw [Finset.card_range] at h_le
    exact h_le
  }
  let F_post := F.filter (fun i => ¬ i ≤ N)
  let Z_post := F_post.image (fun i => i + 1)
  have h_inj : Set.InjOn (fun i => i + 1) (F_post : Set ℕ) :=
    fun _i _hi _j _hj heq => Nat.succ.inj heq
  have hZ : ∀ z ∈ Z_post, N + 1 < z ∧ vanEckNthTerm z = 0 := by {
    intro z hz
    rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
    rcases Finset.mem_filter.mp hi with ⟨hiF, hi_gt⟩
    exact ⟨by { omega }, (Finset.mem_filter.mp hiF).2⟩
  }
  have h_post : Z_post.card ≤ (vanEckPrefixMax m + 1) / 2 := by {
    have h_eq : Z_post.filter (fun z => vanEckNthTerm (z - 1) ≤ vanEckPrefixMax m) = Z_post := by {
      apply Finset.filter_true_of_mem
      intro z hz
      rcases Finset.mem_image.mp hz with ⟨i, hi, rfl⟩
      have hi_lt := Finset.mem_range.mp (Finset.mem_filter.mp (Finset.mem_filter.mp hi).1).1
      exact vanEckNthTerm_le_prefixMax m i (by { omega })
    }
    have h_dem := (only_odds_large_birth_zero_demand N (vanEckPrefixMax m) Z_post h_odds hZ).1
    rw [h_eq] at h_dem
    exact h_dem
  }
  rw [Finset.card_image_of_injOn h_inj] at h_post
  change (F.filter (fun i => i ≤ N)).card + F_post.card = F.card at h_part
  omega
}

/--
Sharpened `{0, odd}` Prefix-Maximum Growth Demand: `2 * lastZero m` (rather than `lastZero m`) is
bounded by `(vanEckPrefixMax (m + 1) + (2 * N + 3)) * vanEckPrefixMax (m + 1)`.
-/
lemma only_odds_double_lastZero_le_sq (N m : ℕ) (h_odds : OnlyOddsAndZerosAfter N) :
    2 * lastZero m ≤
      (vanEckPrefixMax (m + 1) + (2 * N + 3)) * vanEckPrefixMax (m + 1) := by {
  have h_zc := only_odds_zerosCount_le_half_max N m h_odds
  have h_mono := vanEckPrefixMax_mono m (m + 1) (Nat.le_succ m)
  have h_bnd : ∀ i ≤ m + 1, vanEckNthTerm i ≤ vanEckPrefixMax (m + 1) :=
    fun i hi => vanEckNthTerm_le_prefixMax (m + 1) i hi
  have h_gap := lastZero_le_gaps m (vanEckPrefixMax (m + 1)) h_bnd
  have h_zc_pos := zerosCount_pos m
  have h_two_zc : 2 * (zerosCount m - 1) ≤ vanEckPrefixMax (m + 1) + (2 * N + 3) := by { omega }
  calc 2 * lastZero m ≤ 2 * ((zerosCount m - 1) * vanEckPrefixMax (m + 1)) :=
        Nat.mul_le_mul_left 2 h_gap
    _ = (2 * (zerosCount m - 1)) * vanEckPrefixMax (m + 1) := (Nat.mul_assoc _ _ _).symm
    _ ≤ (vanEckPrefixMax (m + 1) + (2 * N + 3)) * vanEckPrefixMax (m + 1) :=
        Nat.mul_le_mul_right _ h_two_zc
}

/--
Half-Palette First-Entry Gate Supply Bound under `OnlyOddsAndZerosAfter N`: every zero `z ∈ Z`
(`N < z_0 < z ≤ B`, `a(z_0) = 0`, `a(z) = 0`) emitting `H < a(z - 1)` crosses `H` from the
`{0, odd}` palette `{0} ∪ (Odd ∩ [1, H])` of size `≤ (H + 1) / 2 + 1`.
-/
theorem only_odds_half_palette_large_birth_supply (N z_0 H B : ℕ) (Z : Finset ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz0_gt : N < z_0) (hz0 : vanEckNthTerm z_0 = 0)
    (hZ : ∀ z ∈ Z, z_0 < z ∧ z ≤ B ∧ vanEckNthTerm z = 0 ∧ H < vanEckNthTerm (z - 1)) :
    Z.card * (H + 1) ≤ ((H + 1) / 2 + 1) * ((B - (z_0 + 1)) + (H + 1)) := by {
  let P := (Finset.Icc 0 H).filter (fun v => v = 0 ∨ v % 2 = 1)
  have hP : ∀ k, z_0 ≤ k → k < B → vanEckNthTerm k ≤ H → vanEckNthTerm k ∈ P := by {
    intro k hk_lo _hk_hi hk_le
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨Nat.zero_le _, hk_le⟩,
      h_odds k (by { omega })⟩
  }
  have h_gate := large_pre_zero_palette_gate_supply Z P z_0 H B hz0 hP hZ
  have h_card := (odd_Icc_filter_card_le H).2
  change P.card ≤ (H + 1) / 2 + 1 at h_card
  exact le_trans h_gate (Nat.mul_le_mul_right _ h_card)
}

/--
Global `{0, odd}` Zero-Count Demand vs. Half-Palette Cooldown Supply: for any finite set `Z_all`
of zeros in `(z_0, B]` (`N < z_0`, `a(z_0) = 0`) and any threshold `H`,
`(Z_all.card - (H + 1) / 2) * (H + 1) ≤ ((H + 1) / 2 + 1) * ((B - (z_0 + 1)) + (H + 1))`.
-/
theorem only_odds_demand_vs_half_palette_supply (N z_0 H B : ℕ) (Z_all : Finset ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz0_gt : N < z_0) (hz0 : vanEckNthTerm z_0 = 0)
    (hZ : ∀ z ∈ Z_all, z_0 < z ∧ z ≤ B ∧ vanEckNthTerm z = 0) :
    (Z_all.card - (H + 1) / 2) * (H + 1) ≤
      ((H + 1) / 2 + 1) * ((B - (z_0 + 1)) + (H + 1)) := by {
  let Z_large := Z_all.filter (fun z => H < vanEckNthTerm (z - 1))
  have h_dem := (only_odds_large_birth_zero_demand N H Z_all h_odds
    (fun z hz => ⟨by { have := (hZ z hz).1; omega }, (hZ z hz).2.2⟩)).2
  change Z_all.card ≤ Z_large.card + (H + 1) / 2 at h_dem
  have h_sub_le : Z_all.card - (H + 1) / 2 ≤ Z_large.card := by { omega }
  have h_sup := only_odds_half_palette_large_birth_supply N z_0 H B Z_large h_odds hz0_gt hz0
    (fun z hz => by {
      rcases Finset.mem_filter.mp hz with ⟨hzA, hgt⟩
      have hp := hZ z hzA
      exact ⟨hp.1, hp.2.1, hp.2.2, hgt⟩
    })
  exact le_trans (Nat.mul_le_mul_right (H + 1) h_sub_le) h_sup
}

/--
Anchor-Floor Cooldown Packing over an Arbitrary Generator Set `P`: if every zero `z ∈ L` (`z ≥ 2`,
`z ≤ B`) has generator `a(z - 2) ∈ P`, anchor `A_0 ≤ z - 2 - a(z - 1)`, and `H < a(z - 1)`, then
`L.card * (H + 1) ≤ P.card * ((B - 2) - A_0)`.
-/
lemma generator_set_anchor_cooldown_bound (L P : Finset ℕ) (H A_0 B : ℕ)
    (hL : ∀ z ∈ L, z ≥ 2 ∧ vanEckNthTerm z = 0 ∧ vanEckNthTerm (z - 2) ∈ P ∧
      A_0 ≤ z - 2 - vanEckNthTerm (z - 1) ∧ z ≤ B ∧ H < vanEckNthTerm (z - 1)) :
    L.card * (H + 1) ≤ P.card * ((B - 2) - A_0) := by {
  have h_low : L.card * (H + 1) ≤ ∑ z ∈ L, vanEckNthTerm (z - 1) := by {
    have h_le : (∑ _z ∈ L, (H + 1)) ≤ ∑ z ∈ L, vanEckNthTerm (z - 1) :=
      Finset.sum_le_sum (fun z hz => (hL z hz).2.2.2.2.2)
    rw [Finset.sum_const, smul_eq_mul] at h_le
    exact h_le
  }
  have h_maps : ∀ z ∈ L, vanEckNthTerm (z - 2) ∈ P := fun z hz => (hL z hz).2.2.1
  have h_fib := Finset.sum_fiberwise_of_maps_to (s := L) (t := P)
    (g := fun z => vanEckNthTerm (z - 2)) h_maps (fun z => vanEckNthTerm (z - 1))
  have h_up : (∑ v ∈ P, ∑ z ∈ L.filter (fun z => vanEckNthTerm (z - 2) = v),
      vanEckNthTerm (z - 1)) ≤ ∑ _v ∈ P, ((B - 2) - A_0) := by {
    apply Finset.sum_le_sum
    intro v _hv
    apply single_generator_anchor_dormancy_sum_le _ v A_0 B
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzL, hzv⟩
    have hp := hL z hzL
    exact ⟨hp.1, hp.2.1, hzv, hp.2.2.2.1, hp.2.2.2.2.1⟩
  }
  rw [h_fib, Finset.sum_const, smul_eq_mul] at h_up
  exact le_trans h_low h_up
}

/--
Regime-3 Later-Return Jump Extraction: any jump zero `z` past `z_0 > N` (`H ≤ vanEckPrefixMax z_0`,
`z ≤ B`) that is neither a post-`N` first-return (`¬ (N < p(z) ∧ a(p(z) + 1) = 0)`) nor bounded by
`vanEckPrefixMax N` (`vanEckPrefixMax N < a(z - 2)`) has its generator born at a zero
`z_b ∈ [N + 2, B]`, anchor `N + 3 ≤ z - 2 - a(z - 1)`, and `H < a(z - 1)`.
-/
lemma only_odds_later_return_jump_spec (N z_0 H B z : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz0_gt : N < z_0) (hz0 : vanEckNthTerm z_0 = 0)
    (hH : H ≤ vanEckPrefixMax z_0) (hz_gt : z_0 < z) (hz_le : z ≤ B)
    (hz : vanEckNthTerm z = 0)
    (h_jump : vanEckPrefixMax (lastZero (z - 1)) < vanEckPrefixMax z)
    (h_not_first : ¬ (N < z - 2 - vanEckNthTerm (z - 1) ∧
      vanEckNthTerm (z - 2 - vanEckNthTerm (z - 1) + 1) = 0))
    (h_not_old : vanEckPrefixMax N < vanEckNthTerm (z - 2)) :
    vanEckNthTerm (z - 2) ∈
        (((Finset.Icc (N + 2) B).filter (fun z_b => vanEckNthTerm z_b = 0)).image
          (fun z_b => vanEckNthTerm (z_b - 1))) ∧
      N + 3 ≤ z - 2 - vanEckNthTerm (z - 1) ∧
      H < vanEckNthTerm (z - 1) := by {
  let z_prev := lastZero (z - 1)
  have hzp_le : z_prev ≤ z - 1 := lastZero_le (z - 1)
  have hzp_zero : vanEckNthTerm z_prev = 0 := vanEck_lastZero_is_zero (z - 1)
  have hz0_le_zp : z_0 ≤ z_prev := by {
    by_contra hc
    exact no_zero_after_lastZero (z - 1) z_0 (by { omega }) (by { omega }) hz0
  }
  have h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0 :=
    fun k hk1 hk2 => no_zero_after_lastZero (z - 1) k hk1 (by { omega })
  rcases only_odds_jump_birth_tripartition N z_prev z h_odds (by { omega }) (by { omega })
      hzp_zero hz h_gap h_jump with ⟨z_b, _, hzb_dist, hzb_zero, hzb_eq, h_tri⟩
  rcases h_tri with h_old | h_first | ⟨hzb_gt, r, hr_gt, hr_le_p, _, _, _, _, h_jlt, _⟩
  · omega
  · exfalso
    have hp_gt : N < z - 2 - vanEckNthTerm (z - 1) := by { omega }
    have hp_z : z - 2 - vanEckNthTerm (z - 1) + 1 = z_b := by { omega }
    rw [← hp_z] at hzb_zero
    exact h_not_first ⟨hp_gt, hzb_zero⟩
  · have hzb_mem : z_b ∈ (Finset.Icc (N + 2) B).filter (fun z_b => vanEckNthTerm z_b = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by { omega }, by { omega }⟩, hzb_zero⟩
    have h_img : vanEckNthTerm (z - 2) ∈
        ((Finset.Icc (N + 2) B).filter (fun z_b => vanEckNthTerm z_b = 0)).image
          (fun z_b => vanEckNthTerm (z_b - 1)) :=
      Finset.mem_image.mpr ⟨z_b, hzb_mem, hzb_eq⟩
    have h_mono := vanEckPrefixMax_mono z_0 z_prev hz0_le_zp
    have hH_lt : H < vanEckNthTerm (z - 1) :=
      Nat.lt_of_le_of_lt (Nat.le_trans hH h_mono) h_jlt
    exact ⟨h_img, by { omega }, hH_lt⟩
}

/--
Unified Window Record-Jump Supply Accounting under `OnlyOddsAndZerosAfter N`: any finite set `J`
of prefix-maximum jump zeros in `[A, B]` (`N < z_0 < z`, `a(z_0) = 0`, `H ≤ vanEckPrefixMax z_0`)
splits into `J_old`, `J_first`, and `J_later` with explicit upper bounds from old pre-`N` values,
post-`N` first returns, and post-`N` later-return cooldowns, while `J` as a whole simultaneously
obeys the half-palette first-entry gate bound.
-/
theorem only_odds_window_jump_total_supply (N z_0 H A B : ℕ) (J : Finset ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hz0_gt : N < z_0) (hz0 : vanEckNthTerm z_0 = 0)
    (hH : H ≤ vanEckPrefixMax z_0)
    (hJ : ∀ z ∈ J, z_0 < z ∧ A ≤ z ∧ z ≤ B ∧ vanEckNthTerm z = 0 ∧
      vanEckPrefixMax (lastZero (z - 1)) < vanEckPrefixMax z) :
    let isFirst : ℕ → Prop := fun z => N < z - 2 - vanEckNthTerm (z - 1) ∧
      vanEckNthTerm (z - 2 - vanEckNthTerm (z - 1) + 1) = 0
    let J_first := J.filter isFirst
    let J_old := J.filter (fun z => ¬ isFirst z ∧ vanEckNthTerm (z - 2) ≤ vanEckPrefixMax N)
    let J_later := J.filter (fun z => ¬ isFirst z ∧ vanEckPrefixMax N < vanEckNthTerm (z - 2))
    let Z_births := (Finset.Icc (N + 2) B).filter (fun z_b => vanEckNthTerm z_b = 0)
    J.card = J_old.card + J_first.card + J_later.card ∧
      J_old.card * (H + 1) ≤ vanEckPrefixMax N * ((B - A) + (H + 1)) ∧
      J_first.card ≤ Z_births.card ∧
      J_later.card * (H + 1) ≤ Z_births.card * ((B - 2) - (N + 3)) ∧
      J.card * (H + 1) ≤ ((H + 1) / 2 + 1) * ((B - (z_0 + 1)) + (H + 1)) := by {
  intro isFirst J_first J_old J_later Z_births
  have h_no_twos := only_odds_implies_no_twos N h_odds
  have h_p1 := Finset.card_filter_add_card_filter_not (s := J) isFirst
  let Jn := J.filter (fun z => ¬ isFirst z)
  have h_p2 := Finset.card_filter_add_card_filter_not
    (s := Jn) (fun z => vanEckNthTerm (z - 2) ≤ vanEckPrefixMax N)
  have h_old_eq : Jn.filter (fun z => vanEckNthTerm (z - 2) ≤ vanEckPrefixMax N) = J_old := by {
    rw [Finset.filter_filter]
  }
  have h_lat_eq : Jn.filter (fun z => ¬ vanEckNthTerm (z - 2) ≤ vanEckPrefixMax N) = J_later := by {
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun _ _ => and_congr_right (fun _ => not_le))
  }
  rw [h_old_eq, h_lat_eq] at h_p2
  change J_first.card + Jn.card = J.card at h_p1
  have h_old_bnd := no_twos_finite_palette_jump_window_bound N z_0 (vanEckPrefixMax N) H A B
    J_old h_no_twos hz0_gt hz0 hH (fun z hz => by {
      rcases Finset.mem_filter.mp hz with ⟨hzJ, _, hle⟩
      have hp := hJ z hzJ
      exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hle, hp.2.2.2.2⟩
    })
  have h_first_bnd := first_return_jumps_le_birth_zeros J_first (N + 2) B (fun z hz => by {
    rcases Finset.mem_filter.mp hz with ⟨hzJ, hp_gt, hp_z⟩
    have hp := hJ z hzJ
    exact ⟨by { omega }, hp.2.2.2.1, by { omega }, by { omega }, hp_z⟩
  })
  let P_b := Z_births.image (fun z_b => vanEckNthTerm (z_b - 1))
  have h_lat_p := generator_set_anchor_cooldown_bound J_later P_b H (N + 3) B (fun z hz => by {
    rcases Finset.mem_filter.mp hz with ⟨hzJ, hnf, hno⟩
    have hp := hJ z hzJ
    have hsp := only_odds_later_return_jump_spec N z_0 H B z h_odds hz0_gt hz0 hH
      hp.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 hnf hno
    exact ⟨by { omega }, hp.2.2.2.1, hsp.1, hsp.2.1, hp.2.2.1, hsp.2.2⟩
  })
  have h_lat_bnd : J_later.card * (H + 1) ≤ Z_births.card * ((B - 2) - (N + 3)) :=
    le_trans h_lat_p (Nat.mul_le_mul_right _ Finset.card_image_le)
  have h_gate_bnd := only_odds_half_palette_large_birth_supply N z_0 H B J h_odds hz0_gt hz0
    (fun z hz => by {
      have hp := hJ z hz
      have hzp_le : lastZero (z - 1) ≤ z - 1 := lastZero_le (z - 1)
      have hz0_le_zp : z_0 ≤ lastZero (z - 1) := by {
        by_contra hc
        exact no_zero_after_lastZero (z - 1) z_0 (by { omega }) (by { omega }) hz0
      }
      have h_dorm := no_twos_prefixMax_jump_requires_dormant_generator N z (lastZero (z - 1))
        h_no_twos (by { omega }) hp.2.2.2.1 (by { omega }) (vanEck_lastZero_is_zero (z - 1))
        (by { omega }) (fun k hk1 hk2 => no_zero_after_lastZero (z - 1) k hk1 (by { omega }))
        hp.2.2.2.2
      have h_mono := vanEckPrefixMax_mono z_0 (lastZero (z - 1)) hz0_le_zp
      have hH_lt : H < vanEckNthTerm (z - 1) :=
        Nat.lt_of_le_of_lt (Nat.le_trans hH h_mono) (hp.2.2.2.2.trans_eq h_dorm.1)
      exact ⟨hp.1, hp.2.2.1, hp.2.2.2.1, hH_lt⟩
    })
  exact ⟨by { omega }, h_old_bnd, h_first_bnd, h_lat_bnd, h_gate_bnd⟩
}

/--
Same-Parity Anchor Obstruction: under `OnlyOddsAndZerosAfter N`, if `vanEckNthTerm m` (`m ≥ N`)
has most-recent prior occurrence `p` (`lastOccBefore m (a m) = some p`), then `p % 2 ≠ m % 2`
and `(m - p) % 2 = 1` — selecting a live symbol whose anchor shares `m`'s parity is forbidden.
-/
lemma only_odds_same_parity_anchor_impossible (N m p : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hm : N ≤ m)
    (h_occ : lastOccBefore m (vanEckNthTerm m) = some p) :
    p % 2 ≠ m % 2 ∧ (m - p) % 2 = 1 := by {
  have hp_lt := (lastOccBefore_eq_some_spec m (vanEckNthTerm m) p h_occ).1
  have h_next := vanEck_next_eq_of_lastOccBefore m
  rw [h_occ] at h_next
  change vanEckNthTerm (m + 1) = m - p at h_next
  rcases h_odds (m + 1) (by { omega }) with hz | hodd
  · omega
  · rw [h_next] at hodd
    exact ⟨by { omega }, hodd⟩
}

/--
Live-Age Parity Obstruction: under `OnlyOddsAndZerosAfter N`, at every index `m ≥ N`, any live
selected symbol (`symbolAge m (a m) = some d`) must have odd age `d % 2 = 1`, whereas every
unselected live symbol's age increments by `1` (`d ↦ d + 1`), flipping parity at each step.
-/
lemma only_odds_even_age_selection_impossible (N m d : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hm : N ≤ m)
    (h_age : symbolAge m (vanEckNthTerm m) = some d) :
    d % 2 = 1 := by {
  unfold symbolAge at h_age
  cases h_occ : lastOccBefore m (vanEckNthTerm m) with
  | none =>
    rw [h_occ] at h_age
    simp at h_age
  | some p =>
    rw [h_occ] at h_age
    simp only [Option.map, Option.some.injEq] at h_age
    have h_odd := (only_odds_same_parity_anchor_impossible N m p h_odds hm h_occ).2
    rw [← h_age]
    exact h_odd
}

/--
Sharp Small-Palette Parity-Collision Theorem (`H = 3`, `P = {1, 3}`):
Under `OnlyOddsAndZerosAfter N`, no `4` consecutive terms past `N` can stay inside `{1, 3}`
(parity collisions with `[1, 3, 1] → 2`, `[3, 1, 3] → 2`, and `[1, 3, 3, 1] → 3 → 2` cut the
generic clamped-automaton bound `2 * 4^2 = 32` down to `3`).
-/
theorem only_odds_no_four_in_one_three (N A : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hA : N < A) :
    ¬ (∀ j < 4, vanEckNthTerm (A + j) ∈ ({1, 3} : Finset ℕ)) := by {
  intro h_run
  have h_no2 := only_odds_implies_no_twos N h_odds
  have h_mem : ∀ j < 4, vanEckNthTerm (A + j) = 1 ∨ vanEckNthTerm (A + j) = 3 := by {
    intro j hj
    have hm := h_run j hj
    simp only [Finset.mem_insert, Finset.mem_singleton] at hm
    exact hm
  }
  have h0 : vanEckNthTerm A = 1 ∨ vanEckNthTerm A = 3 := h_mem 0 (by { omega })
  rcases h0 with ha0 | ha0
  · rcases h_mem 1 (by { omega }) with ha1 | ha1
    · exact vanEck_no_stutter_one A ⟨ha0, ha1⟩
    · rcases h_mem 2 (by { omega }) with ha2 | ha2
      · exact h_no2 (A + 3) (by { omega })
          (vanEck_alt_pair_emits_two A (ha0.trans ha2.symm) (by { omega }))
      · have ha3 : vanEckNthTerm (A + 3) = 1 :=
          vanEck_stutter_emits_one (A + 1) (ha1.trans ha2.symm)
        have ha4 : vanEckNthTerm (A + 4) = 3 :=
          vanEck_gap_three_emits_three A (ha0.trans ha3.symm) (by { omega }) (by { omega })
        have hne23 : vanEckNthTerm (A + 2 + 1) ≠ vanEckNthTerm (A + 2) := by {
          change vanEckNthTerm (A + 3) ≠ vanEckNthTerm (A + 2)
          omega
        }
        exact h_no2 (A + 5) (by { omega })
          (vanEck_alt_pair_emits_two (A + 2) (ha2.trans ha4.symm) hne23)
  · rcases h_mem 1 (by { omega }) with ha1 | ha1
    · rcases h_mem 2 (by { omega }) with ha2 | ha2
      · exact vanEck_no_stutter_one (A + 1) ⟨ha1, ha2⟩
      · exact h_no2 (A + 3) (by { omega })
          (vanEck_alt_pair_emits_two A (ha0.trans ha2.symm) (by { omega }))
    · have ha2 : vanEckNthTerm (A + 2) = 1 := vanEck_stutter_emits_one A (ha0.trans ha1.symm)
      rcases h_mem 3 (by { omega }) with ha3 | ha3
      · exact vanEck_no_stutter_one (A + 2) ⟨ha2, ha3⟩
      · have hne12 : vanEckNthTerm (A + 1 + 1) ≠ vanEckNthTerm (A + 1) := by {
          change vanEckNthTerm (A + 2) ≠ vanEckNthTerm (A + 1)
          omega
        }
        exact h_no2 (A + 4) (by { omega })
          (vanEck_alt_pair_emits_two (A + 1) (ha1.trans ha3.symm) hne12)
}

/--
Parity-Aware Finite-Palette Zero-Free Obstruction:
Under `OnlyOddsAndZerosAfter N`, for any threshold `H` (`K = (H + 1) / 2`) and `A > N`, any
window `[A, A + L]` of length `L + 1 > K * (H + 1) ^ K` must exit `{1, 3, ..., H}` — emitting
either `0` or an odd term `> H`.
-/
theorem only_odds_bounded_palette_run_obstruction (N H A L : ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hA : N < A)
    (hL : ((H + 1) / 2) * (H + 1) ^ ((H + 1) / 2) < L + 1) :
    ∃ t ≤ L, vanEckNthTerm (A + t) = 0 ∨ H < vanEckNthTerm (A + t) := by {
  by_contra hc
  let P := (Finset.Icc 1 H).filter (fun v => v % 2 = 1)
  have hP : ∀ v ∈ P, 1 ≤ v ∧ v ≤ H := by {
    intro v hv
    exact Finset.mem_Icc.mp (Finset.mem_filter.mp hv).1
  }
  have h_run : ∀ t ≤ L, vanEckNthTerm (A + t) ∈ P := by {
    intro t ht
    have hnz : vanEckNthTerm (A + t) ≠ 0 := fun hz => hc ⟨t, ht, Or.inl hz⟩
    have hle : vanEckNthTerm (A + t) ≤ H :=
      Nat.le_of_not_lt (fun hgt => hc ⟨t, ht, Or.inr hgt⟩)
    rcases h_odds (A + t) (by { omega }) with hz | hodd
    · exact False.elim (hnz hz)
    · exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by { omega }, hle⟩, hodd⟩
  }
  have h_len := finite_palette_run_length_bound P H A L hP h_run
  have h_card : P.card ≤ (H + 1) / 2 := (odd_Icc_filter_card_le H).1
  have h_pow : P.card * (H + 1) ^ P.card ≤ ((H + 1) / 2) * (H + 1) ^ ((H + 1) / 2) :=
    Nat.mul_le_mul h_card (Nat.pow_le_pow_right (Nat.succ_pos H) h_card)
  omega
}

/--
Small-Palette Exit Gate Bound:
Under `OnlyOddsAndZerosAfter N`, for any window `[A, B]` (`N + 1 < A`) and any set `M` of
indices `m ∈ [A, B]` where the sequence leaves `{0, 1, 3, ..., H}` (`a(m - 1) ≤ H < a(m)`),
`M.card * (H + 1) ≤ ((H + 1) / 2 + 1) * ((B - A) + (H + 1))`.
-/
theorem only_odds_small_palette_exit_gate_bound (N H A B : ℕ) (M : Finset ℕ)
    (h_odds : OnlyOddsAndZerosAfter N) (hA : N + 1 < A)
    (hM : ∀ m ∈ M, A ≤ m ∧ m ≤ B ∧ vanEckNthTerm (m - 1) ≤ H ∧ H < vanEckNthTerm m) :
    M.card * (H + 1) ≤ ((H + 1) / 2 + 1) * ((B - A) + (H + 1)) := by {
  let P_odd := (Finset.Icc 1 H).filter (fun v => v % 2 = 1)
  let P_0 := insert 0 P_odd
  have hM_P : ∀ m ∈ M, A ≤ m ∧ m ≤ B ∧ vanEckNthTerm (m - 1) ∈ P_0 ∧ H < vanEckNthTerm m := by {
    intro m hm
    have hp := hM m hm
    have hmem : vanEckNthTerm (m - 1) ∈ P_0 := by {
      rcases h_odds (m - 1) (by { omega }) with hz | hodd
      · exact Finset.mem_insert.mpr (Or.inl hz)
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_filter.mpr
          ⟨Finset.mem_Icc.mpr ⟨by { omega }, hp.2.2.1⟩, hodd⟩))
    }
    exact ⟨hp.1, hp.2.1, hmem, hp.2.2.2⟩
  }
  have h_bnd := palette_set_all_index_window_cooldown_bound M P_0 H A B hM_P
  have h_c0 : P_0.card ≤ P_odd.card + 1 := Finset.card_insert_le 0 P_odd
  have h_codd : P_odd.card ≤ (H + 1) / 2 := (odd_Icc_filter_card_le H).1
  exact le_trans h_bnd (Nat.mul_le_mul_right _ (by { omega }))
}

/--
Most-recent prior occurrence of `v` strictly before `m` in an arbitrary sequence `f : ℕ → ℕ`.
-/
def lastOccBeforeFn (f : ℕ → ℕ) : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | m + 1, v => if f m = v then some m else lastOccBeforeFn f m v

/--
`IsVanEckFrom f z_0` states that `f` obeys the exact Van Eck recurrence from index `z_0` onward
(allowing `f` to carry an arbitrary prefix history on `[0, z_0]`).
-/
def IsVanEckFrom (f : ℕ → ℕ) (z_0 : ℕ) : Prop :=
  ∀ m ≥ z_0, f (m + 1) =
    match lastOccBeforeFn f m (f m) with
    | none => 0
    | some p => m - p

/--
`lastOccBeforeFn vanEckNthTerm` agrees everywhere with `lastOccBefore`.
-/
lemma lastOccBeforeFn_vanEckNthTerm (m v : ℕ) :
    lastOccBeforeFn vanEckNthTerm m v = lastOccBefore m v := by {
  induction m with
  | zero => rfl
  | succ k ih =>
    simp only [lastOccBeforeFn, lastOccBefore, ih]
}

/--
The true Van Eck sequence `vanEckNthTerm` satisfies `IsVanEckFrom vanEckNthTerm z_0` for all `z_0`.
-/
lemma vanEckNthTerm_isVanEckFrom (z_0 : ℕ) : IsVanEckFrom vanEckNthTerm z_0 := by {
  intro m _hm
  rw [lastOccBeforeFn_vanEckNthTerm]
  exact vanEck_next_eq_of_lastOccBefore m
}

/--
`lastOccBeforeFn f m v = none` iff `v` never appears in `f` on `[0, m)`.
-/
lemma lastOccBeforeFn_eq_none_iff (f : ℕ → ℕ) (m v : ℕ) :
    lastOccBeforeFn f m v = none ↔ ∀ i < m, f i ≠ v := by {
  induction m with
  | zero => simp [lastOccBeforeFn]
  | succ k ih =>
    simp only [lastOccBeforeFn]
    split_ifs with hk
    · constructor
      · intro h
        nomatch h
      · intro h_all
        exact False.elim (h_all k (Nat.lt_succ_self k) hk)
    · rw [ih]
      constructor
      · intro h_prev i hi
        rcases lt_or_eq_of_le (Nat.le_of_lt_succ hi) with hlt | rfl
        · exact h_prev i hlt
        · exact hk
      · exact fun h_all i hi => h_all i (Nat.lt_succ_of_lt hi)
}

/--
Specification of `lastOccBeforeFn f m v = some p`.
-/
lemma lastOccBeforeFn_eq_some_spec (f : ℕ → ℕ) (m v p : ℕ)
    (h : lastOccBeforeFn f m v = some p) :
    p < m ∧ f p = v ∧ ∀ j, p < j → j < m → f j ≠ v := by {
  induction m with
  | zero => simp [lastOccBeforeFn] at h
  | succ k ih =>
    simp only [lastOccBeforeFn] at h
    split_ifs at h with hk
    · injection h with hp_eq
      subst hp_eq
      exact ⟨Nat.lt_succ_self k, hk, fun _ hj1 hj2 => by { omega }⟩
    · have h_prev := ih h
      refine ⟨Nat.lt_succ_of_lt h_prev.1, h_prev.2.1, ?_⟩
      intro j hj1 hj2
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj2) with hlt | rfl
      · exact h_prev.2.2 j hj1 hlt
      · exact hk
}

/--
If `v` never occurs in `[z_0, m)`, `lastOccBeforeFn f m v = lastOccBeforeFn f z_0 v`.
-/
lemma lastOccBeforeFn_no_hit_tail (f : ℕ → ℕ) (z_0 m v : ℕ) (hm : z_0 ≤ m)
    (h_no : ∀ j, z_0 ≤ j → j < m → f j ≠ v) :
    lastOccBeforeFn f m v = lastOccBeforeFn f z_0 v := by {
  induction m with
  | zero =>
    have hz : z_0 = 0 := by { omega }
    rw [hz]
  | succ k ih =>
    rcases eq_or_lt_of_le hm with rfl | hlt
    · rfl
    · have hne : f k ≠ v := h_no k (by { omega }) (Nat.lt_succ_self k)
      simp only [lastOccBeforeFn, if_neg hne]
      exact ih (by { omega }) (fun j hj1 hj2 => h_no j hj1 (Nat.lt_succ_of_lt hj2))
}

/--
Most-recently-used head lookup in an association list `(symbol, index)`.
-/
def lookupHead (k : ℕ) : List (ℕ × ℕ) → Option ℕ
  | [] => none
  | (w, q) :: rest => if Nat.beq k w then some q else lookupHead k rest

/--
Removes the first occurrence of `x` from a list of free prefix anchor positions.
-/
def removeFirst (x : ℕ) : List ℕ → List ℕ
  | [] => []
  | y :: ys => if Nat.beq x y then ys else y :: removeFirst x ys

/--
Checks predicate `g` on all candidate prefix anchors `p ∈ free` with `(m - p) % 2 = 1`.
-/
def allFreeOdd : (ℕ → Bool) → ℕ → List ℕ → Bool
  | _, _, [] => true
  | g, m, p :: ps =>
    (if Nat.beq ((m - p) % 2) 1 then g p else true) && allFreeOdd g m ps

/--
Computable lazy-prefix DFS refutation checker: verifies that from `(m, cur, tailMap, free)`, every
branch of a sequence obeying `IsVanEckFrom` must emit a positive even gap within `fuel` steps.
-/
def refuteFast : ℕ → ℕ → ℕ → List (ℕ × ℕ) → List ℕ → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, m, cur, tailMap, free =>
    match lookupHead cur tailMap with
    | some q =>
      let nxt := m - q
      if Nat.beq (nxt % 2) 0 then true
      else refuteFast fuel (m + 1) nxt ((cur, m) :: tailMap) free
    | none =>
      let tailMap' := (cur, m) :: tailMap
      refuteFast fuel (m + 1) 0 tailMap' free &&
        allFreeOdd (fun p => refuteFast fuel (m + 1) (m - p) tailMap' (removeFirst p free))
          m free

/--
Universal prefix certificate checker at zero `z0`: verifies `refuteFast` across all odd initial
zero-gaps `z0 - zPrev` (`1 ≤ zPrev < z0`) with `free = { p ∈ [2, z0 - 1] | p ≠ zPrev }`.
-/
def refuteZ0Fast (z0 fuel : ℕ) : Bool :=
  (List.range z0).all (fun zPrev =>
    if Nat.ble 1 zPrev && Nat.beq ((z0 - zPrev) % 2) 1 then
      let free := (List.range z0).filter (fun p => Nat.ble 2 p && !Nat.beq p zPrev)
      refuteFast fuel (z0 + 1) (z0 - zPrev) [(0, z0)] free
    else true)

lemma lookupHead_cons (k cur m : ℕ) (tailMap : List (ℕ × ℕ)) :
    lookupHead k ((cur, m) :: tailMap) = if k = cur then some m else lookupHead k tailMap := by {
  simp only [lookupHead, Nat.beq_eq]
}

lemma mem_removeFirst_of_ne (x y : ℕ) (ys : List ℕ) (h_mem : y ∈ ys) (h_ne : y ≠ x) :
    y ∈ removeFirst x ys := by {
  induction ys with
  | nil => simp at h_mem
  | cons z zs ih =>
    simp only [removeFirst]
    cases hbeq : Nat.beq x z with
    | false =>
      rcases List.mem_cons.mp h_mem with rfl | h_tail
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (ih h_tail))
    | true =>
      have hxz : x = z := Nat.beq_eq.mp hbeq
      rcases List.mem_cons.mp h_mem with rfl | h_tail
      · exact False.elim (h_ne hxz.symm)
      · exact h_tail
}

lemma allFreeOdd_spec (g : ℕ → Bool) (m : ℕ) (free : List ℕ)
    (h : allFreeOdd g m free = true) (p : ℕ) (hp : p ∈ free) (hodd : (m - p) % 2 = 1) :
    g p = true := by {
  induction free with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [allFreeOdd, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hp with rfl | h_tail
    · have hbeq : Nat.beq ((m - p) % 2) 1 = true := Nat.beq_eq.mpr hodd
      rw [hbeq, if_pos rfl] at h
      exact h.1
    · exact ih h.2 h_tail
}

/--
Abstraction invariant relating a concrete sequence `f` (`IsVanEckFrom f z_0`) at step `m > z_0`
to the lazy-prefix DFS state `(m, cur, tailMap, free)`.
-/
structure ValidDFSState (f : ℕ → ℕ) (z_0 m cur : ℕ)
    (tailMap : List (ℕ × ℕ)) (free : List ℕ) : Prop where
  hm : z_0 < m
  hcur : f m = cur
  hzero : ∃ qz, lookupHead 0 tailMap = some qz
  htail_some : ∀ v q, lookupHead v tailMap = some q →
    z_0 ≤ q ∧ q < m ∧ lastOccBeforeFn f m v = some q
  htail_none : ∀ v, lookupHead v tailMap = none →
    ∀ j, z_0 ≤ j → j < m → f j ≠ v
  hfree : ∀ v p, v ≠ 0 → lookupHead v tailMap = none →
    lastOccBeforeFn f z_0 v = some p → p ∈ free

lemma validDFSState_step_tail (f : ℕ → ℕ) (z_0 m cur nxt : ℕ)
    (tailMap : List (ℕ × ℕ)) (free free' : List ℕ)
    (hs : ValidDFSState f z_0 m cur tailMap free) (hnxt : f (m + 1) = nxt)
    (hfree' : ∀ v p, v ≠ 0 → lookupHead v ((cur, m) :: tailMap) = none →
      lastOccBeforeFn f z_0 v = some p → p ∈ free') :
    ValidDFSState f z_0 (m + 1) nxt ((cur, m) :: tailMap) free' := by {
  refine ⟨Nat.lt_succ_of_lt hs.hm, hnxt, ?_, ?_, ?_, hfree'⟩
  · rw [lookupHead_cons]
    split_ifs
    · exact ⟨m, rfl⟩
    · exact hs.hzero
  · intro v q hlk
    rw [lookupHead_cons] at hlk
    split_ifs at hlk with hvc
    · injection hlk with hqm
      subst hqm
      have hfm : f m = v := hs.hcur.trans hvc.symm
      exact ⟨Nat.le_of_lt hs.hm, Nat.lt_succ_self m, by { simp [lastOccBeforeFn, hfm] }⟩
    · have hprev := hs.htail_some v q hlk
      have hfm : f m ≠ v := fun heq => hvc (heq.symm.trans hs.hcur)
      exact ⟨hprev.1, Nat.lt_succ_of_lt hprev.2.1,
        by { simp [lastOccBeforeFn, if_neg hfm, hprev.2.2] }⟩
  · intro v hlk j hj1 hj2
    rw [lookupHead_cons] at hlk
    split_ifs at hlk with hvc
    rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj2) with hlt | rfl
    · exact hs.htail_none v hlk j hj1 hlt
    · exact fun heq => hvc (heq.symm.trans hs.hcur)
}

lemma refuteFast_none_branch (f : ℕ → ℕ) (z_0 fuel m cur : ℕ)
    (tailMap : List (ℕ × ℕ)) (free : List ℕ) (h_rec : IsVanEckFrom f z_0)
    (ih : ∀ m' cur' tailMap' free', refuteFast fuel m' cur' tailMap' free' = true →
      ValidDFSState f z_0 m' cur' tailMap' free' →
      ∃ k, m' < k ∧ k ≤ m' + fuel ∧ f k ≠ 0 ∧ f k % 2 = 0)
    (hs : ValidDFSState f z_0 m cur tailMap free) (hlk : lookupHead cur tailMap = none)
    (h_zero_br : refuteFast fuel (m + 1) 0 ((cur, m) :: tailMap) free = true)
    (h_free_br : allFreeOdd
      (fun p => refuteFast fuel (m + 1) (m - p) ((cur, m) :: tailMap) (removeFirst p free))
      m free = true) :
    ∃ k, m < k ∧ k ≤ m + (fuel + 1) ∧ f k ≠ 0 ∧ f k % 2 = 0 := by {
  have hcur_nz : cur ≠ 0 := by {
    intro hc0
    rcases hs.hzero with ⟨qz, hqz⟩
    rw [← hc0, hlk] at hqz
    nomatch hqz
  }
  have h_occ_eq := lastOccBeforeFn_no_hit_tail f z_0 m cur (Nat.le_of_lt hs.hm)
    (hs.htail_none cur hlk)
  have h_step_rec := h_rec m (Nat.le_of_lt hs.hm)
  rw [hs.hcur, h_occ_eq] at h_step_rec
  cases h_z0_occ : lastOccBeforeFn f z_0 cur with
  | none =>
    rw [h_z0_occ] at h_step_rec
    have hs' := validDFSState_step_tail f z_0 m cur 0 tailMap free free hs h_step_rec
      (fun v p hv hlk' hp => by {
        rw [lookupHead_cons] at hlk'
        split_ifs at hlk'
        exact hs.hfree v p hv hlk' hp
      })
    rcases ih (m + 1) 0 ((cur, m) :: tailMap) free h_zero_br hs' with ⟨k, hk1, hk2, hknz, hkev⟩
    exact ⟨k, by { omega }, by { omega }, hknz, hkev⟩
  | some p =>
    rw [h_z0_occ] at h_step_rec
    change f (m + 1) = m - p at h_step_rec
    have hp_sp := lastOccBeforeFn_eq_some_spec f z_0 cur p h_z0_occ
    by_cases hpar : (m - p) % 2 = 0
    · have hm_gt := hs.hm
      have hp_lt := hp_sp.1
      have hfnz : f (m + 1) ≠ 0 := h_step_rec.symm ▸ (show m - p ≠ 0 by { omega })
      have hfev : f (m + 1) % 2 = 0 := h_step_rec.symm ▸ hpar
      exact ⟨m + 1, Nat.lt_succ_self m, by { omega }, hfnz, hfev⟩
    · have hodd : (m - p) % 2 = 1 := by { omega }
      have href' := allFreeOdd_spec _ m free h_free_br p
        (hs.hfree cur p hcur_nz hlk h_z0_occ) hodd
      have hs' := validDFSState_step_tail f z_0 m cur (m - p) tailMap free (removeFirst p free)
        hs h_step_rec (fun v p' hv hlk' hp' => by {
          rw [lookupHead_cons] at hlk'
          split_ifs at hlk' with hvc
          have hp'_sp := lastOccBeforeFn_eq_some_spec f z_0 v p' hp'
          have hne_p : p' ≠ p := fun heq => hvc (hp'_sp.2.1.symm.trans (heq ▸ hp_sp.2.1))
          exact mem_removeFirst_of_ne p p' free (hs.hfree v p' hv hlk' hp') hne_p
        })
      rcases ih (m + 1) (m - p) ((cur, m) :: tailMap) (removeFirst p free) href' hs' with
        ⟨k, hk1, hk2, hknz, hkev⟩
      exact ⟨k, by { omega }, by { omega }, hknz, hkev⟩
}

/--
Soundness of `refuteFast`: whenever `refuteFast fuel m cur tailMap free = true` on a valid DFS
abstraction of `f`, `f` emits a positive even term at some `m < k ≤ m + fuel`.
-/
lemma refuteFast_sound (f : ℕ → ℕ) (z_0 : ℕ) (h_rec : IsVanEckFrom f z_0) :
    ∀ (fuel m cur : ℕ) (tailMap : List (ℕ × ℕ)) (free : List ℕ),
      refuteFast fuel m cur tailMap free = true →
      ValidDFSState f z_0 m cur tailMap free →
      ∃ k, m < k ∧ k ≤ m + fuel ∧ f k ≠ 0 ∧ f k % 2 = 0 := by {
  intro fuel
  induction fuel with
  | zero =>
    intro m cur tailMap free h_ref
    simp [refuteFast] at h_ref
  | succ fuel ih =>
    intro m cur tailMap free h_ref hs
    simp only [refuteFast] at h_ref
    cases hlk : lookupHead cur tailMap with
    | some q =>
      rw [hlk] at h_ref
      dsimp only at h_ref
      have hq := hs.htail_some cur q hlk
      have h_step_rec := h_rec m (Nat.le_of_lt hs.hm)
      rw [hs.hcur, hq.2.2] at h_step_rec
      change f (m + 1) = m - q at h_step_rec
      cases hbeq : Nat.beq ((m - q) % 2) 0 with
      | true =>
        have hev : (m - q) % 2 = 0 := Nat.beq_eq.mp hbeq
        have hq_lt := hq.2.1
        have hfnz : f (m + 1) ≠ 0 := h_step_rec.symm ▸ (show m - q ≠ 0 by { omega })
        have hfev : f (m + 1) % 2 = 0 := h_step_rec.symm ▸ hev
        exact ⟨m + 1, Nat.lt_succ_self m, by { omega }, hfnz, hfev⟩
      | false =>
        rw [hbeq, if_neg (by { decide })] at h_ref
        have hs' := validDFSState_step_tail f z_0 m cur (m - q) tailMap free free hs h_step_rec
          (fun v p hv hlk' hp => by {
            rw [lookupHead_cons] at hlk'
            split_ifs at hlk'
            exact hs.hfree v p hv hlk' hp
          })
        rcases ih (m + 1) (m - q) ((cur, m) :: tailMap) free h_ref hs' with
          ⟨k, hk1, hk2, hknz, hkev⟩
        exact ⟨k, by { omega }, by { omega }, hknz, hkev⟩
    | none =>
      rw [hlk] at h_ref
      simp only [Bool.and_eq_true] at h_ref
      exact refuteFast_none_branch f z_0 fuel m cur tailMap free h_rec ih hs hlk h_ref.1 h_ref.2
}

lemma validDFSState_init_z0 (f : ℕ → ℕ) (z_0 z_prev : ℕ)
    (hf0 : f 0 = 0) (hf1 : f 1 = 0) (hfz0 : f z_0 = 0)
    (h_f1 : f (z_0 + 1) = z_0 - z_prev) (hzp_zero : f z_prev = 0) :
    ValidDFSState f z_0 (z_0 + 1) (z_0 - z_prev) [(0, z_0)]
      ((List.range z_0).filter (fun p => Nat.ble 2 p && !Nat.beq p z_prev)) := by {
  refine ⟨Nat.lt_succ_self z_0, h_f1, ⟨z_0, rfl⟩, ?_, ?_, ?_⟩
  · intro v q hlk
    rw [lookupHead_cons] at hlk
    split_ifs at hlk with hv0
    · injection hlk with hq
      subst hq
      subst hv0
      exact ⟨le_rfl, Nat.lt_succ_self z_0, by { simp [lastOccBeforeFn, hfz0] }⟩
    · simp [lookupHead] at hlk
  · intro v hlk j hj1 hj2
    rw [lookupHead_cons] at hlk
    split_ifs at hlk with hv0
    have hj_eq : j = z_0 := by { omega }
    rw [hj_eq, hfz0]
    exact Ne.symm hv0
  · intro v p hv _hlk hp
    have hp_sp := lastOccBeforeFn_eq_some_spec f z_0 v p hp
    have hp_ge2 : 2 ≤ p := by {
      by_contra hc
      interval_cases p
      · exact hv (hp_sp.2.1.symm.trans hf0)
      · exact hv (hp_sp.2.1.symm.trans hf1)
    }
    have hp_ne : Nat.beq p z_prev = false := by {
      cases hb : Nat.beq p z_prev with
      | false => rfl
      | true =>
        have heq := Nat.beq_eq.mp hb
        rw [heq, hzp_zero] at hp_sp
        exact False.elim (hv hp_sp.2.1.symm)
    }
    refine List.mem_filter.mpr ⟨List.mem_range.mpr hp_sp.1, ?_⟩
    rw [Bool.and_eq_true, Nat.ble_eq, hp_ne]
    exact ⟨hp_ge2, rfl⟩
}

/--
Soundness of `refuteZ0Fast`: if `refuteZ0Fast z_0 fuel = true`, then EVERY sequence `f : ℕ → ℕ`
with `f 0 = 0`, `f 1 = 0`, `f z_0 = 0` obeying `IsVanEckFrom f z_0` must emit a positive even
term at some `z_0 < k ≤ z_0 + 1 + fuel`, regardless of its prefix values on `[2, z_0 - 1]`.
-/
theorem refuteZ0Fast_sound (f : ℕ → ℕ) (z_0 fuel : ℕ)
    (hz0_ge : 2 ≤ z_0) (hf0 : f 0 = 0) (hf1 : f 1 = 0) (hfz0 : f z_0 = 0)
    (h_rec : IsVanEckFrom f z_0) (h_cert : refuteZ0Fast z_0 fuel = true) :
    ∃ k, z_0 < k ∧ k ≤ z_0 + 1 + fuel ∧ f k ≠ 0 ∧ f k % 2 = 0 := by {
  cases h_occ0 : lastOccBeforeFn f z_0 0 with
  | none =>
    exact False.elim (((lastOccBeforeFn_eq_none_iff f z_0 0).mp h_occ0) 1 (by { omega }) hf1)
  | some z_prev =>
    have hzp := lastOccBeforeFn_eq_some_spec f z_0 0 z_prev h_occ0
    have hzp_ge1 : 1 ≤ z_prev := by {
      by_contra hc
      exact hzp.2.2 1 (by { omega }) (by { omega }) hf1
    }
    have h_f1 := h_rec z_0 le_rfl
    rw [hfz0, h_occ0] at h_f1
    change f (z_0 + 1) = z_0 - z_prev at h_f1
    by_cases hpar : (z_0 - z_prev) % 2 = 0
    · have hzp_lt := hzp.1
      have hfnz : f (z_0 + 1) ≠ 0 := h_f1.symm ▸ (show z_0 - z_prev ≠ 0 by { omega })
      have hfev : f (z_0 + 1) % 2 = 0 := h_f1.symm ▸ hpar
      exact ⟨z_0 + 1, Nat.lt_succ_self z_0, by { omega }, hfnz, hfev⟩
    · have hodd : (z_0 - z_prev) % 2 = 1 := by { omega }
      have hall := (List.all_eq_true.mp h_cert) z_prev (List.mem_range.mpr hzp.1)
      have hcond : (Nat.ble 1 z_prev && Nat.beq ((z_0 - z_prev) % 2) 1) = true := by {
        rw [Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq]
        exact ⟨hzp_ge1, hodd⟩
      }
      rw [hcond, if_pos rfl] at hall
      have hs0 := validDFSState_init_z0 f z_0 z_prev hf0 hf1 hfz0 h_f1 hzp.2.1
      rcases refuteFast_sound f z_0 h_rec fuel (z_0 + 1) (z_0 - z_prev) [(0, z_0)] _ hall hs0 with
        ⟨k, hk1, hk2, hknz, hkev⟩
      exact ⟨k, by { omega }, by { omega }, hknz, hkev⟩
}

/--
Kernel-Checked Boolean Certificate for `z_0 = 12` (`135,582` DFS states across odd `12 - zPrev`).
-/
lemma refuteZ0Fast_twelve_cert : refuteZ0Fast 12 45 = true := by {
  decide +kernel
}

/--
Kernel-Checked `z_0 = 12` Universal Admissible-Prefix Certificate:
Every sequence `f : ℕ → ℕ` with `f 0 = 0`, `f 1 = 0`, `f 12 = 0` obeying the Van Eck recurrence
from index `12` onward (`IsVanEckFrom f 12`) — regardless of what arbitrary unbounded values
occupy `[2, 11]` — must emit a positive even term at some `12 < k ≤ 58`.
-/
theorem z0_twelve_universal_prefix_obstruction (f : ℕ → ℕ)
    (hf0 : f 0 = 0) (hf1 : f 1 = 0) (hf12 : f 12 = 0)
    (h_rec : IsVanEckFrom f 12) :
    ∃ k, 12 < k ∧ k ≤ 58 ∧ f k ≠ 0 ∧ f k % 2 = 0 := by {
  exact refuteZ0Fast_sound f 12 45 (by { omega }) hf0 hf1 hf12 h_rec refuteZ0Fast_twelve_cert
}

/--
Earliest Return of a Pre-Zero Birth Value (`2`-Free Tail):
If `z_1` (`N_0 + 1 < z_1`, `a(z_1) = 0`) has `a(z_1 - 1)` reappearing after `z_1 - 1`, its earliest
return `r` satisfies `z_1 + 2 ≤ r` and `a(r + 1) = r - (z_1 - 1)` (allowing `4, 6, ...`).
-/
lemma no_twos_birth_earliest_return_spec (N_0 z_1 m : ℕ)
    (h_no_twos : ∀ k > N_0, vanEckNthTerm k ≠ 2)
    (hz1_gt : N_0 + 1 < z_1) (hz1 : vanEckNthTerm z_1 = 0)
    (hm_gt : z_1 - 1 < m) (hm_eq : vanEckNthTerm m = vanEckNthTerm (z_1 - 1)) :
    ∃ r, z_1 + 2 ≤ r ∧ r ≤ m ∧ vanEckNthTerm r = vanEckNthTerm (z_1 - 1) ∧
      (∀ i, z_1 - 1 < i → i < r → vanEckNthTerm i ≠ vanEckNthTerm (z_1 - 1)) ∧
      vanEckNthTerm (r + 1) = r - (z_1 - 1) := by {
  have h_ex : ∃ i, z_1 - 1 < i ∧ vanEckNthTerm i = vanEckNthTerm (z_1 - 1) := ⟨m, hm_gt, hm_eq⟩
  let r := Nat.find h_ex
  have hr_gt : z_1 - 1 < r := (Nat.find_spec h_ex).1
  have hr_eq : vanEckNthTerm r = vanEckNthTerm (z_1 - 1) := (Nat.find_spec h_ex).2
  have hr_le : r ≤ m := Nat.find_min' h_ex ⟨hm_gt, hm_eq⟩
  have hr_min : ∀ i, z_1 - 1 < i → i < r → vanEckNthTerm i ≠ vanEckNthTerm (z_1 - 1) :=
    fun i hi1 hi2 hc => Nat.find_min h_ex hi2 ⟨hi1, hc⟩
  have hz1_pos := (pre_zero_new_value_prior_occurrence_spec z_1 hz1 (by { omega })).1
  have hr_ne0 : r ≠ z_1 := by {
    intro heq
    have h0 := hr_eq
    rw [heq, hz1] at h0
    omega
  }
  have hr_ne1 : r ≠ z_1 + 1 := by {
    intro heq
    have h_eq2 : vanEckNthTerm (z_1 - 1) = vanEckNthTerm (z_1 - 1 + 2) := by {
      have hidx : z_1 - 1 + 2 = r := by { omega }
      rw [hidx, hr_eq]
    }
    have h_ne0 : vanEckNthTerm (z_1 - 1 + 1) ≠ vanEckNthTerm (z_1 - 1) := by {
      have hidx : z_1 - 1 + 1 = z_1 := by { omega }
      rw [hidx, hz1]
      omega
    }
    have h2 := vanEck_alt_pair_emits_two (z_1 - 1) h_eq2 h_ne0
    have hidx2 : z_1 - 1 + 3 = z_1 + 2 := by { omega }
    rw [hidx2] at h2
    exact h_no_twos (z_1 + 2) (by { omega }) h2
  }
  cases h_occ : lastOccBefore r (vanEckNthTerm r) with
  | none =>
    exact False.elim (((lastOccBefore_eq_none_iff _ _).mp h_occ) (z_1 - 1) hr_gt hr_eq.symm)
  | some q =>
    have hq_sp := lastOccBefore_eq_some_spec r (vanEckNthTerm r) q h_occ
    have h_next := vanEck_next_eq_of_lastOccBefore r
    rw [h_occ] at h_next
    change vanEckNthTerm (r + 1) = r - q at h_next
    have hq_ge : z_1 - 1 ≤ q := by {
      by_contra hlt
      exact hq_sp.2.2 (z_1 - 1) (by { omega }) hr_gt hr_eq.symm
    }
    have hq_le : q ≤ z_1 - 1 := by {
      by_contra hgt
      exact hr_min q (by { omega }) hq_sp.1 (hq_sp.2.1.trans hr_eq)
    }
    have hq_eq : q = z_1 - 1 := by { omega }
    rw [hq_eq] at h_next
    exact ⟨r, by { omega }, hr_le, hr_eq, hr_min, h_next⟩
}

/--
`2`-Free Birth-as-Generator Dichotomy (Allowing `4, 6, ...`):
When `a(z_1 - 1)` (`N_0 + 1 < z_1`, `a(z_1) = 0`) generates a later zero `z > z_1`, either `z` is
its first return (`p(z) = z_1 - 1`) or an earlier return `r ≥ z_1 + 2` precedes `p(z)`.
-/
lemma no_twos_birth_as_generator_cases (N_0 z_1 z : ℕ)
    (h_no_twos : ∀ k > N_0, vanEckNthTerm k ≠ 2)
    (hz1_gt : N_0 + 1 < z_1) (h_lt : z_1 < z)
    (hz1 : vanEckNthTerm z_1 = 0) (hz : vanEckNthTerm z = 0)
    (h_gen : vanEckNthTerm (z - 2) = vanEckNthTerm (z_1 - 1)) :
    z_1 + 3 ≤ z ∧
      ((z - 2 - vanEckNthTerm (z - 1) = z_1 - 1 ∧
          vanEckNthTerm (z - 1) = z - z_1 - 1 ∧
          ∀ i, z_1 - 1 < i → i < z - 2 → vanEckNthTerm i ≠ vanEckNthTerm (z_1 - 1)) ∨
        ∃ r, z_1 + 2 ≤ r ∧ r ≤ z - 2 - vanEckNthTerm (z - 1) ∧
          vanEckNthTerm r = vanEckNthTerm (z_1 - 1) ∧
          (∀ i, z_1 - 1 < i → i < r → vanEckNthTerm i ≠ vanEckNthTerm (z_1 - 1)) ∧
          vanEckNthTerm (r + 1) = r - (z_1 - 1) ∧
          vanEckNthTerm (z - 1) ≤ (z - 2) - r) := by {
  have h_dist := birth_as_later_generator_min_dist z_1 z (by { omega }) h_lt hz1 hz h_gen
  have h_sz := pre_zero_new_value_prior_occurrence_spec z hz (by { omega })
  rcases no_twos_birth_earliest_return_spec N_0 z_1 (z - 2) h_no_twos hz1_gt hz1
      (by { omega }) h_gen with ⟨r, hr_ge, hr_le, hr_eq, hr_min, hr_gap⟩
  refine ⟨h_dist.1, ?_⟩
  rcases eq_or_lt_of_le hr_le with hr_z2 | hr_lt_z2
  · left
    have hp_val : vanEckNthTerm (z - 2 - vanEckNthTerm (z - 1)) = vanEckNthTerm (z_1 - 1) :=
      h_sz.2.2.2.2.1.trans h_gen
    have hp_le : z - 2 - vanEckNthTerm (z - 1) ≤ z_1 - 1 := by {
      by_contra hp_gt
      have hp_lt_r : z - 2 - vanEckNthTerm (z - 1) < r := hr_z2.symm ▸ h_sz.2.2.1
      exact hr_min (z - 2 - vanEckNthTerm (z - 1)) (by { omega }) hp_lt_r hp_val
    }
    have hp_eq : z - 2 - vanEckNthTerm (z - 1) = z_1 - 1 := by { omega }
    have hz1_val := h_sz.2.2.2.1
    exact ⟨hp_eq, by { omega }, fun i hi1 hi2 => hr_min i hi1 (hr_z2.symm ▸ hi2)⟩
  · right
    have hp_ge_r : r ≤ z - 2 - vanEckNthTerm (z - 1) := by {
      by_contra hp_lt_r
      exact h_sz.2.2.2.2.2 r (by { omega }) hr_lt_z2 (hr_eq.trans h_gen.symm)
    }
    have hz1_val := h_sz.2.2.2.1
    exact ⟨r, hr_ge, hp_ge_r, hr_eq, hr_min, hr_gap, by { omega }⟩
}

/--
`2`-Free Jump Birth-Return Tripartition (Allowing `4, 6, ...`):
Every prefix-maximum jump `(z_prev, z)` past `N_0` (`∀ k > N_0, a(k) ≠ 2`) partitions into:
(1) pre-`N_0` bounded palette (`a(z - 2) ≤ vanEckPrefixMax N_0`),
(2) post-`N_0` first return (`p(z) = z_b - 1`), or
(3) post-`N_0` later return (`z_b + 2 ≤ r ≤ p(z)`).
-/
theorem no_twos_jump_birth_tripartition (N_0 z_prev z : ℕ)
    (h_no_twos : ∀ k > N_0, vanEckNthTerm k ≠ 2)
    (hN_lt : N_0 < z_prev) (h_prev_lt : z_prev < z)
    (hz_prev : vanEckNthTerm z_prev = 0) (hz : vanEckNthTerm z = 0)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0)
    (h_jump : vanEckPrefixMax z_prev < vanEckPrefixMax z) :
    ∃ z_b, 3 ≤ z_b ∧ z_b + 3 ≤ z ∧ vanEckNthTerm z_b = 0 ∧
      vanEckNthTerm (z_b - 1) = vanEckNthTerm (z - 2) ∧
      ((z_b ≤ N_0 + 1 ∧ 1 ≤ vanEckNthTerm (z - 2) ∧
          vanEckNthTerm (z - 2) ≤ vanEckPrefixMax N_0) ∨
        (N_0 + 1 < z_b ∧ z - 2 - vanEckNthTerm (z - 1) = z_b - 1 ∧
          vanEckPrefixMax z = z - z_b - 1 ∧
          ∀ i, z_b - 1 < i → i < z - 2 → vanEckNthTerm i ≠ vanEckNthTerm (z_b - 1)) ∨
        (N_0 + 1 < z_b ∧ ∃ r, z_b + 2 ≤ r ∧ r ≤ z - 2 - vanEckNthTerm (z - 1) ∧
          vanEckNthTerm r = vanEckNthTerm (z_b - 1) ∧
          vanEckNthTerm (r + 1) = r - (z_b - 1) ∧
          vanEckPrefixMax z_prev < vanEckNthTerm (z - 1) ∧
          vanEckNthTerm (z - 1) ≤ (z - 2) - r)) := by {
  have h_dorm := no_twos_prefixMax_jump_requires_dormant_generator N_0 z z_prev h_no_twos
    (by { omega }) hz (by { omega }) hz_prev h_prev_lt h_gap h_jump
  rcases pos_generator_has_unique_birth_zero z (by { omega }) hz h_dorm.2.1 with
    ⟨z_b, hzb_ge, hzb_dist, hzb_zero, hzb_eq, _, _⟩
  refine ⟨z_b, hzb_ge, hzb_dist, hzb_zero, hzb_eq, ?_⟩
  by_cases hzb_le : z_b ≤ N_0 + 1
  · left
    have h_le_max := vanEckNthTerm_le_prefixMax N_0 (z_b - 1) (by { omega })
    rw [hzb_eq] at h_le_max
    exact ⟨hzb_le, h_dorm.2.1, h_le_max⟩
  · have hzb_gt : N_0 + 1 < z_b := by { omega }
    have h_cases := no_twos_birth_as_generator_cases N_0 z_b z h_no_twos hzb_gt
      (by { omega }) hzb_zero hz hzb_eq.symm
    rcases h_cases.2 with h_first | ⟨r, hr_ge, hr_le_p, hr_eq, _, hr_gap, hr_ub⟩
    · right
      left
      exact ⟨hzb_gt, h_first.1, h_dorm.1.trans h_first.2.1, h_first.2.2⟩
    · right
      right
      exact ⟨hzb_gt, r, hr_ge, hr_le_p, hr_eq, hr_gap, h_jump.trans_eq h_dorm.1, hr_ub⟩
}

lemma no_twos_later_return_jump_spec (N_0 z_0 H B z : ℕ)
    (h_no_twos : ∀ k > N_0, vanEckNthTerm k ≠ 2) (hz0_gt : N_0 < z_0)
    (hz0 : vanEckNthTerm z_0 = 0) (hH : H ≤ vanEckPrefixMax z_0)
    (hz_gt : z_0 < z) (hz_le : z ≤ B) (hz : vanEckNthTerm z = 0)
    (h_jump : vanEckPrefixMax (lastZero (z - 1)) < vanEckPrefixMax z)
    (h_not_first : ¬ (N_0 < z - 2 - vanEckNthTerm (z - 1) ∧
      vanEckNthTerm (z - 2 - vanEckNthTerm (z - 1) + 1) = 0))
    (h_not_old : vanEckPrefixMax N_0 < vanEckNthTerm (z - 2)) :
    vanEckNthTerm (z - 2) ∈
        (((Finset.Icc (N_0 + 2) B).filter (fun z_b => vanEckNthTerm z_b = 0)).image
          (fun z_b => vanEckNthTerm (z_b - 1))) ∧
      N_0 + 4 ≤ z - 2 - vanEckNthTerm (z - 1) ∧
      H < vanEckNthTerm (z - 1) := by {
  let z_prev := lastZero (z - 1)
  have hzp_le : z_prev ≤ z - 1 := lastZero_le (z - 1)
  have hzp_zero : vanEckNthTerm z_prev = 0 := vanEck_lastZero_is_zero (z - 1)
  have hz0_le_zp : z_0 ≤ z_prev := by {
    by_contra hc
    exact no_zero_after_lastZero (z - 1) z_0 (by { omega }) (by { omega }) hz0
  }
  have h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0 :=
    fun k hk1 hk2 => no_zero_after_lastZero (z - 1) k hk1 (by { omega })
  rcases no_twos_jump_birth_tripartition N_0 z_prev z h_no_twos (by { omega }) (by { omega })
      hzp_zero hz h_gap h_jump with ⟨z_b, _, hzb_dist, hzb_zero, hzb_eq, h_tri⟩
  rcases h_tri with h_old | h_first | ⟨hzb_gt, r, hr_ge, hr_le_p, _, _, h_jlt, _⟩
  · omega
  · exfalso
    have hp_gt : N_0 < z - 2 - vanEckNthTerm (z - 1) := by { omega }
    have hp_z : z - 2 - vanEckNthTerm (z - 1) + 1 = z_b := by { omega }
    rw [← hp_z] at hzb_zero
    exact h_not_first ⟨hp_gt, hzb_zero⟩
  · have hzb_mem : z_b ∈ (Finset.Icc (N_0 + 2) B).filter (fun z_b => vanEckNthTerm z_b = 0) :=
      Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by { omega }, by { omega }⟩, hzb_zero⟩
    have h_img : vanEckNthTerm (z - 2) ∈
        ((Finset.Icc (N_0 + 2) B).filter (fun z_b => vanEckNthTerm z_b = 0)).image
          (fun z_b => vanEckNthTerm (z_b - 1)) :=
      Finset.mem_image.mpr ⟨z_b, hzb_mem, hzb_eq⟩
    have hH_lt := Nat.lt_of_le_of_lt (Nat.le_trans hH (vanEckPrefixMax_mono z_0 z_prev hz0_le_zp))
      h_jlt
    exact ⟨h_img, by { omega }, hH_lt⟩
}

/--
Unified `2`-Free Window Record-Jump Supply Theorem (Allowing `4, 6, ...`):
Under `∀ k > N_0, vanEckNthTerm k ≠ 2`, any finite set `J` of prefix-maximum jump zeros in
`[A, B]` (`N_0 < z_0 < z`, `2 ≤ H ≤ vanEckPrefixMax z_0`) splits into `J_old`, `J_first`, and
`J_later` with explicit cooldown/birth bounds AND obeys the sub-unit `H / (H + 1)` gate bound.
-/
theorem no_twos_window_jump_total_supply (N_0 z_0 H A B : ℕ) (J : Finset ℕ)
    (h_no_twos : ∀ k > N_0, vanEckNthTerm k ≠ 2) (hz0_gt : N_0 < z_0)
    (hz0 : vanEckNthTerm z_0 = 0) (hH2 : 2 ≤ H) (hH : H ≤ vanEckPrefixMax z_0)
    (hJ : ∀ z ∈ J, z_0 < z ∧ A ≤ z ∧ z ≤ B ∧ vanEckNthTerm z = 0 ∧
      vanEckPrefixMax (lastZero (z - 1)) < vanEckPrefixMax z) :
    let isFirst : ℕ → Prop := fun z => N_0 < z - 2 - vanEckNthTerm (z - 1) ∧
      vanEckNthTerm (z - 2 - vanEckNthTerm (z - 1) + 1) = 0
    let J_first := J.filter isFirst
    let J_old := J.filter (fun z => ¬ isFirst z ∧ vanEckNthTerm (z - 2) ≤ vanEckPrefixMax N_0)
    let J_later := J.filter (fun z => ¬ isFirst z ∧ vanEckPrefixMax N_0 < vanEckNthTerm (z - 2))
    let Z_births := (Finset.Icc (N_0 + 2) B).filter (fun z_b => vanEckNthTerm z_b = 0)
    J.card = J_old.card + J_first.card + J_later.card ∧
      J_old.card * (H + 1) ≤ vanEckPrefixMax N_0 * ((B - A) + (H + 1)) ∧
      J_first.card ≤ Z_births.card ∧
      J_later.card * (H + 1) ≤ Z_births.card * ((B - 2) - (N_0 + 4)) ∧
      J.card * (H + 1) ≤ H * ((B - (z_0 + 1)) + (H + 1)) := by {
  intro isFirst J_first J_old J_later Z_births
  have h_p1 := Finset.card_filter_add_card_filter_not (s := J) isFirst
  let Jn := J.filter (fun z => ¬ isFirst z)
  have h_p2 := Finset.card_filter_add_card_filter_not
    (s := Jn) (fun z => vanEckNthTerm (z - 2) ≤ vanEckPrefixMax N_0)
  have h_old_eq : Jn.filter (fun z => vanEckNthTerm (z - 2) ≤ vanEckPrefixMax N_0) = J_old := by {
    rw [Finset.filter_filter]
  }
  have h_lat_eq : Jn.filter (fun z => ¬ vanEckNthTerm (z - 2) ≤ vanEckPrefixMax N_0) =
      J_later := by {
    rw [Finset.filter_filter]
    exact Finset.filter_congr (fun _ _ => and_congr_right (fun _ => not_le))
  }
  rw [h_old_eq, h_lat_eq] at h_p2
  change J_first.card + Jn.card = J.card at h_p1
  have h_old_bnd := no_twos_finite_palette_jump_window_bound N_0 z_0 (vanEckPrefixMax N_0) H A B
    J_old h_no_twos hz0_gt hz0 hH (fun z hz => by {
      rcases Finset.mem_filter.mp hz with ⟨hzJ, _, hle⟩
      have hp := hJ z hzJ
      exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hle, hp.2.2.2.2⟩
    })
  have h_first_bnd := first_return_jumps_le_birth_zeros J_first (N_0 + 2) B (fun z hz => by {
    rcases Finset.mem_filter.mp hz with ⟨hzJ, hp_gt, hp_z⟩
    have hp := hJ z hzJ
    exact ⟨by { omega }, hp.2.2.2.1, by { omega }, by { omega }, hp_z⟩
  })
  let P_b := Z_births.image (fun z_b => vanEckNthTerm (z_b - 1))
  have h_lat_p := generator_set_anchor_cooldown_bound J_later P_b H (N_0 + 4) B (fun z hz => by {
    rcases Finset.mem_filter.mp hz with ⟨hzJ, hnf, hno⟩
    have hp := hJ z hzJ
    have hsp := no_twos_later_return_jump_spec N_0 z_0 H B z h_no_twos hz0_gt hz0 hH
      hp.1 hp.2.2.1 hp.2.2.2.1 hp.2.2.2.2 hnf hno
    exact ⟨by { omega }, hp.2.2.2.1, hsp.1, hsp.2.1, hp.2.2.1, hsp.2.2⟩
  })
  have h_lat_bnd : J_later.card * (H + 1) ≤ Z_births.card * ((B - 2) - (N_0 + 4)) :=
    le_trans h_lat_p (Nat.mul_le_mul_right _ Finset.card_image_le)
  have h_gate_bnd := no_twos_sub_unit_palette_gate_supply J N_0 z_0 H B h_no_twos hH2 hz0_gt hz0
    (fun z hz => by {
      have hp := hJ z hz
      have hzp_le : lastZero (z - 1) ≤ z - 1 := lastZero_le (z - 1)
      have hz0_le_zp : z_0 ≤ lastZero (z - 1) := by {
        by_contra hc
        exact no_zero_after_lastZero (z - 1) z_0 (by { omega }) (by { omega }) hz0
      }
      have h_dorm := no_twos_prefixMax_jump_requires_dormant_generator N_0 z (lastZero (z - 1))
        h_no_twos (by { omega }) hp.2.2.2.1 (by { omega }) (vanEck_lastZero_is_zero (z - 1))
        (by { omega }) (fun k hk1 hk2 => no_zero_after_lastZero (z - 1) k hk1 (by { omega }))
        hp.2.2.2.2
      have h_mono := vanEckPrefixMax_mono z_0 (lastZero (z - 1)) hz0_le_zp
      have hH_lt := Nat.lt_of_le_of_lt (Nat.le_trans hH h_mono) (hp.2.2.2.2.trans_eq h_dorm.1)
      exact ⟨hp.1, hp.2.2.1, hp.2.2.2.1, hH_lt⟩
    })
  exact ⟨by { omega }, h_old_bnd, h_first_bnd, h_lat_bnd, h_gate_bnd⟩
}

/--
Checks predicate `g` on all candidate prefix anchors `p ∈ free` with `m - p ≠ 2`.
-/
def allFreeNeTwo : (ℕ → Bool) → ℕ → List ℕ → Bool
  | _, _, [] => true
  | g, m, p :: ps =>
    (if Nat.beq (m - p) 2 then true else g p) && allFreeNeTwo g m ps

/--
Computable `2`-free lazy-prefix DFS refutation checker (allowing `4, 6, 8, ...`): verifies that
from `(m, cur, tailMap, free)`, every branch obeying `IsVanEckFrom` must emit `2` within `fuel`
steps.
-/
def refuteNoTwosFast : ℕ → ℕ → ℕ → List (ℕ × ℕ) → List ℕ → Bool
  | 0, _, _, _, _ => false
  | fuel + 1, m, cur, tailMap, free =>
    match lookupHead cur tailMap with
    | some q =>
      let nxt := m - q
      if Nat.beq nxt 2 then true
      else refuteNoTwosFast fuel (m + 1) nxt ((cur, m) :: tailMap) free
    | none =>
      let tailMap' := (cur, m) :: tailMap
      refuteNoTwosFast fuel (m + 1) 0 tailMap' free &&
        allFreeNeTwo (fun p =>
          refuteNoTwosFast fuel (m + 1) (m - p) tailMap' (removeFirst p free)) m free

/--
Universal `2`-free prefix certificate checker at zero `z0`: verifies `refuteNoTwosFast` across all
initial zero-gaps `z0 - zPrev ≠ 2` (`1 ≤ zPrev < z0`).
-/
def refuteNoTwosZ0Fast (z0 fuel : ℕ) : Bool :=
  (List.range z0).all (fun zPrev =>
    if Nat.ble 1 zPrev && !Nat.beq (z0 - zPrev) 2 then
      let free := (List.range z0).filter (fun p => Nat.ble 2 p && !Nat.beq p zPrev)
      refuteNoTwosFast fuel (z0 + 1) (z0 - zPrev) [(0, z0)] free
    else true)

lemma allFreeNeTwo_spec (g : ℕ → Bool) (m : ℕ) (free : List ℕ)
    (h : allFreeNeTwo g m free = true) (p : ℕ) (hp : p ∈ free) (hne2 : m - p ≠ 2) :
    g p = true := by {
  induction free with
  | nil => simp at hp
  | cons q qs ih =>
    simp only [allFreeNeTwo, Bool.and_eq_true] at h
    rcases List.mem_cons.mp hp with rfl | h_tail
    · cases hbeq : Nat.beq (m - p) 2 with
      | true => exact False.elim (hne2 (Nat.beq_eq.mp hbeq))
      | false =>
        rw [hbeq, if_neg (by { decide })] at h
        exact h.1
    · exact ih h.2 h_tail
}

lemma refuteNoTwosFast_none_branch (f : ℕ → ℕ) (z_0 fuel m cur : ℕ)
    (tailMap : List (ℕ × ℕ)) (free : List ℕ) (h_rec : IsVanEckFrom f z_0)
    (ih : ∀ m' cur' tailMap' free', refuteNoTwosFast fuel m' cur' tailMap' free' = true →
      ValidDFSState f z_0 m' cur' tailMap' free' → ∃ k, m' < k ∧ k ≤ m' + fuel ∧ f k = 2)
    (hs : ValidDFSState f z_0 m cur tailMap free) (hlk : lookupHead cur tailMap = none)
    (h_zero_br : refuteNoTwosFast fuel (m + 1) 0 ((cur, m) :: tailMap) free = true)
    (h_free_br : allFreeNeTwo
      (fun p => refuteNoTwosFast fuel (m + 1) (m - p) ((cur, m) :: tailMap) (removeFirst p free))
      m free = true) :
    ∃ k, m < k ∧ k ≤ m + (fuel + 1) ∧ f k = 2 := by {
  have hcur_nz : cur ≠ 0 := by {
    intro hc0
    rcases hs.hzero with ⟨qz, hqz⟩
    rw [← hc0, hlk] at hqz
    nomatch hqz
  }
  have h_occ_eq := lastOccBeforeFn_no_hit_tail f z_0 m cur (Nat.le_of_lt hs.hm)
    (hs.htail_none cur hlk)
  have h_step_rec := h_rec m (Nat.le_of_lt hs.hm)
  rw [hs.hcur, h_occ_eq] at h_step_rec
  cases h_z0_occ : lastOccBeforeFn f z_0 cur with
  | none =>
    rw [h_z0_occ] at h_step_rec
    have hs' := validDFSState_step_tail f z_0 m cur 0 tailMap free free hs h_step_rec
      (fun v p hv hlk' hp => by {
        rw [lookupHead_cons] at hlk'
        split_ifs at hlk'
        exact hs.hfree v p hv hlk' hp
      })
    rcases ih (m + 1) 0 ((cur, m) :: tailMap) free h_zero_br hs' with ⟨k, hk1, hk2, hk2_eq⟩
    exact ⟨k, by { omega }, by { omega }, hk2_eq⟩
  | some p =>
    rw [h_z0_occ] at h_step_rec
    change f (m + 1) = m - p at h_step_rec
    have hp_sp := lastOccBeforeFn_eq_some_spec f z_0 cur p h_z0_occ
    by_cases heq2 : m - p = 2
    · exact ⟨m + 1, Nat.lt_succ_self m, by { omega }, h_step_rec.trans heq2⟩
    · have href' := allFreeNeTwo_spec _ m free h_free_br p
        (hs.hfree cur p hcur_nz hlk h_z0_occ) heq2
      have hs' := validDFSState_step_tail f z_0 m cur (m - p) tailMap free (removeFirst p free)
        hs h_step_rec (fun v p' hv hlk' hp' => by {
          rw [lookupHead_cons] at hlk'
          split_ifs at hlk' with hvc
          have hp'_sp := lastOccBeforeFn_eq_some_spec f z_0 v p' hp'
          have hne_p : p' ≠ p := fun heq => hvc (hp'_sp.2.1.symm.trans (heq ▸ hp_sp.2.1))
          exact mem_removeFirst_of_ne p p' free (hs.hfree v p' hv hlk' hp') hne_p
        })
      rcases ih (m + 1) (m - p) ((cur, m) :: tailMap) (removeFirst p free) href' hs' with
        ⟨k, hk1, hk2, hk2_eq⟩
      exact ⟨k, by { omega }, by { omega }, hk2_eq⟩
}

/--
Soundness of `refuteNoTwosFast`: whenever `refuteNoTwosFast fuel m cur tailMap free = true` on a
valid DFS state of `f`, `f` must emit `2` at some `m < k ≤ m + fuel`.
-/
lemma refuteNoTwosFast_sound (f : ℕ → ℕ) (z_0 : ℕ) (h_rec : IsVanEckFrom f z_0) :
    ∀ (fuel m cur : ℕ) (tailMap : List (ℕ × ℕ)) (free : List ℕ),
      refuteNoTwosFast fuel m cur tailMap free = true →
      ValidDFSState f z_0 m cur tailMap free →
      ∃ k, m < k ∧ k ≤ m + fuel ∧ f k = 2 := by {
  intro fuel
  induction fuel with
  | zero =>
    intro m cur tailMap free h_ref
    simp [refuteNoTwosFast] at h_ref
  | succ fuel ih =>
    intro m cur tailMap free h_ref hs
    simp only [refuteNoTwosFast] at h_ref
    cases hlk : lookupHead cur tailMap with
    | some q =>
      rw [hlk] at h_ref
      dsimp only at h_ref
      have hq := hs.htail_some cur q hlk
      have h_step_rec := h_rec m (Nat.le_of_lt hs.hm)
      rw [hs.hcur, hq.2.2] at h_step_rec
      change f (m + 1) = m - q at h_step_rec
      cases hbeq : Nat.beq (m - q) 2 with
      | true =>
        exact ⟨m + 1, Nat.lt_succ_self m, by { omega }, h_step_rec.trans (Nat.beq_eq.mp hbeq)⟩
      | false =>
        rw [hbeq, if_neg (by { decide })] at h_ref
        have hs' := validDFSState_step_tail f z_0 m cur (m - q) tailMap free free hs h_step_rec
          (fun v p hv hlk' hp => by {
            rw [lookupHead_cons] at hlk'
            split_ifs at hlk'
            exact hs.hfree v p hv hlk' hp
          })
        rcases ih (m + 1) (m - q) ((cur, m) :: tailMap) free h_ref hs' with
          ⟨k, hk1, hk2, hk2_eq⟩
        exact ⟨k, by { omega }, by { omega }, hk2_eq⟩
    | none =>
      rw [hlk] at h_ref
      simp only [Bool.and_eq_true] at h_ref
      exact refuteNoTwosFast_none_branch f z_0 fuel m cur tailMap free h_rec ih hs hlk
        h_ref.1 h_ref.2
}

/--
Soundness of `refuteNoTwosZ0Fast`: if `refuteNoTwosZ0Fast z_0 fuel = true`, then EVERY sequence
`f : ℕ → ℕ` with `f 0 = 0`, `f 1 = 0`, `f z_0 = 0` obeying `IsVanEckFrom f z_0` — even allowing
`4, 6, 8, ...` and arbitrary unbounded values on `[2, z_0 - 1]` — emits `f k = 2` at some
`z_0 < k ≤ z_0 + 1 + fuel`.
-/
theorem refuteNoTwosZ0Fast_sound (f : ℕ → ℕ) (z_0 fuel : ℕ)
    (hz0_ge : 2 ≤ z_0) (hf0 : f 0 = 0) (hf1 : f 1 = 0) (hfz0 : f z_0 = 0)
    (h_rec : IsVanEckFrom f z_0) (h_cert : refuteNoTwosZ0Fast z_0 fuel = true) :
    ∃ k, z_0 < k ∧ k ≤ z_0 + 1 + fuel ∧ f k = 2 := by {
  cases h_occ0 : lastOccBeforeFn f z_0 0 with
  | none =>
    exact False.elim (((lastOccBeforeFn_eq_none_iff f z_0 0).mp h_occ0) 1 (by { omega }) hf1)
  | some z_prev =>
    have hzp := lastOccBeforeFn_eq_some_spec f z_0 0 z_prev h_occ0
    have hzp_ge1 : 1 ≤ z_prev := by {
      by_contra hc
      exact hzp.2.2 1 (by { omega }) (by { omega }) hf1
    }
    have h_f1 := h_rec z_0 le_rfl
    rw [hfz0, h_occ0] at h_f1
    change f (z_0 + 1) = z_0 - z_prev at h_f1
    by_cases heq2 : z_0 - z_prev = 2
    · exact ⟨z_0 + 1, Nat.lt_succ_self z_0, by { omega }, h_f1.trans heq2⟩
    · have hall := (List.all_eq_true.mp h_cert) z_prev (List.mem_range.mpr hzp.1)
      have hb2 : Nat.beq (z_0 - z_prev) 2 = false := by {
        cases hb : Nat.beq (z_0 - z_prev) 2 with
        | false => rfl
        | true => exact False.elim (heq2 (Nat.beq_eq.mp hb))
      }
      have hcond : (Nat.ble 1 z_prev && !Nat.beq (z_0 - z_prev) 2) = true := by {
        rw [Bool.and_eq_true, Nat.ble_eq, hb2]
        exact ⟨hzp_ge1, rfl⟩
      }
      rw [hcond, if_pos rfl] at hall
      have hs0 := validDFSState_init_z0 f z_0 z_prev hf0 hf1 hfz0 h_f1 hzp.2.1
      rcases refuteNoTwosFast_sound f z_0 h_rec fuel (z_0 + 1) (z_0 - z_prev) [(0, z_0)] _
        hall hs0 with ⟨k, hk1, hk2, hk2_eq⟩
      exact ⟨k, by { omega }, by { omega }, hk2_eq⟩
}

/--
Kernel-Checked `2`-Free Boolean Certificate at `z_0 = 5` (`431` DFS states, sharp depth `148`).
-/
lemma refuteNoTwosZ0Fast_five_cert : refuteNoTwosZ0Fast 5 148 = true := by {
  decide +kernel
}

/--
Sharp Kernel-Checked `z_0 = 5` Universal `2`-Free Obstruction (Allowing `4, 6, 8, ...`):
Every sequence `f : ℕ → ℕ` with `f 0 = 0`, `f 1 = 0`, `f 5 = 0` obeying `IsVanEckFrom f 5` —
regardless of what arbitrary unbounded values occupy `[2, 4]` — must emit `f k = 2` at some
`5 < k ≤ 154` (attained sharply at `k = 154` by `[0, 0, 5, 4, 3, 0, ...]`).
-/
theorem z0_five_universal_no_twos_obstruction (f : ℕ → ℕ)
    (hf0 : f 0 = 0) (hf1 : f 1 = 0) (hf5 : f 5 = 0)
    (h_rec : IsVanEckFrom f 5) :
    ∃ k, 5 < k ∧ k ≤ 154 ∧ f k = 2 := by {
  exact refuteNoTwosZ0Fast_sound f 5 148 (by { omega }) hf0 hf1 hf5 h_rec
    refuteNoTwosZ0Fast_five_cert
}

/--
Kernel-Checked `2`-Free Boolean Certificates at `z_0 = 3` (`2` states) and `z_0 = 4` (`21` states).
-/
lemma refuteNoTwosZ0Fast_three_cert : refuteNoTwosZ0Fast 3 2 = true := by {
  decide +kernel
}

lemma refuteNoTwosZ0Fast_four_cert : refuteNoTwosZ0Fast 4 10 = true := by {
  decide +kernel
}

/--
Uniform Kernel-Checked Base Cases (`3 ≤ z_0 ≤ 5`) for `no_twos_zero_cut_refuted`.
-/
theorem no_twos_zero_cut_refuted_le_five (z_0 : ℕ) (hge : 3 ≤ z_0) (hle : z_0 ≤ 5) :
    ∃ fuel, refuteNoTwosZ0Fast z_0 fuel = true := by {
  interval_cases z_0
  · exact ⟨2, refuteNoTwosZ0Fast_three_cert⟩
  · exact ⟨10, refuteNoTwosZ0Fast_four_cert⟩
  · exact ⟨148, refuteNoTwosZ0Fast_five_cert⟩
}

lemma allFreeNeTwo_mono (g1 g2 : ℕ → Bool) (m : ℕ) (free : List ℕ)
    (h_imp : ∀ p ∈ free, m - p ≠ 2 → g1 p = true → g2 p = true)
    (h1 : allFreeNeTwo g1 m free = true) :
    allFreeNeTwo g2 m free = true := by {
  induction free with
  | nil => rfl
  | cons q qs ih =>
    simp only [allFreeNeTwo, Bool.and_eq_true] at h1 ⊢
    refine ⟨?_, ih (fun p hp => h_imp p (List.mem_cons.mpr (Or.inr hp))) h1.2⟩
    cases hbeq : Nat.beq (m - q) 2 with
    | true => simp
    | false =>
      have h1_l := h1.1
      rw [hbeq] at h1_l
      simp only [Bool.false_eq_true, ↓reduceIte] at h1_l ⊢
      have hne2 : m - q ≠ 2 :=
        fun heq => Bool.noConfusion (hbeq.symm.trans (Nat.beq_eq.mpr heq))
      exact h_imp q (List.mem_cons.mpr (Or.inl rfl)) hne2 h1_l
}

/--
Monotonicity of `refuteNoTwosFast` with respect to search depth `fuel`.
-/
lemma refuteNoTwosFast_mono :
    ∀ (fuel1 fuel2 m cur : ℕ) (tailMap : List (ℕ × ℕ)) (free : List ℕ),
      fuel1 ≤ fuel2 →
      refuteNoTwosFast fuel1 m cur tailMap free = true →
      refuteNoTwosFast fuel2 m cur tailMap free = true := by {
  intro fuel1
  induction fuel1 with
  | zero =>
    intro fuel2 m cur tailMap free _hle h1
    simp [refuteNoTwosFast] at h1
  | succ f1 ih =>
    intro fuel2 m cur tailMap free hle h1
    cases fuel2 with
    | zero => omega
    | succ f2 =>
      have hf : f1 ≤ f2 := by { omega }
      simp only [refuteNoTwosFast] at h1 ⊢
      cases hlk : lookupHead cur tailMap with
      | some q =>
        rw [hlk] at h1
        dsimp only at h1 ⊢
        cases hbeq : Nat.beq (m - q) 2 with
        | true => simp
        | false =>
          rw [hbeq] at h1
          simp only [Bool.false_eq_true, ↓reduceIte] at h1 ⊢
          exact ih f2 (m + 1) (m - q) ((cur, m) :: tailMap) free hf h1
      | none =>
        rw [hlk] at h1
        simp only [Bool.and_eq_true] at h1 ⊢
        refine ⟨ih f2 (m + 1) 0 ((cur, m) :: tailMap) free hf h1.1, ?_⟩
        exact allFreeNeTwo_mono _ _ m free
          (fun p _hp _hne hr => ih f2 (m + 1) (m - p) ((cur, m) :: tailMap)
            (removeFirst p free) hf hr) h1.2
}

lemma exists_allFreeNeTwo_fuel (g : ℕ → ℕ → Bool) (m : ℕ) (ps : List ℕ)
    (h_mono : ∀ f1 f2 p, f1 ≤ f2 → g f1 p = true → g f2 p = true)
    (h_ex : ∀ p ∈ ps, m - p ≠ 2 → ∃ fuel, g fuel p = true) :
    ∃ fuel, allFreeNeTwo (g fuel) m ps = true := by {
  induction ps with
  | nil => exact ⟨0, rfl⟩
  | cons q qs ih =>
    rcases ih (fun p hp => h_ex p (List.mem_cons.mpr (Or.inr hp))) with ⟨f_tl, h_tl⟩
    by_cases heq2 : m - q = 2
    · refine ⟨f_tl, ?_⟩
      have hb2 : Nat.beq (m - q) 2 = true := Nat.beq_eq.mpr heq2
      simp only [allFreeNeTwo, hb2, ↓reduceIte, Bool.true_and]
      exact h_tl
    · rcases h_ex q (List.mem_cons.mpr (Or.inl rfl)) heq2 with ⟨f_hd, h_hd⟩
      refine ⟨max f_hd f_tl, ?_⟩
      have hb2 : Nat.beq (m - q) 2 = false := by {
        cases hb : Nat.beq (m - q) 2 with
        | false => rfl
        | true => exact False.elim (heq2 (Nat.beq_eq.mp hb))
      }
      simp only [allFreeNeTwo, hb2, Bool.false_eq_true, ↓reduceIte, Bool.and_eq_true]
      exact ⟨h_mono f_hd (max f_hd f_tl) q (Nat.le_max_left _ _) h_hd,
        allFreeNeTwo_mono _ _ m qs
          (fun p _ _ hr => h_mono f_tl (max f_hd f_tl) p (Nat.le_max_right _ _) hr) h_tl⟩
}

/--
One-step `2`-free DFS transition relation corresponding to surviving branches of `refuteNoTwosFast`.
-/
def StepNoTwosDFS (m cur : ℕ) (tm : List (ℕ × ℕ)) (free : List ℕ)
    (cur' : ℕ) (tm' : List (ℕ × ℕ)) (free' : List ℕ) : Prop :=
  (∃ q, lookupHead cur tm = some q ∧ m - q ≠ 2 ∧
      cur' = m - q ∧ tm' = (cur, m) :: tm ∧ free' = free) ∨
    (lookupHead cur tm = none ∧
      cur' = 0 ∧ tm' = (cur, m) :: tm ∧ free' = free) ∨
    (∃ p ∈ free, lookupHead cur tm = none ∧ m - p ≠ 2 ∧
      cur' = m - p ∧ tm' = (cur, m) :: tm ∧ free' = removeFirst p free)

/--
Finite-Branching Step Contrapositive: any unrefuted DFS state `(m, cur, tm, free)` admits at least
one surviving `2`-free child `(cur', tm', free')` that is also unrefuted for all `fuel`.
-/
lemma exists_unrefuted_child_of_not_refuted (m cur : ℕ) (tm : List (ℕ × ℕ)) (free : List ℕ)
    (h_not : ¬ ∃ fuel, refuteNoTwosFast fuel m cur tm free = true) :
    ∃ cur' tm' free', StepNoTwosDFS m cur tm free cur' tm' free' ∧
      ¬ ∃ fuel, refuteNoTwosFast fuel (m + 1) cur' tm' free' = true := by {
  by_contra h_all
  have h_child : ∀ cur' tm' free', StepNoTwosDFS m cur tm free cur' tm' free' →
      ∃ fuel, refuteNoTwosFast fuel (m + 1) cur' tm' free' = true := by {
    intro cur' tm' free' hst
    by_contra hnc
    exact h_all ⟨cur', tm', free', hst, hnc⟩
  }
  apply h_not
  cases hlk : lookupHead cur tm with
  | some q =>
    by_cases heq2 : m - q = 2
    · refine ⟨1, ?_⟩
      have hb2 : Nat.beq (m - q) 2 = true := Nat.beq_eq.mpr heq2
      simp only [refuteNoTwosFast, hlk, hb2, ↓reduceIte]
    · rcases h_child (m - q) ((cur, m) :: tm) free
          (Or.inl ⟨q, hlk, heq2, rfl, rfl, rfl⟩) with ⟨f1, hf1⟩
      refine ⟨f1 + 1, ?_⟩
      have hb2 : Nat.beq (m - q) 2 = false := by {
        cases hb : Nat.beq (m - q) 2 with
        | false => rfl
        | true => exact False.elim (heq2 (Nat.beq_eq.mp hb))
      }
      simp only [refuteNoTwosFast, hlk, hb2, Bool.false_eq_true, ↓reduceIte]
      exact hf1
  | none =>
    rcases h_child 0 ((cur, m) :: tm) free (Or.inr (Or.inl ⟨hlk, rfl, rfl, rfl⟩)) with ⟨f0, hf0⟩
    rcases exists_allFreeNeTwo_fuel
        (fun f p => refuteNoTwosFast f (m + 1) (m - p) ((cur, m) :: tm) (removeFirst p free))
        m free
        (fun f1 f2 p hle hr => refuteNoTwosFast_mono f1 f2 _ _ _ _ hle hr)
        (fun p hp hne2 => h_child _ _ _ (Or.inr (Or.inr ⟨p, hp, hlk, hne2, rfl, rfl, rfl⟩))) with
      ⟨ff, hff⟩
    refine ⟨max f0 ff + 1, ?_⟩
    simp only [refuteNoTwosFast, hlk, Bool.and_eq_true]
    exact ⟨refuteNoTwosFast_mono f0 (max f0 ff) _ _ _ _ (Nat.le_max_left _ _) hf0,
      allFreeNeTwo_mono _ _ m free
        (fun p _ _ hr => refuteNoTwosFast_mono ff (max f0 ff) _ _ _ _ (Nat.le_max_right _ _) hr)
        hff⟩
}

lemma exists_all_zprev_fuel (z_0 : ℕ) (xs : List ℕ)
    (h_each : ∀ x ∈ xs, ∃ fuel,
      (if Nat.ble 1 x && !Nat.beq (z_0 - x) 2 then
        refuteNoTwosFast fuel (z_0 + 1) (z_0 - x) [(0, z_0)]
          ((List.range z_0).filter (fun p => Nat.ble 2 p && !Nat.beq p x))
      else true) = true) :
    ∃ fuel, xs.all (fun x =>
      if Nat.ble 1 x && !Nat.beq (z_0 - x) 2 then
        refuteNoTwosFast fuel (z_0 + 1) (z_0 - x) [(0, z_0)]
          ((List.range z_0).filter (fun p => Nat.ble 2 p && !Nat.beq p x))
      else true) = true := by {
  induction xs with
  | nil => exact ⟨0, rfl⟩
  | cons x xs ih =>
    rcases h_each x (List.mem_cons.mpr (Or.inl rfl)) with ⟨fx, hfx⟩
    rcases ih (fun y hy => h_each y (List.mem_cons.mpr (Or.inr hy))) with ⟨fxs, hfxs⟩
    refine ⟨max fx fxs, ?_⟩
    rw [List.all_cons, Bool.and_eq_true]
    refine ⟨?_, ?_⟩
    · by_cases hcx : (Nat.ble 1 x && !Nat.beq (z_0 - x) 2) = true
      · rw [if_pos hcx] at hfx ⊢
        exact refuteNoTwosFast_mono fx (max fx fxs) _ _ _ _ (Nat.le_max_left _ _) hfx
      · exact if_neg hcx
    · rw [List.all_eq_true] at hfxs ⊢
      intro y hy
      have hy_ok := hfxs y hy
      by_cases hcy : (Nat.ble 1 y && !Nat.beq (z_0 - y) 2) = true
      · rw [if_pos hcy] at hy_ok ⊢
        exact refuteNoTwosFast_mono fxs (max fx fxs) _ _ _ _ (Nat.le_max_right _ _) hy_ok
      · exact if_neg hcy
}

lemma exists_unrefuted_zprev_of_not_refuted (z_0 : ℕ)
    (h_not : ¬ ∃ fuel, refuteNoTwosZ0Fast z_0 fuel = true) :
    ∃ z_prev, 1 ≤ z_prev ∧ z_prev < z_0 ∧ z_0 - z_prev ≠ 2 ∧
      ¬ ∃ fuel, refuteNoTwosFast fuel (z_0 + 1) (z_0 - z_prev) [(0, z_0)]
        ((List.range z_0).filter (fun p => Nat.ble 2 p && !Nat.beq p z_prev)) = true := by {
  by_contra h_all
  have h_each : ∀ z_prev ∈ List.range z_0,
      ∃ fuel, (if Nat.ble 1 z_prev && !Nat.beq (z_0 - z_prev) 2 then
        refuteNoTwosFast fuel (z_0 + 1) (z_0 - z_prev) [(0, z_0)]
          ((List.range z_0).filter (fun p => Nat.ble 2 p && !Nat.beq p z_prev))
      else true) = true := by {
    intro z_prev hmem
    by_cases hcond : (Nat.ble 1 z_prev && !Nat.beq (z_0 - z_prev) 2) = true
    · simp only [hcond, ↓reduceIte]
      have hc := Eq.mp (Bool.and_eq_true _ _) hcond
      have hge1 : 1 ≤ z_prev := Nat.ble_eq.mp hc.1
      have hne2 : z_0 - z_prev ≠ 2 := fun heq => by {
        have hb := Nat.beq_eq.mpr heq
        rw [hb] at hc
        nomatch hc.2
      }
      by_contra hnf
      exact h_all ⟨z_prev, hge1, List.mem_range.mp hmem, hne2, hnf⟩
    · exact ⟨0, if_neg hcond⟩
  }
  rcases exists_all_zprev_fuel z_0 (List.range z_0) h_each with ⟨fuel, hfuel⟩
  exact h_not ⟨fuel, hfuel⟩
}

/--
An infinite `2`-free DFS ray starting from a zero cut `z_0`.
-/
structure InfiniteNoTwosDFSRay (z_0 : ℕ) where
  z_prev : ℕ
  hzp_ge1 : 1 ≤ z_prev
  hzp_lt : z_prev < z_0
  hgap_ne2 : z_0 - z_prev ≠ 2
  curSeq : ℕ → ℕ
  tmSeq : ℕ → List (ℕ × ℕ)
  freeSeq : ℕ → List ℕ
  h_init_cur : curSeq 0 = z_0 - z_prev
  h_init_tm : tmSeq 0 = [(0, z_0)]
  h_init_free : freeSeq 0 =
    (List.range z_0).filter (fun p => Nat.ble 2 p && !Nat.beq p z_prev)
  h_step : ∀ t, StepNoTwosDFS (z_0 + 1 + t) (curSeq t) (tmSeq t) (freeSeq t)
    (curSeq (t + 1)) (tmSeq (t + 1)) (freeSeq (t + 1))
  h_unrefuted : ∀ t fuel,
    refuteNoTwosFast fuel (z_0 + 1 + t) (curSeq t) (tmSeq t) (freeSeq t) = false

/--
Kőnig's Lemma for `refuteNoTwosZ0Fast`: if no finite `fuel` refutes the `z_0` cut, there exists an
infinite `2`-free DFS ray `InfiniteNoTwosDFSRay z_0`.
-/
theorem nonempty_infinite_dfs_ray_of_not_refuted (z_0 : ℕ)
    (h_not : ¬ ∃ fuel, refuteNoTwosZ0Fast z_0 fuel = true) :
    Nonempty (InfiniteNoTwosDFSRay z_0) := by {
  rcases exists_unrefuted_zprev_of_not_refuted z_0 h_not with
    ⟨z_prev, hge1, hlt, hne2, h_not0⟩
  let Node (t : ℕ) := { s : ℕ × List (ℕ × ℕ) × List ℕ //
    ¬ ∃ fuel, refuteNoTwosFast fuel (z_0 + 1 + t) s.1 s.2.1 s.2.2 = true }
  let stepNode : ∀ t, Node t → Node (t + 1) := fun t ⟨⟨c, tm, fr⟩, hn⟩ =>
    let hex := exists_unrefuted_child_of_not_refuted (z_0 + 1 + t) c tm fr hn
    let c' := Classical.choose hex
    let hex2 := Classical.choose_spec hex
    let tm' := Classical.choose hex2
    let hex3 := Classical.choose_spec hex2
    let fr' := Classical.choose hex3
    have hspec := Classical.choose_spec hex3
    have hidx : z_0 + 1 + t + 1 = z_0 + 1 + (t + 1) := by { omega }
    ⟨(c', tm', fr'), hidx ▸ hspec.2⟩
  let seq : ∀ t, Node t := Nat.rec
    ⟨(z_0 - z_prev, [(0, z_0)],
      (List.range z_0).filter (fun p => Nat.ble 2 p && !Nat.beq p z_prev)), h_not0⟩
    stepNode
  refine ⟨⟨z_prev, hge1, hlt, hne2,
    fun t => (seq t).1.1, fun t => (seq t).1.2.1, fun t => (seq t).1.2.2,
    rfl, rfl, rfl, ?_, ?_⟩⟩
  · intro t
    have hspec := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec
      (exists_unrefuted_child_of_not_refuted (z_0 + 1 + t)
        (seq t).1.1 (seq t).1.2.1 (seq t).1.2.2 (seq t).2)))
    exact hspec.1
  · intro t fuel
    cases hb : refuteNoTwosFast fuel (z_0 + 1 + t) (seq t).1.1 (seq t).1.2.1 (seq t).1.2.2 with
    | false => rfl
    | true => exact False.elim ((seq t).2 ⟨fuel, hb⟩)
}

lemma removeFirst_length_lt_of_mem (p : ℕ) (xs : List ℕ) (hp : p ∈ xs) :
    (removeFirst p xs).length < xs.length := by {
  induction xs with
  | nil => simp at hp
  | cons y ys ih =>
    simp only [removeFirst]
    cases hbeq : Nat.beq p y with
    | true => simp
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.length_cons]
      rcases List.mem_cons.mp hp with rfl | h_tl
      · have hb : Nat.beq p p = true := Nat.beq_eq.mpr rfl
        exact Bool.noConfusion (hbeq.symm.trans hb)
      · have hlt := ih h_tl
        omega
}

/--
Prefix-Slot Exhaustion along an Infinite DFS Ray: `freeSeq` has non-increasing length and
stabilizes permanently after a finite horizon `T_stab`.
-/
lemma dfs_ray_free_stabilizes {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) :
    (∀ t, (R.freeSeq (t + 1)).length ≤ (R.freeSeq t).length) ∧
      ∃ T_stab, ∀ t ≥ T_stab, R.freeSeq (t + 1) = R.freeSeq t := by {
  classical
  have h_mono : ∀ t, (R.freeSeq (t + 1)).length ≤ (R.freeSeq t).length := by {
    intro t
    rcases R.h_step t with ⟨_, _, _, _, _, hfr⟩ | ⟨_, _, _, hfr⟩ | ⟨p, hp, _, _, _, _, hfr⟩
    · rw [hfr]
    · rw [hfr]
    · rw [hfr]
      exact Nat.le_of_lt (removeFirst_length_lt_of_mem p (R.freeSeq t) hp)
  }
  refine ⟨h_mono, ?_⟩
  have h_ex_min : ∃ k, ∃ t, (R.freeSeq t).length = k := ⟨(R.freeSeq 0).length, 0, rfl⟩
  rcases Nat.find_spec h_ex_min with ⟨T_stab, _hT_eq⟩
  refine ⟨T_stab, ?_⟩
  have h_le_T : ∀ t ≥ T_stab, (R.freeSeq t).length ≤ (R.freeSeq T_stab).length := by {
    intro t ht
    induction t with
    | zero =>
      have hT0 : T_stab = 0 := by { omega }
      rw [hT0]
    | succ s ih =>
      rcases eq_or_lt_of_le ht with h_eq | hlt
      · rw [← h_eq]
      · exact le_trans (h_mono s) (ih (by { omega }))
  }
  intro t ht
  rcases R.h_step t with ⟨_, _, _, _, _, hfr⟩ | ⟨_, _, _, hfr⟩ | ⟨p, hp, _, _, _, _, hfr⟩
  · exact hfr
  · exact hfr
  · exfalso
    have hlt := removeFirst_length_lt_of_mem p (R.freeSeq t) hp
    have hle := h_le_T t ht
    have hmin := Nat.find_min' h_ex_min ⟨t + 1, rfl⟩
    rw [hfr] at hmin
    omega
}

/--
Shifted realization of an `InfiniteNoTwosDFSRay` (`raySeq R 0 = 0`, `raySeq R (t + 1) = curSeq t`).
-/
def raySeq {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) : ℕ → ℕ
  | 0 => 0
  | t + 1 => R.curSeq t

lemma dfs_ray_lookup_eq_lastOcc {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) (t v : ℕ) :
    lookupHead v (R.tmSeq t) = (lastOccBeforeFn (raySeq R) (t + 1) v).map (· + z_0) := by {
  induction t with
  | zero =>
    rw [R.h_init_tm, lookupHead_cons]
    simp only [lastOccBeforeFn, raySeq]
    by_cases hv0 : v = 0
    · subst hv0
      simp
    · have h0v : ¬ (0 = v) := Ne.symm hv0
      simp [hv0, h0v, lookupHead]
  | succ s ih =>
    have htm : R.tmSeq (s + 1) = (R.curSeq s, z_0 + 1 + s) :: R.tmSeq s := by {
      rcases R.h_step s with ⟨_, _, _, _, htm, _⟩ | ⟨_, _, htm, _⟩ | ⟨_, _, _, _, _, htm, _⟩
      · exact htm
      · exact htm
      · exact htm
    }
    have hstep_occ : lastOccBeforeFn (raySeq R) (s + 2) v =
        if R.curSeq s = v then some (s + 1) else lastOccBeforeFn (raySeq R) (s + 1) v := rfl
    rw [htm, lookupHead_cons, hstep_occ]
    by_cases hvc : v = R.curSeq s
    · subst hvc
      simp only [↓reduceIte, Option.map]
      congr 1
      omega
    · have hcv : ¬ (R.curSeq s = v) := Ne.symm hvc
      rw [if_neg hvc, if_neg hcv, ih]
}

lemma dfs_ray_shifted_ne_two {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) :
    ∀ j ≥ 1, raySeq R j ≠ 2 := by {
  intro j hj
  cases j with
  | zero => omega
  | succ t =>
    cases t with
    | zero => exact R.hgap_ne2 ∘ R.h_init_cur.symm.trans
    | succ s =>
      change R.curSeq (s + 1) ≠ 2
      rcases R.h_step s with ⟨_, _, hne2, hc, _, _⟩ | ⟨_, hc, _, _⟩ | ⟨_, _, _, hne2, hc, _, _⟩
      · rw [hc]
        exact hne2
      · rw [hc]
        decide
      · rw [hc]
        exact hne2
}

/--
Exact `IsVanEckFrom` Realization of an Infinite DFS Ray:
Once `freeSeq` stabilizes at `T_stab`, `raySeq R` obeys the exact Van Eck recurrence
`IsVanEckFrom (raySeq R) (T_stab + 1)` with `raySeq R 0 = 0` and `∀ j ≥ 1, raySeq R j ≠ 2`.
-/
theorem dfs_ray_shifted_seq_spec {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) :
    raySeq R 0 = 0 ∧
      raySeq R 1 = z_0 - R.z_prev ∧
      (∀ j ≥ 1, raySeq R j ≠ 2) ∧
      ∃ T_stab, IsVanEckFrom (raySeq R) (T_stab + 1) := by {
  refine ⟨rfl, R.h_init_cur, dfs_ray_shifted_ne_two R, ?_⟩
  rcases (dfs_ray_free_stabilizes R).2 with ⟨T_stab, hT⟩
  refine ⟨T_stab, ?_⟩
  intro m hm
  cases m with
  | zero => omega
  | succ t =>
    have ht : T_stab ≤ t := by { omega }
    have hfr_eq := hT t ht
    have hlk_eq := dfs_ray_lookup_eq_lastOcc R t (R.curSeq t)
    change R.curSeq (t + 1) =
      match lastOccBeforeFn (raySeq R) (t + 1) (R.curSeq t) with
      | none => 0
      | some p => t + 1 - p
    rcases R.h_step t with ⟨q, hlk, _, hc, _, _⟩ | ⟨hlk, hc, _, _⟩ | ⟨p, hp, _, _, _, _, hfr⟩
    · rw [hlk] at hlk_eq
      cases h_occ : lastOccBeforeFn (raySeq R) (t + 1) (R.curSeq t) with
      | none =>
        rw [h_occ] at hlk_eq
        nomatch hlk_eq
      | some r =>
        rw [h_occ] at hlk_eq
        simp only [Option.map, Option.some.injEq] at hlk_eq
        have hr_lt := (lastOccBeforeFn_eq_some_spec (raySeq R) (t + 1) _ r h_occ).1
        rw [hc]
        change z_0 + 1 + t - q = t + 1 - r
        omega
    · rw [hlk] at hlk_eq
      cases h_occ : lastOccBeforeFn (raySeq R) (t + 1) (R.curSeq t) with
      | none => exact hc
      | some r =>
        rw [h_occ] at hlk_eq
        nomatch hlk_eq
    · exfalso
      have hlt := removeFirst_length_lt_of_mem p (R.freeSeq t) hp
      rw [← hfr, hfr_eq] at hlt
      omega
}

/--
Universal Lookback-Anchor Injectivity for `IsVanEckFrom f M_0`:
Any two positive terms at `M_0 < i < j` have distinct anchors `i - 1 - f i ≠ j - 1 - f j`.
-/
lemma isVanEckFrom_lookback_anchor_unique (f : ℕ → ℕ) (M_0 i j : ℕ)
    (h_rec : IsVanEckFrom f M_0) (hi : M_0 < i) (hlt : i < j)
    (hi_pos : 0 < f i) (hj_pos : 0 < f j) :
    i - 1 - f i ≠ j - 1 - f j := by {
  intro heq
  have hri := h_rec (i - 1) (by { omega })
  have hrj := h_rec (j - 1) (by { omega })
  have hi_idx : i - 1 + 1 = i := by { omega }
  have hj_idx : j - 1 + 1 = j := by { omega }
  rw [hi_idx] at hri
  rw [hj_idx] at hrj
  cases h_occi : lastOccBeforeFn f (i - 1) (f (i - 1)) with
  | none =>
    rw [h_occi] at hri
    change f i = 0 at hri
    omega
  | some pi =>
    rw [h_occi] at hri
    change f i = i - 1 - pi at hri
    have hpi_sp := lastOccBeforeFn_eq_some_spec f (i - 1) (f (i - 1)) pi h_occi
    cases h_occj : lastOccBeforeFn f (j - 1) (f (j - 1)) with
    | none =>
      rw [h_occj] at hrj
      change f j = 0 at hrj
      omega
    | some pj =>
      rw [h_occj] at hrj
      change f j = j - 1 - pj at hrj
      have hpj_sp := lastOccBeforeFn_eq_some_spec f (j - 1) (f (j - 1)) pj h_occj
      have hpi_lt := hpi_sp.1
      have hpj_lt := hpj_sp.1
      have hp_eq : pi = pj := by { omega }
      have hval_eq : f (i - 1) = f (j - 1) :=
        hpi_sp.2.1.symm.trans (hp_eq ▸ hpj_sp.2.1)
      exact hpj_sp.2.2 (i - 1) (by { omega }) (by { omega }) hval_eq
}


lemma odds_and_zeros_chain_contradiction (N : ℕ) (h_odds : OnlyOddsAndZerosAfter N) : False := by {
  sorry
}

/--
`vanEck_unbounded` makes every global boundedness conclusion false.
-/
theorem not_eventually_bounded : ¬ ∃ M, ∀ m, vanEckNthTerm m ≤ M := by {
  rintro ⟨M, hM⟩
  rcases vanEck_unbounded M with ⟨m, hm⟩
  have h_le := hM m
  omega
}

/--
Honest status of the retired `no_twos_implies_bounded` route. Because the sequence is unbounded,
"no `2` after `N_0` ⇒ bounded" is *equivalent* to `InfiniteTwos` itself, so its `k = z - 1`
branch could never be closed by a local bound (cf. `prefixMax_jump_in_two_free_window`).
-/
theorem no_twos_implies_bounded_iff_infinite_twos :
    (∀ N_0, (∀ m > N_0, vanEckNthTerm m ≠ 2) → ∃ M > 0, ∀ m, vanEckNthTerm m ≤ M) ↔
      ∀ N, ∃ m > N, vanEckNthTerm m = 2 := by {
  constructor
  · intro h N
    by_contra h_none
    push Not at h_none
    rcases h N h_none with ⟨M, _, hM⟩
    exact not_eventually_bounded ⟨M, hM⟩
  · intro h N_0 h_no
    rcases h N_0 with ⟨m, hm, h2⟩
    exact absurd h2 (h_no m hm)
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
  exact odds_and_zeros_chain_contradiction N_0 h_no_evens
}
