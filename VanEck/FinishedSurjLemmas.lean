import VanEck
import ImpossiblePatterns
import LimSup
import Mathlib

lemma vanEck_surjective_zero : ∃ m, vanEckNthTerm m = 0 := by {
  use 0
  exact vanEck_head_eq_zero 0
}

lemma vanEck_surjective_one : ∃ m, vanEckNthTerm m = 1 := by {
  use 2
  rfl
}

lemma vanEck_surjective_two : ∃ m, vanEckNthTerm m = 2 := by {
  use 4
  rfl
}

/--
Level 1 Conjecture (Easy): The Van Eck sequence is unbounded.
Since we previously proved that the limsup of a(n)/sqrt(n) >= 1, we know the sequence
must take arbitrarily large values.
-/
theorem vanEck_unbounded (N : ℕ) : ∃ m : ℕ, vanEckNthTerm m > N := by {
  let N_sq := N * N + 2 * N + 2
  have h_bound := vanEck_limsup_ge_sqrt N_sq
  rcases h_bound with ⟨m, hm_le, hm_ineq⟩
  use m
  by_contra hc
  have h_le : vanEckNthTerm m ≤ N := Nat.le_of_not_lt hc
  have h_ineq_contra : vanEckNthTerm m * vanEckNthTerm m + 2 * vanEckNthTerm m + 1 ≤ N * N + 2 * N + 1 := by nlinarith
  have h_contra : m ≤ N * N + 2 * N + 1 := Nat.le_trans hm_ineq h_ineq_contra
  have h_m_gt : m ≥ N * N + 2 * N + 2 := hm_le
  nlinarith
}

/--
Level 2 Conjecture (Easy): The sequence is not eventually periodic.
Any periodic sequence is bounded. Since we know the sequence is unbounded,
it cannot be periodic.
-/
theorem vanEck_not_periodic (p : ℕ) (hp : p > 0) : ∀ N, ∃ m > N, vanEckNthTerm m ≠ vanEckNthTerm (m + p) := by {
  intro N
  by_contra hc
  have h_per : ∀ m > N, vanEckNthTerm m = vanEckNthTerm (m + p) := by
    intro m hm
    have h1 : ¬(vanEckNthTerm m ≠ vanEckNthTerm (m + p)) := by
      intro h_neq
      have h_ex : ∃ m > N, vanEckNthTerm m ≠ vanEckNthTerm (m + p) := ⟨m, hm, h_neq⟩
      exact hc h_ex
    exact Classical.not_not.mp h1

  have h_per_k : ∀ k m, m > N → vanEckNthTerm m = vanEckNthTerm (m + k * p) := by
    intro k
    induction k with
    | zero =>
      intro m hm
      have hz : m + 0 * p = m := by rw [Nat.zero_mul, Nat.add_zero]
      rw [hz]
    | succ k ih =>
      intro m hm
      have hs : m + (k + 1) * p = m + k * p + p := by
        rw [Nat.add_mul, Nat.one_mul]
        exact (Nat.add_assoc m (k * p) p).symm
      rw [hs]
      have hm_gt : m + k * p > N := Nat.lt_of_lt_of_le hm (Nat.le_add_right m (k * p))
      have h_step := h_per (m + k * p) hm_gt
      have h_ih := ih m hm
      exact h_ih.trans h_step

  let B := vanEckPrefixMax (N + p)

  have h_bound : ∀ m > N, vanEckNthTerm m ≤ B := by
    intro m hm
    let d := m - (N + 1)
    let k := d / p
    let r := d % p
    have hd : m = N + 1 + d := (Nat.add_sub_cancel' hm).symm
    have hdr : d = k * p + r := by {
      dsimp [k, r]
      rw [Nat.mul_comm]
      exact (Nat.div_add_mod d p).symm
    }
    have hr_lt : r < p := Nat.mod_lt d hp

    have hm_eq : m = N + 1 + r + k * p := by omega

    have h_base_gt : N + 1 + r > N := by
      calc N + 1 + r ≥ N + 1 := Nat.le_add_right (N + 1) r
           _ > N := Nat.lt_succ_self N

    have h_eval : vanEckNthTerm (N + 1 + r) = vanEckNthTerm (N + 1 + r + k * p) := h_per_k k (N + 1 + r) h_base_gt

    have h_m_val : vanEckNthTerm m = vanEckNthTerm (N + 1 + r) := by
      rw [hm_eq]
      exact h_eval.symm

    have h_idx_le : N + 1 + r ≤ N + p := by
      have h1 : r + 1 ≤ p := hr_lt
      calc N + 1 + r = N + (r + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 r]
           _ ≤ N + p := Nat.add_le_add_left h1 N

    have h_B : vanEckNthTerm (N + 1 + r) ≤ B := vanEckNthTerm_le_prefixMax (N + p) (N + 1 + r) h_idx_le

    rw [h_m_val]
    exact h_B

  have h_unb := vanEck_unbounded (max B (vanEckPrefixMax N))
  rcases h_unb with ⟨m, hm_gt⟩

  have h_max_B : B ≤ max B (vanEckPrefixMax N) := Nat.le_max_left _ _
  have h_max_N : vanEckPrefixMax N ≤ max B (vanEckPrefixMax N) := Nat.le_max_right _ _

  by_cases hm_N : m > N
  · have h1 : vanEckNthTerm m ≤ B := h_bound m hm_N
    have h2 : B < vanEckNthTerm m := Nat.lt_of_le_of_lt h_max_B hm_gt
    have h3 := Nat.lt_of_le_of_lt h1 h2
    exact Nat.lt_irrefl _ h3
  · have hm_le : m ≤ N := Nat.le_of_not_lt hm_N
    have h1 : vanEckNthTerm m ≤ vanEckPrefixMax N := vanEckNthTerm_le_prefixMax N m hm_le
    have h2 : vanEckPrefixMax N < vanEckNthTerm m := Nat.lt_of_le_of_lt h_max_N hm_gt
    have h3 := Nat.lt_of_le_of_lt h1 h2
    exact Nat.lt_irrefl _ h3
}

/--
Intermediate Lemma 1 for `vanEck_not_periodic2`:
If the sequence is eventually periodic with period `p`, then its values in the periodic tail
are strictly bounded by `p`. This holds because any sequence value $a(m) = x > 0$ represents
the exact distance to the most recent previous occurrence. Since the sequence is periodic,
every element must re-appear within `p` steps, capping the maximum possible gap at `p`.
-/
lemma periodic_implies_bounded_by_period (p N : ℕ) (hp : p > 0)
    (h_per : ∀ m > N, vanEckNthTerm m = vanEckNthTerm (m + p)) :
    ∀ m > N + p + 1, vanEckNthTerm m ≤ p := by {
  intro m hm
  by_cases h0 : vanEckNthTerm m = 0
  · rw [h0]; exact Nat.zero_le p
  · have hm_pos : m ≥ 2 := by omega
    have h_a_def : vanEckNthTerm m = matchSearch (vanEck (m - 1)) (m - 1) := vanEck_term_is_matchSearch m (Nat.lt_of_succ_lt hm_pos)
    have h_ms_neq : matchSearch (vanEck (m - 1)) (m - 1) ≠ 0 := by
      rw [← h_a_def]
      exact h0

    have hm_sub_p_gt : m - 1 - p > N := by omega
    have h_per_val : vanEckNthTerm (m - 1 - p) = vanEckNthTerm (m - 1 - p + p) := h_per (m - 1 - p) hm_sub_p_gt
    have h_p_cancel : m - 1 - p + p = m - 1 := by omega
    rw [h_p_cancel] at h_per_val
    have h_match_val : vanEckNthTerm (m - 1) = vanEckNthTerm (m - 1 - p) := h_per_val.symm

    have h_L_len : (vanEck (m - 1)).length = m := by
      have h1 := vanEckLength (m - 1)
      have h2 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.le_trans (by decide) hm_pos)
      rw [h2] at h1
      exact h1
    have h_L_len1 : (vanEck (m - 1)).length - 1 = m - 1 := by rw [h_L_len]

    have hd_last : listNth (vanEck (m - 1)) (m - 1) = vanEckNthTerm (m - 1) := by
      exact VanEck_deterministic (m - 1) (m - 1) (Nat.le_refl _)
    have hd_prev : listNth (vanEck (m - 1)) (m - 1 - p) = vanEckNthTerm (m - 1 - p) := by
      have hle : m - 1 - p ≤ m - 1 := Nat.sub_le _ _
      exact VanEck_deterministic (m - 1) (m - 1 - p) hle

    have h_match : listNth (vanEck (m - 1)) ((vanEck (m - 1)).length - 1) = listNth (vanEck (m - 1)) (m - 1 - p) := by
      rw [h_L_len1, hd_last, hd_prev]
      exact h_match_val

    have hk_lt_n : m - 1 - p < m - 1 := by omega

    have h_bound := matchSearch_first (vanEck (m - 1)) (m - 1) (m - 1 - p) h_ms_neq hk_lt_n h_match
    rw [h_L_len1] at h_bound
    have h_sub_sub : m - 1 - (m - 1 - p) = p := by omega
    rw [h_sub_sub] at h_bound

    rw [h_a_def]
    exact h_bound
}

/--
Level 2 Alternative Conjecture: The sequence is not eventually periodic, proved directly via the
infinite zeroes property. If a sequence is periodic, its maximum gap is bounded.
By Pigeonholing the number of elements against this maximum gap, we can force a contradiction.
-/
theorem vanEck_not_periodic2 (p : ℕ) (hp : p > 0) : ∀ N, ∃ m > N, vanEckNthTerm m ≠ vanEckNthTerm (m + p) := by {
  intro N
  by_contra hc
  have h_per : ∀ m > N, vanEckNthTerm m = vanEckNthTerm (m + p) := by
    intro m hm
    exact Classical.not_not.mp (by intro hneq; exact hc ⟨m, hm, hneq⟩)

  have h_zeros := infinite_zeros_vanEck (N + p + 2)
  rcases h_zeros with ⟨Z, hZ_gt, hZ_zero⟩

  -- Z > N + p + 2.
  have hZ_p_gt : Z + p > N := by omega

  have h_Z_eq : vanEckNthTerm Z = vanEckNthTerm (Z + p) := h_per Z (by omega)

  have hZ_p_zero : vanEckNthTerm (Z + p) = 0 := by
    rw [← h_Z_eq]
    exact hZ_zero

  have hZ_prev_gt : Z - 1 > N := by omega

  have h_prev_eq : vanEckNthTerm (Z - 1) = vanEckNthTerm (Z - 1 + p) := h_per (Z - 1) hZ_prev_gt

  have h_add_comm : Z - 1 + p = Z + p - 1 := by omega
  rw [h_add_comm] at h_prev_eq

  -- Now we evaluate a(Z+p)
  have hZp_pos : Z + p ≥ 2 := by omega

  have haZp := vanEck_term_is_matchSearch (Z + p) (Nat.lt_of_succ_lt hZp_pos)
  rw [hZ_p_zero] at haZp
  have h_ms_zero : matchSearch (vanEck (Z + p - 1)) (Z + p - 1) = 0 := haZp.symm

  let L := vanEck (Z + p - 1)
  have h_len : L.length = Z + p := by {
    have hl1 := vanEckLength (Z + p - 1)
    have hl2 : Z + p - 1 + 1 = Z + p := by omega
    rw [hl2] at hl1
    exact hl1
  }

  have hlen2 : L.length ≥ 2 := by rw [h_len]; exact hZp_pos

  let n := p - 1
  have hn_lt : n < L.length - 1 := by omega

  have hd_last : listNth L (L.length - 1) = vanEckNthTerm (Z + p - 1) := by
    have hl1 : L.length - 1 = Z + p - 1 := by rw [h_len]
    rw [hl1]
    exact VanEck_deterministic (Z + p - 1) (Z + p - 1) (Nat.le_refl _)

  have h_idx : L.length - 2 - n = Z - 1 := by omega

  have hd_prev : listNth L (L.length - 2 - n) = vanEckNthTerm (Z - 1) := by
    rw [h_idx]
    exact VanEck_deterministic (Z + p - 1) (Z - 1) (by omega)

  have h_match : listNth L (L.length - 2 - n) = listNth L (L.length - 1) := by
    rw [hd_last, hd_prev]
    exact h_prev_eq

  have h_ge1 := if_match_then_match_search_at_end_ge_1 n L hlen2 hn_lt h_match

  have h_L_len1 : L.length - 1 = Z + p - 1 := by rw [h_len]
  rw [h_L_len1] at h_ge1

  rw [h_ms_zero] at h_ge1
  exact Nat.not_lt_zero 0 h_ge1
}

lemma listMax_le {L : List ℕ} {c : ℕ} (h : ∀ x ∈ L, x ≤ c) : listMax L ≤ c := by {
  induction L with
  | nil => exact Nat.zero_le c
  | cons x xs ih =>
    unfold listMax
    have h1 : x ∈ x :: xs := List.Mem.head _
    have hx_le : x ≤ c := h x h1
    have hxs_le : listMax xs ≤ c := by {
      apply ih
      intro y hy
      exact h y (List.Mem.tail _ hy)
    }
    exact Nat.max_le.mpr ⟨hx_le, hxs_le⟩
}

lemma vanEck_lastZero_is_zero (m : ℕ) : vanEckNthTerm (lastZero m) = 0 := by {
  induction m with
  | zero => rfl
  | succ m ih =>
    unfold lastZero
    split
    · rename_i hz
      exact hz
    · exact ih
}

lemma lastZero_le (m : ℕ) : lastZero m ≤ m := by {
  induction m with
  | zero => exact Nat.le_refl 0
  | succ m ih =>
    unfold lastZero
    split
    · exact Nat.le_refl (m + 1)
    · exact Nat.le_trans ih (Nat.le_succ m)
}

lemma no_zero_after_lastZero (m k : ℕ) (hk1 : lastZero m < k) (hk2 : k ≤ m) :
    vanEckNthTerm k ≠ 0 := by {
  induction m generalizing k with
  | zero => omega
  | succ m ih =>
    unfold lastZero at hk1
    split at hk1
    · omega
    · by_cases hkm : k = m + 1
      · subst hkm
        rename_i h_neq
        exact h_neq
      · have hk2' : k ≤ m := by omega
        exact ih k hk1 hk2'
}

lemma gap_contains_all_terms (N G : ℕ)
    (h_nonzero : ∀ j, N < j → j < N + G → vanEckNthTerm j ≠ 0) :
    ∀ k < N + G - 1, vanEckNthTerm k ≤ vanEckPrefixMax N := by {
  intro k
  induction k using Nat.strong_induction_on
  next m ih =>
    intro hk
    by_cases h_le : m ≤ N
    · exact vanEckNthTerm_le_prefixMax N m h_le
    · have h_gt : m > N := Nat.lt_of_not_ge h_le
      have hm_pos : m > 0 := Nat.lt_of_le_of_lt (Nat.zero_le N) h_gt
      have h_m_sub : m - 1 ≥ N := Nat.le_sub_one_of_lt h_gt
      have h_m2 : m - 1 + 2 < N + G := by
        have h_sub : m - 1 + 1 = m := Nat.sub_add_cancel hm_pos
        have h1 : m - 1 + 2 = m + 1 := by
          calc m - 1 + 2 = m - 1 + 1 + 1 := rfl
               _ = m + 1 := by rw [h_sub]
        rw [h1]
        exact Nat.add_lt_of_lt_sub hk
      have h_ex := gap_nonzero_implies_recurrence N (m - 1) G h_nonzero h_m_sub h_m2
      rcases h_ex with ⟨n, hn, heq⟩
      have hm_eq : m - 1 + 1 = m := Nat.sub_add_cancel hm_pos
      rw [hm_eq] at heq
      rw [hm_eq] at hn
      have hn_lt : n < N + G - 1 := Nat.lt_trans hn hk
      have ih_res := ih n hn hn_lt
      rw [heq]
      exact ih_res
}

lemma gap_between_zeros (z z_prev : ℕ) (hz : vanEckNthTerm z = 0) (hz_pos : z > 0)
    (hz_prev : vanEckNthTerm z_prev = 0) (h_prev_lt : z_prev < z)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) :
    vanEckNthTerm (z + 1) = z - z_prev := by {
  have ha := vanEck_term_is_matchSearch (z + 1) (by omega)
  have h_len : (vanEck z).length = z + 1 := vanEckLength z
  
  have hd_last : listNth (vanEck z) z = 0 := by
    rw [VanEck_deterministic z z (Nat.le_refl _)]
    exact hz
    
  have hd_start : listNth (vanEck z) z_prev = 0 := by
    rw [VanEck_deterministic z z_prev (by omega)]
    exact hz_prev
    
  have h_match : listNth (vanEck z) ((vanEck z).length - 1) = listNth (vanEck z) z_prev := by
    have h1 : (vanEck z).length - 1 = z := by rw [h_len]; rfl
    rw [h1, hd_last, hd_start]
    
  have h_fail : ∀ k, 1 ≤ k → k ≤ z - z_prev - 1 → listNth (vanEck z) ((vanEck z).length - 1) ≠ listNth (vanEck z) (z_prev + k) := by
    intro k hk1 hk_le
    have h_idx : z_prev + k < z := by omega
    have h_det : listNth (vanEck z) (z_prev + k) = vanEckNthTerm (z_prev + k) := VanEck_deterministic z (z_prev + k) (by omega)
    have h1 : (vanEck z).length - 1 = z := by rw [h_len]; rfl
    rw [h1, hd_last, h_det]
    intro hc
    have h_i_zero : vanEckNthTerm (z_prev + k) = 0 := hc.symm
    exact h_gap (z_prev + k) (by omega) (by omega) h_i_zero

  have h_ms := matchSearch_eq_dist (vanEck z) z_prev (z - z_prev - 1) h_match h_fail
  have h_arg : z_prev + (z - z_prev - 1) + 1 = z := by omega
  rw [h_arg] at h_ms
  have h_len_sub : (vanEck z).length - 1 - z_prev = z - z_prev := by rw [h_len]; omega
  rw [h_len_sub] at h_ms
  have h_z_sub : z + 1 - 1 = z := by omega
  rw [h_z_sub] at ha
  rw [ha, h_ms]
}

