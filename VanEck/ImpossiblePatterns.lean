/-
Copyright (c) 2026 Austin Anderson
SPDX-License-Identifier: MIT

Note: Gemini was used for both intuition and especially detailed entry in formalizing this proof.
Credit to oeis.org and Van Eck himself for the intuition behind these impossible patterns.
-/
import VanEck
import Mathlib

lemma a_le_idx_minus_one {i : ℕ} (hi : i ≥ 2) (hi_pos : vanEckNthTerm i > 0) : vanEckNthTerm i ≤ i - 1 := by {
  by_cases heq : vanEckNthTerm i = i
  · exfalso
    have h_a_i : vanEckNthTerm i = matchSearch (vanEck (i - 1)) (i - 1) := vanEck_term_is_matchSearch i (Nat.le_trans (by decide) hi)
    have hm_match := matchSearch_matches (vanEck (i - 1)) (i - 1)
    have hm_neq : matchSearch (vanEck (i - 1)) (i - 1) ≠ 0 := by rw [← h_a_i]; exact (Nat.ne_of_gt hi_pos)
    have hm := hm_match hm_neq
    have h_len : (vanEck (i - 1)).length = i := by
      have hl := vanEckLength (i - 1)
      have h1 : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.le_trans (by decide) hi)
      rw [h1] at hl
      exact hl
    have h_len_sub_1 : (vanEck (i - 1)).length - 1 = i - 1 := by rw [h_len]
    rw [h_len_sub_1] at hm
    rw [← h_a_i] at hm
    rw [heq] at hm
    have h_sub2 : i - 1 - i = 0 := by exact Nat.sub_eq_zero_of_le (Nat.le_trans (Nat.sub_le i 1) (Nat.le_refl i))
    rw [h_sub2] at hm
    have hl_0 : listNth (vanEck (i - 1)) 0 = 0 := list_nth_VanEck_zero_eq_zero (i - 1)
    rw [hl_0] at hm
    have hd_list : listNth (vanEck (i - 1)) (i - 1) = vanEckNthTerm (i - 1) := rfl
    rw [hd_list] at hm
    have h_a_i_1 : vanEckNthTerm (i - 1) = 0 := hm

    have h_first := matchSearch_first (vanEck (i - 1)) (i - 1) 0 hm_neq (Nat.sub_pos_of_lt (Nat.lt_of_succ_le hi))
    have h_match2 : listNth (vanEck (i - 1)) ((vanEck (i - 1)).length - 1) = listNth (vanEck (i - 1)) 0 := by
      rw [h_len_sub_1, hd_list, hl_0, h_a_i_1]
    have h_bound := h_first h_match2
    rw [← h_a_i, heq, h_len_sub_1] at h_bound
    have h_bound2 : i ≤ i - 1 := by
      calc i ≤ i - 1 - 0 := h_bound
        _ = i - 1 := Nat.sub_zero _
    have h_not : ¬(i ≤ i - 1) := by
      intro hl
      have hs : i - 1 + 1 ≤ i - 1 := by
        calc i - 1 + 1 = i := Nat.sub_add_cancel (Nat.le_trans (by decide) hi)
          _ ≤ i - 1 := hl
      exact Nat.not_succ_le_self (i - 1) hs
    exact h_not h_bound2
  · have h_le := vanEckNthTerm_le_n i
    have h_lt : vanEckNthTerm i < i := Nat.lt_of_le_of_ne h_le heq
    exact Nat.le_pred_of_lt h_lt
}

/--
Theorem: i - a(i) is unique for all i, a(i) > 0.
Put differently: i - a(i) ≠ j - a(j) for all i, j with a(i) > 0 and j > i.
-/
theorem vanEck_idx_sub_val_unique (i j : ℕ) (hi_pos : vanEckNthTerm i > 0) (h_lt : i < j) :
    i - vanEckNthTerm i ≠ j - vanEckNthTerm j := by {
  intro h_eq

  have hi_ge_2 : i ≥ 2 := by
    cases i with
    | zero =>
      have h0 : vanEckNthTerm 0 = 0 := vanEck_head_eq_zero 0
      rw [h0] at hi_pos; contradiction
    | succ i1 =>
      cases i1 with
      | zero =>
        have h1 : vanEckNthTerm 1 = 0 := rfl
        rw [h1] at hi_pos; contradiction
      | succ i2 => exact Nat.le_add_left 2 i2

  have hj_ge_2 : j ≥ 2 := Nat.le_trans hi_ge_2 (Nat.le_of_lt h_lt)

  have ha_i_le : vanEckNthTerm i ≤ i - 1 := a_le_idx_minus_one hi_ge_2 hi_pos

  have h_sub_i : i - vanEckNthTerm i ≥ 1 := by
    exact Nat.le_sub_of_add_le (by
      calc 1 + vanEckNthTerm i = vanEckNthTerm i + 1 := Nat.add_comm 1 _
        _ ≤ i - 1 + 1 := Nat.add_le_add_right ha_i_le 1
        _ = i := Nat.sub_add_cancel (Nat.le_trans (by decide) hi_ge_2)
    )

  have hj_pos : vanEckNthTerm j > 0 := by
    by_cases hj0 : vanEckNthTerm j = 0
    · rw [hj0] at h_eq
      have h_sub_j : j - 0 = j := Nat.sub_zero j
      rw [h_sub_j] at h_eq
      have h_i_sub_le : i - vanEckNthTerm i ≤ i := Nat.sub_le _ _
      have h_bad : j ≤ i := by
        calc j = i - vanEckNthTerm i := h_eq.symm
          _ ≤ i := h_i_sub_le
      have h_not : ¬(j ≤ i) := Nat.not_le_of_lt h_lt
      contradiction
    · exact Nat.pos_of_ne_zero hj0

  have ha_j_le : vanEckNthTerm j ≤ j - 1 := a_le_idx_minus_one hj_ge_2 hj_pos

  have hd_i : vanEckNthTerm (i - 1) = vanEckNthTerm (i - 1 - vanEckNthTerm i) := by
    have h1 : i - 1 ≥ 1 := Nat.le_sub_of_add_le (by exact hi_ge_2)
    have hi_neq : vanEckNthTerm i ≠ 0 := Nat.ne_of_gt hi_pos
    have hx : vanEckNthTerm (i - 1 + 1) = vanEckNthTerm i := by
      have h2 : i - 1 + 1 = i := Nat.sub_add_cancel (Nat.le_trans (by decide) hi_ge_2)
      rw [h2]
    exact gap_determines_value (i - 1) (Nat.le_refl _) (vanEckNthTerm i) h1 hx hi_neq

  have hd_j : vanEckNthTerm (j - 1) = vanEckNthTerm (j - 1 - vanEckNthTerm j) := by
    have h1 : j - 1 ≥ 1 := Nat.le_sub_of_add_le (by exact hj_ge_2)
    have hj_neq : vanEckNthTerm j ≠ 0 := Nat.ne_of_gt hj_pos
    have hx : vanEckNthTerm (j - 1 + 1) = vanEckNthTerm j := by
      have h2 : j - 1 + 1 = j := Nat.sub_add_cancel (Nat.le_trans (by decide) hj_ge_2)
      rw [h2]
    exact gap_determines_value (j - 1) (Nat.le_refl _) (vanEckNthTerm j) h1 hx hj_neq

  have h_sub_eq : i - 1 - vanEckNthTerm i = j - 1 - vanEckNthTerm j := by
    calc i - 1 - vanEckNthTerm i = i - vanEckNthTerm i - 1 := Nat.sub_right_comm i 1 (vanEckNthTerm i)
      _ = j - vanEckNthTerm j - 1 := by rw [h_eq]
      _ = j - 1 - vanEckNthTerm j := (Nat.sub_right_comm j 1 (vanEckNthTerm j)).symm

  have ha_eq : vanEckNthTerm (i - 1) = vanEckNthTerm (j - 1) := by
    rw [hd_i, hd_j, h_sub_eq]

  have h_a_j : vanEckNthTerm j = matchSearch (vanEck (j - 1)) (j - 1) := vanEck_term_is_matchSearch j (Nat.le_trans (by decide) hj_ge_2)
  have hj_neq : matchSearch (vanEck (j - 1)) (j - 1) ≠ 0 := by rw [← h_a_j]; exact Nat.ne_of_gt hj_pos
  have hk_lt : i - 1 < j - 1 := Nat.sub_lt_sub_right (Nat.le_trans (by decide) hi_ge_2) h_lt

  have hl_len : (vanEck (j - 1)).length = j := by
    have hl := vanEckLength (j - 1)
    have h1 : j - 1 + 1 = j := Nat.sub_add_cancel (Nat.le_trans (by decide) hj_ge_2)
    rw [h1] at hl
    exact hl
  have hl_len_sub_1 : (vanEck (j - 1)).length - 1 = j - 1 := by rw [hl_len]

  have h_match : listNth (vanEck (j - 1)) ((vanEck (j - 1)).length - 1) = listNth (vanEck (j - 1)) (i - 1) := by
    rw [hl_len_sub_1]
    have hd_j_list : listNth (vanEck (j - 1)) (j - 1) = vanEckNthTerm (j - 1) := rfl
    have hd_i_list : listNth (vanEck (j - 1)) (i - 1) = vanEckNthTerm (i - 1) := by
      have hlt2 : i - 1 ≤ j - 1 := Nat.le_of_lt hk_lt
      have hd_symm : listNth (vanEck (i - 1)) (i - 1) = listNth (vanEck (j - 1)) (i - 1) := (VanEck_deterministic (j - 1) (i - 1) hlt2).symm
      change vanEckNthTerm (i - 1) = listNth (vanEck (j - 1)) (i - 1) at hd_symm
      exact hd_symm.symm
    rw [hd_j_list, hd_i_list]
    exact ha_eq.symm

  have h_first := matchSearch_first (vanEck (j - 1)) (j - 1) (i - 1) hj_neq hk_lt h_match
  rw [hl_len_sub_1] at h_first
  rw [← h_a_j] at h_first

  have h_j_sub : j - vanEckNthTerm j ≥ i := by
    calc j - vanEckNthTerm j ≥ j - (j - 1 - (i - 1)) := Nat.sub_le_sub_left h_first j
      _ = j - (j - i) := by
        have hsub : j - 1 - (i - 1) = j - i := by
          have h1 : j - 1 - (i - 1) + (i - 1) = j - 1 := Nat.sub_add_cancel (Nat.le_of_lt hk_lt)
          have h2 : j - i + (i - 1) = j - i + i - 1 := by rw [Nat.add_sub_assoc (Nat.le_trans (by decide) hi_ge_2)]
          have h3 : j - i + i = j := Nat.sub_add_cancel (Nat.le_of_lt h_lt)
          have h4 : j - i + (i - 1) = j - 1 := by rw [h2, h3]
          exact Nat.add_right_cancel (h1.trans h4.symm)
        rw [hsub]
      _ = i := Nat.sub_sub_self (Nat.le_of_lt h_lt)

  have h_contra : j - vanEckNthTerm j < i := by
    have h_i_pos : 0 < i := Nat.le_trans (by decide) hi_ge_2
    calc j - vanEckNthTerm j = i - vanEckNthTerm i := h_eq.symm
      _ < i := Nat.sub_lt h_i_pos hi_pos

  have h_not : ¬(j - vanEckNthTerm j ≥ i) := Nat.not_le_of_lt h_contra
  exact h_not h_j_sub
}

/--
Theorem: i - a(i+1) - a(i) is unique for all i with a(i+1) > 0 and a(i) > 0.
-/
theorem vanEck_idx_sub_succ_sub_val_unique (i j : ℕ)
    (hi1_pos : vanEckNthTerm (i + 1) > 0) (hi_pos : vanEckNthTerm i > 0)
    (hj1_pos : vanEckNthTerm (j + 1) > 0) (hj_pos : vanEckNthTerm j > 0)
    (h_lt : i < j) :
    i - vanEckNthTerm (i + 1) - vanEckNthTerm i ≠ j - vanEckNthTerm (j + 1) - vanEckNthTerm j := by {
  intro h_eq

  have hi_ge_1 : i ≥ 1 := by
    cases i with
    | zero =>
      have h0 : vanEckNthTerm 0 = 0 := vanEck_head_eq_zero 0
      rw [h0] at hi_pos; contradiction
    | succ i1 => exact Nat.le_add_left 1 i1
  have hj_ge_1 : j ≥ 1 := Nat.le_trans hi_ge_1 (Nat.le_of_lt h_lt)
  have hd_i : vanEckNthTerm i = vanEckNthTerm (i - vanEckNthTerm (i + 1)) := by
    exact gap_determines_value i hi_ge_1 (vanEckNthTerm (i + 1))
      (Nat.le_refl 1) rfl (Nat.ne_of_gt hi1_pos)
  have hd_j : vanEckNthTerm j = vanEckNthTerm (j - vanEckNthTerm (j + 1)) := by
    exact gap_determines_value j hj_ge_1 (vanEckNthTerm (j + 1))
      (Nat.le_refl 1) rfl (Nat.ne_of_gt hj1_pos)
  let ki := i - vanEckNthTerm (i + 1)
  let kj := j - vanEckNthTerm (j + 1)
  have hk_eq : ki - vanEckNthTerm ki = kj - vanEckNthTerm kj := by
    have h1 : ki - vanEckNthTerm ki = i - vanEckNthTerm (i + 1) - vanEckNthTerm i := by rw [← hd_i]
    have h2 : kj - vanEckNthTerm kj = j - vanEckNthTerm (j + 1) - vanEckNthTerm j := by rw [← hd_j]
    rw [h1, h2]
    exact h_eq
  have hki_pos : vanEckNthTerm ki > 0 := by
    rw [← hd_i]
    exact hi_pos
  by_cases hki_eq : ki = kj
  · have hj_match := matchSearch_matches (vanEck j) j
    have hj_search : vanEckNthTerm (j + 1) = matchSearch (vanEck j) j :=
      vanEck_term_is_matchSearch (j + 1) (Nat.le_add_left 1 j)
    have hj_neq : matchSearch (vanEck j) j ≠ 0 := by rw [← hj_search]; exact Nat.ne_of_gt hj1_pos
    have hm := hj_match hj_neq
    have h_len : (vanEck j).length = j + 1 := vanEckLength j
    have h_len_sub_1 : (vanEck j).length - 1 = j := by
      rw [h_len, Nat.add_sub_cancel]
    rw [h_len_sub_1] at hm
    rw [← hj_search] at hm
    have hl_j : listNth (vanEck j) j = vanEckNthTerm j := rfl
    rw [hl_j] at hm
    have hl_kj : listNth (vanEck j) kj = vanEckNthTerm kj := by
      have h_kj_le : kj ≤ j := Nat.sub_le _ _
      exact VanEck_deterministic j kj h_kj_le
    have h_sub_kj : j - vanEckNthTerm (j + 1) = kj := rfl
    rw [h_sub_kj, hl_kj] at hm
    have h_aj_eq : vanEckNthTerm j = vanEckNthTerm kj := hm
    have h_first := matchSearch_first (vanEck j) j i hj_neq h_lt
    have h_match2 : listNth (vanEck j) ((vanEck j).length - 1) = listNth (vanEck j) i := by
      rw [h_len_sub_1, hl_j]
      have hl_i : listNth (vanEck j) i = vanEckNthTerm i := by
        have h_i_le : i ≤ j := Nat.le_of_lt h_lt
        exact VanEck_deterministic j i h_i_le
      rw [hl_i]
      have h_ai_eq : vanEckNthTerm i = vanEckNthTerm ki := hd_i
      rw [h_aj_eq, h_ai_eq]
      rw [hki_eq]
    have h_bound := h_first h_match2
    rw [h_len_sub_1, ← hj_search] at h_bound
    have h_j_sub : j - vanEckNthTerm (j + 1) ≥ i := by
      calc j - vanEckNthTerm (j + 1) ≥ j - (j - i) := Nat.sub_le_sub_left h_bound j
        _ = i := Nat.sub_sub_self (Nat.le_of_lt h_lt)
    have h_kj_ge_i : kj ≥ i := h_j_sub
    rw [← hki_eq] at h_kj_ge_i
    have h_ki_sub : ki = i - vanEckNthTerm (i + 1) := rfl
    have h_contra : i - vanEckNthTerm (i + 1) ≥ i := by
      calc i - vanEckNthTerm (i + 1) = ki := h_ki_sub.symm
        _ ≥ i := h_kj_ge_i
    have h_i_lt : i - vanEckNthTerm (i + 1) < i :=
      Nat.sub_lt (Nat.le_trans (by decide) hi_ge_1) hi1_pos
    have h_not_ge : ¬(i - vanEckNthTerm (i + 1) ≥ i) := Nat.not_le_of_lt h_i_lt
    exact h_not_ge h_contra
  · by_cases hk_lt_ki : ki < kj
    · have h_unique := vanEck_idx_sub_val_unique ki kj hki_pos hk_lt_ki
      exact h_unique hk_eq
    · have hk_gt : kj < ki := Nat.lt_of_le_of_ne (Nat.le_of_not_lt hk_lt_ki) (Ne.symm hki_eq)
      have hkj_pos : vanEckNthTerm kj > 0 := by
        rw [← hd_j]
        exact hj_pos
      have h_unique := vanEck_idx_sub_val_unique kj ki hkj_pos hk_gt
      exact h_unique hk_eq.symm
}

/--
Theorem: If two consecutive elements are equal, the next element must be 1.
-/
theorem vanEck_consecutive_eq_implies_next_one (i : ℕ)
    (h : vanEckNthTerm i = vanEckNthTerm (i + 1)) :
    vanEckNthTerm (i + 2) = 1 := by {
  have hm := vanEck_term_is_matchSearch (i + 2) (Nat.zero_lt_succ _)
  have hsub : i + 2 - 1 = i + 1 := rfl
  rw [hsub] at hm
  rw [hm]
  have hlen : (vanEck (i + 1)).length = i + 2 := vanEckLength (i + 1)
  have hlen1 : (vanEck (i + 1)).length - 1 = i + 1 := by rw [hlen]; rfl
  have hd1 : listNth (vanEck (i + 1)) (i + 1) = vanEckNthTerm (i + 1) := by
    exact VanEck_deterministic (i + 1) (i + 1) (Nat.le_refl _)
  have hd0 : listNth (vanEck (i + 1)) i = vanEckNthTerm i := by
    exact VanEck_deterministic (i + 1) i (Nat.le_succ _)
  have hpos : listNth (vanEck (i + 1)) ((vanEck (i + 1)).length - 1) =
              listNth (vanEck (i + 1)) i := by
    rw [hlen1, hd1, hd0]
    exact h.symm
  have h_ms := ms_succ_ifpos (vanEck (i + 1)) i hpos
  rw [hlen1] at h_ms
  have h_sub_1 : i + 1 - i = 1 := Nat.add_sub_cancel_left i 1
  rw [h_sub_1] at h_ms
  exact h_ms
}

lemma vanEck_consecutive_ones_implies_prev_one (i : ℕ) (hi : i ≥ 1)
    (h : vanEckNthTerm i = 1 ∧ vanEckNthTerm (i + 1) = 1) :
    vanEckNthTerm (i - 1) = 1 := by {
  have hd : vanEckNthTerm i = vanEckNthTerm (i - vanEckNthTerm (i + 1)) := by
    exact gap_determines_value i (Nat.le_refl _) (vanEckNthTerm (i + 1)) hi
      rfl (by rw [h.2]; decide)
  rw [h.2] at hd
  have heq : vanEckNthTerm i = vanEckNthTerm (i - 1) := hd
  rw [h.1] at heq
  exact heq.symm
}

/--
Theorem: The sequence never contains two consecutive 1s.
-/
theorem vanEck_no_consecutive_ones (i : ℕ) :
    ¬(vanEckNthTerm i = 1 ∧ vanEckNthTerm (i + 1) = 1) := by {
  induction i with
  | zero =>
    intro h
    have h0 : vanEckNthTerm 0 = 0 := vanEck_head_eq_zero 0
    have h1 : 0 = 1 := by calc 0 = vanEckNthTerm 0 := h0.symm
                            _ = 1 := h.1
    contradiction
  | succ i ih =>
    intro h
    have h_prev : vanEckNthTerm i = 1 := by
      have h1 : i + 1 ≥ 1 := Nat.le_add_left 1 i
      have h_prev_1 := vanEck_consecutive_ones_implies_prev_one (i + 1) h1 h
      have hsub : i + 1 - 1 = i := rfl
      rw [hsub] at h_prev_1
      exact h_prev_1
    have h_conj : vanEckNthTerm i = 1 ∧ vanEckNthTerm (i + 1) = 1 := ⟨h_prev, h.1⟩
    exact ih h_conj
}

/--
Theorem: The sequence never contains three consecutive identical values (no triples).
-/
theorem vanEck_triple_impossible (i x : ℕ) :
    ¬(vanEckNthTerm i = x ∧ vanEckNthTerm (i + 1) = x ∧ vanEckNthTerm (i + 2) = x) := by {
  intro h
  rcases h with ⟨h1, h2, h3⟩
  have heq : vanEckNthTerm i = vanEckNthTerm (i + 1) := by rw [h1, h2]
  have hnext := vanEck_consecutive_eq_implies_next_one i heq
  have h_x_eq_1 : x = 1 := by
    calc x = vanEckNthTerm (i + 2) := h3.symm
         _ = 1 := hnext
  have h_ones : vanEckNthTerm (i + 1) = 1 ∧ vanEckNthTerm (i + 2) = 1 := by
    constructor
    · rw [h2, h_x_eq_1]
    · exact hnext
  exact vanEck_no_consecutive_ones (i + 1) h_ones
}


lemma constant_tail_backward (c n : ℕ) (hc : c > 0)
    (h_tail : ∀ k ≥ n, vanEckNthTerm k = c) :
    ∀ m ≤ n, ∀ k ≥ n - m, vanEckNthTerm k = c := by {
  intro m
  induction m with
  | zero =>
    intro h_le k hk
    have h_eq : n - 0 = n := rfl
    rw [h_eq] at hk
    exact h_tail k hk
  | succ m ih =>
    intro h_le k hk
    have h_le_m : m ≤ n := Nat.le_trans (Nat.le_succ m) h_le
    have h_prev := ih h_le_m

    by_cases hk_ge : k ≥ n - m
    · exact h_prev k hk_ge
    · have h_k_eq : k = n - (m + 1) := by omega

      let k2 := k + c + 1
      have hk2_ge : k2 ≥ n - m := by omega
      have h1 : vanEckNthTerm k2 = c := h_prev k2 hk2_ge

      let k1 := k + c
      have hk1_ge : k1 ≥ n - m := by omega
      have h2 : vanEckNthTerm k1 = c := h_prev k1 hk1_ge

      have hk1_ge1 : k1 ≥ 1 := by omega
      have h_c_neq_0 : c ≠ 0 := by omega
      
      have hk_eq_succ : k1 + 1 = k2 := by omega
      have h1_subst : vanEckNthTerm (k1 + 1) = c := by rw [hk_eq_succ]; exact h1
      
      have h_gap := gap_determines_value (n := 1) k1 hk1_ge1 c (by omega) h1_subst h_c_neq_0
      
      have h_sub : k1 - c = k := by omega
      
      rw [h_sub] at h_gap
      rw [h2] at h_gap
      exact h_gap.symm
}

lemma constant_tail_contradiction (c n_0 : ℕ) (hc : c > 0)
    (h_tail : ∀ k ≥ n_0, vanEckNthTerm k = c) : False := by {
  have hz := constant_tail_backward c n_0 hc h_tail n_0 (Nat.le_refl n_0) 0 (by omega)
  have hz_def : vanEckNthTerm 0 = 0 := rfl
  rw [hz_def] at hz
  omega
}

/-
Note on recursions in Lean:
Proving properties of general nested recursions (like those arising from direct lookback relationships
in the Van Eck sequence) is notorious in Lean for causing cyclic termination and well-founded
recursion proof obligations. To avoid these "motive is not type correct" type errors and
accessibility (Acc) proof mismatches, we proxy the structural constraints by proving bounds
on the density/growth of the sets (e.g. FibonacciSet or PowersOfTwoSet) instead of induction
directly over the lookup definitions.
-/

def FibonacciSet : Set ℕ := {n | ∃ k, n = Nat.fib k}

def PowersOfTwoSet : Set ℕ := {n | n = 0 ∨ ∃ k, n = 2 ^ k}

lemma five_not_in_powers_of_two : 5 ∉ PowersOfTwoSet := by {
  intro hc
  rcases hc with h0 | ⟨k, hk⟩
  · contradiction
  · cases k with
    | zero => contradiction
    | succ k =>
      cases k with
      | zero => contradiction
      | succ k =>
        cases k with
        | zero => contradiction
        | succ k =>
          have h_ge : 2 ^ (k + 3) ≥ 8 := by {
            have h1 : 2 ^ (k + 3) = 2 ^ k * 8 := by ring
            rw [h1]
            have h2 : 2 ^ k ≥ 1 := Nat.one_le_pow k 2 (by decide)
            omega
          }
          omega
}



lemma fib_two_k_succ_ge_pow_two (k : ℕ) : Nat.fib (2 * k + 2) ≥ 2 ^ k := by {
  induction k with
  | zero => decide
  | succ k ih =>
    have h_eq : 2 * (k + 1) + 2 = (2 * k + 2) + 2 := by ring
    rw [h_eq]
    rw [Nat.fib_add_two]
    have h_mono : Nat.fib (2 * k + 2) ≤ Nat.fib (2 * k + 2 + 1) := Nat.fib_le_fib_succ
    have h_ge : Nat.fib (2 * k + 2 + 1) + Nat.fib (2 * k + 2) ≥ 2 * Nat.fib (2 * k + 2) := by omega
    have h_pow : 2 ^ (k + 1) = 2 * 2 ^ k := by ring
    rw [h_pow]
    omega

}




