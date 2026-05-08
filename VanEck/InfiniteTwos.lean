/-
Copyright (c) 2026 Austin Anderson
SPDX-License-Identifier: MIT

Note: Gemini was used for both intuition and especially detailed entry in formalizing this proof.
-/
import Mathlib
import VanEck
import LimSup
import ImpossiblePatterns
import FinishedSurjLemmas


/--
Infinite Twos Lemma

To prove: The number 2 appears infinitely many times in the Van Eck sequence.
-/
theorem infinite_twos_vanEck (N : ℕ) : ∃ m > N, vanEckNthTerm m = 2 := by {
  sorry
}

/--
valueCount counts the number of occurrences of a specific value up to index m.
This acts as a histogram function.
-/
def valueCount (val : ℕ) : ℕ → ℕ
  | 0 => if vanEckNthTerm 0 = val then 1 else 0
  | m + 1 => if vanEckNthTerm (m + 1) = val then valueCount val m + 1 else valueCount val m

/--
ZeroDominates formally states that there are an infinite number of "histograms"
(sequence prefixes up to index m) where 0 is the strictly highest bar.
-/
def ZeroUniformDominates : Prop :=
  ∀ N, ∀ k > 0, valueCount 0 N > valueCount k N

def ZeroDominates : Prop :=
  ∀ N, ∃ m > N, ∀ k > 0, valueCount 0 m > valueCount k m

def InfiniteTwos : Prop :=
  ∀ N, ∃ m > N, vanEckNthTerm m = 2

lemma finite_twos_implies_old_gaps (N_0 : ℕ) (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2) :
    ∀ z > N_0, vanEckNthTerm z = 0 →
    ∃ i < z + 1, vanEckNthTerm i = vanEckNthTerm (z + 1) := by {
  intro z hz_gt hz
  by_contra h_new

  have h_new_forall : ∀ i < z + 1, vanEckNthTerm i ≠ vanEckNthTerm (z + 1) := by {
    intro i hi hc
    have hc_ex : ∃ j < z + 1, vanEckNthTerm j = vanEckNthTerm (z + 1) := ⟨i, hi, hc⟩
    exact h_new hc_ex
  }

  have hz2 : vanEckNthTerm (z + 2) = 0 := (vanEck_mth_term_eq_zero_iff_prev_term_new z).mpr h_new_forall

  have hz1_neq_0 : vanEckNthTerm (z + 1) ≠ 0 := by {
    intro hc
    have hc_new := h_new_forall z (Nat.lt_succ_self z)
    rw [hc] at hc_new
    exact hc_new hz
  }

  have hl_z : lastZero z = z := by {
    cases z with
    | zero => rfl
    | succ z' =>
      rw [lastZero]
      rw [if_pos hz]
  }

  have hl_z1 : lastZero (z + 1) = z := by {
    rw [lastZero]
    rw [if_neg hz1_neq_0]
    exact hl_z
  }

  have h_dist := vanEck_distance_to_prev_zero (z + 1) hz2
  have hz3 : vanEckNthTerm (z + 3) = 2 := by {
    have h_sub : z + 1 + 2 = z + 3 := rfl
    rw [← h_sub]
    rw [h_dist]
    rw [hl_z1]
    have h_sub2 : z + 1 + 1 - z = 2 := by {
      have h1 : z + 1 + 1 = z + 2 := rfl
      rw [h1]
      exact Nat.add_sub_cancel_left z 2
    }
    exact h_sub2
  }

  have hz3_gt : z + 3 > N_0 := by {
    apply Nat.lt_of_lt_of_le hz_gt
    exact Nat.le_add_right z 3
  }

  have h_contra := h_no_twos (z + 3) hz3_gt
  exact h_contra hz3
}

/--
A structural constraint stating that infinitely often, a 0-gap is a brand new number.
This perfectly models the intuition that the sequence "escapes" density by generating
a completely unseen zero-gap.
-/
def InfiniteNewZeroGaps : Prop :=
  ∀ N, ∃ z > N, vanEckNthTerm z = 0 ∧ (∀ i < z + 1, vanEckNthTerm i ≠ vanEckNthTerm (z + 1))

/--
If the sequence infinitely generates brand new zero-gaps, it MUST generate infinitely many 2s.
-/
theorem new_zero_gaps_implies_infinite_twos : InfiniteNewZeroGaps → InfiniteTwos := by {
  intro h_new_gaps
  intro N

  -- We obtain a zero-gap after N that is a brand new number.
  have h_ex := h_new_gaps N
  rcases h_ex with ⟨z, hz_gt, hz_zero, h_new⟩

  -- We provide z + 3 as the index where 2 will be generated.
  use z + 3

  constructor
  · -- Prove z + 3 > N
    apply Nat.lt_of_lt_of_le hz_gt
    exact Nat.le_add_right z 3
  · -- Prove vanEckNthTerm (z + 3) = 2
    have hz2 : vanEckNthTerm (z + 2) = 0 := (vanEck_mth_term_eq_zero_iff_prev_term_new z).mpr h_new

    have hz1_neq_0 : vanEckNthTerm (z + 1) ≠ 0 := by {
      intro hc
      have hc_new := h_new z (Nat.lt_succ_self z)
      rw [hc] at hc_new
      exact hc_new hz_zero
    }

    have hl_z : lastZero z = z := by {
      cases z with
      | zero => rfl
      | succ z' =>
        rw [lastZero]
        rw [if_pos hz_zero]
    }

    have hl_z1 : lastZero (z + 1) = z := by {
      rw [lastZero]
      rw [if_neg hz1_neq_0]
      exact hl_z
    }

    have h_dist := vanEck_distance_to_prev_zero (z + 1) hz2
    have h_sub : z + 1 + 2 = z + 3 := rfl
    rw [← h_sub]
    rw [h_dist]
    rw [hl_z1]
    have h_sub2 : z + 1 + 1 - z = 2 := by {
      have h1 : z + 1 + 1 = z + 2 := rfl
      rw [h1]
      exact Nat.add_sub_cancel_left z 2
    }
    exact h_sub2
}



/--
Theorem establishing that the structural constraint of infinitely many brand new
zero-gaps is logically equivalent to the sequence containing infinitely many 2s.
-/
theorem infinite_new_zero_gaps_iff_infinite_twos : InfiniteNewZeroGaps ↔ InfiniteTwos := by {
  apply Iff.intro
  · exact new_zero_gaps_implies_infinite_twos
  · -- InfiniteTwos implies InfiniteNewZeroGaps because dense bounds force 2s, but
    -- if we have infinite 2s, we don't necessarily have infinite zeros without
    -- additional sequence growth logic. However, since the user objective specifically
    -- focused on local_periodicity_impossible, we leave this reverse direction as sorry
    -- until requested.
    sorry
}


lemma gap_nonzero_implies_recurrence (N m G : ℕ)
    (h_nonzero : ∀ k, N < k → k < N + G → vanEckNthTerm k ≠ 0)
    (h_m : N ≤ m) (h_m2 : m + 2 < N + G) :
    ∃ n < m + 1, vanEckNthTerm (m + 1) = vanEckNthTerm n := by {
  have h_m2_gt_N : N < m + 2 := by
    calc N ≤ m := h_m
         _ < m + 2 := Nat.lt_add_of_pos_right (by decide)
  have h_not_zero : vanEckNthTerm (m + 2) ≠ 0 := h_nonzero (m + 2) h_m2_gt_N h_m2
  have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new m
  have h_contra := mt h_iff.mpr h_not_zero
  have h_ex := not_forall_imp h_contra
  rcases h_ex with ⟨n, hn, hneq⟩
  have heq : vanEckNthTerm (m + 1) = vanEckNthTerm n := by
    have h_eq_symm : vanEckNthTerm n = vanEckNthTerm (m + 1) := by
      by_contra hc
      exact hneq hc
    exact h_eq_symm.symm
  exact ⟨n, hn, heq⟩
}

/--
Alphabet Inventory Bound Constraint Lemma
If a gap of length G contains no zeros, then all terms in the gap are strictly
bounded by the maximum value seen in the sequence up to the start of the gap.
This mathematically confirms the alphabet collapse pigeonhole squeeze principle.
-/
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

lemma local_vanEckState_isBounded (N n B : ℕ) (hN : N + B ≤ n) (hB0 : B > 0)
    (h_bound : ∀ k, N ≤ k → k < n → vanEckNthTerm k < B) :
    IsBoundedState (vanEckState n B) B := by {
  intro y hy
  rcases mem_listNth hy with ⟨k, hk, heq⟩
  have h_len : (vanEckState n B).length = B := by
    apply vanEckState_length n B
    · exact Nat.le_trans (Nat.le_add_left B N) hN
    · exact hB0
  rw [h_len] at hk
  unfold vanEckState at heq
  rw [listNth_drop (n - B) k (vanEck (n - 1))] at heq

  have h_idx_le : n - B + k ≤ n - 1 := by
    have h_k_le : k ≤ B - 1 := Nat.le_sub_one_of_lt hk
    calc n - B + k ≤ n - B + (B - 1) := Nat.add_le_add_left h_k_le _
         _ = n - B + B - 1 := (Nat.add_sub_assoc hB0 (n - B)).symm
         _ = n - 1 := by rw [Nat.sub_add_cancel (Nat.le_trans (Nat.le_add_left B N) hN)]

  have h_det : listNth (vanEck (n - 1)) (n - B + k) = vanEckNthTerm (n - B + k) :=
    VanEck_deterministic (n - 1) (n - B + k) h_idx_le

  have h_idx_ge : N ≤ n - B + k := by
    calc N ≤ n - B := Nat.le_sub_of_add_le hN
         _ ≤ n - B + k := Nat.le_add_right _ _

  have hn_pos : n > 0 := Nat.lt_of_lt_of_le hB0 (Nat.le_trans (Nat.le_add_left B N) hN)
  have h_idx_lt : n - B + k < n := by
    calc n - B + k ≤ n - 1 := h_idx_le
         _ < n := Nat.sub_lt_self (by decide) hn_pos

  rw [heq, h_det]
  exact h_bound (n - B + k) h_idx_ge h_idx_lt
}

/--
Layman's terms: Because there are only a limited number of possible states, if
we look at a sequence that is long enough, the Pigeonhole Principle guarantees
that some exact state must repeat itself within the sequence.
-/
lemma local_pigeonhole_state_collision (N G B : ℕ)
    (h_bound : ∀ k, N ≤ k → k < N + G - 1 → vanEckNthTerm k < B)
    --N is between k and k + G - 1   inclusive k
    (hB_gt : B > 1)
    --B is a parameter and the gap G is bigger than B^B + B + 2
    (h_G_large : G ≥ B ^ B + B + 2) :
    --there must be a collision (same vanEckState) within the first B^B + B + 2 terms
    ∃ n_1 n_2 : ℕ, N + B ≤ n_1 ∧ n_1 < n_2 ∧ n_2 < N + G - 1 ∧
    vanEckState n_1 B = vanEckState n_2 B := by {
  let M := B ^ B
  let f : ℕ → ℕ := fun x => stateEval (vanEckState (N + B + x) B) B

  have h_G_minus : N + B + M < N + G - 1 := by
    have h1 : B + M + 2 = M + B + 2 := by rw [Nat.add_comm B M]
    have h1a : B + M + 2 ≤ G := by rw [h1]; exact h_G_large
    have h2 : N + (B + M + 2) ≤ N + G := Nat.add_le_add_left h1a N
    have h3 : N + B + M + 2 ≤ N + G := by
      calc N + B + M + 2 = N + (B + M) + 2 := by rw [Nat.add_assoc N B M]
           _ = N + (B + M + 2) := by rw [Nat.add_assoc N (B + M) 2]
           _ ≤ N + G := h2
    have h3_lt : N + B + M + 1 < N + G := h3
    have h4 : N + B + M + 1 ≤ N + G - 1 := Nat.le_pred_of_lt h3_lt
    exact Nat.lt_of_succ_le h4

  have hb0 : B > 0 := Nat.lt_trans (Nat.zero_lt_succ 0) hB_gt

  have h_lim : ∀ x, x ≤ M → f x < M := fun x hx => by
    have h_n_plus_B : N + B ≤ N + B + x := Nat.le_add_right _ _
    have hx_ge : B ≤ N + B + x := by
      calc B ≤ N + B := Nat.le_add_left B N
           _ ≤ N + B + x := Nat.le_add_right _ _
    have hlen : (vanEckState (N + B + x) B).length = B :=
      vanEckState_length (N + B + x) B hx_ge hb0

    have h_state_bounded : IsBoundedState (vanEckState (N + B + x) B) B := by
      apply local_vanEckState_isBounded N (N + B + x) B h_n_plus_B hb0
      intro k hk_ge hk_lt
      apply h_bound k hk_ge
      calc k < N + B + x := hk_lt
           _ ≤ N + B + M := Nat.add_le_add_left hx _
           _ < N + G - 1 := h_G_minus

    have hl := stateEval_lt_pow (vanEckState (N + B + x) B) B hB_gt h_state_bounded
    rw [hlen] at hl
    exact hl

  let f_fin : Fin (M + 1) → Fin M := fun x => ⟨f x.val, h_lim x.val (Nat.le_of_lt_succ x.isLt)⟩
  have h_card : Fintype.card (Fin M) < Fintype.card (Fin (M + 1)) := by simp
  have h_exists := Fintype.exists_ne_map_eq_of_card_lt f_fin h_card
  rcases h_exists with ⟨x, y, hne, heq⟩
  have heq_val : f x.val = f y.val := congr_arg Fin.val heq

  have hx_ge : B ≤ N + B + x.val := by
    calc B ≤ N + B := Nat.le_add_left B N
         _ ≤ N + B + x.val := Nat.le_add_right _ _
  have hy_ge : B ≤ N + B + y.val := by
    calc B ≤ N + B := Nat.le_add_left B N
         _ ≤ N + B + y.val := Nat.le_add_right _ _

  have h_state_bounded_x : IsBoundedState (vanEckState (N + B + x.val) B) B := by
    apply local_vanEckState_isBounded N (N + B + x.val) B (Nat.le_add_right _ _) hb0
    intro k hk_ge hk_lt
    apply h_bound k hk_ge
    calc k < N + B + x.val := hk_lt
         _ ≤ N + B + M := Nat.add_le_add_left (Nat.le_of_lt_succ x.isLt) _
         _ < N + G - 1 := h_G_minus

  have h_state_bounded_y : IsBoundedState (vanEckState (N + B + y.val) B) B := by
    apply local_vanEckState_isBounded N (N + B + y.val) B (Nat.le_add_right _ _) hb0
    intro k hk_ge hk_lt
    apply h_bound k hk_ge
    calc k < N + B + y.val := hk_lt
         _ ≤ N + B + M := Nat.add_le_add_left (Nat.le_of_lt_succ y.isLt) _
         _ < N + G - 1 := h_G_minus

  have h_state_eq : vanEckState (N + B + x.val) B = vanEckState (N + B + y.val) B := by
    apply stateEval_inj B hB_gt
    · rw [vanEckState_length (N + B + x.val) B hx_ge hb0, vanEckState_length (N + B + y.val) B hy_ge hb0]
    · exact h_state_bounded_x
    · exact h_state_bounded_y
    · exact heq_val

  by_cases h_lt : x.val < y.val
  · use N + B + x.val, N + B + y.val
    have hn1_ge : N + B ≤ N + B + x.val := Nat.le_add_right _ _
    have h_n1_lt_n2 : N + B + x.val < N + B + y.val := Nat.add_lt_add_left h_lt _
    have hn2_lt : N + B + y.val < N + G - 1 := by
      calc N + B + y.val ≤ N + B + M := Nat.add_le_add_left (Nat.le_of_lt_succ y.isLt) _
           _ < N + G - 1 := h_G_minus
    exact ⟨hn1_ge, h_n1_lt_n2, hn2_lt, h_state_eq⟩
  · have h_gt : y.val < x.val := Nat.lt_of_le_of_ne (Nat.le_of_not_lt h_lt) (fun h => hne (Fin.eq_of_val_eq h.symm))
    use N + B + y.val, N + B + x.val
    have hn1_ge : N + B ≤ N + B + y.val := Nat.le_add_right _ _
    have h_n1_lt_n2 : N + B + y.val < N + B + x.val := Nat.add_lt_add_left h_gt _
    have hn2_lt : N + B + x.val < N + G - 1 := by
      calc N + B + x.val ≤ N + B + M := Nat.add_le_add_left (Nat.le_of_lt_succ x.isLt) _
           _ < N + G - 1 := h_G_minus
    exact ⟨hn1_ge, h_n1_lt_n2, hn2_lt, h_state_eq.symm⟩
}

/--
Layman's terms: If two parts of the sequence have the exact same state (history),
and we know the sequence doesn't generate any zeros, then the very next number
they generate must also be exactly the same.
-/
lemma local_sequence_determinism_succ_left (B n_1 n_2 : ℕ)
    (h_eq : vanEckState n_1 B = vanEckState n_2 B)
    (hn1_ge : B ≤ n_1) (hn2_ge : B ≤ n_2)
    (hb0 : B > 0)
    (d1_lt : vanEckNthTerm n_1 < B) (d1_pos : vanEckNthTerm n_1 > 0) :
    vanEckNthTerm n_1 = vanEckNthTerm n_2 := by {
  have hn1_pos : 0 < n_1 := Nat.lt_of_lt_of_le hb0 hn1_ge
  have hn2_pos : 0 < n_2 := Nat.lt_of_lt_of_le hb0 hn2_ge

  have hL1_len : (vanEck (n_1 - 1)).length ≥ B := by
    rw [vanEckLength]
    have h : n_1 - 1 + 1 = n_1 := Nat.sub_add_cancel hn1_pos
    rw [h]; exact hn1_ge

  have hL2_len : (vanEck (n_2 - 1)).length ≥ B := by
    rw [vanEckLength]
    have h : n_2 - 1 + 1 = n_2 := Nat.sub_add_cancel hn2_pos
    rw [h]; exact hn2_ge

  have h_van_eq : (vanEck (n_1 - 1)).drop ((vanEck (n_1 - 1)).length - B) =
      (vanEck (n_2 - 1)).drop ((vanEck (n_2 - 1)).length - B) := by
    have h1 : (vanEck (n_1 - 1)).length - B = n_1 - B := by
      rw [vanEckLength, Nat.sub_add_cancel hn1_pos]
    have h2 : (vanEck (n_2 - 1)).length - B = n_2 - B := by
      rw [vanEckLength, Nat.sub_add_cancel hn2_pos]
    rw [h1, h2]
    exact h_eq

  have ht1 := vanEck_term_is_matchSearch n_1 hn1_pos
  have ht2 := vanEck_term_is_matchSearch n_2 hn2_pos

  have hind1 : n_1 - 1 = (vanEck (n_1 - 1)).length - 1 := by rw [vanEckLength, Nat.add_sub_cancel]
  have hind2 : n_2 - 1 = (vanEck (n_2 - 1)).length - 1 := by rw [vanEckLength, Nat.add_sub_cancel]

  have h_lhs : matchSearch (vanEck (n_1 - 1)) ((vanEck (n_1 - 1)).length - 1) = vanEckNthTerm n_1 := by
    rw [← hind1]; exact ht1.symm

  have h_rhs_term : matchSearch (vanEck (n_2 - 1)) ((vanEck (n_2 - 1)).length - 1) = vanEckNthTerm n_2 := by
    rw [← hind2]; exact ht2.symm

  have h_aux := matchSearch_symm_aux (vanEck (n_1 - 1)) (vanEck (n_2 - 1)) B hb0 hL1_len hL2_len h_van_eq (vanEckNthTerm n_1) d1_lt h_lhs d1_pos
  rw [← h_rhs_term]
  exact h_aux.symm
}

/--
Layman's terms: If a state repeats itself, and the sequence doesn't hit any zeros,
the sequence is forced into a repeating loop (periodicity). It will continue to
generate the exact same pattern forever as long as no zeros break the cycle.
-/
lemma local_forward_periodicity_left (B n_1 n_2 K : ℕ)
    (h_eq : vanEckState n_1 B = vanEckState n_2 B)
    (hn1_ge : B ≤ n_1) (hn2_ge : B ≤ n_2)
    (hb0 : B > 0)
    (hd1_lt : ∀ k ≤ K, vanEckNthTerm (n_1 + k) < B)
    (hd1_pos : ∀ k ≤ K, vanEckNthTerm (n_1 + k) > 0) :
    ∀ k ≤ K, vanEckState (n_1 + k) B = vanEckState (n_2 + k) B ∧
      vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k) := by {
  intro k
  induction k with
  | zero =>
    intro _
    constructor
    · have h1 : n_1 + 0 = n_1 := rfl
      have h2 : n_2 + 0 = n_2 := rfl
      rw [h1, h2]
      exact h_eq
    · have h1 : n_1 + 0 = n_1 := rfl
      have h2 : n_2 + 0 = n_2 := rfl
      rw [h1, h2]
      exact local_sequence_determinism_succ_left B n_1 n_2 h_eq hn1_ge hn2_ge hb0 (hd1_lt 0 (Nat.zero_le K)) (hd1_pos 0 (Nat.zero_le K))
  | succ k ih =>
    intro hk
    have h_k_le : k ≤ K := Nat.le_of_succ_le hk
    rcases ih h_k_le with ⟨ih_state, ih_term⟩
    have hk1 : n_1 + (k + 1) = (n_1 + k) + 1 := rfl
    have hk2 : n_2 + (k + 1) = (n_2 + k) + 1 := rfl
    rw [hk1, hk2]

    have h_s1 := vanEckState_succ (n_1 + k) B (Nat.le_trans hn1_ge (Nat.le_add_right n_1 k)) hb0
    have h_s2 := vanEckState_succ (n_2 + k) B (Nat.le_trans hn2_ge (Nat.le_add_right n_2 k)) hb0

    have h_next_state : vanEckState ((n_1 + k) + 1) B = vanEckState ((n_2 + k) + 1) B := by
      rw [h_s1, h_s2, ih_state, ih_term]

    constructor
    · exact h_next_state
    · apply local_sequence_determinism_succ_left B ((n_1 + k) + 1) ((n_2 + k) + 1) h_next_state
      · exact Nat.le_succ_of_le (Nat.le_trans hn1_ge (Nat.le_add_right n_1 k))
      · exact Nat.le_succ_of_le (Nat.le_trans hn2_ge (Nat.le_add_right n_2 k))
      · exact hb0
      · have hh1 : (n_1 + k) + 1 = n_1 + (k + 1) := rfl
        rw [hh1]
        exact hd1_lt (k + 1) hk
      · have hh1 : (n_1 + k) + 1 = n_1 + (k + 1) := rfl
        rw [hh1]
        exact hd1_pos (k + 1) hk
}

lemma gap_bounded_by_pigeonhole (N G : ℕ) (hN_ge : N ≥ 2)
    (h_nonzero : ∀ k, N ≤ k → k < N + G → vanEckNthTerm k ≠ 0)
    (h_end_zero : vanEckNthTerm (N + G) = 0) :
    G < (vanEckPrefixMax N + 1) ^ (vanEckPrefixMax N + 1) + (vanEckPrefixMax N + 1) + 2 := by {
  by_contra h_ge
  have h_G_large : G ≥ (vanEckPrefixMax N + 1) ^ (vanEckPrefixMax N + 1) + (vanEckPrefixMax N + 1) + 2 := Nat.le_of_not_lt h_ge

  let M := vanEckPrefixMax N
  let B := M + 1
  have hb0 : B > 0 := Nat.zero_lt_succ M
  have hB_gt : B > 1 := by
    have hM : M ≥ vanEckNthTerm 2 := vanEckNthTerm_le_prefixMax N 2 hN_ge
    have h2 : vanEckNthTerm 2 = 1 := rfl
    rw [h2] at hM
    exact Nat.succ_lt_succ hM

  have h_bound : ∀ k, N ≤ k → k < N + G - 1 → vanEckNthTerm k < B := by
    intro k hk_ge hk_lt
    have hz : ∀ j, N < j → j < N + G → vanEckNthTerm j ≠ 0 := fun j hj_ge hj_lt => h_nonzero j (Nat.le_of_lt hj_ge) hj_lt
    have h_pos : N + G > 0 := Nat.lt_of_lt_of_le (Nat.lt_trans (by decide) hN_ge) (Nat.le_add_right N G)
    have h_k_lt2 : k < N + G - 1 := hk_lt
    have h1 : vanEckNthTerm k ≤ M := gap_contains_all_terms N G hz k h_k_lt2
    exact Nat.lt_succ_of_le h1

  have h_coll := local_pigeonhole_state_collision N G B h_bound hB_gt h_G_large
  rcases h_coll with ⟨n_1, n_2, hn1_ge, hn1_lt_n2, hn2_lt, h_eq⟩

  have h_NG_minus_2 : N + G ≥ 2 := Nat.le_trans hN_ge (Nat.le_add_right N G)

  let K := N + G - 1 - n_2
  have h_n2_K : n_2 + K = N + G - 1 := by
    have h_n2_le : n_2 ≤ N + G - 1 := Nat.le_of_lt hn2_lt
    exact Nat.add_sub_cancel' h_n2_le

  have hd1_lt : ∀ k ≤ K, vanEckNthTerm (n_1 + k) < B := by
    intro k hk
    have h_lt : n_1 + k < N + G - 1 := by
      calc n_1 + k < n_2 + k := Nat.add_lt_add_right hn1_lt_n2 k
           _ ≤ n_2 + K := Nat.add_le_add_left hk n_2
           _ = N + G - 1 := h_n2_K
    have h_ge : N ≤ n_1 + k := by
      calc N ≤ N + B := Nat.le_add_right N B
           _ ≤ n_1 := hn1_ge
           _ ≤ n_1 + k := Nat.le_add_right n_1 k
    have hz : ∀ j, N < j → j < N + G → vanEckNthTerm j ≠ 0 := fun j hj_ge hj_lt => h_nonzero j (Nat.le_of_lt hj_ge) hj_lt
    have h1 : vanEckNthTerm (n_1 + k) ≤ M := gap_contains_all_terms N G hz (n_1 + k) h_lt
    exact Nat.lt_succ_of_le h1

  have hd1_pos : ∀ k ≤ K, vanEckNthTerm (n_1 + k) > 0 := by
    intro k hk
    have h_lt : n_1 + k < N + G - 1 := by
      calc n_1 + k < n_2 + k := Nat.add_lt_add_right hn1_lt_n2 k
           _ ≤ n_2 + K := Nat.add_le_add_left hk n_2
           _ = N + G - 1 := h_n2_K
    have h_ge : N ≤ n_1 + k := by
      calc N ≤ N + B := Nat.le_add_right N B
           _ ≤ n_1 := hn1_ge
           _ ≤ n_1 + k := Nat.le_add_right n_1 k
    have h_lt_G : n_1 + k < N + G := Nat.lt_of_lt_of_le h_lt (Nat.sub_le (N + G) 1)
    have hz : vanEckNthTerm (n_1 + k) ≠ 0 := h_nonzero (n_1 + k) h_ge h_lt_G
    exact Nat.pos_of_ne_zero hz

  have h_per := local_forward_periodicity_left B n_1 n_2 K h_eq (Nat.le_trans (Nat.le_add_left B N) hn1_ge) (Nat.le_trans (Nat.le_add_left B N) (Nat.le_trans hn1_ge (Nat.le_of_lt hn1_lt_n2))) hb0 hd1_lt hd1_pos

  have h_term_eq := (h_per K (Nat.le_refl K)).right
  rw [h_n2_K] at h_term_eq

  have h_contra_lt : n_1 + K < N + G - 1 := by
    calc n_1 + K < n_2 + K := Nat.add_lt_add_right hn1_lt_n2 K
         _ = N + G - 1 := h_n2_K

  have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new (N + G - 2)
  have h_sub_add : N + G - 2 + 2 = N + G := Nat.sub_add_cancel h_NG_minus_2
  rw [h_sub_add] at h_iff
  have h_new := h_iff.mp h_end_zero

  have h_sub_add1 : N + G - 2 + 1 = N + G - 1 := by
    have h1 : N + G - 1 ≥ 1 := by
      have h : N + G ≥ 2 := Nat.le_trans hN_ge (Nat.le_add_right N G)
      exact Nat.le_sub_one_of_lt h
    exact Nat.sub_add_cancel h1
  rw [h_sub_add1] at h_new

  have h_not_eq := h_new (n_1 + K) h_contra_lt
  exact h_not_eq h_term_eq
}

/--
A structural definition of "Dense" for the Van Eck sequence.
A finite set of small numbers (bounded by B) is considered dense if they occur
in contiguous blocks of length at least G infinitely often.
-/
def DenseSmallNumbers (B G : ℕ) : Prop :=
  ∀ N, ∃ start > N, ∀ i < G, vanEckNthTerm (start + i) ≤ B

/--
Stepping Stone for Dense Collisions:
If a dense block of small numbers contains no 2s, it is completely forbidden
from containing any alternating pairs (x, y, x). This means the density is
mathematically compressed without the ability to form distance-2 collisions.
-/
lemma dense_block_without_twos_has_no_alternating_pairs (B G start : ℕ)
    (h_dense : ∀ i < G, vanEckNthTerm (start + i) ≤ B)
    (h_no_twos : ∀ m > start, vanEckNthTerm m ≠ 2) :
    ∀ k, k + 2 < G → vanEckNthTerm (start + k) ≠ vanEckNthTerm (start + k + 2) := by {
  intro k hk_lt h_eq
  let i := start + k
  have h_eq_i : vanEckNthTerm i = vanEckNthTerm (i + 2) := h_eq

  by_cases h_eq1 : vanEckNthTerm (i + 1) = vanEckNthTerm (i + 2)
  · -- Triple case: x, x, x
    have h_trip : vanEckNthTerm i = vanEckNthTerm (i + 2) ∧ vanEckNthTerm (i + 1) = vanEckNthTerm (i + 2) ∧ vanEckNthTerm (i + 2) = vanEckNthTerm (i + 2) := ⟨h_eq_i, h_eq1, rfl⟩
    have hc := vanEck_triple_impossible i (vanEckNthTerm (i + 2))
    exact hc h_trip
  · -- Gap is exactly 2. We prove vanEckNthTerm (i + 3) = 2.
    have hd_2 : vanEckNthTerm (i + 3) = 2 := by
      have hpos : 0 < i + 3 := Nat.zero_lt_succ _
      have hm := vanEck_term_is_matchSearch (i + 3) hpos
      have hsub : i + 3 - 1 = i + 2 := rfl
      rw [hsub] at hm

      have hlen : (vanEck (i + 2)).length = i + 3 := vanEckLength (i + 2)

      have hd_2_list : listNth (vanEck (i + 2)) (i + 2) = vanEckNthTerm (i + 2) := by
        exact VanEck_deterministic (i + 2) (i + 2) (Nat.le_refl _)
      have hd_1_list : listNth (vanEck (i + 2)) (i + 1) = vanEckNthTerm (i + 1) := by
        exact VanEck_deterministic (i + 2) (i + 1) (Nat.le_succ _)
      have hd_0_list : listNth (vanEck (i + 2)) i = vanEckNthTerm i := by
        exact VanEck_deterministic (i + 2) i (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))

      have hsub2 : i + 3 - 1 = i + 2 := rfl

      -- first iteration of matchSearch
      have h_ite_1 : matchSearch (vanEck (i + 2)) (i + 2) = matchSearch (vanEck (i + 2)) (i + 1) := by
        have h_neq2 : listNth (vanEck (i + 2)) ((vanEck (i + 2)).length - 1) ≠ listNth (vanEck (i + 2)) (i + 1) := by
          rw [hlen, hsub2, hd_2_list, hd_1_list]
          intro hc
          exact h_eq1 hc.symm
        have h_ff := matchSearch_ite_ff (vanEck (i + 2)) (i + 1) h_neq2
        have hi2 : i + 1 + 1 = i + 2 := rfl
        rw [hi2] at h_ff
        exact h_ff

      -- second iteration of matchSearch
      have h_ite_2 : matchSearch (vanEck (i + 2)) (i + 1) = 2 := by
        have h_eq2 : listNth (vanEck (i + 2)) ((vanEck (i + 2)).length - 1) = listNth (vanEck (i + 2)) i := by
          rw [hlen, hsub2, hd_2_list, hd_0_list]
          exact h_eq_i.symm
        have h_tt := matchSearch_ite_tt (vanEck (i + 2)) i h_eq2
        have hi1 : i + 1 = i + 1 := rfl
        rw [hi1] at h_tt
        rw [h_tt, hlen, hsub2]
        exact Nat.add_sub_cancel_left i 2

      rw [h_ite_1, h_ite_2] at hm
      exact hm

    have h_contra := h_no_twos (i + 3) (by
      have h1 : start ≤ i := Nat.le_add_right start k
      have h2 : i < i + 3 := Nat.lt_add_of_pos_right (by decide)
      exact Nat.lt_of_le_of_lt h1 h2
    )
    exact h_contra hd_2
}

/--
If a dense block is periodic and evaluates its own positive bounded gaps
without any occurrences of 2, the graph structure of the sequence
cycles breaks and mathematically evaluates to False.
-/
lemma matchSearch_upper_bound_of_match (L : List ℕ) (n : ℕ) (start : ℕ)
  (h_match : listNth L (L.length - 1) = listNth L start)
  (h_start_lt : start < n) :
  matchSearch L n ≤ L.length - 1 - start := by {
  induction n with
  | zero => contradiction
  | succ n ih =>
    by_cases h : listNth L (L.length - 1) = listNth L n
    · rw [matchSearch_ite_tt L n h]
      have h1 : start ≤ n := Nat.le_of_lt_succ h_start_lt
      exact Nat.sub_le_sub_left h1 (L.length - 1)
    · rw [matchSearch_ite_ff L n h]
      have h1 : start < n := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ h_start_lt) (by
        intro heq
        rw [heq] at h_match
        exact h h_match
      )
      exact ih h1
}

lemma mod_eq_cases (A B P : ℕ) (hA : A < 2 * P) (hB : B < 2 * P) (hc : A % P = B % P) :
    A = B ∨ A + P = B ∨ B + P = A := by {
  have h2P : 2 * P = P + P := Nat.two_mul P
  rw [h2P] at hA hB
  by_cases hA_lt : A < P
  · have hA_mod : A % P = A := Nat.mod_eq_of_lt hA_lt
    by_cases hB_lt : B < P
    · have hB_mod : B % P = B := Nat.mod_eq_of_lt hB_lt
      rw [hA_mod, hB_mod] at hc
      left; exact hc
    · push Not at hB_lt
      have h1 : B - P < P := Nat.sub_lt_left_of_lt_add hB_lt hB
      have hB_mod : B % P = B - P := by {
        have hB_add : B = B - P + P := (Nat.sub_add_cancel hB_lt).symm
        nth_rw 1 [hB_add]
        have h_add := Nat.add_mod_right (B - P) P
        rw [Nat.mod_eq_of_lt h1] at h_add
        exact h_add
      }
      rw [hA_mod, hB_mod] at hc
      right; left
      have h_eq : A = B - P := hc
      rw [h_eq]
      exact Nat.sub_add_cancel hB_lt
  · push Not at hA_lt
    have h1 : A - P < P := Nat.sub_lt_left_of_lt_add hA_lt hA
    have hA_mod : A % P = A - P := by {
      have hA_add : A = A - P + P := (Nat.sub_add_cancel hA_lt).symm
      nth_rw 1 [hA_add]
      have h_add := Nat.add_mod_right (A - P) P
      rw [Nat.mod_eq_of_lt h1] at h_add
      exact h_add
    }
    by_cases hB_lt : B < P
    · have hB_mod : B % P = B := Nat.mod_eq_of_lt hB_lt
      rw [hA_mod, hB_mod] at hc
      right; right
      have h_eq : A - P = B := hc
      rw [← h_eq]
      exact Nat.sub_add_cancel hA_lt
    · push Not at hB_lt
      have h2 : B - P < P := Nat.sub_lt_left_of_lt_add hB_lt hB
      have hB_mod : B % P = B - P := by {
        have hB_add : B = B - P + P := (Nat.sub_add_cancel hB_lt).symm
        nth_rw 1 [hB_add]
        have h_add := Nat.add_mod_right (B - P) P
        rw [Nat.mod_eq_of_lt h2] at h_add
        exact h_add
      }
      rw [hA_mod, hB_mod] at hc
      left
      have h_eq : A - P = B - P := hc
      have hA_ge : P ≤ A := hA_lt
      have hB_ge : P ≤ B := hB_lt
      calc A = A - P + P := (Nat.sub_add_cancel hA_ge).symm
           _ = B - P + P := by rw [h_eq]
           _ = B := Nat.sub_add_cancel hB_ge
}

lemma fin_sum_mod_P_multiple (P : ℕ) (hP : P > 0) (v : Fin P → ℕ) 
    (hv1 : ∀ k, 1 ≤ v k) (hvP : ∀ k, v k ≤ P)
    (f : Fin P → Fin P)
    (hf : ∀ k, (f k).val = (k.val + 1 + P - v k) % P)
    (hbij : Function.Bijective f) :
    ∃ C : ℕ, ∑ k : Fin P, v k = C * P := by {
  have h_sum_f : ∑ k : Fin P, (f k).val = ∑ k : Fin P, k.val := by
    have heq : ∑ k : Fin P, (f k).val = ∑ k : Fin P, (fun x => x.val) (f k) := rfl
    rw [heq]
    exact Equiv.sum_comp (Equiv.ofBijective f hbij) (fun k => k.val)

  let d := fun (k : Fin P) => (k.val + 1 + P - v k) / P

  have h_div_mod : ∀ k, (k.val + 1 + P - v k) = P * d k + (f k).val := by {
    intro k
    have h_mod := Nat.div_add_mod (k.val + 1 + P - v k) P
    have hfk := hf k
    have hd_def : d k = (k.val + 1 + P - v k) / P := rfl
    rw [hfk, hd_def]
    exact h_mod.symm
  }

  have h_sum1 : ∑ k : Fin P, (k.val + 1 + P - v k) = ∑ k : Fin P, (P * d k + (f k).val) := by {
    apply Finset.sum_congr rfl
    intro x _
    exact h_div_mod x
  }

  have h_sum_left : ∑ k : Fin P, (k.val + 1 + P - v k) + ∑ k : Fin P, v k = ∑ k : Fin P, (k.val + 1 + P) := by {
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    have h2 := hvP x
    have h3 : v x ≤ x.val + 1 + P := by
      have h_le : 1 + P ≤ x.val + 1 + P := by
        rw [Nat.add_assoc]
        exact Nat.le_add_left (1 + P) x.val
      exact le_trans (le_trans h2 (Nat.le_add_left P 1)) h_le
    exact Nat.sub_add_cancel h3
  }

  have h_sum_right : ∑ k : Fin P, (P * d k + (f k).val) = P * ∑ k : Fin P, d k + ∑ k : Fin P, (f k).val := by {
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  }

  have h_sum_1P : ∑ k : Fin P, (k.val + 1 + P) = ∑ k : Fin P, k.val + P * (P + 1) := by {
    have h1 : ∑ k : Fin P, (k.val + 1 + P) = ∑ k : Fin P, k.val + ∑ k : Fin P, (1 + P) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [Nat.add_assoc]
    rw [h1]
    have h2 : ∑ k : Fin P, (1 + P) = P * (P + 1) := by
      have hz : ∑ k : Fin P, (1 + P) = (Finset.card (Finset.univ : Finset (Fin P))) * (1 + P) := by
        exact Finset.sum_const (1 + P)
      have hc : Finset.card (Finset.univ : Finset (Fin P)) = P := Fintype.card_fin P
      rw [hc] at hz
      rw [hz]
      ring
    rw [h2]
  }

  have h_eq1 : ∑ k : Fin P, (k.val + 1 + P - v k) = P * ∑ k : Fin P, d k + ∑ k : Fin P, k.val := by {
    rw [h_sum1, h_sum_right, h_sum_f]
  }

  have h_eq2 : P * ∑ k : Fin P, d k + ∑ k : Fin P, k.val + ∑ k : Fin P, v k = ∑ k : Fin P, k.val + P * (P + 1) := by {
    have hr : P * ∑ k : Fin P, d k + ∑ k : Fin P, k.val + ∑ k : Fin P, v k = ∑ k : Fin P, (k.val + 1 + P - v k) + ∑ k : Fin P, v k := by rw [h_eq1]
    rw [hr, h_sum_left]
    exact h_sum_1P
  }

  have h_eq3 : (∑ k : Fin P, k.val) + (P * ∑ k : Fin P, d k + ∑ k : Fin P, v k) = (∑ k : Fin P, k.val) + P * (P + 1) := by {
    have hr : (∑ k : Fin P, k.val) + (P * ∑ k : Fin P, d k + ∑ k : Fin P, v k) = P * ∑ k : Fin P, d k + ∑ k : Fin P, k.val + ∑ k : Fin P, v k := by
      calc
        (∑ k : Fin P, k.val) + (P * ∑ k : Fin P, d k + ∑ k : Fin P, v k) 
          = ((∑ k : Fin P, k.val) + P * ∑ k : Fin P, d k) + ∑ k : Fin P, v k := by rw [Nat.add_assoc]
        _ = (P * ∑ k : Fin P, d k + (∑ k : Fin P, k.val)) + ∑ k : Fin P, v k := by rw [Nat.add_comm (∑ k : Fin P, k.val) (P * ∑ k : Fin P, d k)]
    rw [hr]
    exact h_eq2
  }

  have h_eq4 : P * ∑ k : Fin P, d k + ∑ k : Fin P, v k = P * (P + 1) := Nat.add_left_cancel h_eq3

  have h_eq5 : ∑ k : Fin P, v k = P * (P + 1) - P * ∑ k : Fin P, d k := by {
    exact Nat.eq_sub_of_add_eq' h_eq4
  }

  have h_eq6 : ∑ k : Fin P, v k = ((P + 1) - ∑ k : Fin P, d k) * P := by {
    rw [h_eq5]
    have hz : P * (P + 1) - P * ∑ k : Fin P, d k = P * ((P + 1) - ∑ k : Fin P, d k) := by
      exact (Nat.mul_sub_left_distrib P (P + 1) (∑ k : Fin P, d k)).symm
    rw [hz]
    ring
  }

  exact ⟨((P + 1) - ∑ k : Fin P, d k), h_eq6⟩
}lemma fin_sum_three {n : ℕ} (hn : n = 3) (f : Fin n → ℕ) :
  ∑ k : Fin n, f k = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ := by {
  subst hn
  exact Fin.sum_univ_three f
}

lemma period_three_forces_all_threes (a b c C : ℕ)
  (ha13 : a = 1 ∨ a = 3)
  (hb13 : b = 1 ∨ b = 3)
  (hc13 : c = 1 ∨ c = 3)
  (hC2 : C ≥ 2)
  (h_sum : a + b + c = C * 3) : a = 3 ∧ b = 3 ∧ c = 3 := by {
  have ha_eq : a = 3 := by {
    rcases ha13 with rfl | rfl <;> rcases hb13 with rfl | rfl <;> rcases hc13 with rfl | rfl <;> omega
  }
  have hb_eq : b = 3 := by {
    rcases ha13 with rfl | rfl <;> rcases hb13 with rfl | rfl <;> rcases hc13 with rfl | rfl <;> omega
  }
  have hc_eq : c = 3 := by {
    rcases ha13 with rfl | rfl <;> rcases hb13 with rfl | rfl <;> rcases hc13 with rfl | rfl <;> omega
  }
  exact ⟨ha_eq, hb_eq, hc_eq⟩
}

--
lemma finite_cycle_gap_collapse (n_1 n_2 K : ℕ)
    (hn1_lt_n2 : n_1 < n_2)
    (h_K_large : K ≥ n_2 - n_1 + 3)
    (h_no_zero : ∀ k, 1 ≤ k → k ≤ K → vanEckNthTerm (n_2 + k) ≠ 0)
    (h_no_twos : ∀ m > n_1, vanEckNthTerm m ≠ 2)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k)) : False := by {
  -- The user requested we attempt induction on K or n_2 and write the edge-sum deductions,
  -- summarizing where we get stuck.
  let P := n_2 - n_1
  have h_P_pos : P ≥ 1 := Nat.sub_pos_of_lt hn1_lt_n2

  -- We proceed by induction on the evaluation length K.
  -- To capture the sum of edges, we would define a Finset sum over the period.
  -- Since we need to prove False, we can extract the local properties first.

  -- 1. Bound the values: every gap is bounded by P.
  have h_val_le_P : ∀ k, 1 ≤ k → k ≤ K → vanEckNthTerm (n_2 + k) ≤ P := by {
    intro k hk1 hkK
    have h_gap := vanEck_term_is_matchSearch (n_2 + k) (Nat.le_trans hk1 (Nat.le_add_left k n_2))
    rw [h_gap]

    have h_match : listNth (vanEck (n_2 + k - 1)) ((vanEck (n_2 + k - 1)).length - 1) =
                   listNth (vanEck (n_2 + k - 1)) (n_1 + k - 1) := by {
      have hl : (vanEck (n_2 + k - 1)).length = n_2 + k := by {
        have hlen := vanEckLength (n_2 + k - 1)
        have h_sub_add : n_2 + k - 1 + 1 = n_2 + k := Nat.sub_add_cancel (Nat.le_trans hk1 (Nat.le_add_left k n_2))
        rw [h_sub_add] at hlen
        exact hlen
      }
      have hl_sub_1 : (vanEck (n_2 + k - 1)).length - 1 = n_2 + k - 1 := by rw [hl]
      rw [hl_sub_1]
      have h_left : listNth (vanEck (n_2 + k - 1)) (n_2 + k - 1) = vanEckNthTerm (n_2 + k - 1) := rfl
      have h_right : listNth (vanEck (n_2 + k - 1)) (n_1 + k - 1) = vanEckNthTerm (n_1 + k - 1) := by {
        apply VanEck_deterministic (n_2 + k - 1) (n_1 + k - 1)
        have h1 : n_1 + k ≤ n_2 + k := Nat.add_le_add_right (Nat.le_of_lt hn1_lt_n2) k
        exact Nat.sub_le_sub_right h1 1
      }
      rw [h_left, h_right]
      have h_k_sub : k - 1 ≤ K := Nat.le_trans (Nat.sub_le k 1) hkK
      have hs1 : n_2 + k - 1 = n_2 + (k - 1) := Nat.add_sub_assoc hk1 n_2
      have hs2 : n_1 + k - 1 = n_1 + (k - 1) := Nat.add_sub_assoc hk1 n_1
      rw [hs1, hs2]
      exact (h_per (k - 1) h_k_sub).symm
    }

    have h_start_lt : n_1 + k - 1 < n_2 + k - 1 := by {
      have hs1 : n_1 + k - 1 = n_1 + (k - 1) := Nat.add_sub_assoc hk1 n_1
      have hs2 : n_2 + k - 1 = n_2 + (k - 1) := Nat.add_sub_assoc hk1 n_2
      rw [hs1, hs2]
      exact Nat.add_lt_add_right hn1_lt_n2 (k - 1)
    }

    have h_bound := matchSearch_upper_bound_of_match (vanEck (n_2 + k - 1)) (n_2 + k - 1) (n_1 + k - 1) h_match h_start_lt

    have hl : (vanEck (n_2 + k - 1)).length = n_2 + k := by {
      have hlen := vanEckLength (n_2 + k - 1)
      have h_sub_add : n_2 + k - 1 + 1 = n_2 + k := Nat.sub_add_cancel (Nat.le_trans hk1 (Nat.le_add_left k n_2))
      rw [h_sub_add] at hlen
      exact hlen
    }
    have hl_sub_1 : (vanEck (n_2 + k - 1)).length - 1 = n_2 + k - 1 := by rw [hl]
    rw [hl_sub_1] at h_bound

    have h_sub : n_2 + k - 1 - (n_1 + k - 1) = P := by {
      have hs1 : n_2 + k - 1 = n_2 + (k - 1) := Nat.add_sub_assoc hk1 n_2
      have hs2 : n_1 + k - 1 = n_1 + (k - 1) := Nat.add_sub_assoc hk1 n_1
      rw [hs1, hs2]
      have hs3 : n_2 + (k - 1) - (n_1 + (k - 1)) = n_2 - n_1 := Nat.add_sub_add_right n_2 (k - 1) n_1
      rw [hs3]
    }
    rw [h_sub] at h_bound
    exact h_bound
  }

  -- 2. No alternating pairs implies gaps cannot be 2.
  -- 3. We construct the graph map f(k) = k - v(n_2+k).

  -- To get past Stuck point 1, we must formalize the Graph Permutation.
  -- We define f(k) = (k - v(n_2+k)) % P for k ∈ {1..P}.
  -- Stuck subpoint 1a: f(k) is well-defined and bounded, already proven above as h_val_le_P!

  -- Stuck subpoint 1b: Proving f(k) is injective modulo P.
  have f_inj : ∀ i j, 1 ≤ i → i ≤ P → 1 ≤ j → j ≤ P → i < j →
      (i + P - vanEckNthTerm (n_2 + i)) % P ≠ (j + P - vanEckNthTerm (n_2 + j)) % P := by {
    intro i j hi1 hiP hj1 hjP hij hc

    have h_P_le_K : P ≤ K := by
      calc P ≤ P + 3 := Nat.le_add_right P 3
           _ = n_2 - n_1 + 3 := rfl
           _ ≤ K := h_K_large
    have hiK : i ≤ K := Nat.le_trans hiP h_P_le_K
    have hjK : j ≤ K := Nat.le_trans hjP h_P_le_K

    have h_vi_le := h_val_le_P i hi1 hiK
    have h_vj_le := h_val_le_P j hj1 hjK
    have h_vi_pos : vanEckNthTerm (n_2 + i) > 0 := Nat.pos_of_ne_zero (h_no_zero i hi1 hiK)
    have h_vj_pos : vanEckNthTerm (n_2 + j) > 0 := Nat.pos_of_ne_zero (h_no_zero j hj1 hjK)

    let A := i + P - vanEckNthTerm (n_2 + i)
    let B := j + P - vanEckNthTerm (n_2 + j)

    have hA_lt : A < 2 * P := by {
      change i + P - vanEckNthTerm (n_2 + i) < 2 * P
      have h_iP_le : i + P ≤ 2 * P := by
        have h2 : 2 * P = P + P := Nat.two_mul P
        rw [h2]
        exact Nat.add_le_add_right hiP P
      have h_sub_lt : i + P - vanEckNthTerm (n_2 + i) < i + P := Nat.sub_lt (by
        calc 0 < i := hi1
             _ ≤ i + P := Nat.le_add_right i P
      ) h_vi_pos
      exact Nat.lt_of_lt_of_le h_sub_lt h_iP_le
    }
    have hB_lt : B < 2 * P := by {
      change j + P - vanEckNthTerm (n_2 + j) < 2 * P
      have h_jP_le : j + P ≤ 2 * P := by
        have h2 : 2 * P = P + P := Nat.two_mul P
        rw [h2]
        exact Nat.add_le_add_right hjP P
      have h_sub_lt : j + P - vanEckNthTerm (n_2 + j) < j + P := Nat.sub_lt (by
        calc 0 < j := hj1
             _ ≤ j + P := Nat.le_add_right j P
      ) h_vj_pos
      exact Nat.lt_of_lt_of_le h_sub_lt h_jP_le
    }

    have h_cases := mod_eq_cases A B P hA_lt hB_lt hc

    rcases h_cases with h1 | h2 | h3
    · -- Case m = 0: n_2+i - v(n_2+i) = n_2+j - v(n_2+j).
      --   This directly contradicts `vanEck_idx_sub_val_unique`!
      have heq : n_2 + i - vanEckNthTerm (n_2 + i) = n_2 + j - vanEckNthTerm (n_2 + j) := by {
        change i + P - vanEckNthTerm (n_2 + i) = j + P - vanEckNthTerm (n_2 + j) at h1
        have hn1_le : n_1 ≤ n_2 := Nat.le_of_lt hn1_lt_n2
        have h_n2_i : n_2 + i = i + P + n_1 := by
          calc n_2 + i = i + n_2 := Nat.add_comm n_2 i
               _ = i + (P + n_1) := by
                 have h_P : P = n_2 - n_1 := rfl
                 rw [h_P, Nat.sub_add_cancel hn1_le]
               _ = i + P + n_1 := (Nat.add_assoc i P n_1).symm
        have h_n2_j : n_2 + j = j + P + n_1 := by
          calc n_2 + j = j + n_2 := Nat.add_comm n_2 j
               _ = j + (P + n_1) := by
                 have h_P : P = n_2 - n_1 := rfl
                 rw [h_P, Nat.sub_add_cancel hn1_le]
               _ = j + P + n_1 := (Nat.add_assoc j P n_1).symm
        have h_vi_le_add : vanEckNthTerm (n_2 + i) ≤ i + P := Nat.le_trans h_vi_le (Nat.le_add_left P i)
        have h_vj_le_add : vanEckNthTerm (n_2 + j) ≤ j + P := Nat.le_trans h_vj_le (Nat.le_add_left P j)
        have h_i_sub_add : i + P - vanEckNthTerm (n_2 + i) + n_1 = i + P + n_1 - vanEckNthTerm (n_2 + i) := (Nat.sub_add_comm h_vi_le_add).symm
        have h_j_sub_add : j + P - vanEckNthTerm (n_2 + j) + n_1 = j + P + n_1 - vanEckNthTerm (n_2 + j) := (Nat.sub_add_comm h_vj_le_add).symm
        have h_eq1 : i + P - vanEckNthTerm (n_2 + i) + n_1 = j + P - vanEckNthTerm (n_2 + j) + n_1 := congrArg (· + n_1) h1
        rw [h_i_sub_add, h_j_sub_add] at h_eq1
        rw [← h_n2_i, ← h_n2_j] at h_eq1
        exact h_eq1
      }
      have h_unique_lt : n_2 + i < n_2 + j := Nat.add_lt_add_left hij n_2
      have h_unique := vanEck_idx_sub_val_unique (n_2 + i) (n_2 + j) h_vi_pos h_unique_lt
      exact h_unique heq
    · -- Case m = 1: i - v(n_2+i) = j - v(n_2+j) + P.
      --   Then n_2+i - v(n_2+i) = n_2+j - P - v(n_2+j) = n_1+j - v(n_1+j) (since v(n_2+j) = v(n_1+j)).
      --   This means `idx - v(idx)` is the same for `idx1 = n_2+i` and `idx2 = n_1+j`.
      --   Since i < j ≤ P, n_2+i ≠ n_1+j. This contradicts `vanEck_idx_sub_val_unique`!
      have heq : n_2 + i - vanEckNthTerm (n_2 + i) = n_1 + j - vanEckNthTerm (n_1 + j) := by {
        change i + P - vanEckNthTerm (n_2 + i) + P = j + P - vanEckNthTerm (n_2 + j) at h2
        have h_P : P = n_2 - n_1 := rfl
        have hn1_le : n_1 ≤ n_2 := Nat.le_of_lt hn1_lt_n2
        have h_vj_le_add : vanEckNthTerm (n_2 + j) ≤ j := by
          have h_P_le : P ≤ j + P - vanEckNthTerm (n_2 + j) := by
            rw [← h2]
            exact Nat.le_add_left P (i + P - vanEckNthTerm (n_2 + i))
          have h_add_le := Nat.add_le_add_right h_P_le (vanEckNthTerm (n_2 + j))
          have h_add_le2 : vanEckNthTerm (n_2 + j) + P ≤ j + P := by
            calc vanEckNthTerm (n_2 + j) + P = P + vanEckNthTerm (n_2 + j) := Nat.add_comm _ P
                 _ ≤ j + P - vanEckNthTerm (n_2 + j) + vanEckNthTerm (n_2 + j) := h_add_le
                 _ = j + P := Nat.sub_add_cancel (Nat.le_trans h_vj_le (Nat.le_add_left P j))
          exact Nat.le_of_add_le_add_right h_add_le2
        have h_vj_le_add2 : vanEckNthTerm (n_2 + j) ≤ n_1 + j := Nat.le_trans h_vj_le_add (Nat.le_add_left j n_1)
        have h_vi_le_add : vanEckNthTerm (n_2 + i) ≤ n_2 + i := Nat.le_trans h_vi_le (by
          have h_P_le_n2 : P ≤ n_2 := by rw [h_P]; exact Nat.sub_le n_2 n_1
          exact Nat.le_trans h_P_le_n2 (Nat.le_add_right n_2 i)
        )

        apply Nat.add_right_cancel (m := P)
        have h_left : n_2 + i - vanEckNthTerm (n_2 + i) + P = i + P - vanEckNthTerm (n_2 + i) + n_2 := by
          have h_sum : n_2 + i + P = i + P + n_2 := by rw [Nat.add_assoc, Nat.add_comm n_2 (i + P)]
          calc n_2 + i - vanEckNthTerm (n_2 + i) + P = n_2 + i + P - vanEckNthTerm (n_2 + i) := (Nat.sub_add_comm h_vi_le_add).symm
               _ = i + P + n_2 - vanEckNthTerm (n_2 + i) := by rw [h_sum]
               _ = i + P - vanEckNthTerm (n_2 + i) + n_2 := Nat.sub_add_comm (Nat.le_trans h_vi_le (Nat.le_add_left P i))
        have h_right : n_1 + j - vanEckNthTerm (n_1 + j) + P = j + P - vanEckNthTerm (n_2 + j) + n_1 := by
          have h_vj_eq : vanEckNthTerm (n_1 + j) = vanEckNthTerm (n_2 + j) := h_per j hjK
          rw [h_vj_eq]
          have h_sum : n_1 + j + P = j + P + n_1 := by rw [Nat.add_assoc, Nat.add_comm n_1 (j + P)]
          calc n_1 + j - vanEckNthTerm (n_2 + j) + P = n_1 + j + P - vanEckNthTerm (n_2 + j) := (Nat.sub_add_comm h_vj_le_add2).symm
               _ = j + P + n_1 - vanEckNthTerm (n_2 + j) := by rw [h_sum]
               _ = j + P - vanEckNthTerm (n_2 + j) + n_1 := Nat.sub_add_comm (Nat.le_trans h_vj_le (Nat.le_add_left P j))

        rw [h_left, h_right]
        have h2_add_n1 : i + P - vanEckNthTerm (n_2 + i) + P + n_1 = j + P - vanEckNthTerm (n_2 + j) + n_1 := congrArg (· + n_1) h2
        have hP_add_n1 : P + n_1 = n_2 := by rw [h_P, Nat.sub_add_cancel hn1_le]
        rw [Nat.add_assoc, hP_add_n1] at h2_add_n1
        exact h2_add_n1
      }
      have h_n1j_pos : vanEckNthTerm (n_1 + j) > 0 := by {
        have h_vj_eq : vanEckNthTerm (n_1 + j) = vanEckNthTerm (n_2 + j) := h_per j hjK
        rw [h_vj_eq]
        exact h_vj_pos
      }
      have h_lt : n_1 + j < n_2 + i := by
        calc n_1 + j ≤ n_1 + P := Nat.add_le_add_left hjP n_1
             _ = n_2 := by
               have h_P : P = n_2 - n_1 := rfl
               have hn1_le : n_1 ≤ n_2 := Nat.le_of_lt hn1_lt_n2
               rw [h_P, Nat.add_comm, Nat.sub_add_cancel hn1_le]
             _ < n_2 + i := Nat.lt_add_of_pos_right hi1
      have h_unique := vanEck_idx_sub_val_unique (n_1 + j) (n_2 + i) h_n1j_pos h_lt
      exact h_unique heq.symm
    · -- Case m = -1: i - v(n_2+i) = j - v(n_2+j) - P.
      --   Since v(n_2+i) ≥ 1, LHS ≤ i - 1. Since v(n_2+j) ≤ P, RHS ≥ j - P + P = j.
      --   So i - 1 ≥ j, which contradicts i < j!
      change j + P - vanEckNthTerm (n_2 + j) + P = i + P - vanEckNthTerm (n_2 + i) at h3
      have h_j_le : j + P ≤ j + P - vanEckNthTerm (n_2 + j) + P := by
        calc j + P = j + P - vanEckNthTerm (n_2 + j) + vanEckNthTerm (n_2 + j) := (Nat.sub_add_cancel (Nat.le_trans h_vj_le (Nat.le_add_left P j))).symm
             _ ≤ j + P - vanEckNthTerm (n_2 + j) + P := Nat.add_le_add_left h_vj_le _
      have h_i_lt : i + P - vanEckNthTerm (n_2 + i) < i + P := Nat.sub_lt (by
        calc 0 < vanEckNthTerm (n_2 + i) := h_vi_pos
             _ ≤ P := h_vi_le
             _ ≤ i + P := Nat.le_add_left P i
      ) h_vi_pos
      have h_j_lt_i : j + P < i + P := by
        calc j + P ≤ j + P - vanEckNthTerm (n_2 + j) + P := h_j_le
             _ = i + P - vanEckNthTerm (n_2 + i) := h3
             _ < i + P := h_i_lt
      have h_j_lt_i2 : j < i := Nat.lt_of_add_lt_add_right h_j_lt_i
      exact False.elim (Nat.lt_irrefl i (Nat.lt_trans hij h_j_lt_i2))
  }

  -- Stuck subpoint 1c: Promoting Injection to Bijection.
  let f : Fin P → Fin P := fun k => ⟨(k.val + 1 + P - vanEckNthTerm (n_2 + k.val + 1)) % P, Nat.mod_lt _ (Nat.pos_of_ne_zero (by
    intro h
    have h1 : P ≥ 1 := h_P_pos
    rw [h] at h1
    exact Nat.not_lt_zero 0 h1
  ))⟩

  have f_bij : Function.Bijective f := by {
    have h_inj : Function.Injective f := by {
      intro i j heq
      have h1 : 1 ≤ i.val + 1 := Nat.le_add_left 1 i.val
      have h2 : i.val + 1 ≤ P := i.isLt
      have h3 : 1 ≤ j.val + 1 := Nat.le_add_left 1 j.val
      have h4 : j.val + 1 ≤ P := j.isLt
      by_cases hlt : i.val + 1 < j.val + 1
      · have hc := f_inj (i.val + 1) (j.val + 1) h1 h2 h3 h4 hlt
        have heq_val := congr_arg Fin.val heq
        exact False.elim (hc heq_val)
      · by_cases hlt2 : j.val + 1 < i.val + 1
        · have hc := f_inj (j.val + 1) (i.val + 1) h3 h4 h1 h2 hlt2
          have heq_val := congr_arg Fin.val heq
          exact False.elim (hc heq_val.symm)
        · have heq_val : i.val + 1 = j.val + 1 := by
            have h_not_lt1 : ¬(i.val + 1 < j.val + 1) := hlt
            have h_not_lt2 : ¬(j.val + 1 < i.val + 1) := hlt2
            exact Nat.le_antisymm (Nat.le_of_not_lt h_not_lt2) (Nat.le_of_not_lt h_not_lt1)
          exact Fin.eq_of_val_eq (Nat.add_right_cancel heq_val)
    }
    exact Finite.injective_iff_bijective.mp h_inj
  }


  -- Stuck point 3: The Numeric Contradiction
  -- We would then need to prove V * P = \sum v(n_2+k).
  -- Since we have `h_no_twos` and `h_no_zero`, we know v(n_2+k) ∈ {1} ∪ [3, P].
  -- The only way the average gap can be an integer V without hitting 2 or 0
  -- is if V = 1 (meaning all 1s, which creates alternating pairs) or through
  -- a strictly symmetric permutation of {1, 3} gaps, which contradicts the
  -- sequence's fundamental injection rules.
  -- This entire chain requires ~500-1000 lines of `Finset.sum_bij` and `Finset.sum_partition`
  -- deductions, which Lean 4 struggles with without heavy automation.

  -- We can evaluate the sum of the bijection over the period:
  have h_sum_bij : ∑ k : Fin P, (f k).val = ∑ k : Fin P, k.val := by {
    have heq : ∑ k : Fin P, (f k).val = ∑ k : Fin P, (fun x => x.val) (f k) := rfl
    rw [heq]
    exact Equiv.sum_comp (Equiv.ofBijective f f_bij) (fun k => k.val)
  }

  -- We deploy our omega-powered Finset summation tool!
  let v_fn : Fin P → ℕ := fun k => vanEckNthTerm (n_2 + k.val + 1)
  have hv1 : ∀ k, 1 ≤ v_fn k := by
    intro k
    have hz := h_no_zero (k.val + 1) (Nat.le_add_left 1 k.val) (by
      calc k.val + 1 ≤ P := k.isLt
           _ ≤ P + 3 := Nat.le_add_right P 3
           _ ≤ K := h_K_large
    )
    exact Nat.pos_of_ne_zero hz
  have hvP : ∀ k, v_fn k ≤ P := by
    intro k
    have h1 : 1 ≤ k.val + 1 := Nat.le_add_left 1 k.val
    have h2 : k.val + 1 ≤ K := by
      have hp : P = n_2 - n_1 := rfl
      calc k.val + 1 ≤ P := k.isLt
           _ ≤ P + 3 := Nat.le_add_right P 3
           _ = n_2 - n_1 + 3 := by rw [hp]
           _ ≤ K := h_K_large
    exact h_val_le_P (k.val + 1) h1 h2

  have h_mod_eq : ∀ k : Fin P, (f k).val = (k.val + 1 + P - v_fn k) % P := fun k => rfl

  have h_sum_multiple := fin_sum_mod_P_multiple P h_P_pos v_fn hv1 hvP f h_mod_eq f_bij

  rcases h_sum_multiple with ⟨C, hC⟩

  -- From here, we know ∑ v_k = C * P.
  -- C cannot be 1 (all 1s -> alternating pairs).
  -- C cannot be > 1 without violating the strict distance bijection graph.
  
  -- The full graph-theoretic partition of this sum into unique sequence elements
  -- requires evaluating Finset.sum_fiberwise over the modulo bijections.
  -- Instead, we formally bound C using our step-wise displacement tracking.
  have h_C_ge_1 : C ≥ 1 := by {
    by_contra h_C_lt_1
    have h_C_zero : C = 0 := by omega
    have h_sum_zero : ∑ k : Fin P, v_fn k = 0 := by
      calc ∑ k : Fin P, v_fn k = C * P := hC
           _ = 0 * P := by rw [h_C_zero]
           _ = 0 := Nat.zero_mul P
    
    have h_P_pos2 : 0 < P := h_P_pos
    have h_nonempty : Nonempty (Fin P) := Fin.pos_iff_nonempty.mp h_P_pos2
    have h_v_pos : 0 < ∑ k : Fin P, v_fn k := Finset.sum_pos (fun i _ => hv1 i) Finset.univ_nonempty
    omega
  }

  have h_C_neq_1 : C ≠ 1 := by {
    intro h_C1
    have h_sum_P : ∑ k : Fin P, v_fn k = P := by
      calc ∑ k : Fin P, v_fn k = C * P := hC
           _ = 1 * P := by rw [h_C1]
           _ = P := Nat.one_mul P
    
    have h_sub_sum : ∑ k : Fin P, (v_fn k - 1) = 0 := by {
      have h1 : ∑ k : Fin P, (v_fn k - 1) + ∑ k : Fin P, 1 = ∑ k : Fin P, v_fn k := by {
        rw [← Finset.sum_add_distrib]
        apply Finset.sum_congr rfl
        intro x _
        exact Nat.sub_add_cancel (hv1 x)
      }
      have h2 : ∑ k : Fin P, 1 = P := by {
        have hz : ∑ k : Fin P, 1 = (Finset.card (Finset.univ : Finset (Fin P))) * 1 := Finset.sum_const 1
        have hc : Finset.card (Finset.univ : Finset (Fin P)) = P := Fintype.card_fin P
        omega
      }
      omega
    }
    
    have h_v_all_1 : ∀ k : Fin P, v_fn k = 1 := by {
      intro k
      have hz := Finset.sum_eq_zero_iff.mp h_sub_sum k (Finset.mem_univ k)
      have hk := hv1 k
      omega
    }
    
    have h_v0_1 : vanEckNthTerm (n_2 + 1) = 1 := by {
      have h0 := h_v_all_1 ⟨0, h_P_pos⟩
      exact h0
    }
    
    have h_v1_1 : vanEckNthTerm (n_2 + 2) = 1 := by {
      by_cases hp_eq_1 : P = 1
      · have h_n2_eq : n_2 = n_1 + 1 := by omega
        have hk2 : 2 ≤ K := by omega
        have h_per_2 : vanEckNthTerm (n_1 + 2) = vanEckNthTerm (n_2 + 2) := h_per 2 hk2
        have h_n1_2 : n_1 + 2 = n_2 + 1 := by omega
        rw [h_n1_2] at h_per_2
        rw [← h_per_2]
        exact h_v0_1
      · have h_p_ge_2 : P ≥ 2 := by omega
        have h_v1 := h_v_all_1 ⟨1, h_p_ge_2⟩
        exact h_v1
    }
    
    have h_no_cons := vanEck_no_consecutive_ones (n_2 + 1)
    have h_cons : vanEckNthTerm (n_2 + 1) = 1 ∧ vanEckNthTerm (n_2 + 1 + 1) = 1 := ⟨h_v0_1, h_v1_1⟩
    exact h_no_cons h_cons
  }

  -- C ≥ 2 from h_C_ge_1 and h_C_neq_1.
  have h_C_ge_2 : C ≥ 2 := by {
    have h1 := h_C_ge_1
    have h2 := h_C_neq_1
    omega
  }

  -- The C ≥ 2 contradiction splits by period length P.
  -- For P ≤ 2, periodicity directly forces a gap of 2 or consecutive 1s.
  -- For P ≥ 3, the C analysis combined with no-twos forces structural collapse.

  -- First establish periodicity extends to val(n_1+k) = val(n_2+k) = val(n_1+k+P).
  have h_P_le_K : P ≤ K := by {
    calc P ≤ P + 3 := Nat.le_add_right P 3
         _ = n_2 - n_1 + 3 := rfl
         _ ≤ K := h_K_large
  }

  -- Case P = 1: consecutive equal values → 1s → consecutive 1s.
  by_cases hP1 : P = 1
  · have h_n2 : n_2 = n_1 + 1 := by omega
    have h0 : vanEckNthTerm n_1 = vanEckNthTerm (n_1 + 1) := by {
      have hp0 := h_per 0 (Nat.zero_le K)
      simp at hp0; rw [h_n2] at hp0; exact hp0
    }
    have h1 : vanEckNthTerm (n_1 + 2) = 1 :=
      vanEck_consecutive_eq_implies_next_one n_1 h0
    have h2 : vanEckNthTerm (n_1 + 2) = vanEckNthTerm (n_1 + 3) := by {
      have hp2 := h_per 2 (by omega)
      rw [h_n2] at hp2
      have : n_1 + 1 + 2 = n_1 + 3 := by omega
      rw [this] at hp2; exact hp2
    }
    have h3 : vanEckNthTerm (n_1 + 3) = 1 := by rw [← h2]; exact h1
    have h_cons : vanEckNthTerm (n_1 + 2) = 1 ∧ vanEckNthTerm (n_1 + 2 + 1) = 1 := by {
      constructor; exact h1
      have : n_1 + 2 + 1 = n_1 + 3 := by omega
      rw [this]; exact h3
    }
    exact vanEck_no_consecutive_ones (n_1 + 2) h_cons

  -- Case P = 2: alternating pairs → gap = 2 contradiction.
  · by_cases hP2 : P = 2
    · -- v(n_1+k) = v(n_1+k+2) for all k ≤ K by periodicity.
      have h_alt : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_1 + k + 2) := by {
        intro k hk
        have hp := h_per k hk
        have h_n2 : n_2 = n_1 + 2 := by omega
        rw [h_n2] at hp
        have : n_1 + 2 + k = n_1 + k + 2 := by omega
        rw [this] at hp; exact hp
      }
      -- v(n_1+1) = v(n_1+3). Two sub-cases on v(n_1+2) vs v(n_1+3).
      have h13 := h_alt 1 (by omega)
      have h24 := h_alt 2 (by omega)
      by_cases heq : vanEckNthTerm (n_1 + 2) = vanEckNthTerm (n_1 + 3)
      · -- Consecutive equal at n_1+2, n_1+3 → v(n_1+4) = 1.
        have h_next := vanEck_consecutive_eq_implies_next_one (n_1 + 2) heq
        have h4 : n_1 + 2 + 2 = n_1 + 4 := by omega
        rw [h4] at h_next
        -- v(n_1+2) = v(n_1+4) = 1 by periodicity.
        have hv2_1 : vanEckNthTerm (n_1 + 2) = 1 := by rw [h24]; exact h_next
        have hv3_1 : vanEckNthTerm (n_1 + 3) = 1 := by rw [← heq]; exact hv2_1
        have h_cons : vanEckNthTerm (n_1 + 2) = 1 ∧ vanEckNthTerm (n_1 + 2 + 1) = 1 := by {
          constructor; exact hv2_1
          have : n_1 + 2 + 1 = n_1 + 3 := by omega
          rw [this]; exact hv3_1
        }
        exact vanEck_no_consecutive_ones (n_1 + 2) h_cons
      · -- v(n_1+1) = v(n_1+3) with v(n_1+2) ≠ v(n_1+3).
        -- This is an alternating pair at n_1+1. By the dense_block logic, v(n_1+4) = 2.
        let i := n_1 + 1
        have h_eq_i : vanEckNthTerm i = vanEckNthTerm (i + 2) := by {
          have : i + 2 = n_1 + 3 := by omega
          rw [this]; exact h13
        }
        have h_neq1 : vanEckNthTerm (i + 1) ≠ vanEckNthTerm (i + 2) := by {
          have h1 : i + 1 = n_1 + 2 := by omega
          have h2 : i + 2 = n_1 + 3 := by omega
          rw [h1, h2]; exact heq
        }
        -- Derive v(i+3) = 2 via matchSearch (same argument as dense_block_without_twos).
        have hd_2 : vanEckNthTerm (i + 3) = 2 := by {
          have hpos : 0 < i + 3 := Nat.zero_lt_succ _
          have hm := vanEck_term_is_matchSearch (i + 3) hpos
          have hsub : i + 3 - 1 = i + 2 := rfl
          rw [hsub] at hm
          have hlen : (vanEck (i + 2)).length = i + 3 := vanEckLength (i + 2)
          have hd_2_list : listNth (vanEck (i + 2)) (i + 2) = vanEckNthTerm (i + 2) :=
            VanEck_deterministic (i + 2) (i + 2) (Nat.le_refl _)
          have hd_1_list : listNth (vanEck (i + 2)) (i + 1) = vanEckNthTerm (i + 1) :=
            VanEck_deterministic (i + 2) (i + 1) (Nat.le_succ _)
          have hd_0_list : listNth (vanEck (i + 2)) i = vanEckNthTerm i :=
            VanEck_deterministic (i + 2) i (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
          have hsub2 : i + 3 - 1 = i + 2 := rfl
          have h_ite_1 : matchSearch (vanEck (i + 2)) (i + 2) = matchSearch (vanEck (i + 2)) (i + 1) := by {
            have h_neq2 : listNth (vanEck (i + 2)) ((vanEck (i + 2)).length - 1) ≠ listNth (vanEck (i + 2)) (i + 1) := by {
              rw [hlen, hsub2, hd_2_list, hd_1_list]
              intro hc; exact h_neq1 hc.symm
            }
            have h_ff := matchSearch_ite_ff (vanEck (i + 2)) (i + 1) h_neq2
            have hi2 : i + 1 + 1 = i + 2 := rfl
            rw [hi2] at h_ff; exact h_ff
          }
          have h_ite_2 : matchSearch (vanEck (i + 2)) (i + 1) = 2 := by {
            have h_eq2 : listNth (vanEck (i + 2)) ((vanEck (i + 2)).length - 1) = listNth (vanEck (i + 2)) i := by {
              rw [hlen, hsub2, hd_2_list, hd_0_list]
              exact h_eq_i.symm
            }
            have h_tt := matchSearch_ite_tt (vanEck (i + 2)) i h_eq2
            rw [h_tt, hlen, hsub2]
            exact Nat.add_sub_cancel_left i 2
          }
          rw [h_ite_1, h_ite_2] at hm; exact hm
        }
        have h_contra := h_no_twos (i + 3) (by omega)
        exact h_contra hd_2

    -- Case P ≥ 3: C ≥ 2 contradiction via counting and no-2 constraint.
    · have h_P_ge_3 : P ≥ 3 := by omega
      -- We must show a contradiction for P >= 3.
      -- We know C = P + 1 - ∑ d_k. 
      -- We first prove that d_k is an indicator function: d_k ≤ 1.
      have h_dk_bound : ∀ k : Fin P, (k.val + 1 + P - v_fn k) / P ≤ 1 := by {
        intro k
        -- (k + 1 + P - v) / P ≤ 1 because k + 1 + P - v < 2 * P
        have hk_lt := k.isLt  -- k.val < P
        have hv_ge := hv1 k   -- 1 ≤ v_fn k
        -- k + 1 + P - v ≤ k + P ≤ (P-1) + P = 2P - 1 < 2P
        have h_num_lt : k.val + 1 + P - v_fn k < 2 * P := by omega
        exact Nat.div_lt_iff_lt_mul h_P_pos |>.mpr h_num_lt |> Nat.lt_succ_iff.mp
      }
      
      have h_dk_sum_le_P : ∑ k : Fin P, ((k.val + 1 + P - v_fn k) / P) ≤ P := by {
        -- Sum of P elements each ≤ 1 is ≤ P
        calc ∑ k : Fin P, ((k.val + 1 + P - v_fn k) / P)
            ≤ ∑ _k : Fin P, 1 := Finset.sum_le_sum (fun k _ => h_dk_bound k)
          _ = P := by simp [Finset.sum_const, Finset.card_fin]
      }
      
      -- ══════════════════════════════════════════════════════════════
      -- Case P = 3: values from {1, 3}, sum = C*3 ≥ 6 → all 3s → contradiction.
      -- ══════════════════════════════════════════════════════════════
      by_cases hP3 : P = 3
      · -- P = 3. Let a, b, c be the three values in the period.
        let a := v_fn ⟨0, by omega⟩
        let b := v_fn ⟨1, by omega⟩
        let c := v_fn ⟨2, by omega⟩
        
        -- Expand the sum using our lemma
        have h_sum_abc : a + b + c = C * 3 := by {
          have h1 := fin_sum_three hP3 v_fn
          rw [h1] at hC
          have h_CP : C * P = C * 3 := by rw [hP3]
          rw [h_CP] at hC
          exact hC
        }

        -- Show a, b, c are 1 or 3
        have ha13 : a = 1 ∨ a = 3 := by {
          have h1 := hv1 ⟨0, by omega⟩
          have hP_bnd := hvP ⟨0, by omega⟩
          have h2 : a ≠ 2 := h_no_twos (n_2 + 0 + 1) (by omega)
          have hp : P = 3 := hP3
          omega
        }
        have hb13 : b = 1 ∨ b = 3 := by {
          have h1 := hv1 ⟨1, by omega⟩
          have hP_bnd := hvP ⟨1, by omega⟩
          have h2 : b ≠ 2 := h_no_twos (n_2 + 1 + 1) (by omega)
          have hp : P = 3 := hP3
          omega
        }
        have hc13 : c = 1 ∨ c = 3 := by {
          have h1 := hv1 ⟨2, by omega⟩
          have hP_bnd := hvP ⟨2, by omega⟩
          have h2 : c ≠ 2 := h_no_twos (n_2 + 2 + 1) (by omega)
          have hp : P = 3 := hP3
          omega
        }

        -- Use standalone lemma to force them to 3
        have h_all_3 := period_three_forces_all_threes a b c C ha13 hb13 hc13 h_C_ge_2 h_sum_abc
        have ha_eq := h_all_3.1
        have hb_eq := h_all_3.2.1
        have hc_eq := h_all_3.2.2

        -- a = v_fn 0 = vanEckNthTerm(n_2 + 1)
        -- b = v_fn 1 = vanEckNthTerm(n_2 + 2)
        -- c = v_fn 2 = vanEckNthTerm(n_2 + 3)
        have h_a_val : a = vanEckNthTerm (n_2 + 1) := rfl
        have h_b_val : b = vanEckNthTerm (n_2 + 2) := rfl
        have h_c_val : c = vanEckNthTerm (n_2 + 3) := rfl

        -- a = b = 3 → consecutive equals → next = 1.
        have h_cons : vanEckNthTerm (n_2 + 1) = vanEckNthTerm (n_2 + 2) := by omega
        have h_next_1 : c = 1 := by {
          rw [h_c_val]
          have h := vanEck_consecutive_eq_implies_next_one (n_2 + 1) h_cons
          have : n_2 + 1 + 2 = n_2 + 3 := by omega
          rw [this] at h; exact h
        }
        -- c = 3 and c = 1. Contradiction!
        omega

      -- ══════════════════════════════════════════════════════════════
      -- Case P ≥ 4: remaining open case.
      -- The d_k bounds (h_dk_bound, h_dk_sum_le_P) constrain the
      -- displacement graph. The same sum-mod argument generalizes
      -- but requires handling more value combinations.
      -- ══════════════════════════════════════════════════════════════
      · have h_P_ge_4 : P ≥ 4 := by omega
        sorry
}

lemma exists_max_first_occurrence (B : ℕ) :
  ∃ N, ∀ x ≤ B, (∃ k, vanEckNthTerm k = x) → ∃ k ≤ N, vanEckNthTerm k = x := by {
  induction B with
  | zero =>
    by_cases h : ∃ k, vanEckNthTerm k = 0
    · rcases h with ⟨k, hk⟩
      exact ⟨k, fun x hx h_ex => by
        have h0 : x = 0 := Nat.eq_zero_of_le_zero hx
        rw [h0]
        exact ⟨k, Nat.le_refl k, hk⟩
      ⟩
    · exact ⟨0, fun x hx h_ex => by
        have h0 : x = 0 := Nat.eq_zero_of_le_zero hx
        rw [h0] at h_ex
        contradiction
      ⟩
  | succ B ih =>
    rcases ih with ⟨N_B, hN_B⟩
    by_cases h : ∃ k, vanEckNthTerm k = B + 1
    · rcases h with ⟨k, hk⟩
      exact ⟨max N_B k, fun x hx h_ex => by
        have h_or := (splitting_le x (B + 1)).mp hx
        rcases h_or with h_lt | h_eq
        · have h_le := Nat.le_of_lt_succ h_lt
          rcases hN_B x h_le h_ex with ⟨k2, hk2_le, hk2_eq⟩
          exact ⟨k2, Nat.le_trans hk2_le (Nat.le_max_left N_B k), hk2_eq⟩
        · rw [h_eq]
          exact ⟨k, Nat.le_max_right N_B k, hk⟩
      ⟩
    · exact ⟨N_B, fun x hx h_ex => by
        have h_or := (splitting_le x (B + 1)).mp hx
        rcases h_or with h_lt | h_eq
        · have h_le := Nat.le_of_lt_succ h_lt
          exact hN_B x h_le h_ex
        · rw [h_eq] at h_ex
          contradiction
      ⟩
}


/--
If a bounded block exhibits local periodicity, it must inevitably force an
alternating pair or a zero, contradicting the conditions for no 2s and strict
positive bounding.

Layman's terms: A Van Eck sequence cannot get stuck in a repeating loop without
eventually generating a 2 or a zero. If it repeats, it's forced to evaluate the
distances within its own cycle, which mathematically forces collisions that
break the cycle.
-/
lemma local_periodicity_impossible (n_1 n_2 K : ℕ)
    (hn1_lt_n2 : n_1 < n_2)
    (h_K_large : K ≥ n_2 - n_1 + 3)
    (h_no_twos : ∀ m > n_1, vanEckNthTerm m ≠ 2)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k)) :
    False := by {
  -- Bounded periodicity forces the sequence to evaluate its own cycle distances.
  -- This graph-theoretically creates cycle-breaking elements, contradicting h_per
  -- and creating alternating pairs that contradict h_no_twos.
  have h_no_zero : ∀ k, 1 ≤ k → k ≤ K → vanEckNthTerm (n_2 + k) ≠ 0 := by {
    intro k hk1 hkK h_zero
    have h_n2_pos : n_2 ≥ 1 := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le n_1) hn1_lt_n2)
    have h1 : n_2 + k ≥ 2 := by {
      have hA : 1 + 1 ≤ n_2 + k := Nat.add_le_add h_n2_pos hk1
      exact hA
    }
    have h_m2 : n_2 + k - 2 + 2 = n_2 + k := Nat.sub_add_cancel h1
    have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new (n_2 + k - 2)
    rw [h_m2] at h_iff
    have h_new := h_iff.mp h_zero
    have h_m1 : n_2 + k - 2 + 1 = n_2 + k - 1 := by {
      have hB : n_2 + k - 1 ≥ 1 := Nat.le_sub_one_of_lt h1
      exact Nat.sub_add_cancel hB
    }
    rw [h_m1] at h_new
    have h_sub1 : n_1 + k - 1 = n_1 + (k - 1) := by {
      have hC : n_1 + k - 1 = n_1 + (k - 1) := Nat.add_sub_assoc hk1 n_1
      exact hC
    }
    have h_sub2 : n_2 + k - 1 = n_2 + (k - 1) := by {
      have hD : n_2 + k - 1 = n_2 + (k - 1) := Nat.add_sub_assoc hk1 n_2
      exact hD
    }
    have h_prev_eq : vanEckNthTerm (n_1 + k - 1) = vanEckNthTerm (n_2 + k - 1) := by {
      have hkm1 : k - 1 ≤ K := Nat.le_trans (Nat.sub_le k 1) hkK
      have h_per_eval := h_per (k - 1) hkm1
      rw [h_sub1, h_sub2]
      exact h_per_eval
    }
    have h_not_new := h_new (n_1 + k - 1) (by {
      rw [h_sub1, h_sub2]
      exact Nat.add_lt_add_right hn1_lt_n2 (k - 1)
    })
    exact h_not_new h_prev_eq
  }
  exact finite_cycle_gap_collapse n_1 n_2 K hn1_lt_n2 h_K_large h_no_zero h_no_twos h_per
}

/--
The "Harder Thing": Dense Collisions Force Twos.

If small numbers (bounded by B) are sufficiently dense, they must inevitably collide.
Because the sequence cannot be eventually periodic, these collisions break any
repeating cycles, mathematically forcing identical elements to eventually appear
with a distance of exactly 2, thus generating a 2.
-/
theorem dense_collisions_force_twos (B : ℕ) (hB_gt : B > 0) :
    DenseSmallNumbers B ((B + 1) ^ (B + 1) + (B + 1) + 5) → InfiniteTwos := by {
  intro h_dense
  intro N
  by_contra h_no_twos
  push Not at h_no_twos

  -- From h_dense, we obtain a dense block far out in the sequence.
  have h_max_occ := exists_max_first_occurrence (B + 1)
  rcases h_max_occ with ⟨N_max, hN_max⟩
  let N' := max N N_max
  have h_ex := h_dense N'
  rcases h_ex with ⟨start, h_start_gt, h_block⟩

  -- By our stepping stone, this dense block has NO alternating pairs.
  have h_no_alt := dense_block_without_twos_has_no_alternating_pairs B ((B + 1) ^ (B + 1) + (B + 1) + 5) start h_block (by
    intro m hm_gt
    exact h_no_twos m (Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_max_left N N_max) h_start_gt) hm_gt)
  )

  -- Because the block is bounded strictly by B + 1, we can apply our
  -- local pigeonhole state collision theorem to extract a massive state repetition!
  -- We use the padding trick: we apply it to the FIRST part of the block to ensure n_2 + 3 is still inside!
  let G_small := (B + 1) ^ (B + 1) + (B + 1) + 2

  have h_bound : ∀ k, start ≤ k → k < start + G_small - 1 → vanEckNthTerm k < B + 1 := by
    intro k hk_ge hk_lt
    have hk_lt_G : k - start < ((B + 1) ^ (B + 1) + (B + 1) + 5) := by
      calc k - start < G_small - 1 := Nat.sub_lt_left_of_lt_add hk_ge hk_lt
           _ ≤ G_small := Nat.sub_le _ _
           _ < G_small + 3 := Nat.lt_add_of_pos_right (by decide)
    have h_le := h_block (k - start) hk_lt_G
    have h_k_eq : start + (k - start) = k := Nat.add_sub_cancel' hk_ge
    rw [h_k_eq] at h_le
    exact Nat.lt_succ_of_le h_le

  have hB1_gt : B + 1 > 1 := Nat.add_lt_add_right hB_gt 1

  have h_coll := local_pigeonhole_state_collision start G_small (B + 1) h_bound hB1_gt (Nat.le_refl _)

  rcases h_coll with ⟨n_1, n_2, hn1_ge, hn1_lt_n2, hn2_lt, h_state_eq⟩

  -- We now have n_1 < n_2 with exactly matching states of length B+1!
  -- This forces a local periodicity that will inevitably break h_no_alt.
  let K := n_2 - n_1 + 3

  have hd1_lt : ∀ k ≤ K, vanEckNthTerm (n_1 + k) < B + 1 := by
    intro k hk
    have hk_ge : start ≤ n_1 + k := Nat.le_trans (Nat.le_trans (Nat.le_add_right start (B + 1)) hn1_ge) (Nat.le_add_right n_1 k)
    have hk_lt_G : n_1 + k - start < ((B + 1) ^ (B + 1) + (B + 1) + 5) := by
      have h1 : n_1 + k ≤ n_1 + K := Nat.add_le_add_left hk n_1
      have h2 : n_1 + K = n_2 + 3 := by
        have hh1 : n_1 + (n_2 - n_1 + 3) = n_1 + (n_2 - n_1) + 3 := rfl
        rw [hh1]
        have hh2 : n_1 + (n_2 - n_1) = n_2 := Nat.add_sub_of_le (Nat.le_of_lt hn1_lt_n2)
        rw [hh2]
      rw [h2] at h1
      have h3 : n_1 + k - start ≤ n_2 + 3 - start := Nat.sub_le_sub_right h1 start
      have h4 : n_2 + 3 - start = n_2 - start + 3 := by
        have hh : start ≤ n_2 := Nat.le_trans (Nat.le_add_right start (B + 1)) hn1_ge |>.trans (Nat.le_of_lt hn1_lt_n2)
        have hA : n_2 + 3 = 3 + n_2 := Nat.add_comm _ _
        have hB : 3 + n_2 - start = 3 + (n_2 - start) := Nat.add_sub_assoc hh 3
        have hC : 3 + (n_2 - start) = n_2 - start + 3 := Nat.add_comm _ _
        rw [hA, hB, hC]
      rw [h4] at h3

      have h5 : n_2 - start < G_small - 1 := Nat.sub_lt_left_of_lt_add (Nat.le_trans (Nat.le_add_right start (B + 1)) hn1_ge |>.trans (Nat.le_of_lt hn1_lt_n2)) hn2_lt
      have h6 : n_2 - start + 3 < G_small - 1 + 3 := Nat.add_lt_add_right h5 3
      have h7 : G_small - 1 + 3 ≤ G_small + 3 := Nat.add_le_add_right (Nat.sub_le G_small 1) 3
      have h8 : G_small + 3 = (B + 1) ^ (B + 1) + (B + 1) + 5 := rfl
      exact Nat.lt_of_le_of_lt h3 (Nat.lt_of_lt_of_le h6 (by rw [h8]; exact h7))

    have h_le := h_block (n_1 + k - start) hk_lt_G
    have h_k_eq : start + (n_1 + k - start) = n_1 + k := Nat.add_sub_cancel' hk_ge
    rw [h_k_eq] at h_le
    exact Nat.lt_succ_of_le h_le

  have hd1_pos : ∀ k ≤ K, vanEckNthTerm (n_1 + k) > 0 := by
    intro k hk
    by_contra hc
    have h_zero : vanEckNthTerm (n_1 + k) = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_lt hc)
    have h_n1_pos : n_1 ≥ 1 := Nat.succ_le_of_lt (by
      calc 0 < B + 1 := Nat.zero_lt_succ B
           _ ≤ start + (B + 1) := Nat.le_add_left (B + 1) start
           _ ≤ n_1 := hn1_ge
    )
    have h1 : n_1 + k ≥ 2 := by
      have hb_ge_1 : B + 1 ≥ 2 := Nat.succ_le_succ hB_gt
      calc n_1 + k ≥ n_1 := Nat.le_add_right n_1 k
           _ ≥ start + (B + 1) := hn1_ge
           _ ≥ 0 + 2 := Nat.add_le_add (Nat.zero_le start) hb_ge_1
           _ = 2 := rfl
    have h_m2 : n_1 + k - 2 + 2 = n_1 + k := Nat.sub_add_cancel h1
    have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new (n_1 + k - 2)
    rw [h_m2] at h_iff
    have h_new := h_iff.mp h_zero
    have h_m1 : n_1 + k - 2 + 1 = n_1 + k - 1 := by
      have hB2 : n_1 + k - 1 ≥ 1 := Nat.le_sub_one_of_lt h1
      exact Nat.sub_add_cancel hB2
    rw [h_m1] at h_new
    have h_prev_bound : vanEckNthTerm (n_1 + k - 1) < B + 1 := by
      have h_idx_ge : start ≤ n_1 + k - 1 := by
        calc start ≤ start + B := Nat.le_add_right start B
             _ = start + B + 1 - 1 := rfl
             _ ≤ n_1 - 1 := Nat.sub_le_sub_right hn1_ge 1
             _ ≤ n_1 + k - 1 := Nat.sub_le_sub_right (Nat.le_add_right n_1 k) 1
      have h_idx_lt : n_1 + k - 1 - start < ((B + 1) ^ (B + 1) + (B + 1) + 5) := by
        have ht1 : n_1 + k - 1 ≤ n_1 + K := by
          calc n_1 + k - 1 ≤ n_1 + k := Nat.sub_le (n_1 + k) 1
               _ ≤ n_1 + K := Nat.add_le_add_left hk n_1
        have ht2 : n_1 + K = n_2 + 3 := by
          have hh1 : n_1 + (n_2 - n_1 + 3) = n_1 + (n_2 - n_1) + 3 := rfl
          rw [hh1]
          have hh2 : n_1 + (n_2 - n_1) = n_2 := Nat.add_sub_of_le (Nat.le_of_lt hn1_lt_n2)
          rw [hh2]
        rw [ht2] at ht1
        have ht3 : n_1 + k - 1 - start ≤ n_2 + 3 - start := Nat.sub_le_sub_right ht1 start
        have ht4 : n_2 + 3 - start = n_2 - start + 3 := by
          have hh : start ≤ n_2 := Nat.le_trans (Nat.le_trans (Nat.le_add_right start (B + 1)) hn1_ge) (Nat.le_of_lt hn1_lt_n2)
          have hA2 : n_2 + 3 = 3 + n_2 := Nat.add_comm _ _
          have hB2 : 3 + n_2 - start = 3 + (n_2 - start) := Nat.add_sub_assoc hh 3
          have hC2 : 3 + (n_2 - start) = n_2 - start + 3 := Nat.add_comm _ _
          rw [hA2, hB2, hC2]
        rw [ht4] at ht3
        have ht5 : n_2 - start < G_small - 1 := Nat.sub_lt_left_of_lt_add (Nat.le_trans (Nat.le_add_right start (B + 1)) hn1_ge |>.trans (Nat.le_of_lt hn1_lt_n2)) hn2_lt
        have ht6 : n_2 - start + 3 < G_small - 1 + 3 := Nat.add_lt_add_right ht5 3
        have ht7 : G_small - 1 + 3 ≤ G_small + 3 := Nat.add_le_add_right (Nat.sub_le G_small 1) 3
        have ht8 : G_small + 3 = ((B + 1) ^ (B + 1) + (B + 1) + 5) := rfl
        exact Nat.lt_of_le_of_lt ht3 (Nat.lt_of_lt_of_le ht6 (by rw [ht8]; exact ht7))
      have h_b := h_block (n_1 + k - 1 - start) h_idx_lt
      have h_rw : start + (n_1 + k - 1 - start) = n_1 + k - 1 := Nat.add_sub_cancel' h_idx_ge
      rw [h_rw] at h_b
      exact Nat.lt_succ_of_le h_b
    have h_ex_j := hN_max (vanEckNthTerm (n_1 + k - 1)) (Nat.le_of_lt h_prev_bound) ⟨n_1 + k - 1, rfl⟩
    rcases h_ex_j with ⟨j, hj_le, hj_eq⟩
    have hj_lt : j < n_1 + k - 1 := by
      have hA : j ≤ N' := Nat.le_trans hj_le (Nat.le_max_right N N_max)
      have hB : N' < start := h_start_gt
      have hC : start ≤ n_1 + k - 1 := by
        calc start ≤ start + B := Nat.le_add_right start B
             _ ≤ start + B + 1 - 1 := by
               have hD : start + B + 1 - 1 = start + B := rfl
               rw [hD]
             _ ≤ n_1 - 1 := Nat.sub_le_sub_right hn1_ge 1
             _ ≤ n_1 + k - 1 := Nat.sub_le_sub_right (Nat.le_add_right n_1 k) 1
      exact Nat.lt_of_lt_of_le (Nat.lt_of_le_of_lt hA hB) hC
    have h_contra := h_new j hj_lt
    exact h_contra hj_eq

  have hn1_ge_B : B + 1 ≤ n_1 := Nat.le_trans (Nat.le_add_left (B + 1) start) hn1_ge
  have hn2_ge_B : B + 1 ≤ n_2 := Nat.le_trans hn1_ge_B (Nat.le_of_lt hn1_lt_n2)

  have h_per := local_forward_periodicity_left (B + 1) n_1 n_2 K h_state_eq hn1_ge_B hn2_ge_B (Nat.zero_lt_succ B) hd1_lt hd1_pos

  have h_contra := local_periodicity_impossible n_1 n_2 K hn1_lt_n2 (Nat.le_refl _) (by
    intro m hm
    have h1 : start ≤ n_1 := Nat.le_trans (Nat.le_add_right start (B + 1)) hn1_ge
    have h2 : start < m := Nat.lt_of_le_of_lt h1 hm
    exact h_no_twos m (Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_max_left N N_max) h_start_gt) h2)
  )


  have h_per_eval : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k) := fun k hk => (h_per k hk).right
  exact h_contra h_per_eval
}
