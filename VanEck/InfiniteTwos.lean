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
import SurjectivityLemmas
import InfiniteEvens
import MirskyNewman

open scoped Classical



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
  --
  -- We obtain a zero-gap after N that is a brand new number.
  have h_ex := h_new_gaps N
  rcases h_ex with ⟨z, hz_gt, hz_zero, h_new⟩
  --
  -- We provide z + 3 as the index where 2 will be generated.
  use z + 3
  --
  constructor
  · -- Prove z + 3 > N
    apply Nat.lt_of_lt_of_le hz_gt
    exact Nat.le_add_right z 3
  · -- Prove vanEckNthTerm (z + 3) = 2
    have hz2 : vanEckNthTerm (z + 2) = 0 := (vanEck_mth_term_eq_zero_iff_prev_term_new z).mpr h_new
  --
    have hz1_neq_0 : vanEckNthTerm (z + 1) ≠ 0 := by {
      intro hc
      have hc_new := h_new z (Nat.lt_succ_self z)
      rw [hc] at hc_new
      exact hc_new hz_zero
    }
  --
    have hl_z : lastZero z = z := by {
      cases z with
      | zero => rfl
      | succ z' =>
        rw [lastZero]
        rw [if_pos hz_zero]
    }
  --
    have hl_z1 : lastZero (z + 1) = z := by {
      rw [lastZero]
      rw [if_neg hz1_neq_0]
      exact hl_z
    }
  --
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



-- Note: The reverse direction (InfiniteTwos → InfiniteNewZeroGaps) was intentionally skipped
-- as it requires tracking global zero density, which is not strictly necessary for our
-- primary local_periodicity_impossible objective.




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
  --
  have h_idx_le : n - B + k ≤ n - 1 := by
    have h_k_le : k ≤ B - 1 := Nat.le_sub_one_of_lt hk
    calc n - B + k ≤ n - B + (B - 1) := Nat.add_le_add_left h_k_le _
         _ = n - B + B - 1 := (Nat.add_sub_assoc hB0 (n - B)).symm
         _ = n - 1 := by rw [Nat.sub_add_cancel (Nat.le_trans (Nat.le_add_left B N) hN)]
  --
  have h_det : listNth (vanEck (n - 1)) (n - B + k) = vanEckNthTerm (n - B + k) :=
    VanEck_deterministic (n - 1) (n - B + k) h_idx_le
  --
  have h_idx_ge : N ≤ n - B + k := by
    calc N ≤ n - B := Nat.le_sub_of_add_le hN
         _ ≤ n - B + k := Nat.le_add_right _ _
  --
  have hn_pos : n > 0 := Nat.lt_of_lt_of_le hB0 (Nat.le_trans (Nat.le_add_left B N) hN)
  have h_idx_lt : n - B + k < n := by
    calc n - B + k ≤ n - 1 := h_idx_le
         _ < n := Nat.sub_lt_self (by decide) hn_pos
  --
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
  --
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
  --
  have hb0 : B > 0 := Nat.lt_trans (Nat.zero_lt_succ 0) hB_gt
  --
  have h_lim : ∀ x, x ≤ M → f x < M := fun x hx => by
    have h_n_plus_B : N + B ≤ N + B + x := Nat.le_add_right _ _
    have hx_ge : B ≤ N + B + x := by
      calc B ≤ N + B := Nat.le_add_left B N
           _ ≤ N + B + x := Nat.le_add_right _ _
    have hlen : (vanEckState (N + B + x) B).length = B :=
      vanEckState_length (N + B + x) B hx_ge hb0
  --
    have h_state_bounded : IsBoundedState (vanEckState (N + B + x) B) B := by
      apply local_vanEckState_isBounded N (N + B + x) B h_n_plus_B hb0
      intro k hk_ge hk_lt
      apply h_bound k hk_ge
      calc k < N + B + x := hk_lt
           _ ≤ N + B + M := Nat.add_le_add_left hx _
           _ < N + G - 1 := h_G_minus
  --
    have hl := stateEval_lt_pow (vanEckState (N + B + x) B) B hB_gt h_state_bounded
    rw [hlen] at hl
    exact hl
  --
  let f_fin : Fin (M + 1) → Fin M := fun x => ⟨f x.val, h_lim x.val (Nat.le_of_lt_succ x.isLt)⟩
  have h_card : Fintype.card (Fin M) < Fintype.card (Fin (M + 1)) := by simp
  have h_exists := Fintype.exists_ne_map_eq_of_card_lt f_fin h_card
  rcases h_exists with ⟨x, y, hne, heq⟩
  have heq_val : f x.val = f y.val := congr_arg Fin.val heq
  --
  have hx_ge : B ≤ N + B + x.val := by
    calc B ≤ N + B := Nat.le_add_left B N
         _ ≤ N + B + x.val := Nat.le_add_right _ _
  have hy_ge : B ≤ N + B + y.val := by
    calc B ≤ N + B := Nat.le_add_left B N
         _ ≤ N + B + y.val := Nat.le_add_right _ _
  --
  have h_state_bounded_x : IsBoundedState (vanEckState (N + B + x.val) B) B := by
    apply local_vanEckState_isBounded N (N + B + x.val) B (Nat.le_add_right _ _) hb0
    intro k hk_ge hk_lt
    apply h_bound k hk_ge
    calc k < N + B + x.val := hk_lt
         _ ≤ N + B + M := Nat.add_le_add_left (Nat.le_of_lt_succ x.isLt) _
         _ < N + G - 1 := h_G_minus
  --
  have h_state_bounded_y : IsBoundedState (vanEckState (N + B + y.val) B) B := by
    apply local_vanEckState_isBounded N (N + B + y.val) B (Nat.le_add_right _ _) hb0
    intro k hk_ge hk_lt
    apply h_bound k hk_ge
    calc k < N + B + y.val := hk_lt
         _ ≤ N + B + M := Nat.add_le_add_left (Nat.le_of_lt_succ y.isLt) _
         _ < N + G - 1 := h_G_minus
  --
  have h_state_eq : vanEckState (N + B + x.val) B = vanEckState (N + B + y.val) B := by
    apply stateEval_inj B hB_gt
    · rw [vanEckState_length (N + B + x.val) B hx_ge hb0, vanEckState_length (N + B + y.val) B hy_ge hb0]
    · exact h_state_bounded_x
    · exact h_state_bounded_y
    · exact heq_val
  --
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
  --
  have hL1_len : (vanEck (n_1 - 1)).length ≥ B := by
    rw [vanEckLength]
    have h : n_1 - 1 + 1 = n_1 := Nat.sub_add_cancel hn1_pos
    rw [h]; exact hn1_ge
  --
  have hL2_len : (vanEck (n_2 - 1)).length ≥ B := by
    rw [vanEckLength]
    have h : n_2 - 1 + 1 = n_2 := Nat.sub_add_cancel hn2_pos
    rw [h]; exact hn2_ge
  --
  have h_van_eq : (vanEck (n_1 - 1)).drop ((vanEck (n_1 - 1)).length - B) =
      (vanEck (n_2 - 1)).drop ((vanEck (n_2 - 1)).length - B) := by
    have h1 : (vanEck (n_1 - 1)).length - B = n_1 - B := by
      rw [vanEckLength, Nat.sub_add_cancel hn1_pos]
    have h2 : (vanEck (n_2 - 1)).length - B = n_2 - B := by
      rw [vanEckLength, Nat.sub_add_cancel hn2_pos]
    rw [h1, h2]
    exact h_eq
  --
  have ht1 := vanEck_term_is_matchSearch n_1 hn1_pos
  have ht2 := vanEck_term_is_matchSearch n_2 hn2_pos
  --
  have hind1 : n_1 - 1 = (vanEck (n_1 - 1)).length - 1 := by rw [vanEckLength, Nat.add_sub_cancel]
  have hind2 : n_2 - 1 = (vanEck (n_2 - 1)).length - 1 := by rw [vanEckLength, Nat.add_sub_cancel]
  --
  have h_lhs : matchSearch (vanEck (n_1 - 1)) ((vanEck (n_1 - 1)).length - 1) = vanEckNthTerm n_1 := by
    rw [← hind1]; exact ht1.symm
  --
  have h_rhs_term : matchSearch (vanEck (n_2 - 1)) ((vanEck (n_2 - 1)).length - 1) = vanEckNthTerm n_2 := by
    rw [← hind2]; exact ht2.symm
  --
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
  --
    have h_s1 := vanEckState_succ (n_1 + k) B (Nat.le_trans hn1_ge (Nat.le_add_right n_1 k)) hb0
    have h_s2 := vanEckState_succ (n_2 + k) B (Nat.le_trans hn2_ge (Nat.le_add_right n_2 k)) hb0
  --
    have h_next_state : vanEckState ((n_1 + k) + 1) B = vanEckState ((n_2 + k) + 1) B := by
      rw [h_s1, h_s2, ih_state, ih_term]
  --
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
  --
  let M := vanEckPrefixMax N
  let B := M + 1
  have hb0 : B > 0 := Nat.zero_lt_succ M
  have hB_gt : B > 1 := by
    have hM : M ≥ vanEckNthTerm 2 := vanEckNthTerm_le_prefixMax N 2 hN_ge
    have h2 : vanEckNthTerm 2 = 1 := rfl
    rw [h2] at hM
    exact Nat.succ_lt_succ hM
  --
  have h_bound : ∀ k, N ≤ k → k < N + G - 1 → vanEckNthTerm k < B := by
    intro k hk_ge hk_lt
    have hz : ∀ j, N < j → j < N + G → vanEckNthTerm j ≠ 0 := fun j hj_ge hj_lt => h_nonzero j (Nat.le_of_lt hj_ge) hj_lt
    have h_pos : N + G > 0 := Nat.lt_of_lt_of_le (Nat.lt_trans (by decide) hN_ge) (Nat.le_add_right N G)
    have h_k_lt2 : k < N + G - 1 := hk_lt
    have h1 : vanEckNthTerm k ≤ M := gap_contains_all_terms N G hz k h_k_lt2
    exact Nat.lt_succ_of_le h1
  --
  have h_coll := local_pigeonhole_state_collision N G B h_bound hB_gt h_G_large
  rcases h_coll with ⟨n_1, n_2, hn1_ge, hn1_lt_n2, hn2_lt, h_eq⟩
  --
  have h_NG_minus_2 : N + G ≥ 2 := Nat.le_trans hN_ge (Nat.le_add_right N G)
  --
  let K := N + G - 1 - n_2
  have h_n2_K : n_2 + K = N + G - 1 := by
    have h_n2_le : n_2 ≤ N + G - 1 := Nat.le_of_lt hn2_lt
    exact Nat.add_sub_cancel' h_n2_le
  --
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
  --
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
  --
  have h_per := local_forward_periodicity_left B n_1 n_2 K h_eq (Nat.le_trans (Nat.le_add_left B N) hn1_ge) (Nat.le_trans (Nat.le_add_left B N) (Nat.le_trans hn1_ge (Nat.le_of_lt hn1_lt_n2))) hb0 hd1_lt hd1_pos
  --
  have h_term_eq := (h_per K (Nat.le_refl K)).right
  rw [h_n2_K] at h_term_eq
  --
  have h_contra_lt : n_1 + K < N + G - 1 := by
    calc n_1 + K < n_2 + K := Nat.add_lt_add_right hn1_lt_n2 K
         _ = N + G - 1 := h_n2_K
  --
  have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new (N + G - 2)
  have h_sub_add : N + G - 2 + 2 = N + G := Nat.sub_add_cancel h_NG_minus_2
  rw [h_sub_add] at h_iff
  have h_new := h_iff.mp h_end_zero
  --
  have h_sub_add1 : N + G - 2 + 1 = N + G - 1 := by
    have h1 : N + G - 1 ≥ 1 := by
      have h : N + G ≥ 2 := Nat.le_trans hN_ge (Nat.le_add_right N G)
      exact Nat.le_sub_one_of_lt h
    exact Nat.sub_add_cancel h1
  rw [h_sub_add1] at h_new
  --
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
  --
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
  --
      have hlen : (vanEck (i + 2)).length = i + 3 := vanEckLength (i + 2)
  --
      have hd_2_list : listNth (vanEck (i + 2)) (i + 2) = vanEckNthTerm (i + 2) := by
        exact VanEck_deterministic (i + 2) (i + 2) (Nat.le_refl _)
      have hd_1_list : listNth (vanEck (i + 2)) (i + 1) = vanEckNthTerm (i + 1) := by
        exact VanEck_deterministic (i + 2) (i + 1) (Nat.le_succ _)
      have hd_0_list : listNth (vanEck (i + 2)) i = vanEckNthTerm i := by
        exact VanEck_deterministic (i + 2) i (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
  --
      have hsub2 : i + 3 - 1 = i + 2 := rfl
  --
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
  --
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
  --
      rw [h_ite_1, h_ite_2] at hm
      exact hm
  --
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
    (hf : ∀ k, (f k).val = (k.val + P - v k) % P)
    (hbij : Function.Bijective f) :
    ∃ C : ℕ, ∑ k : Fin P, v k = C * P := by {
  have h_sum_f : ∑ k : Fin P, (f k).val = ∑ k : Fin P, k.val := by
    have heq : ∑ k : Fin P, (f k).val = ∑ k : Fin P, (fun x => x.val) (f k) := rfl
    rw [heq]
    exact Equiv.sum_comp (Equiv.ofBijective f hbij) (fun k => k.val)
  --
  let d := fun (k : Fin P) => (k.val + P - v k) / P
  --
  have h_div_mod : ∀ k, (k.val + P - v k) = P * d k + (f k).val := by {
    intro k
    have h_mod := Nat.div_add_mod (k.val + P - v k) P
    have hfk := hf k
    have hd_def : d k = (k.val + P - v k) / P := rfl
    rw [hfk, hd_def]
    exact h_mod.symm
  }
  --
  have h_sum1 : ∑ k : Fin P, (k.val + P - v k) = ∑ k : Fin P, (P * d k + (f k).val) := by {
    apply Finset.sum_congr rfl
    intro x _
    exact h_div_mod x
  }
  --
  have h_sum_left : ∑ k : Fin P, (k.val + P - v k) + ∑ k : Fin P, v k = ∑ k : Fin P, (k.val + P) := by {
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    have h2 := hvP x
    have h3 : v x ≤ x.val + P := by
      exact le_trans h2 (Nat.le_add_left P x.val)
    exact Nat.sub_add_cancel h3
  }
  --
  have h_sum_right : ∑ k : Fin P, (P * d k + (f k).val) = P * ∑ k : Fin P, d k + ∑ k : Fin P, (f k).val := by {
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  }
  --
  have h_sum_1P : ∑ k : Fin P, (k.val + P) = ∑ k : Fin P, k.val + P * P := by {
    have h1 : ∑ k : Fin P, (k.val + P) = ∑ k : Fin P, k.val + ∑ k : Fin P, P := by
      rw [← Finset.sum_add_distrib]
    rw [h1]
    have h2 : ∑ k : Fin P, P = P * P := by
      have hz : ∑ k : Fin P, P = (Finset.card (Finset.univ : Finset (Fin P))) * P := by
        exact Finset.sum_const P
      have hc : Finset.card (Finset.univ : Finset (Fin P)) = P := Fintype.card_fin P
      rw [hc] at hz
      exact hz
    rw [h2]
  }
  --
  have h_eq1 : ∑ k : Fin P, (k.val + P - v k) = P * ∑ k : Fin P, d k + ∑ k : Fin P, k.val := by {
    rw [h_sum1, h_sum_right, h_sum_f]
  }
  --
  have h_eq2 : P * ∑ k : Fin P, d k + ∑ k : Fin P, k.val + ∑ k : Fin P, v k = ∑ k : Fin P, k.val + P * P := by {
    have hr : P * ∑ k : Fin P, d k + ∑ k : Fin P, k.val + ∑ k : Fin P, v k = ∑ k : Fin P, (k.val + P - v k) + ∑ k : Fin P, v k := by rw [h_eq1]
    rw [hr, h_sum_left]
    exact h_sum_1P
  }
  --
  have h_eq3 : (∑ k : Fin P, k.val) + (P * ∑ k : Fin P, d k + ∑ k : Fin P, v k) = (∑ k : Fin P, k.val) + P * P := by {
    have hr : (∑ k : Fin P, k.val) + (P * ∑ k : Fin P, d k + ∑ k : Fin P, v k) = P * ∑ k : Fin P, d k + ∑ k : Fin P, k.val + ∑ k : Fin P, v k := by
      calc
        (∑ k : Fin P, k.val) + (P * ∑ k : Fin P, d k + ∑ k : Fin P, v k)
          = ((∑ k : Fin P, k.val) + P * ∑ k : Fin P, d k) + ∑ k : Fin P, v k := by rw [Nat.add_assoc]
        _ = (P * ∑ k : Fin P, d k + (∑ k : Fin P, k.val)) + ∑ k : Fin P, v k := by rw [Nat.add_comm (∑ k : Fin P, k.val) (P * ∑ k : Fin P, d k)]
    rw [hr]
    exact h_eq2
  }
  --
  have h_eq4 : P * ∑ k : Fin P, d k + ∑ k : Fin P, v k = P * P := Nat.add_left_cancel h_eq3
  --
  have h_eq5 : ∑ k : Fin P, v k = P * P - P * ∑ k : Fin P, d k := by {
    exact Nat.eq_sub_of_add_eq' h_eq4
  }
  --
  have h_eq6 : ∑ k : Fin P, v k = (P - ∑ k : Fin P, d k) * P := by {
    rw [h_eq5]
    have hz : P * P - P * ∑ k : Fin P, d k = P * (P - ∑ k : Fin P, d k) := by
      exact (Nat.mul_sub_left_distrib P P (∑ k : Fin P, d k)).symm
    rw [hz]
    ring
  }
  --
  exact ⟨(P - ∑ k : Fin P, d k), h_eq6⟩
}

lemma periodic_mod_eq (n_1 n_2 K P : ℕ)
    (h_P : P = n_2 - n_1)
    (hn1_lt_n2 : n_1 < n_2)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k))
    (m : ℕ) (hm : m ≤ P + K) :
    vanEckNthTerm (n_1 + m) = vanEckNthTerm (n_1 + m % P) := by {
  induction m using Nat.strong_induction_on with
  | h m ih =>
    by_cases hlt : m < P
    · rw [Nat.mod_eq_of_lt hlt]
    · have h_ge : m ≥ P := Nat.le_of_not_lt hlt
      have h_sub : n_1 + m = n_2 + (m - P) := by omega
      rw [h_sub]
      have hmK : m - P ≤ K := by omega
      rw [← h_per (m - P) hmK]
      have h_lt : m - P < m := by omega
      have h_ih := ih (m - P) h_lt (by omega)
      rw [h_ih]
      congr 2
      have h_mod : (m - P) % P = m % P := by {
        have h_eq : m = m - P + P := (Nat.sub_add_cancel h_ge).symm
        nth_rw 2 [h_eq]
        rw [Nat.add_mod_right]
      }
      exact h_mod
}

lemma fin_sum_three {n : ℕ} (hn : n = 3) (f : Fin n → ℕ) :
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

lemma vanEck_val_le_P (n_1 n_2 K P k : ℕ)
    (h_P : P = n_2 - n_1)
    (hn1_lt_n2 : n_1 < n_2)
    (h_K_large : K ≥ P + 3)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k))
    (hk1 : 1 ≤ k) (hkK : k ≤ K) :
    vanEckNthTerm (n_2 + k) ≤ P := by {
  have h_gap := vanEck_term_is_matchSearch (n_2 + k) (Nat.le_trans hk1 (Nat.le_add_left k n_2))
  rw [h_gap]
  --
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
  --
  have h_start_lt : n_1 + k - 1 < n_2 + k - 1 := by {
    have hs1 : n_1 + k - 1 = n_1 + (k - 1) := Nat.add_sub_assoc hk1 n_1
    have hs2 : n_2 + k - 1 = n_2 + (k - 1) := Nat.add_sub_assoc hk1 n_2
    rw [hs1, hs2]
    exact Nat.add_lt_add_right hn1_lt_n2 (k - 1)
  }
  --
  have h_bound := matchSearch_upper_bound_of_match (vanEck (n_2 + k - 1)) (n_2 + k - 1) (n_1 + k - 1) h_match h_start_lt
  --
  have hl : (vanEck (n_2 + k - 1)).length = n_2 + k := by {
    have hlen := vanEckLength (n_2 + k - 1)
    have h_sub_add : n_2 + k - 1 + 1 = n_2 + k := Nat.sub_add_cancel (Nat.le_trans hk1 (Nat.le_add_left k n_2))
    rw [h_sub_add] at hlen
    exact hlen
  }
  have hl_sub_1 : (vanEck (n_2 + k - 1)).length - 1 = n_2 + k - 1 := by rw [hl]
  rw [hl_sub_1] at h_bound
  --
  have h_sub : n_2 + k - 1 - (n_1 + k - 1) = P := by {
    have hs1 : n_2 + k - 1 = n_2 + (k - 1) := Nat.add_sub_assoc hk1 n_2
    have hs2 : n_1 + k - 1 = n_1 + (k - 1) := Nat.add_sub_assoc hk1 n_1
    rw [hs1, hs2]
    have hs3 : n_2 + (k - 1) - (n_1 + (k - 1)) = n_2 - n_1 := Nat.add_sub_add_right n_2 (k - 1) n_1
    rw [hs3, h_P]
  }
  rw [h_sub] at h_bound
  exact h_bound
}


lemma vanEck_displacement_bijective (n_1 n_2 K P : ℕ)
    (h_P : P = n_2 - n_1)
    (hn1_lt_n2 : n_1 < n_2)
    (h_K_large : K ≥ P + 3)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k))
    (h_no_zero : ∀ k, 1 ≤ k → k ≤ K → vanEckNthTerm (n_2 + k) ≠ 0) :
    Function.Bijective (fun k : Fin P =>
      (⟨(k.val + P - vanEckNthTerm (n_2 + k.val + 1)) % P, Nat.mod_lt _ (Nat.pos_of_ne_zero (by omega))⟩ : Fin P)) := by {
  have h_val_le_P : ∀ k, 1 ≤ k → k ≤ K → vanEckNthTerm (n_2 + k) ≤ P := by {
    intro k hk1 hkK
    exact vanEck_val_le_P n_1 n_2 K P k h_P hn1_lt_n2 h_K_large h_per hk1 hkK
  }
  have f_inj : ∀ i j, 1 ≤ i → i ≤ P → 1 ≤ j → j ≤ P → i < j →
      (i + P - vanEckNthTerm (n_2 + i)) % P ≠ (j + P - vanEckNthTerm (n_2 + j)) % P := by {
    intro i j hi1 hiP hj1 hjP hij hc
    have h_P_le_K : P ≤ K := by omega
    have hiK : i ≤ K := Nat.le_trans hiP h_P_le_K
    have hjK : j ≤ K := Nat.le_trans hjP h_P_le_K
  --
    have h_vi_le := h_val_le_P i hi1 hiK
    have h_vj_le := h_val_le_P j hj1 hjK
    have h_vi_pos : vanEckNthTerm (n_2 + i) > 0 := Nat.pos_of_ne_zero (h_no_zero i hi1 hiK)
    have h_vj_pos : vanEckNthTerm (n_2 + j) > 0 := Nat.pos_of_ne_zero (h_no_zero j hj1 hjK)
  --
    let A := i + P - vanEckNthTerm (n_2 + i)
    let B := j + P - vanEckNthTerm (n_2 + j)
  --
    have hA_lt : A < 2 * P := by {
      change i + P - vanEckNthTerm (n_2 + i) < 2 * P
      have h_iP_le : i + P ≤ 2 * P := by omega
      have h_sub_lt : i + P - vanEckNthTerm (n_2 + i) < i + P := Nat.sub_lt (by omega) h_vi_pos
      exact Nat.lt_of_lt_of_le h_sub_lt h_iP_le
    }
    have hB_lt : B < 2 * P := by {
      change j + P - vanEckNthTerm (n_2 + j) < 2 * P
      have h_jP_le : j + P ≤ 2 * P := by omega
      have h_sub_lt : j + P - vanEckNthTerm (n_2 + j) < j + P := Nat.sub_lt (by omega) h_vj_pos
      exact Nat.lt_of_lt_of_le h_sub_lt h_jP_le
    }
  --
    have h_cases := mod_eq_cases A B P hA_lt hB_lt hc
  --
    rcases h_cases with h1 | h2 | h3
    · have heq : n_2 + i - vanEckNthTerm (n_2 + i) = n_2 + j - vanEckNthTerm (n_2 + j) := by {
        change i + P - vanEckNthTerm (n_2 + i) = j + P - vanEckNthTerm (n_2 + j) at h1
        have hn1_le : n_1 ≤ n_2 := Nat.le_of_lt hn1_lt_n2
        have h_n2_i : n_2 + i = i + P + n_1 := by omega
        have h_n2_j : n_2 + j = j + P + n_1 := by omega
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
    · have heq : n_2 + i - vanEckNthTerm (n_2 + i) = n_1 + j - vanEckNthTerm (n_1 + j) := by {
        change i + P - vanEckNthTerm (n_2 + i) + P = j + P - vanEckNthTerm (n_2 + j) at h2
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
        have h_vi_le_add : vanEckNthTerm (n_2 + i) ≤ n_2 + i := Nat.le_trans h_vi_le (by omega)
  --
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
  --
        rw [h_left, h_right]
        have h2_add_n1 : i + P - vanEckNthTerm (n_2 + i) + P + n_1 = j + P - vanEckNthTerm (n_2 + j) + n_1 := congrArg (· + n_1) h2
        have hP_add_n1 : P + n_1 = n_2 := by omega
        rw [Nat.add_assoc, hP_add_n1] at h2_add_n1
        exact h2_add_n1
      }
      have h_n1j_pos : vanEckNthTerm (n_1 + j) > 0 := by {
        have h_vj_eq : vanEckNthTerm (n_1 + j) = vanEckNthTerm (n_2 + j) := h_per j hjK
        rw [h_vj_eq]
        exact h_vj_pos
      }
      have h_lt : n_1 + j < n_2 + i := by omega
      have h_unique := vanEck_idx_sub_val_unique (n_1 + j) (n_2 + i) h_n1j_pos h_lt
      exact h_unique heq.symm
    · change j + P - vanEckNthTerm (n_2 + j) + P = i + P - vanEckNthTerm (n_2 + i) at h3
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
  --
  let f : Fin P → Fin P := fun k => ⟨(k.val + P - vanEckNthTerm (n_2 + k.val + 1)) % P, Nat.mod_lt _ (Nat.pos_of_ne_zero (by omega))⟩
  have h_inj : Function.Injective f := by {
    intro i j heq
    have h1 : 1 ≤ i.val + 1 := Nat.le_add_left 1 i.val
    have h2 : i.val + 1 ≤ P := i.isLt
    have h3 : 1 ≤ j.val + 1 := Nat.le_add_left 1 j.val
    have h4 : j.val + 1 ≤ P := j.isLt
    by_cases hlt : i.val + 1 < j.val + 1
    · have hc := f_inj (i.val + 1) (j.val + 1) h1 h2 h3 h4 hlt
      have heq_val : (i.val + P - vanEckNthTerm (n_2 + i.val + 1)) % P = (j.val + P - vanEckNthTerm (n_2 + j.val + 1)) % P := congr_arg Fin.val heq
      have hc_contra : (i.val + 1 + P - vanEckNthTerm (n_2 + i.val + 1)) % P = (j.val + 1 + P - vanEckNthTerm (n_2 + j.val + 1)) % P := by {
        have hi1 : i.val + 1 + P - vanEckNthTerm (n_2 + i.val + 1) = i.val + P - vanEckNthTerm (n_2 + i.val + 1) + 1 := by {
          have hv : vanEckNthTerm (n_2 + i.val + 1) ≤ P := h_val_le_P (i.val + 1) h1 (by omega)
          omega
        }
        have hj1 : j.val + 1 + P - vanEckNthTerm (n_2 + j.val + 1) = j.val + P - vanEckNthTerm (n_2 + j.val + 1) + 1 := by {
          have hv : vanEckNthTerm (n_2 + j.val + 1) ≤ P := h_val_le_P (j.val + 1) h3 (by omega)
          omega
        }
        rw [hi1, hj1]
        calc (i.val + P - vanEckNthTerm (n_2 + i.val + 1) + 1) % P
          _ = ((i.val + P - vanEckNthTerm (n_2 + i.val + 1)) % P + 1 % P) % P := by rw [Nat.add_mod]
          _ = ((j.val + P - vanEckNthTerm (n_2 + j.val + 1)) % P + 1 % P) % P := by rw [heq_val]
          _ = (j.val + P - vanEckNthTerm (n_2 + j.val + 1) + 1) % P := by rw [← Nat.add_mod]
      }
      exact False.elim (hc hc_contra)
    · by_cases hlt2 : j.val + 1 < i.val + 1
      · have hc := f_inj (j.val + 1) (i.val + 1) h3 h4 h1 h2 hlt2
        have heq_val : (j.val + P - vanEckNthTerm (n_2 + j.val + 1)) % P = (i.val + P - vanEckNthTerm (n_2 + i.val + 1)) % P := congr_arg Fin.val heq.symm
        have hc_contra : (j.val + 1 + P - vanEckNthTerm (n_2 + j.val + 1)) % P = (i.val + 1 + P - vanEckNthTerm (n_2 + i.val + 1)) % P := by {
          have hi1 : i.val + 1 + P - vanEckNthTerm (n_2 + i.val + 1) = i.val + P - vanEckNthTerm (n_2 + i.val + 1) + 1 := by {
            have hv : vanEckNthTerm (n_2 + i.val + 1) ≤ P := h_val_le_P (i.val + 1) h1 (by omega)
            omega
          }
          have hj1 : j.val + 1 + P - vanEckNthTerm (n_2 + j.val + 1) = j.val + P - vanEckNthTerm (n_2 + j.val + 1) + 1 := by {
            have hv : vanEckNthTerm (n_2 + j.val + 1) ≤ P := h_val_le_P (j.val + 1) h3 (by omega)
            omega
          }
          rw [hj1, hi1]
          calc (j.val + P - vanEckNthTerm (n_2 + j.val + 1) + 1) % P
            _ = ((j.val + P - vanEckNthTerm (n_2 + j.val + 1)) % P + 1 % P) % P := by rw [Nat.add_mod]
            _ = ((i.val + P - vanEckNthTerm (n_2 + i.val + 1)) % P + 1 % P) % P := by rw [heq_val]
            _ = (i.val + P - vanEckNthTerm (n_2 + i.val + 1) + 1) % P := by rw [← Nat.add_mod]
        }
        exact False.elim (hc hc_contra)
      · have heq_val : i.val + 1 = j.val + 1 := by omega
        exact Fin.eq_of_val_eq (Nat.add_right_cancel heq_val)
  }
  exact Finite.injective_iff_bijective.mp h_inj
}

lemma cute_reciprocal_sum : (1/3 : ℚ) + 1/4 + 1/5 + 1/6 + 1/20 = 1 := by norm_num

/--
The `combinatorial_squeeze` theorem provides the bridge between the local periodicity
assumptions of the Van Eck sequence and the Mirsky-Newman exact cover contradiction.

Informally:
If the sequence falls into a perfectly repeating cycle of length `P`, we can map the step sizes
(the values of the sequence) into an exact cover of the cycle.
The `h_no_intermediate` constraint (the Van Eck "Most Recent Occurrence" rule) ensures that
for any value `X` in the sequence, the gap between its occurrences is exactly `X`.
Because every gap is strictly `X` and there are no intermediate occurrences, the occurrences
of `X` must form exactly one perfect arithmetic progression of step size `X`.

The Mirsky-Newman theorem dictates that no finite cycle can be perfectly partitioned by
distinct step sizes where the minimum step is ≥ 3. Since `h_no1` and `h_no2` eliminate
step sizes 1 and 2, the exact cover is impossible, yielding a contradiction (`False`).
-/
lemma combinatorial_squeeze (P : ℕ) (hP : P ≥ 4)
    (v : ℕ → ℕ)
    (f : Fin P → Fin P)
    (hv1 : ∀ k : Fin P, 1 ≤ v (k.val + 1))
    (hvP : ∀ k : Fin P, v (k.val + 1) ≤ P)
    (h_no2 : ∀ k : Fin P, v (k.val + 1) ≠ 2)
    (h_no1 : ∃ k : Fin P, v (k.val + 1) ≠ 1)
    (hf : ∀ k : Fin P, (f k).val = (k.val + P - v (k.val + 1)) % P)
    (hbij : Function.Bijective f)
    (h_recent : ∀ k : Fin P, v ((f k).val + 1) = v (k.val + 1))
    (h_no_intermediate : ∀ k : Fin P, ∀ i < v (k.val + 1), i > 0 → v ((k.val + P - i) % P + 1) ≠ v (k.val + 1)) :
    False := by {
  have hP_pos : P > 0 := by omega
  --
  let S : Finset ℕ := Finset.image (fun (k : Fin P) => v (k.val + 1)) Finset.univ
  let cover : ℕ → Finset (Fin P) := fun X => Finset.filter (fun k => v (k.val + 1) = X) Finset.univ
  --
  have h_min : ∀ X ∈ S, X ≥ 3 := by {
    intro X hX
    have ⟨k, _, hk_eq⟩ := Finset.mem_image.mp hX
    have hX_ne_2 : X ≠ 2 := by rw [← hk_eq]; exact h_no2 k
    have hX_ne_1 : X ≠ 1 := by {
      intro hX_1
      have ⟨k_no1, hk_no1⟩ := h_no1
      have h1_in : ∃ k : Fin P, v (k.val + 1) = 1 := by {
        use k
        rw [hk_eq, hX_1]
      }
      have h_no_int : ∀ k_inner : Fin P, v (k_inner.val + 1) = 1 → ∀ i < 1, i > 0 → v ((k_inner.val + P - i) % P + 1) ≠ 1 := by {
        intro k_inner _ i hi hi_pos
        omega
      }
      have h_fib_sum := vanEck_fiber_sum P hP v f hf hbij h_recent 1 (by omega) (by omega) h1_in h_no_int
      rw [mul_one] at h_fib_sum
      have h_card_eq : (Finset.univ.filter (fun k : Fin P => v (k.val + 1) = 1)).card = Fintype.card (Fin P) := by {
        rw [Fintype.card_fin]
        exact h_fib_sum
      }
      have h_eq_univ : Finset.univ.filter (fun k : Fin P => v (k.val + 1) = 1) = Finset.univ := by {
        apply Finset.eq_of_subset_of_card_le (Finset.filter_subset _ _)
        rw [h_card_eq, Finset.card_univ]
      }
      have h_mem : k_no1 ∈ Finset.univ.filter (fun k : Fin P => v (k.val + 1) = 1) := by {
        rw [h_eq_univ]
        exact Finset.mem_univ k_no1
      }
      have h_v1 : v (k_no1.val + 1) = 1 := by {
        have h_mem_filter := Finset.mem_filter.mp h_mem
        exact h_mem_filter.right
      }
      exact hk_no1 h_v1
    }
    have hX_ge_1 : X ≥ 1 := by rw [← hk_eq]; exact hv1 k
    omega
  }
  --
  have h_div : ∀ X ∈ S, X ∣ P := by {
    intro X hX
    have ⟨k, _, hk_eq⟩ := Finset.mem_image.mp hX
    have h_in : ∃ k : Fin P, v (k.val + 1) = X := ⟨k, hk_eq⟩
    have h_no_int : ∀ k : Fin P, v (k.val + 1) = X → ∀ i < X, i > 0 → v ((k.val + P - i) % P + 1) ≠ X := by {
      intro k_inner hk_inner i hi hi_pos
      have hc := h_no_intermediate k_inner i (by rw [hk_inner]; exact hi) hi_pos
      rw [hk_inner] at hc
      exact hc
    }
    have h_sum := vanEck_fiber_sum P hP v f hf hbij h_recent X (by { have hk := hv1 k; rw [hk_eq] at hk; omega }) (by { have hk := hvP k; rw [hk_eq] at hk; exact hk }) h_in h_no_int
    have h_mul_comm : X * (Finset.filter (fun k : Fin P => v (k.val + 1) = X) Finset.univ).card = P := by
      rw [mul_comm]
      exact h_sum
    exact ⟨(Finset.filter (fun k : Fin P => v (k.val + 1) = X) Finset.univ).card, h_mul_comm.symm⟩
  }
  --
  have h_partition : ∀ k : Fin P, ∃! X, X ∈ S ∧ k ∈ cover X := by {
    intro k
    use v (k.val + 1)
    constructor
    · constructor
      · apply Finset.mem_image.mpr
        exact ⟨k, Finset.mem_univ k, rfl⟩
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ k, rfl⟩
    · intro Y ⟨_, hY_cover⟩
      exact (Finset.mem_filter.mp hY_cover).2.symm
  }
  --
  have h_ap : ∀ X ∈ S, ∃ start : Fin P, cover X = Finset.filter (fun (k : Fin P) => ∃ i : ℕ, k.val = (start.val + i * X) % P) Finset.univ := by {
    intro X hX
    have ⟨k, _, hk_eq⟩ := Finset.mem_image.mp hX
    have h_in : ∃ k : Fin P, v (k.val + 1) = X := ⟨k, hk_eq⟩
    have h_no_int : ∀ k : Fin P, v (k.val + 1) = X → ∀ i < X, i > 0 → v ((k.val + P - i) % P + 1) ≠ X := by {
      intro k_inner hk_inner i hi hi_pos
      have hc := h_no_intermediate k_inner i (by rw [hk_inner]; exact hi) hi_pos
      rw [hk_inner] at hc
      exact hc
    }
    have h_is_ap := vanEck_fiber_is_ap P hP v f hf hbij h_recent X (by { have hk := hv1 k; rw [hk_eq] at hk; omega }) (by { have hk := hvP k; rw [hk_eq] at hk; exact hk }) h_in h_no_int
    let k0 := Classical.choose h_in
    use k0
    have h_div_X : X ∣ P := h_div X hX
    have h_L : P / Nat.gcd P X = P / X := by {
      congr 1
      exact Nat.gcd_eq_right h_div_X
    }
    have h_L_pos : P / Nat.gcd P X > 0 := by {
      rw [h_L]
      exact Nat.div_pos (by { have hk := hvP k; rw [hk_eq] at hk; exact hk }) (by { have hk := hv1 k; rw [hk_eq] at hk; omega })
    }
    let L := P / Nat.gcd P X
    let orbit := Finset.image (fun n : Fin L => (⟨(k0.val + P - (n.val * X) % P) % P, Nat.mod_lt _ hP_pos⟩ : Fin P)) Finset.univ
    have h_cov_eq_orb : cover X = orbit := h_is_ap
    have h_orb_sub_filter : orbit ⊆ Finset.filter (fun (k : Fin P) => ∃ i : ℕ, k.val = (k0.val + i * X) % P) Finset.univ := by {
      intro y hy
      rw [Finset.mem_image] at hy
      rcases hy with ⟨n, _, hn_eq⟩
      rw [Finset.mem_filter]
      constructor
      · exact Finset.mem_univ y
      · use L - n.val
        have hn_lt : n.val * X < L * X := by {
          have h_lt_L : n.val < L := n.isLt
          have hX_pos : X > 0 := by { have hk := hv1 k; rw [hk_eq] at hk; omega }
          exact Nat.mul_lt_mul_of_pos_right h_lt_L hX_pos
        }
        have h_LX_eq_P : L * X = P := by {
          change P / P.gcd X * X = P
          rw [h_L]
          exact Nat.div_mul_cancel h_div_X
        }
        have h_mod_val : (n.val * X) % P = n.val * X := by {
          rw [h_LX_eq_P] at hn_lt
          exact Nat.mod_eq_of_lt hn_lt
        }
        have h_val : y.val = (k0.val + P - n.val * X) % P := by {
          rw [← hn_eq]
          dsimp
          rw [h_mod_val]
        }
        rw [h_val]
        congr 1
        have h_sub_X : (L - n.val) * X = P - n.val * X := by {
          rw [Nat.sub_mul, h_LX_eq_P]
        }
        rw [h_sub_X]
        omega
    }
    have h_filter_sub_img : Finset.filter (fun (k : Fin P) => ∃ i : ℕ, k.val = (k0.val + i * X) % P) Finset.univ ⊆
        Finset.image (fun r : Fin L => (⟨(k0.val + r.val * X) % P, Nat.mod_lt _ hP_pos⟩ : Fin P)) Finset.univ := by {
      intro y hy
      rw [Finset.mem_filter] at hy
      rcases hy.2 with ⟨i, hi_eq⟩
      rw [Finset.mem_image]
      let r_val := i % L
      have hr_lt : r_val < L := Nat.mod_lt _ h_L_pos
      let r : Fin L := ⟨r_val, hr_lt⟩
      use r
      constructor
      · exact Finset.mem_univ r
      · apply Fin.eq_of_val_eq
        rw [hi_eq]
        have h_LX_eq_P : L * X = P := by {
          change P / P.gcd X * X = P
          rw [h_L]
          exact Nat.div_mul_cancel h_div_X
        }
        have h_eq_mod : (i * X) % P = (r.val * X) % P := by {
          rw [← h_LX_eq_P]
          change (i * X) % (L * X) = (r_val * X) % (L * X)
          rw [Nat.mul_mod_mul_right, Nat.mul_mod_mul_right]
          dsimp [r_val]
          rw [Nat.mod_mod]
        }
        have h_add : (k0.val + r.val * X) % P = (k0.val + i * X) % P := by {
          rw [Nat.add_mod, ← h_eq_mod, ← Nat.add_mod]
        }
        exact h_add
    }
    have h_card_le : (Finset.filter (fun (k : Fin P) => ∃ i : ℕ, k.val = (k0.val + i * X) % P) Finset.univ).card ≤ (cover X).card := by {
      have h1 : (Finset.filter (fun (k : Fin P) => ∃ i : ℕ, k.val = (k0.val + i * X) % P) Finset.univ).card ≤
          (Finset.image (fun r : Fin L => (⟨(k0.val + r.val * X) % P, Nat.mod_lt _ hP_pos⟩ : Fin P)) Finset.univ).card := Finset.card_le_card h_filter_sub_img
      have h2 : (Finset.image (fun r : Fin L => (⟨(k0.val + r.val * X) % P, Nat.mod_lt _ hP_pos⟩ : Fin P)) Finset.univ).card ≤ L := by {
        have h_le := Finset.card_image_le (f := fun r : Fin L => (⟨(k0.val + r.val * X) % P, Nat.mod_lt _ hP_pos⟩ : Fin P)) (s := Finset.univ)
        rw [Finset.card_univ, Fintype.card_fin] at h_le
        exact h_le
      }
      have h3 : L = orbit.card := by {
        have h_inj : Function.Injective (fun n : Fin L => (⟨(k0.val + P - (n.val * X) % P) % P, Nat.mod_lt _ hP_pos⟩ : Fin P)) := by {
          intro n1 n2 heq
          have h_val : (k0.val + P - (n1.val * X) % P) % P = (k0.val + P - (n2.val * X) % P) % P := by injection heq
          haveI : NeZero P := ⟨by omega⟩
          have h_eq_nat := orbit_inj P k0.val X n1.val n2.val n1.isLt n2.isLt h_val
          exact Fin.eq_of_val_eq h_eq_nat
        }
        rw [Finset.card_image_of_injective Finset.univ h_inj, Finset.card_univ, Fintype.card_fin]
      }
      rw [h_cov_eq_orb]
      omega
    }
    exact Finset.eq_of_subset_of_card_le (by { rw [h_cov_eq_orb]; exact h_orb_sub_filter }) h_card_le
  }
  --
  exact mirsky_newman_exact_cover P hP_pos S h_min h_div cover h_partition h_ap
}

/--
In any locally periodic window `a(n_1 + k) = a(n_2 + k)` (`0 ≤ k ≤ K`) with `n_1 < n_2`,
every term `a(n_2 + k)` for `1 ≤ k ≤ K` is strictly positive because `a(n_2 + k - 1)` already
appeared earlier at `n_1 + k - 1 < n_2 + k - 1`.
-/
lemma local_period_no_zero (n_1 n_2 K : ℕ)
    (hn1_lt_n2 : n_1 < n_2)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k)) :
    ∀ k, 1 ≤ k → k ≤ K → vanEckNthTerm (n_2 + k) ≠ 0 := by {
  intro k hk1 hkK h_zero
  have h_n2_pos : n_2 ≥ 1 := Nat.succ_le_of_lt (Nat.lt_of_le_of_lt (Nat.zero_le n_1) hn1_lt_n2)
  have h1 : n_2 + k ≥ 2 := Nat.add_le_add h_n2_pos hk1
  have h_m2 : n_2 + k - 2 + 2 = n_2 + k := Nat.sub_add_cancel h1
  have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new (n_2 + k - 2)
  rw [h_m2] at h_iff
  have h_new := h_iff.mp h_zero
  have h_m1 : n_2 + k - 2 + 1 = n_2 + k - 1 := Nat.sub_add_cancel (Nat.le_sub_one_of_lt h1)
  rw [h_m1] at h_new
  have h_sub1 : n_1 + k - 1 = n_1 + (k - 1) := Nat.add_sub_assoc hk1 n_1
  have h_sub2 : n_2 + k - 1 = n_2 + (k - 1) := Nat.add_sub_assoc hk1 n_2
  have h_prev_eq : vanEckNthTerm (n_1 + k - 1) = vanEckNthTerm (n_2 + k - 1) := by {
    rw [h_sub1, h_sub2]
    exact h_per (k - 1) (Nat.le_trans (Nat.sub_le k 1) hkK)
  }
  have h_not_new := h_new (n_1 + k - 1) (by {
    rw [h_sub1, h_sub2]
    exact Nat.add_lt_add_right hn1_lt_n2 (k - 1)
  })
  exact h_not_new h_prev_eq
}

/--
Any natural number `X ≤ 2P - 2` whose remainder modulo `P ≥ 1` equals `P - 1`
must equal `P - 1` itself.
-/
lemma mod_eq_pred_of_le_two_mul_sub_two (X P : ℕ)
    (hP : P ≥ 1) (hX : X ≤ 2 * P - 2) (hmod : X % P = P - 1) :
    X = P - 1 := by {
  by_cases hlt : X < P
  · have hm : X % P = X := Nat.mod_eq_of_lt hlt
    rw [hm] at hmod
    exact hmod
  · exfalso
    have hge : P ≤ X := Nat.le_of_not_lt hlt
    have hsub_lt : X - P < P := by { omega }
    have hm1 : X % P = (X - P) % P := Nat.mod_eq_sub_mod hge
    have hm2 : (X - P) % P = X - P := Nat.mod_eq_of_lt hsub_lt
    rw [hm1, hm2] at hmod
    omega
}

/--
Backward determinism across a local period: surjectivity of the displacement bijection
`f : Fin P → Fin P` (`P = n_2 - n_1`) hits `P - 1`, yielding an offset `k < P` with
`a(n_2 + k + 1) = k + 1 = a(n_1 + k + 1)` that steps backward to `a(n_1 - 1) = a(n_2 - 1)`.
-/
lemma local_period_step_backward (n_1 n_2 K : ℕ)
    (hn1_pos : n_1 ≥ 1)
    (hn1_lt_n2 : n_1 < n_2)
    (h_K_large : K ≥ n_2 - n_1 + 3)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k)) :
    vanEckNthTerm (n_1 - 1) = vanEckNthTerm (n_2 - 1) := by {
  let P := n_2 - n_1
  have hP_pos : P ≥ 1 := Nat.sub_pos_of_lt hn1_lt_n2
  have h_no_zero := local_period_no_zero n_1 n_2 K hn1_lt_n2 h_per
  have f_bij :=
    vanEck_displacement_bijective n_1 n_2 K P rfl hn1_lt_n2 h_K_large h_per h_no_zero
  rcases f_bij.2 ⟨P - 1, by { omega }⟩ with ⟨k, hk_eq⟩
  have hk_mod : (k.val + P - vanEckNthTerm (n_2 + k.val + 1)) % P = P - 1 :=
    congrArg Fin.val hk_eq
  have hk1 : 1 ≤ k.val + 1 := Nat.le_add_left 1 k.val
  have hkK : k.val + 1 ≤ K := by { have hklt := k.isLt; omega }
  have hd_pos : vanEckNthTerm (n_2 + k.val + 1) ≥ 1 :=
    Nat.pos_of_ne_zero (h_no_zero (k.val + 1) hk1 hkK)
  have hd_le_P : vanEckNthTerm (n_2 + k.val + 1) ≤ P :=
    vanEck_val_le_P n_1 n_2 K P (k.val + 1) rfl hn1_lt_n2 h_K_large h_per hk1 hkK
  have h_num_le : k.val + P - vanEckNthTerm (n_2 + k.val + 1) ≤ 2 * P - 2 := by {
    have hklt := k.isLt; omega
  }
  have h_num_eq : k.val + P - vanEckNthTerm (n_2 + k.val + 1) = P - 1 :=
    mod_eq_pred_of_le_two_mul_sub_two _ P hP_pos h_num_le hk_mod
  have hd_eq : vanEckNthTerm (n_2 + k.val + 1) = k.val + 1 := by {
    have hklt := k.isLt; omega
  }
  have h_n1_step : vanEckNthTerm (n_1 + k.val + 1) = k.val + 1 := by {
    have hp := h_per (k.val + 1) hkK
    have ha1 : n_1 + (k.val + 1) = n_1 + k.val + 1 := by { omega }
    have ha2 : n_2 + (k.val + 1) = n_2 + k.val + 1 := by { omega }
    rw [ha1, ha2] at hp
    rw [hp]
    exact hd_eq
  }
  have hg1 := gap_determines_value (n := 1) (n_1 + k.val) (by { omega }) (k.val + 1)
    (Nat.le_refl 1) h_n1_step (by { omega })
  have hg2 := gap_determines_value (n := 1) (n_2 + k.val) (by { omega }) (k.val + 1)
    (Nat.le_refl 1) hd_eq (by { omega })
  have hs1 : n_1 + k.val - (k.val + 1) = n_1 - 1 := by { omega }
  have hs2 : n_2 + k.val - (k.val + 1) = n_2 - 1 := by { omega }
  rw [hs1] at hg1
  rw [hs2] at hg2
  have hp0 := h_per k.val (by { have hklt := k.isLt; omega })
  rw [← hg1, ← hg2]
  exact hp0
}

/--
No local period of length `K ≥ (n_2 - n_1) + 3` can ever occur anywhere in the Van Eck
sequence: stepping the periodic window backward to `n_1 = 0` forces `a(n_2 - n_1 + 1) = a(1) = 0`,
contradicting `local_period_no_zero`.
-/
lemma local_period_impossible_unconditional (n_1 : ℕ) :
    ∀ n_2 K : ℕ, n_1 < n_2 → K ≥ n_2 - n_1 + 3 →
    (∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k)) → False := by {
  induction n_1 with
  | zero =>
    intro n_2 K hn1_lt_n2 h_K_large h_per
    have h_no_zero := local_period_no_zero 0 n_2 K hn1_lt_n2 h_per
    have hk1_le_K : 1 ≤ K := by { omega }
    have h_per_1 := h_per 1 hk1_le_K
    have h_0_add : 0 + 1 = 1 := rfl
    rw [h_0_add] at h_per_1
    have hv1 : vanEckNthTerm 1 = 0 := rfl
    rw [hv1] at h_per_1
    exact h_no_zero 1 (Nat.le_refl 1) hk1_le_K h_per_1.symm
  | succ m ih =>
    intro n_2 K hn1_lt_n2 h_K_large h_per
    have hm_pos : m + 1 ≥ 1 := Nat.le_add_left 1 m
    have h_prev := local_period_step_backward (m + 1) n_2 K hm_pos hn1_lt_n2 h_K_large h_per
    have hm_sub : m + 1 - 1 = m := rfl
    rw [hm_sub] at h_prev
    have h_per' : ∀ k ≤ K + 1, vanEckNthTerm (m + k) = vanEckNthTerm (n_2 - 1 + k) := by {
      intro k hk
      cases k with
      | zero =>
        simp only [Nat.add_zero]
        exact h_prev
      | succ j =>
        have hj : j ≤ K := by { omega }
        have hp := h_per j hj
        have ha1 : m + (j + 1) = m + 1 + j := by { omega }
        have ha2 : n_2 - 1 + (j + 1) = n_2 + j := by { omega }
        rw [ha1, ha2]
        exact hp
    }
    exact ih (n_2 - 1) (K + 1) (by { omega }) (by { omega }) h_per'
}

lemma finite_cycle_gap_collapse (n_1 n_2 K : ℕ)
    (hn1_lt_n2 : n_1 < n_2)
    (h_K_large : K ≥ n_2 - n_1 + 3)
    (_h_no_zero : ∀ k, 1 ≤ k → k ≤ K → vanEckNthTerm (n_2 + k) ≠ 0)
    (_h_no_twos : ∀ m > n_1, vanEckNthTerm m ≠ 2)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k)) : False := by {
  exact local_period_impossible_unconditional n_1 n_2 K hn1_lt_n2 h_K_large h_per
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
    (_h_no_twos : ∀ m > n_1, vanEckNthTerm m ≠ 2)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k)) :
    False := by {
  exact local_period_impossible_unconditional n_1 n_2 K hn1_lt_n2 h_K_large h_per
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
  --
  -- From h_dense, we obtain a dense block far out in the sequence.
  have h_max_occ := exists_max_first_occurrence (B + 1)
  rcases h_max_occ with ⟨N_max, hN_max⟩
  let N' := max N N_max
  have h_ex := h_dense N'
  rcases h_ex with ⟨start, h_start_gt, h_block⟩
  --
  -- By our stepping stone, this dense block has NO alternating pairs.
  have h_no_alt := dense_block_without_twos_has_no_alternating_pairs B ((B + 1) ^ (B + 1) + (B + 1) + 5) start h_block (by
    intro m hm_gt
    exact h_no_twos m (Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_max_left N N_max) h_start_gt) hm_gt)
  )
  --
  -- Because the block is bounded strictly by B + 1, we can apply our
  -- local pigeonhole state collision theorem to extract a massive state repetition!
  -- We use the padding trick: we apply it to the FIRST part of the block to ensure n_2 +
-- 3 is still inside!
  let G_small := (B + 1) ^ (B + 1) + (B + 1) + 2
  --
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
  --
  have hB1_gt : B + 1 > 1 := Nat.add_lt_add_right hB_gt 1
  --
  have h_coll := local_pigeonhole_state_collision start G_small (B + 1) h_bound hB1_gt (Nat.le_refl _)
  --
  rcases h_coll with ⟨n_1, n_2, hn1_ge, hn1_lt_n2, hn2_lt, h_state_eq⟩
  --
  -- We now have n_1 < n_2 with exactly matching states of length B+1!
  -- This forces a local periodicity that will inevitably break h_no_alt.
  let K := n_2 - n_1 + 3
  --
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
  --
      have h5 : n_2 - start < G_small - 1 := Nat.sub_lt_left_of_lt_add (Nat.le_trans (Nat.le_add_right start (B + 1)) hn1_ge |>.trans (Nat.le_of_lt hn1_lt_n2)) hn2_lt
      have h6 : n_2 - start + 3 < G_small - 1 + 3 := Nat.add_lt_add_right h5 3
      have h7 : G_small - 1 + 3 ≤ G_small + 3 := Nat.add_le_add_right (Nat.sub_le G_small 1) 3
      have h8 : G_small + 3 = (B + 1) ^ (B + 1) + (B + 1) + 5 := rfl
      exact Nat.lt_of_le_of_lt h3 (Nat.lt_of_lt_of_le h6 (by rw [h8]; exact h7))
  --
    have h_le := h_block (n_1 + k - start) hk_lt_G
    have h_k_eq : start + (n_1 + k - start) = n_1 + k := Nat.add_sub_cancel' hk_ge
    rw [h_k_eq] at h_le
    exact Nat.lt_succ_of_le h_le
  --
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
          have hh : start ≤ n_2 := Nat.le_trans (Nat.le_add_right start (B + 1)) hn1_ge |>.trans (Nat.le_of_lt hn1_lt_n2)
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
  --
  have hn1_ge_B : B + 1 ≤ n_1 := Nat.le_trans (Nat.le_add_left (B + 1) start) hn1_ge
  have hn2_ge_B : B + 1 ≤ n_2 := Nat.le_trans hn1_ge_B (Nat.le_of_lt hn1_lt_n2)
  --
  have h_per := local_forward_periodicity_left (B + 1) n_1 n_2 K h_state_eq hn1_ge_B hn2_ge_B (Nat.zero_lt_succ B) hd1_lt hd1_pos
  --
  have h_contra := local_periodicity_impossible n_1 n_2 K hn1_lt_n2 (Nat.le_refl _) (by {
    intro m hm
    have h1 : start ≤ n_1 := Nat.le_trans (Nat.le_add_right start (B + 1)) hn1_ge
    have h2 : start < m := Nat.lt_of_le_of_lt h1 hm
    exact h_no_twos m (Nat.lt_trans (Nat.lt_of_le_of_lt (Nat.le_max_left N N_max) h_start_gt) h2)
  })
  -- Periodicity evaluation matches.
  have h_per_eval : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k) := fun k hk => (h_per k hk).right
  exact h_contra h_per_eval
}

lemma sequence_bounded_implies_dense (M : ℕ)
    (h_bound : ∀ m, vanEckNthTerm m ≤ M) :
    DenseSmallNumbers M ((M + 1) ^ (M + 1) + (M + 1) + 5) := by {
  intro N_test
  use N_test + 1
  constructor
  · exact Nat.lt_succ_self N_test
  · intro i hi
    exact h_bound (N_test + 1 + i)
}

/--
Infinitely many step-2 repeats (`a(i) = a(i + 2)`) immediately force `InfiniteTwos`.
-/
lemma infinite_alternating_pairs_implies_infinite_twos
    (h_inf : ∀ N, ∃ i > N, vanEckNthTerm i = vanEckNthTerm (i + 2)) :
    InfiniteTwos := by {
  intro N
  rcases h_inf N with ⟨i, hi_gt, h_eq⟩
  refine ⟨i + 3, ?_, eq_add_two_implies_next_two i h_eq⟩
  omega
}

/--
If the even-index subsequence `k ↦ a(2k)` stutters infinitely often, `InfiniteTwos` holds.
-/
lemma infinite_even_track_stutters_implies_infinite_twos
    (h_even : ∀ N, ∃ k > N, vanEckNthTerm (2 * k) = vanEckNthTerm (2 * (k + 1))) :
    InfiniteTwos := by {
  apply infinite_alternating_pairs_implies_infinite_twos
  intro N
  rcases h_even N with ⟨k, hk_gt, h_eq⟩
  have h_step : 2 * (k + 1) = 2 * k + 2 := by { omega }
  rw [h_step] at h_eq
  refine ⟨2 * k, ?_, h_eq⟩
  omega
}

/--
If the odd-index subsequence `k ↦ a(2k + 1)` stutters infinitely often, `InfiniteTwos` holds.
-/
lemma infinite_odd_track_stutters_implies_infinite_twos
    (h_odd : ∀ N, ∃ k > N, vanEckNthTerm (2 * k + 1) = vanEckNthTerm (2 * (k + 1) + 1)) :
    InfiniteTwos := by {
  apply infinite_alternating_pairs_implies_infinite_twos
  intro N
  rcases h_odd N with ⟨k, hk_gt, h_eq⟩
  have h_step : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by { omega }
  rw [h_step] at h_eq
  refine ⟨2 * k + 1, ?_, h_eq⟩
  omega
}

/--
Direct Late-Zero Cut Bridge to `InfiniteTwos` (Bypassing `no_twos_implies_bounded`):
If every zero cut `z_0 ≥ 3` is refuted at some finite `fuel` (`refuteNoTwosZ0Fast z_0 fuel = true`),
then `infinite_zeros_vanEck` + `refuteNoTwosZ0Fast_sound` immediately yields `InfiniteTwos`.
-/
theorem infinite_twos_of_zero_cut_refuted
    (h_cut : ∀ z_0 ≥ 3, ∃ fuel, refuteNoTwosZ0Fast z_0 fuel = true) :
    InfiniteTwos := by {
  intro N
  rcases infinite_zeros_vanEck (max N 2) with ⟨z_0, hz0_gt, hz0_zero⟩
  rcases h_cut z_0 (by { omega }) with ⟨fuel, h_cert⟩
  have h0 : vanEckNthTerm 0 = 0 := rfl
  have h1 : vanEckNthTerm 1 = 0 := rfl
  rcases refuteNoTwosZ0Fast_sound vanEckNthTerm z_0 fuel (by { omega }) h0 h1 hz0_zero
    (vanEckNthTerm_isVanEckFrom z_0) h_cert with ⟨k, hk_gt, _, hk_two⟩
  exact ⟨k, by { omega }, hk_two⟩
}

/--
Counterexample to the unguarded deterministic-tail statement without `no_stutter_one`:
`g n := if n = 0 then 0 else 1` satisfies `g 0 = 0`, `∀ j ≥ 1, g j ≠ 2`, and `IsVanEckFrom g 2`.
-/
lemma const_one_tail_counterexample :
    let g : ℕ → ℕ := fun n => if n = 0 then 0 else 1
    g 0 = 0 ∧ (∀ j ≥ 1, g j ≠ 2) ∧ IsVanEckFrom g 2 := by {
  refine ⟨rfl, ?_, ?_⟩
  · intro j hj
    have hj0 : j ≠ 0 := by { omega }
    dsimp only
    rw [if_neg hj0]
    decide
  · intro m hm
    cases m with
    | zero => omega
    | succ k =>
      have hk0 : k ≠ 0 := by { omega }
      have hkm : k + 1 ≠ 0 := by { omega }
      have hocc : lastOccBeforeFn (fun n => if n = 0 then 0 else 1) (k + 1) 1 = some k := by {
        simp only [lastOccBeforeFn, if_neg hk0, ↓reduceIte]
      }
      dsimp only
      rw [if_neg (by { omega } : k + 2 ≠ 0), if_neg hkm, hocc]
      change 1 = k + 1 - k
      omega
}

lemma mem_of_mem_removeFirst (x y : ℕ) (ys : List ℕ) (h : y ∈ removeFirst x ys) : y ∈ ys := by {
  induction ys with
  | nil => simp [removeFirst] at h
  | cons z zs ih =>
    simp only [removeFirst] at h
    cases hbeq : Nat.beq x z with
    | true =>
      rw [hbeq] at h
      simp only [↓reduceIte] at h
      exact List.mem_cons.mpr (Or.inr h)
    | false =>
      rw [hbeq] at h
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons] at h
      rcases h with rfl | htl
      · exact List.mem_cons.mpr (Or.inl rfl)
      · exact List.mem_cons.mpr (Or.inr (ih htl))
}

lemma nodup_removeFirst (x : ℕ) (ys : List ℕ) (hnd : ys.Nodup) :
    (removeFirst x ys).Nodup := by {
  induction ys with
  | nil => exact List.nodup_nil
  | cons z zs ih =>
    rcases List.nodup_cons.mp hnd with ⟨hz_nin, hnd_zs⟩
    simp only [removeFirst]
    cases hbeq : Nat.beq x z with
    | true =>
      simp only [↓reduceIte]
      exact hnd_zs
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte]
      exact List.nodup_cons.mpr ⟨fun hm => hz_nin (mem_of_mem_removeFirst x z zs hm), ih hnd_zs⟩
}

lemma not_mem_removeFirst_of_nodup (x : ℕ) (ys : List ℕ) (hnd : ys.Nodup) :
    x ∉ removeFirst x ys := by {
  induction ys with
  | nil => simp [removeFirst]
  | cons z zs ih =>
    rcases List.nodup_cons.mp hnd with ⟨hz_nin, hnd_zs⟩
    simp only [removeFirst]
    cases hbeq : Nat.beq x z with
    | true =>
      simp only [↓reduceIte]
      rw [Nat.beq_eq.mp hbeq]
      exact hz_nin
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, List.mem_cons]
      rintro (rfl | htl)
      · exact Bool.noConfusion (hbeq.symm.trans (Nat.beq_eq.mpr rfl))
      · exact ih hnd_zs htl
}

lemma dfs_ray_freeSeq_nodup_and_mono {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) :
    (∀ t, (R.freeSeq t).Nodup) ∧
      (∀ t1 t2 p, t1 ≤ t2 → p ∈ R.freeSeq t2 → p ∈ R.freeSeq t1) := by {
  have h_step_sub : ∀ t p, p ∈ R.freeSeq (t + 1) → p ∈ R.freeSeq t := by {
    intro t p hp
    rcases R.h_step t with ⟨_, _, _, _, _, hfr⟩ | ⟨_, _, _, hfr⟩ | ⟨q, _, _, _, _, _, hfr⟩
    · rw [hfr] at hp
      exact hp
    · rw [hfr] at hp
      exact hp
    · rw [hfr] at hp
      exact mem_of_mem_removeFirst q p (R.freeSeq t) hp
  }
  refine ⟨?_, ?_⟩
  · intro t
    induction t with
    | zero =>
      rw [R.h_init_free]
      exact List.Nodup.filter _ List.nodup_range
    | succ s ih =>
      rcases R.h_step s with ⟨_, _, _, _, _, hfr⟩ | ⟨_, _, _, hfr⟩ | ⟨q, _, _, _, _, _, hfr⟩
      · rw [hfr]
        exact ih
      · rw [hfr]
        exact ih
      · rw [hfr]
        exact nodup_removeFirst q (R.freeSeq s) ih
  · intro t1 t2 p hle hp
    induction t2 with
    | zero =>
      have ht0 : t1 = 0 := by { omega }
      rw [ht0]
      exact hp
    | succ s ih =>
      rcases eq_or_lt_of_le hle with rfl | hlt
      · exact hp
      · exact ih (by { omega }) (h_step_sub s p hp)
}

lemma dfs_ray_freeSeq_invariant {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) :
    (∀ t, (R.freeSeq t).Nodup) ∧
      (∀ t1 t2 p, t1 ≤ t2 → p ∈ R.freeSeq t2 → p ∈ R.freeSeq t1) ∧
      (∀ t p, p ∈ R.freeSeq t → 2 ≤ p ∧ p < z_0 ∧ p ≠ R.z_prev) := by {
  rcases dfs_ray_freeSeq_nodup_and_mono R with ⟨h_nd, h_mono⟩
  refine ⟨h_nd, h_mono, ?_⟩
  intro t p hp
  have hp0 := h_mono 0 t p (Nat.zero_le t) hp
  rw [R.h_init_free, List.mem_filter, List.mem_range] at hp0
  have hc := Eq.mp (Bool.and_eq_true _ _) hp0.2
  have hge2 : 2 ≤ p := Nat.ble_eq.mp hc.1
  have hne : p ≠ R.z_prev := fun heq => by {
    have hb := Nat.beq_eq.mpr heq
    rw [hb] at hc
    nomatch hc.2
  }
  exact ⟨hge2, hp0.1, hne⟩
}

/--
No Adjacent Ones along an Infinite DFS Ray: `raySeq R` never emits `(1, 1)`, ruling out the
degenerate `[0, 1, 1, 1, ...]` tail across every prefix-slot branch.
-/
theorem dfs_ray_no_stutter_one {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) :
    ∀ j, ¬ (raySeq R j = 1 ∧ raySeq R (j + 1) = 1) := by {
  intro j
  induction j with
  | zero =>
    rintro ⟨h0, _⟩
    nomatch h0
  | succ t ih =>
    rintro ⟨ht1, ht2⟩
    change R.curSeq t = 1 at ht1
    change R.curSeq (t + 1) = 1 at ht2
    rcases R.h_step t with ⟨q, hlk, _, hc, _, _⟩ | ⟨_, hc, _, _⟩ | ⟨p, hp, _, _, hc, _, _⟩
    · have hlk_eq := dfs_ray_lookup_eq_lastOcc R t (R.curSeq t)
      rw [hlk, ht1] at hlk_eq
      cases h_occ : lastOccBeforeFn (raySeq R) (t + 1) 1 with
      | none =>
        rw [h_occ] at hlk_eq
        nomatch hlk_eq
      | some r =>
        rw [h_occ] at hlk_eq
        simp only [Option.map, Option.some.injEq] at hlk_eq
        have hr_sp := lastOccBeforeFn_eq_some_spec (raySeq R) (t + 1) 1 r h_occ
        have hr_lt := hr_sp.1
        have h_rt : r = t := by { omega }
        rw [h_rt] at hr_sp
        exact ih ⟨hr_sp.2.1, ht1⟩
    · omega
    · have hp_lt := ((dfs_ray_freeSeq_invariant R).2.2 t p hp).2.1
      omega
}

/--
Any positive term `raySeq R j < j` (`j ≥ 2`) necessarily arose from a post-cut tail-map lookup
(never from `p ∈ freeSeq`, since `p < z_0` forces gap `≥ j`), so `raySeq R (j - 1 - raySeq R j) =
raySeq R (j - 1)`.
-/
lemma raySeq_small_pos_step_spec {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) (j : ℕ)
    (hj_ge : 2 ≤ j) (h_pos : 0 < raySeq R j) (h_lt : raySeq R j < j) :
    j - 1 - raySeq R j < j - 1 ∧
      raySeq R (j - 1 - raySeq R j) = raySeq R (j - 1) := by {
  let t := j - 2
  have hj_eq : j = t + 2 := by { omega }
  rw [hj_eq] at h_pos h_lt ⊢
  change 0 < R.curSeq (t + 1) at h_pos
  change R.curSeq (t + 1) < t + 2 at h_lt
  rcases R.h_step t with ⟨q, hlk, _, hc, _, _⟩ | ⟨_, hc, _, _⟩ | ⟨p, hp, _, _, hc, _, _⟩
  · have hlk_eq := dfs_ray_lookup_eq_lastOcc R t (R.curSeq t)
    rw [hlk] at hlk_eq
    cases h_occ : lastOccBeforeFn (raySeq R) (t + 1) (R.curSeq t) with
    | none =>
      rw [h_occ] at hlk_eq
      nomatch hlk_eq
    | some r =>
      rw [h_occ] at hlk_eq
      simp only [Option.map, Option.some.injEq] at hlk_eq
      have hr_sp := lastOccBeforeFn_eq_some_spec (raySeq R) (t + 1) (R.curSeq t) r h_occ
      have hr_lt := hr_sp.1
      have hidx : t + 2 - 1 - R.curSeq (t + 1) = r := by { omega }
      have hj1 : t + 2 - 1 = t + 1 := rfl
      change t + 2 - 1 - R.curSeq (t + 1) < t + 2 - 1 ∧
        raySeq R (t + 2 - 1 - R.curSeq (t + 1)) = R.curSeq t
      rw [hidx, hj1]
      exact ⟨hr_lt, hr_sp.2.1⟩
  · omega
  · exfalso
    have hp_lt := ((dfs_ray_freeSeq_invariant R).2.2 t p hp).2.1
    omega
}

lemma raySeq_pos_anchor_trichotomy {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) (k : ℕ)
    (hk_ge : 1 ≤ k) (hk_pos : 0 < raySeq R k) :
    raySeq R k ≤ z_0 + k - 1 ∧
      ((k = 1 ∧ (z_0 + k - 1) - raySeq R k = R.z_prev) ∨
        (2 ≤ k ∧ ∃ p, p < z_0 ∧ p ≠ R.z_prev ∧ p ∈ R.freeSeq (k - 2) ∧
          R.freeSeq (k - 1) = removeFirst p (R.freeSeq (k - 2)) ∧
          (z_0 + k - 1) - raySeq R k = p) ∨
        (2 ≤ k ∧ ∃ r,
          lastOccBeforeFn (raySeq R) (k - 1) (raySeq R (k - 1)) = some r ∧
          (z_0 + k - 1) - raySeq R k = r + z_0)) := by {
  rcases eq_or_lt_of_le hk_ge with rfl | hk2
  · have h1 : raySeq R 1 = z_0 - R.z_prev := R.h_init_cur
    have hzp_lt := R.hzp_lt
    rw [h1]
    exact ⟨by { omega }, Or.inl ⟨rfl, by { omega }⟩⟩
  · let t := k - 2
    have hk_eq : k = t + 2 := by { omega }
    have hk1 : k - 1 = t + 1 := by { omega }
    have h_rk_def : raySeq R k = R.curSeq (t + 1) := by {
      rw [hk_eq]
      rfl
    }
    have hpos_c : 0 < R.curSeq (t + 1) := h_rk_def ▸ hk_pos
    rcases R.h_step t with ⟨q, hlk, _, hc, _, _⟩ | ⟨_, hc, _, _⟩ | ⟨p, hp, _, _, hc, _, hfr⟩
    · have hlk_eq := dfs_ray_lookup_eq_lastOcc R t (R.curSeq t)
      rw [hlk] at hlk_eq
      cases h_occ : lastOccBeforeFn (raySeq R) (t + 1) (R.curSeq t) with
      | none =>
        rw [h_occ] at hlk_eq
        nomatch hlk_eq
      | some r =>
        rw [h_occ] at hlk_eq
        simp only [Option.map, Option.some.injEq] at hlk_eq
        have hr_lt := (lastOccBeforeFn_eq_some_spec (raySeq R) (t + 1) _ r h_occ).1
        have h_rk : raySeq R k = z_0 + 1 + t - q := h_rk_def.trans hc
        refine ⟨by { omega }, Or.inr (Or.inr ⟨by { omega }, r, ?_, by { omega }⟩)⟩
        rw [hk1]
        exact h_occ
    · omega
    · have hp_inv := (dfs_ray_freeSeq_invariant R).2.2 t p hp
      have h_rk : raySeq R k = z_0 + 1 + t - p := h_rk_def.trans hc
      refine ⟨by { omega }, Or.inr (Or.inl ⟨by { omega }, p, hp_inv.2.1, hp_inv.2.2, ?_, ?_, ?_⟩)⟩
      · exact hp
      · rw [hk1]
        exact hfr
      · omega
}

/--
Global Lookback-Anchor Injectivity along `raySeq R` (even across pre-stabilization `freeSeq`
returns): for all `1 ≤ i < j` with `0 < raySeq R i` and `0 < raySeq R j`, the global anchors
`(z_0 + i - 1) - raySeq R i` and `(z_0 + j - 1) - raySeq R j` are distinct.
-/
lemma raySeq_anchor_unique {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) (i j : ℕ)
    (hi_ge : 1 ≤ i) (hlt : i < j) (hi_pos : 0 < raySeq R i) (hj_pos : 0 < raySeq R j) :
    raySeq R i ≤ z_0 + i - 1 ∧ raySeq R j ≤ z_0 + j - 1 ∧
      (z_0 + i - 1) - raySeq R i ≠ (z_0 + j - 1) - raySeq R j := by {
  have hti := raySeq_pos_anchor_trichotomy R i hi_ge hi_pos
  have htj := raySeq_pos_anchor_trichotomy R j (by { omega }) hj_pos
  refine ⟨hti.1, htj.1, ?_⟩
  intro heq
  have hzp_lt := R.hzp_lt
  have hinv := dfs_ray_freeSeq_invariant R
  rcases hti.2 with ⟨hi1, hai⟩ |
      ⟨hi2, pi, hpi_lt, _, hpi_mem, hpi_fr, hai⟩ |
      ⟨hi2, ri, hri_occ, hai⟩
  · rcases htj.2 with ⟨hj1, _⟩ | ⟨_, pj, _, hpj_ne, _, _, haj⟩ | ⟨_, rj, _, haj⟩
    · omega
    · exact hpj_ne (haj.symm.trans (heq.symm.trans hai))
    · omega
  · rcases htj.2 with ⟨hj1, _⟩ | ⟨_, pj, _, _, hpj_mem, _, haj⟩ | ⟨_, rj, _, haj⟩
    · omega
    · have hp_eq : pi = pj := hai.symm.trans (heq.trans haj)
      have hp_in : pi ∈ R.freeSeq (i - 1) :=
        hinv.2.1 (i - 1) (j - 2) pi (by { omega }) (hp_eq.symm ▸ hpj_mem)
      rw [hpi_fr] at hp_in
      exact not_mem_removeFirst_of_nodup pi (R.freeSeq (i - 2)) (hinv.1 (i - 2)) hp_in
    · omega
  · rcases htj.2 with ⟨hj1, _⟩ | ⟨_, pj, hpj_lt, _, _, _, haj⟩ | ⟨_, rj, hrj_occ, haj⟩
    · omega
    · omega
    · have hr_eq : ri = rj := by { omega }
      have hri_sp := lastOccBeforeFn_eq_some_spec (raySeq R) (i - 1) _ ri hri_occ
      have hrj_sp := lastOccBeforeFn_eq_some_spec (raySeq R) (j - 1) _ rj hrj_occ
      have hri_lt := hri_sp.1
      have hval_eq : raySeq R (i - 1) = raySeq R (j - 1) :=
        hri_sp.2.1.symm.trans (hr_eq ▸ hrj_sp.2.1)
      exact hrj_sp.2.2 (i - 1) (by { omega }) (by { omega }) hval_eq
}

lemma raySeq_periodic_val_le_P {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) (n_1 P u : ℕ)
    (hn1 : 1 ≤ n_1) (hP : 1 ≤ P) (hu : 1 ≤ u)
    (h_per : ∀ t, 1 ≤ raySeq R (n_1 + P + t) ∧ raySeq R (n_1 + t) = raySeq R (n_1 + P + t)) :
    raySeq R (n_1 + P + u) ≤ P := by {
  let t := n_1 + P + u - 2
  have hj_eq : n_1 + P + u = t + 2 := by { omega }
  have ht1 : t + 1 = n_1 + P + (u - 1) := by { omega }
  have hcur_eq : raySeq R (n_1 + (u - 1)) = R.curSeq t := by {
    have hp := (h_per (u - 1)).2
    rw [← ht1] at hp
    exact hp
  }
  cases h_occ : lastOccBeforeFn (raySeq R) (t + 1) (R.curSeq t) with
  | none =>
    have hnone := (lastOccBeforeFn_eq_none_iff (raySeq R) (t + 1) (R.curSeq t)).mp h_occ
    exact False.elim (hnone (n_1 + (u - 1)) (by { omega }) hcur_eq)
  | some r =>
    have hr_sp := lastOccBeforeFn_eq_some_spec (raySeq R) (t + 1) (R.curSeq t) r h_occ
    have hr_ge : n_1 + (u - 1) ≤ r := by {
      by_contra hlt
      exact hr_sp.2.2 (n_1 + (u - 1)) (by { omega }) (by { omega }) hcur_eq
    }
    have hlk_eq := dfs_ray_lookup_eq_lastOcc R t (R.curSeq t)
    rw [h_occ] at hlk_eq
    simp only [Option.map] at hlk_eq
    rcases R.h_step t with ⟨q, hlk, _, hc, _, _⟩ | ⟨hlk, _, _, _⟩ | ⟨_, _, hlk, _, _, _, _⟩
    · rw [hlk] at hlk_eq
      injection hlk_eq with hq_eq
      have hr_lt := hr_sp.1
      rw [hj_eq]
      change R.curSeq (t + 1) ≤ P
      omega
    · rw [hlk] at hlk_eq
      nomatch hlk_eq
    · rw [hlk] at hlk_eq
      nomatch hlk_eq
}

lemma raySeq_periodic_disp_ne_of_lt {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) (n_1 P : ℕ)
    (hn1 : 1 ≤ n_1) (hP : 1 ≤ P)
    (h_per : ∀ t, 1 ≤ raySeq R (n_1 + P + t) ∧ raySeq R (n_1 + t) = raySeq R (n_1 + P + t))
    (k_1 k_2 : Fin P) (hlt : k_1.val < k_2.val) :
    (k_1.val + P - raySeq R (n_1 + P + (k_1.val + 1))) % P ≠
      (k_2.val + P - raySeq R (n_1 + P + (k_2.val + 1))) % P := by {
  intro hmod
  let X_1 := raySeq R (n_1 + P + (k_1.val + 1))
  let X_2 := raySeq R (n_1 + P + (k_2.val + 1))
  have hX1_pos : 1 ≤ X_1 := (h_per (k_1.val + 1)).1
  have hX2_pos : 1 ≤ X_2 := (h_per (k_2.val + 1)).1
  have hX1_le : X_1 ≤ P :=
    raySeq_periodic_val_le_P R n_1 P (k_1.val + 1) hn1 hP (by { omega }) h_per
  have hX2_le : X_2 ≤ P :=
    raySeq_periodic_val_le_P R n_1 P (k_2.val + 1) hn1 hP (by { omega }) h_per
  have hk1_lt := k_1.isLt
  have hk2_lt := k_2.isLt
  rcases mod_eq_cases (k_1.val + P - X_1) (k_2.val + P - X_2) P
      (by { omega }) (by { omega }) hmod with heq | hadd1 | hadd2
  · have han := raySeq_anchor_unique R (n_1 + P + (k_1.val + 1)) (n_1 + P + (k_2.val + 1))
      (by { omega }) (by { omega }) hX1_pos hX2_pos
    exact han.2.2 (by { omega })
  · have hX2_eq : raySeq R (n_1 + (k_2.val + 1)) = X_2 := (h_per (k_2.val + 1)).2
    have han := raySeq_anchor_unique R (n_1 + (k_2.val + 1)) (n_1 + P + (k_1.val + 1))
      (by { omega }) (by { omega }) (hX2_eq.symm ▸ hX2_pos) hX1_pos
    rw [hX2_eq] at han
    have hi_le := han.1
    exact han.2.2 (by { omega })
  · omega
}

lemma raySeq_periodic_disp_bijective {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) (n_1 P : ℕ)
    (hn1 : 1 ≤ n_1) (hP : 1 ≤ P)
    (h_per : ∀ t, 1 ≤ raySeq R (n_1 + P + t) ∧ raySeq R (n_1 + t) = raySeq R (n_1 + P + t)) :
    Function.Bijective (fun k : Fin P =>
      (⟨(k.val + P - raySeq R (n_1 + P + (k.val + 1))) % P, Nat.mod_lt _ hP⟩ : Fin P)) := by {
  refine Finite.injective_iff_bijective.mp ?_
  intro k_1 k_2 heq
  have hmod : (k_1.val + P - raySeq R (n_1 + P + (k_1.val + 1))) % P =
      (k_2.val + P - raySeq R (n_1 + P + (k_2.val + 1))) % P := congrArg Fin.val heq
  rcases lt_trichotomy k_1.val k_2.val with hlt | hval_eq | hgt
  · exact False.elim (raySeq_periodic_disp_ne_of_lt R n_1 P hn1 hP h_per k_1 k_2 hlt hmod)
  · exact Fin.ext hval_eq
  · exact False.elim (raySeq_periodic_disp_ne_of_lt R n_1 P hn1 hP h_per k_2 k_1 hgt hmod.symm)
}

lemma raySeq_periodic_step_backward {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) (n_1 P : ℕ)
    (hP : 1 ≤ P)
    (h_per : ∀ t, 1 ≤ raySeq R (n_1 + 1 + P + t) ∧
      raySeq R (n_1 + 1 + t) = raySeq R (n_1 + 1 + P + t)) :
    ∀ t, 1 ≤ raySeq R (n_1 + P + t) ∧ raySeq R (n_1 + t) = raySeq R (n_1 + P + t) := by {
  have hbij := raySeq_periodic_disp_bijective R (n_1 + 1) P (by { omega }) hP h_per
  rcases hbij.2 ⟨P - 1, by { omega }⟩ with ⟨k, hk_eq⟩
  have hk_mod : (k.val + P - raySeq R (n_1 + 1 + P + (k.val + 1))) % P = P - 1 :=
    congrArg Fin.val hk_eq
  have hk_lt := k.isLt
  have hd_pos : 1 ≤ raySeq R (n_1 + 1 + P + (k.val + 1)) := (h_per (k.val + 1)).1
  have hd_le : raySeq R (n_1 + 1 + P + (k.val + 1)) ≤ P :=
    raySeq_periodic_val_le_P R (n_1 + 1) P (k.val + 1) (by { omega }) hP (by { omega }) h_per
  have hnum_eq : k.val + P - raySeq R (n_1 + 1 + P + (k.val + 1)) = P - 1 :=
    mod_eq_pred_of_le_two_mul_sub_two _ P hP (by { omega }) hk_mod
  have hd2_eq : raySeq R (n_1 + 1 + P + (k.val + 1)) = k.val + 1 := by { omega }
  have hd1_eq : raySeq R (n_1 + 1 + (k.val + 1)) = k.val + 1 :=
    (h_per (k.val + 1)).2.trans hd2_eq
  have hsp1 := raySeq_small_pos_step_spec R (n_1 + 1 + (k.val + 1)) (by { omega })
    (by { omega }) (by { omega })
  have hsp2 := raySeq_small_pos_step_spec R (n_1 + 1 + P + (k.val + 1)) (by { omega })
    (by { omega }) (by { omega })
  have hidx1 : n_1 + 1 + (k.val + 1) - 1 - raySeq R (n_1 + 1 + (k.val + 1)) = n_1 := by { omega }
  have hidx2 : n_1 + 1 + P + (k.val + 1) - 1 - raySeq R (n_1 + 1 + P + (k.val + 1)) =
      n_1 + P := by { omega }
  have hj1 : n_1 + 1 + (k.val + 1) - 1 = n_1 + 1 + k.val := by { omega }
  have hj2 : n_1 + 1 + P + (k.val + 1) - 1 = n_1 + 1 + P + k.val := by { omega }
  rw [hidx1, hj1] at hsp1
  rw [hidx2, hj2] at hsp2
  intro t
  cases t with
  | zero =>
    have hpk := h_per k.val
    refine ⟨?_, ?_⟩
    · simp only [Nat.add_zero]
      rw [hsp2.2]
      exact hpk.1
    · simp only [Nat.add_zero]
      rw [hsp1.2, hsp2.2]
      exact hpk.2
  | succ s =>
    have hps := h_per s
    have ha1 : n_1 + (s + 1) = n_1 + 1 + s := by { omega }
    have ha2 : n_1 + P + (s + 1) = n_1 + 1 + P + s := by { omega }
    rw [ha1, ha2]
    exact hps
}

/--
No Positive Periodic Tail along an Infinite DFS Ray: `raySeq R` cannot eventually enter any
positive periodic cycle of period `P ≥ 1` (backward determinism steps down to `raySeq R 0 = 0`).
-/
theorem raySeq_not_eventually_periodic {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) (n_1 P : ℕ)
    (hP : 1 ≤ P) :
    ¬ ∀ t, 1 ≤ raySeq R (n_1 + P + t) ∧ raySeq R (n_1 + t) = raySeq R (n_1 + P + t) := by {
  induction n_1 with
  | zero =>
    intro h_per
    have hp0 := h_per 0
    simp only [Nat.zero_add, Nat.add_zero] at hp0
    have hr0 : raySeq R 0 = 0 := rfl
    omega
  | succ m ih =>
    intro h_per
    exact ih (raySeq_periodic_step_backward R m P hP h_per)
}

/--
Clamped symbol-age state for an arbitrary sequence `f : ℕ → ℕ` at cap `B`.
-/
def clampedAgeFn (f : ℕ → ℕ) (B m w : ℕ) : ℕ :=
  match lastOccBeforeFn f m w with
  | none => 0
  | some p => if m - p ≤ B then m - p else 0

lemma clampedAgeFn_le (f : ℕ → ℕ) (B m w : ℕ) : clampedAgeFn f B m w ≤ B := by {
  unfold clampedAgeFn
  cases lastOccBeforeFn f m w with
  | none => exact Nat.zero_le B
  | some p =>
    dsimp only
    split_ifs with hle
    · exact hle
    · exact Nat.zero_le B
}

lemma clampedAgeFn_step (f : ℕ → ℕ) (B m w : ℕ) :
    clampedAgeFn f B (m + 1) w = stepClampedAge B (f m) (clampedAgeFn f B m) w := by {
  by_cases hw : w = f m
  · subst hw
    have hocc : lastOccBeforeFn f (m + 1) (f m) = some m := by { simp [lastOccBeforeFn] }
    rw [stepClampedAge, if_pos rfl]
    unfold clampedAgeFn
    rw [hocc]
    dsimp only
    have hsub : m + 1 - m = 1 := by { omega }
    rw [hsub]
  · have hmw : ¬ (f m = w) := Ne.symm hw
    have hocc : lastOccBeforeFn f (m + 1) w = lastOccBeforeFn f m w := by {
      simp [lastOccBeforeFn, hmw]
    }
    rw [stepClampedAge, if_neg hw]
    unfold clampedAgeFn
    rw [hocc]
    cases h_prev : lastOccBeforeFn f m w with
    | none => simp
    | some p =>
      have hp_lt := (lastOccBeforeFn_eq_some_spec f m w p h_prev).1
      have h_prev_val : (match some p with
          | none => 0
          | some p => if m - p ≤ B then m - p else 0) =
          if m - p ≤ B then m - p else 0 := rfl
      have h_next_val : (match some p with
          | none => 0
          | some p => if m + 1 - p ≤ B then m + 1 - p else 0) =
          if m + 1 - p ≤ B then m + 1 - p else 0 := rfl
      rw [h_prev_val, h_next_val]
      by_cases hd_le : m - p ≤ B
      · simp only [hd_le, ↓reduceIte]
        by_cases hd_lt : m - p < B
        · have hnot : ¬ (m - p = 0 ∨ B ≤ m - p) := by { omega }
          rw [if_neg hnot, if_pos (by { omega })]
          omega
        · have hor : m - p = 0 ∨ B ≤ m - p := Or.inr (by { omega })
          rw [if_pos hor, if_neg (by { omega })]
      · have hn_next : ¬ (m + 1 - p ≤ B) := by { omega }
        simp [hd_le, hn_next]
}

lemma clampedAgeFn_output_of_pos_bounded (f : ℕ → ℕ) (M_0 B m : ℕ)
    (h_rec : IsVanEckFrom f M_0) (hm : M_0 ≤ m)
    (h_pos : 1 ≤ f (m + 1)) (h_le : f (m + 1) ≤ B) :
    f (m + 1) = clampedAgeFn f B m (f m) := by {
  have hr := h_rec m hm
  cases h_occ : lastOccBeforeFn f m (f m) with
  | none =>
    rw [h_occ] at hr
    change f (m + 1) = 0 at hr
    omega
  | some p =>
    rw [h_occ] at hr
    change f (m + 1) = m - p at hr
    unfold clampedAgeFn
    rw [h_occ]
    dsimp only
    rw [if_pos (hr ▸ h_le)]
    exact hr
}

lemma isVanEckFrom_periodic_of_state_eq (f : ℕ → ℕ) (M_0 N_pos B k_1 k_2 : ℕ)
    (h_rec : IsVanEckFrom f M_0) (hM : M_0 ≤ N_pos)
    (h_bnd : ∀ m ≥ N_pos, 1 ≤ f m ∧ f m ≤ B)
    (hk1 : N_pos ≤ k_1) (hk2 : N_pos ≤ k_2)
    (h_cur : f k_1 = f k_2)
    (h_st : ∀ w ≤ B, clampedAgeFn f B k_1 w = clampedAgeFn f B k_2 w) :
    ∀ t, f (k_1 + t) = f (k_2 + t) ∧
      ∀ w ≤ B, clampedAgeFn f B (k_1 + t) w = clampedAgeFn f B (k_2 + t) w := by {
  intro t
  induction t with
  | zero => exact ⟨h_cur, h_st⟩
  | succ s ih =>
    have hb1s := h_bnd (k_1 + s) (by { omega })
    have hb1 := h_bnd (k_1 + s + 1) (by { omega })
    have hb2 := h_bnd (k_2 + s + 1) (by { omega })
    have hout1 := clampedAgeFn_output_of_pos_bounded f M_0 B (k_1 + s) h_rec
      (by { omega }) hb1.1 hb1.2
    have hout2 := clampedAgeFn_output_of_pos_bounded f M_0 B (k_2 + s) h_rec
      (by { omega }) hb2.1 hb2.2
    have ha1 : k_1 + (s + 1) = k_1 + s + 1 := by { omega }
    have ha2 : k_2 + (s + 1) = k_2 + s + 1 := by { omega }
    refine ⟨?_, ?_⟩
    · rw [ha1, ha2, hout1, hout2, ih.1, ih.2 (f (k_2 + s)) (ih.1 ▸ hb1s.2)]
    · intro w hw
      rw [ha1, ha2, clampedAgeFn_step, clampedAgeFn_step, ih.1]
      unfold stepClampedAge
      rw [ih.2 w hw]
}

/--
Clamped-Age Pigeonhole Theorem for `IsVanEckFrom`: any sequence `f` obeying `IsVanEckFrom f M_0`
whose tail `m ≥ N_pos` (`N_pos ≥ M_0`) lies in `[1, B]` is eventually periodic (`P ≥ 1`).
-/
theorem isVanEckFrom_pos_bounded_periodic (f : ℕ → ℕ) (M_0 N_pos B : ℕ)
    (h_rec : IsVanEckFrom f M_0) (hM : M_0 ≤ N_pos)
    (h_bnd : ∀ m ≥ N_pos, 1 ≤ f m ∧ f m ≤ B) :
    ∃ k_1 P, N_pos ≤ k_1 ∧ 1 ≤ P ∧
      ∀ t, 1 ≤ f (k_1 + P + t) ∧ f (k_1 + t) = f (k_1 + P + t) := by {
  let State := Fin (B + 1) × (Fin (B + 1) → Fin (B + 1))
  let enc : ℕ → State := fun n =>
    (⟨f (N_pos + n), Nat.lt_succ_of_le (h_bnd (N_pos + n) (by { omega })).2⟩,
      fun w => ⟨clampedAgeFn f B (N_pos + n) w.val,
        Nat.lt_succ_of_le (clampedAgeFn_le f B (N_pos + n) w.val)⟩)
  rcases Finite.exists_ne_map_eq_of_infinite enc with ⟨i, j, hne, heq⟩
  have extract : ∀ a b, a < b → enc a = enc b →
      ∃ k_1 P, N_pos ≤ k_1 ∧ 1 ≤ P ∧
        ∀ t, 1 ≤ f (k_1 + P + t) ∧ f (k_1 + t) = f (k_1 + P + t) := by {
    intro a b hlt hab
    have hcur : f (N_pos + a) = f (N_pos + b) := congrArg (fun s => s.1.val) hab
    have hst : ∀ w ≤ B, clampedAgeFn f B (N_pos + a) w = clampedAgeFn f B (N_pos + b) w := by {
      intro w hw
      exact congrArg Fin.val (congrFun (congrArg Prod.snd hab) ⟨w, Nat.lt_succ_of_le hw⟩)
    }
    have hper := isVanEckFrom_periodic_of_state_eq f M_0 N_pos B (N_pos + a) (N_pos + b)
      h_rec hM h_bnd (by { omega }) (by { omega }) hcur hst
    refine ⟨N_pos + a, b - a, by { omega }, by { omega }, ?_⟩
    intro t
    have hidx : N_pos + a + (b - a) + t = N_pos + b + t := by { omega }
    rw [hidx]
    exact ⟨(h_bnd (N_pos + b + t) (by { omega })).1, (hper t).1⟩
  }
  rcases lt_or_gt_of_ne hne with hlt | hgt
  · exact extract i j hlt heq
  · exact extract j i hgt heq.symm
}

/--
Infinitely Many Zeros along an Infinite DFS Ray: `raySeq R` hits `0` arbitrarily far out
(otherwise its tail is bounded, positive, and periodic, violating `raySeq_not_eventually_periodic`).
-/
theorem raySeq_infinite_zeros {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) (K : ℕ) :
    ∃ z > K, raySeq R z = 0 := by {
  classical
  by_contra h_none
  rcases (dfs_ray_shifted_seq_spec R).2.2.2 with ⟨T_stab, h_rec⟩
  let N_pos := max (K + 1) (T_stab + 1)
  have h_nz : ∀ u ≥ N_pos, raySeq R u ≠ 0 := fun u hu hz => h_none ⟨u, by { omega }, hz⟩
  let S := (Finset.range (N_pos + 1)).image (raySeq R)
  have hS_ne : S.Nonempty :=
    ⟨raySeq R 0, Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by { omega }))⟩
  let B := S.max' hS_ne + 1
  have h_all_le : ∀ m, raySeq R m ≤ B := by {
    intro m
    refine Nat.strong_induction_on m (fun m ih => ?_)
    by_cases hm : m ≤ N_pos
    · have hmem : raySeq R m ∈ S :=
        Finset.mem_image_of_mem _ (Finset.mem_range.mpr (by { omega }))
      exact Nat.le_succ_of_le (Finset.le_max' S _ hmem)
    · have hr := h_rec m (by { omega })
      have hnz1 := h_nz (m + 1) (by { omega })
      cases h_occ : lastOccBeforeFn (raySeq R) m (raySeq R m) with
      | none =>
        rw [h_occ] at hr
        exact False.elim (hnz1 hr)
      | some p =>
        have hp_sp := lastOccBeforeFn_eq_some_spec (raySeq R) m (raySeq R m) p h_occ
        rw [← hp_sp.2.1]
        exact ih p hp_sp.1
  }
  rcases isVanEckFrom_pos_bounded_periodic (raySeq R) (T_stab + 1) N_pos B h_rec
      (Nat.le_max_right _ _)
      (fun m hm => ⟨Nat.pos_of_ne_zero (h_nz m hm), h_all_le m⟩) with
    ⟨k_1, P, _hk1, hP, h_per⟩
  exact raySeq_not_eventually_periodic R k_1 P hP h_per
}

lemma isVanEckFrom_pre_zero_inj (g : ℕ → ℕ) (M_0 z_1 z_2 : ℕ)
    (h_rec : IsVanEckFrom g M_0) (hz1 : M_0 < z_1) (hlt : z_1 < z_2)
    (hz2_zero : g z_2 = 0) :
    g (z_1 - 1) ≠ g (z_2 - 1) := by {
  intro hval
  have hr := h_rec (z_2 - 1) (by { omega })
  have hidx : z_2 - 1 + 1 = z_2 := by { omega }
  rw [hidx, hz2_zero] at hr
  cases h_occ : lastOccBeforeFn g (z_2 - 1) (g (z_2 - 1)) with
  | none =>
    have hnone := (lastOccBeforeFn_eq_none_iff g _ _).mp h_occ
    exact hnone (z_1 - 1) (by { omega }) hval
  | some p =>
    rw [h_occ] at hr
    have hp_lt := (lastOccBeforeFn_eq_some_spec g _ _ p h_occ).1
    change 0 = z_2 - 1 - p at hr
    omega
}

/--
Unboundedness of an Infinite DFS Ray: no `InfiniteNoTwosDFSRay` is bounded above (completely
ruling out all bounded `2`-free DFS branches without `sorry`).
-/
theorem raySeq_unbounded {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) (B : ℕ) :
    ∃ j, B < raySeq R j := by {
  by_contra h_not
  have h_bdd : ∀ j, raySeq R j ≤ B := fun j => Nat.le_of_not_lt (fun hgt => h_not ⟨j, hgt⟩)
  rcases (dfs_ray_shifted_seq_spec R).2.2.2 with ⟨T_stab, h_rec⟩
  let zSeq : ℕ → ℕ := Nat.rec
    (Classical.choose (raySeq_infinite_zeros R (T_stab + 1)))
    (fun _ zk => Classical.choose (raySeq_infinite_zeros R zk))
  have hz_step : ∀ k, (T_stab + 1 < zSeq k ∧ raySeq R (zSeq k) = 0) ∧ zSeq k < zSeq (k + 1) := by {
    intro k
    induction k with
    | zero =>
      have hs0 := Classical.choose_spec (raySeq_infinite_zeros R (T_stab + 1))
      have hs1 := Classical.choose_spec (raySeq_infinite_zeros R (zSeq 0))
      exact ⟨hs0, hs1.1⟩
    | succ s ih =>
      have hs1 := Classical.choose_spec (raySeq_infinite_zeros R (zSeq s))
      have hs2 := Classical.choose_spec (raySeq_infinite_zeros R (zSeq (s + 1)))
      exact ⟨⟨by { omega }, hs1.2⟩, hs2.1⟩
  }
  have hz_mono : StrictMono zSeq := strictMono_nat_of_lt_succ (fun k => (hz_step k).2)
  let valOf : Fin (B + 2) → Fin (B + 1) := fun k =>
    ⟨raySeq R (zSeq k.val - 1), Nat.lt_succ_of_le (h_bdd _)⟩
  have hinj : Function.Injective valOf := by {
    intro a b heq
    have hval : raySeq R (zSeq a.val - 1) = raySeq R (zSeq b.val - 1) := congrArg Fin.val heq
    rcases lt_trichotomy a.val b.val with hlt | hval_eq | hgt
    · exact False.elim (isVanEckFrom_pre_zero_inj (raySeq R) (T_stab + 1) _ _ h_rec
        (hz_step a.val).1.1 (hz_mono hlt) (hz_step b.val).1.2 hval)
    · exact Fin.ext hval_eq
    · exact False.elim (isVanEckFrom_pre_zero_inj (raySeq R) (T_stab + 1) _ _ h_rec
        (hz_step b.val).1.1 (hz_mono hgt) (hz_step a.val).1.2 hval.symm)
  }
  have hcard := Fintype.card_le_of_injective valOf hinj
  simp only [Fintype.card_fin] at hcard
  omega
}

/--
Running prefix maximum `max_{i ≤ n} f i` of an arbitrary sequence `f : ℕ → ℕ`.
-/
def prefixMaxFn (f : ℕ → ℕ) : ℕ → ℕ
  | 0 => f 0
  | n + 1 => max (prefixMaxFn f n) (f (n + 1))

lemma le_prefixMaxFn_and_mono (f : ℕ → ℕ) :
    (∀ n, f n ≤ prefixMaxFn f n) ∧ (∀ a b, a ≤ b → prefixMaxFn f a ≤ prefixMaxFn f b) := by {
  refine ⟨?_, ?_⟩
  · intro n
    cases n with
    | zero => exact le_rfl
    | succ k => exact Nat.le_max_right _ _
  · intro a b hab
    induction b with
    | zero =>
      have ha0 : a = 0 := by { omega }
      rw [ha0]
    | succ k ih =>
      rcases eq_or_lt_of_le hab with rfl | hlt
      · exact le_rfl
      · exact le_trans (ih (by { omega })) (Nat.le_max_left _ _)
}

/--
Any unbounded sequence with infinitely many zeros undergoes infinitely many consecutive-zero
prefix-maximum jumps arbitrarily far out and above any height threshold.
-/
theorem infinite_record_jumps_of_zeros_and_unbounded (g : ℕ → ℕ)
    (h_zeros : ∀ K, ∃ z > K, g z = 0) (h_unb : ∀ B, ∃ j, B < g j) (K V : ℕ) :
    ∃ z_prev z, K < z_prev ∧ z_prev < z ∧ g z_prev = 0 ∧ g z = 0 ∧
      (∀ k, z_prev < k → k < z → g k ≠ 0) ∧
      V < prefixMaxFn g z_prev ∧ prefixMaxFn g z_prev < prefixMaxFn g z := by {
  classical
  have hpm := le_prefixMaxFn_and_mono g
  rcases h_unb V with ⟨j_1, hj1⟩
  rcases h_zeros (max K j_1) with ⟨z_start, hzs_gt, hzs_zero⟩
  rcases h_unb (prefixMaxFn g z_start) with ⟨j_2, hj2⟩
  rcases h_zeros (max z_start j_2) with ⟨z_hi, hzhi_gt, hzhi_zero⟩
  have hex : ∃ z, z_start < z ∧ g z = 0 ∧ prefixMaxFn g z_start < prefixMaxFn g z := by {
    refine ⟨z_hi, by { omega }, hzhi_zero, ?_⟩
    exact lt_of_lt_of_le hj2 (le_trans (hpm.1 j_2) (hpm.2 j_2 z_hi (by { omega })))
  }
  let z := Nat.find hex
  have hz_sp := Nat.find_spec hex
  cases h_occ : lastOccBeforeFn g z 0 with
  | none =>
    have hnone := (lastOccBeforeFn_eq_none_iff g z 0).mp h_occ
    exact False.elim (hnone z_start hz_sp.1 hzs_zero)
  | some z_prev =>
    have hzp := lastOccBeforeFn_eq_some_spec g z 0 z_prev h_occ
    have hzs_le : z_start ≤ z_prev := by {
      by_contra hlt
      exact hzp.2.2 z_start (by { omega }) hz_sp.1 hzs_zero
    }
    have hpm_le : prefixMaxFn g z_prev ≤ prefixMaxFn g z_start := by {
      rcases eq_or_lt_of_le hzs_le with rfl | hlt
      · exact le_rfl
      · have hmin := Nat.find_min hex hzp.1
        by_contra hgt
        exact hmin ⟨hlt, hzp.2.1, Nat.lt_of_not_le hgt⟩
    }
    refine ⟨z_prev, z, by { omega }, hzp.1, hzp.2.1, hz_sp.2.1, hzp.2.2, ?_, ?_⟩
    · exact lt_of_lt_of_le hj1 (le_trans (hpm.1 j_1) (hpm.2 j_1 z_prev (by { omega })))
    · exact lt_of_le_of_lt hpm_le hz_sp.2.2
}

/--
Infinitely Many Consecutive-Zero Record Jumps along an Infinite DFS Ray `raySeq R`.
-/
theorem raySeq_infinite_record_jumps {z_0 : ℕ} (R : InfiniteNoTwosDFSRay z_0) (K V : ℕ) :
    ∃ z_prev z, K < z_prev ∧ z_prev < z ∧ raySeq R z_prev = 0 ∧ raySeq R z = 0 ∧
      (∀ k, z_prev < k → k < z → raySeq R k ≠ 0) ∧
      V < prefixMaxFn (raySeq R) z_prev ∧
      prefixMaxFn (raySeq R) z_prev < prefixMaxFn (raySeq R) z := by {
  exact infinite_record_jumps_of_zeros_and_unbounded
    (raySeq R) (raySeq_infinite_zeros R) (raySeq_unbounded R) K V
}

lemma lastOccBeforeFn_eq_some_of_prev (f : ℕ → ℕ) (m p v : ℕ)
    (hp_lt : p < m) (hfp : f p = v) (h_none_after : ∀ k, p < k → k < m → f k ≠ v) :
    lastOccBeforeFn f m v = some p := by {
  cases h_occ : lastOccBeforeFn f m v with
  | none =>
    exact False.elim (((lastOccBeforeFn_eq_none_iff f m v).mp h_occ) p hp_lt hfp)
  | some r =>
    have hr := lastOccBeforeFn_eq_some_spec f m v r h_occ
    rcases lt_trichotomy r p with hlt | rfl | hgt
    · exact False.elim (hr.2.2 p hlt hp_lt hfp)
    · rfl
    · exact False.elim (h_none_after r hgt hr.1 hr.2.1)
}

lemma prefixMaxFn_le_iff (f : ℕ → ℕ) (n B : ℕ) :
    prefixMaxFn f n ≤ B ↔ ∀ k ≤ n, f k ≤ B := by {
  induction n with
  | zero =>
    simp only [prefixMaxFn, Nat.le_zero]
    exact ⟨fun h k hk => hk ▸ h, fun h => h 0 rfl⟩
  | succ m ih =>
    simp only [prefixMaxFn, max_le_iff, ih]
    refine ⟨?_, ?_⟩
    · intro h k hk
      rcases eq_or_lt_of_le hk with rfl | hlt
      · exact h.2
      · exact h.1 k (by { omega })
    · intro h
      exact ⟨fun k hk => h k (by { omega }), h (m + 1) le_rfl⟩
}

/--
Consecutive-zero gap formula and lower bound (`≥ 3`) for any `2`-free `IsVanEckFrom g M_0` tail.
-/
lemma isVanEckFrom_zero_gap_eq_and_ge_three (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0) :
    g (z + 1) = z - z_prev ∧ 3 ≤ z - z_prev := by {
  have hzp1_nz : g (z_prev + 1) ≠ 0 := by {
    have hr := h_rec z_prev hzp_M
    rw [hzp] at hr
    cases h_occ0 : lastOccBeforeFn g z_prev 0 with
    | none =>
      exact False.elim (((lastOccBeforeFn_eq_none_iff g z_prev 0).mp h_occ0) 0 hzp_pos hg0)
    | some r_0 =>
      rw [h_occ0] at hr
      have hr0_lt := (lastOccBeforeFn_eq_some_spec g z_prev 0 r_0 h_occ0).1
      change g (z_prev + 1) = z_prev - r_0 at hr
      omega
  }
  have h_ge2 : 2 ≤ z - z_prev := by {
    by_contra hlt2
    have hz_eq : z = z_prev + 1 := by { omega }
    exact hzp1_nz (hz_eq ▸ hz)
  }
  have h_occz : lastOccBeforeFn g z 0 = some z_prev :=
    lastOccBeforeFn_eq_some_of_prev g z z_prev 0 h_lt hzp h_gap
  have hrz := h_rec z (by { omega })
  rw [hz, h_occz] at hrz
  change g (z + 1) = z - z_prev at hrz
  have hne2 : g (z + 1) ≠ 2 := h_no2 (z + 1) (by { omega })
  exact ⟨hrz, by { omega }⟩
}

/--
Post-Zero Return Specification for `IsVanEckFrom g M_0`: at consecutive zeros `1 ≤ z_prev < z`
(`M_0 ≤ z_prev`), the zero gap `g (z + 1) = z - z_prev` has most recent anchor
`q = z + 1 - g (z + 2) ≤ z - 2` (`3 ≤ g (z + 2) ≤ z + 1`).
-/
lemma isVanEckFrom_post_zero_return_spec (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0) :
    3 ≤ g (z + 2) ∧
      g (z + 2) ≤ z + 1 ∧
      z + 1 - g (z + 2) ≤ z - 2 ∧
      g (z + 1 - g (z + 2)) = z - z_prev ∧
      ∀ j, z + 1 - g (z + 2) < j → j < z + 1 → g j ≠ z - z_prev := by {
  have hgap_sp := isVanEckFrom_zero_gap_eq_and_ge_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hr1 := h_rec (z + 1) (by { omega })
  cases h_occ : lastOccBeforeFn g (z + 1) (g (z + 1)) with
  | none =>
    rw [h_occ] at hr1
    change g (z + 2) = 0 at hr1
    have h_occ2 : lastOccBeforeFn g (z + 2) 0 = some z :=
      lastOccBeforeFn_eq_some_of_prev g (z + 2) z 0 (by { omega }) hz (fun k hk1 hk2 => by {
        have hk_eq : k = z + 1 := by { omega }
        rw [hk_eq, hgap_sp.1]
        omega
      })
    have hr2 := h_rec (z + 2) (by { omega })
    rw [hr1, h_occ2] at hr2
    change g (z + 3) = z + 2 - z at hr2
    exact False.elim (h_no2 (z + 3) (by { omega }) (by { omega }))
  | some q =>
    rw [h_occ] at hr1
    change g (z + 2) = z + 1 - q at hr1
    have hq_sp := lastOccBeforeFn_eq_some_spec g (z + 1) (g (z + 1)) q h_occ
    have hq_lt := hq_sp.1
    have hq_ne_z : q ≠ z := fun heq => by {
      have h0 : g q = 0 := heq ▸ hz
      omega
    }
    have hq_ne_z1 : q ≠ z - 1 := fun heq =>
      h_no2 (z + 2) (by { omega }) (by { omega })
    have hq_eq : z + 1 - g (z + 2) = q := by { omega }
    rw [hq_eq]
    exact ⟨by { omega }, by { omega }, by { omega },
      hq_sp.2.1.trans hgap_sp.1, hgap_sp.1 ▸ hq_sp.2.2⟩
}

/--
Post-Zero Anchor Uniqueness & Pre-Zero Disjointness for `IsVanEckFrom g M_0`:
post-zero return anchors `q(z) = z + 1 - g (z + 2)` are pairwise distinct across zeros and
disjoint from every pre-zero anchor `p(z'') = z'' - 2 - g (z'' - 1)` with `z'' ≠ z + 3`.
-/
lemma isVanEckFrom_post_zero_anchor_unique_and_disjoint (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0) :
    (∀ z_prev' z', z < z' → z_prev' < z' → 1 ≤ z_prev' → M_0 ≤ z_prev' →
      g z_prev' = 0 → g z' = 0 → (∀ k, z_prev' < k → k < z' → g k ≠ 0) →
      z + 1 - g (z + 2) ≠ z' + 1 - g (z' + 2)) ∧
    (∀ z'', M_0 + 2 ≤ z'' → z'' ≠ z + 3 → 0 < g (z'' - 1) →
      z + 1 - g (z + 2) ≠ z'' - 2 - g (z'' - 1)) := by {
  have hret := isVanEckFrom_post_zero_return_spec g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  refine ⟨?_, ?_⟩
  · intro z_prev' z' hzz' hlt' hpos' hM' hzp' hz' hgap'
    have hret' := isVanEckFrom_post_zero_return_spec g M_0 z_prev' z'
      hg0 h_rec h_no2 hpos' hM' hlt' hzp' hz' hgap'
    exact isVanEckFrom_lookback_anchor_unique g M_0 (z + 2) (z' + 2) h_rec
      (by { omega }) (by { omega }) (by { omega }) (by { omega })
  · intro z'' hz''_ge hne3 hz''_pos
    rcases lt_trichotomy (z + 2) (z'' - 1) with hlt1 | heq1 | hgt1
    · have hu := isVanEckFrom_lookback_anchor_unique g M_0 (z + 2) (z'' - 1) h_rec
        (by { omega }) hlt1 (by { omega }) hz''_pos
      have hs : z'' - 1 - 1 = z'' - 2 := by { omega }
      rw [hs] at hu
      exact hu
    · omega
    · have hu := isVanEckFrom_lookback_anchor_unique g M_0 (z'' - 1) (z + 2) h_rec
        (by { omega }) hgt1 hz''_pos (by { omega })
      have hs : z'' - 1 - 1 = z'' - 2 := by { omega }
      rw [hs] at hu
      exact Ne.symm hu
}

/--
Every index `k < z - 1` and `z + 1` in a consecutive-zero block `[z_prev, z]` is bounded by
`prefixMaxFn g z_prev` (`3 ≤ prefixMaxFn g z_prev`), and `prefixMaxFn g z =
max (prefixMaxFn g z_prev) (g (z - 1))`.
-/
lemma isVanEckFrom_block_le_prefixMax_prev (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0) :
    (∀ k < z - 1, g k ≤ prefixMaxFn g z_prev) ∧
      g (z + 1) ≤ prefixMaxFn g z_prev ∧
      3 ≤ prefixMaxFn g z_prev ∧
      prefixMaxFn g z = max (prefixMaxFn g z_prev) (g (z - 1)) := by {
  have hpm := le_prefixMaxFn_and_mono g
  have hgap_sp := isVanEckFrom_zero_gap_eq_and_ge_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hret := isVanEckFrom_post_zero_return_spec g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have h_all : ∀ k < z - 1, g k ≤ prefixMaxFn g z_prev := by {
    intro k
    refine Nat.strong_induction_on k (fun k ih hk_lt => ?_)
    by_cases hle : k ≤ z_prev
    · exact le_trans (hpm.1 k) (hpm.2 k z_prev hle)
    · have hr := h_rec k (by { omega })
      have hnz : g (k + 1) ≠ 0 := h_gap (k + 1) (by { omega }) (by { omega })
      cases h_occ : lastOccBeforeFn g k (g k) with
      | none =>
        rw [h_occ] at hr
        exact False.elim (hnz hr)
      | some r =>
        have hr_sp := lastOccBeforeFn_eq_some_spec g k (g k) r h_occ
        rw [← hr_sp.2.1]
        exact ih r hr_sp.1 (by { omega })
  }
  have hz1_le : g (z + 1) ≤ prefixMaxFn g z_prev := by {
    rw [hgap_sp.1, ← hret.2.2.2.1]
    exact h_all (z + 1 - g (z + 2)) (by { omega })
  }
  have hpm_eq : prefixMaxFn g z = max (prefixMaxFn g z_prev) (g (z - 1)) := by {
    apply le_antisymm
    · rw [prefixMaxFn_le_iff]
      intro k hk
      rcases lt_or_eq_of_le hk with hlt_z | rfl
      · rcases lt_or_eq_of_le (by { omega } : k ≤ z - 1) with hlt_z1 | rfl
        · exact le_trans (h_all k hlt_z1) (Nat.le_max_left _ _)
        · exact Nat.le_max_right _ _
      · rw [hz]
        exact Nat.zero_le _
    · exact max_le (hpm.2 z_prev z (Nat.le_of_lt h_lt))
        (le_trans (hpm.1 (z - 1)) (hpm.2 (z - 1) z (by { omega })))
  }
  exact ⟨h_all, hz1_le, by { omega }, hpm_eq⟩
}

lemma isVanEckFrom_first_occ_birth (g : ℕ → ℕ) (M_0 m : ℕ)
    (h_rec : IsVanEckFrom g M_0) :
    ∃ b ≤ m, g b = g m ∧ (∀ i < b, g i ≠ g m) ∧ (M_0 < b → g (b + 1) = 0) := by {
  classical
  have hex : ∃ i, g i = g m := ⟨m, rfl⟩
  let b := Nat.find hex
  have hb_eq : g b = g m := Nat.find_spec hex
  have hb_le : b ≤ m := Nat.find_min' hex rfl
  have hb_min : ∀ i < b, g i ≠ g m := fun i hi => Nat.find_min hex hi
  refine ⟨b, hb_le, hb_eq, hb_min, fun hb_gt => ?_⟩
  have hnone : lastOccBeforeFn g b (g b) = none :=
    (lastOccBeforeFn_eq_none_iff g b (g b)).mpr (fun i hi => hb_eq ▸ hb_min i hi)
  have hr := h_rec b (Nat.le_of_lt hb_gt)
  rw [hnone] at hr
  exact hr
}

/--
Earliest-Occurrence Birth Dichotomy in a Consecutive-Zero Block:
any positive value `v` occurring at `m ≤ z + 1` with `v ≠ g (z - 1)` first appeared strictly
before `z_prev`, hence either in `[0, M_0]` or at a birth zero `M_0 + 1 < z_b ≤ z_prev`.
-/
lemma isVanEckFrom_earlier_birth_dichotomy (g : ℕ → ℕ) (M_0 z_prev z m : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (hm_le : m ≤ z + 1) (hm_pos : 0 < g m) (hm_ne : g m ≠ g (z - 1)) :
    (∃ i ≤ M_0, g i = g m) ∨
      ∃ z_b, M_0 + 1 < z_b ∧ z_b ≤ z_prev ∧ z_b - 1 ≤ m ∧
        g z_b = 0 ∧ g (z_b - 1) = g m ∧ ∀ i < z_b - 1, g i ≠ g m := by {
  have hgap_sp := isVanEckFrom_zero_gap_eq_and_ge_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hret := isVanEckFrom_post_zero_return_spec g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  rcases isVanEckFrom_first_occ_birth g M_0 m h_rec with
    ⟨b, hb_le_m, hb_eq, hb_min, hb_zero⟩
  have hb_lt_zp : b < z_prev := by {
    by_contra hb_ge
    by_cases hb_z1 : b = z + 1
    · exact hb_min (z + 1 - g (z + 2)) (by { omega })
        (hret.2.2.2.1.trans (hgap_sp.1.symm.trans (hb_z1 ▸ hb_eq)))
    · by_cases hb_z : b = z
      · exact (by { omega } : g b ≠ 0) (hb_z ▸ hz)
      · by_cases hb_zm1 : b = z - 1
        · exact hm_ne (hb_eq.symm.trans (congrArg g hb_zm1))
        · by_cases hb_zp : b = z_prev
          · exact (by { omega } : g b ≠ 0) (hb_zp ▸ hzp)
          · exact (h_gap (b + 1) (by { omega }) (by { omega })) (hb_zero (by { omega }))
  }
  by_cases hb_M : b ≤ M_0
  · exact Or.inl ⟨b, hb_M, hb_eq⟩
  · exact Or.inr ⟨b + 1, by { omega }, by { omega }, by { omega },
      hb_zero (by { omega }), hb_eq, hb_min⟩
}

/--
Zero-Gap Birth Dichotomy for `IsVanEckFrom g M_0`: for consecutive zeros `1 ≤ z_prev < z`
(`M_0 ≤ z_prev`), the zero gap `z - z_prev` either occurred in `[0, M_0]` or was born at a
strictly earlier zero `M_0 + 1 < z_b ≤ z_prev` satisfying `z_b - 1 ≤ z + 1 - g (z + 2)`.
-/
lemma isVanEckFrom_zero_gap_birth_dichotomy (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0) :
    (∃ i ≤ M_0, g i = z - z_prev) ∨
      ∃ z_b, M_0 + 1 < z_b ∧ z_b ≤ z_prev ∧ z_b - 1 ≤ z + 1 - g (z + 2) ∧
        g z_b = 0 ∧ g (z_b - 1) = z - z_prev ∧ ∀ i < z_b - 1, g i ≠ z - z_prev := by {
  have hgap_sp := isVanEckFrom_zero_gap_eq_and_ge_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hret := isVanEckFrom_post_zero_return_spec g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hq_le : z + 1 - g (z + 2) ≤ z - 2 := hret.2.2.1
  have hq_val : g (z + 1 - g (z + 2)) = z - z_prev := hret.2.2.2.1
  have hq_ne_z1 : g (z + 1 - g (z + 2)) ≠ g (z - 1) := by {
    intro heq
    have hr := h_rec (z - 1) (by { omega })
    have hidx : z - 1 + 1 = z := by { omega }
    rw [hidx, hz] at hr
    cases h_occ : lastOccBeforeFn g (z - 1) (g (z - 1)) with
    | none =>
      exact ((lastOccBeforeFn_eq_none_iff g (z - 1) (g (z - 1))).mp h_occ)
        (z + 1 - g (z + 2)) (by { omega }) heq
    | some r =>
      rw [h_occ] at hr
      have hr_lt := (lastOccBeforeFn_eq_some_spec g (z - 1) (g (z - 1)) r h_occ).1
      change 0 = z - 1 - r at hr
      omega
  }
  have hd := isVanEckFrom_earlier_birth_dichotomy g M_0 z_prev z (z + 1 - g (z + 2))
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
    (by { omega }) (by { omega }) hq_ne_z1
  rw [hq_val] at hd
  exact hd
}

/--
Record-Jump Anchor Identity for `IsVanEckFrom g M_0`:
at a consecutive-zero record jump `prefixMaxFn g z_prev < prefixMaxFn g z`, the pre-zero anchor
`p = z - 2 - g (z - 1)` (`p + 3 ≤ z_prev`) and post-zero anchor `q = z + 1 - g (z + 2)`
satisfy the exact subtraction-free identity `g (z + 2) + q = g (z - 1) + p + 3`.
-/
lemma isVanEckFrom_record_jump_anchor_identity (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z) :
    prefixMaxFn g z = g (z - 1) ∧
      4 ≤ g (z - 1) ∧
      (z - 2 - g (z - 1)) + 3 ≤ z_prev ∧
      g (z - 2 - g (z - 1)) = g (z - 2) ∧
      (∀ j, z - 2 - g (z - 1) < j → j < z - 2 → g j ≠ g (z - 2)) ∧
      z - 2 - (z - 2 - g (z - 1)) = g (z - 1) ∧
      z + 1 - (z + 1 - g (z + 2)) = g (z + 2) ∧
      g (z + 2) + (z + 1 - g (z + 2)) = g (z - 1) + (z - 2 - g (z - 1)) + 3 := by {
  have hblk := isVanEckFrom_block_le_prefixMax_prev g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hgap_sp := isVanEckFrom_zero_gap_eq_and_ge_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hret := isVanEckFrom_post_zero_return_spec g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hz1_gt : prefixMaxFn g z_prev < g (z - 1) := by { omega }
  have hr_z2 := h_rec (z - 2) (by { omega })
  have hidx_z1 : z - 2 + 1 = z - 1 := by { omega }
  rw [hidx_z1] at hr_z2
  cases h_occ : lastOccBeforeFn g (z - 2) (g (z - 2)) with
  | none =>
    rw [h_occ] at hr_z2
    change g (z - 1) = 0 at hr_z2
    omega
  | some p =>
    rw [h_occ] at hr_z2
    change g (z - 1) = z - 2 - p at hr_z2
    have hp_sp := lastOccBeforeFn_eq_some_spec g (z - 2) (g (z - 2)) p h_occ
    have hp_lt := hp_sp.1
    have hp_eq : z - 2 - g (z - 1) = p := by { omega }
    have hgap_le : z - z_prev ≤ prefixMaxFn g z_prev := hgap_sp.1 ▸ hblk.2.1
    have h_p_val : g (z - 2 - g (z - 1)) = g (z - 2) := hp_eq.symm ▸ hp_sp.2.1
    have h_p_min : ∀ j, z - 2 - g (z - 1) < j → j < z - 2 → g j ≠ g (z - 2) :=
      hp_eq.symm ▸ hp_sp.2.2
    exact ⟨by { omega }, by { omega }, by { omega }, h_p_val, h_p_min,
      by { omega }, by { omega }, by { omega }⟩
}

lemma isVanEckFrom_zero_at_add_three_of_none (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (hnone : lastOccBeforeFn g (z + 2) (g (z + 2)) = none) :
    g (z + 3) = 0 ∧
      (∀ k, z < k → k < z + 3 → g k ≠ 0) ∧
      (z + 3) - 2 - g ((z + 3) - 1) = z + 1 - g (z + 2) ∧
      g (z + 4) = 3 := by {
  have hgap_sp := isVanEckFrom_zero_gap_eq_and_ge_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hret := isVanEckFrom_post_zero_return_spec g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hz3 : g (z + 3) = 0 := by {
    have hr := h_rec (z + 2) (by { omega })
    rw [hnone] at hr
    exact hr
  }
  have hgap3 : ∀ k, z < k → k < z + 3 → g k ≠ 0 := by {
    intro k hk1 hk2
    by_cases hk_eq1 : k = z + 1
    · rw [hk_eq1]
      omega
    · have hk_eq2 : k = z + 2 := by { omega }
      rw [hk_eq2]
      omega
  }
  have hz4 := (isVanEckFrom_zero_gap_eq_and_ge_three g M_0 z (z + 3)
    hg0 h_rec h_no2 (by { omega }) (by { omega }) (by { omega }) hz hz3 hgap3).1
  change g (z + 4) = (z + 3) - z at hz4
  exact ⟨hz3, hgap3, rfl, by { omega }⟩
}

/--
Record-Jump Case 1 (`q ≤ p + 2`): `g (z + 2) > g (z - 1)` is a fresh record, forcing the next zero
at `z + 3`, making `z + 3` a new record-jump zero with pre-zero anchor `p(z + 3) = q`, and
emitting `g (z + 4) = 3`.
-/
lemma isVanEckFrom_record_jump_case_le_add_two (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z)
    (h_case1 : z + 1 - g (z + 2) ≤ (z - 2 - g (z - 1)) + 2) :
    g (z - 1) < g (z + 2) ∧
      g (z + 3) = 0 ∧
      (∀ k, z < k → k < z + 3 → g k ≠ 0) ∧
      prefixMaxFn g z < prefixMaxFn g (z + 3) ∧
      prefixMaxFn g (z + 3) = g (z + 2) ∧
      (z + 3) - 2 - g ((z + 3) - 1) = z + 1 - g (z + 2) ∧
      g (z + 4) = 3 := by {
  have hid := isVanEckFrom_record_jump_anchor_identity g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump
  have hblk := isVanEckFrom_block_le_prefixMax_prev g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hgt_rec : g (z - 1) < g (z + 2) := by { omega }
  have hpm_z1 : prefixMaxFn g (z + 1) = g (z - 1) := by {
    change max (prefixMaxFn g z) (g (z + 1)) = g (z - 1)
    omega
  }
  have hnone : lastOccBeforeFn g (z + 2) (g (z + 2)) = none := by {
    rw [lastOccBeforeFn_eq_none_iff]
    intro i hi
    have hi_le : g i ≤ prefixMaxFn g (z + 1) :=
      le_trans ((le_prefixMaxFn_and_mono g).1 i)
        ((le_prefixMaxFn_and_mono g).2 i (z + 1) (by { omega }))
    omega
  }
  rcases isVanEckFrom_zero_at_add_three_of_none g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap hnone with ⟨hz3, hgap3, hp3, hz4⟩
  have hpm_z3 : prefixMaxFn g (z + 3) = g (z + 2) := by {
    change max (max (prefixMaxFn g (z + 1)) (g (z + 2))) (g (z + 3)) = g (z + 2)
    omega
  }
  exact ⟨hgt_rec, hz3, hgap3, by { omega }, hpm_z3, hp3, hz4⟩
}

/--
Record-Jump Case 2 (`q = p + 3`): `g (z + 2) = g (z - 1)`, and since `g (z - 1)` was born at
`z - 1` (`g z = 0`, `g (z + 1) < g (z - 1)`), the next term is `g (z + 3) = 3`.
-/
lemma isVanEckFrom_record_jump_case_eq_add_three (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z)
    (h_case2 : z + 1 - g (z + 2) = (z - 2 - g (z - 1)) + 3) :
    g (z + 2) = g (z - 1) ∧
      g (z + 3) = 3 ∧
      prefixMaxFn g (z + 3) = g (z - 1) := by {
  have hid := isVanEckFrom_record_jump_anchor_identity g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump
  have hblk := isVanEckFrom_block_le_prefixMax_prev g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have heq_rec : g (z + 2) = g (z - 1) := by { omega }
  have h_occ : lastOccBeforeFn g (z + 2) (g (z + 2)) = some (z - 1) :=
    lastOccBeforeFn_eq_some_of_prev g (z + 2) (z - 1) (g (z + 2)) (by { omega }) heq_rec.symm
      (fun k hk1 hk2 => by {
        by_cases hk_z : k = z
        · rw [hk_z, hz]
          omega
        · have hk_eq1 : k = z + 1 := by { omega }
          rw [hk_eq1]
          omega
      })
  have hz3 : g (z + 3) = 3 := by {
    have hr := h_rec (z + 2) (by { omega })
    rw [h_occ] at hr
    change g (z + 3) = z + 2 - (z - 1) at hr
    omega
  }
  have hpm_z3 : prefixMaxFn g (z + 3) = g (z - 1) := by {
    change max (max (max (prefixMaxFn g z) (g (z + 1))) (g (z + 2))) (g (z + 3)) = g (z - 1)
    omega
  }
  exact ⟨heq_rec, hz3, hpm_z3⟩
}

/--
Record-Jump Case 3 (`p + 4 ≤ q`): `3 ≤ g (z + 2) < g (z - 1)`, and either `g (z + 2)` is fresh
(`g (z + 3) = 0`, non-record-jump zero with `prefixMaxFn g (z + 3) = g (z - 1)` and `p(z + 3) = q`)
or `g (z + 3) ≠ 0` and `g (z + 2)` returns to an earlier birth class (`≤ M_0` or `z_R ≤ z_prev`).
-/
lemma isVanEckFrom_record_jump_case_ge_add_four (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z)
    (h_case3 : (z - 2 - g (z - 1)) + 4 ≤ z + 1 - g (z + 2)) :
    3 ≤ g (z + 2) ∧
      g (z + 2) < g (z - 1) ∧
      ((g (z + 3) = 0 ∧ prefixMaxFn g (z + 3) = g (z - 1) ∧
          (z + 3) - 2 - g ((z + 3) - 1) = z + 1 - g (z + 2) ∧ g (z + 4) = 3) ∨
        (g (z + 3) ≠ 0 ∧
          ((∃ i ≤ M_0, g i = g (z + 2)) ∨
            ∃ z_R, M_0 + 1 < z_R ∧ z_R ≤ z_prev ∧
              g z_R = 0 ∧ g (z_R - 1) = g (z + 2) ∧ ∀ i < z_R - 1, g i ≠ g (z + 2)))) := by {
  have hid := isVanEckFrom_record_jump_anchor_identity g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump
  have hblk := isVanEckFrom_block_le_prefixMax_prev g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hret := isVanEckFrom_post_zero_return_spec g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hlt_rec : g (z + 2) < g (z - 1) := by { omega }
  refine ⟨hret.1, hlt_rec, ?_⟩
  cases h_occ : lastOccBeforeFn g (z + 2) (g (z + 2)) with
  | none =>
    rcases isVanEckFrom_zero_at_add_three_of_none g M_0 z_prev z
      hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_occ with ⟨hz3, _, hp3, hz4⟩
    have hpm_z3 : prefixMaxFn g (z + 3) = g (z - 1) := by {
      change max (max (max (prefixMaxFn g z) (g (z + 1))) (g (z + 2))) (g (z + 3)) = g (z - 1)
      omega
    }
    exact Or.inl ⟨hz3, hpm_z3, hp3, hz4⟩
  | some r =>
    have hr2 := h_rec (z + 2) (by { omega })
    rw [h_occ] at hr2
    have hr_sp := lastOccBeforeFn_eq_some_spec g (z + 2) (g (z + 2)) r h_occ
    have hr_lt := hr_sp.1
    change g (z + 3) = z + 2 - r at hr2
    have hd := isVanEckFrom_earlier_birth_dichotomy g M_0 z_prev z r
      hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
      (by { omega }) (by { omega }) (hr_sp.2.1 ▸ ne_of_lt hlt_rec)
    rw [hr_sp.2.1] at hd
    refine Or.inr ⟨by { omega }, ?_⟩
    rcases hd with hpre | ⟨z_R, hzR_gt, hzR_le, _, hzR0, hzR_eq, hzR_min⟩
    · exact Or.inl hpre
    · exact Or.inr ⟨z_R, hzR_gt, hzR_le, hzR0, hzR_eq, hzR_min⟩
}

/--
Generic `IsVanEckFrom` Record-Jump Anchor Trichotomy (`q ≤ p + 2`, `q = p + 3`, `p + 4 ≤ q`).
-/
theorem isVanEckFrom_record_jump_anchor_trichotomy (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z) :
    let p := z - 2 - g (z - 1)
    let q := z + 1 - g (z + 2)
    (q ≤ p + 2 ∧ g (z - 1) < g (z + 2) ∧ g (z + 3) = 0 ∧
        prefixMaxFn g z < prefixMaxFn g (z + 3) ∧
        (z + 3) - 2 - g ((z + 3) - 1) = q ∧ g (z + 4) = 3) ∨
      (q = p + 3 ∧ g (z + 2) = g (z - 1) ∧ g (z + 3) = 3 ∧
        prefixMaxFn g (z + 3) = g (z - 1)) ∨
      (p + 4 ≤ q ∧ 3 ≤ g (z + 2) ∧ g (z + 2) < g (z - 1)) := by {
  dsimp only
  let p := z - 2 - g (z - 1)
  let q := z + 1 - g (z + 2)
  by_cases h1 : q ≤ p + 2
  · rcases isVanEckFrom_record_jump_case_le_add_two g M_0 z_prev z
      hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump h1 with
      ⟨hgt, hz3, _, hjmp3, _, hp3, hz4⟩
    exact Or.inl ⟨h1, hgt, hz3, hjmp3, hp3, hz4⟩
  · by_cases h2 : q = p + 3
    · rcases isVanEckFrom_record_jump_case_eq_add_three g M_0 z_prev z
        hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump h2 with ⟨heq, hz3, hpm3⟩
      exact Or.inr (Or.inl ⟨h2, heq, hz3, hpm3⟩)
    · have h3 : p + 4 ≤ q := by { omega }
      rcases isVanEckFrom_record_jump_case_ge_add_four g M_0 z_prev z
        hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump h3 with ⟨hge3, hlt, _⟩
      exact Or.inr (Or.inr ⟨h3, hge3, hlt⟩)
}

lemma isVanEckFrom_three_repeat_pair (g : ℕ → ℕ) (M_0 a : ℕ)
    (h_rec : IsVanEckFrom g M_0) (ha_M : M_0 ≤ a + 3)
    (ha3 : g a = 3) (ha_add3 : g (a + 3) = 3)
    (h_no3 : ∀ k, a < k → k < a + 3 → g k ≠ 3) :
    g (a + 4) = 3 ∧ g (a + 5) = 1 := by {
  have hocc1 : lastOccBeforeFn g (a + 3) 3 = some a :=
    lastOccBeforeFn_eq_some_of_prev g (a + 3) a 3 (by { omega }) ha3 h_no3
  have ha4 : g (a + 4) = 3 := by {
    have hr := h_rec (a + 3) ha_M
    rw [ha_add3, hocc1] at hr
    change g (a + 4) = a + 3 - a at hr
    omega
  }
  have hocc2 : lastOccBeforeFn g (a + 4) 3 = some (a + 3) :=
    lastOccBeforeFn_eq_some_of_prev g (a + 4) (a + 3) 3 (by { omega }) ha_add3
      (fun _ hk1 hk2 => by { omega })
  have ha5 : g (a + 5) = 1 := by {
    have hr := h_rec (a + 4) (by { omega })
    rw [ha4, hocc2] at hr
    change g (a + 5) = a + 4 - (a + 3) at hr
    omega
  }
  exact ⟨ha4, ha5⟩
}

/--
1-Step Case-1 Exit when `z - z_prev = 3`: if `z - z_prev = 3` and `q(z) ≤ p(z) + 2`, then at the
next record-jump zero `z + 3`, `g (z + 1) = 3` forces `q(z + 3) = z + 1 ≥ p(z + 3) + 5`
(`g (z + 5) = 3`, `g (z + 6) = 1`), immediately exiting Case 1.
-/
lemma isVanEckFrom_case1_exits_if_gap_three (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z)
    (h_case1 : z + 1 - g (z + 2) ≤ (z - 2 - g (z - 1)) + 2)
    (h_gap3 : z - z_prev = 3) :
    (z + 3) + 1 - g ((z + 3) + 2) = z + 1 ∧
      ((z + 3) - 2 - g ((z + 3) - 1)) + 5 ≤ (z + 3) + 1 - g ((z + 3) + 2) ∧
      g (z + 5) = 3 ∧ g (z + 6) = 1 := by {
  have hid := isVanEckFrom_record_jump_anchor_identity g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump
  rcases isVanEckFrom_record_jump_case_le_add_two g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump h_case1 with
    ⟨hgt2, hz3, _, _, _, hp3, hz4⟩
  have hz1_3 : g (z + 1) = 3 := (isVanEckFrom_zero_gap_eq_and_ge_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap).1.trans h_gap3
  rcases isVanEckFrom_three_repeat_pair g M_0 (z + 1) h_rec (by { omega }) hz1_3 hz4
    (fun k hk1 hk2 => by {
      by_cases hk_eq2 : k = z + 2
      · rw [hk_eq2]
        omega
      · have hk_eq3 : k = z + 3 := by { omega }
        rw [hk_eq3, hz3]
        decide
    }) with ⟨hz5, hz6⟩
  change g (z + 5) = 3 at hz5
  change g (z + 6) = 1 at hz6
  have h5_idx : (z + 3) + 2 = z + 5 := rfl
  rw [h5_idx, hz5, hp3]
  exact ⟨by { omega }, by { omega }, rfl, hz6⟩
}

/--
Universal 2-Step Termination of Rigid `+3` Record-Jump Chains:
if both `z` and `z + 3` fall in Case 1 (`q ≤ p + 2`), then `z + 6` is a record-jump zero whose
post-zero anchor is forced by `g (z + 4) = 3` to equal `q(z + 6) = z + 4 ≥ p(z + 6) + 6`
(`g (z + 8) = 3`, `g (z + 9) = 1`).
-/
theorem isVanEckFrom_two_step_case1_forces_case3 (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z)
    (h_c1 : z + 1 - g (z + 2) ≤ (z - 2 - g (z - 1)) + 2)
    (h_c2 : (z + 3) + 1 - g ((z + 3) + 2) ≤ ((z + 3) - 2 - g ((z + 3) - 1)) + 2) :
    g (z + 6) = 0 ∧
      (∀ k, z + 3 < k → k < z + 6 → g k ≠ 0) ∧
      prefixMaxFn g (z + 3) < prefixMaxFn g (z + 6) ∧
      (z + 6) + 1 - g ((z + 6) + 2) = z + 4 ∧
      ((z + 6) - 2 - g ((z + 6) - 1)) + 6 ≤ (z + 6) + 1 - g ((z + 6) + 2) ∧
      g (z + 8) = 3 ∧ g (z + 9) = 1 := by {
  have hid := isVanEckFrom_record_jump_anchor_identity g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump
  rcases isVanEckFrom_record_jump_case_le_add_two g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump h_c1 with
    ⟨hgt2, hz3, hgap3, hjmp3, _, hp3, hz4⟩
  rcases isVanEckFrom_record_jump_case_le_add_two g M_0 z (z + 3)
    hg0 h_rec h_no2 (by { omega }) (by { omega }) (by { omega }) hz hz3 hgap3 hjmp3 h_c2 with
    ⟨hgt5, hz6, hgap6, hjmp6, _, hp6, hz7⟩
  change g (z + 2) < g (z + 5) at hgt5
  change g (z + 6) = 0 at hz6
  change g (z + 7) = 3 at hz7
  rcases isVanEckFrom_three_repeat_pair g M_0 (z + 4) h_rec (by { omega }) hz4 hz7
    (fun k hk1 hk2 => by {
      by_cases hk_eq5 : k = z + 5
      · rw [hk_eq5]
        omega
      · have hk_eq6 : k = z + 6 := by { omega }
        rw [hk_eq6, hz6]
        decide
    }) with ⟨hz8, hz9⟩
  change g (z + 8) = 3 at hz8
  change g (z + 9) = 1 at hz9
  change (z + 6) - 2 - g ((z + 6) - 1) = (z + 3) + 1 - g ((z + 3) + 2) at hp6
  have h8_idx : (z + 6) + 2 = z + 8 := rfl
  rw [h8_idx, hz8, hp6]
  rw [hp3] at h_c2
  exact ⟨hz6, hgap6, hjmp6, by { omega }, by { omega }, rfl, hz9⟩
}

/--
No Three-Step Case-1 Record-Jump Chain: `z`, `z + 3`, and `z + 6` cannot all satisfy `q ≤ p + 2`.
-/
theorem isVanEckFrom_no_three_step_case1_chain (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z) :
    ¬ (z + 1 - g (z + 2) ≤ (z - 2 - g (z - 1)) + 2 ∧
        (z + 3) + 1 - g ((z + 3) + 2) ≤ ((z + 3) - 2 - g ((z + 3) - 1)) + 2 ∧
        (z + 6) + 1 - g ((z + 6) + 2) ≤ ((z + 6) - 2 - g ((z + 6) - 1)) + 2) := by {
  rintro ⟨h1, h2, h3⟩
  have hforce := (isVanEckFrom_two_step_case1_forces_case3 g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump h1 h2).2.2.2.2.1
  omega
}

/--
Every record-jump zero `z` terminates its Case-1 (`+3`) cascade at a consecutive-zero record jump
`z' ∈ {z, z + 3, z + 6}` satisfying `p(z') + 3 ≤ q(z')` (Case 2 or Case 3).
-/
theorem isVanEckFrom_exists_terminal_record_jump (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z) :
    ∃ z_prev' z', z_prev ≤ z_prev' ∧ z ≤ z' ∧ z' ≤ z + 6 ∧ 1 ≤ z_prev' ∧ M_0 ≤ z_prev' ∧
      z_prev' < z' ∧ g z_prev' = 0 ∧ g z' = 0 ∧ (∀ k, z_prev' < k → k < z' → g k ≠ 0) ∧
      prefixMaxFn g z_prev' < prefixMaxFn g z' ∧
      (z' - 2 - g (z' - 1)) + 3 ≤ z' + 1 - g (z' + 2) := by {
  by_cases hc1 : z + 1 - g (z + 2) ≤ (z - 2 - g (z - 1)) + 2
  · rcases isVanEckFrom_record_jump_case_le_add_two g M_0 z_prev z
      hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump hc1 with
      ⟨_, hz3, hgap3, hjmp3, _, _, _⟩
    by_cases hc2 : (z + 3) + 1 - g ((z + 3) + 2) ≤ ((z + 3) - 2 - g ((z + 3) - 1)) + 2
    · rcases isVanEckFrom_two_step_case1_forces_case3 g M_0 z_prev z
        hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump hc1 hc2 with
        ⟨hz6, hgap6, hjmp6, _, hge6, _, _⟩
      exact ⟨z + 3, z + 6, by { omega }, by { omega }, le_rfl, by { omega }, by { omega },
        by { omega }, hz3, hz6, hgap6, hjmp6, by { omega }⟩
    · exact ⟨z, z + 3, by { omega }, by { omega }, by { omega }, by { omega }, by { omega },
        by { omega }, hz, hz3, hgap3, hjmp3, by { omega }⟩
  · exact ⟨z_prev, z, le_rfl, le_rfl, by { omega }, hzp_pos, hzp_M, h_lt, hzp, hz, h_gap,
      h_jump, by { omega }⟩
}

/--
Any unbounded `2`-free `IsVanEckFrom g M_0` sequence (`g 0 = 0`, infinitely many zeros) undergoes
infinitely many terminal (Case-2 or Case-3: `p(z) + 3 ≤ q(z)`) consecutive-zero record jumps.
-/
theorem isVanEckFrom_infinite_terminal_record_jumps (g : ℕ → ℕ) (M_0 : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (h_zeros : ∀ K, ∃ z > K, g z = 0) (h_unb : ∀ B, ∃ j, B < g j) (K V : ℕ) :
    ∃ z_prev z, K < z_prev ∧ M_0 ≤ z_prev ∧ z_prev < z ∧ g z_prev = 0 ∧ g z = 0 ∧
      (∀ k, z_prev < k → k < z → g k ≠ 0) ∧
      V < prefixMaxFn g z_prev ∧ prefixMaxFn g z_prev < prefixMaxFn g z ∧
      (z - 2 - g (z - 1)) + 3 ≤ z + 1 - g (z + 2) := by {
  rcases infinite_record_jumps_of_zeros_and_unbounded g h_zeros h_unb (max K M_0) V with
    ⟨zp0, z0, hgt0, hlt0, hzp0, hz0, hgap0, hV0, hjmp0⟩
  rcases isVanEckFrom_exists_terminal_record_jump g M_0 zp0 z0
    hg0 h_rec h_no2 (by { omega }) (by { omega }) hlt0 hzp0 hz0 hgap0 hjmp0 with
    ⟨z_prev, z, hzp_le, _, _, _, hM, hlt, hzp, hz, hgap, hjmp, hterm⟩
  have hV : V < prefixMaxFn g z_prev :=
    lt_of_lt_of_le hV0 ((le_prefixMaxFn_and_mono g).2 zp0 z_prev hzp_le)
  exact ⟨z_prev, z, by { omega }, hM, hlt, hzp, hz, hgap, hV, hjmp, hterm⟩
}

/--
Exact Slack Formula for Terminal Record Jumps (`p + 3 ≤ q`):
`R = g (z + 2) ≤ g (z - 1) = X` and `q - p - 3 = X - R`, vanishing iff `q = p + 3` (Case 2)
and strictly positive iff `p + 4 ≤ q` (Case 3).
-/
lemma isVanEckFrom_terminal_jump_slack_eq (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z)
    (h_term : (z - 2 - g (z - 1)) + 3 ≤ z + 1 - g (z + 2)) :
    g (z + 2) ≤ g (z - 1) ∧
      (z + 1 - g (z + 2)) - (z - 2 - g (z - 1)) - 3 = g (z - 1) - g (z + 2) ∧
      (z + 1 - g (z + 2) = (z - 2 - g (z - 1)) + 3 ↔ g (z + 2) = g (z - 1)) ∧
      ((z - 2 - g (z - 1)) + 4 ≤ z + 1 - g (z + 2) ↔ g (z + 2) < g (z - 1)) := by {
  have hid := isVanEckFrom_record_jump_anchor_identity g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump
  exact ⟨by { omega }, by { omega }, by { omega }, by { omega }⟩
}

/--
In Case 2 (`q = p + 3`), `z - z_prev = g (z + 1) ≠ 3` (`4 ≤ z - z_prev`), since `g (z + 1) = 3`
together with `g (z + 2) = g (z - 1) ≥ 4` and `g (z + 3) = 3` would force `g (z + 4) = 2`.
-/
lemma isVanEckFrom_case2_gap_ge_four (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z)
    (h_case2 : z + 1 - g (z + 2) = (z - 2 - g (z - 1)) + 3) :
    4 ≤ z - z_prev ∧ g (z + 1) ≠ 3 := by {
  have hid := isVanEckFrom_record_jump_anchor_identity g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump
  have hc2 := isVanEckFrom_record_jump_case_eq_add_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump h_case2
  have hgap_sp := isVanEckFrom_zero_gap_eq_and_ge_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hne3 : g (z + 1) ≠ 3 := by {
    intro hz1_3
    have hocc3 : lastOccBeforeFn g (z + 3) 3 = some (z + 1) :=
      lastOccBeforeFn_eq_some_of_prev g (z + 3) (z + 1) 3 (by { omega }) hz1_3
        (fun k hk1 hk2 => by {
          have hk_eq : k = z + 2 := by { omega }
          rw [hk_eq]
          omega
        })
    have hr3 := h_rec (z + 3) (by { omega })
    rw [hc2.2.1, hocc3] at hr3
    change g (z + 4) = z + 3 - (z + 1) at hr3
    exact h_no2 (z + 4) (by { omega }) (by { omega })
  }
  exact ⟨by { omega }, hne3⟩
}

lemma isVanEckFrom_case2_raw_three_return (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z)
    (h_case2 : z + 1 - g (z + 2) = (z - 2 - g (z - 1)) + 3)
    (h_ex3 : ∃ i < z + 3, g i = 3) :
    5 ≤ g (z + 4) ∧
      g (z + 4) ≤ z + 3 ∧
      z + 3 - g (z + 4) ≤ z - 2 ∧
      g (z + 3 - g (z + 4)) = 3 ∧
      (∀ j, z + 3 - g (z + 4) < j → j < z + 3 → g j ≠ 3) := by {
  have hid := isVanEckFrom_record_jump_anchor_identity g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump
  have hc2 := isVanEckFrom_record_jump_case_eq_add_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump h_case2
  have hg4 := isVanEckFrom_case2_gap_ge_four g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump h_case2
  rcases h_ex3 with ⟨i0, hi0_lt, hi0_eq⟩
  have hr3 := h_rec (z + 3) (by { omega })
  rw [hc2.2.1] at hr3
  cases h_occ : lastOccBeforeFn g (z + 3) 3 with
  | none =>
    exact False.elim (((lastOccBeforeFn_eq_none_iff g (z + 3) 3).mp h_occ) i0 hi0_lt hi0_eq)
  | some s =>
    rw [h_occ] at hr3
    change g (z + 4) = z + 3 - s at hr3
    have hs_sp := lastOccBeforeFn_eq_some_spec g (z + 3) 3 s h_occ
    have hs_lt := hs_sp.1
    have hs_val := hs_sp.2.1
    have hs_le : s ≤ z - 2 := by {
      by_contra hgt
      by_cases hs2 : s = z + 2
      · rw [hs2] at hs_val
        omega
      · by_cases hs1 : s = z + 1
        · exact hg4.2 (hs1 ▸ hs_val)
        · by_cases hsz : s = z
          · rw [hsz] at hs_val
            omega
          · have hsz1 : s = z - 1 := by { omega }
            rw [hsz1] at hs_val
            omega
    }
    have hs_eq : z + 3 - g (z + 4) = s := by { omega }
    rw [hs_eq]
    exact ⟨by { omega }, by { omega }, hs_le, hs_val, hs_sp.2.2⟩
}

/--
Case-2 Secondary `3`-Return Specification:
whenever `3` appeared before `z + 3`, `g (z + 3) = 3` forces `5 ≤ g (z + 4) ≤ z + 3`, secondary
anchor `s = z + 3 - g (z + 4) ≤ z - 2`, exact identity `g (z + 4) + s = g (z - 1) + p + 5`,
and forbidden resonance `s ≠ p + 5` (`g (z + 4) ≠ g (z - 1)`).
-/
lemma isVanEckFrom_case2_three_return_spec (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z)
    (h_case2 : z + 1 - g (z + 2) = (z - 2 - g (z - 1)) + 3)
    (h_ex3 : ∃ i < z + 3, g i = 3) :
    5 ≤ g (z + 4) ∧
      z + 3 - g (z + 4) ≤ z - 2 ∧
      g (z + 3 - g (z + 4)) = 3 ∧
      (∀ j, z + 3 - g (z + 4) < j → j < z + 3 → g j ≠ 3) ∧
      g (z + 4) + (z + 3 - g (z + 4)) = g (z - 1) + (z - 2 - g (z - 1)) + 5 ∧
      z + 3 - g (z + 4) ≠ (z - 2 - g (z - 1)) + 5 ∧
      (∀ k, z < k → k < z + 5 → g k ≠ 0) := by {
  have hid := isVanEckFrom_record_jump_anchor_identity g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump
  have hc2 := isVanEckFrom_record_jump_case_eq_add_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump h_case2
  have hgap_sp := isVanEckFrom_zero_gap_eq_and_ge_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hraw := isVanEckFrom_case2_raw_three_return g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump h_case2 h_ex3
  have hne_res : z + 3 - g (z + 4) ≠ (z - 2 - g (z - 1)) + 5 := fun hres => by {
    have hz4_eq : g (z + 4) = g (z - 1) := by { omega }
    have hocc4 := lastOccBeforeFn_eq_some_of_prev g (z + 4) (z + 2) (g (z - 1))
      (by { omega }) hc2.1 (fun k hk1 hk2 => by {
        have hk_eq : k = z + 3 := by { omega }
        rw [hk_eq, hc2.2.1]
        omega
      })
    have hr4 := h_rec (z + 4) (by { omega })
    rw [hz4_eq, hocc4] at hr4
    change g (z + 5) = z + 4 - (z + 2) at hr4
    exact h_no2 (z + 5) (by { omega }) (by { omega })
  }
  have hnz5 : ∀ k, z < k → k < z + 5 → g k ≠ 0 := fun k hk1 hk2 => by {
    rcases lt_trichotomy k (z + 2) with _ | rfl | _
    · have hk1_eq : k = z + 1 := by { omega }
      rw [hk1_eq]
      omega
    · omega
    · rcases eq_or_lt_of_le (by { omega } : k ≤ z + 4) with rfl | _
      · omega
      · have hk3_eq : k = z + 3 := by { omega }
        rw [hk3_eq]
        omega
  }
  exact ⟨hraw.1, hraw.2.2.1, hraw.2.2.2.1, hraw.2.2.2.2, by { omega }, hne_res, hnz5⟩
}

/--
Ordering and Anchor Disjointness of Secondary Case-2 Anchors `s(z) = z + 3 - g (z + 4)`:
`s(z)` is strictly ordered across Case-2 jumps (`z_1 + 3 ≤ s(z_2)`, `g(z_2 + 4) ≤ z_2 - z_1`)
and globally disjoint from every post-zero anchor `q(z')`.
-/
lemma isVanEckFrom_case2_secondary_anchor_order_and_disjoint (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z)
    (h_case2 : z + 1 - g (z + 2) = (z - 2 - g (z - 1)) + 3)
    (h_ex3 : ∃ i < z + 3, g i = 3) :
    (∀ z_prev2 z2, z < z2 → 1 ≤ z_prev2 → M_0 ≤ z_prev2 → z_prev2 < z2 →
      g z_prev2 = 0 → g z2 = 0 → (∀ k, z_prev2 < k → k < z2 → g k ≠ 0) →
      prefixMaxFn g z_prev2 < prefixMaxFn g z2 →
      z2 + 1 - g (z2 + 2) = (z2 - 2 - g (z2 - 1)) + 3 →
      z + 3 ≤ z2 + 3 - g (z2 + 4) ∧ g (z2 + 4) ≤ z2 - z) ∧
    (∀ z_prev' z', 1 ≤ z_prev' → M_0 ≤ z_prev' → z_prev' < z' →
      g z_prev' = 0 → g z' = 0 → (∀ k, z_prev' < k → k < z' → g k ≠ 0) →
      z + 3 - g (z + 4) ≠ z' + 1 - g (z' + 2)) := by {
  have hs1 := isVanEckFrom_case2_three_return_spec g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump h_case2 h_ex3
  have hc2 := isVanEckFrom_record_jump_case_eq_add_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap h_jump h_case2
  refine ⟨?_, ?_⟩
  · intro zp2 z2 hzz2 hp2 hM2 hlt2 hzp2 hz2 hgap2 hjmp2 hc2_2
    have hz2_ge5 : z + 5 ≤ z2 := by {
      by_contra hlt5
      exact hs1.2.2.2.2.2.2 z2 hzz2 (by { omega }) hz2
    }
    have hs2 := isVanEckFrom_case2_raw_three_return g M_0 zp2 z2
      hg0 h_rec h_no2 hp2 hM2 hlt2 hzp2 hz2 hgap2 hjmp2 hc2_2 ⟨z + 3, by { omega }, hc2.2.1⟩
    have hge_z3 : z + 3 ≤ z2 + 3 - g (z2 + 4) := by {
      by_contra hlt3
      exact hs2.2.2.2.2 (z + 3) (by { omega }) (by { omega }) hc2.2.1
    }
    exact ⟨hge_z3, by { omega }⟩
  · intro zp' z' hp' hM' hlt' hzp' hz' hgap'
    have hret' := isVanEckFrom_post_zero_return_spec g M_0 zp' z'
      hg0 h_rec h_no2 hp' hM' hlt' hzp' hz' hgap'
    have hne_z2 : z' ≠ z + 2 := fun heq => hs1.2.2.2.2.2.2 z' (by { omega }) (by { omega }) hz'
    rcases lt_trichotomy (z + 4) (z' + 2) with hlt1 | heq1 | hgt1
    · exact isVanEckFrom_lookback_anchor_unique g M_0 (z + 4) (z' + 2) h_rec
        (by { omega }) hlt1 (by { omega }) (by { omega })
    · omega
    · exact Ne.symm (isVanEckFrom_lookback_anchor_unique g M_0 (z' + 2) (z + 4) h_rec
        (by { omega }) hgt1 (by { omega }) (by { omega }))
}

/--
Case-3 Fresh Finset Cardinality Bound: across any `Finset` `CF` of indices `z ≤ N` where
`3 ≤ g (z + 2) ≤ prefixMaxFn g N` and `g (z + 3) = 0` (`M_0 ≤ z + 2`), `z ↦ g (z + 2)` is
injective on `CF`, yielding `CF.card ≤ prefixMaxFn g N - 2`.
-/
lemma isVanEckFrom_case3_fresh_card_bound (g : ℕ → ℕ) (M_0 N : ℕ)
    (h_rec : IsVanEckFrom g M_0) (CF : Finset ℕ)
    (hCF : ∀ z ∈ CF, M_0 ≤ z + 2 ∧ z ≤ N ∧ 3 ≤ g (z + 2) ∧
      g (z + 2) ≤ prefixMaxFn g N ∧ g (z + 3) = 0) :
    CF.card ≤ prefixMaxFn g N - 2 := by {
  have hinj : Set.InjOn (fun z => g (z + 2)) ↑CF := by {
    have ne_lt : ∀ a ∈ CF, ∀ b ∈ CF, a < b → g (a + 2) ≠ g (b + 2) := by {
      intro a ha b hb hlt heq
      have hb_sp := hCF b hb
      have hr := h_rec (b + 2) hb_sp.1
      rw [hb_sp.2.2.2.2] at hr
      cases h_occ : lastOccBeforeFn g (b + 2) (g (b + 2)) with
      | none =>
        exact ((lastOccBeforeFn_eq_none_iff g (b + 2) (g (b + 2))).mp h_occ)
          (a + 2) (by { omega }) heq
      | some r =>
        rw [h_occ] at hr
        have hr_lt := (lastOccBeforeFn_eq_some_spec g (b + 2) (g (b + 2)) r h_occ).1
        change 0 = b + 2 - r at hr
        omega
    }
    intro a ha b hb heq
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · exact False.elim (ne_lt a ha b hb hlt heq)
    · rfl
    · exact False.elim (ne_lt b hb a ha hgt heq.symm)
  }
  have hmaps : Set.MapsTo (fun z => g (z + 2)) ↑CF ↑(Finset.Icc 3 (prefixMaxFn g N)) := by {
    intro z hz
    have hsp := hCF z hz
    exact Finset.mem_Icc.mpr ⟨hsp.2.2.1, hsp.2.2.2.1⟩
  }
  have hle := Finset.card_le_card_of_injOn (fun z => g (z + 2)) hmaps hinj
  rw [Nat.card_Icc] at hle
  omega
}

lemma isVanEckFrom_hit_interval_spec (g : ℕ → ℕ) (M_0 m v b_v : ℕ)
    (h_rec : IsVanEckFrom g M_0) (hb_min : ∀ i < b_v, g i ≠ v)
    (hm_M : M_0 ≤ m) (hgm : g m = v) (hnz : g (m + 1) ≠ 0) :
    g (m + 1) ≤ m ∧ b_v ≤ m - g (m + 1) ∧ 1 ≤ g (m + 1) ∧
      g (m - g (m + 1)) = v ∧ ∀ j, m - g (m + 1) < j → j < m → g j ≠ v := by {
  have hr := h_rec m hm_M
  cases h_occ : lastOccBeforeFn g m (g m) with
  | none =>
    rw [h_occ] at hr
    exact False.elim (hnz hr)
  | some r =>
    rw [h_occ] at hr
    change g (m + 1) = m - r at hr
    have hr_sp := lastOccBeforeFn_eq_some_spec g m (g m) r h_occ
    have hr_lt := hr_sp.1
    have hr_eq : m - g (m + 1) = r := by { omega }
    have hb_le : b_v ≤ r := by {
      by_contra hlt
      exact hb_min r (by { omega }) (hr_sp.2.1.trans hgm)
    }
    rw [hr_eq]
    exact ⟨by { omega }, hb_le, by { omega }, hr_sp.2.1.trans hgm, hgm ▸ hr_sp.2.2⟩
}

/--
Disjoint Return-Interval Sum Bound for Repeated Hits of One Value `v`:
for any `Finset` `S` of indices `m ≤ K` (`M_0 ≤ m`) with `g m = v`, `g (m + 1) ≠ 0`, and first
occurrence `b_v` (`∀ i < b_v, g i ≠ v`), `∑ m ∈ S, g (m + 1) ≤ K - b_v`.
-/
lemma isVanEckFrom_value_return_sum_bound (g : ℕ → ℕ) (M_0 K v b_v : ℕ)
    (h_rec : IsVanEckFrom g M_0) (hb_min : ∀ i < b_v, g i ≠ v)
    (S : Finset ℕ) (hS : ∀ m ∈ S, M_0 ≤ m ∧ m ≤ K ∧ g m = v ∧ g (m + 1) ≠ 0) :
    S.sum (fun m => g (m + 1)) ≤ K - b_v := by {
  have h_sp : ∀ m ∈ S, g (m + 1) ≤ m ∧ b_v ≤ m - g (m + 1) ∧ 1 ≤ g (m + 1) ∧
      g (m - g (m + 1)) = v ∧ ∀ j, m - g (m + 1) < j → j < m → g j ≠ v := fun m hm => by {
    rcases hS m hm with ⟨hm_M, _, hgm, hnz⟩
    exact isVanEckFrom_hit_interval_spec g M_0 m v b_v h_rec hb_min hm_M hgm hnz
  }
  let ivl : ℕ → Finset ℕ := fun m => Finset.Ico (m - g (m + 1)) m
  have hdisj : (↑S : Set ℕ).PairwiseDisjoint ivl := by {
    have disj_lt : ∀ a ∈ S, ∀ b ∈ S, a < b → Disjoint (ivl a) (ivl b) := by {
      intro a ha b hb hlt
      have hsb := h_sp b hb
      have ha_le : a ≤ b - g (b + 1) := by {
        by_contra hgt
        exact hsb.2.2.2.2 a (by { omega }) hlt (hS a ha).2.2.1
      }
      rw [Finset.disjoint_left]
      intro x hxa hxb
      rw [Finset.mem_Ico] at hxa hxb
      omega
    }
    intro a ha b hb hne
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · exact disj_lt a ha b hb hlt
    · exact False.elim (hne rfl)
    · exact (disj_lt b hb a ha hgt).symm
  }
  have hsub : S.biUnion ivl ⊆ Finset.Ico b_v K := by {
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨m, hm, hxm⟩
    rw [Finset.mem_Ico] at hxm ⊢
    have hsm := h_sp m hm
    have hmK := (hS m hm).2.1
    omega
  }
  have hcard := Finset.card_le_card hsub
  rw [Finset.card_biUnion hdisj, Nat.card_Ico] at hcard
  have hsum_eq : S.sum (fun m => (ivl m).card) = S.sum (fun m => g (m + 1)) :=
    Finset.sum_congr rfl (fun m hm => by {
      have hsm := (h_sp m hm).1
      dsimp only [ivl]
      rw [Nat.card_Ico]
      omega
    })
  rw [hsum_eq] at hcard
  exact hcard
}

/--
Case-3 Repeat Per-Birth-Class Sum Bound: for any birth class `v` (first occurring at `b_v`, e.g.
`b_v = z_R - 1`) and any `Finset` `CR` of indices `z ≤ N` (`M_0 ≤ z + 2`) with `g (z + 2) = v`
and `g (z + 3) ≠ 0`, `∑ z ∈ CR, g (z + 3) ≤ N + 2 - b_v`.
-/
lemma isVanEckFrom_case3_repeat_class_sum_bound (g : ℕ → ℕ) (M_0 N v b_v : ℕ)
    (h_rec : IsVanEckFrom g M_0) (hb_min : ∀ i < b_v, g i ≠ v)
    (CR : Finset ℕ) (hCR : ∀ z ∈ CR, M_0 ≤ z + 2 ∧ z ≤ N ∧ g (z + 2) = v ∧ g (z + 3) ≠ 0) :
    CR.sum (fun z => g (z + 3)) ≤ N + 2 - b_v := by {
  classical
  have hinj : Set.InjOn (fun z => z + 2) ↑CR := fun _ _ _ _ h => Nat.add_right_cancel h
  have hbound := isVanEckFrom_value_return_sum_bound g M_0 (N + 2) v b_v h_rec hb_min
    (CR.image (fun z => z + 2)) (fun m hm => by {
      rcases Finset.mem_image.mp hm with ⟨z, hz, rfl⟩
      rcases hCR z hz with ⟨hM, hzN, hgv, hnz⟩
      exact ⟨hM, by { omega }, hgv, hnz⟩
    })
  rw [Finset.sum_image hinj] at hbound
  exact hbound
}

/--
Case-2 `3`-Return Sum Bound: across any `Finset` `C2` of Case-2 indices `z ≤ N` (`M_0 ≤ z + 3`)
with `g (z + 3) = 3` and `5 ≤ g (z + 4)`, `5 * C2.card ≤ ∑ z ∈ C2, g (z + 4) ≤ N + 3`.
-/
lemma isVanEckFrom_case2_three_return_sum_bound (g : ℕ → ℕ) (M_0 N : ℕ)
    (h_rec : IsVanEckFrom g M_0)
    (C2 : Finset ℕ) (hC2 : ∀ z ∈ C2, M_0 ≤ z + 3 ∧ z ≤ N ∧ g (z + 3) = 3 ∧ 5 ≤ g (z + 4)) :
    5 * C2.card ≤ C2.sum (fun z => g (z + 4)) ∧ C2.sum (fun z => g (z + 4)) ≤ N + 3 := by {
  classical
  have hinj : Set.InjOn (fun z => z + 3) ↑C2 := fun _ _ _ _ h => Nat.add_right_cancel h
  have hbound := isVanEckFrom_value_return_sum_bound g M_0 (N + 3) 3 0 h_rec
    (fun _ hi => nomatch hi) (C2.image (fun z => z + 3)) (fun m hm => by {
      rcases Finset.mem_image.mp hm with ⟨z, hz, rfl⟩
      rcases hC2 z hz with ⟨hM, hzN, hg3, hge5⟩
      refine ⟨hM, by { omega }, hg3, ?_⟩
      change g (z + 4) ≠ 0
      omega
    })
  rw [Finset.sum_image hinj] at hbound
  have hlow : C2.card * 5 ≤ C2.sum (fun z => g (z + 4)) := by {
    have hc := Finset.card_nsmul_le_sum C2 (fun z => g (z + 4)) 5 (fun z hz => (hC2 z hz).2.2.2)
    simpa only [smul_eq_mul] using hc
  }
  exact ⟨by { omega }, by { omega }⟩
}

/--
Universal Pre/Post Anchor Disjointness across ALL Terminal Record Jumps:
for any two terminal record-jump zeros `z_1, z_2` (`p(z_i) + 3 ≤ q(z_i)`), `q(z_1) ≠ p(z_2)`
without exception (`z_2 = z_1 + 3` is ruled out even in Case-3 Fresh because `z_1 + 3` is not a
record jump).
-/
theorem isVanEckFrom_terminal_jump_anchors_disjoint (g : ℕ → ℕ) (M_0 zp1 z1 zp2 z2 : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hp1 : 1 ≤ zp1) (hM1 : M_0 ≤ zp1) (hlt1 : zp1 < z1)
    (hzp1 : g zp1 = 0) (hz1 : g z1 = 0) (hgap1 : ∀ k, zp1 < k → k < z1 → g k ≠ 0)
    (hjmp1 : prefixMaxFn g zp1 < prefixMaxFn g z1)
    (hterm1 : (z1 - 2 - g (z1 - 1)) + 3 ≤ z1 + 1 - g (z1 + 2))
    (hp2 : 1 ≤ zp2) (hM2 : M_0 ≤ zp2) (hlt2 : zp2 < z2)
    (hzp2 : g zp2 = 0) (hz2 : g z2 = 0) (hgap2 : ∀ k, zp2 < k → k < z2 → g k ≠ 0)
    (hjmp2 : prefixMaxFn g zp2 < prefixMaxFn g z2) :
    z1 + 1 - g (z1 + 2) ≠ z2 - 2 - g (z2 - 1) := by {
  have hid1 := isVanEckFrom_record_jump_anchor_identity g M_0 zp1 z1
    hg0 h_rec h_no2 hp1 hM1 hlt1 hzp1 hz1 hgap1 hjmp1
  have hid2 := isVanEckFrom_record_jump_anchor_identity g M_0 zp2 z2
    hg0 h_rec h_no2 hp2 hM2 hlt2 hzp2 hz2 hgap2 hjmp2
  have hg3_2 := (isVanEckFrom_zero_gap_eq_and_ge_three g M_0 zp2 z2
    hg0 h_rec h_no2 hp2 hM2 hlt2 hzp2 hz2 hgap2).2
  have hdisj := (isVanEckFrom_post_zero_anchor_unique_and_disjoint g M_0 zp1 z1
    hg0 h_rec h_no2 hp1 hM1 hlt1 hzp1 hz1 hgap1).2
  by_cases hz2_eq : z2 = z1 + 3
  · exfalso
    subst hz2_eq
    by_cases hc2 : z1 + 1 - g (z1 + 2) = (z1 - 2 - g (z1 - 1)) + 3
    · have hz1_3 := (isVanEckFrom_record_jump_case_eq_add_three g M_0 zp1 z1
        hg0 h_rec h_no2 hp1 hM1 hlt1 hzp1 hz1 hgap1 hjmp1 hc2).2.1
      omega
    · have hc3 : (z1 - 2 - g (z1 - 1)) + 4 ≤ z1 + 1 - g (z1 + 2) := by { omega }
      rcases (isVanEckFrom_record_jump_case_ge_add_four g M_0 zp1 z1
        hg0 h_rec h_no2 hp1 hM1 hlt1 hzp1 hz1 hgap1 hjmp1 hc3).2.2 with
        ⟨_, hpm_eq, _, _⟩ | ⟨hnz3, _⟩
      · have hzp2_eq : zp2 = z1 := by {
          by_contra hne
          exact hgap2 z1 (by { omega }) (by { omega }) hz1
        }
        rw [hzp2_eq, hpm_eq, hid1.1] at hjmp2
        exact Nat.lt_irrefl _ hjmp2
      · exact hnz3 hz2
  · exact hdisj z2 (by { omega }) hz2_eq (by { omega })
}

/--
Predicate packaging a consecutive-zero terminal record jump `z` (`p(z) + 3 ≤ q(z)`).
-/
def IsTerminalRecordJump (g : ℕ → ℕ) (M_0 z : ℕ) : Prop :=
  ∃ z_prev, 1 ≤ z_prev ∧ M_0 ≤ z_prev ∧ z_prev < z ∧
    g z_prev = 0 ∧ g z = 0 ∧ (∀ k, z_prev < k → k < z → g k ≠ 0) ∧
    prefixMaxFn g z_prev < prefixMaxFn g z ∧
    (z - 2 - g (z - 1)) + 3 ≤ z + 1 - g (z + 2)

lemma isTerminalRecordJump_anchors_injOn (g : ℕ → ℕ) (M_0 : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (TJ : Finset ℕ) (hTJ : ∀ z ∈ TJ, IsTerminalRecordJump g M_0 z) :
    Set.InjOn (fun z => z - 2 - g (z - 1)) ↑TJ ∧
      Set.InjOn (fun z => z + 1 - g (z + 2)) ↑TJ := by {
  have p_lt : ∀ a ∈ TJ, ∀ b ∈ TJ, a < b → a - 2 - g (a - 1) ≠ b - 2 - g (b - 1) := by {
    intro a ha b hb hlt heq
    rcases hTJ a ha with ⟨zpa, hpa, hMa, hlta, hzpa, hza, hgapa, hjmpa, _⟩
    rcases hTJ b hb with ⟨zpb, hpb, hMb, hltb, hzpb, hzb, hgapb, hjmpb, _⟩
    have hida := isVanEckFrom_record_jump_anchor_identity g M_0 zpa a
      hg0 h_rec h_no2 hpa hMa hlta hzpa hza hgapa hjmpa
    have hidb := isVanEckFrom_record_jump_anchor_identity g M_0 zpb b
      hg0 h_rec h_no2 hpb hMb hltb hzpb hzb hgapb hjmpb
    have hga := (isVanEckFrom_zero_gap_eq_and_ge_three g M_0 zpa a
      hg0 h_rec h_no2 hpa hMa hlta hzpa hza hgapa).2
    have hgb := (isVanEckFrom_zero_gap_eq_and_ge_three g M_0 zpb b
      hg0 h_rec h_no2 hpb hMb hltb hzpb hzb hgapb).2
    have hu := isVanEckFrom_lookback_anchor_unique g M_0 (a - 1) (b - 1) h_rec
      (by { omega }) (by { omega }) (by { omega }) (by { omega })
    have hsa : a - 1 - 1 = a - 2 := by { omega }
    have hsb : b - 1 - 1 = b - 2 := by { omega }
    rw [hsa, hsb] at hu
    exact hu heq
  }
  refine ⟨?_, ?_⟩
  · intro a ha b hb heq
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · exact False.elim (p_lt a ha b hb hlt heq)
    · rfl
    · exact False.elim (p_lt b hb a ha hgt heq.symm)
  · intro a ha b hb heq
    rcases hTJ a ha with ⟨zpa, hpa, hMa, hlta, hzpa, hza, hgapa, _, _⟩
    rcases hTJ b hb with ⟨zpb, hpb, hMb, hltb, hzpb, hzb, hgapb, _, _⟩
    rcases lt_trichotomy a b with hlt | rfl | hgt
    · exact False.elim ((isVanEckFrom_post_zero_anchor_unique_and_disjoint g M_0 zpa a
        hg0 h_rec h_no2 hpa hMa hlta hzpa hza hgapa).1 zpb b hlt hltb hpb hMb hzpb hzb hgapb heq)
    · rfl
    · exact False.elim ((isVanEckFrom_post_zero_anchor_unique_and_disjoint g M_0 zpb b
        hg0 h_rec h_no2 hpb hMb hltb hzpb hzb hgapb).1 zpa a hgt hlta hpa hMa hzpa hza hgapa
        heq.symm)
}

lemma isTerminalRecordJump_anchors_disjoint_and_sub (g : ℕ → ℕ) (M_0 N : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (TJ : Finset ℕ) (hTJ : ∀ z ∈ TJ, z ≤ N ∧ IsTerminalRecordJump g M_0 z) :
    Disjoint (TJ.image (fun z => z - 2 - g (z - 1)))
        (TJ.image (fun z => z + 1 - g (z + 2))) ∧
      TJ.image (fun z => z - 2 - g (z - 1)) ∪
        TJ.image (fun z => z + 1 - g (z + 2)) ⊆ Finset.range (N - 1) := by {
  classical
  refine ⟨?_, ?_⟩
  · rw [Finset.disjoint_left]
    intro x hxp hxq
    rcases Finset.mem_image.mp hxp with ⟨z2, hz2_mem, rfl⟩
    rcases Finset.mem_image.mp hxq with ⟨z1, hz1_mem, heq⟩
    rcases (hTJ z1 hz1_mem).2 with ⟨zp1, hp1, hM1, hlt1, hzp1, hz1, hgap1, hjmp1, hterm1⟩
    rcases (hTJ z2 hz2_mem).2 with ⟨zp2, hp2, hM2, hlt2, hzp2, hz2, hgap2, hjmp2, _⟩
    exact isVanEckFrom_terminal_jump_anchors_disjoint g M_0 zp1 z1 zp2 z2
      hg0 h_rec h_no2 hp1 hM1 hlt1 hzp1 hz1 hgap1 hjmp1 hterm1
      hp2 hM2 hlt2 hzp2 hz2 hgap2 hjmp2 heq
  · intro x hx
    rw [Finset.mem_range]
    rcases Finset.mem_union.mp hx with hxp | hxq
    · rcases Finset.mem_image.mp hxp with ⟨z, hz_mem, rfl⟩
      rcases hTJ z hz_mem with ⟨hzN, zp, hp, hM, hlt, hzp, hz, hgap, hjmp, _⟩
      have hid := isVanEckFrom_record_jump_anchor_identity g M_0 zp z
        hg0 h_rec h_no2 hp hM hlt hzp hz hgap hjmp
      omega
    · rcases Finset.mem_image.mp hxq with ⟨z, hz_mem, rfl⟩
      rcases hTJ z hz_mem with ⟨hzN, zp, hp, hM, hlt, hzp, hz, hgap, _, _⟩
      have hret := isVanEckFrom_post_zero_return_spec g M_0 zp z
        hg0 h_rec h_no2 hp hM hlt hzp hz hgap
      have hg3 := (isVanEckFrom_zero_gap_eq_and_ge_three g M_0 zp z
        hg0 h_rec h_no2 hp hM hlt hzp hz hgap).2
      omega
}

/--
Finite-Window Anchor & Slack Budget for Terminal Record Jumps:
for any `Finset` `TJ` of terminal record jumps `z ≤ N` (`2 ≤ N`), `p '' TJ` and `q '' TJ` are
disjoint `TJ.card`-element subsets of `Finset.range (N - 1)`, so `2 * TJ.card ≤ N - 1` and
`∑ (g(z - 1) - g(z + 2)) + 3 * TJ.card + ∑ p(z) = ∑ q(z)`.
-/
theorem isVanEckFrom_terminal_jumps_window_budget (g : ℕ → ℕ) (M_0 N : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (_hN : 2 ≤ N) (TJ : Finset ℕ) (hTJ : ∀ z ∈ TJ, z ≤ N ∧ IsTerminalRecordJump g M_0 z) :
    Disjoint (TJ.image (fun z => z - 2 - g (z - 1))) (TJ.image (fun z => z + 1 - g (z + 2))) ∧
      2 * TJ.card ≤ N - 1 ∧
      TJ.sum (fun z => g (z - 1) - g (z + 2)) + 3 * TJ.card +
        TJ.sum (fun z => z - 2 - g (z - 1)) = TJ.sum (fun z => z + 1 - g (z + 2)) := by {
  classical
  have hinjs := isTerminalRecordJump_anchors_injOn g M_0 hg0 h_rec h_no2 TJ
    (fun z hz => (hTJ z hz).2)
  rcases isTerminalRecordJump_anchors_disjoint_and_sub g M_0 N hg0 h_rec h_no2 TJ hTJ with
    ⟨hdisj, hsub⟩
  have hcard_u := Finset.card_le_card hsub
  rw [Finset.card_union_of_disjoint hdisj, Finset.card_image_of_injOn hinjs.1,
    Finset.card_image_of_injOn hinjs.2, Finset.card_range] at hcard_u
  have hpt : ∀ z ∈ TJ,
      (g (z - 1) - g (z + 2)) + 3 + (z - 2 - g (z - 1)) = z + 1 - g (z + 2) := by {
    intro z hz_mem
    rcases (hTJ z hz_mem).2 with ⟨zp, hp, hM, hlt, hzp, hz, hgap, hjmp, hterm⟩
    have hsl := isVanEckFrom_terminal_jump_slack_eq g M_0 zp z
      hg0 h_rec h_no2 hp hM hlt hzp hz hgap hjmp hterm
    have hid := isVanEckFrom_record_jump_anchor_identity g M_0 zp z
      hg0 h_rec h_no2 hp hM hlt hzp hz hgap hjmp
    omega
  }
  have hsum := Finset.sum_congr rfl hpt
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_const, smul_eq_mul,
    Nat.mul_comm TJ.card 3] at hsum
  exact ⟨hdisj, by { omega }, hsum⟩
}

/--
Infinite Case-2 vs Infinite Case-3 Dichotomy:
every unbounded `2`-free `IsVanEckFrom g M_0` sequence (`g 0 = 0`, infinite zeros) either undergoes
infinitely many zero-slack Case-2 record jumps (`q = p + 3`) or infinitely many positive-slack
Case-3 record jumps (`p + 4 ≤ q`, `g(z - 1) - g(z + 2) ≥ 1`) arbitrarily far out and high up.
-/
theorem isVanEckFrom_infinite_case2_or_case3_jumps (g : ℕ → ℕ) (M_0 : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (h_zeros : ∀ K, ∃ z > K, g z = 0) (h_unb : ∀ B, ∃ j, B < g j) :
    (∀ K V, ∃ z_prev z, K < z_prev ∧ M_0 ≤ z_prev ∧ z_prev < z ∧ g z_prev = 0 ∧ g z = 0 ∧
      (∀ k, z_prev < k → k < z → g k ≠ 0) ∧ V < prefixMaxFn g z_prev ∧
      prefixMaxFn g z_prev < prefixMaxFn g z ∧
      z + 1 - g (z + 2) = (z - 2 - g (z - 1)) + 3) ∨
    (∀ K V, ∃ z_prev z, K < z_prev ∧ M_0 ≤ z_prev ∧ z_prev < z ∧ g z_prev = 0 ∧ g z = 0 ∧
      (∀ k, z_prev < k → k < z → g k ≠ 0) ∧ V < prefixMaxFn g z_prev ∧
      prefixMaxFn g z_prev < prefixMaxFn g z ∧
      (z - 2 - g (z - 1)) + 4 ≤ z + 1 - g (z + 2)) := by {
  by_cases h_inf2 : ∀ K V, ∃ z_prev z, K < z_prev ∧ M_0 ≤ z_prev ∧ z_prev < z ∧
      g z_prev = 0 ∧ g z = 0 ∧ (∀ k, z_prev < k → k < z → g k ≠ 0) ∧
      V < prefixMaxFn g z_prev ∧ prefixMaxFn g z_prev < prefixMaxFn g z ∧
      z + 1 - g (z + 2) = (z - 2 - g (z - 1)) + 3
  · exact Or.inl h_inf2
  · right
    push Not at h_inf2
    rcases h_inf2 with ⟨K_0, V_0, h_no_c2⟩
    intro K V
    rcases isVanEckFrom_infinite_terminal_record_jumps g M_0 hg0 h_rec h_no2 h_zeros h_unb
      (max K K_0) (max V V_0) with
      ⟨zp, z, hgtK, hM, hlt, hzp, hz, hgap, hgtV, hjmp, hterm⟩
    have hne_c2 := h_no_c2 zp z (lt_of_le_of_lt (Nat.le_max_right _ _) hgtK)
      hM hlt hzp hz hgap (lt_of_le_of_lt (Nat.le_max_right _ _) hgtV) hjmp
    exact ⟨zp, z, lt_of_le_of_lt (Nat.le_max_left _ _) hgtK, hM, hlt, hzp, hz, hgap,
      lt_of_le_of_lt (Nat.le_max_left _ _) hgtV, hjmp, by { omega }⟩
}

/--
Universal Distance-Two `(A, B, A) → 2` Collision for `IsVanEckFrom g M_0`:
if `2 ≤ g (m - 1)` (`1 ≤ m`, `M_0 ≤ m`) and the most recent occurrence of `g m` before `m` is at
`u` with `m - u = g (m - 1)`, then `g (m - 1) ≠ g m`, `g (m + 1) = g (m - 1)`, and `g (m + 2) = 2`.
-/
lemma isVanEckFrom_match_prev_emits_two (g : ℕ → ℕ) (M_0 m u : ℕ)
    (h_rec : IsVanEckFrom g M_0) (hm_pos : 1 ≤ m) (hm_M : M_0 ≤ m)
    (h_ge2 : 2 ≤ g (m - 1)) (h_occ : lastOccBeforeFn g m (g m) = some u)
    (h_dist : m - u = g (m - 1)) :
    g (m - 1) ≠ g m ∧ g (m + 1) = g (m - 1) ∧ g (m + 2) = 2 := by {
  have hu_sp := lastOccBeforeFn_eq_some_spec g m (g m) u h_occ
  have hu_lt := hu_sp.1
  have hne : g (m - 1) ≠ g m := hu_sp.2.2 (m - 1) (by { omega }) (by { omega })
  have hm1_eq : g (m + 1) = g (m - 1) := by {
    have hr := h_rec m hm_M
    rw [h_occ] at hr
    change g (m + 1) = m - u at hr
    exact hr.trans h_dist
  }
  have hocc_next : lastOccBeforeFn g (m + 1) (g (m + 1)) = some (m - 1) :=
    lastOccBeforeFn_eq_some_of_prev g (m + 1) (m - 1) (g (m + 1)) (by { omega }) hm1_eq.symm
      (fun k hk1 hk2 => by {
        have hk_eq : k = m := by { omega }
        rw [hk_eq, hm1_eq]
        exact Ne.symm hne
      })
  have hm2_eq : g (m + 2) = 2 := by {
    have hr := h_rec (m + 1) (by { omega })
    rw [hocc_next] at hr
    change g (m + 2) = m + 1 - (m - 1) at hr
    omega
  }
  exact ⟨hne, hm1_eq, hm2_eq⟩
}

lemma isVanEckFrom_raw_consecutive_zero_gap (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0) :
    g (z + 1) = z - z_prev ∧ 2 ≤ z - z_prev := by {
  have hzp1_nz : g (z_prev + 1) ≠ 0 := by {
    have hr := h_rec z_prev hzp_M
    rw [hzp] at hr
    cases h0 : lastOccBeforeFn g z_prev 0 with
    | none =>
      exact False.elim (((lastOccBeforeFn_eq_none_iff g z_prev 0).mp h0) 0 hzp_pos hg0)
    | some r0 =>
      rw [h0] at hr
      have hr0_lt := (lastOccBeforeFn_eq_some_spec g z_prev 0 r0 h0).1
      change g (z_prev + 1) = z_prev - r0 at hr
      omega
  }
  have h_ge2 : 2 ≤ z - z_prev := by {
    by_contra hlt2
    have hzeq : z = z_prev + 1 := by { omega }
    exact hzp1_nz (hzeq ▸ hz)
  }
  have hoccz : lastOccBeforeFn g z 0 = some z_prev :=
    lastOccBeforeFn_eq_some_of_prev g z z_prev 0 h_lt hzp h_gap
  have hrz := h_rec z (by { omega })
  rw [hz, hoccz] at hrz
  exact ⟨hrz, h_ge2⟩
}

/--
The `(G, R, G) → 2` Post-Zero Collision Theorem:
for consecutive zeros `1 ≤ z_prev < z` (`M_0 ≤ z_prev`), if the most recent occurrence of
`R = g (z + 2)` before `z + 2` is at `z_prev + 2`, then `R ≠ G = z - z_prev` automatically,
`g (z + 3) = G`, and `g (z + 4) = 2`.
-/
theorem isVanEckFrom_post_zero_prev2_emits_two (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_occ : lastOccBeforeFn g (z + 2) (g (z + 2)) = some (z_prev + 2)) :
    g (z + 1) = z - z_prev ∧
      g (z + 2) ≠ z - z_prev ∧
      g (z + 3) = z - z_prev ∧
      g (z + 4) = 2 := by {
  have hg_raw := isVanEckFrom_raw_consecutive_zero_gap g M_0 z_prev z
    hg0 h_rec hzp_pos hzp_M h_lt hzp hz h_gap
  have hge2_m1 : 2 ≤ g (z + 2 - 1) := by {
    change 2 ≤ g (z + 1)
    omega
  }
  have hdist_m1 : z + 2 - (z_prev + 2) = g (z + 2 - 1) := by {
    change z + 2 - (z_prev + 2) = g (z + 1)
    omega
  }
  have hm := isVanEckFrom_match_prev_emits_two g M_0 (z + 2) (z_prev + 2) h_rec
    (by { omega }) (by { omega }) hge2_m1 h_occ hdist_m1
  exact ⟨hg_raw.1, fun heq => hm.1 (hg_raw.1.trans heq.symm), hm.2.1.trans hg_raw.1, hm.2.2⟩
}

/--
Universal Post-Zero Step-3 Exclusion in a `2`-Free Tail:
at every consecutive zero pair `1 ≤ z_prev < z` (`M_0 ≤ z_prev`), `g (z + 3) ≠ z - z_prev`,
`lastOccBeforeFn g (z + 2) (g (z + 2)) ≠ some (z_prev + 2)`, and `g (z_prev + 2) = g (z + 2)`
requires an intermediate occurrence in `(z_prev + 2, z + 2)`.
-/
theorem isVanEckFrom_post_zero_step3_ne_gap (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0) :
    lastOccBeforeFn g (z + 2) (g (z + 2)) ≠ some (z_prev + 2) ∧
      g (z + 3) ≠ z - z_prev ∧
      (g (z_prev + 2) = g (z + 2) → ∃ k, z_prev + 2 < k ∧ k < z + 2 ∧ g k = g (z + 2)) := by {
  have hgap_sp := isVanEckFrom_zero_gap_eq_and_ge_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hne_occ : lastOccBeforeFn g (z + 2) (g (z + 2)) ≠ some (z_prev + 2) := fun h_occ => by {
    have h2 := (isVanEckFrom_post_zero_prev2_emits_two g M_0 z_prev z
      hg0 h_rec hzp_pos hzp_M h_lt hzp hz h_gap h_occ).2.2.2
    exact h_no2 (z + 4) (by { omega }) h2
  }
  have hne_step3 : g (z + 3) ≠ z - z_prev := fun heq => by {
    have hr := h_rec (z + 2) (by { omega })
    cases h_occ : lastOccBeforeFn g (z + 2) (g (z + 2)) with
    | none =>
      rw [h_occ] at hr
      change g (z + 3) = 0 at hr
      omega
    | some r =>
      rw [h_occ] at hr
      change g (z + 3) = z + 2 - r at hr
      have hr_lt := (lastOccBeforeFn_eq_some_spec g (z + 2) (g (z + 2)) r h_occ).1
      have hr_eq : r = z_prev + 2 := by { omega }
      exact hne_occ (hr_eq ▸ h_occ)
  }
  refine ⟨hne_occ, hne_step3, fun hsame => ?_⟩
  by_contra hno_mid
  push Not at hno_mid
  exact hne_occ (lastOccBeforeFn_eq_some_of_prev g (z + 2) (z_prev + 2) (g (z + 2))
    (by { omega }) hsame hno_mid)
}

lemma isVanEckFrom_local_post_zero_return (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0)
    (h_no2_loc : ∀ k, z < k → k ≤ z + 4 → g k ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0) :
    g (z + 1) = z - z_prev ∧
      3 ≤ z - z_prev ∧
      3 ≤ g (z + 2) ∧
      g (z + 2) ≤ z + 1 ∧
      z + 1 - g (z + 2) ≤ z - 2 ∧
      g (z + 1 - g (z + 2)) = z - z_prev := by {
  have hraw := isVanEckFrom_raw_consecutive_zero_gap g M_0 z_prev z
    hg0 h_rec hzp_pos hzp_M h_lt hzp hz h_gap
  have hz1_ne2 : g (z + 1) ≠ 2 := h_no2_loc (z + 1) (by { omega }) (by { omega })
  have hr1 := h_rec (z + 1) (by { omega })
  cases h_occ : lastOccBeforeFn g (z + 1) (g (z + 1)) with
  | none =>
    rw [h_occ] at hr1
    change g (z + 2) = 0 at hr1
    have hocc2 := lastOccBeforeFn_eq_some_of_prev g (z + 2) z 0 (by { omega }) hz
      (fun k hk1 hk2 => by {
        have hkeq : k = z + 1 := by { omega }
        rw [hkeq]
        omega
      })
    have hr2 := h_rec (z + 2) (by { omega })
    rw [hr1, hocc2] at hr2
    change g (z + 3) = z + 2 - z at hr2
    exact False.elim (h_no2_loc (z + 3) (by { omega }) (by { omega }) (by { omega }))
  | some q =>
    rw [h_occ] at hr1
    change g (z + 2) = z + 1 - q at hr1
    have hq_sp := lastOccBeforeFn_eq_some_spec g (z + 1) (g (z + 1)) q h_occ
    have hq_lt := hq_sp.1
    have hq_ne_z : q ≠ z := fun heq => (by { omega } : g q ≠ 0) (heq ▸ hz)
    have hq_ne_z1 : q ≠ z - 1 := fun heq =>
      h_no2_loc (z + 2) (by { omega }) (by { omega }) (by { omega })
    have hq_eq : z + 1 - g (z + 2) = q := by { omega }
    rw [hq_eq]
    exact ⟨hraw.1, by { omega }, by { omega }, by { omega }, by { omega },
      hq_sp.2.1.trans hraw.1⟩
}

lemma isVanEckFrom_local_step3_ne_gap (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0)
    (h_no2_loc : ∀ k, z < k → k ≤ z + 4 → g k ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0) :
    g (z + 3) ≠ z - z_prev := by {
  have hret := isVanEckFrom_local_post_zero_return g M_0 z_prev z
    hg0 h_rec h_no2_loc hzp_pos hzp_M h_lt hzp hz h_gap
  have hne_occ : lastOccBeforeFn g (z + 2) (g (z + 2)) ≠ some (z_prev + 2) := fun ho =>
    h_no2_loc (z + 4) (by { omega }) le_rfl
      (isVanEckFrom_post_zero_prev2_emits_two g M_0 z_prev z
        hg0 h_rec hzp_pos hzp_M h_lt hzp hz h_gap ho).2.2.2
  intro heq
  have hr := h_rec (z + 2) (by { omega })
  cases ho : lastOccBeforeFn g (z + 2) (g (z + 2)) with
  | none =>
    rw [ho] at hr
    change g (z + 3) = 0 at hr
    omega
  | some r =>
    rw [ho] at hr
    change g (z + 3) = z + 2 - r at hr
    have hr_lt := (lastOccBeforeFn_eq_some_spec g (z + 2) (g (z + 2)) r ho).1
    have hreq : r = z_prev + 2 := by { omega }
    exact hne_occ (hreq ▸ ho)
}

lemma isVanEckFrom_raw_block_le_prefixMax (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (h_rec : IsVanEckFrom g M_0) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0) :
    (∀ k < z - 1, g k ≤ prefixMaxFn g z_prev) ∧
      prefixMaxFn g z = max (prefixMaxFn g z_prev) (g (z - 1)) := by {
  have hpm := le_prefixMaxFn_and_mono g
  have h_all : ∀ k < z - 1, g k ≤ prefixMaxFn g z_prev := by {
    intro k
    refine Nat.strong_induction_on k (fun k ih hk_lt => ?_)
    by_cases hle : k ≤ z_prev
    · exact le_trans (hpm.1 k) (hpm.2 k z_prev hle)
    · have hr := h_rec k (by { omega })
      have hnz : g (k + 1) ≠ 0 := h_gap (k + 1) (by { omega }) (by { omega })
      cases h_occ : lastOccBeforeFn g k (g k) with
      | none =>
        rw [h_occ] at hr
        exact False.elim (hnz hr)
      | some r =>
        have hr_sp := lastOccBeforeFn_eq_some_spec g k (g k) r h_occ
        rw [← hr_sp.2.1]
        exact ih r hr_sp.1 (by { omega })
  }
  refine ⟨h_all, le_antisymm ?_ ?_⟩
  · rw [prefixMaxFn_le_iff]
    intro k hk
    rcases lt_or_eq_of_le hk with hlt_z | rfl
    · rcases lt_or_eq_of_le (by { omega } : k ≤ z - 1) with hlt_z1 | rfl
      · exact le_trans (h_all k hlt_z1) (Nat.le_max_left _ _)
      · exact Nat.le_max_right _ _
    · rw [hz]
      exact Nat.zero_le _
  · exact max_le (hpm.2 z_prev z (Nat.le_of_lt h_lt))
      (le_trans (hpm.1 (z - 1)) (hpm.2 (z - 1) z (by { omega })))
}

lemma isVanEckFrom_local_block_and_anchor (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0)
    (h_no2_loc : ∀ k, z < k → k ≤ z + 4 → g k ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z) :
    prefixMaxFn g z = g (z - 1) ∧
      4 ≤ g (z - 1) ∧
      g (z + 1) ≤ prefixMaxFn g z_prev ∧
      g (z + 2) + (z + 1 - g (z + 2)) = g (z - 1) + (z - 2 - g (z - 1)) + 3 := by {
  have hloc := isVanEckFrom_local_post_zero_return g M_0 z_prev z
    hg0 h_rec h_no2_loc hzp_pos hzp_M h_lt hzp hz h_gap
  have hraw_blk := isVanEckFrom_raw_block_le_prefixMax g M_0 z_prev z
    h_rec hzp_M h_lt hz h_gap
  have hz1_le : g (z + 1) ≤ prefixMaxFn g z_prev := by {
    rw [hloc.1, ← hloc.2.2.2.2.2]
    exact hraw_blk.1 (z + 1 - g (z + 2)) (by { omega })
  }
  have hr_z2 := h_rec (z - 2) (by { omega })
  have hidx_z1 : z - 2 + 1 = z - 1 := by { omega }
  rw [hidx_z1] at hr_z2
  cases h_occ : lastOccBeforeFn g (z - 2) (g (z - 2)) with
  | none =>
    rw [h_occ] at hr_z2
    change g (z - 1) = 0 at hr_z2
    omega
  | some p =>
    rw [h_occ] at hr_z2
    change g (z - 1) = z - 2 - p at hr_z2
    have hp_lt := (lastOccBeforeFn_eq_some_spec g (z - 2) (g (z - 2)) p h_occ).1
    exact ⟨by { omega }, by { omega }, hz1_le, by { omega }⟩
}

lemma isVanEckFrom_local_case2_eq_three (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0)
    (h_no2_loc : ∀ k, z < k → k ≤ z + 4 → g k ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z)
    (hc2 : z + 1 - g (z + 2) = (z - 2 - g (z - 1)) + 3) :
    g (z + 2) = g (z - 1) ∧ g (z + 3) = 3 ∧ 4 ≤ z - z_prev := by {
  have hloc := isVanEckFrom_local_post_zero_return g M_0 z_prev z
    hg0 h_rec h_no2_loc hzp_pos hzp_M h_lt hzp hz h_gap
  have hs3_ne := isVanEckFrom_local_step3_ne_gap g M_0 z_prev z
    hg0 h_rec h_no2_loc hzp_pos hzp_M h_lt hzp hz h_gap
  have hba := isVanEckFrom_local_block_and_anchor g M_0 z_prev z
    hg0 h_rec h_no2_loc hzp_pos hzp_M h_lt hzp hz h_gap h_jump
  have heq_rec : g (z + 2) = g (z - 1) := by { omega }
  have hocc2 := lastOccBeforeFn_eq_some_of_prev g (z + 2) (z - 1) (g (z + 2))
    (by { omega }) heq_rec.symm (fun k hk1 hk2 => by {
      by_cases hkz : k = z
      · rw [hkz, hz]
        omega
      · have hk1_eq : k = z + 1 := by { omega }
        rw [hk1_eq]
        omega
    })
  have hz3 : g (z + 3) = 3 := by {
    have hr := h_rec (z + 2) (by { omega })
    rw [hocc2] at hr
    change g (z + 3) = z + 2 - (z - 1) at hr
    omega
  }
  exact ⟨heq_rec, hz3, by { omega }⟩
}

lemma isVanEckFrom_local_case3_repeat_birth (g : ℕ → ℕ) (M_0 z_prev z r : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0)
    (h_no2_loc : ∀ k, z < k → k ≤ z + 4 → g k ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (hlt_rec : g (z + 2) < g (z - 1))
    (ho : lastOccBeforeFn g (z + 2) (g (z + 2)) = some r) :
    (∃ i ≤ M_0, g i = g (z + 2)) ∨
      ∃ z_R, M_0 + 1 < z_R ∧ z_R ≤ z_prev ∧
        g z_R = 0 ∧ g (z_R - 1) = g (z + 2) ∧ ∀ i < z_R - 1, g i ≠ g (z + 2) := by {
  have hloc := isVanEckFrom_local_post_zero_return g M_0 z_prev z
    hg0 h_rec h_no2_loc hzp_pos hzp_M h_lt hzp hz h_gap
  have hr_sp := lastOccBeforeFn_eq_some_spec g (z + 2) (g (z + 2)) r ho
  have hr_lt := hr_sp.1
  rcases isVanEckFrom_first_occ_birth g M_0 r h_rec with ⟨b, hb_le, hb_eq, hb_min, hb_z⟩
  have hb_lt_zp : b < z_prev := by {
    by_contra hb_ge
    by_cases hbz1 : b = z + 1
    · exact hb_min (z + 1 - g (z + 2)) (by { omega })
        (hloc.2.2.2.2.2.trans (hloc.1.symm.trans (hbz1 ▸ hb_eq)))
    · by_cases hbz : b = z
      · have hr_val := hr_sp.2.1
        exact (by { omega } : g b ≠ 0) (hbz ▸ hz)
      · by_cases hbzm1 : b = z - 1
        · have heqr : g b = g (z + 2) := hb_eq.trans hr_sp.2.1
          rw [hbzm1] at heqr
          omega
        · by_cases hbzp : b = z_prev
          · have hr_val := hr_sp.2.1
            exact (by { omega } : g b ≠ 0) (hbzp ▸ hzp)
          · exact (h_gap (b + 1) (by { omega }) (by { omega })) (hb_z (by { omega }))
  }
  rw [hr_sp.2.1] at hb_eq hb_min
  by_cases hb_M : b ≤ M_0
  · exact Or.inl ⟨b, hb_M, hb_eq⟩
  · exact Or.inr ⟨b + 1, by { omega }, by { omega }, hb_z (by { omega }), hb_eq, hb_min⟩
}

/--
Uniform Local Collision-or-Descent Dichotomy at ANY Terminal Record Jump (with NO `2`-free
assumption): either `g` emits a `2` within `4` steps (`z < k ≤ z + 4`, including `(G, R, G) → 2`),
or `g (z + 3) ≠ z - z_prev` and `z` enters Case 2 (`g (z + 3) = 3`, `4 ≤ z - z_prev`), Case 3
Fresh (`g (z + 3) = 0`), or Case 3 Repeat with strict birth-class descent (`z_R ≤ z_prev < z`).
-/
theorem isVanEckFrom_record_jump_local_collision_or_descent (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (h_jump : prefixMaxFn g z_prev < prefixMaxFn g z)
    (h_term : (z - 2 - g (z - 1)) + 3 ≤ z + 1 - g (z + 2)) :
    (∃ k, z < k ∧ k ≤ z + 4 ∧ g k = 2) ∨
      (g (z + 3) ≠ z - z_prev ∧
        ((z + 1 - g (z + 2) = (z - 2 - g (z - 1)) + 3 ∧
            g (z + 2) = g (z - 1) ∧ g (z + 3) = 3 ∧ 4 ≤ z - z_prev) ∨
          ((z - 2 - g (z - 1)) + 4 ≤ z + 1 - g (z + 2) ∧
            g (z + 3) = 0 ∧ prefixMaxFn g (z + 3) = g (z - 1)) ∨
          ((z - 2 - g (z - 1)) + 4 ≤ z + 1 - g (z + 2) ∧
            g (z + 3) ≠ 0 ∧ 3 ≤ g (z + 2) ∧ g (z + 2) < g (z - 1) ∧
            ((∃ i ≤ M_0, g i = g (z + 2)) ∨
              ∃ z_R, M_0 + 1 < z_R ∧ z_R ≤ z_prev ∧
                g z_R = 0 ∧ g (z_R - 1) = g (z + 2) ∧ ∀ i < z_R - 1, g i ≠ g (z + 2))))) := by {
  by_cases h_hit2 : ∃ k, z < k ∧ k ≤ z + 4 ∧ g k = 2
  · exact Or.inl h_hit2
  · right
    have h_no2_loc : ∀ k, z < k → k ≤ z + 4 → g k ≠ 2 := fun k hk1 hk2 heq =>
      h_hit2 ⟨k, hk1, hk2, heq⟩
    have hloc := isVanEckFrom_local_post_zero_return g M_0 z_prev z
      hg0 h_rec h_no2_loc hzp_pos hzp_M h_lt hzp hz h_gap
    have hs3_ne := isVanEckFrom_local_step3_ne_gap g M_0 z_prev z
      hg0 h_rec h_no2_loc hzp_pos hzp_M h_lt hzp hz h_gap
    have hba := isVanEckFrom_local_block_and_anchor g M_0 z_prev z
      hg0 h_rec h_no2_loc hzp_pos hzp_M h_lt hzp hz h_gap h_jump
    refine ⟨hs3_ne, ?_⟩
    by_cases hc2 : z + 1 - g (z + 2) = (z - 2 - g (z - 1)) + 3
    · rcases isVanEckFrom_local_case2_eq_three g M_0 z_prev z
        hg0 h_rec h_no2_loc hzp_pos hzp_M h_lt hzp hz h_gap h_jump hc2 with ⟨heq, hz3, hg4⟩
      exact Or.inl ⟨hc2, heq, hz3, hg4⟩
    · have hc3 : (z - 2 - g (z - 1)) + 4 ≤ z + 1 - g (z + 2) := by { omega }
      have hlt_rec : g (z + 2) < g (z - 1) := by { omega }
      have hr2 := h_rec (z + 2) (by { omega })
      cases ho : lastOccBeforeFn g (z + 2) (g (z + 2)) with
      | none =>
        rw [ho] at hr2
        change g (z + 3) = 0 at hr2
        have hpm_z3 : prefixMaxFn g (z + 3) = g (z - 1) := by {
          change max (max (max (prefixMaxFn g z) (g (z + 1))) (g (z + 2))) (g (z + 3)) = g (z - 1)
          omega
        }
        exact Or.inr (Or.inl ⟨hc3, hr2, hpm_z3⟩)
      | some r =>
        rw [ho] at hr2
        have hr_lt := (lastOccBeforeFn_eq_some_spec g (z + 2) (g (z + 2)) r ho).1
        change g (z + 3) = z + 2 - r at hr2
        have hbd := isVanEckFrom_local_case3_repeat_birth g M_0 z_prev z r
          hg0 h_rec h_no2_loc hzp_pos hzp_M h_lt hzp hz h_gap hlt_rec ho
        exact Or.inr (Or.inr ⟨hc3, by { omega }, hloc.2.2.1, hlt_rec, hbd⟩)
}

lemma isVanEckFrom_self_return_step3_eq_three (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0)
    (heq_z1 : g (z + 2) = g (z - 1)) :
    g (z + 3) = 3 := by {
  have hret := isVanEckFrom_post_zero_return_spec g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hgap_sp := isVanEckFrom_zero_gap_eq_and_ge_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hz1_ne : g (z + 1) ≠ g (z - 1) := fun h1 => by {
    have hr_zm1 := h_rec (z - 1) (by { omega })
    have hidx : z - 1 + 1 = z := by { omega }
    rw [hidx, hz] at hr_zm1
    cases ho1 : lastOccBeforeFn g (z - 1) (g (z - 1)) with
    | none =>
      exact ((lastOccBeforeFn_eq_none_iff g (z - 1) (g (z - 1))).mp ho1)
        (z + 1 - g (z + 2)) (by { omega }) (hret.2.2.2.1.trans (hgap_sp.1.symm.trans h1))
    | some u =>
      rw [ho1] at hr_zm1
      have hu_lt := (lastOccBeforeFn_eq_some_spec g (z - 1) (g (z - 1)) u ho1).1
      change 0 = z - 1 - u at hr_zm1
      omega
  }
  have hocc_z1 := lastOccBeforeFn_eq_some_of_prev g (z + 2) (z - 1) (g (z + 2))
    (by { omega }) heq_z1.symm (fun k hk1 hk2 => by {
      by_cases hkz : k = z
      · rw [hkz, hz]
        omega
      · have hk_eq1 : k = z + 1 := by { omega }
        rw [hk_eq1, heq_z1]
        exact hz1_ne
    })
  have hr2 := h_rec (z + 2) (by { omega })
  rw [hocc_z1] at hr2
  change g (z + 3) = z + 2 - (z - 1) at hr2
  omega
}

/--
Single-Step Post-Zero Return Dichotomy for ANY Consecutive Zeros `1 ≤ z_prev < z` (`M_0 ≤ z_prev`):
`R = g (z + 2)` either is fresh (`g (z + 3) = 0`, `g (z + 4) = 3`), equals `g (z - 1)`
(`g (z + 3) = 3`), appears in `[0, M_0]`, or descends to a strictly earlier birth zero
`M_0 + 1 < z_R ≤ z_prev < z` with `g (z_R - 1) = g (z + 2)`.
-/
lemma isVanEckFrom_any_zero_return_step_dichotomy (g : ℕ → ℕ) (M_0 z_prev z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hzp_pos : 1 ≤ z_prev) (hzp_M : M_0 ≤ z_prev) (h_lt : z_prev < z)
    (hzp : g z_prev = 0) (hz : g z = 0) (h_gap : ∀ k, z_prev < k → k < z → g k ≠ 0) :
    (g (z + 3) = 0 ∧ g (z + 4) = 3) ∨
      (g (z + 2) = g (z - 1) ∧ g (z + 3) = 3) ∨
      (∃ i ≤ M_0, g i = g (z + 2)) ∨
      ∃ z_R, M_0 + 1 < z_R ∧ z_R ≤ z_prev ∧
        g z_R = 0 ∧ g (z_R - 1) = g (z + 2) ∧ ∀ i < z_R - 1, g i ≠ g (z + 2) := by {
  have hret := isVanEckFrom_post_zero_return_spec g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  have hgap_sp := isVanEckFrom_zero_gap_eq_and_ge_three g M_0 z_prev z
    hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
  cases ho : lastOccBeforeFn g (z + 2) (g (z + 2)) with
  | none =>
    rcases isVanEckFrom_zero_at_add_three_of_none g M_0 z_prev z
      hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap ho with ⟨hz3, _, _, hz4⟩
    exact Or.inl ⟨hz3, hz4⟩
  | some r =>
    have hr_sp := lastOccBeforeFn_eq_some_spec g (z + 2) (g (z + 2)) r ho
    have hr_lt := hr_sp.1
    by_cases heq_z1 : g (z + 2) = g (z - 1)
    · exact Or.inr (Or.inl ⟨heq_z1, isVanEckFrom_self_return_step3_eq_three g M_0 z_prev z
        hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap heq_z1⟩)
    · have hd := isVanEckFrom_earlier_birth_dichotomy g M_0 z_prev z r
        hg0 h_rec h_no2 hzp_pos hzp_M h_lt hzp hz h_gap
        (by { omega }) (by { omega }) (hr_sp.2.1.trans_ne heq_z1)
      rw [hr_sp.2.1] at hd
      rcases hd with hpre | ⟨z_R, hzR_gt, hzR_le, _, hzR0, hzR_eq, hzR_min⟩
      · exact Or.inr (Or.inr (Or.inl hpre))
      · exact Or.inr (Or.inr (Or.inr ⟨z_R, hzR_gt, hzR_le, hzR0, hzR_eq, hzR_min⟩))
}

/--
Strictly decreasing chain of zeros linked by post-zero return birth `g (z_R - 1) = g (z + 2)`.
-/
inductive IsPostZeroReturnChain (g : ℕ → ℕ) : ℕ → ℕ → Prop
  | refl (z : ℕ) (hz : g z = 0) : IsPostZeroReturnChain g z z
  | step (z_base z_R z : ℕ) (h_prev : IsPostZeroReturnChain g z_base z_R)
      (hz : g z = 0) (hz_lt : z_R < z) (h_birth : g (z_R - 1) = g (z + 2)) :
      IsPostZeroReturnChain g z_base z

/--
Post-Zero Return Chain Termination Theorem:
in any `2`-free `IsVanEckFrom g M_0` tail (`g 0 = 0`), every zero `z ≥ max M_0 1` descends via
`IsPostZeroReturnChain` to a root zero `z_base` (`max M_0 1 ≤ z_base ≤ z`) that either reaches the
cut prefix (`lastOccBeforeFn g z_base 0` below `max M_0 1`, or `g (z_base + 2)` in `[0, M_0]`)
or emits `3` (`g (z_base + 3) = 3`, or `g (z_base + 3) = 0 ∧ g (z_base + 4) = 3`).
-/
theorem isVanEckFrom_post_zero_return_chain_terminates (g : ℕ → ℕ) (M_0 z : ℕ)
    (hg0 : g 0 = 0) (h_rec : IsVanEckFrom g M_0) (h_no2 : ∀ j > M_0, g j ≠ 2)
    (hz_ge : max M_0 1 ≤ z) (hz : g z = 0) :
    ∃ z_base, max M_0 1 ≤ z_base ∧ z_base ≤ z ∧ g z_base = 0 ∧
      IsPostZeroReturnChain g z_base z ∧
      ((∀ zp, lastOccBeforeFn g z_base 0 = some zp → zp < max M_0 1) ∨
        (∃ i ≤ M_0, g i = g (z_base + 2)) ∨
        (g (z_base + 2) = g (z_base - 1) ∧ g (z_base + 3) = 3) ∨
        (g (z_base + 3) = 0 ∧ g (z_base + 4) = 3)) := by {
  revert hz_ge hz
  refine Nat.strong_induction_on z (fun z ih hz_ge hz => ?_)
  cases ho0 : lastOccBeforeFn g z 0 with
  | none =>
    exact False.elim (((lastOccBeforeFn_eq_none_iff g z 0).mp ho0) 0 (by { omega }) hg0)
  | some z_prev =>
    have hzp_sp := lastOccBeforeFn_eq_some_spec g z 0 z_prev ho0
    by_cases hzp_cut : z_prev < max M_0 1
    · refine ⟨z, hz_ge, le_rfl, hz, IsPostZeroReturnChain.refl z hz, Or.inl ?_⟩
      intro zp hzp_eq
      rw [ho0] at hzp_eq
      injection hzp_eq with h_eq
      omega
    · have hstep := isVanEckFrom_any_zero_return_step_dichotomy g M_0 z_prev z
        hg0 h_rec h_no2 (by { omega }) (by { omega }) hzp_sp.1 hzp_sp.2.1 hz hzp_sp.2.2
      rcases hstep with hfresh | hself | hpre | ⟨z_R, hzR_gt, hzR_le, hzR0, hzR_eq, _⟩
      · exact ⟨z, hz_ge, le_rfl, hz, IsPostZeroReturnChain.refl z hz,
          Or.inr (Or.inr (Or.inr hfresh))⟩
      · exact ⟨z, hz_ge, le_rfl, hz, IsPostZeroReturnChain.refl z hz,
          Or.inr (Or.inr (Or.inl hself))⟩
      · exact ⟨z, hz_ge, le_rfl, hz, IsPostZeroReturnChain.refl z hz,
          Or.inr (Or.inl hpre)⟩
      · have hzR_lt : z_R < z := lt_of_le_of_lt hzR_le hzp_sp.1
        rcases ih z_R hzR_lt (by { omega }) hzR0 with
          ⟨z_base, hb_ge, hb_le, hb0, hchain, hout⟩
        exact ⟨z_base, hb_ge, le_trans hb_le (Nat.le_of_lt hzR_lt), hb0,
          IsPostZeroReturnChain.step z_base z_R z hchain hz hzR_lt hzR_eq, hout⟩
}

/--
Repaired Kőnig + Prefix-Stabilization + Bounded-Branch Elimination Reduction of `InfiniteTwos`:
Refuting every zero cut `z_0 ≥ 3` (and hence proving `InfiniteTwos`) reduces to ruling out an
**unbounded** deterministic post-stabilization `2`-free sequence `g` (`g 0 = 0`, `∀ j ≥ 1, g j ≠ 2`,
no adjacent `(1, 1)`, infinitely many zeros, unbounded, and `IsVanEckFrom g M_0`). All bounded
`2`-free DFS rays (including `[0, 1, 1, 1, ...]`) are already unconditionally eliminated above.
-/
theorem infinite_twos_of_no_post_cut_two_free_tail
    (h_no_tail : ∀ (g : ℕ → ℕ) (M_0 : ℕ),
      g 0 = 0 →
      (∀ j ≥ 1, g j ≠ 2) →
      (∀ j, ¬ (g j = 1 ∧ g (j + 1) = 1)) →
      (∀ K, ∃ z > K, g z = 0) →
      (∀ B, ∃ j, B < g j) →
      IsVanEckFrom g M_0 →
      False) :
    (∀ z_0 ≥ 3, ∃ fuel, refuteNoTwosZ0Fast z_0 fuel = true) ∧ InfiniteTwos := by {
  have h_cut : ∀ z_0 ≥ 3, ∃ fuel, refuteNoTwosZ0Fast z_0 fuel = true := by {
    intro z_0 _hz0
    by_contra h_not
    rcases nonempty_infinite_dfs_ray_of_not_refuted z_0 h_not with ⟨R⟩
    rcases dfs_ray_shifted_seq_spec R with ⟨hg0, _, hg_no2, T_stab, hg_rec⟩
    exact h_no_tail (raySeq R) (T_stab + 1) hg0 hg_no2
      (dfs_ray_no_stutter_one R) (raySeq_infinite_zeros R) (raySeq_unbounded R) hg_rec
  }
  exact ⟨h_cut, infinite_twos_of_zero_cut_refuted h_cut⟩
}

/-!
## Return-Gap Forest & Aperiodic Exact-Cover Conservation
-/

/-- `IsConsecOcc p q` holds when `p < q` are consecutive occurrence indices of the same
Van Eck value (`a(p) = a(q)` with no intermediate occurrence in `(p, q)`). -/
def IsConsecOcc (p q : ℕ) : Prop :=
  p < q ∧ vanEckNthTerm p = vanEckNthTerm q ∧
    ∀ k, p < k → k < q → vanEckNthTerm k ≠ vanEckNthTerm q

instance instDecidableIsConsecOcc (p q : ℕ) : Decidable (IsConsecOcc p q) := by {
  unfold IsConsecOcc
  have h_iff : (∀ k, p < k → k < q → vanEckNthTerm k ≠ vanEckNthTerm q) ↔
      ∀ k ∈ Finset.Ioo p q, vanEckNthTerm k ≠ vanEckNthTerm q := by {
    constructor
    · intro h k hk
      have hk_ioo := Finset.mem_Ioo.mp hk
      exact h k hk_ioo.1 hk_ioo.2
    · intro h k hk1 hk2
      exact h k (Finset.mem_Ioo.mpr ⟨hk1, hk2⟩)
  }
  exact decidable_of_iff
    (p < q ∧ vanEckNthTerm p = vanEckNthTerm q ∧
      ∀ k ∈ Finset.Ioo p q, vanEckNthTerm k ≠ vanEckNthTerm q)
    (and_congr_right (fun _ => and_congr_right (fun _ => h_iff.symm)))
}

/-- Every positive Van Eck term `a(n) > 0` corresponds, via a `-1` index shift, to the
consecutive-occurrence link `(n - 1 - a(n), n - 1)` of gap length `a(n)`. -/
lemma isConsecOcc_of_pos_term (n : ℕ) (h_pos : 0 < vanEckNthTerm n) :
    2 ≤ n ∧ vanEckNthTerm n ≤ n - 1 ∧ IsConsecOcc (n - 1 - vanEckNthTerm n) (n - 1) ∧
      (n - 1) - (n - 1 - vanEckNthTerm n) = vanEckNthTerm n := by {
  have hn2 : 2 ≤ n := by {
    by_contra hlt
    interval_cases n
    · change 0 < 0 at h_pos
      omega
    · change 0 < 0 at h_pos
      omega
  }
  have h_le : vanEckNthTerm n ≤ n - 1 := a_le_idx_minus_one hn2 h_pos
  have h_rec := pos_value_most_recent_occurrence n (vanEckNthTerm n) hn2 rfl h_pos
  refine ⟨hn2, h_le, ⟨h_rec.1, h_rec.2.1, h_rec.2.2⟩, ?_⟩
  omega
}

/-- Conversely, every consecutive-occurrence link `(p, q)` produces the positive Van Eck
term `a(q + 1) = q - p > 0` at the shifted index `q + 1`, recovering `p`. -/
lemma pos_term_of_isConsecOcc {p q : ℕ} (h : IsConsecOcc p q) :
    vanEckNthTerm (q + 1) = q - p ∧ 0 < vanEckNthTerm (q + 1) ∧
      (q + 1) - 1 - vanEckNthTerm (q + 1) = p := by {
  rcases h with ⟨hpq, h_eq, h_no_int⟩
  have h_gap : vanEckNthTerm (q + 1) = q - p :=
    strict_prior_match_gives_gap p q hpq h_eq.symm h_no_int
  refine ⟨h_gap, ?_, ?_⟩
  · omega
  · omega
}

/-- Consecutive-occurrence pairs `(p, q)` inside the finite prefix `[0, N)`. -/
def consecOccPairs (N : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.range N ×ˢ Finset.range N).filter (fun pq => IsConsecOcc pq.1 pq.2)

/-- Indices `n ∈ [1, N]` where `vanEckNthTerm n > 0`. -/
def posValIndices (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => 0 < vanEckNthTerm n)

/-- Indices `n ∈ [1, N]` where `vanEckNthTerm n = 0` (positive-index zeros). -/
def posZeroIndices (N : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => vanEckNthTerm n = 0)

/-- Indices `n ∈ [1, N]` where `vanEckNthTerm n = d`. -/
def gapFiber (N d : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter (fun n => vanEckNthTerm n = d)

/-- Weighted Finset bijection between positive Van Eck indices in `[1, N]` and consecutive
occurrence links in `[0, N)`, identifying `a(n)` with the link length `q - p`. -/
theorem sum_posValIndices_eq_sum_consecOccPairs {M : Type*} [AddCommMonoid M]
    (f : ℕ → ℕ → M) (N : ℕ) :
    ∑ n ∈ posValIndices N, f (n - 1 - vanEckNthTerm n) (n - 1) =
      ∑ pq ∈ consecOccPairs N, f pq.1 pq.2 := by {
  refine Finset.sum_nbij (fun n => (n - 1 - vanEckNthTerm n, n - 1)) ?_ ?_ ?_ ?_
  · intro n hn
    have hn_mem := Finset.mem_filter.mp hn
    have hn_icc := Finset.mem_Icc.mp hn_mem.1
    have h_link := isConsecOcc_of_pos_term n hn_mem.2
    have h_le := h_link.2.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, h_link.2.2.1⟩
    · refine Finset.mem_range.mpr ?_
      change n - 1 - vanEckNthTerm n < N
      omega
    · refine Finset.mem_range.mpr ?_
      change n - 1 < N
      omega
  · intro n1 hn1 n2 hn2 h_eq
    have hn1_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn1).1
    have hn2_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn2).1
    have h2 : n1 - 1 = n2 - 1 := congrArg Prod.snd h_eq
    omega
  · intro pq hpq
    rcases pq with ⟨p, q⟩
    have hpq_f := Finset.mem_filter.mp hpq
    have hq_lt : q < N := Finset.mem_range.mp (Finset.mem_product.mp hpq_f.1).2
    have h_pos := pos_term_of_isConsecOcc hpq_f.2
    refine ⟨q + 1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by { omega }, by { omega }⟩,
      h_pos.2.1⟩, ?_⟩
    exact Prod.ext h_pos.2.2 rfl
  · intro _ _
    rfl
}

/-- Cardinality specialization: positive terms in `[1, N]` are in exact 1-to-1 correspondence
with consecutive-occurrence links in `[0, N)`. -/
theorem posValIndices_card_eq_consecOccPairs_card (N : ℕ) :
    (posValIndices N).card = (consecOccPairs N).card := by {
  have h := sum_posValIndices_eq_sum_consecOccPairs (fun _ _ => (1 : ℕ)) N
  simpa only [Finset.sum_const, smul_eq_mul, mul_one] using h
}

/-- `InfiniteTwos` is equivalent to the occurrence forest containing infinitely many
consecutive-occurrence links of length `2`. -/
theorem infinite_twos_iff_infinite_len_two_links :
    InfiniteTwos ↔ ∀ N, ∃ p q, N < q + 1 ∧ IsConsecOcc p q ∧ q - p = 2 := by {
  constructor
  · intro h_inf N
    rcases h_inf (max N 3) with ⟨m, hm_gt, hm_two⟩
    have hm_pos : 0 < vanEckNthTerm m := by { omega }
    have h_link := isConsecOcc_of_pos_term m hm_pos
    refine ⟨m - 1 - vanEckNthTerm m, m - 1, by { omega }, h_link.2.2.1, ?_⟩
    rw [h_link.2.2.2, hm_two]
  · intro h_links N
    rcases h_links N with ⟨p, q, hq_gt, h_link, h_len⟩
    have h_pos := pos_term_of_isConsecOcc h_link
    exact ⟨q + 1, hq_gt, by { omega }⟩
}

/-- Occurrence indices of value `v` in `[0, N)`. -/
def occFiber (N v : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun i => vanEckNthTerm i = v)

/-- Distinct values seen in the prefix `[0, N)`. -/
def seenValues (N : ℕ) : Finset ℕ :=
  (Finset.range N).image vanEckNthTerm

/-- First occurrence index of `v` in `[0, N)` (or `0` if unseen). -/
def firstOccIn (N v : ℕ) : ℕ :=
  if h : (occFiber N v).Nonempty then (occFiber N v).min' h else 0

/-- Last occurrence index of `v` in `[0, N)` (or `0` if unseen). -/
def lastOccIn (N v : ℕ) : ℕ :=
  if h : (occFiber N v).Nonempty then (occFiber N v).max' h else 0

/-- Chain-start indices in `[0, N)`: indices `m < N` followed by a zero `a(m + 1) = 0`. -/
def firstOccIndices (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun m => vanEckNthTerm (m + 1) = 0)

/-- Chain-end (frontier) indices in `[0, N)`: indices `p < N` with no later match in `[0, N)`. -/
def lastOccIndices (N : ℕ) : Finset ℕ :=
  (Finset.range N).filter (fun p => ∀ q ∈ Finset.Ioo p N, vanEckNthTerm q ≠ vanEckNthTerm p)

lemma mem_lastOccIndices_iff (N p : ℕ) :
    p ∈ lastOccIndices N ↔
      p < N ∧ ∀ q, p < q → q < N → vanEckNthTerm q ≠ vanEckNthTerm p := by {
  simp only [lastOccIndices, Finset.mem_filter, Finset.mem_range, Finset.mem_Ioo]
  exact and_congr_right (fun _ => ⟨fun h q hq1 hq2 => h q ⟨hq1, hq2⟩,
    fun h q hq => h q hq.1 hq.2⟩)
}

lemma occFiber_nonempty_iff_mem_seenValues (N v : ℕ) :
    (occFiber N v).Nonempty ↔ v ∈ seenValues N := by {
  constructor
  · rintro ⟨i, hi⟩
    have hi_f := Finset.mem_filter.mp hi
    exact Finset.mem_image.mpr ⟨i, hi_f.1, hi_f.2⟩
  · intro hv
    rcases Finset.mem_image.mp hv with ⟨i, hi_r, rfl⟩
    exact ⟨i, Finset.mem_filter.mpr ⟨hi_r, rfl⟩⟩
}

lemma firstOccIn_spec {N v : ℕ} (hv : v ∈ seenValues N) :
    firstOccIn N v < N ∧ vanEckNthTerm (firstOccIn N v) = v ∧
      ∀ i < firstOccIn N v, vanEckNthTerm i ≠ v := by {
  have hne : (occFiber N v).Nonempty := (occFiber_nonempty_iff_mem_seenValues N v).mpr hv
  have h_eq : firstOccIn N v = (occFiber N v).min' hne := dif_pos hne
  have h_mem := Finset.min'_mem (occFiber N v) hne
  rw [← h_eq] at h_mem
  have h_f := Finset.mem_filter.mp h_mem
  have h_lt : firstOccIn N v < N := Finset.mem_range.mp h_f.1
  refine ⟨h_lt, h_f.2, ?_⟩
  intro i hi h_iv
  have hi_mem : i ∈ occFiber N v :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by { omega }), h_iv⟩
  have h_le : firstOccIn N v ≤ i := by {
    rw [h_eq]
    exact Finset.min'_le (occFiber N v) i hi_mem
  }
  omega
}

lemma lastOccIn_spec {N v : ℕ} (hv : v ∈ seenValues N) :
    lastOccIn N v < N ∧ vanEckNthTerm (lastOccIn N v) = v ∧
      ∀ q, lastOccIn N v < q → q < N → vanEckNthTerm q ≠ v := by {
  have hne : (occFiber N v).Nonempty := (occFiber_nonempty_iff_mem_seenValues N v).mpr hv
  have h_eq : lastOccIn N v = (occFiber N v).max' hne := dif_pos hne
  have h_mem := Finset.max'_mem (occFiber N v) hne
  rw [← h_eq] at h_mem
  have h_f := Finset.mem_filter.mp h_mem
  have h_lt : lastOccIn N v < N := Finset.mem_range.mp h_f.1
  refine ⟨h_lt, h_f.2, ?_⟩
  intro q hq1 hq2 h_qv
  have hq_mem : q ∈ occFiber N v :=
    Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hq2, h_qv⟩
  have h_le : q ≤ lastOccIn N v := by {
    rw [h_eq]
    exact Finset.le_max' (occFiber N v) q hq_mem
  }
  omega
}

lemma firstOccIn_le_lastOccIn {N v : ℕ} (hv : v ∈ seenValues N) :
    firstOccIn N v ≤ lastOccIn N v := by {
  have hne : (occFiber N v).Nonempty := (occFiber_nonempty_iff_mem_seenValues N v).mpr hv
  rw [firstOccIn, lastOccIn, dif_pos hne, dif_pos hne]
  exact Finset.min'_le (occFiber N v) _ (Finset.max'_mem (occFiber N v) hne)
}

lemma mem_firstOccIndices_iff (N m : ℕ) :
    m ∈ firstOccIndices N ↔ m < N ∧ ∀ i < m, vanEckNthTerm i ≠ vanEckNthTerm m := by {
  simp only [firstOccIndices, Finset.mem_filter, Finset.mem_range]
  refine and_congr_right (fun _ => ?_)
  constructor
  · intro hz i hi
    by_cases hm0 : m = 0
    · omega
    · exact Ne.symm (pre_zero_ne_prior_val (m + 1) i hz (by { omega }) (by { omega }))
  · intro h_new
    exact new_value_next_is_zero m h_new
}

theorem sum_seenValues_firstOcc_eq {M : Type*} [AddCommMonoid M] (h : ℕ → M) (N : ℕ) :
    ∑ v ∈ seenValues N, h (firstOccIn N v) = ∑ m ∈ firstOccIndices N, h m := by {
  refine Finset.sum_nbij (fun v => firstOccIn N v) ?_ ?_ ?_ ?_
  · intro v hv
    have hs := firstOccIn_spec hv
    rw [mem_firstOccIndices_iff]
    refine ⟨hs.1, fun i hi => ?_⟩
    rw [hs.2.1]
    exact hs.2.2 i hi
  · intro v1 hv1 v2 hv2 h_eq
    have hs1 := (firstOccIn_spec hv1).2.1
    have hs2 := (firstOccIn_spec hv2).2.1
    calc v1 = vanEckNthTerm (firstOccIn N v1) := hs1.symm
      _ = vanEckNthTerm (firstOccIn N v2) := congrArg vanEckNthTerm h_eq
      _ = v2 := hs2
  · intro m hm
    have hm_mem : m ∈ firstOccIndices N := Finset.mem_coe.mp hm
    rw [mem_firstOccIndices_iff] at hm_mem
    have hv : vanEckNthTerm m ∈ seenValues N :=
      Finset.mem_image.mpr ⟨m, Finset.mem_range.mpr hm_mem.1, rfl⟩
    refine ⟨vanEckNthTerm m, Finset.mem_coe.mpr hv, ?_⟩
    change firstOccIn N (vanEckNthTerm m) = m
    have hs := firstOccIn_spec hv
    by_contra h_ne
    rcases lt_trichotomy (firstOccIn N (vanEckNthTerm m)) m with hlt | heq | hgt
    · exact hm_mem.2 _ hlt hs.2.1
    · exact h_ne heq
    · exact hs.2.2 m hgt rfl
  · intro _ _
    rfl
}

theorem sum_seenValues_lastOcc_eq {M : Type*} [AddCommMonoid M] (h : ℕ → M) (N : ℕ) :
    ∑ v ∈ seenValues N, h (lastOccIn N v) = ∑ p ∈ lastOccIndices N, h p := by {
  refine Finset.sum_nbij (fun v => lastOccIn N v) ?_ ?_ ?_ ?_
  · intro v hv
    have hs := lastOccIn_spec hv
    rw [mem_lastOccIndices_iff]
    refine ⟨hs.1, fun q hq1 hq2 => ?_⟩
    rw [hs.2.1]
    exact hs.2.2 q hq1 hq2
  · intro v1 hv1 v2 hv2 h_eq
    have hs1 := (lastOccIn_spec hv1).2.1
    have hs2 := (lastOccIn_spec hv2).2.1
    calc v1 = vanEckNthTerm (lastOccIn N v1) := hs1.symm
      _ = vanEckNthTerm (lastOccIn N v2) := congrArg vanEckNthTerm h_eq
      _ = v2 := hs2
  · intro p hp
    have hp_mem : p ∈ lastOccIndices N := Finset.mem_coe.mp hp
    rw [mem_lastOccIndices_iff] at hp_mem
    have hv : vanEckNthTerm p ∈ seenValues N :=
      Finset.mem_image.mpr ⟨p, Finset.mem_range.mpr hp_mem.1, rfl⟩
    refine ⟨vanEckNthTerm p, Finset.mem_coe.mpr hv, ?_⟩
    change lastOccIn N (vanEckNthTerm p) = p
    have hs := lastOccIn_spec hv
    by_contra h_ne
    rcases lt_trichotomy (lastOccIn N (vanEckNthTerm p)) p with hlt | heq | hgt
    · exact hs.2.2 p hlt hp_mem.1 rfl
    · exact h_ne heq
    · exact hp_mem.2 _ hgt hs.1 hs.2.1
  · intro _ _
    rfl
}

/-- The number of distinct values seen in `[0, N)` (number of return chains) equals the
number of zeros in `[1, N]`. -/
theorem seenValues_card_eq_posZeroIndices_card (N : ℕ) :
    (seenValues N).card = (posZeroIndices N).card := by {
  have h1 := sum_seenValues_firstOcc_eq (fun _ => (1 : ℕ)) N
  simp only [Finset.sum_const, smul_eq_mul, mul_one] at h1
  rw [h1]
  refine Finset.card_nbij (fun m => m + 1) ?_ ?_ ?_
  · intro m hm
    have hm_f := Finset.mem_filter.mp hm
    have hm_lt : m < N := Finset.mem_range.mp hm_f.1
    refine Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨?_, ?_⟩, hm_f.2⟩
    · change 1 ≤ m + 1
      omega
    · change m + 1 ≤ N
      omega
  · intro m1 _ m2 _ h_eq
    change m1 + 1 = m2 + 1 at h_eq
    omega
  · intro n hn
    have hn_f := Finset.mem_filter.mp hn
    have hn_icc := Finset.mem_Icc.mp hn_f.1
    refine ⟨n - 1, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by { omega }), ?_⟩, ?_⟩
    · have h_add : n - 1 + 1 = n := by { omega }
      rw [h_add]
      exact hn_f.2
    · change n - 1 + 1 = n
      omega
}

lemma sum_posValIndices_curr_eq {M : Type*} [AddCommMonoid M] (h : ℕ → M) (N : ℕ) :
    ∑ n ∈ posValIndices N, h (n - 1) = ∑ m ∈ Finset.range N \ firstOccIndices N, h m := by {
  refine Finset.sum_nbij (fun n => n - 1) ?_ ?_ ?_ ?_
  · intro n hn
    have hn_f := Finset.mem_filter.mp hn
    have hn_icc := Finset.mem_Icc.mp hn_f.1
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · change n - 1 < N
      omega
    · intro hm_first
      have hz := (Finset.mem_filter.mp hm_first).2
      have h_add : n - 1 + 1 = n := by { omega }
      rw [h_add] at hz
      omega
  · intro n1 hn1 n2 hn2 h_eq
    have hn1_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn1).1
    have hn2_icc := Finset.mem_Icc.mp (Finset.mem_filter.mp hn2).1
    change n1 - 1 = n2 - 1 at h_eq
    omega
  · intro m hm
    have hm_sd := Finset.mem_sdiff.mp hm
    have hm_lt : m < N := Finset.mem_range.mp hm_sd.1
    have h_nz : vanEckNthTerm (m + 1) ≠ 0 := by {
      intro hz
      exact hm_sd.2 (Finset.mem_filter.mpr ⟨hm_sd.1, hz⟩)
    }
    exact ⟨m + 1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by { omega }, by { omega }⟩,
      Nat.pos_of_ne_zero h_nz⟩, rfl⟩
  · intro _ _
    rfl
}

lemma exists_consecOcc_of_not_lastOcc {N p : ℕ} (hp : p ∈ Finset.range N \ lastOccIndices N) :
    ∃ q < N, IsConsecOcc p q := by {
  have hp_sd := Finset.mem_sdiff.mp hp
  have hp_lt : p < N := Finset.mem_range.mp hp_sd.1
  have h_ex : ∃ q, q < N ∧ p < q ∧ vanEckNthTerm q = vanEckNthTerm p := by {
    by_contra h_none
    push Not at h_none
    exact hp_sd.2 ((mem_lastOccIndices_iff N p).mpr ⟨hp_lt, fun q hq1 hq2 => h_none q hq2 hq1⟩)
  }
  let S := (Finset.range N).filter (fun q => p < q ∧ vanEckNthTerm q = vanEckNthTerm p)
  have hS_ne : S.Nonempty := by {
    rcases h_ex with ⟨q, hqN, hpq, h_eq⟩
    exact ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hqN, hpq, h_eq⟩⟩
  }
  let q := S.min' hS_ne
  have hq_f := Finset.mem_filter.mp (Finset.min'_mem S hS_ne)
  refine ⟨q, Finset.mem_range.mp hq_f.1, hq_f.2.1, hq_f.2.2.symm, fun k hpk hkq h_kv => ?_⟩
  have hq_lt : q < N := Finset.mem_range.mp hq_f.1
  have hk_mem : k ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_range.mpr (by { omega }),
    hpk, h_kv.trans hq_f.2.2⟩
  have hq_le : q ≤ k := Finset.min'_le S k hk_mem
  omega
}

lemma sum_posValIndices_prev_eq {M : Type*} [AddCommMonoid M] (h : ℕ → M) (N : ℕ) :
    ∑ n ∈ posValIndices N, h (n - 1 - vanEckNthTerm n) =
      ∑ p ∈ Finset.range N \ lastOccIndices N, h p := by {
  refine Finset.sum_nbij (fun n => n - 1 - vanEckNthTerm n) ?_ ?_ ?_ ?_
  · intro n hn
    have hn_f := Finset.mem_filter.mp hn
    have hn_icc := Finset.mem_Icc.mp hn_f.1
    have h_link := isConsecOcc_of_pos_term n hn_f.2
    have h_le := h_link.2.1
    refine Finset.mem_sdiff.mpr ⟨Finset.mem_range.mpr ?_, ?_⟩
    · change n - 1 - vanEckNthTerm n < N
      omega
    · intro hp_last
      rw [mem_lastOccIndices_iff] at hp_last
      exact hp_last.2 (n - 1) h_link.2.2.1.1 (by { omega }) h_link.2.2.1.2.1.symm
  · intro n1 hn1 n2 hn2 h_eq
    change n1 - 1 - vanEckNthTerm n1 = n2 - 1 - vanEckNthTerm n2 at h_eq
    have h1_pos := (Finset.mem_filter.mp hn1).2
    have h2_pos := (Finset.mem_filter.mp hn2).2
    have h1_le := (isConsecOcc_of_pos_term n1 h1_pos).2.1
    have h2_le := (isConsecOcc_of_pos_term n2 h2_pos).2.1
    have h_sub_eq : n1 - vanEckNthTerm n1 = n2 - vanEckNthTerm n2 := by { omega }
    by_contra h_ne
    rcases lt_trichotomy n1 n2 with hlt | heq | hgt
    · exact vanEck_idx_sub_val_unique n1 n2 h1_pos hlt h_sub_eq
    · exact h_ne heq
    · exact vanEck_idx_sub_val_unique n2 n1 h2_pos hgt h_sub_eq.symm
  · intro p hp
    rcases exists_consecOcc_of_not_lastOcc hp with ⟨q, hq_lt, h_consec⟩
    have h_pos := pos_term_of_isConsecOcc h_consec
    exact ⟨q + 1, Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨by { omega }, by { omega }⟩,
      h_pos.2.1⟩, h_pos.2.2⟩
  · intro _ _
    rfl
}

/-- Master Return-Forest Conservation Law: for any `AddCommGroup`-valued test function `h`,
summing `h(n - 1) - h(n - 1 - a(n))` across `n ∈ [1, N]` telescopes along every occurrence
chain to `∑ v ∈ seenValues N, (h(lastOccIn N v) - h(firstOccIn N v))`. -/
theorem sum_return_chain_diff_eq {M : Type*} [AddCommGroup M] (h : ℕ → M) (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, (h (n - 1) - h (n - 1 - vanEckNthTerm n)) =
      ∑ v ∈ seenValues N, (h (lastOccIn N v) - h (firstOccIn N v)) := by {
  have h_filter : ∑ n ∈ Finset.Icc 1 N, (h (n - 1) - h (n - 1 - vanEckNthTerm n)) =
      ∑ n ∈ posValIndices N, (h (n - 1) - h (n - 1 - vanEckNthTerm n)) := by {
    rw [posValIndices, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N)
      (fun n => 0 < vanEckNthTerm n)]
    have h_zero_part : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ 0 < vanEckNthTerm n),
        (h (n - 1) - h (n - 1 - vanEckNthTerm n)) = 0 := by {
      refine Finset.sum_eq_zero (fun n hn => ?_)
      have hz : vanEckNthTerm n = 0 := by {
        have hnot := (Finset.mem_filter.mp hn).2
        omega
      }
      rw [hz, Nat.sub_zero, sub_self]
    }
    rw [h_zero_part, add_zero]
  }
  rw [h_filter, Finset.sum_sub_distrib, sum_posValIndices_curr_eq, sum_posValIndices_prev_eq]
  have h_first_sub : firstOccIndices N ⊆ Finset.range N := Finset.filter_subset _ _
  have h_last_sub : lastOccIndices N ⊆ Finset.range N := Finset.filter_subset _ _
  have h_sd1 := Finset.sum_sdiff h_first_sub (f := h)
  have h_sd2 := Finset.sum_sdiff h_last_sub (f := h)
  rw [Finset.sum_sub_distrib, sum_seenValues_lastOcc_eq, sum_seenValues_firstOcc_eq,
    sub_eq_sub_iff_add_eq_add]
  exact h_sd1.trans (h_sd2.symm.trans (add_comm _ _))
}

/-- Finite-Prefix Return-Gap Sum Identity: the sum of Van Eck terms `a(1) + ⋯ + a(N)` equals
the sum over distinct values seen in `[0, N)` of `lastOccIn N v - firstOccIn N v`. -/
theorem sum_vanEck_eq_sum_last_sub_first (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, vanEckNthTerm n =
      ∑ v ∈ seenValues N, (lastOccIn N v - firstOccIn N v) := by {
  have h_int := sum_return_chain_diff_eq (fun k => (k : ℤ)) N
  have h_lhs : ∑ n ∈ Finset.Icc 1 N, ((n - 1 : ℕ) - (n - 1 - vanEckNthTerm n : ℕ) : ℤ) =
      ((∑ n ∈ Finset.Icc 1 N, vanEckNthTerm n : ℕ) : ℤ) := by {
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h_pos : 0 < vanEckNthTerm n
    · have h_le := (isConsecOcc_of_pos_term n h_pos).2.1
      omega
    · have hz : vanEckNthTerm n = 0 := by { omega }
      rw [hz]
      simp
  }
  have h_rhs : ∑ v ∈ seenValues N, ((lastOccIn N v : ℤ) - (firstOccIn N v : ℤ)) =
      ((∑ v ∈ seenValues N, (lastOccIn N v - firstOccIn N v) : ℕ) : ℤ) := by {
    rw [Nat.cast_sum]
    refine Finset.sum_congr rfl (fun v hv => ?_)
    have h_le := firstOccIn_le_lastOccIn hv
    omega
  }
  rw [h_lhs, h_rhs] at h_int
  exact Int.ofNat.inj h_int
}

/-- Prefix sum from `0` through `N` (since `a(0) = 0`) equals the sum of chain spans. -/
theorem sum_vanEck_range_eq_sum_last_sub_first (N : ℕ) :
    ∑ n ∈ Finset.range (N + 1), vanEckNthTerm n =
      ∑ v ∈ seenValues N, (lastOccIn N v - firstOccIn N v) := by {
  rw [← sum_vanEck_eq_sum_last_sub_first N]
  have h_split : Finset.range (N + 1) = insert 0 (Finset.Icc 1 N) := by {
    ext x
    simp only [Finset.mem_range, Finset.mem_insert, Finset.mem_Icc]
    omega
  }
  rw [h_split, Finset.sum_insert (by { simp })]
  change 0 + ∑ n ∈ Finset.Icc 1 N, vanEckNthTerm n = _
  exact zero_add _
}

/-- Decomposition of positive indices in `[1, N]` into pairwise-disjoint fibers `gapFiber N d`. -/
lemma posValIndices_eq_biUnion_gapFiber (N : ℕ) :
    posValIndices N = (Finset.Icc 1 N).biUnion (gapFiber N) := by {
  ext n
  simp only [posValIndices, gapFiber, Finset.mem_biUnion, Finset.mem_filter, Finset.mem_Icc]
  constructor
  · rintro ⟨⟨h1, hN⟩, hpos⟩
    have hle := (isConsecOcc_of_pos_term n hpos).2.1
    exact ⟨vanEckNthTerm n, ⟨by { omega }, by { omega }⟩, ⟨h1, hN⟩, rfl⟩
  · rintro ⟨d, ⟨hd1, _⟩, ⟨h1, hN⟩, rfl⟩
    exact ⟨⟨h1, hN⟩, by { omega }⟩
}

lemma zpow_diff_eq_one_sub_inv_pow (z : ℂ) (hz : z ≠ 0) {n d : ℕ} (h_le : d ≤ n - 1) :
    (1 - z⁻¹ ^ d) * z ^ (n - 1) = z ^ (n - 1) - z ^ (n - 1 - d) := by {
  have h_split : n - 1 = (n - 1 - d) + d := (Nat.sub_add_cancel h_le).symm
  have h_pow : z ^ (n - 1) = z ^ (n - 1 - d) * z ^ d := by {
    conv_lhs => rw [h_split]
    exact pow_add z (n - 1 - d) d
  }
  have h_inv : z⁻¹ ^ d * z ^ d = 1 := by {
    rw [← mul_pow, inv_mul_cancel₀ hz, one_pow]
  }
  calc (1 - z⁻¹ ^ d) * z ^ (n - 1)
    _ = z ^ (n - 1) - z ^ (n - 1 - d) * (z⁻¹ ^ d * z ^ d) := by {
      rw [h_pow]
      ring
    }
    _ = z ^ (n - 1) - z ^ (n - 1 - d) := by { rw [h_inv, mul_one] }
}

/-- Aperiodic Mirsky–Newman Spectral Identity: for every `z ∈ ℂ \ {0}`, weighting the return
forest by `z^k` groups positive gaps into `(1 - z⁻ᵈ) ∑_{n ∈ gapFiber N d} z^(n - 1)` on the
left and chain-endpoint differences `z^(lastOcc) - z^(firstOcc)` on the right. -/
theorem aperiodic_mirsky_newman_identity (z : ℂ) (hz : z ≠ 0) (N : ℕ) :
    ∑ d ∈ Finset.Icc 1 N, (1 - z⁻¹ ^ d) * (∑ n ∈ gapFiber N d, z ^ (n - 1)) =
      ∑ v ∈ seenValues N, (z ^ lastOccIn N v - z ^ firstOccIn N v) := by {
  rw [← sum_return_chain_diff_eq (fun k => z ^ k) N]
  have h_pos_only : ∑ n ∈ Finset.Icc 1 N, (z ^ (n - 1) - z ^ (n - 1 - vanEckNthTerm n)) =
      ∑ n ∈ posValIndices N, (z ^ (n - 1) - z ^ (n - 1 - vanEckNthTerm n)) := by {
    rw [posValIndices, ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N)
      (fun n => 0 < vanEckNthTerm n)]
    have h0 : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ 0 < vanEckNthTerm n),
        (z ^ (n - 1) - z ^ (n - 1 - vanEckNthTerm n)) = 0 := by {
      refine Finset.sum_eq_zero (fun n hn => ?_)
      have hz0 : vanEckNthTerm n = 0 := by {
        have hnot := (Finset.mem_filter.mp hn).2
        omega
      }
      rw [hz0, Nat.sub_zero, sub_self]
    }
    rw [h0, add_zero]
  }
  rw [h_pos_only, posValIndices_eq_biUnion_gapFiber N]
  have h_disj : Set.PairwiseDisjoint (Finset.Icc 1 N : Set ℕ) (gapFiber N) := by {
    intro d1 _ d2 _ hne
    refine Finset.disjoint_left.mpr (fun n hn1 hn2 => ?_)
    exact hne ((Finset.mem_filter.mp hn1).2.symm.trans (Finset.mem_filter.mp hn2).2)
  }
  rw [Finset.sum_biUnion h_disj]
  refine Finset.sum_congr rfl (fun d hd => ?_)
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hd_pos : 0 < d := (Finset.mem_Icc.mp hd).1
  have hn_val : vanEckNthTerm n = d := (Finset.mem_filter.mp hn).2
  have h_le : d ≤ n - 1 := by {
    have h_pos : 0 < vanEckNthTerm n := by { omega }
    have hle := (isConsecOcc_of_pos_term n h_pos).2.1
    omega
  }
  rw [hn_val]
  exact zpow_diff_eq_one_sub_inv_pow z hz h_le
}

/-- Unit-Circle Boundary Defect Bound: at every `z ∈ ℂ` with `‖z‖ = 1` (including all roots
of unity), the spectral return-gap sum has norm at most `2 * |posZeroIndices N|`. -/
theorem aperiodic_mirsky_newman_norm_le_two_mul_zeros (z : ℂ) (hz : ‖z‖ = 1) (N : ℕ) :
    ‖∑ d ∈ Finset.Icc 1 N, (1 - z⁻¹ ^ d) * (∑ n ∈ gapFiber N d, z ^ (n - 1))‖ ≤
      2 * ((posZeroIndices N).card : ℝ) := by {
  have hz_ne : z ≠ 0 := by {
    intro h0
    rw [h0, norm_zero] at hz
    norm_num at hz
  }
  rw [aperiodic_mirsky_newman_identity z hz_ne N]
  have h_tri := norm_sum_le (seenValues N) (fun v => z ^ lastOccIn N v - z ^ firstOccIn N v)
  have h_each : ∑ v ∈ seenValues N, ‖z ^ lastOccIn N v - z ^ firstOccIn N v‖ ≤
      ∑ _v ∈ seenValues N, (2 : ℝ) := by {
    refine Finset.sum_le_sum (fun v _ => ?_)
    calc ‖z ^ lastOccIn N v - z ^ firstOccIn N v‖
      _ ≤ ‖z ^ lastOccIn N v‖ + ‖z ^ firstOccIn N v‖ := norm_sub_le _ _
      _ = ‖z‖ ^ lastOccIn N v + ‖z‖ ^ firstOccIn N v := by { rw [norm_pow, norm_pow] }
      _ = 2 := by {
        rw [hz, one_pow, one_pow]
        norm_num
      }
  }
  have h_const : ∑ _v ∈ seenValues N, (2 : ℝ) = 2 * ((posZeroIndices N).card : ℝ) := by {
    rw [Finset.sum_const, nsmul_eq_mul, seenValues_card_eq_posZeroIndices_card N, mul_comm]
  }
  exact (h_tri.trans h_each).trans_eq h_const
}

/-- Signed Odd-Gap Parity Balance (`z = -1` over `ℤ`): even return gaps annihilate, while
odd return gaps telescope to chain-endpoint parity flips. -/
theorem odd_gap_parity_balance (N : ℕ) :
    2 * ∑ n ∈ (Finset.Icc 1 N).filter (fun n => vanEckNthTerm n % 2 = 1),
        (-1 : ℤ) ^ (n - 1) =
      ∑ v ∈ seenValues N, ((-1 : ℤ) ^ lastOccIn N v - (-1 : ℤ) ^ firstOccIn N v) := by {
  rw [← sum_return_chain_diff_eq (fun k => (-1 : ℤ) ^ k) N, Finset.mul_sum,
    ← Finset.sum_filter_add_sum_filter_not (Finset.Icc 1 N) (fun n => vanEckNthTerm n % 2 = 1)]
  have h_even_zero : ∑ n ∈ (Finset.Icc 1 N).filter (fun n => ¬ vanEckNthTerm n % 2 = 1),
      ((-1 : ℤ) ^ (n - 1) - (-1 : ℤ) ^ (n - 1 - vanEckNthTerm n)) = 0 := by {
    refine Finset.sum_eq_zero (fun n hn => ?_)
    have hnot := (Finset.mem_filter.mp hn).2
    by_cases hpos : 0 < vanEckNthTerm n
    · have hle := (isConsecOcc_of_pos_term n hpos).2.1
      have hev : vanEckNthTerm n = 2 * (vanEckNthTerm n / 2) := by { omega }
      have hsp : n - 1 = (n - 1 - vanEckNthTerm n) + 2 * (vanEckNthTerm n / 2) := by { omega }
      have hpow : (-1 : ℤ) ^ (n - 1) = (-1 : ℤ) ^ (n - 1 - vanEckNthTerm n) := by {
        conv_lhs => rw [hsp]
        rw [pow_add, pow_mul]
        norm_num
      }
      rw [hpow, sub_self]
    · have hz : vanEckNthTerm n = 0 := by { omega }
      rw [hz, Nat.sub_zero, sub_self]
  }
  rw [h_even_zero, add_zero]
  refine Finset.sum_congr rfl (fun n hn => ?_)
  have hodd : vanEckNthTerm n % 2 = 1 := (Finset.mem_filter.mp hn).2
  have hpos : 0 < vanEckNthTerm n := by { omega }
  have hle := (isConsecOcc_of_pos_term n hpos).2.1
  have hsp : n - 1 = (n - 1 - vanEckNthTerm n) + (2 * (vanEckNthTerm n / 2) + 1) := by { omega }
  have hpow : (-1 : ℤ) ^ (n - 1) = -(-1 : ℤ) ^ (n - 1 - vanEckNthTerm n) := by {
    conv_lhs => rw [hsp]
    rw [pow_add, pow_add, pow_mul]
    norm_num
  }
  have h_inv : (-1 : ℤ) ^ (n - 1 - vanEckNthTerm n) = -(-1 : ℤ) ^ (n - 1) := by { omega }
  rw [h_inv]
  ring
}

/-- Any `S : Finset ℕ` satisfies `|S| * (|S| - 1) ≤ 2 * ∑ x ∈ S, x`. -/
lemma card_mul_pred_le_two_mul_sum (S : Finset ℕ) :
    S.card * (S.card - 1) ≤ 2 * ∑ x ∈ S, x := by {
  induction h_card : S.card using Nat.strong_induction_on generalizing S with
  | h k ih =>
    by_cases hk0 : k = 0
    · rw [hk0]
      omega
    · have hne : S.Nonempty := Finset.card_pos.mp (by { omega })
      let m := S.max' hne
      have hm_mem : m ∈ S := Finset.max'_mem S hne
      let S' := S.erase m
      have hS'_card : S'.card = k - 1 := by {
        rw [Finset.card_erase_of_mem hm_mem, h_card]
      }
      have h_ih := ih (k - 1) (by { omega }) S' hS'_card
      have hS'_sub : S' ⊆ Finset.range m := by {
        intro x hx
        have hx_er := Finset.mem_erase.mp hx
        have hx_le : x ≤ m := Finset.le_max' S x hx_er.2
        exact Finset.mem_range.mpr (Nat.lt_of_le_of_ne hx_le hx_er.1)
      }
      have hm_ge : k - 1 ≤ m := by {
        have hc := Finset.card_le_card hS'_sub
        rw [hS'_card, Finset.card_range] at hc
        exact hc
      }
      have h_sum_split : ∑ x ∈ S, x = m + ∑ x ∈ S', x :=
        (Finset.add_sum_erase S id hm_mem).symm
      rw [h_sum_split]
      have h_alg : k * (k - 1) ≤ 2 * (k - 1) + (k - 1) * (k - 1 - 1) := by {
        cases k with
        | zero => omega
        | succ k' =>
          cases k' with
          | zero => omega
          | succ k'' =>
            change (k'' + 2) * (k'' + 1) ≤ 2 * (k'' + 1) + (k'' + 1) * k''
            nlinarith
      }
      omega
}

/-- Any `S ⊆ Finset.range N` satisfies `2 * ∑ x ∈ S, x + |S| * (|S| - 1) ≤ 2 * (|S| * (N - 1))`. -/
lemma two_mul_sum_le_of_subset_range {S : Finset ℕ} {N : ℕ} (hS : S ⊆ Finset.range N) :
    2 * ∑ x ∈ S, x + S.card * (S.card - 1) ≤ 2 * (S.card * (N - 1)) := by {
  by_cases hN : N = 0
  · subst hN
    have h_emp : S = ∅ := Finset.subset_empty.mp (by { simpa using hS })
    subst h_emp
    simp
  · let T := S.image (fun x => N - 1 - x)
    have h_inj : Set.InjOn (fun x => N - 1 - x) S := by {
      intro x hx y hy h_eq
      change N - 1 - x = N - 1 - y at h_eq
      have hx_lt : x < N := Finset.mem_range.mp (hS hx)
      have hy_lt : y < N := Finset.mem_range.mp (hS hy)
      omega
    }
    have hT_card : T.card = S.card := Finset.card_image_of_injOn h_inj
    have hT_sum : ∑ y ∈ T, y = ∑ x ∈ S, (N - 1 - x) := Finset.sum_image h_inj
    have h_low := card_mul_pred_le_two_mul_sum T
    rw [hT_card, hT_sum] at h_low
    have h_add : ∑ x ∈ S, (N - 1 - x) + ∑ x ∈ S, x = S.card * (N - 1) := by {
      rw [← Finset.sum_add_distrib]
      have h_congr : ∑ x ∈ S, (N - 1 - x + x) = ∑ _x ∈ S, (N - 1) := by {
        refine Finset.sum_congr rfl (fun x hx => ?_)
        have hx_lt : x < N := Finset.mem_range.mp (hS hx)
        omega
      }
      rw [h_congr, Finset.sum_const, smul_eq_mul]
    }
    omega
}

/-- Sharp Chain-Span Packing Upper Bound: `∑_{n=1}^N a(n) ≤ Z * (N - Z)`, where
`Z = (posZeroIndices N).card` is the number of positive-index zeros in `[1, N]`. -/
theorem sum_vanEck_le_zeros_mul_complement (N : ℕ) :
    ∑ n ∈ Finset.Icc 1 N, vanEckNthTerm n ≤
      (posZeroIndices N).card * (N - (posZeroIndices N).card) := by {
  rw [sum_vanEck_eq_sum_last_sub_first N]
  let Z := (posZeroIndices N).card
  have hF_card : (firstOccIndices N).card = Z := by {
    have hc := sum_seenValues_firstOcc_eq (fun _ => (1 : ℕ)) N
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hc
    rw [← hc, seenValues_card_eq_posZeroIndices_card N]
  }
  have hL_card : (lastOccIndices N).card = Z := by {
    have hc := sum_seenValues_lastOcc_eq (fun _ => (1 : ℕ)) N
    simp only [Finset.sum_const, smul_eq_mul, mul_one] at hc
    rw [← hc, seenValues_card_eq_posZeroIndices_card N]
  }
  have hZ_le_N : Z ≤ N := by {
    rw [← hF_card]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (Finset.card_range N)
  }
  have h_split : ∑ v ∈ seenValues N, (lastOccIn N v - firstOccIn N v) +
      ∑ m ∈ firstOccIndices N, m = ∑ p ∈ lastOccIndices N, p := by {
    rw [← sum_seenValues_firstOcc_eq (fun x => x) N,
      ← sum_seenValues_lastOcc_eq (fun x => x) N, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun v hv => Nat.sub_add_cancel (firstOccIn_le_lastOccIn hv))
  }
  have h_low := card_mul_pred_le_two_mul_sum (firstOccIndices N)
  have h_sub_L : lastOccIndices N ⊆ Finset.range N := Finset.filter_subset _ _
  have h_high := two_mul_sum_le_of_subset_range h_sub_L
  rw [hF_card] at h_low
  rw [hL_card] at h_high
  by_cases hZ0 : Z = 0
  · change _ ≤ Z * (N - Z)
    have hL0 : lastOccIndices N = ∅ := Finset.card_eq_zero.mp (hL_card.trans hZ0)
    rw [hL0, Finset.sum_empty] at h_split
    rw [hZ0]
    omega
  · have h_id : Z * (N - 1) = Z * (N - Z) + Z * (Z - 1) := by {
      have hN_pos : 1 ≤ N := by { omega }
      have hZ_pos : 1 ≤ Z := by { omega }
      have h1 : (N - 1) = (N - Z) + (Z - 1) := by { omega }
      rw [h1, mul_add]
    }
    rw [h_id] at h_high
    change _ ≤ Z * (N - Z)
    omega
}

/-- Unconditional spacing in the `1`-chain: any two distinct indices where `a(i) = a(j) = 1`
satisfy `3 ≤ j - i` (no adjacent `1`s and no step-`2` `1`s anywhere in the Van Eck sequence). -/
theorem vanEck_one_gap_ge_three {i j : ℕ} (hij : i < j)
    (hi : vanEckNthTerm i = 1) (hj : vanEckNthTerm j = 1) :
    3 ≤ j - i := by {
  by_contra hlt
  have hcases : j = i + 1 ∨ j = i + 2 := by { omega }
  rcases hcases with rfl | rfl
  · exact vanEck_no_consecutive_ones i ⟨hi, hj⟩
  · have h_gap := pos_value_implies_gap (i + 2) 1 (by { omega }) hj (by { omega })
    have h_sub : i + 2 - 1 - 1 = i := by { omega }
    have h_sub1 : i + 2 - 1 = i + 1 := by { omega }
    rw [h_sub, h_sub1, hi] at h_gap
    exact vanEck_no_consecutive_ones i ⟨hi, h_gap.2.symm⟩
}

/-- In a `2`-free tail (`∀ m > N_0, a(m) ≠ 2`), every `0` or `1` after `max N_0 3` is
immediately followed by a term `a(n + 1) ≥ 3`. -/
theorem no_twos_zero_or_one_next_ge_three (N_0 n : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hn : max N_0 3 < n) (hle : vanEckNthTerm n ≤ 1) :
    3 ≤ vanEckNthTerm (n + 1) := by {
  have hn1_ne2 : vanEckNthTerm (n + 1) ≠ 2 := h_no_twos (n + 1) (by { omega })
  have hcases : vanEckNthTerm n = 0 ∨ vanEckNthTerm n = 1 := by { omega }
  rcases hcases with hz | h1
  · let z_prev := lastZero (n - 1)
    have hz_prev_zero : vanEckNthTerm z_prev = 0 := vanEck_lastZero_is_zero (n - 1)
    have hz_prev_pos : 0 < z_prev := by {
      by_contra h0
      have hn1_zero : vanEckNthTerm 1 = 0 := rfl
      exact no_zero_after_lastZero (n - 1) 1 (by { omega }) (by { omega }) hn1_zero
    }
    have hz_prev_lt : z_prev < n := by {
      have hle_z := lastZero_le (n - 1)
      omega
    }
    have h_gap_z : ∀ k, z_prev < k → k < n → vanEckNthTerm k ≠ 0 :=
      fun k hk1 hk2 => no_zero_after_lastZero (n - 1) k hk1 (by { omega })
    have h_dist := gap_between_zeros n z_prev hz (by { omega }) hz_prev_zero hz_prev_lt h_gap_z
    have h_ge3 := consecutive_zeros_gap_ge_three_of_ne_two n z_prev hz_prev_pos
      hz hz_prev_zero hz_prev_lt h_gap_z hn1_ne2
    omega
  · have hn1_ne0 : vanEckNthTerm (n + 1) ≠ 0 := by {
      intro hz_next
      have h_ne := pre_zero_ne_prior_val (n + 1) 2 hz_next (by { omega }) (by { omega })
      have ha2 : vanEckNthTerm 2 = 1 := rfl
      exact h_ne (by {
        change vanEckNthTerm n = vanEckNthTerm 2
        rw [h1, ha2]
      })
    }
    have hn1_ne1 : vanEckNthTerm (n + 1) ≠ 1 := by {
      intro h1_next
      exact vanEck_no_consecutive_ones n ⟨h1, h1_next⟩
    }
    omega
}

lemma no_twos_pair_small_card_le_one (N_0 m : ℕ)
    (h_no_twos : ∀ k > N_0, vanEckNthTerm k ≠ 2) (hm : max N_0 3 < m) :
    (({m, m + 1} : Finset ℕ).filter (fun n => vanEckNthTerm n ≤ 1)).card ≤ 1 := by {
  by_cases h1 : vanEckNthTerm m ≤ 1
  · have h_ge3 := no_twos_zero_or_one_next_ge_three N_0 m h_no_twos hm h1
    have h_sub : ({m, m + 1} : Finset ℕ).filter (fun n => vanEckNthTerm n ≤ 1) ⊆ {m} := by {
      intro x hx
      have hxf := Finset.mem_filter.mp hx
      rcases Finset.mem_insert.mp hxf.1 with rfl | hx2
      · exact Finset.mem_singleton_self _
      · rw [Finset.mem_singleton.mp hx2] at hxf
        omega
    }
    exact le_trans (Finset.card_le_card h_sub) (by { simp })
  · have h_sub : ({m, m + 1} : Finset ℕ).filter (fun n => vanEckNthTerm n ≤ 1) ⊆ {m + 1} := by {
      intro x hx
      have hxf := Finset.mem_filter.mp hx
      rcases Finset.mem_insert.mp hxf.1 with rfl | hx2
      · exact False.elim (h1 hxf.2)
      · exact hx2
    }
    exact le_trans (Finset.card_le_card h_sub) (by { simp })
}

/-- Non-adjacency of `{0, 1}` in a `2`-free tail forces at most `(L + 1) / 2` occurrences of
values `≤ 1` in any post-cut window `[a + 1, a + L]` (`a ≥ max N_0 3`). -/
theorem no_twos_small_terms_half_window_bound (N_0 a L : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2) (ha : max N_0 3 ≤ a) :
    2 * ((Finset.Icc (a + 1) (a + L)).filter (fun n => vanEckNthTerm n ≤ 1)).card ≤ L + 1 := by {
  induction L using Nat.strong_induction_on with
  | h L ih =>
    match L with
    | 0 =>
      have h_emp : Finset.Icc (a + 1) (a + 0) = ∅ := by { simp }
      rw [h_emp]
      simp
    | 1 =>
      rw [Finset.Icc_self]
      have hc : (({a + 1} : Finset ℕ).filter (fun n => vanEckNthTerm n ≤ 1)).card ≤
          ({a + 1} : Finset ℕ).card := Finset.card_filter_le _ _
      simp only [Finset.card_singleton] at hc
      omega
    | L' + 2 =>
      let S := (Finset.Icc (a + 1) (a + (L' + 2))).filter (fun n => vanEckNthTerm n ≤ 1)
      let S0 := (Finset.Icc (a + 1) (a + L')).filter (fun n => vanEckNthTerm n ≤ 1)
      let Tail := ({a + L' + 1, a + L' + 2} : Finset ℕ).filter (fun n => vanEckNthTerm n ≤ 1)
      have h_union : S ⊆ S0 ∪ Tail := by {
        intro x hx
        have hxf := Finset.mem_filter.mp hx
        have hxi := Finset.mem_Icc.mp hxf.1
        by_cases hle_L : x ≤ a + L'
        · exact Finset.mem_union_left _ (Finset.mem_filter.mpr
            ⟨Finset.mem_Icc.mpr ⟨hxi.1, hle_L⟩, hxf.2⟩)
        · refine Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨?_, hxf.2⟩)
          simp only [Finset.mem_insert, Finset.mem_singleton]
          omega
      }
      have hTail_le : Tail.card ≤ 1 := by {
        have hm := no_twos_pair_small_card_le_one N_0 (a + L' + 1) h_no_twos (by { omega })
        have h_eq : a + L' + 1 + 1 = a + L' + 2 := by { omega }
        rw [h_eq] at hm
        exact hm
      }
      have h_card_le := le_trans (Finset.card_le_card h_union) (Finset.card_union_le S0 Tail)
      have h_ih := ih L' (by { omega })
      change 2 * S.card ≤ L' + 2 + 1
      change 2 * S0.card ≤ L' + 1 at h_ih
      omega
}

lemma no_twos_icc_card_cover (N_0 N : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2) :
    N ≤ (posZeroIndices N).card + (gapFiber N 1).card + N_0 +
      ((Finset.Icc 1 N).filter (fun n => 3 ≤ vanEckNthTerm n)).card := by {
  let S3 := (Finset.Icc 1 N).filter (fun n => 3 ≤ vanEckNthTerm n)
  have h_cover : Finset.Icc 1 N ⊆
      posZeroIndices N ∪ gapFiber N 1 ∪ Finset.Icc 1 N_0 ∪ S3 := by {
    intro n hn
    have h_icc := Finset.mem_Icc.mp hn
    by_cases h0 : vanEckNthTerm n = 0
    · exact Finset.mem_union_left _ (Finset.mem_union_left _
        (Finset.mem_union_left _ (Finset.mem_filter.mpr ⟨hn, h0⟩)))
    · by_cases h1 : vanEckNthTerm n = 1
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn, h1⟩)))
      · by_cases h2 : vanEckNthTerm n = 2
        · have hn_le : n ≤ N_0 := by {
            by_contra hgt
            exact h_no_twos n (by { omega }) h2
          }
          exact Finset.mem_union_left _ (Finset.mem_union_right _
            (Finset.mem_Icc.mpr ⟨h_icc.1, hn_le⟩))
        · exact Finset.mem_union_right _ (Finset.mem_filter.mpr ⟨hn, by { omega }⟩)
  }
  have hc := Finset.card_le_card h_cover
  have hu1 := Finset.card_union_le (posZeroIndices N ∪ gapFiber N 1 ∪ Finset.Icc 1 N_0) S3
  have hu2 := Finset.card_union_le (posZeroIndices N ∪ gapFiber N 1) (Finset.Icc 1 N_0)
  have hu3 := Finset.card_union_le (posZeroIndices N) (gapFiber N 1)
  have hcN : (Finset.Icc 1 N).card = N := by { simp }
  have hcN0 : (Finset.Icc 1 N_0).card = N_0 := by { simp }
  change N ≤ (posZeroIndices N).card + (gapFiber N 1).card + N_0 + S3.card
  omega
}

/-- Combined Return-Forest Sum Squeeze: under `∀ m > N_0, a(m) ≠ 2`, every index in `[1, N]`
outside `posZeroIndices N`, `gapFiber N 1`, and `[1, N_0]` carries a link of length `≥ 3`,
sandwiching `∑_{n=1}^N a(n)` against the chain-span bound `Z * (N - Z)`. -/
theorem no_twos_return_forest_sum_squeeze (N_0 N : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2) :
    (gapFiber N 1).card +
        3 * (N - (posZeroIndices N).card - (gapFiber N 1).card - N_0) ≤
      (posZeroIndices N).card * (N - (posZeroIndices N).card) := by {
  let S3 := (Finset.Icc 1 N).filter (fun n => 3 ≤ vanEckNthTerm n)
  have h_card_cov := no_twos_icc_card_cover N_0 N h_no_twos
  have h_disj : Disjoint (gapFiber N 1) S3 := by {
    refine Finset.disjoint_left.mpr (fun n hn1 hn3 => ?_)
    have hv1 := (Finset.mem_filter.mp hn1).2
    have hv3 := (Finset.mem_filter.mp hn3).2
    omega
  }
  have h_sub : gapFiber N 1 ∪ S3 ⊆ Finset.Icc 1 N :=
    Finset.union_subset (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  have h_sum_low : (gapFiber N 1).card + 3 * S3.card ≤
      ∑ n ∈ Finset.Icc 1 N, vanEckNthTerm n := by {
    have h1 : (gapFiber N 1).card = ∑ n ∈ gapFiber N 1, vanEckNthTerm n := by {
      have hc : ∑ n ∈ gapFiber N 1, vanEckNthTerm n = ∑ _n ∈ gapFiber N 1, 1 :=
        Finset.sum_congr rfl (fun n hn => (Finset.mem_filter.mp hn).2)
      rw [hc, Finset.sum_const, smul_eq_mul, mul_one]
    }
    have h3 : 3 * S3.card ≤ ∑ n ∈ S3, vanEckNthTerm n := by {
      have hc : 3 * S3.card = ∑ _n ∈ S3, 3 := by {
        rw [Finset.sum_const, smul_eq_mul, mul_comm]
      }
      rw [hc]
      exact Finset.sum_le_sum (fun n hn => (Finset.mem_filter.mp hn).2)
    }
    calc (gapFiber N 1).card + 3 * S3.card
      _ ≤ ∑ n ∈ gapFiber N 1, vanEckNthTerm n + ∑ n ∈ S3, vanEckNthTerm n :=
        add_le_add (le_of_eq h1) h3
      _ = ∑ n ∈ gapFiber N 1 ∪ S3, vanEckNthTerm n := (Finset.sum_union h_disj).symm
      _ ≤ ∑ n ∈ Finset.Icc 1 N, vanEckNthTerm n :=
        Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun _ _ _ => Nat.zero_le _)
  }
  have h_up := sum_vanEck_le_zeros_mul_complement N
  have hS3_ge : N - (posZeroIndices N).card - (gapFiber N 1).card - N_0 ≤ S3.card := by {
    change N ≤ (posZeroIndices N).card + (gapFiber N 1).card + N_0 + S3.card at h_card_cov
    omega
  }
  have h_mul : 3 * (N - (posZeroIndices N).card - (gapFiber N 1).card - N_0) ≤ 3 * S3.card :=
    Nat.mul_le_mul_left 3 hS3_ge
  exact le_trans (Nat.add_le_add_left h_mul _) (le_trans h_sum_low h_up)
}

/--
Infinite Twos Lemma


To prove: The number 2 appears infinitely many times in the Van Eck sequence.
-/
theorem infinite_twos_vanEck (N : ℕ) : ∃ m > N, vanEckNthTerm m = 2 := by {
  by_contra h_no_twos
  push Not at h_no_twos
  have h_bound := no_twos_implies_bounded N h_no_twos
  rcases h_bound with ⟨M, hM_pos, hM_bound⟩
  have h_dense := sequence_bounded_implies_dense M hM_bound
  have h_twos := dense_collisions_force_twos M hM_pos h_dense
  have h_contra := h_twos N
  rcases h_contra with ⟨m, hm_gt, hm_eq⟩
  exact h_no_twos m hm_gt hm_eq
}
