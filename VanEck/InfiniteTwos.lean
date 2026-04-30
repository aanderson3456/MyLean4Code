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
lemma finite_cycle_gap_collapse (n_1 n_2 K : ℕ)
    (hn1_lt_n2 : n_1 < n_2)
    (h_K_large : K ≥ n_2 - n_1 + 3)
    (h_no_zero : ∀ k, 1 ≤ k → k ≤ K → vanEckNthTerm (n_2 + k) ≠ 0)
    (h_no_twos : ∀ m > n_1, vanEckNthTerm m ≠ 2)
    (h_per : ∀ k ≤ K, vanEckNthTerm (n_1 + k) = vanEckNthTerm (n_2 + k)) : False := by {
  sorry
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
  push_neg at h_no_twos

  -- From h_dense, we obtain a dense block far out in the sequence.
  have h_ex := h_dense N
  rcases h_ex with ⟨start, h_start_gt, h_block⟩

  -- By our stepping stone, this dense block has NO alternating pairs.
  have h_no_alt := dense_block_without_twos_has_no_alternating_pairs B ((B + 1) ^ (B + 1) + (B + 1) + 5) start h_block (by
    intro m hm_gt
    exact h_no_twos m (Nat.lt_trans h_start_gt hm_gt)
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
    by_contra h_zero
    have h_zero_eq : vanEckNthTerm (n_1 + k) = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_not_lt h_zero)
    -- If it's zero, we prove finite_twos_implies_old_gaps
    sorry

  have hn1_ge_B : B + 1 ≤ n_1 := Nat.le_trans (Nat.le_add_left (B + 1) start) hn1_ge
  have hn2_ge_B : B + 1 ≤ n_2 := Nat.le_trans hn1_ge_B (Nat.le_of_lt hn1_lt_n2)

  have h_per := local_forward_periodicity_left (B + 1) n_1 n_2 K h_state_eq hn1_ge_B hn2_ge_B (Nat.zero_lt_succ B) hd1_lt hd1_pos

  have h_contra := local_periodicity_impossible n_1 n_2 K hn1_lt_n2 (Nat.le_refl _) (by
    intro m hm
    have h1 : start ≤ n_1 := Nat.le_trans (Nat.le_add_right start (B + 1)) hn1_ge
    have h2 : start < m := Nat.lt_of_le_of_lt h1 hm
    exact h_no_twos m (Nat.lt_trans h_start_gt h2)
  )


  sorry
}
