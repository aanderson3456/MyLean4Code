import VanEck
import ImpossiblePatterns
import LimSup
import FinishedSurjLemmas
import Mathlib

lemma new_value_next_is_zero (m : ℕ) (h_new : ∀ i < m, vanEckNthTerm i ≠ vanEckNthTerm m) :
    vanEckNthTerm (m + 1) = 0 := by {
  by_cases hm : m = 0
  · subst hm
    rfl
  · have h_iff := (vanEck_mth_term_eq_zero_iff_prev_term_new (m - 1)).mpr
    have hm_sub : m - 1 + 1 = m := by omega
    have hm_add : m - 1 + 2 = m + 1 := by omega
    rw [hm_sub, hm_add] at h_iff
    exact h_iff h_new
}

lemma pos_value_implies_gap (m n : ℕ) (hm : m ≥ 2) (h_val : vanEckNthTerm m = n) (h_pos : n > 0) :
    m > n ∧ vanEckNthTerm (m - 1 - n) = vanEckNthTerm (m - 1) := by {
  have h_le : vanEckNthTerm m ≤ m - 1 := a_le_idx_minus_one hm (by rw [h_val]; exact h_pos)
  rw [h_val] at h_le
  have h_m_gt_n : m > n := by omega

  have hm_sub : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.le_trans (by decide) hm)
  have h_match : vanEckNthTerm (m - 1 + 1) = matchSearch (vanEck (m - 1)) (m - 1) := by {
    rw [hm_sub]
    exact vanEck_term_is_matchSearch m (Nat.le_trans (by decide) hm)
  }
  rw [hm_sub] at h_match
  have h_match_eq : matchSearch (vanEck (m - 1)) (m - 1) = n := by
    rw [← h_match]
    exact h_val
  have h_neq : matchSearch (vanEck (m - 1)) (m - 1) ≠ 0 := by
    rw [h_match_eq]
    exact Nat.ne_of_gt h_pos
  have hm_match := matchSearch_matches (vanEck (m - 1)) (m - 1)
  have h_eval := hm_match h_neq
  have h_len : (vanEck (m - 1)).length = m := by
    have h1 := vanEckLength (m - 1)
    rw [hm_sub] at h1
    exact h1
  have h_len_sub_1 : (vanEck (m - 1)).length - 1 = m - 1 := by rw [h_len]
  rw [h_len_sub_1] at h_eval
  rw [h_match_eq] at h_eval

  have hd1 : listNth (vanEck (m - 1)) (m - 1) = vanEckNthTerm (m - 1) := by
    exact VanEck_deterministic (m - 1) (m - 1) (Nat.le_refl _)

  have hd0 : listNth (vanEck (m - 1)) (m - 1 - n) = vanEckNthTerm (m - 1 - n) := by
    have h_le_n : m - 1 - n ≤ m - 1 := Nat.sub_le _ _
    exact VanEck_deterministic (m - 1) (m - 1 - n) h_le_n

  rw [hd1, hd0] at h_eval

  exact ⟨h_m_gt_n, h_eval.symm⟩
}

/-!
# Surjectivity Open Problem - Progressive Conjectures

The following 5 theorems represent increasing levels of difficulty towards proving the
full surjectivity of the Van Eck sequence (that it contains every natural number).
-/


/--
If an element `x` only appears finitely many times in the Van Eck sequence,
there must exist some maximum index `Z` such that for all `k > Z`, `vanEckNthTerm k ≠ x`.
-/
lemma finite_occurrences_implies_last_index (x : ℕ) (h_finite : ∃ Z, ∀ k > Z, vanEckNthTerm k ≠ x) :
    ∃ Z, vanEckNthTerm Z = x ∧ ∀ k > Z, vanEckNthTerm k ≠ x := by {
  sorry
}

/--
If an element `x` never appears after index `Z`, then no element after `Z+1` can have its previous occurrence exactly `x` steps ago.
-/
lemma never_appears_again_implies_no_gap_x (x Z : ℕ) (hx : ∀ k > Z, vanEckNthTerm k ≠ x) :
    ∀ k > Z + 1, listNth (vanEck (k - 1)) (k - 1) ≠ listNth (vanEck (k - 1)) (k - 1 - x) := by {
  sorry
}

/--
If two consecutive gaps between zeros are identical, the sequence deterministically produces a 1.
This provides the mathematical bridge linking zero gap patterns to occurrences of 1.
-/
lemma vanEck_consecutive_gaps_imply_one (Z1 Z2 d : ℕ)
  (hZ1 : vanEckNthTerm Z1 = 0)
  (hZ2 : vanEckNthTerm Z2 = 0)
  (hd : d = Z2 - Z1)
  (hd_pos : d > 0)
  (hZ1_lt : Z1 < Z2)
  (haZ1 : vanEckNthTerm (Z1 + 1) = d)
  (haZ2 : vanEckNthTerm (Z2 + 1) = d)
  (h_no_d : ∀ k, Z1 + 1 < k → k < Z2 + 1 → vanEckNthTerm k ≠ d) :
  vanEckNthTerm (Z2 + 3) = 1 := by {
  have hZ2_pos : Z2 ≥ 1 := by omega

  let L := vanEck (Z2 + 1)
  have h_len : L.length = Z2 + 2 := by
    have hl := vanEckLength (Z2 + 1)
    have hz : Z2 + 1 + 1 = Z2 + 2 := rfl
    rw [hz] at hl
    exact hl

  have ha2 : vanEckNthTerm (Z2 + 2) = matchSearch L (Z2 + 1) := by
    have h1 : Z2 + 2 = Z2 + 1 + 1 := rfl
    rw [h1]
    exact vanEck_term_is_matchSearch (Z2 + 2) (by omega)

  have hd_last : listNth L (L.length - 1) = d := by
    have hl : L.length - 1 = Z2 + 1 := by rw [h_len]; rfl
    rw [hl]
    have h_det := VanEck_deterministic (Z2 + 1) (Z2 + 1) (Nat.le_refl _)
    rw [h_det]
    exact haZ2

  have hd_start : listNth L (Z1 + 1) = d := by
    have h_le : Z1 + 1 ≤ Z2 + 1 := Nat.add_le_add_right (Nat.le_of_lt hZ1_lt) 1
    have h_det := VanEck_deterministic (Z2 + 1) (Z1 + 1) h_le
    rw [h_det]
    exact haZ1

  have h_match : listNth L (L.length - 1) = listNth L (Z1 + 1) := by
    rw [hd_last, hd_start]

  have h_fail : ∀ k, 1 ≤ k → k ≤ d - 1 → listNth L (L.length - 1) ≠ listNth L (Z1 + 1 + k) := by {
    intro k hk1 hkd
    rw [hd_last]
    have h_idx_le : Z1 + 1 + k ≤ Z2 + 1 := by omega
    have h_det := VanEck_deterministic (Z2 + 1) (Z1 + 1 + k) h_idx_le
    rw [h_det]
    intro heq
    have h_symm : vanEckNthTerm (Z1 + 1 + k) = d := heq.symm

    have h_gt : Z1 + 1 < Z1 + 1 + k := by omega
    have h_lt : Z1 + 1 + k < Z2 + 1 := by omega
    exact h_no_d (Z1 + 1 + k) h_gt h_lt h_symm
  }

  have h_ms := matchSearch_eq_dist L (Z1 + 1) (d - 1) h_match h_fail

  have h_arg : Z1 + 1 + (d - 1) + 1 = Z2 + 1 := by omega
  rw [h_arg] at h_ms

  have h_val : L.length - 1 - (Z1 + 1) = d := by omega
  rw [h_val] at h_ms

  have h_a_eq : vanEckNthTerm (Z2 + 2) = d := by
    rw [ha2, h_ms]

  have h_cons : vanEckNthTerm (Z2 + 1) = vanEckNthTerm (Z2 + 2) := by
    rw [haZ2, h_a_eq]

  have h_final := vanEck_consecutive_eq_implies_next_one (Z2 + 1) h_cons
  exact h_final
}

/--
The gaps between consecutive zeros in the Van Eck sequence must be unbounded.
If the gaps were bounded, some gap size `d` would appear infinitely often.
The distance between occurrences of `d` would form the elements immediately preceding the zeros.
Since the gaps are bounded, these distances would be bounded, and therefore repeat.
However, the element immediately preceding a zero MUST be a new, never-before-seen number.
This contradiction proves the zero-gaps are unbounded.
-/
lemma vanEck_zero_gaps_unbounded (B : ℕ) :
    ∃ Z1 Z2, vanEckNthTerm Z1 = 0 ∧ vanEckNthTerm Z2 = 0 ∧ Z1 < Z2 ∧
    (∀ k, Z1 < k → k < Z2 → vanEckNthTerm k ≠ 0) ∧ Z2 - Z1 > B := by {
  sorry
}

/--
A "strict" gap of exactly n exists if two identical terms are separated by exactly n indices,
and the value does not appear anywhere inside the gap.
-/
def has_strict_gap (n : ℕ) : Prop :=
  ∃ m, vanEckNthTerm m = vanEckNthTerm (m + n) ∧
       ∀ k, m < k → k < m + n → vanEckNthTerm k ≠ vanEckNthTerm m

/--
If a strict gap of exactly n exists, then the term immediately following the second occurrence will be precisely n.
This mathematically bridges the gap structure directly to the sequence's output values.
-/
lemma strict_gap_implies_value (n : ℕ) (hn : n > 0) (h : has_strict_gap n) :
  ∃ k, vanEckNthTerm k = n := by {
  rcases h with ⟨m, h_eq, h_strict⟩
  use m + n + 1
  have h_pos : m + n + 1 ≥ 2 := by omega

  have ha := vanEck_term_is_matchSearch (m + n + 1) (Nat.lt_of_succ_lt h_pos)
  have h_len : (vanEck (m + n)).length = m + n + 1 := by
    have hl := vanEckLength (m + n)
    have hz : m + n + 1 = m + n + 1 := rfl
    exact hl

  let L := vanEck (m + n)
  have h_match : listNth L (L.length - 1) = listNth L m := by
    have h1 : L.length - 1 = m + n := by rw [h_len]; rfl
    rw [h1]
    have hd1 := VanEck_deterministic (m + n) (m + n) (Nat.le_refl _)
    have hd2 := VanEck_deterministic (m + n) m (Nat.le_add_right m n)
    rw [hd1, hd2]
    exact h_eq.symm

  have h_fail : ∀ k, 1 ≤ k → k ≤ n - 1 → listNth L (L.length - 1) ≠ listNth L (m + k) := by
    intro k hk1 hkn
    have h1 : L.length - 1 = m + n := by rw [h_len]; rfl
    rw [h1]
    have h_idx_le : m + k ≤ m + n := by
      have h2 : m + k ≤ m + (n - 1) := Nat.add_le_add_left hkn m
      have h3 : m + (n - 1) = m + n - 1 := by
        have h_ge : n ≥ 1 := hn
        exact (Nat.add_sub_assoc h_ge m).symm
      rw [h3] at h2
      have h4 : m + n - 1 ≤ m + n := Nat.sub_le _ _
      exact Nat.le_trans h2 h4

    have hd1 := VanEck_deterministic (m + n) (m + n) (Nat.le_refl _)
    have hd2 := VanEck_deterministic (m + n) (m + k) h_idx_le
    rw [hd1, hd2]
    intro heq
    have heq_symm : vanEckNthTerm (m + k) = vanEckNthTerm (m + n) := heq.symm
    have h_eq_val : vanEckNthTerm (m + k) = vanEckNthTerm m := by
      rw [heq_symm]
      exact h_eq.symm

    have h_gt : m < m + k := Nat.lt_add_of_pos_right hk1
    have h_lt : m + k < m + n := by
      have h2 : m + k ≤ m + (n - 1) := Nat.add_le_add_left hkn m
      have h3 : m + (n - 1) = m + n - 1 := by
        have h_ge : n ≥ 1 := hn
        exact (Nat.add_sub_assoc h_ge m).symm
      rw [h3] at h2
      have h4 : m + n - 1 < m + n := Nat.sub_lt (Nat.add_pos_right m hn) (by decide)
      exact Nat.lt_of_le_of_lt h2 h4
    exact h_strict (m + k) h_gt h_lt h_eq_val

  have h_ms := matchSearch_eq_dist L m (n - 1) h_match h_fail

  have h_arg : m + (n - 1) + 1 = m + n := by
    have h1 : m + (n - 1) + 1 = m + (n - 1 + 1) := by rw [← Nat.add_assoc]
    have h2 : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [h1, h2]

  rw [h_arg] at h_ms

  have h_val : L.length - 1 - m = n := by
    rw [h_len]
    have h1 : m + n + 1 - 1 = m + n := rfl
    rw [h1]
    exact Nat.add_sub_cancel_left m n

  rw [h_val] at h_ms
  have h_ha : vanEckNthTerm (m + n + 1) = matchSearch L (m + n) := by
    have h_idx : m + n + 1 - 1 = m + n := rfl
    rw [h_idx] at ha
    exact ha
  rw [h_ha]
  exact h_ms
}

/--
If 1 only appears finitely many times, there is a point after which no two consecutive elements are equal.
-/
lemma finite_ones_implies_no_consecutive_equal (h_finite : ∃ Z, ∀ k > Z, vanEckNthTerm k ≠ 1) :
    ∃ Z, ∀ k > Z, vanEckNthTerm k ≠ vanEckNthTerm (k + 1) := by {
  rcases h_finite with ⟨Z, hZ⟩
  use Z
  intro k hk
  intro heq
  have h_next := vanEck_consecutive_eq_implies_next_one k heq
  have hk_add : k + 2 > Z := Nat.lt_trans hk (Nat.lt_add_of_pos_right (by decide))
  have h_not_one := hZ (k + 2) hk_add
  exact h_not_one h_next
}

/--
Level 3 Conjecture (Hard): Every value that appears in the sequence appears infinitely many times.
We know 0 appears infinitely often, but it is an open question whether an arbitrary
value like 1 or 2 appears infinitely often.
-/
theorem vanEck_all_seen_appear_infinitely (n : ℕ) : (∃ m, vanEckNthTerm m = n) → ∀ N, ∃ k > N, vanEckNthTerm k = n := by {
  sorry
}

/--
Level 4 Conjecture (Very Hard): For any natural number n, there exist two identical terms separated by exactly n indices.
This is a necessary precursor to surjectivity, stating that every possible gap length exists.
-/
theorem vanEck_any_gap_exists (n : ℕ) : ∃ m : ℕ, vanEckNthTerm m = vanEckNthTerm (m + n) := by {
  sorry
}

/-
Level 5 Conjecture (Equivalent to Surjectivity): For any positive n, there exists a "strict" gap of exactly n indices between identical values, meaning the value does not appear anywhere inside the gap.
If this holds, the term immediately following the second occurrence will be precisely `n`. This is mathematically equivalent to the conjecture that the sequence takes on every natural number.
-/
/--
Theorem: For all n, there exists m such that vanEckNthTerm m = n.
This is the open problem: Does every number appear in the Van Eck sequence?
-/
theorem vanEck_surjective (n : ℕ) : ∃ m : ℕ, vanEckNthTerm m = n := by {
  sorry
}

-- ============================================================================
-- MISSING NUMBER DENSITY CONSTRAINTS
-- ============================================================================

lemma missing_number_implies_no_gap (s : ℕ) (h_pos : s > 0)
  (h_missing : ∀ k, vanEckNthTerm k ≠ s) :
  ∀ m, vanEckNthTerm m ≠ vanEckNthTerm (m + s) ∨
  ∃ k, m < k ∧ k < m + s ∧ vanEckNthTerm k = vanEckNthTerm m := by {
  intro m
  by_contra hc
  push Not at hc
  have h_eq : vanEckNthTerm m = vanEckNthTerm (m + s) := hc.1
  have h_strict : ∀ k, m < k → k < m + s → vanEckNthTerm k ≠ vanEckNthTerm m := hc.2

  have h_gap : has_strict_gap s := ⟨m, h_eq, h_strict⟩

  have h_val := strict_gap_implies_value s h_pos h_gap
  rcases h_val with ⟨k, hk⟩
  exact h_missing k hk
}

lemma exists_strict_gap_of_eq (m s : ℕ) (h_pos : s > 0) (h_eq : vanEckNthTerm m = vanEckNthTerm (m + s)) :
  ∃ d, 0 < d ∧ d ≤ s ∧ vanEckNthTerm m = vanEckNthTerm (m + d) ∧
  ∀ k, m < k → k < m + d → vanEckNthTerm k ≠ vanEckNthTerm m := by {
  have h_ex : ∃ d, 0 < d ∧ vanEckNthTerm m = vanEckNthTerm (m + d) := ⟨s, h_pos, h_eq⟩
  let d := Nat.find h_ex
  have hd_spec := Nat.find_spec h_ex
  have hd_pos : 0 < d := hd_spec.1
  have hd_eq : vanEckNthTerm m = vanEckNthTerm (m + d) := hd_spec.2
  have hd_le : d ≤ s := Nat.find_le ⟨h_pos, h_eq⟩
  use d
  refine ⟨hd_pos, hd_le, hd_eq, ?_⟩
  intro k hm_lt hk_lt hc
  have hk_pos : 0 < k - m := by omega
  have hk_eq : m + (k - m) = k := by omega
  have h_lt : k - m < d := by omega
  have h_min := Nat.find_min h_ex h_lt
  apply h_min
  refine ⟨hk_pos, ?_⟩
  rw [hk_eq]
  exact hc.symm
}

/--
Missing Number Density Constraint:
If the numbers 1 through n never appear in the sequence,
then any contiguous block of n + 1 elements consists entirely of distinct values.
-/
lemma missing_numbers_imply_distinct_window (n : ℕ)
  (h_missing : ∀ k, ∀ s, 1 ≤ s → s ≤ n → vanEckNthTerm k ≠ s) :
  ∀ m : ℕ, ∀ i j, i ≤ n → j ≤ n → i < j → vanEckNthTerm (m + i) ≠ vanEckNthTerm (m + j) := by {
  intro m i j hi hj h_lt h_eq
  have h_s : j - i > 0 := Nat.sub_pos_of_lt h_lt
  have h_s_le : j - i ≤ n := by
    calc j - i ≤ j := Nat.sub_le j i
         _ ≤ n := hj

  have h_idx : m + j = m + i + (j - i) := by
    rw [Nat.add_assoc]
    have h_sub : i + (j - i) = j := Nat.add_sub_cancel' (Nat.le_of_lt h_lt)
    rw [h_sub]

  have h_eq2 : vanEckNthTerm (m + i) = vanEckNthTerm (m + i + (j - i)) := by
    rw [← h_idx]
    exact h_eq

  have h_strict_ex := exists_strict_gap_of_eq (m + i) (j - i) h_s h_eq2
  rcases h_strict_ex with ⟨d, hd_pos, hd_le, hd_eq, hd_strict⟩

  have h_d_le_n : d ≤ n := Nat.le_trans hd_le h_s_le

  have h_no_gap := missing_number_implies_no_gap d hd_pos (h_missing · d hd_pos h_d_le_n) (m + i)
  cases h_no_gap with
  | inl h_not => exact h_not hd_eq
  | inr h_ex =>
    rcases h_ex with ⟨k, h_k_gt, h_k_lt, h_k_eq⟩
    exact hd_strict k h_k_gt h_k_lt h_k_eq
}

lemma pigeonhole_n_plus_one (n : ℕ) (f : Fin (n + 1) → Fin n) : ∃ i j, i ≠ j ∧ f i = f j := by {
  have h_card : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by
    simp
  exact Fintype.exists_ne_map_eq_of_card_lt f h_card
}

lemma bounded_distinct_elements (n : ℕ) (hn : n > 0)
  (a : Fin (n + 1) → ℕ)
  (h_dist : ∀ i j, i ≠ j → a i ≠ a j)
  (h_excl : ∀ i, a i = 0 ∨ a i > n) :
  ∃ i, a i ≥ 2 * n := by {
  by_contra hc
  push Not at hc

  let g : Fin (n + 1) → Fin n := fun i =>
    let x := a i
    if hx : x = 0 then
      ⟨0, hn⟩
    else
      have h_gt : x > n := by
        cases (h_excl i) with
        | inl h0 => exact False.elim (hx h0)
        | inr hgt => exact hgt
      have h_lt : x < 2 * n := hc i
      have h_lt2 : x < n + n := by
        have h_two : 2 * n = n + n := Nat.two_mul n
        rw [h_two] at h_lt
        exact h_lt
      have h_sub : x - n < n := by
        exact Nat.sub_lt_left_of_lt_add (Nat.le_of_lt h_gt) h_lt2
      ⟨x - n, h_sub⟩

  have h_pig := pigeonhole_n_plus_one n g
  rcases h_pig with ⟨i, j, h_neq, h_geq⟩

  have h_eq : a i = a j := by
    dsimp [g] at h_geq
    split at h_geq
    · rename_i hx_i
      split at h_geq
      · rename_i hx_j
        rw [hx_i, hx_j]
      · rename_i hx_j
        have h_val : 0 = a j - n := Fin.ext_iff.mp h_geq
        have h_gt_j : a j > n := by
          cases (h_excl j) with
          | inl h0 => exact False.elim (hx_j h0)
          | inr hgt => exact hgt
        have h_sub_pos : a j - n > 0 := Nat.sub_pos_of_lt h_gt_j
        rw [← h_val] at h_sub_pos
        exact False.elim (Nat.lt_irrefl 0 h_sub_pos)
    · rename_i hx_i
      split at h_geq
      · rename_i hx_j
        have h_val : a i - n = 0 := Fin.ext_iff.mp h_geq
        have h_gt_i : a i > n := by
          cases (h_excl i) with
          | inl h0 => exact False.elim (hx_i h0)
          | inr hgt => exact hgt
        have h_sub_pos : a i - n > 0 := Nat.sub_pos_of_lt h_gt_i
        rw [h_val] at h_sub_pos
        exact False.elim (Nat.lt_irrefl 0 h_sub_pos)
      · rename_i hx_j
        have h_val : a i - n = a j - n := Fin.ext_iff.mp h_geq
        have h_gt_i : a i > n := by
          cases (h_excl i) with
          | inl h0 => exact False.elim (hx_i h0)
          | inr hgt => exact hgt
        have h_gt_j : a j > n := by
          cases (h_excl j) with
          | inl h0 => exact False.elim (hx_j h0)
          | inr hgt => exact hgt
        have h_add : a i - n + n = a j - n + n := by rw [h_val]
        rw [Nat.sub_add_cancel (Nat.le_of_lt h_gt_i)] at h_add
        rw [Nat.sub_add_cancel (Nat.le_of_lt h_gt_j)] at h_add
        exact h_add

  exact h_dist i j h_neq h_eq
}

/--
Bounding the Gap Growth based on Missing Numbers:
If the numbers 1 through n never appear, then in any window of n + 1 elements,
all elements are distinct and cannot be 1..n.
This forces the maximum value in any window of length n + 1 to be at least 2n.
This establishes a strict linear lower bound on the local values based on missing elements.
-/
lemma missing_numbers_force_local_growth (n : ℕ) (hn : n > 0)
  (h_missing : ∀ k, ∀ s, 1 ≤ s → s ≤ n → vanEckNthTerm k ≠ s) :
  ∀ m : ℕ, ∃ k, m ≤ k ∧ k ≤ m + n ∧ vanEckNthTerm k ≥ 2 * n := by {
  intro m
  let a : Fin (n + 1) → ℕ := fun i => vanEckNthTerm (m + i.val)

  have h_dist : ∀ i j : Fin (n + 1), i ≠ j → a i ≠ a j := by
    intro i j h_neq
    have hi_le : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    have hj_le : j.val ≤ n := Nat.le_of_lt_succ j.isLt
    have h_tri := Nat.lt_trichotomy i.val j.val
    cases h_tri with
    | inl h_lt =>
      exact missing_numbers_imply_distinct_window n h_missing m i.val j.val hi_le hj_le h_lt
    | inr h_eq_or_gt =>
      cases h_eq_or_gt with
      | inl h_eq =>
        have h_eq_fin : i = j := Fin.eq_of_val_eq h_eq
        exact False.elim (h_neq h_eq_fin)
      | inr h_gt =>
        have h_ne := missing_numbers_imply_distinct_window n h_missing m j.val i.val hj_le hi_le h_gt
        exact h_ne.symm

  have h_excl : ∀ i : Fin (n + 1), a i = 0 ∨ a i > n := by {
    intro i
    by_cases h0 : a i = 0
    · exact Or.inl h0
    · have h_pos : a i > 0 := Nat.pos_of_ne_zero h0
      by_cases h_le : a i ≤ n
      · have h_not := h_missing (m + i.val) (a i) h_pos h_le
        exact False.elim (h_not rfl)
      · exact Or.inr (Nat.lt_of_not_le h_le)
  }

  have h_bound := bounded_distinct_elements n hn a h_dist h_excl
  rcases h_bound with ⟨i, hi⟩
  use m + i.val
  exact ⟨by omega, by omega, hi⟩
}

lemma vanEck_le_index (k : ℕ) (hk : k > 0) : vanEckNthTerm k ≤ k := by {
  have ha := vanEck_term_is_matchSearch k hk
  have h_le := matchSearch_le (k - 1)
  have hk_sub : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [ha]
  rw [hk_sub] at h_le
  exact h_le
}

lemma missing_numbers_dense_large_gaps (n : ℕ) (hn : n > 0)
  (h_missing : ∀ k, ∀ s, 1 ≤ s → s ≤ n → vanEckNthTerm k ≠ s) :
  ∀ m : ℕ, ∃ k, m ≤ k ∧ k ≤ m + n ∧
  ∃ d, d ≥ 2 * n ∧ vanEckNthTerm k = d ∧
  k ≥ d + 1 ∧ vanEckNthTerm (k - 1) = vanEckNthTerm (k - 1 - d) := by {
  intro m
  have h_local := missing_numbers_force_local_growth n hn h_missing m
  rcases h_local with ⟨k, hk_ge, hk_le, hk_val⟩

  -- Since k >= m >= 0, we need to be careful if k = 0.
  -- But if k = 0, a(0) = 0. But a(k) >= 2n >= 2 > 0.
  -- So k > 0.
  have hk_pos : k > 0 := by
    by_contra h0
    push Not at h0
    have hz : k = 0 := Nat.eq_zero_of_le_zero h0
    rw [hz] at hk_val
    have ha0 : vanEckNthTerm 0 = 0 := rfl
    rw [ha0] at hk_val
    have hn_pos : 2 * n > 0 := Nat.mul_pos (by decide) hn
    exact False.elim (Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hn_pos hk_val))

  let d := vanEckNthTerm k
  use k
  refine ⟨hk_ge, hk_le, d, hk_val, rfl, ?_⟩

  have hd_pos : d > 0 := by
    have hn_pos : 2 * n > 0 := Nat.mul_pos (by decide) hn
    exact Nat.lt_of_lt_of_le hn_pos hk_val

  have hd_pos_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd_pos

  have h_gap := matchSearch_is_gap_distance k hk_pos d rfl hd_pos_ne

  have h_k_ge : k ≥ d + 1 := by {
    have h_bound := vanEck_le_index k hk_pos
    have hk_ge_2 : k ≥ 2 := by omega
    have hd_le : d ≤ k - 1 := a_le_idx_minus_one hk_ge_2 hd_pos
    omega
  }

  have hd1 : listNth (vanEck (k - 1)) (k - 1) = vanEckNthTerm (k - 1) :=
    VanEck_deterministic (k - 1) (k - 1) (Nat.le_refl _)
  have hd0 : listNth (vanEck (k - 1)) (k - 1 - d) = vanEckNthTerm (k - 1 - d) :=
    VanEck_deterministic (k - 1) (k - 1 - d) (by omega)
  rw [hd1, hd0] at h_gap

  exact ⟨h_k_ge, h_gap⟩
}

/--
The Monkey Bars Collapse (Rung 5 directly):
If the numbers 1 through n never appear, the very first window of length n + 1
must contain an element >= 2n. But the Van Eck sequence can never generate a
value greater than its own index! Thus, the local growth bound violently
collides with the absolute bounding envelope of the sequence on the very first window.
-/
lemma missing_numbers_pigeonhole_contradiction (n : ℕ) (hn : n > 0)
  (h_missing : ∀ k, ∀ s, 1 ≤ s → s ≤ n → vanEckNthTerm k ≠ s) : False := by {
  -- Get the local growth bound for the very first window (m = 0)
  have h_growth := missing_numbers_force_local_growth n hn h_missing 0
  rcases h_growth with ⟨k, hk_ge, hk_le, hk_val⟩

  -- Since k <= n, and vanEckNthTerm k <= k, we have vanEckNthTerm k <= n.
  -- We must be careful if k = 0.
  by_cases hk0 : k = 0
  · rw [hk0] at hk_val
    have ha0 : vanEckNthTerm 0 = 0 := rfl
    rw [ha0] at hk_val
    have hn_pos : 2 * n > 0 := Nat.mul_pos (by decide) hn
    exact False.elim (Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hn_pos hk_val))
  · have hk_pos : k > 0 := Nat.pos_of_ne_zero hk0
    have h_bound := vanEck_le_index k hk_pos
    have h_le_n : vanEckNthTerm k ≤ n := by
      have hk_le_n : k ≤ n := by
        have h_zero_add : 0 + n = n := Nat.zero_add n
        rw [← h_zero_add]
        exact hk_le
      exact Nat.le_trans h_bound hk_le_n

    -- Now we have 2n ≤ a(k) ≤ n.
    have h_contra : 2 * n ≤ n := Nat.le_trans hk_val h_le_n
    omega
}

-- ============================================================================
-- ZERO DOMINATION CONJECTURES & LEMMAS
-- ============================================================================

/--
The count of 0 in the prefix vanEck n is at least 2 for any n ≥ 1.
-/
lemma count_zero_ge_two (n : ℕ) (hn : n ≥ 1) : (vanEck n).count 0 ≥ 2 := by {
  induction n with
  | zero => exfalso; omega
  | succ n ih =>
    by_cases hn1 : n = 0
    · rw [hn1]
      decide
    · have hn_ge : n ≥ 1 := Nat.pos_of_ne_zero hn1
      have ih_res := ih hn_ge
      unfold vanEck
      rw [List.count_append]
      omega
}

/--
The count of 0 in any prefix of the VanEck sequence is strictly positive.
-/
lemma count_zero_pos (n : ℕ) : (vanEck n).count 0 > 0 := by {
  cases n with
  | zero =>
    decide
  | succ n =>
    have h_ge := count_zero_ge_two (n + 1) (by omega)
    omega
}

/--
Helper: The sum of counts of two distinct elements in any list is at most the list length.
-/
lemma count_add_count_le {α : Type*} [DecidableEq α] (x y : α) (hxy : x ≠ y) (L : List α) :
    L.count x + L.count y ≤ L.length := by {
  induction L with
  | nil => simp
  | cons a L' ih =>
    rw [List.count_cons, List.count_cons]
    split_ifs with h1 h2
    · have hax : a = x := beq_iff_eq.mp h1
      have hay : a = y := beq_iff_eq.mp h2
      subst hax hay
      exact False.elim (hxy rfl)
    · have h_len : (a :: L').length = L'.length + 1 := rfl
      rw [h_len]
      omega
    · have h_len : (a :: L').length = L'.length + 1 := rfl
      rw [h_len]
      omega
    · have h_len : (a :: L').length = L'.length + 1 := rfl
      rw [h_len]
      omega
}

/--
Helper: The count of x in L is strictly less than L's length if some other element y is in L.
-/
lemma count_lt_length_of_mem_ne {α : Type*} [DecidableEq α] (x y : α) (hxy : x ≠ y) (L : List α) (hy : y ∈ L) :
    L.count x < L.length := by {
  have h_le := count_add_count_le x y hxy L
  have h_pos : 1 ≤ L.count y := List.one_le_count_iff.mpr hy
  omega
}

/--
Weaker Conjecture: The frequency of any non-zero element x is strictly bounded
by the square of the frequency of 0.
-/
theorem count_lt_count_zero_sq (n x : ℕ) (hx : x > 0) (hn : n ≥ 2)
    (h_dom : (vanEck n).count x ≤ (vanEck n).count 0) :
    (vanEck n).count x < ((vanEck n).count 0) ^ 2 := by {
  have h_ge : 2 ≤ (vanEck n).count 0 := count_zero_ge_two n (by omega)
  have h_sq : (vanEck n).count 0 < ((vanEck n).count 0) ^ 2 := by {
    rw [pow_two]
    have h_mul : 2 * (vanEck n).count 0 ≤ (vanEck n).count 0 * (vanEck n).count 0 := by {
      apply Nat.mul_le_mul_right _ h_ge
    }
    omega
  }
  omega
}

/--
Helper: For any n ≥ 2, we have n + 1 < 2^n.
-/
lemma lt_pow_two_self (n : ℕ) (hn : n ≥ 2) : n + 1 < 2 ^ n := by {
  induction n with
  | zero => exfalso; omega
  | succ n ih =>
    by_cases hn2 : n ≥ 2
    · have ih_res := ih hn2
      have h_pow : 2 ^ (n + 1) = 2 ^ n + 2 ^ n := by {
        rw [pow_succ]
        ring
      }
      rw [h_pow]
      omega
    · have heq : n = 1 := by omega
      rw [heq]
      decide
}

/--
Weaker Conjecture: The frequency of any non-zero element x is strictly bounded
by the n-th power of the frequency of 0.
-/
theorem count_lt_count_zero_pow (n x : ℕ) (hx : x > 0) (hn : n ≥ 2) :
    (vanEck n).count x < ((vanEck n).count 0) ^ n := by {
  have h_len : (vanEck n).count x ≤ (vanEck n).length := List.count_le_length
  have h_len_eq := vanEckLength n
  rw [h_len_eq] at h_len
  have h_lt_pow := lt_pow_two_self n hn
  have h_ge : 2 ≤ (vanEck n).count 0 := count_zero_ge_two n (by omega)
  have h_pow_le : 2 ^ n ≤ ((vanEck n).count 0) ^ n := Nat.pow_le_pow_left h_ge n
  omega
}

/--
Special Case (General): The n-th power conjecture holds trivially for any element x
that has not yet appeared in the sequence.
-/
lemma count_lt_count_zero_pow_of_not_mem (n x : ℕ) (hx : x > 0) (hn : n ≥ 2) (h_not_mem : x ∉ vanEck n) :
    (vanEck n).count x < ((vanEck n).count 0) ^ n := by {
  have h_count_x : (vanEck n).count x = 0 := List.count_eq_zero.mpr h_not_mem
  rw [h_count_x]
  have h_pos : (vanEck n).count 0 > 0 := count_zero_pos n
  have h_pow_pos : ((vanEck n).count 0) ^ n > 0 := Nat.pow_pos h_pos
  exact h_pow_pos
}

/--
Helper: For any k, 2*k + 3 ≤ 2^(k+2).
-/
lemma linear_le_pow (k : ℕ) : 2 * k + 3 ≤ 2 ^ (k + 2) := by {
  induction k with
  | zero => decide
  | succ k ih =>
    have h_pow : 2 ^ (k + 3) = 2 ^ (k + 2) + 2 ^ (k + 2) := by {
      rw [pow_succ]
      ring
    }
    rw [h_pow]
    have h_ge : 2 ≤ 2 ^ (k + 2) := by {
      have h_pow_ge : 2 ^ 2 ≤ 2 ^ (k + 2) := Nat.pow_le_pow_right (by decide) (by omega)
      have h2 : 2 ^ 2 = 4 := rfl
      omega
    }
    omega
}

/--
Helper: For any k, (k+1)^2 ≤ 2^(k+2). We express k+1 as k.succ for convenience with Nat.sqrt.
-/
lemma succ_sq_le_pow_two_add_two (k : ℕ) : (k.succ) ^ 2 ≤ 2 ^ (k + 2) := by {
  induction k with
  | zero => decide
  | succ k ih =>
    have h_pow : 2 ^ (k + 3) = 2 ^ (k + 2) + 2 ^ (k + 2) := by {
      rw [pow_succ]
      ring
    }
    rw [h_pow]
    have h_sq1 : (k.succ.succ) ^ 2 = (k.succ) ^ 2 + 2 * k + 3 := by {
      repeat rw [Nat.succ_eq_add_one]
      ring
    }
    rw [h_sq1]
    have h_lin := linear_le_pow k
    omega
}

/--
Weaker Conjecture (Logarithmic): The frequency of any non-zero element x is strictly bounded
by the (log2(n) + 1)-th power of the frequency of 0. This is proven unconditionally.
-/
theorem count_lt_count_zero_pow_log (n x : ℕ) (hx : x > 0) (hn : n ≥ 2) :
    (vanEck n).count x < ((vanEck n).count 0) ^ (Nat.log2 n + 1) := by {
  have h_zero_mem : 0 ∈ vanEck n := by {
    have h_pos : 1 ≤ (vanEck n).count 0 := count_zero_pos n
    exact List.one_le_count_iff.mp h_pos
  }
  have h_ne : x ≠ 0 := Nat.ne_of_gt hx
  have h_lt_len := count_lt_length_of_mem_ne x 0 h_ne (vanEck n) h_zero_mem
  have h_len_eq := vanEckLength n
  rw [h_len_eq] at h_lt_len
  have h_lt_pow : n < 2 ^ (Nat.log2 n + 1) := Nat.lt_log2_self
  have h_cx_lt_pow2 : (vanEck n).count x < 2 ^ (Nat.log2 n + 1) := by omega
  have h_ge : 2 ≤ (vanEck n).count 0 := count_zero_ge_two n (by omega)
  have h_pow_le : 2 ^ (Nat.log2 n + 1) ≤ ((vanEck n).count 0) ^ (Nat.log2 n + 1) :=
    Nat.pow_le_pow_left h_ge (Nat.log2 n + 1)
  exact Nat.lt_of_lt_of_le h_cx_lt_pow2 h_pow_le
}

/--
Weaker Conjecture (Square Root): The frequency of any non-zero element x is strictly bounded
by the (sqrt(n) + 2)-th power of the frequency of 0. This is proven unconditionally.
-/
theorem count_lt_count_zero_pow_sqrt (n x : ℕ) (hx : x > 0) (hn : n ≥ 2) :
    (vanEck n).count x < ((vanEck n).count 0) ^ (Nat.sqrt n + 2) := by {
  have h_zero_mem : 0 ∈ vanEck n := by {
    have h_pos : 1 ≤ (vanEck n).count 0 := count_zero_pos n
    exact List.one_le_count_iff.mp h_pos
  }
  have h_ne : x ≠ 0 := Nat.ne_of_gt hx
  have h_lt_len := count_lt_length_of_mem_ne x 0 h_ne (vanEck n) h_zero_mem
  have h_len_eq := vanEckLength n
  rw [h_len_eq] at h_lt_len
  have h_lt_succ_sqrt := Nat.lt_succ_sqrt' n
  have h_succ_sqrt_le_pow := succ_sq_le_pow_two_add_two (Nat.sqrt n)
  have h_lt_pow : n < 2 ^ (Nat.sqrt n + 2) := by omega
  have h_cx_lt_pow2 : (vanEck n).count x < 2 ^ (Nat.sqrt n + 2) := by omega
  have h_ge : 2 ≤ (vanEck n).count 0 := count_zero_ge_two n (by omega)
  have h_pow_le : 2 ^ (Nat.sqrt n + 2) ≤ ((vanEck n).count 0) ^ (Nat.sqrt n + 2) :=
    Nat.pow_le_pow_left h_ge (Nat.sqrt n + 2)
  exact Nat.lt_of_lt_of_le h_cx_lt_pow2 h_pow_le
}

/--
Helper: For any n, log2(n) ≤ sqrt(n) + 1.
Proven by contradiction: if sqrt(n) + 1 < log2(n), then since log2(n) and sqrt(n) are integers,
sqrt(n) + 2 ≤ log2(n). This implies 2^(sqrt(n)+2) ≤ 2^log2(n) ≤ n < (sqrt(n)+1)^2 ≤ 2^(sqrt(n)+2),
a contradiction.
-/
lemma log2_le_sqrt_add_one (n : ℕ) : Nat.log2 n ≤ Nat.sqrt n + 1 := by {
  by_cases hn : n = 0
  · subst hn
    decide
  · by_contra! h
    have h_le : Nat.sqrt n + 2 ≤ Nat.log2 n := h
    have h_pow_mono : 2 ^ (Nat.sqrt n + 2) ≤ 2 ^ (Nat.log2 n) :=
      Nat.pow_le_pow_right (by decide) h_le
    have h_log_le : 2 ^ (Nat.log2 n) ≤ n := by {
      have h_pow_log_le := Nat.pow_log_le_self 2 hn
      rw [← Nat.log2_eq_log_two] at h_pow_log_le
      exact h_pow_log_le
    }
    have h_sqrt_lt := Nat.lt_succ_sqrt' n
    have h_succ_le := succ_sq_le_pow_two_add_two (Nat.sqrt n)
    omega
}

/--
Alternative Proof of the Square Root Conjecture: Derived from the logarithmic bound
using the property log2(n) ≤ sqrt(n) + 1.
-/
theorem count_lt_count_zero_pow_sqrt_2nd_proof (n x : ℕ) (hx : x > 0) (hn : n ≥ 2) :
    (vanEck n).count x < ((vanEck n).count 0) ^ (Nat.sqrt n + 2) := by {
  have h_log_bound := count_lt_count_zero_pow_log n x hx hn
  have h_log2_le_sqrt := log2_le_sqrt_add_one n
  have h_exp_le : Nat.log2 n + 1 ≤ Nat.sqrt n + 2 := by omega
  have h_pow_le : ((vanEck n).count 0) ^ (Nat.log2 n + 1) ≤ ((vanEck n).count 0) ^ (Nat.sqrt n + 2) :=
    Nat.pow_le_pow_right (count_zero_pos n) h_exp_le
  exact Nat.lt_of_lt_of_le h_log_bound h_pow_le
}


lemma prefix_max_linear_bound (n : ℕ) : vanEckPrefixMax n ≤ n := by {
  unfold vanEckPrefixMax
  apply listMax_le
  intro x hx
  rcases mem_listNth hx with ⟨k, hk, rfl⟩
  have h_len : (vanEck n).length = n + 1 := vanEckLength n
  rw [h_len] at hk
  have hk_le : k ≤ n := Nat.le_of_lt_succ hk
  by_cases hk0 : k = 0
  · subst hk0
    have h0 : listNth (vanEck n) 0 = 0 := list_nth_VanEck_zero_eq_zero n
    rw [h0]
    exact Nat.zero_le n
  · have hk_pos : k > 0 := Nat.pos_of_ne_zero hk0
    have h_det : listNth (vanEck n) k = vanEckNthTerm k := VanEck_deterministic n k hk_le
    rw [h_det]
    have h_le_k := vanEck_le_index k hk_pos
    exact Nat.le_trans h_le_k hk_le
}

lemma vanEckPrefixMax_monotone (n m : ℕ) (hnm : n ≤ m) : vanEckPrefixMax n ≤ vanEckPrefixMax m := by {
  unfold vanEckPrefixMax
  apply listMax_le
  intro x hx
  rcases mem_listNth hx with ⟨k, hk, rfl⟩
  have h_len : (vanEck n).length = n + 1 := vanEckLength n
  rw [h_len] at hk
  have hk_le : k ≤ n := Nat.le_of_lt_succ hk
  have h_in : listNth (vanEck m) k ∈ vanEck m := by {
    apply listNth_mem
    rw [vanEckLength]
    exact Nat.lt_of_lt_of_le hk (Nat.succ_le_succ hnm)
  }
  have hd1 := VanEck_deterministic n k hk_le
  have hd2 := VanEck_deterministic m k (Nat.le_trans hk_le hnm)
  rw [hd2, ← hd1] at h_in
  exact le_listMax_of_mem h_in
}


lemma gap_2_implies_two (i : ℕ) (h_eq : vanEckNthTerm i = vanEckNthTerm (i + 2))
    (h_neq1 : vanEckNthTerm (i + 1) ≠ vanEckNthTerm (i + 2)) :
    vanEckNthTerm (i + 3) = 2 := by {
  have hpos : 0 < i + 3 := Nat.zero_lt_succ _
  have hm := vanEck_term_is_matchSearch (i + 3) hpos
  have hsub : i + 3 - 1 = i + 2 := rfl
  rw [hsub] at hm
  have hlen : (vanEck (i + 2)).length = i + 3 := vanEckLength (i + 2)
  have hd_2_list : listNth (vanEck (i + 2)) (i + 2) = vanEckNthTerm (i + 2) := by {
    exact VanEck_deterministic (i + 2) (i + 2) (Nat.le_refl _)
  }
  have hd_1_list : listNth (vanEck (i + 2)) (i + 1) = vanEckNthTerm (i + 1) := by {
    exact VanEck_deterministic (i + 2) (i + 1) (Nat.le_succ _)
  }
  have hd_0_list : listNth (vanEck (i + 2)) i = vanEckNthTerm i := by {
    exact VanEck_deterministic (i + 2) i (Nat.le_trans (Nat.le_succ _) (Nat.le_succ _))
  }
  have hsub2 : i + 3 - 1 = i + 2 := rfl
  have h_ite_1 : matchSearch (vanEck (i + 2)) (i + 2) = matchSearch (vanEck (i + 2)) (i + 1) := by {
    have h_neq2 : listNth (vanEck (i + 2)) ((vanEck (i + 2)).length - 1) ≠ listNth (vanEck (i + 2)) (i + 1) := by {
      rw [hlen, hsub2, hd_2_list, hd_1_list]
      intro hc
      exact h_neq1 hc.symm
    }
    have h_ff := matchSearch_ite_ff (vanEck (i + 2)) (i + 1) h_neq2
    have hi2 : i + 1 + 1 = i + 2 := rfl
    rw [hi2] at h_ff
    exact h_ff
  }
  have h_ite_2 : matchSearch (vanEck (i + 2)) (i + 1) = 2 := by {
    have h_eq2 : listNth (vanEck (i + 2)) ((vanEck (i + 2)).length - 1) = listNth (vanEck (i + 2)) i := by {
      rw [hlen, hsub2, hd_2_list, hd_0_list]
      exact h_eq.symm
    }
    have h_tt := matchSearch_ite_tt (vanEck (i + 2)) i h_eq2
    have hi1 : i + 1 = i + 1 := rfl
    rw [hi1] at h_tt
    rw [h_tt, hlen, hsub2]
    exact Nat.add_sub_cancel_left i 2
  }
  rw [hm, h_ite_1, h_ite_2]
}

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

lemma post_zero_bounded (N_0 z z_prev : ℕ) (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hz : vanEckNthTerm z = 0) (hz_gt : z > N_0)
    (_h_prev : vanEckNthTerm z_prev = 0) (h_prev_lt : z_prev < z)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) :
    vanEckNthTerm (z + 1) ≤ vanEckPrefixMax z_prev := by {
  have h_old := finite_twos_implies_old_gaps N_0 h_no_twos z hz_gt hz
  rcases h_old with ⟨i, hi_lt, heq_i⟩
  have hi_le : i ≤ z := Nat.le_of_lt_succ hi_lt
  rw [← heq_i]
  by_cases hi_zprev : i ≤ z_prev
  · exact vanEckNthTerm_le_prefixMax z_prev i hi_zprev
  · have hi_gt : i > z_prev := Nat.lt_of_not_ge hi_zprev
    by_cases hiz : i = z
    · rw [hiz, hz]
      exact Nat.zero_le _
    · by_cases hi_z_1 : i = z - 1
      · have hz_pos : z > 0 := by omega
        have hz_sub : z - 1 + 2 = z + 1 := by omega
        have h_eq_gap : vanEckNthTerm (z - 1) = vanEckNthTerm (z - 1 + 2) := by {
          rw [hz_sub, ← hi_z_1, heq_i]
        }
        have h_neq_gap : vanEckNthTerm (z - 1 + 1) ≠ vanEckNthTerm (z - 1 + 2) := by {
          have hz_sub_1 : z - 1 + 1 = z := by omega
          rw [hz_sub_1, hz_sub, hz]
          intro hc
          have h_i_zero : vanEckNthTerm i = 0 := by rw [heq_i, hc]
          exact h_gap i hi_gt (by omega) h_i_zero
        }
        have h_two := gap_2_implies_two (z - 1) h_eq_gap h_neq_gap
        have hz_sub_3 : z - 1 + 3 = z + 2 := by omega
        rw [hz_sub_3] at h_two
        have h_contra := h_no_twos (z + 2) (by omega)
        contradiction
      · have h_G : z = z_prev + (z - z_prev) := (Nat.add_sub_of_le (Nat.le_of_lt h_prev_lt)).symm
        have h_nonzero : ∀ j, z_prev < j → j < z_prev + (z - z_prev) → vanEckNthTerm j ≠ 0 := by {
          intro j hj_gt hj_lt
          rw [← h_G] at hj_lt
          exact h_gap j hj_gt hj_lt
        }
        have h_all := gap_contains_all_terms z_prev (z - z_prev) h_nonzero
        have hi_lt_z_1 : i < z_prev + (z - z_prev) - 1 := by {
          rw [← h_G]
          omega
        }
        exact h_all i hi_lt_z_1
}

lemma gap_parity (N_0 i j : ℕ) (h_no_evens : ∀ m > N_0, vanEckNthTerm m = 0 ∨ vanEckNthTerm m % 2 = 1)
  (h_j_gt : j > N_0) (h_lt : i < j) (h_eq : vanEckNthTerm i = vanEckNthTerm j)
  (h_strict : ∀ k, i < k → k < j → vanEckNthTerm k ≠ vanEckNthTerm i) :
  (j - i) % 2 = 1 := by {
  have h_j1_gt : j + 1 > N_0 := Nat.lt_trans h_j_gt (Nat.lt_succ_self _)
  have h_val := h_no_evens (j + 1) h_j1_gt
  have h_len : (vanEck j).length = j + 1 := vanEckLength j
  have h_pos : j + 1 ≥ 2 := by omega
  have ha := vanEck_term_is_matchSearch (j + 1) (by omega)
  
  have hd_last : listNth (vanEck j) j = vanEckNthTerm j := by
    exact VanEck_deterministic j j (Nat.le_refl _)
    
  have hd_start : listNth (vanEck j) i = vanEckNthTerm i := by
    have h_le : i ≤ j := Nat.le_of_lt h_lt
    exact VanEck_deterministic j i h_le
    
  have h_match : listNth (vanEck j) ((vanEck j).length - 1) = listNth (vanEck j) i := by
    have h1 : (vanEck j).length - 1 = j := by rw [h_len]; rfl
    rw [h1]
    rw [hd_last, hd_start]
    exact h_eq.symm
    
  have h_fail : ∀ k, 1 ≤ k → k ≤ j - i - 1 → listNth (vanEck j) ((vanEck j).length - 1) ≠ listNth (vanEck j) (i + k) := by
    intro k hk1 hk_le
    have h_idx : i + k ≤ j := by omega
    have h_det : listNth (vanEck j) (i + k) = vanEckNthTerm (i + k) := VanEck_deterministic j (i + k) h_idx
    have h1 : (vanEck j).length - 1 = j := by rw [h_len]; rfl
    rw [h1]
    rw [hd_last]
    rw [h_det]
    intro hc
    have hc_symm : vanEckNthTerm (i + k) = vanEckNthTerm i := by
      rw [hc.symm]
      exact h_eq.symm
    have h_k_gt : i < i + k := by omega
    have h_k_lt : i + k < j := by omega
    exact h_strict (i + k) h_k_gt h_k_lt hc_symm

  have h_ms := matchSearch_eq_dist (vanEck j) i (j - i - 1) h_match h_fail

  have h_arg : i + (j - i - 1) + 1 = j := by omega
  rw [h_arg] at h_ms

  have h_sub_1 : j + 1 - 1 = j := rfl
  rw [h_sub_1] at ha
  rw [ha] at h_val

  have h_len_sub : (vanEck j).length - 1 - i = j - i := by rw [h_len]; omega
  rw [h_len_sub] at h_ms
  rw [h_ms] at h_val

  cases h_val with
  | inl h0 =>
    have h_pos_sub : j - i > 0 := by omega
    have h_contra : j - i = 0 := h0
    omega
  | inr h1 =>
    exact h1
}

lemma triple_eq_implies_one (i : ℕ) (x : ℕ) (h1 : vanEckNthTerm i = x) (h2 : vanEckNthTerm (i + 1) = x) (h3 : vanEckNthTerm (i + 2) = x) :
  x = 1 := by {
  have hpos : 0 < i + 2 := by omega
  have ha := vanEck_term_is_matchSearch (i + 2) hpos
  have hi_sub : i + 2 - 1 = i + 1 := rfl
  rw [hi_sub] at ha
  have hlen : (vanEck (i + 1)).length = i + 2 := vanEckLength (i + 1)

  have hd_last : listNth (vanEck (i + 1)) (i + 1) = vanEckNthTerm (i + 1) := VanEck_deterministic (i + 1) (i + 1) (Nat.le_refl _)
  have hd_prev : listNth (vanEck (i + 1)) i = vanEckNthTerm i := VanEck_deterministic (i + 1) i (Nat.le_succ _)

  have h_match : listNth (vanEck (i + 1)) ((vanEck (i + 1)).length - 1) = listNth (vanEck (i + 1)) i := by
    have hl : (vanEck (i + 1)).length - 1 = i + 1 := by rw [hlen]; rfl
    rw [hl, hd_last, hd_prev]
    rw [h2, h1]

  have h_tt := matchSearch_ite_tt (vanEck (i + 1)) i h_match
  have h_eq_i1 : i + 1 = i + 1 := rfl
  rw [h_eq_i1] at h_tt

  rw [h_tt] at ha
  rw [hlen] at ha
  have ha_simp : vanEckNthTerm (i + 2) = 1 := by
    rw [ha]
    have h_sub_simp : i + 2 - 1 - i = 1 := by omega
    exact h_sub_simp

  rw [h3] at ha_simp
  exact ha_simp
}

lemma no_gap_two_of_no_twos (N_0 i : ℕ) (h_no_evens : ∀ m > N_0, vanEckNthTerm m = 0 ∨ vanEckNthTerm m % 2 = 1)
  (h_i_gt : i > N_0) : vanEckNthTerm i ≠ vanEckNthTerm (i + 2) := by {
  intro h_eq
  have h_val := h_no_evens (i + 3) (by omega)
  have h_no_two : vanEckNthTerm (i + 3) ≠ 2 := by
    intro hc
    rw [hc] at h_val
    cases h_val with
    | inl h0 => contradiction
    | inr h1 => revert h1; decide

  by_cases h_eq1 : vanEckNthTerm (i + 1) = vanEckNthTerm (i + 2)
  · have h_eq0 : vanEckNthTerm i = vanEckNthTerm (i + 1) := by
      rw [h_eq1]
      exact h_eq
    let x := vanEckNthTerm i
    have h1 : vanEckNthTerm i = x := rfl
    have h2 : vanEckNthTerm (i + 1) = x := h_eq0.symm
    have h3 : vanEckNthTerm (i + 2) = x := h_eq.symm
    have hx_one := triple_eq_implies_one i x h1 h2 h3

    have h_seq_1 : vanEckNthTerm i = 1 := by rw [h1, hx_one]
    have h_seq_2 : vanEckNthTerm (i + 1) = 1 := by rw [h2, hx_one]

    have h_per : ∀ d, vanEckNthTerm (i + d) = 1 := by
      intro d
      induction d using Nat.strong_induction_on with
      | h d ih =>
        by_cases hd0 : d = 0
        · rw [hd0]; exact h_seq_1
        · by_cases hd1 : d = 1
          · rw [hd1]; exact h_seq_2
          · have hd_ge_2 : d ≥ 2 := by omega
            have h_d_1_lt : d - 1 < d := by omega
            have h_d_2_lt : d - 2 < d := by omega
            have hd_1 := ih (d - 1) h_d_1_lt
            have hd_2 := ih (d - 2) h_d_2_lt
            have h_m : i + (d - 2) + 1 = i + (d - 1) := by omega
            have h_m2 : i + (d - 2) + 2 = i + d := by omega
            have heq_consec : vanEckNthTerm (i + (d - 2)) = vanEckNthTerm (i + (d - 2) + 1) := by
              rw [h_m]
              rw [hd_2, hd_1]
            have h_next := vanEck_consecutive_eq_implies_next_one (i + (d - 2)) heq_consec
            rw [h_m2] at h_next
            exact h_next

    have h_contra := vanEck_not_periodic 1 (by decide) i
    rcases h_contra with ⟨m, hm_gt, hneq⟩
    have hm_eq : m = i + (m - i) := by omega
    have hm1_eq : m + 1 = i + (m - i + 1) := by omega
    have h_val_m := h_per (m - i)
    have h_val_m1 := h_per (m - i + 1)
    rw [← hm_eq] at h_val_m
    rw [← hm1_eq] at h_val_m1
    rw [h_val_m, h_val_m1] at hneq
    exact hneq rfl
  · have h_two := gap_2_implies_two i h_eq h_eq1
    exact h_no_two h_two
}





lemma prefix_max_bound_at_zero (n : ℕ) (hn_pos : n > 0) (hn_zero : vanEckNthTerm n = 0) :
    vanEckPrefixMax n ≤ n - 1 := by {
  unfold vanEckPrefixMax
  apply listMax_le
  intro x hx
  rcases mem_listNth hx with ⟨k, hk, rfl⟩
  have h_len : (vanEck n).length = n + 1 := vanEckLength n
  rw [h_len] at hk
  have hk_le : k ≤ n := Nat.le_of_lt_succ hk
  by_cases hk_eq : k = n
  · rw [hk_eq]
    have h_n_val : listNth (vanEck n) n = vanEckNthTerm n := rfl
    rw [h_n_val, hn_zero]
    omega
  · have hk_lt : k < n := Nat.lt_of_le_of_ne hk_le hk_eq
    by_cases hk0 : k = 0
    · subst hk0
      have h0 : listNth (vanEck n) 0 = 0 := list_nth_VanEck_zero_eq_zero n
      rw [h0]
      omega
    · have hk_pos : k > 0 := Nat.pos_of_ne_zero hk0
      have h_det : listNth (vanEck n) k = vanEckNthTerm k := VanEck_deterministic n k (Nat.le_of_lt hk_lt)
      rw [h_det]
      have h_le_k := vanEck_le_index k hk_pos
      omega
}

/--
Unconditional local step-2 collision rule: whenever `a(i) = a(i + 2)` at any index `i`,
the very next term `a(i + 3)` must equal `2`, since `a(i + 1) = a(i + 2)` would create
a forbidden three-in-a-row run.
-/
lemma eq_add_two_implies_next_two (i : ℕ)
    (h_eq : vanEckNthTerm i = vanEckNthTerm (i + 2)) :
    vanEckNthTerm (i + 3) = 2 := by {
  by_cases h_mid : vanEckNthTerm (i + 1) = vanEckNthTerm (i + 2)
  · exfalso
    exact vanEck_triple_impossible i (vanEckNthTerm (i + 2)) ⟨h_eq, h_mid, rfl⟩
  · exact gap_2_implies_two i h_eq h_mid
}

/--
In a `2`-free tail (`∀ m > N_0, a(m) ≠ 2`), no two terms at distance `2` can be equal
once `i + 3 > N_0`.
-/
lemma no_step_two_repeat_of_no_twos (N_0 i : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hi : i + 3 > N_0) :
    vanEckNthTerm i ≠ vanEckNthTerm (i + 2) := by {
  intro h_eq
  have h_two : vanEckNthTerm (i + 3) = 2 := eq_add_two_implies_next_two i h_eq
  exact h_no_twos (i + 3) hi h_two
}

/--
Global non-stuttering of the even-index track `k ↦ a(2k)` in a `2`-free tail:
consecutive terms of the even-index subsequence are never equal once `2k + 3 > N_0`.
-/
lemma even_track_non_stuttering (N_0 k : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hk : 2 * k + 3 > N_0) :
    vanEckNthTerm (2 * k) ≠ vanEckNthTerm (2 * (k + 1)) := by {
  have h_step : 2 * (k + 1) = 2 * k + 2 := by { omega }
  rw [h_step]
  exact no_step_two_repeat_of_no_twos N_0 (2 * k) h_no_twos hk
}

/--
Global non-stuttering of the odd-index track `k ↦ a(2k + 1)` in a `2`-free tail:
consecutive terms of the odd-index subsequence are never equal once `2k + 4 > N_0`.
-/
lemma odd_track_non_stuttering (N_0 k : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hk : 2 * k + 4 > N_0) :
    vanEckNthTerm (2 * k + 1) ≠ vanEckNthTerm (2 * (k + 1) + 1) := by {
  have h_step : 2 * (k + 1) + 1 = (2 * k + 1) + 2 := by { omega }
  have hi : (2 * k + 1) + 3 > N_0 := by { omega }
  rw [h_step]
  exact no_step_two_repeat_of_no_twos N_0 (2 * k + 1) h_no_twos hi
}

/--
Shifted (`k ↦ k + 1`) even-track non-stuttering in a `2`-free tail:
`a(2(k + 1)) ≠ a(2(k + 2))` once `2k + 5 > N_0`.
-/
lemma even_track_succ_non_stuttering (N_0 k : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hk : 2 * k + 5 > N_0) :
    vanEckNthTerm (2 * (k + 1)) ≠ vanEckNthTerm (2 * (k + 2)) := by {
  exact even_track_non_stuttering N_0 (k + 1) h_no_twos (by { omega })
}

/--
Shifted (`k ↦ k + 1`) odd-track non-stuttering in a `2`-free tail:
`a(2(k + 1) + 1) ≠ a(2(k + 2) + 1)` once `2k + 6 > N_0`.
-/
lemma odd_track_succ_non_stuttering (N_0 k : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hk : 2 * k + 6 > N_0) :
    vanEckNthTerm (2 * (k + 1) + 1) ≠ vanEckNthTerm (2 * (k + 2) + 1) := by {
  exact odd_track_non_stuttering N_0 (k + 1) h_no_twos (by { omega })
}

/--
Arbitrary shift (`k ↦ k + n` for any `n : ℕ`) even-track non-stuttering in a `2`-free tail:
`a(2(k + n)) ≠ a(2(k + n + 1))` whenever `2(k + n) + 3 > N_0`.
-/
lemma even_track_add_non_stuttering (N_0 k n : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hk : 2 * (k + n) + 3 > N_0) :
    vanEckNthTerm (2 * (k + n)) ≠ vanEckNthTerm (2 * (k + n + 1)) := by {
  exact even_track_non_stuttering N_0 (k + n) h_no_twos hk
}

/--
Arbitrary shift (`k ↦ k + n` for any `n : ℕ`) odd-track non-stuttering in a `2`-free tail:
`a(2(k + n) + 1) ≠ a(2(k + n + 1) + 1)` whenever `2(k + n) + 4 > N_0`.
-/
lemma odd_track_add_non_stuttering (N_0 k n : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hk : 2 * (k + n) + 4 > N_0) :
    vanEckNthTerm (2 * (k + n) + 1) ≠ vanEckNthTerm (2 * (k + n + 1) + 1) := by {
  exact odd_track_non_stuttering N_0 (k + n) h_no_twos hk
}

/--
Threshold-free tail form (`n = N_0`): for *every* `k : ℕ` unconditionally,
both shifted tracks `k ↦ a(2(k + N_0))` and `k ↦ a(2(k + N_0) + 1)` never stutter.
-/
lemma tail_tracks_non_stuttering (N_0 k : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2) :
    vanEckNthTerm (2 * (k + N_0)) ≠ vanEckNthTerm (2 * (k + N_0 + 1)) ∧
      vanEckNthTerm (2 * (k + N_0) + 1) ≠ vanEckNthTerm (2 * (k + N_0 + 1) + 1) := by {
  constructor
  · exact even_track_add_non_stuttering N_0 k N_0 h_no_twos (by { omega })
  · exact odd_track_add_non_stuttering N_0 k N_0 h_no_twos (by { omega })
}

/--
Unconditional exclusion of back-to-back equal pairs `(x, x, y, y)`:
if `a(i) = a(i + 1)`, then `a(i + 2) = 1`, so `a(i + 2) = a(i + 3)` would force two
consecutive `1`s. In particular, `a(2k) = a(2k + 1)` and `a(2(k + 1)) = a(2(k + 1) + 1)`
can never both hold.
-/
lemma vanEck_no_consecutive_pairs (i : ℕ) :
    ¬(vanEckNthTerm i = vanEckNthTerm (i + 1) ∧
      vanEckNthTerm (i + 2) = vanEckNthTerm (i + 3)) := by {
  rintro ⟨h01, h23⟩
  have h2_one : vanEckNthTerm (i + 2) = 1 :=
    vanEck_consecutive_eq_implies_next_one i h01
  have h3_one : vanEckNthTerm (i + 3) = 1 := by {
    rw [← h23]
    exact h2_one
  }
  exact vanEck_no_consecutive_ones (i + 2) ⟨h2_one, h3_one⟩
}

/--
After index `0`, two zeros in the Van Eck sequence can never be adjacent:
for any `0 < z_prev < z` with `a(z_prev) = 0` and `a(z) = 0`, we have `z - z_prev ≥ 2`.
-/
lemma consecutive_zeros_gap_ge_two (z z_prev : ℕ)
    (hz_prev_pos : z_prev > 0)
    (hz : vanEckNthTerm z = 0)
    (hz_prev : vanEckNthTerm z_prev = 0)
    (h_prev_lt : z_prev < z) :
    z - z_prev ≥ 2 := by {
  by_contra h_lt_two
  have hz_eq : z = (z_prev - 1) + 2 := by { omega }
  have hz_iff := vanEck_mth_term_eq_zero_iff_prev_term_new (z_prev - 1)
  rw [← hz_eq] at hz_iff
  have h_new := hz_iff.mp hz
  have hz_sub : z_prev - 1 + 1 = z_prev := by { omega }
  rw [hz_sub] at h_new
  have h0_neq := h_new 0 hz_prev_pos
  have h0_zero : vanEckNthTerm 0 = 0 := rfl
  rw [h0_zero, hz_prev] at h0_neq
  exact h0_neq rfl
}

/--
If `0 < z_prev < z` are consecutive zeros and `a(z + 1) ≠ 2`, then the zero-to-zero
distance satisfies `z - z_prev ≥ 3` (so `z_prev < z - 2 < z - 1`).
-/
lemma consecutive_zeros_gap_ge_three_of_ne_two (z z_prev : ℕ)
    (hz_prev_pos : z_prev > 0)
    (hz : vanEckNthTerm z = 0)
    (hz_prev : vanEckNthTerm z_prev = 0)
    (h_prev_lt : z_prev < z)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0)
    (h_ne_two : vanEckNthTerm (z + 1) ≠ 2) :
    z - z_prev ≥ 3 := by {
  have h_ge_two : z - z_prev ≥ 2 :=
    consecutive_zeros_gap_ge_two z z_prev hz_prev_pos hz hz_prev h_prev_lt
  have hz_pos : z > 0 := by { omega }
  have h_dist : vanEckNthTerm (z + 1) = z - z_prev :=
    gap_between_zeros z z_prev hz hz_pos hz_prev h_prev_lt h_gap
  rw [h_dist] at h_ne_two
  omega
}

/--
In a `2`-free tail (`∀ m > N_0, a(m) ≠ 2`), any consecutive zeros `0 < z_prev < z`
with `z > N_0` satisfy `3 ≤ z - z_prev ≤ vanEckPrefixMax z_prev`, and the term at
`z - 2` (which generates the new value `a(z - 1)`) is bounded by `vanEckPrefixMax z_prev`.
-/
lemma no_twos_zero_gap_and_predecessor_bounds (N_0 z z_prev : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hz_prev_pos : z_prev > 0)
    (hz : vanEckNthTerm z = 0)
    (hz_gt : z > N_0)
    (hz_prev : vanEckNthTerm z_prev = 0)
    (h_prev_lt : z_prev < z)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) :
    3 ≤ z - z_prev ∧
      z - z_prev ≤ vanEckPrefixMax z_prev ∧
      vanEckNthTerm (z - 2) ≤ vanEckPrefixMax z_prev := by {
  have hz1_ne_two : vanEckNthTerm (z + 1) ≠ 2 := h_no_twos (z + 1) (by { omega })
  have h_ge_three : 3 ≤ z - z_prev :=
    consecutive_zeros_gap_ge_three_of_ne_two z z_prev hz_prev_pos hz hz_prev
      h_prev_lt h_gap hz1_ne_two
  have h_post : vanEckNthTerm (z + 1) ≤ vanEckPrefixMax z_prev :=
    post_zero_bounded N_0 z z_prev h_no_twos hz hz_gt hz_prev h_prev_lt h_gap
  have h_dist : vanEckNthTerm (z + 1) = z - z_prev :=
    gap_between_zeros z z_prev hz (by { omega }) hz_prev h_prev_lt h_gap
  rw [h_dist] at h_post
  have h_G : z_prev + (z - z_prev) = z := Nat.add_sub_of_le (Nat.le_of_lt h_prev_lt)
  have h_nonzero : ∀ j, z_prev < j → j < z_prev + (z - z_prev) → vanEckNthTerm j ≠ 0 := by {
    intro j hj1 hj2
    rw [h_G] at hj2
    exact h_gap j hj1 hj2
  }
  have h_all := gap_contains_all_terms z_prev (z - z_prev) h_nonzero
  have hz2_lt : z - 2 < z_prev + (z - z_prev) - 1 := by { omega }
  exact ⟨h_ge_three, h_post, h_all (z - 2) hz2_lt⟩
}

/--
At any consecutive zero pair `0 < z_prev < z` in a `2`-free tail (`z > N_0`),
the new value `a(z - 1)` is positive, strictly less than `z - 1`, and arises as a
lookback gap of a value `a(z - 2) ≤ vanEckPrefixMax z_prev` matching `a(z - 2 - a(z - 1))`.
-/
lemma pre_zero_new_value_from_bounded_predecessor (N_0 z z_prev : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hz_prev_pos : z_prev > 0)
    (hz : vanEckNthTerm z = 0)
    (hz_gt : z > N_0)
    (hz_prev : vanEckNthTerm z_prev = 0)
    (h_prev_lt : z_prev < z)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) :
    0 < vanEckNthTerm (z - 1) ∧
      vanEckNthTerm (z - 1) < z - 1 ∧
      vanEckNthTerm (z - 2) ≤ vanEckPrefixMax z_prev ∧
      vanEckNthTerm (z - 2 - vanEckNthTerm (z - 1)) = vanEckNthTerm (z - 2) := by {
  have h_bounds :=
    no_twos_zero_gap_and_predecessor_bounds N_0 z z_prev h_no_twos
      hz_prev_pos hz hz_gt hz_prev h_prev_lt h_gap
  rcases h_bounds with ⟨h_ge_three, _, hz2_le⟩
  have hz1_ne_zero : vanEckNthTerm (z - 1) ≠ 0 :=
    h_gap (z - 1) (by { omega }) (by { omega })
  have hz1_pos : 0 < vanEckNthTerm (z - 1) := Nat.pos_of_ne_zero hz1_ne_zero
  have hz1_ge_two : z - 1 ≥ 2 := by { omega }
  have h_lookback :=
    pos_value_implies_gap (z - 1) (vanEckNthTerm (z - 1)) hz1_ge_two rfl hz1_pos
  have hz_sub : z - 1 - 1 = z - 2 := by { omega }
  rw [hz_sub] at h_lookback
  exact ⟨hz1_pos, h_lookback.1, hz2_le, h_lookback.2⟩
}

/--
Strict lookback characterization of any positive Van Eck term `a(m) = n > 0` (`m ≥ 2`):
`m - 1 - n` is strictly less than `m - 1`, matches `a(m - 1)`, and is the strictly most
recent prior occurrence of `a(m - 1)` before `m - 1`.
-/
lemma pos_value_most_recent_occurrence (m n : ℕ) (hm : m ≥ 2)
    (h_val : vanEckNthTerm m = n) (h_pos : n > 0) :
    m - 1 - n < m - 1 ∧
      vanEckNthTerm (m - 1 - n) = vanEckNthTerm (m - 1) ∧
      ∀ j, m - 1 - n < j → j < m - 1 → vanEckNthTerm j ≠ vanEckNthTerm (m - 1) := by {
  have h_gap := pos_value_implies_gap m n hm h_val h_pos
  have h_lt : m - 1 - n < m - 1 := by { omega }
  refine ⟨h_lt, h_gap.2, ?_⟩
  intro j hj1 hj2 h_eq
  have h_ms : vanEckNthTerm m = matchSearch (vanEck (m - 1)) (m - 1) :=
    vanEck_term_is_matchSearch m (by { omega })
  have h_ms_ne : matchSearch (vanEck (m - 1)) (m - 1) ≠ 0 := by {
    rw [← h_ms, h_val]
    omega
  }
  have h_len : (vanEck (m - 1)).length - 1 = m - 1 := by {
    have hl := vanEckLength (m - 1)
    omega
  }
  have h_match : listNth (vanEck (m - 1)) ((vanEck (m - 1)).length - 1) =
      listNth (vanEck (m - 1)) j := by {
    rw [h_len]
    have hd1 := VanEck_deterministic (m - 1) (m - 1) (Nat.le_refl _)
    have hd2 := VanEck_deterministic (m - 1) j (by { omega })
    rw [hd1, hd2]
    exact h_eq.symm
  }
  have h_first := matchSearch_first (vanEck (m - 1)) (m - 1) j h_ms_ne hj2 h_match
  rw [← h_ms, h_val, h_len] at h_first
  omega
}

/--
Any term `a(z - 1)` immediately preceding a zero `a(z) = 0` (`z ≥ 2`) is strictly
distinct from every earlier term `a(idx)` (`idx < z - 1`).
-/
lemma pre_zero_ne_prior_val (z idx : ℕ) (hz : vanEckNthTerm z = 0)
    (hz_ge : z ≥ 2) (h_idx : idx < z - 1) :
    vanEckNthTerm (z - 1) ≠ vanEckNthTerm idx := by {
  have hz_eq : z = (z - 2) + 2 := by { omega }
  have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new (z - 2)
  rw [← hz_eq] at h_iff
  have h_sub : z - 2 + 1 = z - 1 := by { omega }
  have h_new := h_iff.mp hz
  rw [h_sub] at h_new
  exact Ne.symm (h_new idx h_idx)
}

/--
Unconditional prior-occurrence specification for the new value `a(z - 1)` before any
zero `a(z) = 0` (`z ≥ 2`): `a(z - 1) > 0` is brand-new, and `p = z - 2 - a(z - 1)` is
the strictly most recent prior occurrence of the generator `a(z - 2)` before `z - 2`,
with `a(z - 1) = (z - 2) - p`.
-/
lemma pre_zero_new_value_prior_occurrence_spec (z : ℕ)
    (hz : vanEckNthTerm z = 0) (hz_ge : z ≥ 2) :
    0 < vanEckNthTerm (z - 1) ∧
      (∀ i < z - 1, vanEckNthTerm i ≠ vanEckNthTerm (z - 1)) ∧
      z - 2 - vanEckNthTerm (z - 1) < z - 2 ∧
      vanEckNthTerm (z - 1) = (z - 2) - (z - 2 - vanEckNthTerm (z - 1)) ∧
      vanEckNthTerm (z - 2 - vanEckNthTerm (z - 1)) = vanEckNthTerm (z - 2) ∧
      ∀ j, z - 2 - vanEckNthTerm (z - 1) < j → j < z - 2 →
        vanEckNthTerm j ≠ vanEckNthTerm (z - 2) := by {
  have hz_ne_two : z ≠ 2 := by {
    intro hc
    rw [hc] at hz
    exact Nat.one_ne_zero hz
  }
  have hz1_ge : z - 1 ≥ 2 := by { omega }
  have hz1_nz : vanEckNthTerm (z - 1) ≠ 0 :=
    pre_zero_ne_prior_val z 0 hz hz_ge (by { omega })
  have hz1_pos : 0 < vanEckNthTerm (z - 1) := Nat.pos_of_ne_zero hz1_nz
  have hz1_le : vanEckNthTerm (z - 1) ≤ z - 2 := by {
    have h_le := a_le_idx_minus_one hz1_ge hz1_pos
    omega
  }
  have h_new : ∀ i < z - 1, vanEckNthTerm i ≠ vanEckNthTerm (z - 1) :=
    fun i hi => Ne.symm (pre_zero_ne_prior_val z i hz hz_ge hi)
  have h_rec :=
    pos_value_most_recent_occurrence (z - 1) (vanEckNthTerm (z - 1)) hz1_ge rfl hz1_pos
  have h_sub : z - 1 - 1 = z - 2 := by { omega }
  rw [h_sub] at h_rec
  exact ⟨hz1_pos, h_new, h_rec.1, by { omega }, h_rec.2.1, h_rec.2.2⟩
}

/--
Any prior occurrence `q < z - 2` of the generator `a(z - 2)` before a zero `a(z) = 0`
(`z ≥ 2`) upper-bounds the newly created value `a(z - 1)` by `(z - 2) - q`.
-/
lemma pre_zero_new_value_le_of_prior_occurrence (z q : ℕ)
    (hz : vanEckNthTerm z = 0) (hz_ge : z ≥ 2)
    (hq_lt : q < z - 2) (hq_eq : vanEckNthTerm q = vanEckNthTerm (z - 2)) :
    vanEckNthTerm (z - 1) ≤ (z - 2) - q := by {
  have h_spec := pre_zero_new_value_prior_occurrence_spec z hz hz_ge
  have h_le : q ≤ z - 2 - vanEckNthTerm (z - 1) := by {
    by_contra h_gt
    exact h_spec.2.2.2.2.2 q (by { omega }) hq_lt hq_eq
  }
  omega
}

/--
Monotonicity of `vanEckPrefixMax`: extending the prefix never decreases its maximum.
-/
lemma vanEckPrefixMax_mono (m n : ℕ) (hmn : m ≤ n) :
    vanEckPrefixMax m ≤ vanEckPrefixMax n := by {
  unfold vanEckPrefixMax
  apply listMax_le
  intro x hx
  rcases mem_listNth hx with ⟨k, hk_lt, rfl⟩
  have h_len := vanEckLength m
  rw [h_len] at hk_lt
  have hk_le_m : k ≤ m := Nat.le_of_lt_succ hk_lt
  have h_det := VanEck_deterministic m k hk_le_m
  rw [h_det]
  exact vanEckNthTerm_le_prefixMax n k (Nat.le_trans hk_le_m hmn)
}

/--
Unconditional prefix-maximum recurrence across any zero-free open interval `(z_prev, z)`
ending at a zero `a(z) = 0`: every term except the brand-new value `a(z - 1)` is bounded
by `vanEckPrefixMax z_prev`, so `vanEckPrefixMax z = max (vanEckPrefixMax z_prev) a(z - 1)`.
-/
lemma prefixMax_at_zero_eq_max (z z_prev : ℕ)
    (hz : vanEckNthTerm z = 0) (h_prev_lt : z_prev < z)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) :
    vanEckPrefixMax z = max (vanEckPrefixMax z_prev) (vanEckNthTerm (z - 1)) := by {
  apply Nat.le_antisymm
  · change listMax (vanEck z) ≤ max (vanEckPrefixMax z_prev) (vanEckNthTerm (z - 1))
    apply listMax_le
    intro x hx
    rcases mem_listNth hx with ⟨k, hk_lt, rfl⟩
    have h_len := vanEckLength z
    rw [h_len] at hk_lt
    have hk_le : k ≤ z := Nat.le_of_lt_succ hk_lt
    have h_det : listNth (vanEck z) k = vanEckNthTerm k := VanEck_deterministic z k hk_le
    rw [h_det]
    by_cases hk_z : k = z
    · rw [hk_z, hz]
      exact Nat.zero_le _
    · by_cases hk_z1 : k = z - 1
      · rw [hk_z1]
        exact Nat.le_max_right _ _
      · have h_G : z_prev + (z - z_prev) = z := Nat.add_sub_of_le (Nat.le_of_lt h_prev_lt)
        have h_nz : ∀ j, z_prev < j → j < z_prev + (z - z_prev) → vanEckNthTerm j ≠ 0 := by {
          intro j hj1 hj2
          rw [h_G] at hj2
          exact h_gap j hj1 hj2
        }
        have h_le := gap_contains_all_terms z_prev (z - z_prev) h_nz k (by { omega })
        exact Nat.le_trans h_le (Nat.le_max_left _ _)
  · exact Nat.max_le.mpr
      ⟨vanEckPrefixMax_mono z_prev z (Nat.le_of_lt h_prev_lt),
        vanEckNthTerm_le_prefixMax z (z - 1) (by { omega })⟩
}

/--
In a `2`-free tail (`∀ m > N_0, a(m) ≠ 2`), if the generator `a(z - 2)` before a zero
`z > N_0` occurred anywhere at or after `z_prev - 1` (`z_prev - 1 ≤ q < z - 2`), then
`a(z - 1) < vanEckPrefixMax z_prev` and `vanEckPrefixMax z = vanEckPrefixMax z_prev`.
-/
lemma no_twos_new_value_bounded_of_recent_generator (N_0 z z_prev q : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hz_prev_pos : z_prev > 0) (hz : vanEckNthTerm z = 0)
    (hz_gt : z > N_0) (hz_prev : vanEckNthTerm z_prev = 0)
    (h_prev_lt : z_prev < z)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0)
    (hq_ge : z_prev - 1 ≤ q) (hq_lt : q < z - 2)
    (hq_eq : vanEckNthTerm q = vanEckNthTerm (z - 2)) :
    vanEckNthTerm (z - 1) < vanEckPrefixMax z_prev ∧
      vanEckPrefixMax z = vanEckPrefixMax z_prev := by {
  have h_bounds :=
    no_twos_zero_gap_and_predecessor_bounds N_0 z z_prev h_no_twos
      hz_prev_pos hz hz_gt hz_prev h_prev_lt h_gap
  have h_le_q :=
    pre_zero_new_value_le_of_prior_occurrence z q hz (by { omega }) hq_lt hq_eq
  have hz1_lt : vanEckNthTerm (z - 1) < vanEckPrefixMax z_prev := by { omega }
  have h_pmax := prefixMax_at_zero_eq_max z z_prev hz h_prev_lt h_gap
  exact ⟨hz1_lt, by { omega }⟩
}

/--
Dormant-Generator Characterization of Prefix-Max Jumps: in a `2`-free tail (`z > N_0`),
`vanEckPrefixMax z > vanEckPrefixMax z_prev` occurs only when `a(z - 1)` is the new
prefix maximum, generated by a bounded value `1 ≤ a(z - 2) ≤ vanEckPrefixMax z_prev`
that was completely dormant throughout `[z_prev - 1, z - 3]` (`p + 1 < z_prev`), with
exact decomposition `a(z - 1) = (z - z_prev - 2) + (z_prev - p)`.
-/
lemma no_twos_prefixMax_jump_requires_dormant_generator (N_0 z z_prev : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hz_prev_pos : z_prev > 0) (hz : vanEckNthTerm z = 0)
    (hz_gt : z > N_0) (hz_prev : vanEckNthTerm z_prev = 0)
    (h_prev_lt : z_prev < z)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0)
    (h_jump : vanEckPrefixMax z_prev < vanEckPrefixMax z) :
    vanEckPrefixMax z = vanEckNthTerm (z - 1) ∧
      1 ≤ vanEckNthTerm (z - 2) ∧
      vanEckNthTerm (z - 2) ≤ vanEckPrefixMax z_prev ∧
      (z - 2 - vanEckNthTerm (z - 1)) + 1 < z_prev ∧
      (∀ j, z_prev - 1 ≤ j → j < z - 2 → vanEckNthTerm j ≠ vanEckNthTerm (z - 2)) ∧
      vanEckNthTerm (z - 1) =
        (z - z_prev - 2) + (z_prev - (z - 2 - vanEckNthTerm (z - 1))) ∧
      vanEckNthTerm (z - 1) ≤
        (vanEckPrefixMax z_prev - 2) + (z_prev - (z - 2 - vanEckNthTerm (z - 1))) := by {
  have h_bounds :=
    no_twos_zero_gap_and_predecessor_bounds N_0 z z_prev h_no_twos
      hz_prev_pos hz hz_gt hz_prev h_prev_lt h_gap
  have h_pmax := prefixMax_at_zero_eq_max z z_prev hz h_prev_lt h_gap
  have hz1_gt : vanEckPrefixMax z_prev < vanEckNthTerm (z - 1) := by { omega }
  have hz2_nz : vanEckNthTerm (z - 2) ≠ 0 := h_gap (z - 2) (by { omega }) (by { omega })
  have h_spec := pre_zero_new_value_prior_occurrence_spec z hz (by { omega })
  have h_dormant : ∀ j, z_prev - 1 ≤ j → j < z - 2 →
      vanEckNthTerm j ≠ vanEckNthTerm (z - 2) := by {
    intro j hj_ge hj_lt hj_eq
    have h_rec := no_twos_new_value_bounded_of_recent_generator N_0 z z_prev j
      h_no_twos hz_prev_pos hz hz_gt hz_prev h_prev_lt h_gap hj_ge hj_lt hj_eq
    omega
  }
  have hp_lt : (z - 2 - vanEckNthTerm (z - 1)) + 1 < z_prev := by {
    by_contra hp_ge
    exact h_dormant (z - 2 - vanEckNthTerm (z - 1)) (by { omega }) h_spec.2.2.1
      h_spec.2.2.2.2.1
  }
  exact ⟨by { omega }, Nat.pos_of_ne_zero hz2_nz, h_bounds.2.2, hp_lt, h_dormant,
    by { omega }, by { omega }⟩
}

/--
If `vanEckPrefixMax` never strictly increases across consecutive zeros at or after a
zero `z_0`, then `vanEckPrefixMax z ≤ vanEckPrefixMax z_0` for every zero `z ≥ z_0`.
-/
lemma no_prefixMax_zero_jumps_implies_bounded (z_0 : ℕ)
    (hz0_zero : vanEckNthTerm z_0 = 0)
    (h_no_jump : ∀ z_prev z, z_0 ≤ z_prev → z_prev < z →
      vanEckNthTerm z_prev = 0 → vanEckNthTerm z = 0 →
      (∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) →
      vanEckPrefixMax z ≤ vanEckPrefixMax z_prev) :
    ∀ z ≥ z_0, vanEckNthTerm z = 0 → vanEckPrefixMax z ≤ vanEckPrefixMax z_0 := by {
  intro z
  induction z using Nat.strong_induction_on with
  | h z ih =>
    intro hz_ge hz_zero
    by_cases hz_eq : z = z_0
    · rw [hz_eq]
    · have hz_gt : z > z_0 := Nat.lt_of_le_of_ne hz_ge (Ne.symm hz_eq)
      let z_prev := lastZero (z - 1)
      have hz_prev_le : z_prev ≤ z - 1 := lastZero_le (z - 1)
      have hz_prev_lt : z_prev < z := by { omega }
      have hz_prev_zero : vanEckNthTerm z_prev = 0 := vanEck_lastZero_is_zero (z - 1)
      have hz_prev_ge : z_0 ≤ z_prev := by {
        by_contra hc
        exact no_zero_after_lastZero (z - 1) z_0 (by { omega }) (by { omega }) hz0_zero
      }
      have h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0 :=
        fun k hk1 hk2 => no_zero_after_lastZero (z - 1) k hk1 (by { omega })
      have h_step := h_no_jump z_prev z hz_prev_ge hz_prev_lt hz_prev_zero hz_zero h_gap
      exact Nat.le_trans h_step (ih z_prev hz_prev_lt hz_prev_ge hz_prev_zero)
}

/--
Unconditionally, `vanEckPrefixMax` strictly increases across consecutive zeros
`z_prev < z` arbitrarily far out in the Van Eck sequence.
-/
lemma infinite_prefixMax_zero_jumps (K : ℕ) :
    ∃ z_prev z, K < z_prev ∧ z_prev < z ∧
      vanEckNthTerm z_prev = 0 ∧ vanEckNthTerm z = 0 ∧
      (∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) ∧
      vanEckPrefixMax z_prev < vanEckPrefixMax z := by {
  rcases infinite_zeros_vanEck K with ⟨z_0, hz0_gt, hz0_zero⟩
  by_contra h_none
  have h_no_jump : ∀ z_prev z, z_0 ≤ z_prev → z_prev < z →
      vanEckNthTerm z_prev = 0 → vanEckNthTerm z = 0 →
      (∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) →
      vanEckPrefixMax z ≤ vanEckPrefixMax z_prev := by {
    intro z_prev z hz_ge hz_lt hzp hz h_gap
    by_contra h_gt
    exact h_none ⟨z_prev, z, by { omega }, hz_lt, hzp, hz, h_gap, by { omega }⟩
  }
  have h_zeros_le := no_prefixMax_zero_jumps_implies_bounded z_0 hz0_zero h_no_jump
  rcases vanEck_unbounded (vanEckPrefixMax z_0) with ⟨m, hm_gt⟩
  rcases infinite_zeros_vanEck (max z_0 m) with ⟨z, hz_gt, hz_zero⟩
  have hm_le : vanEckNthTerm m ≤ vanEckPrefixMax z :=
    vanEckNthTerm_le_prefixMax z m (by { omega })
  have hz_le : vanEckPrefixMax z ≤ vanEckPrefixMax z_0 :=
    h_zeros_le z (by { omega }) hz_zero
  omega
}

/--
In a `2`-free tail (`∀ m > N_0, a(m) ≠ 2`), dormant-generator prefix-maximum jumps occur
arbitrarily far out (`K < z_prev`) and above any value floor (`V < vanEckPrefixMax z_prev`).
-/
lemma no_twos_infinite_dormant_generator_jumps (N_0 K V : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2) :
    ∃ z_prev z, N_0 < z_prev ∧ K < z_prev ∧ z_prev < z ∧
      vanEckNthTerm z_prev = 0 ∧ vanEckNthTerm z = 0 ∧
      (∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) ∧
      V < vanEckPrefixMax z_prev ∧
      vanEckPrefixMax z_prev < vanEckPrefixMax z ∧
      vanEckPrefixMax z = vanEckNthTerm (z - 1) ∧
      1 ≤ vanEckNthTerm (z - 2) ∧
      vanEckNthTerm (z - 2) ≤ vanEckPrefixMax z_prev ∧
      (z - 2 - vanEckNthTerm (z - 1)) + 1 < z_prev ∧
      (∀ j, z_prev - 1 ≤ j → j < z - 2 → vanEckNthTerm j ≠ vanEckNthTerm (z - 2)) := by {
  rcases vanEck_unbounded V with ⟨m_V, hmV_gt⟩
  rcases infinite_prefixMax_zero_jumps (max (max N_0 K) m_V) with
    ⟨z_prev, z, h_gt, hz_lt, hzp_zero, hz_zero, h_gap, h_jump⟩
  have hV_lt : V < vanEckPrefixMax z_prev :=
    Nat.lt_of_lt_of_le hmV_gt (vanEckNthTerm_le_prefixMax z_prev m_V (by { omega }))
  have h_dorm := no_twos_prefixMax_jump_requires_dormant_generator N_0 z z_prev
    h_no_twos (by { omega }) hz_zero (by { omega }) hzp_zero hz_lt h_gap h_jump
  exact ⟨z_prev, z, by { omega }, by { omega }, hz_lt, hzp_zero, hz_zero, h_gap, hV_lt,
    h_jump, h_dorm.1, h_dorm.2.1, h_dorm.2.2.1, h_dorm.2.2.2.1, h_dorm.2.2.2.2.1⟩
}

/--
Generator-Reuse Bound: whenever the same generator value appears at `z - 2` and `z' - 2`
for indices `2 ≤ z < z'` with `a(z') = 0`, the occurrence at `z - 2` caps `a(z' - 1)` by
`z' - z`.
-/
lemma generator_reuse_new_value_le_zero_dist (z z' : ℕ)
    (hz_ge : z ≥ 2) (h_lt : z < z') (hz' : vanEckNthTerm z' = 0)
    (h_same_gen : vanEckNthTerm (z' - 2) = vanEckNthTerm (z - 2)) :
    vanEckNthTerm (z' - 1) ≤ z' - z := by {
  have h_le := pre_zero_new_value_le_of_prior_occurrence z' (z - 2) hz'
    (by { omega }) (by { omega }) h_same_gen.symm
  omega
}

/--
Cooldown Consumption Lemma: in a `2`-free tail, firing a generator `v = a(z - 2)` resets
its dormancy at `z - 2`, so `v` cannot trigger a prefix-maximum jump at the immediately
following zero (`z < z'_prev`) nor until `z' - z > vanEckPrefixMax z'_prev`.
-/
lemma no_twos_generator_cooldown_after_use (N_0 z z'_prev z' : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hz_ge : z ≥ 2) (hz_le_prev : z ≤ z'_prev) (h_prev_lt : z'_prev < z')
    (hz'_gt : z' > N_0) (hz'_prev : vanEckNthTerm z'_prev = 0)
    (hz' : vanEckNthTerm z' = 0)
    (h_gap' : ∀ k, z'_prev < k → k < z' → vanEckNthTerm k ≠ 0)
    (h_jump' : vanEckPrefixMax z'_prev < vanEckPrefixMax z')
    (h_same_gen : vanEckNthTerm (z' - 2) = vanEckNthTerm (z - 2)) :
    z < z'_prev ∧ vanEckPrefixMax z'_prev < z' - z := by {
  have h_le_dist := generator_reuse_new_value_le_zero_dist z z' hz_ge
    (by { omega }) hz' h_same_gen
  have h_jump_spec := no_twos_prefixMax_jump_requires_dormant_generator N_0 z' z'_prev
    h_no_twos (by { omega }) hz' hz'_gt hz'_prev h_prev_lt h_gap' h_jump'
  have h_bounds' := no_twos_zero_gap_and_predecessor_bounds N_0 z' z'_prev
    h_no_twos (by { omega }) hz' hz'_gt hz'_prev h_prev_lt h_gap'
  exact ⟨by { omega }, by { omega }⟩
}

/--
Anchor-Slot Uniqueness: for any two zeros `2 ≤ z < z'`, the strictly most recent prior
occurrences `p = z - 2 - a(z - 1)` and `p' = z' - 2 - a(z' - 1)` of their generators are
distinct. Each index `p` can anchor at most one zero's pre-zero value across the sequence.
-/
lemma pre_zero_prior_anchor_unique (z z' : ℕ)
    (hz_ge : z ≥ 2) (h_lt : z < z')
    (hz : vanEckNthTerm z = 0) (hz' : vanEckNthTerm z' = 0) :
    z - 2 - vanEckNthTerm (z - 1) ≠ z' - 2 - vanEckNthTerm (z' - 1) := by {
  have h_spec := pre_zero_new_value_prior_occurrence_spec z hz hz_ge
  have h_spec' := pre_zero_new_value_prior_occurrence_spec z' hz' (by { omega })
  have h_uniq := vanEck_idx_sub_val_unique (z - 1) (z' - 1) h_spec.1 (by { omega })
  have hp_eq := h_spec.2.2.2.1
  have hp'_eq := h_spec'.2.2.2.1
  omega
}

/--
If a pre-zero birth value `a(z_1 - 1)` (`z_1 ≥ 2`) serves as the generator `a(z - 2)` of a
later zero `z > z_1`, then `z_1 + 3 ≤ z` and its prior-occurrence anchor satisfies
`z_1 - 1 ≤ z - 2 - a(z - 1)`.
-/
lemma birth_as_later_generator_min_dist (z_1 z : ℕ)
    (hz1_ge : z_1 ≥ 2) (h_lt : z_1 < z)
    (hz1 : vanEckNthTerm z_1 = 0) (hz : vanEckNthTerm z = 0)
    (h_gen : vanEckNthTerm (z - 2) = vanEckNthTerm (z_1 - 1)) :
    z_1 + 3 ≤ z ∧ z_1 - 1 ≤ z - 2 - vanEckNthTerm (z - 1) := by {
  have h_s1 := pre_zero_new_value_prior_occurrence_spec z_1 hz1 hz1_ge
  have h_sz := pre_zero_new_value_prior_occurrence_spec z hz (by { omega })
  have hz_ne1 : z ≠ z_1 + 1 := by {
    intro hc
    have h0 := h_sz.1
    have h_sub : z_1 + 1 - 1 = z_1 := by { omega }
    rw [hc, h_sub, hz1] at h0
    omega
  }
  have hz_ne2 : z ≠ z_1 + 2 := by {
    intro hc
    have h_eq := h_gen
    have h_sub : z_1 + 2 - 2 = z_1 := by { omega }
    rw [hc, h_sub, hz1] at h_eq
    have h0 := h_s1.1
    omega
  }
  have hp_val : vanEckNthTerm (z - 2 - vanEckNthTerm (z - 1)) =
      vanEckNthTerm (z_1 - 1) := by { rw [h_sz.2.2.2.2.1, h_gen] }
  have hp_ge : z_1 - 1 ≤ z - 2 - vanEckNthTerm (z - 1) := by {
    by_contra hp_lt
    exact h_s1.2.1 (z - 2 - vanEckNthTerm (z - 1)) (by { omega }) hp_val
  }
  exact ⟨by { omega }, hp_ge⟩
}

/--
For any two zeros `2 ≤ z < z'` sharing the same generator `a(z - 2) = a(z' - 2)`, `z - 2`
lies at or before `z'`'s prior-occurrence anchor `z' - 2 - a(z' - 1)`, so their half-open
dormancy intervals `[z - 2 - a(z - 1), z - 2)` and `[z' - 2 - a(z' - 1), z' - 2)` are
disjoint.
-/
lemma generator_dormancy_intervals_disjoint (z z' : ℕ)
    (hz_ge : z ≥ 2) (h_lt : z < z')
    (hz : vanEckNthTerm z = 0) (hz' : vanEckNthTerm z' = 0)
    (h_same : vanEckNthTerm (z - 2) = vanEckNthTerm (z' - 2)) :
    z - 2 ≤ z' - 2 - vanEckNthTerm (z' - 1) ∧
      Disjoint (Finset.Ico (z - 2 - vanEckNthTerm (z - 1)) (z - 2))
        (Finset.Ico (z' - 2 - vanEckNthTerm (z' - 1)) (z' - 2)) := by {
  have h_sz := pre_zero_new_value_prior_occurrence_spec z hz hz_ge
  have h_sz' := pre_zero_new_value_prior_occurrence_spec z' hz' (by { omega })
  have hp_ge : z - 2 ≤ z' - 2 - vanEckNthTerm (z' - 1) := by {
    by_contra hp_lt
    have hz_pos := h_sz.1
    have hz_eq := h_sz.2.2.2.1
    have h_ne := h_sz'.2.2.2.2.2 (z - 2) (by { omega }) (by { omega })
    exact h_ne h_same
  }
  refine ⟨hp_ge, Finset.disjoint_left.mpr ?_⟩
  intro x hx1 hx2
  have hx1' := Finset.mem_Ico.mp hx1
  have hx2' := Finset.mem_Ico.mp hx2
  omega
}

/--
Single-Generator Disjoint-Interval Packing: for any finite set `S` of zeros `z ≥ 2` sharing
generator `v = a(z - 2)` with `A_0 ≤ z - 2 - a(z - 1)` and `z ≤ B`, the sum of their newly
created values `a(z - 1)` is at most `(B - 2) - A_0`.
-/
lemma single_generator_anchor_dormancy_sum_le (S : Finset ℕ) (v A_0 B : ℕ)
    (hS : ∀ z ∈ S, z ≥ 2 ∧ vanEckNthTerm z = 0 ∧ vanEckNthTerm (z - 2) = v ∧
      A_0 ≤ z - 2 - vanEckNthTerm (z - 1) ∧ z ≤ B) :
    (∑ z ∈ S, vanEckNthTerm (z - 1)) ≤ (B - 2) - A_0 := by {
  let f : ℕ → Finset ℕ := fun z => Finset.Ico (z - 2 - vanEckNthTerm (z - 1)) (z - 2)
  have h_pw : (S : Set ℕ).PairwiseDisjoint f := by {
    intro z hz z' hz' hne
    rcases lt_trichotomy z z' with hlt | heq | hgt
    · exact (generator_dormancy_intervals_disjoint z z' (hS z hz).1 hlt
        (hS z hz).2.1 (hS z' hz').2.1 ((hS z hz).2.2.1.trans (hS z' hz').2.2.1.symm)).2
    · exact False.elim (hne heq)
    · exact (generator_dormancy_intervals_disjoint z' z (hS z' hz').1 hgt
        (hS z' hz').2.1 (hS z hz).2.1 ((hS z' hz').2.2.1.trans (hS z hz).2.2.1.symm)).2.symm
  }
  have h_sub : S.biUnion f ⊆ Finset.Ico A_0 (B - 2) := by {
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨z, hz, hxf⟩
    have hxf' := Finset.mem_Ico.mp hxf
    have hz_p := hS z hz
    exact Finset.mem_Ico.mpr ⟨by { omega }, by { omega }⟩
  }
  have h_card_le := Finset.card_le_card h_sub
  rw [Finset.card_biUnion h_pw, Nat.card_Ico] at h_card_le
  have h_sum_eq : (∑ z ∈ S, (f z).card) = ∑ z ∈ S, vanEckNthTerm (z - 1) := by {
    apply Finset.sum_congr rfl
    intro z hz
    have h_sz := pre_zero_new_value_prior_occurrence_spec z (hS z hz).2.1 (hS z hz).1
    rw [Nat.card_Ico]
    exact h_sz.2.2.2.1.symm
  }
  rw [h_sum_eq] at h_card_le
  exact h_card_le
}

/--
Single-Generator Window Cooldown Bound: if every zero `z ∈ S` lies in `[A, B]`, shares
generator `v = a(z - 2)`, and emits `H < a(z - 1)`, then `(S.card - 1) * (H + 1) ≤ B - A` and
`S.card * (H + 1) ≤ (B - A) + (H + 1)`.
-/
lemma single_generator_window_cooldown_bound (S : Finset ℕ) (v H A B : ℕ)
    (hS : ∀ z ∈ S, z ≥ 2 ∧ A ≤ z ∧ z ≤ B ∧ vanEckNthTerm z = 0 ∧
      vanEckNthTerm (z - 2) = v ∧ H < vanEckNthTerm (z - 1)) :
    (S.card - 1) * (H + 1) ≤ B - A ∧ S.card * (H + 1) ≤ (B - A) + (H + 1) := by {
  by_cases hne : S.Nonempty
  · let z_0 := S.min' hne
    have hz0_mem : z_0 ∈ S := Finset.min'_mem S hne
    have hz0_p := hS z_0 hz0_mem
    have h_er : ∀ z ∈ S.erase z_0, z ≥ 2 ∧ vanEckNthTerm z = 0 ∧
        vanEckNthTerm (z - 2) = v ∧ z_0 - 2 ≤ z - 2 - vanEckNthTerm (z - 1) ∧ z ≤ B := by {
      intro z hz
      have hz_mem := Finset.mem_of_mem_erase hz
      have hz_p := hS z hz_mem
      have hz_lt : z_0 < z :=
        lt_of_le_of_ne (Finset.min'_le S z hz_mem) (Finset.ne_of_mem_erase hz).symm
      have h_disj := generator_dormancy_intervals_disjoint z_0 z hz0_p.1 hz_lt
        hz0_p.2.2.2.1 hz_p.2.2.2.1 (hz0_p.2.2.2.2.1.trans hz_p.2.2.2.2.1.symm)
      exact ⟨hz_p.1, hz_p.2.2.2.1, hz_p.2.2.2.2.1, h_disj.1, hz_p.2.2.1⟩
    }
    have h_sum_le := single_generator_anchor_dormancy_sum_le (S.erase z_0) v (z_0 - 2) B h_er
    have h_low : (S.erase z_0).card * (H + 1) ≤ ∑ z ∈ S.erase z_0, vanEckNthTerm (z - 1) := by {
      have h_le : (∑ _z ∈ S.erase z_0, (H + 1)) ≤ ∑ z ∈ S.erase z_0, vanEckNthTerm (z - 1) :=
        Finset.sum_le_sum (fun z hz => (hS z (Finset.mem_of_mem_erase hz)).2.2.2.2.2)
      rw [Finset.sum_const, smul_eq_mul] at h_le
      exact h_le
    }
    have h_card_er : (S.erase z_0).card = S.card - 1 := Finset.card_erase_of_mem hz0_mem
    have h_card_pos : 1 ≤ S.card := Finset.card_pos.mpr hne
    rw [h_card_er] at h_low
    have h_first : (S.card - 1) * (H + 1) ≤ B - A := by { omega }
    have h_mul : S.card * (H + 1) = (S.card - 1) * (H + 1) + (H + 1) := by {
      calc S.card * (H + 1) = ((S.card - 1) + 1) * (H + 1) := by {
            rw [Nat.sub_add_cancel h_card_pos]
          }
        _ = (S.card - 1) * (H + 1) + (H + 1) := Nat.succ_mul (S.card - 1) (H + 1)
    }
    exact ⟨h_first, by { omega }⟩
  · have h_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [h_empty, Finset.card_empty]
    simp
}

/--
Finite-Palette Anchor Cooldown Bound: for any finite set `J` of zeros `z ≥ 2` driven by a
generator palette `1 ≤ a(z - 2) ≤ W` with `A_0 ≤ z - 2 - a(z - 1)`, `z ≤ B`, and `H < a(z - 1)`,
both `J.card * (H + 1) ≤ ∑_{z ∈ J} a(z - 1)` and `∑_{z ∈ J} a(z - 1) ≤ W * ((B - 2) - A_0)`.
-/
lemma finite_palette_anchor_cooldown_bound (J : Finset ℕ) (W H A_0 B : ℕ)
    (hJ : ∀ z ∈ J, z ≥ 2 ∧ vanEckNthTerm z = 0 ∧ 1 ≤ vanEckNthTerm (z - 2) ∧
      vanEckNthTerm (z - 2) ≤ W ∧ A_0 ≤ z - 2 - vanEckNthTerm (z - 1) ∧
      z ≤ B ∧ H < vanEckNthTerm (z - 1)) :
    J.card * (H + 1) ≤ (∑ z ∈ J, vanEckNthTerm (z - 1)) ∧
      (∑ z ∈ J, vanEckNthTerm (z - 1)) ≤ W * ((B - 2) - A_0) := by {
  have h_low : J.card * (H + 1) ≤ ∑ z ∈ J, vanEckNthTerm (z - 1) := by {
    have h_le : (∑ _z ∈ J, (H + 1)) ≤ ∑ z ∈ J, vanEckNthTerm (z - 1) :=
      Finset.sum_le_sum (fun z hz => (hJ z hz).2.2.2.2.2.2)
    rw [Finset.sum_const, smul_eq_mul] at h_le
    exact h_le
  }
  have h_maps : ∀ z ∈ J, vanEckNthTerm (z - 2) ∈ Finset.Icc 1 W :=
    fun z hz => Finset.mem_Icc.mpr ⟨(hJ z hz).2.2.1, (hJ z hz).2.2.2.1⟩
  have h_fib := Finset.sum_fiberwise_of_maps_to (s := J) (t := Finset.Icc 1 W)
    (g := fun z => vanEckNthTerm (z - 2)) h_maps (fun z => vanEckNthTerm (z - 1))
  have h_up : (∑ v ∈ Finset.Icc 1 W,
      ∑ z ∈ J.filter (fun z => vanEckNthTerm (z - 2) = v), vanEckNthTerm (z - 1)) ≤
      ∑ _v ∈ Finset.Icc 1 W, ((B - 2) - A_0) := by {
    apply Finset.sum_le_sum
    intro v _hv
    apply single_generator_anchor_dormancy_sum_le _ v A_0 B
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzJ, hzv⟩
    have hp := hJ z hzJ
    exact ⟨hp.1, hp.2.1, hzv, hp.2.2.2.2.1, hp.2.2.2.2.2.1⟩
  }
  rw [h_fib, Finset.sum_const, Nat.card_Icc, smul_eq_mul] at h_up
  have hW : W + 1 - 1 = W := Nat.add_sub_cancel W 1
  rw [hW] at h_up
  exact ⟨h_low, h_up⟩
}

/--
Finite-Palette Window Cooldown Bound: for any finite set `J` of zeros `z ∈ [A, B]` (`z ≥ 2`)
driven by a generator palette `1 ≤ a(z - 2) ≤ W` with `H < a(z - 1)`,
`J.card * (H + 1) ≤ W * ((B - A) + (H + 1))`.
-/
lemma finite_palette_window_cooldown_bound (J : Finset ℕ) (W H A B : ℕ)
    (hJ : ∀ z ∈ J, z ≥ 2 ∧ A ≤ z ∧ z ≤ B ∧ vanEckNthTerm z = 0 ∧
      1 ≤ vanEckNthTerm (z - 2) ∧ vanEckNthTerm (z - 2) ≤ W ∧ H < vanEckNthTerm (z - 1)) :
    J.card * (H + 1) ≤ W * ((B - A) + (H + 1)) := by {
  have h_maps : ∀ z ∈ J, vanEckNthTerm (z - 2) ∈ Finset.Icc 1 W :=
    fun z hz => Finset.mem_Icc.mpr ⟨(hJ z hz).2.2.2.2.1, (hJ z hz).2.2.2.2.2.1⟩
  have h_fib := Finset.sum_fiberwise_of_maps_to (s := J) (t := Finset.Icc 1 W)
    (g := fun z => vanEckNthTerm (z - 2)) h_maps (fun _ => H + 1)
  rw [Finset.sum_const, smul_eq_mul] at h_fib
  have h_up : (∑ v ∈ Finset.Icc 1 W,
      ∑ _z ∈ J.filter (fun z => vanEckNthTerm (z - 2) = v), (H + 1)) ≤
      ∑ _v ∈ Finset.Icc 1 W, ((B - A) + (H + 1)) := by {
    apply Finset.sum_le_sum
    intro v _hv
    rw [Finset.sum_const, smul_eq_mul]
    apply (single_generator_window_cooldown_bound _ v H A B _).2
    intro z hz
    rcases Finset.mem_filter.mp hz with ⟨hzJ, hzv⟩
    have hp := hJ z hzJ
    exact ⟨hp.1, hp.2.1, hp.2.2.1, hp.2.2.2.1, hzv, hp.2.2.2.2.2.2⟩
  }
  rw [h_fib, Finset.sum_const, Nat.card_Icc, smul_eq_mul] at h_up
  have hW : W + 1 - 1 = W := Nat.add_sub_cancel W 1
  rw [hW] at h_up
  exact h_up
}

/--
`2`-Free Finite-Palette Jump Cooldown Bound: in a `2`-free tail past a zero `z_0 > N_0` with
`H ≤ vanEckPrefixMax z_0`, any finite set `J` of prefix-maximum jump zeros `z ∈ [A, B]`
(`z_0 < z`, `a(z - 2) ≤ W`) satisfies `J.card * (H + 1) ≤ W * ((B - A) + (H + 1))`.
-/
lemma no_twos_finite_palette_jump_window_bound (N_0 z_0 W H A B : ℕ) (J : Finset ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hz0_gt : N_0 < z_0) (hz0 : vanEckNthTerm z_0 = 0)
    (hH : H ≤ vanEckPrefixMax z_0)
    (hJ : ∀ z ∈ J, z_0 < z ∧ A ≤ z ∧ z ≤ B ∧ vanEckNthTerm z = 0 ∧
      vanEckNthTerm (z - 2) ≤ W ∧ vanEckPrefixMax (lastZero (z - 1)) < vanEckPrefixMax z) :
    J.card * (H + 1) ≤ W * ((B - A) + (H + 1)) := by {
  apply finite_palette_window_cooldown_bound J W H A B
  intro z hz
  have hp := hJ z hz
  let z_prev := lastZero (z - 1)
  have hzp_le : z_prev ≤ z - 1 := lastZero_le (z - 1)
  have hzp_zero : vanEckNthTerm z_prev = 0 := vanEck_lastZero_is_zero (z - 1)
  have hz0_le_zp : z_0 ≤ z_prev := by {
    by_contra hc
    exact no_zero_after_lastZero (z - 1) z_0 (by { omega }) (by { omega }) hz0
  }
  have h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0 :=
    fun k hk1 hk2 => no_zero_after_lastZero (z - 1) k hk1 (by { omega })
  have h_dorm := no_twos_prefixMax_jump_requires_dormant_generator N_0 z z_prev
    h_no_twos (by { omega }) hp.2.2.2.1 (by { omega }) hzp_zero (by { omega }) h_gap hp.2.2.2.2.2
  have h_mono := vanEckPrefixMax_mono z_0 z_prev hz0_le_zp
  have h_H_lt : H < vanEckNthTerm (z - 1) :=
    Nat.lt_of_le_of_lt (Nat.le_trans hH h_mono) (hp.2.2.2.2.2.trans_eq h_dorm.1)
  exact ⟨by { omega }, hp.2.1, hp.2.2.1, hp.2.2.2.1, h_dorm.2.1, hp.2.2.2.2.1, h_H_lt⟩
}

/--
Every positive generator `a(z - 2) > 0` before a zero `z ≥ 2` has a unique birth zero `z_b`
(`3 ≤ z_b`, `z_b + 3 ≤ z`, `a(z_b) = 0`, `a(z_b - 1) = a(z - 2)`).
-/
lemma pos_generator_has_unique_birth_zero (z : ℕ)
    (hz_ge : z ≥ 2) (hz : vanEckNthTerm z = 0) (hgen_pos : 0 < vanEckNthTerm (z - 2)) :
    ∃ z_b, 3 ≤ z_b ∧ z_b + 3 ≤ z ∧ vanEckNthTerm z_b = 0 ∧
      vanEckNthTerm (z_b - 1) = vanEckNthTerm (z - 2) ∧
      (∀ i < z_b - 1, vanEckNthTerm i ≠ vanEckNthTerm (z - 2)) ∧
      ∀ z_b', 1 ≤ z_b' → vanEckNthTerm z_b' = 0 →
        vanEckNthTerm (z_b' - 1) = vanEckNthTerm (z - 2) → z_b' = z_b := by {
  have h_ex : ∃ i, vanEckNthTerm i = vanEckNthTerm (z - 2) := ⟨z - 2, rfl⟩
  let b := Nat.find h_ex
  have hb_eq : vanEckNthTerm b = vanEckNthTerm (z - 2) := Nat.find_spec h_ex
  have hb_min : ∀ i < b, vanEckNthTerm i ≠ vanEckNthTerm b :=
    fun i hi hc => Nat.find_min h_ex hi (hc.trans hb_eq)
  have hb_le : b ≤ z - 2 := Nat.find_min' h_ex rfl
  have hb_ge2 : 2 ≤ b := by {
    have hb0 : b ≠ 0 := by {
      intro hc
      rw [hc] at hb_eq
      have h0 : vanEckNthTerm 0 = 0 := rfl
      rw [h0] at hb_eq
      omega
    }
    have hb1 : b ≠ 1 := by {
      intro hc
      rw [hc] at hb_eq
      have h1 : vanEckNthTerm 1 = 0 := rfl
      rw [h1] at hb_eq
      omega
    }
    omega
  }
  have hzb_zero : vanEckNthTerm (b + 1) = 0 := new_value_next_is_zero b hb_min
  have h_sz := pre_zero_new_value_prior_occurrence_spec z hz hz_ge
  have hb_ne_z2 : b ≠ z - 2 := by {
    intro hc
    have h_eq0 := hzb_zero
    have h_idx : b + 1 = z - 1 := by { omega }
    rw [h_idx] at h_eq0
    have hz1_pos := h_sz.1
    omega
  }
  have h_dist := birth_as_later_generator_min_dist (b + 1) z (by { omega }) (by { omega })
    hzb_zero hz hb_eq.symm
  refine ⟨b + 1, by { omega }, h_dist.1, hzb_zero, hb_eq, ?_, ?_⟩
  · intro i hi
    have h_sub : b + 1 - 1 = b := rfl
    rw [h_sub] at hi
    rw [← hb_eq]
    exact hb_min i hi
  · intro z_b' hzb'_ge hzb'_zero hzb'_eq
    by_contra hne
    have h_inj := zero_predecessors_inj (i := z_b' - 1) (j := b)
      (by { have h : z_b' - 1 + 1 = z_b' := by { omega }; rw [h]; exact hzb'_zero })
      hzb_zero (by { omega })
    exact h_inj (hzb'_eq.trans hb_eq.symm)
}

/--
Any index `m` with `0 < vanEckNthTerm m` satisfies `m ≥ 2` and `vanEckNthTerm m ≤ m - 1`.
-/
lemma pos_vanEckNthTerm_ge_two (m : ℕ) (h_pos : 0 < vanEckNthTerm m) :
    m ≥ 2 ∧ vanEckNthTerm m ≤ m - 1 := by {
  have hm_ge2 : m ≥ 2 := by {
    by_contra hc
    interval_cases m
    · have h0 : vanEckNthTerm 0 = 0 := rfl
      omega
    · have h1 : vanEckNthTerm 1 = 0 := rfl
      omega
  }
  exact ⟨hm_ge2, a_le_idx_minus_one hm_ge2 h_pos⟩
}

/--
All-Index Dormancy Disjointness: for any `1 ≤ m_1 < m_2` sharing the same predecessor symbol
`a(m_1 - 1) = a(m_2 - 1)` with `0 < a(m_2)`, `m_1 - 1 ≤ m_2 - 1 - a(m_2)`, `a(m_2) ≤ m_2 - m_1`,
and the dormancy intervals `[m_1 - 1 - a(m_1), m_1 - 1)` and `[m_2 - 1 - a(m_2), m_2 - 1)` are
disjoint.
-/
lemma all_index_dormancy_intervals_disjoint (m_1 m_2 : ℕ)
    (hm1_ge : m_1 ≥ 1) (h_lt : m_1 < m_2) (hm2_pos : 0 < vanEckNthTerm m_2)
    (h_same : vanEckNthTerm (m_1 - 1) = vanEckNthTerm (m_2 - 1)) :
    m_1 - 1 ≤ m_2 - 1 - vanEckNthTerm m_2 ∧
      vanEckNthTerm m_2 ≤ m_2 - m_1 ∧
      Disjoint (Finset.Ico (m_1 - 1 - vanEckNthTerm m_1) (m_1 - 1))
        (Finset.Ico (m_2 - 1 - vanEckNthTerm m_2) (m_2 - 1)) := by {
  have hm2_b := pos_vanEckNthTerm_ge_two m_2 hm2_pos
  have h_occ := pos_value_most_recent_occurrence m_2 (vanEckNthTerm m_2) hm2_b.1 rfl hm2_pos
  have hp_ge : m_1 - 1 ≤ m_2 - 1 - vanEckNthTerm m_2 := by {
    by_contra hp_lt
    exact h_occ.2.2 (m_1 - 1) (by { omega }) (by { omega }) h_same
  }
  refine ⟨hp_ge, by { omega }, Finset.disjoint_left.mpr ?_⟩
  intro x hx1 hx2
  have hx1' := Finset.mem_Ico.mp hx1
  have hx2' := Finset.mem_Ico.mp hx2
  omega
}

/--
All-Index Single-Symbol Packing: for any finite set `S` of indices `m ≤ B` with `0 < a(m)`,
`a(m - 1) = v`, and `A_0 ≤ m - 1 - a(m)`, the sum `∑_{m ∈ S} a(m)` is at most `(B - 1) - A_0`.
-/
lemma single_symbol_all_index_dormancy_sum_le (S : Finset ℕ) (v A_0 B : ℕ)
    (hS : ∀ m ∈ S, 0 < vanEckNthTerm m ∧ vanEckNthTerm (m - 1) = v ∧
      A_0 ≤ m - 1 - vanEckNthTerm m ∧ m ≤ B) :
    (∑ m ∈ S, vanEckNthTerm m) ≤ (B - 1) - A_0 := by {
  let f : ℕ → Finset ℕ := fun m => Finset.Ico (m - 1 - vanEckNthTerm m) (m - 1)
  have h_pw : (S : Set ℕ).PairwiseDisjoint f := by {
    intro m hm m' hm' hne
    have hm_ge := (pos_vanEckNthTerm_ge_two m (hS m hm).1).1
    have hm'_ge := (pos_vanEckNthTerm_ge_two m' (hS m' hm').1).1
    rcases lt_trichotomy m m' with hlt | heq | hgt
    · exact (all_index_dormancy_intervals_disjoint m m' (by { omega }) hlt (hS m' hm').1
        ((hS m hm).2.1.trans (hS m' hm').2.1.symm)).2.2
    · exact False.elim (hne heq)
    · exact (all_index_dormancy_intervals_disjoint m' m (by { omega }) hgt (hS m hm).1
        ((hS m' hm').2.1.trans (hS m hm).2.1.symm)).2.2.symm
  }
  have h_sub : S.biUnion f ⊆ Finset.Ico A_0 (B - 1) := by {
    intro x hx
    rcases Finset.mem_biUnion.mp hx with ⟨m, hm, hxf⟩
    have hxf' := Finset.mem_Ico.mp hxf
    have hm_p := hS m hm
    exact Finset.mem_Ico.mpr ⟨by { omega }, by { omega }⟩
  }
  have h_card_le := Finset.card_le_card h_sub
  rw [Finset.card_biUnion h_pw, Nat.card_Ico] at h_card_le
  have h_sum_eq : (∑ m ∈ S, (f m).card) = ∑ m ∈ S, vanEckNthTerm m := by {
    apply Finset.sum_congr rfl
    intro m hm
    have hm_b := pos_vanEckNthTerm_ge_two m (hS m hm).1
    rw [Nat.card_Ico]
    omega
  }
  rw [h_sum_eq] at h_card_le
  exact h_card_le
}

/--
All-Index Single-Symbol Window Cooldown Bound: if every `m ∈ S` lies in `[A, B]`, shares
predecessor `a(m - 1) = v`, and emits `H < a(m)`, then `(S.card - 1) * (H + 1) ≤ B - A` and
`S.card * (H + 1) ≤ (B - A) + (H + 1)`.
-/
lemma single_symbol_all_index_window_cooldown_bound (S : Finset ℕ) (v H A B : ℕ)
    (hS : ∀ m ∈ S, A ≤ m ∧ m ≤ B ∧ vanEckNthTerm (m - 1) = v ∧ H < vanEckNthTerm m) :
    (S.card - 1) * (H + 1) ≤ B - A ∧ S.card * (H + 1) ≤ (B - A) + (H + 1) := by {
  by_cases hne : S.Nonempty
  · let m_0 := S.min' hne
    have hm0_mem : m_0 ∈ S := Finset.min'_mem S hne
    have hm0_p := hS m_0 hm0_mem
    have hm0_b := pos_vanEckNthTerm_ge_two m_0 (by { omega })
    have h_er : ∀ m ∈ S.erase m_0, 0 < vanEckNthTerm m ∧ vanEckNthTerm (m - 1) = v ∧
        m_0 - 1 ≤ m - 1 - vanEckNthTerm m ∧ m ≤ B := by {
      intro m hm
      have hm_mem := Finset.mem_of_mem_erase hm
      have hm_p := hS m hm_mem
      have hm_lt : m_0 < m :=
        lt_of_le_of_ne (Finset.min'_le S m hm_mem) (Finset.ne_of_mem_erase hm).symm
      have h_disj := all_index_dormancy_intervals_disjoint m_0 m (by { omega }) hm_lt
        (by { omega }) (hm0_p.2.2.1.trans hm_p.2.2.1.symm)
      exact ⟨by { omega }, hm_p.2.2.1, h_disj.1, hm_p.2.1⟩
    }
    have h_sum_le := single_symbol_all_index_dormancy_sum_le (S.erase m_0) v (m_0 - 1) B h_er
    have h_low : (S.erase m_0).card * (H + 1) ≤ ∑ m ∈ S.erase m_0, vanEckNthTerm m := by {
      have h_le : (∑ _m ∈ S.erase m_0, (H + 1)) ≤ ∑ m ∈ S.erase m_0, vanEckNthTerm m :=
        Finset.sum_le_sum (fun m hm => (hS m (Finset.mem_of_mem_erase hm)).2.2.2)
      rw [Finset.sum_const, smul_eq_mul] at h_le
      exact h_le
    }
    have h_card_er : (S.erase m_0).card = S.card - 1 := Finset.card_erase_of_mem hm0_mem
    have h_card_pos : 1 ≤ S.card := Finset.card_pos.mpr hne
    rw [h_card_er] at h_low
    have h_first : (S.card - 1) * (H + 1) ≤ B - A := by { omega }
    have h_mul : S.card * (H + 1) = (S.card - 1) * (H + 1) + (H + 1) := by {
      calc S.card * (H + 1) = ((S.card - 1) + 1) * (H + 1) := by {
            rw [Nat.sub_add_cancel h_card_pos]
          }
        _ = (S.card - 1) * (H + 1) + (H + 1) := Nat.succ_mul (S.card - 1) (H + 1)
    }
    exact ⟨h_first, by { omega }⟩
  · have h_empty : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hne
    rw [h_empty, Finset.card_empty]
    simp
}

/--
Arbitrary Finite-Palette All-Index Cooldown Bound: for any finite palette `P` and finite set `M`
of indices `m ∈ [A, B]` whose predecessor `a(m - 1)` lies in `P` and emits `H < a(m)`,
`M.card * (H + 1) ≤ P.card * ((B - A) + (H + 1))`.
-/
lemma palette_set_all_index_window_cooldown_bound (M P : Finset ℕ) (H A B : ℕ)
    (hM : ∀ m ∈ M, A ≤ m ∧ m ≤ B ∧ vanEckNthTerm (m - 1) ∈ P ∧ H < vanEckNthTerm m) :
    M.card * (H + 1) ≤ P.card * ((B - A) + (H + 1)) := by {
  have h_maps : ∀ m ∈ M, vanEckNthTerm (m - 1) ∈ P := fun m hm => (hM m hm).2.2.1
  have h_fib := Finset.sum_fiberwise_of_maps_to (s := M) (t := P)
    (g := fun m => vanEckNthTerm (m - 1)) h_maps (fun _ => H + 1)
  rw [Finset.sum_const, smul_eq_mul] at h_fib
  have h_up : (∑ v ∈ P, ∑ _m ∈ M.filter (fun m => vanEckNthTerm (m - 1) = v), (H + 1)) ≤
      ∑ _v ∈ P, ((B - A) + (H + 1)) := by {
    apply Finset.sum_le_sum
    intro v _hv
    rw [Finset.sum_const, smul_eq_mul]
    apply (single_symbol_all_index_window_cooldown_bound _ v H A B _).2
    intro m hm
    rcases Finset.mem_filter.mp hm with ⟨hmM, hmv⟩
    have hp := hM m hmM
    exact ⟨hp.1, hp.2.1, hmv, hp.2.2.2⟩
  }
  rw [h_fib, Finset.sum_const, smul_eq_mul] at h_up
  exact h_up
}

/--
First-Entry Bounded-Palette Gate: for any `z_prev < z` with `a(z_prev) = 0` and `H < a(z - 1)`,
there is an earliest index `m ∈ (z_prev, z - 1]` with `a(m - 1) ≤ H` and `H < a(m)`.
-/
lemma zero_block_first_entry_above_threshold (z_prev z H : ℕ)
    (h_lt : z_prev < z) (hz_prev : vanEckNthTerm z_prev = 0)
    (h_large : H < vanEckNthTerm (z - 1)) :
    ∃ m, z_prev < m ∧ m ≤ z - 1 ∧ vanEckNthTerm (m - 1) ≤ H ∧ H < vanEckNthTerm m ∧
      ∀ k, z_prev ≤ k → k < m → vanEckNthTerm k ≤ H := by {
  have hzp_lt_z1 : z_prev < z - 1 := by {
    by_contra hc
    have heq : z - 1 = z_prev := by { omega }
    rw [heq, hz_prev] at h_large
    omega
  }
  have h_ex : ∃ m, z_prev < m ∧ m ≤ z - 1 ∧ H < vanEckNthTerm m :=
    ⟨z - 1, hzp_lt_z1, le_rfl, h_large⟩
  let m := Nat.find h_ex
  have hm_spec : z_prev < m ∧ m ≤ z - 1 ∧ H < vanEckNthTerm m := Nat.find_spec h_ex
  have hm_below : ∀ k, z_prev ≤ k → k < m → vanEckNthTerm k ≤ H := by {
    intro k hk_lo hk_hi
    by_cases hk_eq : k = z_prev
    · rw [hk_eq, hz_prev]
      omega
    · by_contra hk_gt
      exact Nat.find_min h_ex hk_hi ⟨by { omega }, by { omega }, by { omega }⟩
  }
  exact ⟨m, hm_spec.1, hm_spec.2.1, hm_below (m - 1) (by { omega }) (by { omega }),
    hm_spec.2.2, hm_below⟩
}

/--
Canonical gate index inside `(lastZero (z - 1), z - 1]` for any zero `z > z_0` (`a(z_0) = 0`)
emitting `H < a(z - 1)`.
-/
lemma zero_gate_idx_spec (z_0 z H : ℕ) (hz0 : vanEckNthTerm z_0 = 0)
    (hz_gt : z_0 < z) (h_large : H < vanEckNthTerm (z - 1)) :
    ∃ m, z_0 < m ∧ lastZero (z - 1) < m ∧ m ≤ z - 1 ∧
      vanEckNthTerm (m - 1) ≤ H ∧ H < vanEckNthTerm m := by {
  let z_prev := lastZero (z - 1)
  have hzp_le : z_prev ≤ z - 1 := lastZero_le (z - 1)
  have hzp_zero : vanEckNthTerm z_prev = 0 := vanEck_lastZero_is_zero (z - 1)
  have hz0_le_zp : z_0 ≤ z_prev := by {
    by_contra hc
    exact no_zero_after_lastZero (z - 1) z_0 (by { omega }) (by { omega }) hz0
  }
  rcases zero_block_first_entry_above_threshold z_prev z H (by { omega }) hzp_zero h_large with
    ⟨m, hm_gt, hm_le, hm_prev_le, hm_gt_H, _⟩
  exact ⟨m, by { omega }, hm_gt, hm_le, hm_prev_le, hm_gt_H⟩
}

/--
Bounded-Palette Gate Supply Theorem: every zero `z ∈ Z` (`z_0 < z ≤ B`, `a(z) = 0`, `a(z_0) = 0`)
emitting `H < a(z - 1)` crosses `H` inside `(lastZero (z - 1), z - 1]` from a predecessor in `P`
whenever `P` contains all values `≤ H` occurring in `[z_0, B)`, yielding
`Z.card * (H + 1) ≤ P.card * ((B - (z_0 + 1)) + (H + 1))`.
-/
theorem large_pre_zero_palette_gate_supply (Z P : Finset ℕ) (z_0 H B : ℕ)
    (hz0 : vanEckNthTerm z_0 = 0)
    (hP : ∀ k, z_0 ≤ k → k < B → vanEckNthTerm k ≤ H → vanEckNthTerm k ∈ P)
    (hZ : ∀ z ∈ Z, z_0 < z ∧ z ≤ B ∧ vanEckNthTerm z = 0 ∧ H < vanEckNthTerm (z - 1)) :
    Z.card * (H + 1) ≤ P.card * ((B - (z_0 + 1)) + (H + 1)) := by {
  classical
  let gate : ℕ → ℕ := fun z =>
    if h : z_0 < z ∧ H < vanEckNthTerm (z - 1) then
      Classical.choose (zero_gate_idx_spec z_0 z H hz0 h.1 h.2)
    else 0
  have hgate : ∀ z ∈ Z, z_0 < gate z ∧ lastZero (z - 1) < gate z ∧ gate z ≤ z - 1 ∧
      vanEckNthTerm (gate z - 1) ≤ H ∧ H < vanEckNthTerm (gate z) := by {
    intro z hz
    have hp := hZ z hz
    have hcond : z_0 < z ∧ H < vanEckNthTerm (z - 1) := ⟨hp.1, hp.2.2.2⟩
    have hch := Classical.choose_spec (zero_gate_idx_spec z_0 z H hz0 hcond.1 hcond.2)
    have hdef : gate z = Classical.choose (zero_gate_idx_spec z_0 z H hz0 hcond.1 hcond.2) :=
      dif_pos hcond
    rw [hdef]
    exact hch
  }
  have h_inj : Set.InjOn gate (Z : Set ℕ) := by {
    intro z hz z' hz' heq
    have hg := hgate z hz
    have hg' := hgate z' hz'
    rcases lt_trichotomy z z' with hlt | h_eq | hgt
    · exfalso
      have hz_le_zp' : z ≤ lastZero (z' - 1) := by {
        by_contra hc
        exact no_zero_after_lastZero (z' - 1) z (by { omega }) (by { omega }) (hZ z hz).2.2.1
      }
      omega
    · exact h_eq
    · exfalso
      have hz'_le_zp : z' ≤ lastZero (z - 1) := by {
        by_contra hc
        exact no_zero_after_lastZero (z - 1) z' (by { omega }) (by { omega }) (hZ z' hz').2.2.1
      }
      omega
  }
  have h_img : ∀ m ∈ Z.image gate, z_0 + 1 ≤ m ∧ m ≤ B ∧
      vanEckNthTerm (m - 1) ∈ P ∧ H < vanEckNthTerm m := by {
    intro m hm
    rcases Finset.mem_image.mp hm with ⟨z, hz, rfl⟩
    have hg := hgate z hz
    have hp := hZ z hz
    have hmemP := hP (gate z - 1) (by { omega }) (by { omega }) hg.2.2.2.1
    exact ⟨by { omega }, by { omega }, hmemP, hg.2.2.2.2⟩
  }
  have h_bnd := palette_set_all_index_window_cooldown_bound (Z.image gate) P H (z_0 + 1) B h_img
  rw [Finset.card_image_of_injOn h_inj] at h_bnd
  exact h_bnd
}

/--
Computable most-recent occurrence of symbol `v` strictly before index `m` in the Van Eck sequence.
-/
def lastOccBefore : ℕ → ℕ → Option ℕ
  | 0, _ => none
  | m + 1, v => if vanEckNthTerm m = v then some m else lastOccBefore m v

/--
`lastOccBefore m v = none` iff `v` never appears in `[0, m)`.
-/
lemma lastOccBefore_eq_none_iff (m v : ℕ) :
    lastOccBefore m v = none ↔ ∀ i < m, vanEckNthTerm i ≠ v := by {
  induction m with
  | zero =>
    simp [lastOccBefore]
  | succ k ih =>
    simp only [lastOccBefore]
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
If `lastOccBefore m v = some p`, then `p < m` is the strictly most recent occurrence of `v`
before `m`.
-/
lemma lastOccBefore_eq_some_spec (m v p : ℕ) (h : lastOccBefore m v = some p) :
    p < m ∧ vanEckNthTerm p = v ∧ ∀ j, p < j → j < m → vanEckNthTerm j ≠ v := by {
  induction m with
  | zero =>
    simp [lastOccBefore] at h
  | succ k ih =>
    simp only [lastOccBefore] at h
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
Exact Recurrence Preservation of `lastOccBefore`: `vanEckNthTerm (m + 1)` is `0` when
`lastOccBefore m (vanEckNthTerm m) = none` and `m - p` when it is `some p`.
-/
lemma vanEck_next_eq_of_lastOccBefore (m : ℕ) :
    vanEckNthTerm (m + 1) =
      match lastOccBefore m (vanEckNthTerm m) with
      | none => 0
      | some p => m - p := by {
  cases h_occ : lastOccBefore m (vanEckNthTerm m) with
  | none =>
    have h_new := (lastOccBefore_eq_none_iff m (vanEckNthTerm m)).mp h_occ
    cases m with
    | zero => rfl
    | succ k => exact (vanEck_mth_term_eq_zero_iff_prev_term_new k).mpr h_new
  | some p =>
    have hp := lastOccBefore_eq_some_spec m (vanEckNthTerm m) p h_occ
    have h_nz : vanEckNthTerm (m + 1) ≠ 0 := by {
      intro hz
      have h_ne := pre_zero_ne_prior_val (m + 1) p hz (by { omega }) (by { omega })
      have h_sub : m + 1 - 1 = m := rfl
      rw [h_sub] at h_ne
      exact h_ne hp.2.1.symm
    }
    have h_pos : 0 < vanEckNthTerm (m + 1) := Nat.pos_of_ne_zero h_nz
    have h_rec := pos_value_most_recent_occurrence (m + 1) (vanEckNthTerm (m + 1))
      (by { omega }) rfl h_pos
    have h_sub : m + 1 - 1 = m := rfl
    rw [h_sub] at h_rec
    rcases lt_trichotomy (m - vanEckNthTerm (m + 1)) p with hlt | heq | hgt
    · exact False.elim (h_rec.2.2 p hlt hp.1 hp.2.1)
    · have h_le : vanEckNthTerm (m + 1) ≤ m := (pos_vanEckNthTerm_ge_two (m + 1) h_pos).2
      dsimp only
      rw [← heq]
      exact (Nat.sub_sub_self h_le).symm
    · exact False.elim (hp.2.2 (m - vanEckNthTerm (m + 1)) hgt h_rec.1 h_rec.2.1)
}

/--
Age (`m - p ≥ 1`) of a live symbol `v` at index `m`, or `none` if `v` has not appeared in `[0, m)`.
-/
def symbolAge (m v : ℕ) : Option ℕ :=
  (lastOccBefore m v).map (fun p => m - p)

/--
Exact Transition Law for `symbolAge`: `a(m + 1) = (symbolAge m (a m)).getD 0`, the selected
symbol's age resets to `some 1`, and every other live symbol's age increments by `1`.
-/
lemma symbolAge_transitions (m : ℕ) :
    vanEckNthTerm (m + 1) = (symbolAge m (vanEckNthTerm m)).getD 0 ∧
      symbolAge (m + 1) (vanEckNthTerm m) = some 1 ∧
      ∀ w, w ≠ vanEckNthTerm m → symbolAge (m + 1) w = (symbolAge m w).map (· + 1) := by {
  refine ⟨?_, ?_, ?_⟩
  · rw [vanEck_next_eq_of_lastOccBefore m]
    unfold symbolAge
    cases lastOccBefore m (vanEckNthTerm m) with
    | none => rfl
    | some _ => rfl
  · unfold symbolAge lastOccBefore
    simp
  · intro w hw
    unfold symbolAge
    have h_step : lastOccBefore (m + 1) w = lastOccBefore m w := by {
      simp only [lastOccBefore]
      exact if_neg (Ne.symm hw)
    }
    rw [h_step]
    cases h_occ : lastOccBefore m w with
    | none => rfl
    | some p =>
      have hp_lt := (lastOccBefore_eq_some_spec m w p h_occ).1
      simp only [Option.map]
      congr 1
      omega
}

/--
Clamped age in `{0, ..., H}`: returns `d ∈ [1, H]` when `symbolAge m v = some d` with `d ≤ H`,
and `0` when `v` is unseen or dormant beyond `H`.
-/
def clampedAgeNat (H m v : ℕ) : ℕ :=
  match symbolAge m v with
  | none => 0
  | some d => if d ≤ H then d else 0

/--
Pure deterministic transition rule for `clampedAgeNat H`.
-/
def stepClampedAge (H cur : ℕ) (st : ℕ → ℕ) (w : ℕ) : ℕ :=
  if w = cur then
    if 1 ≤ H then 1 else 0
  else if st w = 0 ∨ H ≤ st w then
    0
  else
    st w + 1

/--
Bounds and output readout for `clampedAgeNat H`: values lie in `[0, H]`, and
`clampedAgeNat H m (vanEckNthTerm m) = d ↔ vanEckNthTerm (m + 1) = d` for all `1 ≤ d ≤ H`.
-/
lemma clampedAgeNat_le_and_output (H m : ℕ) :
    (∀ w, clampedAgeNat H m w ≤ H) ∧
      (∀ d, 1 ≤ d → d ≤ H →
        (clampedAgeNat H m (vanEckNthTerm m) = d ↔ vanEckNthTerm (m + 1) = d)) := by {
  have h_tr := symbolAge_transitions m
  refine ⟨?_, ?_⟩
  · intro w
    unfold clampedAgeNat
    cases symbolAge m w with
    | none => exact Nat.zero_le H
    | some d =>
      dsimp only
      split_ifs with hd
      · exact hd
      · exact Nat.zero_le H
  · intro d hd1 hdH
    rw [h_tr.1]
    unfold clampedAgeNat
    cases symbolAge m (vanEckNthTerm m) with
    | none =>
      dsimp only [Option.getD]
      omega
    | some d' =>
      dsimp only [Option.getD]
      split_ifs with hd'
      · omega
      · omega
}

/--
`clampedAgeNat H` evolves deterministically via `stepClampedAge` at every step `m`.
-/
lemma clampedAgeNat_step (H m w : ℕ) :
    clampedAgeNat H (m + 1) w =
      stepClampedAge H (vanEckNthTerm m) (clampedAgeNat H m) w := by {
  have h_tr := symbolAge_transitions m
  by_cases hw : w = vanEckNthTerm m
  · rw [hw, stepClampedAge, if_pos rfl]
    unfold clampedAgeNat
    rw [h_tr.2.1]
  · rw [stepClampedAge, if_neg hw]
    unfold clampedAgeNat
    rw [h_tr.2.2 w hw]
    cases h_occ : lastOccBefore m w with
    | none =>
      have h_sa : symbolAge m w = none := by { simp [symbolAge, h_occ] }
      rw [h_sa]
      simp
    | some p =>
      have hp_lt := (lastOccBefore_eq_some_spec m w p h_occ).1
      have h_sa : symbolAge m w = some (m - p) := by { simp [symbolAge, h_occ] }
      rw [h_sa]
      simp only [Option.map]
      by_cases hd_le : m - p ≤ H
      · rw [if_pos hd_le]
        by_cases hd_lt : m - p < H
        · have h_not : ¬ (m - p = 0 ∨ H ≤ m - p) := by { omega }
          rw [if_neg h_not, if_pos (by { omega })]
        · have h_or : m - p = 0 ∨ H ≤ m - p := Or.inr (by { omega })
          rw [if_pos h_or, if_neg (by { omega })]
      · rw [if_neg hd_le, if_pos (Or.inl rfl), if_neg (by { omega })]
}

/--
If the clamped palette state `(a(k), clampedAgeNat H k ↾ P)` repeats across `k_1 < k_2` at the
ends of a run `k ∈ [k_1, k_2]` staying inside `P ⊆ [1, H]`, then `vanEckNthTerm` is periodic of
period `k_2 - k_1` and nonzero from `k_1` onward.
-/
lemma palette_clamped_state_periodic_from_collision (P : Finset ℕ) (H k_1 k_2 : ℕ)
    (hP : ∀ v ∈ P, 1 ≤ v ∧ v ≤ H) (h_lt : k_1 < k_2)
    (h_run : ∀ k, k_1 ≤ k → k ≤ k_2 → vanEckNthTerm k ∈ P)
    (h_cur : vanEckNthTerm k_1 = vanEckNthTerm k_2)
    (h_st : ∀ w ∈ P, clampedAgeNat H k_1 w = clampedAgeNat H k_2 w) :
    ∀ t, vanEckNthTerm (k_1 + t) ∈ P ∧
      vanEckNthTerm (k_2 + t) = vanEckNthTerm (k_1 + t) ∧
      ∀ w ∈ P, clampedAgeNat H (k_2 + t) w = clampedAgeNat H (k_1 + t) w := by {
  intro t
  refine Nat.strong_induction_on t (fun t ih => ?_)
  cases t with
  | zero =>
    exact ⟨h_run k_1 le_rfl (Nat.le_of_lt h_lt), h_cur.symm, fun w hw => (h_st w hw).symm⟩
  | succ s =>
    have ih_s := ih s (Nat.lt_succ_self s)
    have h_next_mem : vanEckNthTerm (k_1 + (s + 1)) ∈ P := by {
      by_cases h_le_Q : s + 1 ≤ k_2 - k_1
      · exact h_run (k_1 + (s + 1)) (by { omega }) (by { omega })
      · let u := (s + 1) - (k_2 - k_1)
        have hu_lt : u < s + 1 := by { omega }
        have ih_u := ih u hu_lt
        have h_idx : k_1 + (s + 1) = k_2 + u := by { omega }
        rw [h_idx, ih_u.2.1]
        exact ih_u.1
    }
    have h_b := hP (vanEckNthTerm (k_1 + (s + 1))) h_next_mem
    have h_out1 := clampedAgeNat_le_and_output H (k_1 + s)
    have h_out2 := clampedAgeNat_le_and_output H (k_2 + s)
    have h_c1 : clampedAgeNat H (k_1 + s) (vanEckNthTerm (k_1 + s)) =
        vanEckNthTerm (k_1 + (s + 1)) := by {
      have h_assoc : k_1 + s + 1 = k_1 + (s + 1) := by { omega }
      exact (h_out1.2 _ h_b.1 h_b.2).mpr (by { rw [h_assoc] })
    }
    have h_c2 : clampedAgeNat H (k_2 + s) (vanEckNthTerm (k_2 + s)) =
        vanEckNthTerm (k_1 + (s + 1)) := by {
      rw [ih_s.2.1, ih_s.2.2 _ ih_s.1]
      exact h_c1
    }
    have h_val2 : vanEckNthTerm (k_2 + (s + 1)) = vanEckNthTerm (k_1 + (s + 1)) := by {
      have h_assoc : k_2 + s + 1 = k_2 + (s + 1) := by { omega }
      rw [← h_assoc]
      exact (h_out2.2 _ h_b.1 h_b.2).mp h_c2
    }
    refine ⟨h_next_mem, h_val2, ?_⟩
    intro w hw
    have ha1 : k_1 + (s + 1) = k_1 + s + 1 := by { omega }
    have ha2 : k_2 + (s + 1) = k_2 + s + 1 := by { omega }
    rw [ha1, ha2, clampedAgeNat_step H (k_2 + s) w, clampedAgeNat_step H (k_1 + s) w, ih_s.2.1]
    unfold stepClampedAge
    rw [ih_s.2.2 w hw]
}

/--
Finite-Palette Clamped-State Collision Obstruction: in any run `k ∈ [k_1, k_2]` (`k_1 < k_2`)
staying inside a finite palette `P ⊆ [1, H]`, `(a(k_1), clampedAgeNat H k_1 ↾ P)` and
`(a(k_2), clampedAgeNat H k_2 ↾ P)` cannot coincide.
-/
lemma palette_clamped_state_repeat_impossible (P : Finset ℕ) (H k_1 k_2 : ℕ)
    (hP : ∀ v ∈ P, 1 ≤ v ∧ v ≤ H) (h_lt : k_1 < k_2)
    (h_run : ∀ k, k_1 ≤ k → k ≤ k_2 → vanEckNthTerm k ∈ P)
    (h_cur : vanEckNthTerm k_1 = vanEckNthTerm k_2)
    (h_st : ∀ w ∈ P, clampedAgeNat H k_1 w = clampedAgeNat H k_2 w) :
    False := by {
  have h_per := palette_clamped_state_periodic_from_collision P H k_1 k_2
    hP h_lt h_run h_cur h_st
  apply no_periodic_nonzero_tail k_1 (k_2 - k_1) (by { omega })
  · intro m hm
    have h_m : m = k_1 + (m - k_1) := by { omega }
    have h_mQ : m + (k_2 - k_1) = k_2 + (m - k_1) := by { omega }
    rw [h_mQ, (h_per (m - k_1)).2.1, ← h_m]
  · intro m hm
    have h_m : m = k_1 + (m - k_1) := by { omega }
    have h_in := (h_per (m - k_1)).1
    rw [← h_m] at h_in
    have h_pos := (hP (vanEckNthTerm m) h_in).1
    omega
}

/--
Unconditional Bounded-Palette Zero-Free Run Bound: no run `A, A + 1, ..., A + L` of length
`L + 1 > P.card * (H + 1) ^ P.card` can remain entirely inside a positive palette `P ⊆ [1, H]`.
-/
theorem finite_palette_run_length_bound (P : Finset ℕ) (H A L : ℕ)
    (hP : ∀ v ∈ P, 1 ≤ v ∧ v ≤ H)
    (h_run : ∀ t ≤ L, vanEckNthTerm (A + t) ∈ P) :
    L + 1 ≤ P.card * (H + 1) ^ P.card := by {
  classical
  let State := { v // v ∈ P } × ({ w // w ∈ P } → Fin (H + 1))
  let encode : Fin (L + 1) → State := fun t =>
    (⟨vanEckNthTerm (A + t.val), h_run t.val (Nat.lt_succ_iff.mp t.isLt)⟩,
      fun w => ⟨clampedAgeNat H (A + t.val) w.val,
        Nat.lt_succ_of_le ((clampedAgeNat_le_and_output H (A + t.val)).1 w.val)⟩)
  have h_inj : Function.Injective encode := by {
    intro t_1 t_2 heq
    have h_cur : vanEckNthTerm (A + t_1.val) = vanEckNthTerm (A + t_2.val) :=
      congrArg (fun s => s.1.val) heq
    have h_st : ∀ w ∈ P, clampedAgeNat H (A + t_1.val) w = clampedAgeNat H (A + t_2.val) w := by {
      intro w hw
      exact congrArg Fin.val (congrFun (congrArg Prod.snd heq) ⟨w, hw⟩)
    }
    rcases lt_trichotomy t_1.val t_2.val with hlt | hval_eq | hgt
    · exfalso
      exact palette_clamped_state_repeat_impossible P H (A + t_1.val) (A + t_2.val) hP
        (by { omega }) (fun k hk1 hk2 => by {
          have hk_eq : k = A + (k - A) := by { omega }
          rw [hk_eq]
          exact h_run (k - A) (by { omega })
        }) h_cur h_st
    · exact Fin.ext hval_eq
    · exfalso
      exact palette_clamped_state_repeat_impossible P H (A + t_2.val) (A + t_1.val) hP
        (by { omega }) (fun k hk1 hk2 => by {
          have hk_eq : k = A + (k - A) := by { omega }
          rw [hk_eq]
          exact h_run (k - A) (by { omega })
        }) h_cur.symm (fun w hw => (h_st w hw).symm)
  }
  have h_card := Fintype.card_le_of_injective encode h_inj
  dsimp only [State] at h_card
  simp only [Fintype.card_fin, Fintype.card_prod, Fintype.card_coe, Fintype.card_fun] at h_card
  exact h_card
}

/--
Unconditional No-Stutter of `1`: the Van Eck sequence never emits two consecutive `1`s (`[1, 1]`),
as doing so collides the `{1}` clamped-age state of height `H = 1`.
-/
theorem vanEck_no_stutter_one (m : ℕ) :
    ¬ (vanEckNthTerm m = 1 ∧ vanEckNthTerm (m + 1) = 1) := by {
  rintro ⟨hm, hm1⟩
  have h_c0 : clampedAgeNat 1 m 1 = 1 := by {
    have h_out := (clampedAgeNat_le_and_output 1 m).2 1 le_rfl le_rfl
    rw [hm] at h_out
    exact h_out.mpr hm1
  }
  have h_c1 : clampedAgeNat 1 (m + 1) 1 = 1 := by {
    rw [clampedAgeNat_step 1 m 1, hm]
    rfl
  }
  exact palette_clamped_state_repeat_impossible ({1} : Finset ℕ) 1 m (m + 1)
    (fun v hv => by {
      rw [Finset.mem_singleton] at hv
      exact ⟨by { omega }, by { omega }⟩
    })
    (Nat.lt_succ_self m)
    (fun k hk1 hk2 => by {
      rw [Finset.mem_singleton]
      rcases eq_or_lt_of_le hk1 with rfl | hgt
      · exact hm
      · have hk_eq : k = m + 1 := by { omega }
        rw [hk_eq]
        exact hm1
    })
    (hm.trans hm1.symm)
    (fun w hw => by {
      rw [Finset.mem_singleton] at hw
      rw [hw, h_c0, h_c1]
    })
}

/--
Any stutter `a(k) = a(k + 1)` immediately emits `a(k + 2) = 1`.
-/
lemma vanEck_stutter_emits_one (k : ℕ) (h : vanEckNthTerm k = vanEckNthTerm (k + 1)) :
    vanEckNthTerm (k + 2) = 1 := by {
  have h_next := vanEck_next_eq_of_lastOccBefore (k + 1)
  have h_occ : lastOccBefore (k + 1) (vanEckNthTerm (k + 1)) = some k := by {
    simp only [lastOccBefore, if_pos h]
  }
  rw [h_occ] at h_next
  change vanEckNthTerm (k + 2) = k + 1 - k at h_next
  rw [h_next]
  omega
}

/--
Any alternating pair `a(k) = a(k + 2)` with `a(k + 1) ≠ a(k)` immediately emits `a(k + 3) = 2`.
-/
lemma vanEck_alt_pair_emits_two (k : ℕ)
    (h_eq : vanEckNthTerm k = vanEckNthTerm (k + 2))
    (h_ne : vanEckNthTerm (k + 1) ≠ vanEckNthTerm k) :
    vanEckNthTerm (k + 3) = 2 := by {
  have h_next := vanEck_next_eq_of_lastOccBefore (k + 2)
  have h_ne2 : vanEckNthTerm (k + 1) ≠ vanEckNthTerm (k + 2) := h_eq ▸ h_ne
  have h_occ : lastOccBefore (k + 2) (vanEckNthTerm (k + 2)) = some k := by {
    simp only [lastOccBefore, if_neg h_ne2, if_pos h_eq]
  }
  rw [h_occ] at h_next
  change vanEckNthTerm (k + 3) = k + 2 - k at h_next
  rw [h_next]
  omega
}

/--
Any distance-3 repeat `a(k) = a(k + 3)` with `a(k + 1) ≠ a(k)` and `a(k + 2) ≠ a(k)` emits `3`.
-/
lemma vanEck_gap_three_emits_three (k : ℕ)
    (h_eq : vanEckNthTerm k = vanEckNthTerm (k + 3))
    (h_ne1 : vanEckNthTerm (k + 1) ≠ vanEckNthTerm k)
    (h_ne2 : vanEckNthTerm (k + 2) ≠ vanEckNthTerm k) :
    vanEckNthTerm (k + 4) = 3 := by {
  have h_next := vanEck_next_eq_of_lastOccBefore (k + 3)
  have h_n2 : vanEckNthTerm (k + 2) ≠ vanEckNthTerm (k + 3) := h_eq ▸ h_ne2
  have h_n1 : vanEckNthTerm (k + 1) ≠ vanEckNthTerm (k + 3) := h_eq ▸ h_ne1
  have h_occ : lastOccBefore (k + 3) (vanEckNthTerm (k + 3)) = some k := by {
    simp only [lastOccBefore, if_neg h_n2, if_neg h_n1, if_pos h_eq]
  }
  rw [h_occ] at h_next
  change vanEckNthTerm (k + 4) = k + 3 - k at h_next
  rw [h_next]
  omega
}

/--
Since `vanEckNthTerm 1 = 0`, `1 ≤ lastZero m` holds for every `m ≥ 1`.
-/
lemma lastZero_pos_of_ge_one (m : ℕ) (hm : 1 ≤ m) : 1 ≤ lastZero m := by {
  by_contra hc
  have h1 : vanEckNthTerm 1 = 0 := rfl
  exact no_zero_after_lastZero m 1 (by { omega }) hm h1
}

/--
Every positive term `vanEckNthTerm m > 0` has a unique birth zero `z_b` (`3 ≤ z_b ≤ m + 1`,
`a(z_b) = 0`, `a(z_b - 1) = a(m)`).
-/
lemma pos_term_has_unique_birth_zero (m : ℕ) (h_pos : 0 < vanEckNthTerm m) :
    ∃ z_b, 3 ≤ z_b ∧ z_b ≤ m + 1 ∧ vanEckNthTerm z_b = 0 ∧
      vanEckNthTerm (z_b - 1) = vanEckNthTerm m ∧
      (∀ i < z_b - 1, vanEckNthTerm i ≠ vanEckNthTerm m) ∧
      ∀ z_b', 1 ≤ z_b' → vanEckNthTerm z_b' = 0 →
        vanEckNthTerm (z_b' - 1) = vanEckNthTerm m → z_b' = z_b := by {
  have h_ex : ∃ i, vanEckNthTerm i = vanEckNthTerm m := ⟨m, rfl⟩
  let b := Nat.find h_ex
  have hb_eq : vanEckNthTerm b = vanEckNthTerm m := Nat.find_spec h_ex
  have hb_min : ∀ i < b, vanEckNthTerm i ≠ vanEckNthTerm b :=
    fun i hi hc => Nat.find_min h_ex hi (hc.trans hb_eq)
  have hb_le : b ≤ m := Nat.find_min' h_ex rfl
  have hb_ge2 : 2 ≤ b := (pos_vanEckNthTerm_ge_two b (hb_eq.symm ▸ h_pos)).1
  have hzb_zero : vanEckNthTerm (b + 1) = 0 := new_value_next_is_zero b hb_min
  refine ⟨b + 1, by { omega }, by { omega }, hzb_zero, hb_eq, ?_, ?_⟩
  · intro i hi
    have h_sub : b + 1 - 1 = b := rfl
    rw [h_sub] at hi
    rw [← hb_eq]
    exact hb_min i hi
  · intro z_b' hzb'_ge hzb'_zero hzb'_eq
    by_contra hne
    have h_zbp : vanEckNthTerm (z_b' - 1 + 1) = 0 := by {
      have hidx : z_b' - 1 + 1 = z_b' := by { omega }
      rw [hidx]
      exact hzb'_zero
    }
    exact zero_predecessors_inj h_zbp hzb_zero (by { omega }) (hzb'_eq.trans hb_eq.symm)
}

/--
Post-Zero Gap-Return Specification (`2`-Free Tail):
For consecutive zeros `0 < z_prev < z` with `N_0 < z`, the zero gap `z - z_prev = a(z + 1)` has a
strictly most recent earlier occurrence `q = z + 1 - a(z + 2) ≤ z - 2` (`3 ≤ a(z + 2)`).
-/
lemma no_twos_post_zero_gap_return_spec (N_0 z z_prev : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hz_prev_pos : 0 < z_prev) (hz : vanEckNthTerm z = 0)
    (hz_gt : N_0 < z) (hz_prev : vanEckNthTerm z_prev = 0)
    (h_prev_lt : z_prev < z)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) :
    3 ≤ vanEckNthTerm (z + 2) ∧
      z + 1 - vanEckNthTerm (z + 2) ≤ z - 2 ∧
      vanEckNthTerm (z + 1 - vanEckNthTerm (z + 2)) = z - z_prev ∧
      ∀ j, z + 1 - vanEckNthTerm (z + 2) < j → j < z + 1 →
        vanEckNthTerm j ≠ z - z_prev := by {
  have h_dist := gap_between_zeros z z_prev hz (by { omega }) hz_prev h_prev_lt h_gap
  have h_ge3 := (no_twos_zero_gap_and_predecessor_bounds N_0 z z_prev h_no_twos
    hz_prev_pos hz hz_gt hz_prev h_prev_lt h_gap).1
  rcases finite_twos_implies_old_gaps N_0 h_no_twos z hz_gt hz with ⟨i, hi_lt, hi_eq⟩
  cases h_occ : lastOccBefore (z + 1) (vanEckNthTerm (z + 1)) with
  | none =>
    exact False.elim (((lastOccBefore_eq_none_iff _ _).mp h_occ) i hi_lt hi_eq)
  | some q =>
    have hq_sp := lastOccBefore_eq_some_spec (z + 1) (vanEckNthTerm (z + 1)) q h_occ
    have h_next := vanEck_next_eq_of_lastOccBefore (z + 1)
    rw [h_occ] at h_next
    change vanEckNthTerm (z + 2) = z + 1 - q at h_next
    have hq_ne_z : q ≠ z := by {
      intro heq
      rw [heq, hz, h_dist] at hq_sp
      omega
    }
    have hq_ne_z1 : q ≠ z - 1 := by {
      intro heq
      have h_eq2 : vanEckNthTerm (z - 1) = vanEckNthTerm (z - 1 + 2) := by {
        have hidx : z - 1 + 2 = z + 1 := by { omega }
        rw [hidx, ← heq]
        exact hq_sp.2.1
      }
      have h_ne0 : vanEckNthTerm (z - 1 + 1) ≠ vanEckNthTerm (z - 1) := by {
        have hidx : z - 1 + 1 = z := by { omega }
        rw [hidx, hz, ← heq, hq_sp.2.1, h_dist]
        omega
      }
      have h2 := vanEck_alt_pair_emits_two (z - 1) h_eq2 h_ne0
      have hidx2 : z - 1 + 3 = z + 2 := by { omega }
      rw [hidx2] at h2
      exact h_no_twos (z + 2) (by { omega }) h2
    }
    have hq_le : q ≤ z - 2 := by { omega }
    have hq_eq : z + 1 - vanEckNthTerm (z + 2) = q := by { omega }
    refine ⟨by { omega }, by { omega }, ?_, ?_⟩
    · rw [hq_eq, hq_sp.2.1, h_dist]
    · rw [hq_eq, ← h_dist]
      exact hq_sp.2.2
}

/--
Universal Lookback-Anchor Injectivity: for any distinct indices `i ≠ j` with `0 < a(i)` and
`0 < a(j)`, their lookback anchors `i - 1 - a(i)` and `j - 1 - a(j)` are distinct.
-/
lemma pos_lookback_anchor_unique (i j : ℕ)
    (hi_pos : 0 < vanEckNthTerm i) (hj_pos : 0 < vanEckNthTerm j) (hne : i ≠ j) :
    i - 1 - vanEckNthTerm i ≠ j - 1 - vanEckNthTerm j := by {
  have hi_ge := (pos_vanEckNthTerm_ge_two i hi_pos).1
  have hi_le := (pos_vanEckNthTerm_ge_two i hi_pos).2
  have hj_ge := (pos_vanEckNthTerm_ge_two j hj_pos).1
  have hj_le := (pos_vanEckNthTerm_ge_two j hj_pos).2
  rcases lt_trichotomy i j with hlt | rfl | hgt
  · have hu := vanEck_idx_sub_val_unique i j hi_pos hlt
    omega
  · exact False.elim (hne rfl)
  · have hu := vanEck_idx_sub_val_unique j i hj_pos hgt
    omega
}

/--
Post-Zero Gap-Anchor Uniqueness & Pre-Zero Disjointness (`2`-Free Tail):
Post-zero gap-return anchors `q(z) = z + 1 - a(z + 2)` are pairwise distinct across zeros
`N_0 < z < z'`, and disjoint from pre-zero generator anchors `p(z'')` whenever `z'' ≠ z + 3`.
-/
lemma no_twos_post_zero_gap_anchor_unique_and_disjoint (N_0 z : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hz_ge : 3 ≤ z) (hz_gt : N_0 < z) (hz : vanEckNthTerm z = 0) :
    (∀ z', z < z' → vanEckNthTerm z' = 0 →
      z + 1 - vanEckNthTerm (z + 2) ≠ z' + 1 - vanEckNthTerm (z' + 2)) ∧
    (∀ z'', 2 ≤ z'' → z'' ≠ z + 3 → vanEckNthTerm z'' = 0 →
      z + 1 - vanEckNthTerm (z + 2) ≠ z'' - 2 - vanEckNthTerm (z'' - 1)) := by {
  have hzp_pos : 0 < lastZero (z - 1) := lastZero_pos_of_ge_one (z - 1) (by { omega })
  have hzp_le : lastZero (z - 1) ≤ z - 1 := lastZero_le (z - 1)
  have hz2_ge3 := (no_twos_post_zero_gap_return_spec N_0 z (lastZero (z - 1)) h_no_twos hzp_pos
    hz hz_gt (vanEck_lastZero_is_zero (z - 1)) (by { omega })
    (fun k hk1 hk2 => no_zero_after_lastZero (z - 1) k hk1 (by { omega }))).1
  refine ⟨?_, ?_⟩
  · intro z' hlt hz'
    have hzp'_pos : 0 < lastZero (z' - 1) := lastZero_pos_of_ge_one (z' - 1) (by { omega })
    have hzp'_le : lastZero (z' - 1) ≤ z' - 1 := lastZero_le (z' - 1)
    have hz'2_ge3 := (no_twos_post_zero_gap_return_spec N_0 z' (lastZero (z' - 1)) h_no_twos
      hzp'_pos hz' (by { omega }) (vanEck_lastZero_is_zero (z' - 1)) (by { omega })
      (fun k hk1 hk2 => no_zero_after_lastZero (z' - 1) k hk1 (by { omega }))).1
    have hu := pos_lookback_anchor_unique (z + 2) (z' + 2)
      (by { omega }) (by { omega }) (by { omega })
    exact hu
  · intro z'' hz''_ge hne3 hz''
    have h_sz'' := pre_zero_new_value_prior_occurrence_spec z'' hz'' hz''_ge
    have hu := pos_lookback_anchor_unique (z + 2) (z'' - 1)
      (by { omega }) h_sz''.1 (by { omega })
    have hsub1 : z + 2 - 1 = z + 1 := rfl
    have hsub2 : z'' - 1 - 1 = z'' - 2 := by { omega }
    rw [hsub1, hsub2] at hu
    exact hu
}

/--
Zero-Gap Birth-Zero Strict Descent (`2`-Free Tail):
For consecutive zeros `0 < z_prev < z` with `N_0 < z`, the zero gap `z - z_prev` was born as the
pre-zero value `a(z_b - 1) = z - z_prev` of a unique strictly earlier zero `3 ≤ z_b ≤ z_prev < z`.
-/
lemma no_twos_zero_gap_birth_zero_strict_descent (N_0 z z_prev : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hz_prev_pos : 0 < z_prev) (hz : vanEckNthTerm z = 0)
    (hz_gt : N_0 < z) (hz_prev : vanEckNthTerm z_prev = 0)
    (h_prev_lt : z_prev < z)
    (h_gap : ∀ k, z_prev < k → k < z → vanEckNthTerm k ≠ 0) :
    ∃ z_b, 3 ≤ z_b ∧ z_b ≤ z_prev ∧ vanEckNthTerm z_b = 0 ∧
      vanEckNthTerm (z_b - 1) = z - z_prev ∧
      ∀ i < z_b - 1, vanEckNthTerm i ≠ z - z_prev := by {
  have h_dist := gap_between_zeros z z_prev hz (by { omega }) hz_prev h_prev_lt h_gap
  have h_ret := no_twos_post_zero_gap_return_spec N_0 z z_prev h_no_twos
    hz_prev_pos hz hz_gt hz_prev h_prev_lt h_gap
  have hz1_pos : 0 < vanEckNthTerm (z + 1) := by { omega }
  rcases pos_term_has_unique_birth_zero (z + 1) hz1_pos with
    ⟨z_b, hzb_ge3, _, hzb_zero, hzb_eq, hzb_min, _⟩
  rw [h_dist] at hzb_eq hzb_min
  have hzb_le_q : z_b - 1 ≤ z + 1 - vanEckNthTerm (z + 2) := by {
    by_contra hgt
    exact hzb_min (z + 1 - vanEckNthTerm (z + 2)) (by { omega }) h_ret.2.2.1
  }
  have hzb_lt_z : z_b < z := by { omega }
  have hzb_le_prev : z_b ≤ z_prev := by {
    by_contra hgt
    exact h_gap z_b (by { omega }) hzb_lt_z hzb_zero
  }
  exact ⟨z_b, hzb_ge3, hzb_le_prev, hzb_zero, hzb_eq, hzb_min⟩
}

/--
Chain of zeros linked by zero-gap birth: each step `z_b → z` satisfies `z_b ≤ lastZero (z - 1) < z`
and `vanEckNthTerm (z_b - 1) = z - lastZero (z - 1)`.
-/
inductive IsZeroGapBirthChain : ℕ → ℕ → Prop
  | refl (z : ℕ) (hz : vanEckNthTerm z = 0) : IsZeroGapBirthChain z z
  | step (z_base z_b z : ℕ) (h_prev : IsZeroGapBirthChain z_base z_b)
      (hz : vanEckNthTerm z = 0) (hzb_le : z_b ≤ lastZero (z - 1))
      (hz_lt : z_b < z)
      (h_birth : vanEckNthTerm (z_b - 1) = z - lastZero (z - 1)) :
      IsZeroGapBirthChain z_base z

/--
Zero-Gap Chain Termination Theorem (`2`-Free Tail):
Under `∀ m > N_0, vanEckNthTerm m ≠ 2`, every zero `z ≥ 3` traces back via strictly decreasing
zero-gap birth steps `IsZeroGapBirthChain` to a root zero `3 ≤ z_base ≤ max N_0 3`.
-/
theorem no_twos_zero_gap_chain_reaches_prefix (N_0 z : ℕ)
    (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2)
    (hz_ge : 3 ≤ z) (hz : vanEckNthTerm z = 0) :
    ∃ z_base, 3 ≤ z_base ∧ z_base ≤ max N_0 3 ∧
      vanEckNthTerm z_base = 0 ∧ IsZeroGapBirthChain z_base z := by {
  revert hz_ge hz
  refine Nat.strong_induction_on z (fun z ih hz_ge hz => ?_)
  by_cases h_le : z ≤ max N_0 3
  · exact ⟨z, hz_ge, h_le, hz, IsZeroGapBirthChain.refl z hz⟩
  · have hz_gt : N_0 < z := by { omega }
    let z_prev := lastZero (z - 1)
    have hzp_pos : 0 < z_prev := lastZero_pos_of_ge_one (z - 1) (by { omega })
    have hzp_le : z_prev ≤ z - 1 := lastZero_le (z - 1)
    rcases no_twos_zero_gap_birth_zero_strict_descent N_0 z z_prev h_no_twos hzp_pos hz hz_gt
        (vanEck_lastZero_is_zero (z - 1)) (by { omega })
        (fun k hk1 hk2 => no_zero_after_lastZero (z - 1) k hk1 (by { omega })) with
      ⟨z_b, hzb_ge3, hzb_le_zp, hzb_zero, hzb_eq, _⟩
    have hzb_lt : z_b < z := by { omega }
    rcases ih z_b hzb_lt hzb_ge3 hzb_zero with ⟨z_base, hb_ge3, hb_le, hb_zero, h_chain⟩
    exact ⟨z_base, hb_ge3, hb_le, hb_zero,
      IsZeroGapBirthChain.step z_base z_b z h_chain hz hzb_le_zp hzb_lt hzb_eq⟩
}

/--
Cardinalities of `[1, H] \ {2}` (`H - 1`) and `[0, H] \ {2}` (`H`) for `2 ≤ H`.
-/
lemma twoFreePalette_card (H : ℕ) (hH : 2 ≤ H) :
    ((Finset.Icc 1 H).erase 2).card = H - 1 ∧
      ((Finset.Icc 0 H).erase 2).card = H := by {
  have hm1 : 2 ∈ Finset.Icc 1 H := Finset.mem_Icc.mpr ⟨by { omega }, hH⟩
  have hm0 : 2 ∈ Finset.Icc 0 H := Finset.mem_Icc.mpr ⟨by { omega }, hH⟩
  have hc1 := Finset.card_erase_of_mem hm1
  have hc0 := Finset.card_erase_of_mem hm0
  rw [Nat.card_Icc] at hc1 hc0
  exact ⟨by { omega }, by { omega }⟩
}

/--
Sharp `H = 2` Run Obstruction (`2`-Free Tail):
For every `m > N_0`, `(a(m), a(m + 1))` cannot stay inside `[1, 2]` — at least one of the two
adjacent terms is `0` or `≥ 3`.
-/
lemma no_twos_pair_exits_below_three (N_0 m : ℕ)
    (h_no_twos : ∀ k > N_0, vanEckNthTerm k ≠ 2) (hm : N_0 < m) :
    vanEckNthTerm m = 0 ∨ 3 ≤ vanEckNthTerm m ∨
      vanEckNthTerm (m + 1) = 0 ∨ 3 ≤ vanEckNthTerm (m + 1) := by {
  by_contra hc
  have hm_ne2 := h_no_twos m hm
  have hm1_ne2 := h_no_twos (m + 1) (by { omega })
  have hm_eq1 : vanEckNthTerm m = 1 := by { omega }
  have hm1_eq1 : vanEckNthTerm (m + 1) = 1 := by { omega }
  exact vanEck_no_stutter_one m ⟨hm_eq1, hm1_eq1⟩
}

/--
`2`-Free Bounded-Palette Zero-Free Obstruction (Allowing `4, 6, ...`):
Under `∀ k > N_0, vanEckNthTerm k ≠ 2`, for any `2 ≤ H` and `A > N_0`, any window `[A, A + L]` of
length `L + 1 > (H - 1) * (H + 1) ^ (H - 1)` must hit `0` or exceed `H`.
-/
theorem no_twos_bounded_palette_run_obstruction (N_0 H A L : ℕ)
    (h_no_twos : ∀ k > N_0, vanEckNthTerm k ≠ 2) (hH : 2 ≤ H) (hA : N_0 < A)
    (hL : (H - 1) * (H + 1) ^ (H - 1) < L + 1) :
    ∃ t ≤ L, vanEckNthTerm (A + t) = 0 ∨ H < vanEckNthTerm (A + t) := by {
  by_contra hc
  let P := (Finset.Icc 1 H).erase 2
  have hP : ∀ v ∈ P, 1 ≤ v ∧ v ≤ H := by {
    intro v hv
    exact Finset.mem_Icc.mp (Finset.mem_of_mem_erase hv)
  }
  have h_run : ∀ t ≤ L, vanEckNthTerm (A + t) ∈ P := by {
    intro t ht
    have hnz : vanEckNthTerm (A + t) ≠ 0 := fun hz => hc ⟨t, ht, Or.inl hz⟩
    have hle : vanEckNthTerm (A + t) ≤ H :=
      Nat.le_of_not_lt (fun hgt => hc ⟨t, ht, Or.inr hgt⟩)
    have hne2 : vanEckNthTerm (A + t) ≠ 2 := h_no_twos (A + t) (by { omega })
    exact Finset.mem_erase.mpr ⟨hne2, Finset.mem_Icc.mpr ⟨by { omega }, hle⟩⟩
  }
  have h_len := finite_palette_run_length_bound P H A L hP h_run
  rw [(twoFreePalette_card H hH).1] at h_len
  omega
}

/--
Sub-Unit `2`-Free Gate Supply Bound (Allowing `4, 6, ...`):
Under `∀ k > N_0, vanEckNthTerm k ≠ 2`, for `2 ≤ H` and a zero `z_0 > N_0`, excluding the single
value `2` shrinks `{0, ..., H} \ {2}` to size `H`, so any set `Z` of zeros in `(z_0, B]` with
`H < a(z - 1)` satisfies `Z.card * (H + 1) ≤ H * ((B - (z_0 + 1)) + (H + 1))`.
-/
theorem no_twos_sub_unit_palette_gate_supply (Z : Finset ℕ) (N_0 z_0 H B : ℕ)
    (h_no_twos : ∀ k > N_0, vanEckNthTerm k ≠ 2) (hH : 2 ≤ H)
    (hz0_gt : N_0 < z_0) (hz0 : vanEckNthTerm z_0 = 0)
    (hZ : ∀ z ∈ Z, z_0 < z ∧ z ≤ B ∧ vanEckNthTerm z = 0 ∧ H < vanEckNthTerm (z - 1)) :
    Z.card * (H + 1) ≤ H * ((B - (z_0 + 1)) + (H + 1)) := by {
  let P := (Finset.Icc 0 H).erase 2
  have hP : ∀ k, z_0 ≤ k → k < B → vanEckNthTerm k ≤ H → vanEckNthTerm k ∈ P := by {
    intro k hk1 _hk2 hle
    exact Finset.mem_erase.mpr
      ⟨h_no_twos k (by { omega }), Finset.mem_Icc.mpr ⟨Nat.zero_le _, hle⟩⟩
  }
  have h_bnd := large_pre_zero_palette_gate_supply Z P z_0 H B hz0 hP hZ
  rw [(twoFreePalette_card H hH).2] at h_bnd
  exact h_bnd
}




