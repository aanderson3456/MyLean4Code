import VanEck
import ImpossiblePatterns
import LimSup
import FinishedSurjLemmas
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

