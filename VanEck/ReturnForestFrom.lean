/-
Copyright (c) 2026 Austin Anderson
SPDX-License-Identifier: MIT

Return-gap forest identities ported from `vanEckNthTerm` to arbitrary sequences `g`
satisfying `IsVanEckFrom g M_0` (so they apply to the 2-free DFS ray tail).

All statements live on a post-cut window `[A, N)` with `M_0 ≤ A`. For `m` in the window the
*back pointer* is `m - g (m + 1)`: when `g (m + 1) > 0` it is the previous occurrence of `g m`
(which may lie before the cut `A`), and when `g (m + 1) = 0` the index `m` is a first occurrence.
-/
import InfiniteTwos

/-!
## Basic link lemmas
-/

/-- A positive post-cut term `g (m + 1) > 0` encodes the consecutive-occurrence link
`(m - g (m + 1), m)` of the value `g m`. -/
lemma isVanEckFrom_pos_link (g : ℕ → ℕ) (M_0 m : ℕ) (h_rec : IsVanEckFrom g M_0)
    (hm : M_0 ≤ m) (h_pos : 0 < g (m + 1)) :
    g (m + 1) ≤ m ∧ g (m - g (m + 1)) = g m ∧
      ∀ k, m - g (m + 1) < k → k < m → g k ≠ g m := by {
  have hr := h_rec m hm
  cases h_occ : lastOccBeforeFn g m (g m) with
  | none =>
    rw [h_occ] at hr
    change g (m + 1) = 0 at hr
    omega
  | some p =>
    rw [h_occ] at hr
    change g (m + 1) = m - p at hr
    have hsp := lastOccBeforeFn_eq_some_spec g m (g m) p h_occ
    have hp_eq : m - g (m + 1) = p := by { omega }
    rw [hp_eq]
    exact ⟨by { omega }, hsp.2.1, hsp.2.2⟩
}

/-- Conversely, a consecutive-occurrence link `(p, m)` with `M_0 ≤ m` forces
`g (m + 1) = m - p`. -/
lemma isVanEckFrom_eq_gap_of_consec (g : ℕ → ℕ) (M_0 p m : ℕ) (h_rec : IsVanEckFrom g M_0)
    (hm : M_0 ≤ m) (hpm : p < m) (h_eq : g p = g m)
    (h_no : ∀ k, p < k → k < m → g k ≠ g m) :
    g (m + 1) = m - p := by {
  have hr := h_rec m hm
  cases h_occ : lastOccBeforeFn g m (g m) with
  | none =>
    exact False.elim ((lastOccBeforeFn_eq_none_iff g m (g m)).mp h_occ p hpm h_eq)
  | some p' =>
    rw [h_occ] at hr
    change g (m + 1) = m - p' at hr
    have hsp := lastOccBeforeFn_eq_some_spec g m (g m) p' h_occ
    have hpp : p' = p := by {
      rcases lt_trichotomy p' p with hlt | heq | hgt
      · exact False.elim (hsp.2.2 p hlt hpm h_eq)
      · exact heq
      · exact False.elim (h_no p' hgt hsp.1 hsp.2.1)
    }
    rw [hr, hpp]
}

/-- A post-cut zero `g (m + 1) = 0` happens exactly when `g m` is a first occurrence. -/
lemma isVanEckFrom_zero_iff_first_occ (g : ℕ → ℕ) (M_0 m : ℕ) (h_rec : IsVanEckFrom g M_0)
    (hm : M_0 ≤ m) : g (m + 1) = 0 ↔ ∀ i < m, g i ≠ g m := by {
  have hr := h_rec m hm
  rw [← lastOccBeforeFn_eq_none_iff g m (g m)]
  cases h_occ : lastOccBeforeFn g m (g m) with
  | none =>
    rw [h_occ] at hr
    change g (m + 1) = 0 at hr
    exact ⟨fun _ => rfl, fun _ => hr⟩
  | some p =>
    rw [h_occ] at hr
    change g (m + 1) = m - p at hr
    have hp_lt := (lastOccBeforeFn_eq_some_spec g m (g m) p h_occ).1
    constructor
    · intro hz
      omega
    · intro h_none
      exact absurd h_none (Option.some_ne_none p)
}

/-- A post-cut positive term `g (m + 1) > 0` happens exactly when `g m` occurred before. -/
lemma isVanEckFrom_pos_iff_seen (g : ℕ → ℕ) (M_0 m : ℕ) (h_rec : IsVanEckFrom g M_0)
    (hm : M_0 ≤ m) : 0 < g (m + 1) ↔ ∃ i < m, g i = g m := by {
  have h_iff := isVanEckFrom_zero_iff_first_occ g M_0 m h_rec hm
  constructor
  · intro h_pos
    by_contra h_none
    exact absurd (h_iff.mpr (fun i hi h_eq => h_none ⟨i, hi, h_eq⟩)) (by { omega })
  · rintro ⟨i, hi, h_eq⟩
    by_contra h_le
    exact h_iff.mp (by { omega }) i hi h_eq
}

/-- Every post-cut term is bounded by its lookback index: `g (m + 1) ≤ m`. -/
lemma isVanEckFrom_succ_le (g : ℕ → ℕ) (M_0 m : ℕ) (h_rec : IsVanEckFrom g M_0)
    (hm : M_0 ≤ m) : g (m + 1) ≤ m := by {
  by_cases h_pos : 0 < g (m + 1)
  · exact (isVanEckFrom_pos_link g M_0 m h_rec hm h_pos).1
  · omega
}

/-!
## Injectivity of the back pointer
-/

/-- The back pointer `m ↦ m - g (m + 1)` is injective on positive post-cut indices. -/
lemma isVanEckFrom_backPtr_inj (g : ℕ → ℕ) (M_0 m_1 m_2 : ℕ) (h_rec : IsVanEckFrom g M_0)
    (hm_1 : M_0 ≤ m_1) (hm_2 : M_0 ≤ m_2) (h_1 : 0 < g (m_1 + 1)) (h_2 : 0 < g (m_2 + 1))
    (h_eq : m_1 - g (m_1 + 1) = m_2 - g (m_2 + 1)) : m_1 = m_2 := by {
  rcases lt_trichotomy m_1 m_2 with hlt | heq | hgt
  · have h_ne := isVanEckFrom_lookback_anchor_unique g M_0 (m_1 + 1) (m_2 + 1) h_rec
      (by { omega }) (by { omega }) h_1 h_2
    omega
  · exact heq
  · have h_ne := isVanEckFrom_lookback_anchor_unique g M_0 (m_2 + 1) (m_1 + 1) h_rec
      (by { omega }) (by { omega }) h_2 h_1
    omega
}

/-!
## Windowed index sets
-/

/-- Positive post-cut indices: `m ∈ [A, N)` with `g (m + 1) > 0` (links ending at `m`). -/
def fromPosIdx (g : ℕ → ℕ) (A N : ℕ) : Finset ℕ :=
  (Finset.Ico A N).filter (fun m => 0 < g (m + 1))

/-- Chain-start (birth) indices: `m ∈ [A, N)` with `g (m + 1) = 0`. -/
def fromZeroIdx (g : ℕ → ℕ) (A N : ℕ) : Finset ℕ :=
  (Finset.Ico A N).filter (fun m => g (m + 1) = 0)

/-- Frontier indices: `p ∈ [A, N)` with no later occurrence of `g p` in `(p, N)`. -/
def fromLastIdx (g : ℕ → ℕ) (A N : ℕ) : Finset ℕ :=
  (Finset.Ico A N).filter (fun p => ∀ q ∈ Finset.Ioo p N, g q ≠ g p)

/-- Pre-cut anchors: `p < A` that are the last occurrence of `g p` in `[0, A)` and whose value
reappears in the window `[A, N)` (the earlier endpoints of links crossing the cut). -/
def fromPreAnchorIdx (g : ℕ → ℕ) (A N : ℕ) : Finset ℕ :=
  (Finset.range A).filter (fun p =>
    (∀ q ∈ Finset.Ioo p A, g q ≠ g p) ∧ ∃ q ∈ Finset.Ico A N, g q = g p)

/-- Earliest occurrence of `g p` in `(p, N) ∩ [A, ∞)`, given one exists. -/
lemma exists_next_occ_from (g : ℕ → ℕ) (p A N : ℕ)
    (h : ∃ q, p < q ∧ A ≤ q ∧ q < N ∧ g q = g p) :
    ∃ q, p < q ∧ A ≤ q ∧ q < N ∧ g q = g p ∧
      ∀ k, p < k → A ≤ k → k < q → g k ≠ g p := by {
  classical
  have hs := Nat.find_spec h
  refine ⟨Nat.find h, hs.1, hs.2.1, hs.2.2.1, hs.2.2.2, ?_⟩
  intro k hpk hAk hkq hk
  have hkN : k < N := by { omega }
  exact Nat.find_min h hkq ⟨hpk, hAk, hkN, hk⟩
}

/-- Back pointers of positive window indices land in the non-frontier window or the
pre-cut anchors. -/
lemma isVanEckFrom_backPtr_mem (g : ℕ → ℕ) (M_0 A N m : ℕ) (h_rec : IsVanEckFrom g M_0)
    (hA : M_0 ≤ A) (hm : m ∈ fromPosIdx g A N) :
    m - g (m + 1) ∈ (Finset.Ico A N \ fromLastIdx g A N) ∪ fromPreAnchorIdx g A N := by {
  have hm_f := Finset.mem_filter.mp hm
  have hm_ico := Finset.mem_Ico.mp hm_f.1
  have hl := isVanEckFrom_pos_link g M_0 m h_rec (by { omega }) hm_f.2
  by_cases hpA : A ≤ m - g (m + 1)
  · refine Finset.mem_union_left _ (Finset.mem_sdiff.mpr
      ⟨Finset.mem_Ico.mpr ⟨hpA, by { omega }⟩, ?_⟩)
    intro h_last
    have h_l := (Finset.mem_filter.mp h_last).2 m (Finset.mem_Ioo.mpr ⟨by { omega }, hm_ico.2⟩)
    exact h_l hl.2.1.symm
  · refine Finset.mem_union_right _ (Finset.mem_filter.mpr
      ⟨Finset.mem_range.mpr (by { omega }), ?_, ⟨m, hm_f.1, hl.2.1.symm⟩⟩)
    intro q hq
    have hq_ioo := Finset.mem_Ioo.mp hq
    rw [hl.2.1]
    exact hl.2.2 q hq_ioo.1 (by { omega })
}

/-- Members of the back-pointer target set have a later window occurrence and no
intermediate pre-cut occurrence. -/
lemma mem_fromBackSet_spec (g : ℕ → ℕ) (A N p : ℕ)
    (hp : p ∈ (Finset.Ico A N \ fromLastIdx g A N) ∪ fromPreAnchorIdx g A N) :
    (∃ q, p < q ∧ A ≤ q ∧ q < N ∧ g q = g p) ∧ ∀ k, p < k → k < A → g k ≠ g p := by {
  rcases Finset.mem_union.mp hp with h1 | h2
  · have hsd := Finset.mem_sdiff.mp h1
    have hp_ico := Finset.mem_Ico.mp hsd.1
    refine ⟨by_contra (fun h_none => hsd.2 (Finset.mem_filter.mpr ⟨hsd.1, fun q hq h_eq => ?_⟩)),
      fun k hpk hkA => by { omega }⟩
    have hq_ioo := Finset.mem_Ioo.mp hq
    exact h_none ⟨q, hq_ioo.1, by { omega }, hq_ioo.2, h_eq⟩
  · have h_f := Finset.mem_filter.mp h2
    have hpA := Finset.mem_range.mp h_f.1
    rcases h_f.2.2 with ⟨q, hq, hq_eq⟩
    have hq_ico := Finset.mem_Ico.mp hq
    refine ⟨⟨q, by { omega }, hq_ico.1, hq_ico.2, hq_eq⟩, fun k hpk hkA => ?_⟩
    exact h_f.2.1 k (Finset.mem_Ioo.mpr ⟨hpk, hkA⟩)
}

/-- Every member of the back-pointer target set is hit by some positive window index. -/
lemma isVanEckFrom_backPtr_surj (g : ℕ → ℕ) (M_0 A N p : ℕ) (h_rec : IsVanEckFrom g M_0)
    (hA : M_0 ≤ A) (hp : p ∈ (Finset.Ico A N \ fromLastIdx g A N) ∪ fromPreAnchorIdx g A N) :
    ∃ m ∈ fromPosIdx g A N, m - g (m + 1) = p := by {
  have h_spec := mem_fromBackSet_spec g A N p hp
  rcases exists_next_occ_from g p A N h_spec.1 with ⟨q, hpq, hAq, hqN, hq_eq, hq_min⟩
  have h_no : ∀ k, p < k → k < q → g k ≠ g q := by {
    intro k hpk hkq
    rw [hq_eq]
    by_cases hkA : A ≤ k
    · exact hq_min k hpk hkA hkq
    · exact h_spec.2 k hpk (by { omega })
  }
  have h_gap := isVanEckFrom_eq_gap_of_consec g M_0 p q h_rec (by { omega }) hpq hq_eq.symm h_no
  refine ⟨q, Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr ⟨hAq, hqN⟩, by { omega }⟩, ?_⟩
  omega
}

/-- The two pieces of the back-pointer target set are disjoint (window vs. pre-cut). -/
lemma fromBackSet_disjoint (g : ℕ → ℕ) (A N : ℕ) :
    Disjoint (Finset.Ico A N \ fromLastIdx g A N) (fromPreAnchorIdx g A N) := by {
  refine Finset.disjoint_left.mpr (fun p h1 h2 => ?_)
  have hp1 := Finset.mem_Ico.mp (Finset.mem_sdiff.mp h1).1
  have hp2 := Finset.mem_range.mp (Finset.mem_filter.mp h2).1
  omega
}

/-!
## Windowed conservation law
-/

/-- Back-pointer reindexing: summing `h` over back pointers of positive window indices equals
summing over non-frontier window indices plus pre-cut anchors. -/
theorem isVanEckFrom_sum_backPtr_eq {M : Type*} [AddCommMonoid M] (g : ℕ → ℕ) (M_0 A N : ℕ)
    (h_rec : IsVanEckFrom g M_0) (hA : M_0 ≤ A) (h : ℕ → M) :
    ∑ m ∈ fromPosIdx g A N, h (m - g (m + 1)) =
      ∑ p ∈ Finset.Ico A N \ fromLastIdx g A N, h p + ∑ p ∈ fromPreAnchorIdx g A N, h p := by {
  rw [← Finset.sum_union (fromBackSet_disjoint g A N)]
  refine Finset.sum_nbij (fun m => m - g (m + 1)) ?_ ?_ ?_ ?_
  · exact fun m hm => isVanEckFrom_backPtr_mem g M_0 A N m h_rec hA hm
  · intro m_1 hm_1 m_2 hm_2 h_eq
    have h1 := Finset.mem_filter.mp hm_1
    have h2 := Finset.mem_filter.mp hm_2
    have h1i := Finset.mem_Ico.mp h1.1
    have h2i := Finset.mem_Ico.mp h2.1
    exact isVanEckFrom_backPtr_inj g M_0 m_1 m_2 h_rec
      (by { omega }) (by { omega }) h1.2 h2.2 h_eq
  · intro p hp
    rcases isVanEckFrom_backPtr_surj g M_0 A N p h_rec hA (Finset.mem_coe.mp hp) with
      ⟨m, hm, hm_eq⟩
    exact ⟨m, Finset.mem_coe.mpr hm, hm_eq⟩
  · intro _ _
    rfl
}

/-- Window positives and window zeros partition the window `[A, N)`. -/
lemma sum_fromPosIdx_add_fromZeroIdx {M : Type*} [AddCommMonoid M] (g : ℕ → ℕ) (A N : ℕ)
    (h : ℕ → M) :
    ∑ m ∈ fromPosIdx g A N, h m + ∑ m ∈ fromZeroIdx g A N, h m = ∑ m ∈ Finset.Ico A N, h m := by {
  have hZ : fromZeroIdx g A N = (Finset.Ico A N).filter (fun m => ¬ 0 < g (m + 1)) :=
    Finset.filter_congr (fun m _ => ⟨fun h0 => by { omega }, fun h0 => by { omega }⟩)
  rw [hZ, fromPosIdx]
  exact Finset.sum_filter_add_sum_filter_not _ _ _
}

/-- Zero window indices contribute nothing to the chain-difference sum. -/
lemma sum_chain_diff_eq_sum_fromPosIdx {M : Type*} [AddCommGroup M] (g : ℕ → ℕ) (A N : ℕ)
    (h : ℕ → M) :
    ∑ m ∈ Finset.Ico A N, (h m - h (m - g (m + 1))) =
      ∑ m ∈ fromPosIdx g A N, (h m - h (m - g (m + 1))) := by {
  rw [fromPosIdx, ← Finset.sum_filter_add_sum_filter_not (Finset.Ico A N)
    (fun m => 0 < g (m + 1))]
  have hz : ∑ m ∈ (Finset.Ico A N).filter (fun m => ¬ 0 < g (m + 1)),
      (h m - h (m - g (m + 1))) = 0 := by {
    refine Finset.sum_eq_zero (fun m hm => ?_)
    have hz' : g (m + 1) = 0 := by {
      have hnot := (Finset.mem_filter.mp hm).2
      omega
    }
    rw [hz', Nat.sub_zero, sub_self]
  }
  rw [hz, add_zero]
}

/-- **Windowed Return-Forest Conservation Law** for `IsVanEckFrom g M_0` on `[A, N)`,
`M_0 ≤ A`: the chain differences `h m - h (m - g (m + 1))` telescope to
(frontier terms) − (window births) − (pre-cut anchors of links crossing the cut). -/
theorem isVanEckFrom_sum_return_chain_diff_eq {M : Type*} [AddCommGroup M] (g : ℕ → ℕ)
    (M_0 A N : ℕ) (h_rec : IsVanEckFrom g M_0) (hA : M_0 ≤ A) (h : ℕ → M) :
    ∑ m ∈ Finset.Ico A N, (h m - h (m - g (m + 1))) =
      ∑ p ∈ fromLastIdx g A N, h p - ∑ m ∈ fromZeroIdx g A N, h m -
        ∑ p ∈ fromPreAnchorIdx g A N, h p := by {
  have h_pos := eq_sub_of_add_eq (sum_fromPosIdx_add_fromZeroIdx g A N h)
  have h_sub : fromLastIdx g A N ⊆ Finset.Ico A N := Finset.filter_subset _ _
  have h_sd : ∑ p ∈ Finset.Ico A N \ fromLastIdx g A N, h p =
      ∑ p ∈ Finset.Ico A N, h p - ∑ p ∈ fromLastIdx g A N, h p :=
    eq_sub_of_add_eq (Finset.sum_sdiff (f := h) h_sub)
  rw [sum_chain_diff_eq_sum_fromPosIdx, Finset.sum_sub_distrib,
    isVanEckFrom_sum_backPtr_eq g M_0 A N h_rec hA h, h_pos, h_sd]
  abel
}

/-!
## Corollaries
-/

/-- Count corollary: #frontier = #window births + #pre-cut anchors. -/
theorem isVanEckFrom_lastIdx_card_eq (g : ℕ → ℕ) (M_0 A N : ℕ) (h_rec : IsVanEckFrom g M_0)
    (hA : M_0 ≤ A) :
    (fromLastIdx g A N).card = (fromZeroIdx g A N).card + (fromPreAnchorIdx g A N).card := by {
  have h := isVanEckFrom_sum_return_chain_diff_eq g M_0 A N h_rec hA (fun _ => (1 : ℤ))
  simp only [sub_self, Finset.sum_const_zero, Finset.sum_const, nsmul_eq_mul, mul_one] at h
  omega
}

/-- Integer sum corollary (`h = id`): the window sum of `g (m + 1)` equals
frontier indices − birth indices − pre-cut anchor indices. -/
theorem isVanEckFrom_sum_succ_eq_int (g : ℕ → ℕ) (M_0 A N : ℕ) (h_rec : IsVanEckFrom g M_0)
    (hA : M_0 ≤ A) :
    ∑ m ∈ Finset.Ico A N, (g (m + 1) : ℤ) =
      ∑ p ∈ fromLastIdx g A N, (p : ℤ) - ∑ m ∈ fromZeroIdx g A N, (m : ℤ) -
        ∑ p ∈ fromPreAnchorIdx g A N, (p : ℤ) := by {
  rw [← isVanEckFrom_sum_return_chain_diff_eq g M_0 A N h_rec hA (fun k => (k : ℤ))]
  refine Finset.sum_congr rfl (fun m hm => ?_)
  have hm_ico := Finset.mem_Ico.mp hm
  have h_le := isVanEckFrom_succ_le g M_0 m h_rec (by { omega })
  omega
}

/-- Natural-number form of the sum corollary. -/
theorem isVanEckFrom_sum_succ_eq (g : ℕ → ℕ) (M_0 A N : ℕ) (h_rec : IsVanEckFrom g M_0)
    (hA : M_0 ≤ A) :
    ∑ m ∈ Finset.Ico A N, g (m + 1) + ∑ m ∈ fromZeroIdx g A N, m +
        ∑ p ∈ fromPreAnchorIdx g A N, p = ∑ p ∈ fromLastIdx g A N, p := by {
  have h := isVanEckFrom_sum_succ_eq_int g M_0 A N h_rec hA
  zify
  linarith
}

/-- Frontier indices are in bijection with the distinct values seen in the window `[A, N)`. -/
theorem fromLastIdx_card_eq_image_card (g : ℕ → ℕ) (A N : ℕ) :
    (fromLastIdx g A N).card = ((Finset.Ico A N).image g).card := by {
  refine Finset.card_nbij g ?_ ?_ ?_
  · intro p hp
    exact Finset.mem_image_of_mem g (Finset.mem_filter.mp hp).1
  · intro p_1 hp_1 p_2 hp_2 h_eq
    have h1 := Finset.mem_filter.mp hp_1
    have h2 := Finset.mem_filter.mp hp_2
    have h1i := Finset.mem_Ico.mp h1.1
    have h2i := Finset.mem_Ico.mp h2.1
    rcases lt_trichotomy p_1 p_2 with hlt | heq | hgt
    · exact absurd h_eq.symm (h1.2 p_2 (Finset.mem_Ioo.mpr ⟨hlt, h2i.2⟩))
    · exact heq
    · exact absurd h_eq (h2.2 p_1 (Finset.mem_Ioo.mpr ⟨hgt, h1i.2⟩))
  · intro v hv
    rcases Finset.mem_image.mp (Finset.mem_coe.mp hv) with ⟨q, hq, rfl⟩
    let S := (Finset.Ico A N).filter (fun i => g i = g q)
    have hS : S.Nonempty := ⟨q, Finset.mem_filter.mpr ⟨hq, rfl⟩⟩
    have hmax := Finset.mem_filter.mp (Finset.max'_mem S hS)
    have hmi := Finset.mem_Ico.mp hmax.1
    refine ⟨S.max' hS, Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨hmax.1, fun r hr h_r => ?_⟩), hmax.2⟩
    have hr_ioo := Finset.mem_Ioo.mp hr
    have hr_mem : r ∈ S := Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨by { omega }, hr_ioo.2⟩, h_r.trans hmax.2⟩
    have h_le := Finset.le_max' S r hr_mem
    omega
}

/-- Window births `m ∈ [A, N)` correspond to zeros `g n = 0` at `n ∈ (A, N]`. -/
theorem fromZeroIdx_card_eq (g : ℕ → ℕ) (A N : ℕ) :
    (fromZeroIdx g A N).card = ((Finset.Ioc A N).filter (fun n => g n = 0)).card := by {
  refine Finset.card_nbij (fun m => m + 1) ?_ ?_ ?_
  · intro m hm
    have hm_f := Finset.mem_filter.mp hm
    have hm_i := Finset.mem_Ico.mp hm_f.1
    change m + 1 ∈ (Finset.Ioc A N).filter (fun n => g n = 0)
    exact Finset.mem_filter.mpr ⟨Finset.mem_Ioc.mpr ⟨by { omega }, by { omega }⟩, hm_f.2⟩
  · intro m_1 _ m_2 _ h_eq
    change m_1 + 1 = m_2 + 1 at h_eq
    omega
  · intro n hn
    have hn_f := Finset.mem_filter.mp (Finset.mem_coe.mp hn)
    have hn_i := Finset.mem_Ioc.mp hn_f.1
    have h_add : n - 1 + 1 = n := by { omega }
    refine ⟨n - 1, Finset.mem_coe.mpr (Finset.mem_filter.mpr
      ⟨Finset.mem_Ico.mpr ⟨by { omega }, by { omega }⟩, ?_⟩), h_add⟩
    rw [h_add]
    exact hn_f.2
}

/-- Windowed count corollary: distinct values seen in `[A, N)` = zeros in `(A, N]` +
pre-cut anchors (values first seen before the cut that recur in the window). -/
theorem isVanEckFrom_seen_card_eq_zeros_add_anchors (g : ℕ → ℕ) (M_0 A N : ℕ)
    (h_rec : IsVanEckFrom g M_0) (hA : M_0 ≤ A) :
    ((Finset.Ico A N).image g).card =
      ((Finset.Ioc A N).filter (fun n => g n = 0)).card + (fromPreAnchorIdx g A N).card := by {
  rw [← fromLastIdx_card_eq_image_card, ← fromZeroIdx_card_eq]
  exact isVanEckFrom_lastIdx_card_eq g M_0 A N h_rec hA
}
