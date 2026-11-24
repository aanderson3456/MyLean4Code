/-
Copyright (c) 2026 Austin Anderson
SPDX-License-Identifier: MIT

Local collision lemmas: why a 2-free Van Eck tail must eventually produce an `X, Y, X` pattern.

Summary of what is proved here (no `sorry`, no new axioms):
* `vanEck_add_three_eq_two_iff`: `a(i+3) = 2 ↔ a(i) = a(i+2)` (exact collision criterion).
* `infiniteTwos_iff_infinite_step_two_repeats`: `InfiniteTwos` is *equivalent* to infinitely
  many step-2 repeats, so the collision formulation loses nothing.
* `ResonanceAt i`: the previous occurrence of `a(i+1)` lies exactly `a(i)` steps back.
  `resonanceAt_iff_step_two_repeat_of_pos` shows this is exactly a collision with `a(i) > 0`.
* `step_two_repeat_swap`: a collision `X, Y, X` (with `X, Y > 0`) forces the swapped echo
  `a(i - Y) = X` and `a(i + 1 - X) = Y`.
* `infiniteTwos_iff_resonances_or_new_zero_gaps`: `InfiniteTwos` is equivalent to
  (infinitely many resonances) ∨ `InfiniteNewZeroGaps`.  Numerically the second disjunct
  only fires at `i ∈ {1, 3, 10}` in the first `10^7` terms, so the whole problem is the
  resonance supply.
* `track_pigeonhole_no_go`: a sequence with every value in `{3, 4}` and no step-2 repeat
  exists, so no density/pigeonhole hypothesis on the even/odd tracks alone can force a
  collision; any proof must use the Van Eck dynamics.
-/
import InfiniteTwos

/-- Exact collision criterion: `a(i + 3) = 2` iff `a(i) = a(i + 2)`. -/
theorem vanEck_add_three_eq_two_iff (i : ℕ) :
    vanEckNthTerm (i + 3) = 2 ↔ vanEckNthTerm i = vanEckNthTerm (i + 2) := by {
  constructor
  · intro h
    have hg := pos_value_implies_gap (i + 3) 2 (by { omega }) h (by { omega })
    have h1 : i + 3 - 1 - 2 = i := by { omega }
    have h2 : i + 3 - 1 = i + 2 := by { omega }
    rw [h1, h2] at hg
    exact hg.2
  · intro h
    exact eq_add_two_implies_next_two i h
}

/-- `InfiniteTwos` is equivalent to infinitely many step-2 repeats `a(i) = a(i + 2)`. -/
theorem infiniteTwos_iff_infinite_step_two_repeats :
    InfiniteTwos ↔ ∀ N, ∃ i > N, vanEckNthTerm i = vanEckNthTerm (i + 2) := by {
  constructor
  · intro h N
    rcases h (N + 3) with ⟨m, hm_gt, hm_two⟩
    refine ⟨m - 3, by { omega }, ?_⟩
    have hm : m - 3 + 3 = m := by { omega }
    have h3 : vanEckNthTerm (m - 3 + 3) = 2 := by {
      rw [hm]
      exact hm_two
    }
    exact (vanEck_add_three_eq_two_iff (m - 3)).mp h3
  · exact infinite_alternating_pairs_implies_infinite_twos
}

/-- Van Eck step from an explicit most-recent previous occurrence. -/
lemma collision_next_eq_gap_of_consec (p m : ℕ) (hpm : p < m)
    (h_eq : vanEckNthTerm p = vanEckNthTerm m)
    (h_no : ∀ k, p < k → k < m → vanEckNthTerm k ≠ vanEckNthTerm m) :
    vanEckNthTerm (m + 1) = m - p := by {
  have hr := vanEckNthTerm_isVanEckFrom 0 m (Nat.zero_le m)
  rw [lastOccBeforeFn_eq_some_of_prev vanEckNthTerm m p (vanEckNthTerm m) hpm h_eq h_no] at hr
  exact hr
}

/--
`ResonanceAt i`: the most recent occurrence of `a(i + 1)` before `i + 1` lies exactly
`a(i)` steps back.  This is the local "resonance" that produces a `2` at `i + 3`.
-/
def ResonanceAt (i : ℕ) : Prop :=
  ∃ p < i + 1, vanEckNthTerm p = vanEckNthTerm (i + 1) ∧
    (∀ k, p < k → k < i + 1 → vanEckNthTerm k ≠ vanEckNthTerm (i + 1)) ∧
    i + 1 - p = vanEckNthTerm i

/-- Infinitely many resonances. -/
def InfinitelyManyResonances : Prop :=
  ∀ N, ∃ i > N, ResonanceAt i

/-- A resonance at `i` is a step-2 repeat `a(i) = a(i + 2)`. -/
lemma step_two_repeat_of_resonanceAt (i : ℕ) (h : ResonanceAt i) :
    vanEckNthTerm i = vanEckNthTerm (i + 2) := by {
  rcases h with ⟨p, hp_lt, hp_eq, hp_no, hp_gap⟩
  have hn := collision_next_eq_gap_of_consec p (i + 1) hp_lt hp_eq hp_no
  rw [hp_gap] at hn
  exact hn.symm
}

/-- A resonance at `i` emits a `2` at `i + 3`. -/
lemma two_of_resonanceAt (i : ℕ) (h : ResonanceAt i) : vanEckNthTerm (i + 3) = 2 := by {
  exact eq_add_two_implies_next_two i (step_two_repeat_of_resonanceAt i h)
}

/-- A step-2 repeat with positive repeated value is a resonance. -/
lemma resonanceAt_of_step_two_repeat (i : ℕ) (h : vanEckNthTerm i = vanEckNthTerm (i + 2))
    (hX : 0 < vanEckNthTerm i) : ResonanceAt i := by {
  have hv : vanEckNthTerm (i + 2) = vanEckNthTerm i := h.symm
  have hm := pos_value_most_recent_occurrence (i + 2) (vanEckNthTerm i) (by { omega }) hv hX
  have hg := pos_value_implies_gap (i + 2) (vanEckNthTerm i) (by { omega }) hv hX
  have h21 : i + 2 - 1 = i + 1 := by { omega }
  rw [h21] at hm
  rcases hm with ⟨hlt, heq, hno⟩
  refine ⟨i + 1 - vanEckNthTerm i, hlt, heq, hno, ?_⟩
  omega
}

/-- Resonance at `i` is exactly a step-2 repeat with positive repeated value. -/
theorem resonanceAt_iff_step_two_repeat_of_pos (i : ℕ) :
    ResonanceAt i ↔ (vanEckNthTerm i = vanEckNthTerm (i + 2) ∧ 0 < vanEckNthTerm i) := by {
  constructor
  · intro h
    refine ⟨step_two_repeat_of_resonanceAt i h, ?_⟩
    rcases h with ⟨p, hp_lt, _, _, hp_gap⟩
    omega
  · intro h
    exact resonanceAt_of_step_two_repeat i h.1 h.2
}

/--
Swap echo of a collision: if `a(i) = a(i + 2) = X > 0` and `a(i + 1) = Y > 0` with `i ≥ 1`,
then `X` occurred at `i - Y` and `Y` occurred at `i + 1 - X`.
-/
theorem step_two_repeat_swap (i : ℕ) (hi : 1 ≤ i)
    (h : vanEckNthTerm i = vanEckNthTerm (i + 2))
    (hX : 0 < vanEckNthTerm i) (hY : 0 < vanEckNthTerm (i + 1)) :
    vanEckNthTerm (i - vanEckNthTerm (i + 1)) = vanEckNthTerm i ∧
      vanEckNthTerm (i + 1 - vanEckNthTerm i) = vanEckNthTerm (i + 1) := by {
  have hY' := pos_value_implies_gap (i + 1) (vanEckNthTerm (i + 1)) (by { omega }) rfl hY
  have h1 : i + 1 - 1 = i := by { omega }
  rw [h1] at hY'
  refine ⟨hY'.2, ?_⟩
  rcases resonanceAt_of_step_two_repeat i h hX with ⟨p, hp_lt, hp_eq, _, hp_gap⟩
  have hp : p = i + 1 - vanEckNthTerm i := by { omega }
  rw [← hp]
  exact hp_eq
}

/-- A zero step-2 repeat `a(i) = a(i + 2) = 0` is a brand-new zero gap at `i`. -/
lemma new_zero_gap_of_zero_step_two_repeat (i : ℕ) (h : vanEckNthTerm i = vanEckNthTerm (i + 2))
    (h0 : vanEckNthTerm i = 0) :
    vanEckNthTerm i = 0 ∧ (∀ j < i + 1, vanEckNthTerm j ≠ vanEckNthTerm (i + 1)) := by {
  have h2 : vanEckNthTerm (i + 2) = 0 := by {
    rw [← h]
    exact h0
  }
  exact ⟨h0, (vanEck_mth_term_eq_zero_iff_prev_term_new i).mp h2⟩
}

/-- Without infinitely many resonances, collisions eventually all have value `0`. -/
lemma new_zero_gaps_of_not_resonances
    (h_rep : ∀ N, ∃ i > N, vanEckNthTerm i = vanEckNthTerm (i + 2))
    (hR : ¬ InfinitelyManyResonances) : InfiniteNewZeroGaps := by {
  unfold InfinitelyManyResonances at hR
  push Not at hR
  rcases hR with ⟨N_0, hN_0⟩
  intro N
  rcases h_rep (max N N_0) with ⟨i, hi_gt, h_eq⟩
  have h0 : vanEckNthTerm i = 0 := by {
    by_contra h_ne
    exact hN_0 i (by { omega }) (resonanceAt_of_step_two_repeat i h_eq (by { omega }))
  }
  exact ⟨i, by { omega }, new_zero_gap_of_zero_step_two_repeat i h_eq h0⟩
}

/--
`InfiniteTwos` is equivalent to infinitely many resonances or infinitely many brand-new
zero gaps.
-/
theorem infiniteTwos_iff_resonances_or_new_zero_gaps :
    InfiniteTwos ↔ InfinitelyManyResonances ∨ InfiniteNewZeroGaps := by {
  constructor
  · intro h
    have h_rep := infiniteTwos_iff_infinite_step_two_repeats.mp h
    by_cases hR : InfinitelyManyResonances
    · exact Or.inl hR
    · exact Or.inr (new_zero_gaps_of_not_resonances h_rep hR)
  · intro h
    rcases h with hR | hZ
    · intro N
      rcases hR N with ⟨i, hi_gt, hi_res⟩
      exact ⟨i + 3, by { omega }, two_of_resonanceAt i hi_res⟩
    · exact new_zero_gaps_implies_infinite_twos hZ
}

/--
No-go for pure pigeonhole: some sequence takes only the values `3` and `4` (so small values
have density `1` in every window) yet has no step-2 repeat.  Hence no density hypothesis on
the even/odd tracks alone forces a collision; the Van Eck dynamics must be used.
-/
theorem track_pigeonhole_no_go :
    ∃ f : ℕ → ℕ, (∀ i, f i ≠ f (i + 2)) ∧ ∀ i, 3 ≤ f i ∧ f i ≤ 4 := by {
  refine ⟨fun i => 3 + (i / 2) % 2, ?_, ?_⟩
  · intro i
    dsimp only
    omega
  · intro i
    dsimp only
    omega
}
