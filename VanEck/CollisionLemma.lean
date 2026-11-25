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

/-- Binary trie storing `Option ℕ` at fixed bit-depth leaves for fast kernel evaluation. -/
inductive VanEckTrie where
  | empty : VanEckTrie
  | leaf : Option ℕ → VanEckTrie
  | branch : VanEckTrie → VanEckTrie → VanEckTrie

/-- Left child of a `VanEckTrie` node (defaulting to `.empty`). -/
def trieLeft : VanEckTrie → VanEckTrie
  | .branch l _ => l
  | _ => .empty

/-- Right child of a `VanEckTrie` node (defaulting to `.empty`). -/
def trieRight : VanEckTrie → VanEckTrie
  | .branch _ r => r
  | _ => .empty

/-- Lookup key `k < 2 ^ d` in a `VanEckTrie` of depth `d`. -/
def trieGet : ℕ → VanEckTrie → ℕ → Option ℕ
  | 0, .leaf v, _ => v
  | 0, _, _ => none
  | _ + 1, .empty, _ => none
  | d + 1, t, k =>
    if k % 2 = 0 then trieGet d (trieLeft t) (k / 2)
    else trieGet d (trieRight t) (k / 2)

/-- Insert `(k, val)` for `k < 2 ^ d` into a `VanEckTrie` of depth `d`. -/
def trieSet : ℕ → VanEckTrie → ℕ → ℕ → VanEckTrie
  | 0, _, _, val => .leaf (some val)
  | d + 1, t, k, val =>
    if k % 2 = 0 then .branch (trieSet d (trieLeft t) (k / 2) val) (trieRight t)
    else .branch (trieLeft t) (trieSet d (trieRight t) (k / 2) val)

lemma trieGet_empty (d q : ℕ) : trieGet d .empty q = none := by {
  cases d with
  | zero => rfl
  | succ _ => rfl
}

lemma trieGet_succ (d : ℕ) (t : VanEckTrie) (k : ℕ) :
    trieGet (d + 1) t k =
      if k % 2 = 0 then trieGet d (trieLeft t) (k / 2)
      else trieGet d (trieRight t) (k / 2) := by {
  cases t with
  | empty =>
    change none = _
    split_ifs with h
    · exact (trieGet_empty d (k / 2)).symm
    · exact (trieGet_empty d (k / 2)).symm
  | leaf _ => rfl
  | branch _ _ => rfl
}

lemma trieGet_trieSet (d : ℕ) :
    ∀ (t : VanEckTrie) (k val q : ℕ), k < 2 ^ d → q < 2 ^ d →
      trieGet d (trieSet d t k val) q = if q = k then some val else trieGet d t q := by {
  induction d with
  | zero =>
    intro t k val q hk hq
    have hqk : q = k := by { omega }
    rw [if_pos hqk]
    rfl
  | succ d ih =>
    intro t k val q hk hq
    have hp : 2 ^ (d + 1) = 2 ^ d * 2 := pow_succ 2 d
    rw [trieSet]
    by_cases hk2 : k % 2 = 0
    · rw [if_pos hk2, trieGet_succ]
      by_cases hq2 : q % 2 = 0
      · rw [if_pos hq2]
        change trieGet d (trieSet d (trieLeft t) (k / 2) val) (q / 2) = _
        rw [ih (trieLeft t) (k / 2) val (q / 2) (by { omega }) (by { omega })]
        by_cases hqk : q = k
        · rw [if_pos hqk, if_pos (by { omega })]
        · rw [if_neg hqk, if_neg (by { omega }), trieGet_succ, if_pos hq2]
      · rw [if_neg hq2]
        have hqk : q ≠ k := by { omega }
        rw [if_neg hqk, trieGet_succ, if_neg hq2]
        rfl
    · rw [if_neg hk2, trieGet_succ]
      by_cases hq2 : q % 2 = 0
      · rw [if_pos hq2]
        have hqk : q ≠ k := by { omega }
        rw [if_neg hqk, trieGet_succ, if_pos hq2]
        rfl
      · rw [if_neg hq2]
        change trieGet d (trieSet d (trieRight t) (k / 2) val) (q / 2) = _
        rw [ih (trieRight t) (k / 2) val (q / 2) (by { omega }) (by { omega })]
        by_cases hqk : q = k
        · rw [if_pos hqk, if_pos (by { omega })]
        · rw [if_neg hqk, if_neg (by { omega }), trieGet_succ, if_neg hq2]
}

/-- Invariant for the trie-backed Van Eck counter state `(m, cur, t, acc)` at depth `d`. -/
def ValidTwosState (d : ℕ) (st : ℕ × ℕ × VanEckTrie × ℕ) : Prop :=
  st.2.1 = vanEckNthTerm st.1 ∧
    (∀ v < 2 ^ d, trieGet d st.2.2.1 v = lastOccBefore st.1 v) ∧
    st.2.2.2 = ((Finset.range st.1).filter (fun n => vanEckNthTerm n = 2)).card

/-- Single step of the trie-backed Van Eck counter `(m, cur, t, acc)`. -/
def fastTwosStep (d : ℕ) (st : ℕ × ℕ × VanEckTrie × ℕ) : ℕ × ℕ × VanEckTrie × ℕ :=
  let (m, cur, t, acc) := st
  let acc' := if cur = 2 then acc + 1 else acc
  let nxt := match trieGet d t cur with
    | none => 0
    | some p => m - p
  (m + 1, nxt, trieSet d t cur m, acc')

/-- Run `steps` iterations of `fastTwosStep d`. -/
def fastTwosRun (d : ℕ) : ℕ → (ℕ × ℕ × VanEckTrie × ℕ) → ℕ × ℕ × VanEckTrie × ℕ
  | 0, st => st
  | steps + 1, st => fastTwosRun d steps (fastTwosStep d st)

/-- Run `blocks` chunks of `chunk` steps each so kernel recursion depth stays `≤ chunk`. -/
def fastTwosBlocks (d : ℕ) : ℕ → ℕ → (ℕ × ℕ × VanEckTrie × ℕ) → ℕ × ℕ × VanEckTrie × ℕ
  | 0, _, st => st
  | blocks + 1, chunk, st => fastTwosBlocks d blocks chunk (fastTwosRun d chunk st)

lemma fastTwosRun_add (d a b : ℕ) (st : ℕ × ℕ × VanEckTrie × ℕ) :
    fastTwosRun d (a + b) st = fastTwosRun d b (fastTwosRun d a st) := by {
  induction a generalizing st with
  | zero =>
    rw [Nat.zero_add]
    rfl
  | succ a ih =>
    rw [Nat.succ_add]
    exact ih (fastTwosStep d st)
}

lemma fastTwosBlocks_eq_run (d blocks chunk : ℕ) (st : ℕ × ℕ × VanEckTrie × ℕ) :
    fastTwosBlocks d blocks chunk st = fastTwosRun d (blocks * chunk) st := by {
  induction blocks generalizing st with
  | zero =>
    rw [Nat.zero_mul]
    rfl
  | succ b ih =>
    rw [fastTwosBlocks, ih (fastTwosRun d chunk st), ← fastTwosRun_add]
    have hmul : (b + 1) * chunk = chunk + b * chunk := by { ring }
    rw [hmul]
}

lemma card_twos_range_succ (m : ℕ) :
    ((Finset.range (m + 1)).filter (fun n => vanEckNthTerm n = 2)).card =
      if vanEckNthTerm m = 2 then
        ((Finset.range m).filter (fun n => vanEckNthTerm n = 2)).card + 1
      else
        ((Finset.range m).filter (fun n => vanEckNthTerm n = 2)).card := by {
  rw [Finset.range_add_one, Finset.filter_insert]
  split_ifs with hm
  · refine Finset.card_insert_of_notMem (fun hmem => ?_)
    have hlt : m < m := Finset.mem_range.mp (Finset.mem_filter.mp hmem).1
    omega
  · rfl
}

lemma fastTwosStep_valid (d : ℕ) (st : ℕ × ℕ × VanEckTrie × ℕ)
    (h_lt : st.1 < 2 ^ d) (hv : ValidTwosState d st) :
    (fastTwosStep d st).1 = st.1 + 1 ∧ ValidTwosState d (fastTwosStep d st) := by {
  rcases st with ⟨m, cur, t, acc⟩
  rcases hv with ⟨hcur, ht, hacc⟩
  dsimp only [fastTwosStep, ValidTwosState] at h_lt hcur ht hacc ⊢
  have hcur_le : vanEckNthTerm m ≤ m := vanEckNthTerm_le_n m
  have hcur_lt : cur < 2 ^ d := by { omega }
  refine ⟨rfl, ?_, ?_, ?_⟩
  · rw [ht cur hcur_lt, hcur]
    exact (vanEck_next_eq_of_lastOccBefore m).symm
  · intro v hv_lt
    rw [trieGet_trieSet d t cur m v hcur_lt hv_lt, ht v hv_lt, hcur]
    simp only [lastOccBefore]
    by_cases hmv : vanEckNthTerm m = v
    · rw [if_pos hmv.symm, if_pos hmv]
    · have hvm : v ≠ vanEckNthTerm m := Ne.symm hmv
      rw [if_neg hvm, if_neg hmv]
  · rw [card_twos_range_succ m, hcur, hacc]
}

lemma fastTwosRun_valid (d steps : ℕ) (st : ℕ × ℕ × VanEckTrie × ℕ)
    (h_le : st.1 + steps ≤ 2 ^ d) (hv : ValidTwosState d st) :
    (fastTwosRun d steps st).1 = st.1 + steps ∧
      ValidTwosState d (fastTwosRun d steps st) := by {
  induction steps generalizing st with
  | zero =>
    rw [Nat.add_zero]
    exact ⟨rfl, hv⟩
  | succ s ih =>
    have hst := fastTwosStep_valid d st (by { omega }) hv
    have h_next := ih (fastTwosStep d st) (by { omega }) hst.2
    rw [fastTwosRun, h_next.1, hst.1]
    exact ⟨by { omega }, h_next.2⟩
}

set_option maxRecDepth 100000 in
lemma fastTwosBlocks_1000_eval :
    (fastTwosBlocks 10 10 100 (0, 0, .empty, 0)).2.2.2 = 18 := by {
  rfl
}

/-- Kernel-checked (`rfl`) exact count: among `n < 1000`, `vanEckNthTerm n = 2` holds `18` times. -/
theorem vanEck_twos_count_lt_1000 :
    ((Finset.range 1000).filter (fun n => vanEckNthTerm n = 2)).card = 18 := by {
  have hv0 : ValidTwosState 10 (0, 0, .empty, 0) :=
    ⟨rfl, fun v _ => trieGet_empty 10 v, rfl⟩
  have hrun := fastTwosRun_valid 10 (10 * 100) (0, 0, .empty, 0) (by { decide }) hv0
  rw [← fastTwosBlocks_eq_run] at hrun
  have h1000 : 0 + 10 * 100 = 1000 := rfl
  rw [h1000] at hrun
  have hacc := hrun.2.2.2
  rw [hrun.1] at hacc
  exact hacc.symm.trans fastTwosBlocks_1000_eval
}
