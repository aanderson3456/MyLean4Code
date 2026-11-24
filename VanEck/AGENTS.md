# VanEck Sequence - Infinite Twos Formalization Context

This document captures the current context and architecture of the VanEck sequence formalization project, specifically for proving that the number 2 appears infinitely many times.

---

## 1. Project Goal
The target is `infinite_twos_vanEck` in [InfiniteTwos.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/InfiniteTwos.lean):
```lean
theorem infinite_twos_vanEck (N : ℕ) : ∃ m > N, vanEckNthTerm m = 2
```
**This is an open problem (OEIS A181391).** It is stated with a single, explicitly labelled `sorry`. Only infinitely many zeros, unboundedness, and the √n limsup bound have known proofs (all formalized here).

---

## 2. File Architecture & Dependencies
* [VanEck.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/VanEck.lean) & [Basic.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/VanEck/Basic.lean): sequence generation, `matchSearch`, lookback properties, `infinite_zeros_vanEck`.
* [ImpossiblePatterns.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/ImpossiblePatterns.lean): lookback uniqueness (`vanEck_idx_sub_val_unique`), forbidden patterns.
* [LimSup.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/LimSup.lean) & [FinishedSurjLemmas.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/FinishedSurjLemmas.lean): `vanEck_limsup_ge_sqrt`, `vanEck_unbounded`.
* [SurjectivityLemmas.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/SurjectivityLemmas.lean): zero-gap, anchor, and palette lemmas.
* [InfiniteEvens.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/InfiniteEvens.lean): `IsVanEckFrom`, DFS refutation certificates, `no_twos_implies_bounded_iff_infinite_twos`.
* [InfiniteTwos.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/InfiniteTwos.lean): local periodicity/Mirsky–Newman squeeze, Kőnig/DFS-ray reduction, record-jump analysis, return-gap forest identities, and the main (open) theorem.
* [ReturnForestFrom.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/ReturnForestFrom.lean): forest identities for any `IsVanEckFrom g M_0` tail.
* [CollisionLemma.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/CollisionLemma.lean): exact collision criterion and resonance reformulation.
* [MirskyNewman.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/MirskyNewman.lean): Mirsky–Newman exact-cover theorem (sorry-free).

---

## 3. Verified Reductions of the Goal
* `infinite_twos_vanEck_of_step_two_repeats` / `infiniteTwos_iff_infinite_step_two_repeats`: equivalent to infinitely many `a(i) = a(i + 2)`.
* `infiniteTwos_iff_resonances_or_new_zero_gaps`: equivalent to infinitely many resonances (previous occurrence of `a(i+1)` exactly `a(i)` back) or infinitely many new zero gaps (numerically the latter stop after index 10).
* `infinite_twos_of_no_post_cut_two_free_tail`: suffices to refute one unbounded 2-free `IsVanEckFrom` tail.
* `no_twos_implies_bounded_iff_infinite_twos`: the old boundedness route is *equivalent* to the goal.

## 4. Known Dead Ends (do not retry)
* **Boundedness:** the sequence is unbounded, so "no 2s ⇒ bounded" carries no extra leverage (the old `z - 1` branch was unprovable locally; see `prefixMax_jump_in_two_free_window`).
* **Global counting / test functions:** every forest identity (`sum_return_chain_diff_eq`, any `h`) is a restatement of the recurrence; finite 2-free runs satisfy all of them, and the real sequence has 2-free stretches longer than 1600.
* **Density / pigeonhole on even-odd tracks:** `track_pigeonhole_no_go`; fixed-K small-value density also fails numerically (decays every decade).
* **Local dynamics alone:** the all-1s orbit obeys the rule and is 2-free, so any proof must use the actual prefix.

---

## 5. Style and Linter Guidelines
* **Tactic Wrappers**: Strictly use curly brackets: `by { ... }`.
* **Goal Chaining**: Avoid semicolon-chaining constructors; use bullet points (`·`).
* **Size Scoping**: Keep proofs/lemmas under 50 lines; extract helper steps.
* **Builds**: never run bare `lake build` (it pulls in the WIP `KjosHanssenPrimes.lean`); use explicit targets, e.g. `lake build +InfiniteTwos +ReturnForestFrom +CollisionLemma`.
* **Do not redefine** helper lemmas that already exist in imported files.
