# VanEck Sequence - Infinite Twos Formalization Context

This document captures the current context and architecture of the VanEck sequence formalization project, specifically for proving that the number 2 appears infinitely many times.

---

## 1. Project Goal
Prove the theorem `infinite_twos_vanEck` in [InfiniteTwos.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/InfiniteTwos.lean):
```lean
theorem infinite_twos_vanEck (N : ℕ) : ∃ m > N, vanEckNthTerm m = 2
```

---

## 2. File Architecture & Dependencies
The formalization spans several key files:
* [VanEck.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/VanEck.lean) & [Basic.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/VanEck/Basic.lean): Define the sequence generation, `matchSearch`, and basic lookback properties.
* [SurjectivityLemmas.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/SurjectivityLemmas.lean): Contains major helper theorems such as `post_zero_bounded` and `pos_value_implies_gap`.
* [ImpossiblePatterns.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/ImpossiblePatterns.lean): Proves index lookback uniqueness properties (e.g., `vanEck_idx_sub_val_unique`).
* [InfiniteTwos.lean](file:///Users/austinanderson/GitHub/MyLean4Code/VanEck/InfiniteTwos.lean): The orchestrator proving that bounded blocks force twos or zeros via a graph-theoretic combinatorial squeeze.

---

## 3. Current Compilation Status
The project builds warning-free with `lake build`.
* **Important**: Do not redefine helper lemmas that already exist in imported files (e.g., `finite_twos_implies_old_gaps` which is in `SurjectivityLemmas.lean`).

---

## 4. Remaining Proving Tasks (The `sorry` Gates)

### A. Periodicity Lookup in `finite_cycle_gap_collapse`
In the sub-proof `h_recent_nat`:
```lean
have h_eq : vanEckNthTerm (n_2 + k.val + 1 - X) = X := by {
  sorry
}
```
* **Task**: Bridge the lookback index equivalence using the periodicity hypothesis `h_per` and the fact that `X = vanEckNthTerm (n_2 + k.val + 1)`.

### B. Most Recent Occurrence Constraint
In the sub-proof `h_no_intermediate_nat`:
```lean
have h_no_intermediate_nat : ∀ k : Fin P, ∀ i < v_nat (k.val + 1), i > 0 → v_nat ((k.val + P - i) % P + 1) ≠ v_nat (k.val + 1) := by {
  intro k i hi_lt hi_pos
  dsimp [v_nat]
  let X := vanEckNthTerm (n_2 + k.val + 1)
  sorry
}
```
* **Task**: Show that no intermediate term inside the gap `X` matches the value, mapped mod $P$ across the periodic cycle.

### C. Boundedness from No Twos
```lean
lemma no_twos_implies_bounded (N_0 : ℕ) (h_no_twos : ∀ m > N_0, vanEckNthTerm m ≠ 2) :
    ∃ M > 0, ∀ m, vanEckNthTerm m ≤ M := by {
  -- ... [Completed: infinite_zeros_vanEck, prefix max positivity, and induction on all k ≤ z_prev and z_prev < k < z - 1]
              by_cases hk_z1 : k = z - 1
              · rw [hk_z1]
                sorry
  -- ...
}
```
* **Task**: Prove that the term at `z - 1` (just before the zero `z`) is bounded by `M`. This is the final remaining sorry in `no_twos_implies_bounded`.

---

## 5. Style and Linter Guidelines
* **Tactic Wrappers**: Strictly use curly brackets: `by { ... }`.
* **Goal Chaining**: Avoid semicolon-chaining constructors (like `constructor; exact h1`); instead, cleanly use bullet points (`·`) to prevent Lean 4 multi-goal focus linter warnings.
* **Size Scoping**: Aim to keep proofs/lemmas under 50 lines. Extract helper steps as modular sub-lemmas.
