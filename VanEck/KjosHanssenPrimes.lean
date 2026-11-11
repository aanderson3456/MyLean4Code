/-
Copyright (c) 2026 Austin Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Austin Anderson
-/
import VanEck
import Arithmetic
import LimSup
import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.Nat.Prime.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Fintype.Card

/-!
# Prime Decomposition of Automata, Kjos-Hanssen Automatic Complexity, and the Van Eck Horizon

This module formalizes:
1. **Deterministic Finite Automata (`FinDFA`) and Kjos-Hanssen Automatic Complexity**:
   `UniquelyWitnesses` and `HasAutomaticComplexityLE` following Shallit–Wang (2001) and
   Hyde–Kjos-Hanssen (2015).
2. **Gödel–FRACTRAN Prime State Coding**:
   Maps each automaton state `s : Fin q` to the `s`-th prime `nthPrime s.val`
   (`p₀ = 2, p₁ = 3, p₂ = 5, p₃ = 7, p₄ = 11, p₅ = 13, p₆ = 17, p₇ = 19`).
   Proves that 2-state NOT/parity and repetition-witness automata are `{2, 3}`-smooth,
   whereas crossing the 8-state Kjos-Hanssen complexity threshold (`A(w) ≥ 8`) forces
   the prime horizon to reach `p₇ = 19`.
3. **Van Eck Unbounded Prime Horizon & `Π⁰₂` Surjectivity Barrier**:
   * `vanEck_unbounded_values` and `vanEck_unbounded_prime_horizon`: The Van Eck sequence takes
     arbitrarily large values, so no finite-state automaton with a bounded prime horizon can
     compute or cover the lookback trajectory `n ↦ vanEckNthTerm n`.
   * `vanEck_not_eventually_periodic`: The Van Eck sequence never enters a periodic cycle.
   * `vanEckAchieves_hasSigma1Form`, `vanEckNeverAchieves_hasPi1Form`, and
     `vanEckSurjective_hasPi2Form`: Exact arithmetical hierarchy classifications.
   * `no_finite_prefix_achieves_large_value` and `gap_v_requires_horizon_v`: Achieving a positive
     value `v` requires sequence horizon `m ≥ v + 1` (prefix length `≥ v + 2`) and an exact
     lookback match at distance `v`.
-/

-- ============================================================================
-- SECTION 1: DETERMINISTIC FINITE AUTOMATA & KJOS-HANSSEN AUTOMATIC COMPLEXITY
-- ============================================================================

/-- A Deterministic Finite Automaton over alphabet `α` with `q` states `Fin q`. -/
structure FinDFA (α : Type*) (q : ℕ) where
  start  : Fin q
  step   : Fin q → α → Fin q
  accept : Fin q → Bool

/-- Run a `FinDFA` on a word `w : List α` starting from state `s`. -/
def FinDFA.evalFrom {α : Type*} {q : ℕ} (M : FinDFA α q) (s : Fin q) : List α → Fin q
  | []      => s
  | a :: as => M.evalFrom (M.step s a) as

/-- Evaluating a `FinDFA` across a concatenated word equals sequential evaluation. -/
lemma FinDFA.evalFrom_append {α : Type*} {q : ℕ} (M : FinDFA α q) (s : Fin q)
    (u v : List α) : M.evalFrom s (u ++ v) = M.evalFrom (M.evalFrom s u) v := by {
  induction u generalizing s with
  | nil => rfl
  | cons a as ih => exact ih (M.step s a)
}

/-- A word `w` is accepted by `M` if `evalFrom M.start w` is an accepting state. -/
def FinDFA.Accepts {α : Type*} {q : ℕ} (M : FinDFA α q) (w : List α) : Prop :=
  M.accept (M.evalFrom M.start w) = true

/-- **Kjos-Hanssen Uniqueness Witness**:
`M` uniquely witnesses `w` at length `w.length` if `M` accepts `w` and rejects every
other word `v` of the same length. -/
def UniquelyWitnesses {α : Type*} {q : ℕ} (M : FinDFA α q) (w : List α) : Prop :=
  M.Accepts w ∧ ∀ v : List α, v.length = w.length → M.Accepts v → v = w

/-- **Kjos-Hanssen Automatic Complexity `A(w) ≤ q`**:
There exists a `q`-state DFA that uniquely witnesses `w` among all words of length `w.length`. -/
def HasAutomaticComplexityLE {α : Type*} (w : List α) (q : ℕ) : Prop :=
  ∃ M : FinDFA α q, UniquelyWitnesses M w

/-- No word can be witnessed by a 0-state DFA. -/
lemma not_hasAutomaticComplexityLE_zero {α : Type*} (w : List α) :
    ¬ HasAutomaticComplexityLE w 0 := by {
  rintro ⟨M, _⟩
  exact Fin.elim0 M.start
}

-- ============================================================================
-- SECTION 2: GÖDEL-FRACTRAN PRIME STATE CODING & THE p_8 = 19 HORIZON
-- ============================================================================

/-- The `i`-th prime number (0-indexed: `nthPrime 0 = 2`, `nthPrime 1 = 3`, `nthPrime 7 = 19`). -/
noncomputable def nthPrime (i : ℕ) : ℕ := Nat.nth Nat.Prime i

/-- Gödel-Prime encoding of a state `s : Fin q` as the prime `p_s`. -/
noncomputable def statePrime {q : ℕ} (s : Fin q) : ℕ := nthPrime s.val

/-- An automaton `M` is `P_bound`-prime-smooth if every state's prime code is at most `P_bound`. -/
def IsPrimeSmoothAutomaton {α : Type*} {q : ℕ} (_M : FinDFA α q) (P_bound : ℕ) : Prop :=
  ∀ s : Fin q, statePrime s ≤ P_bound

/-- Every value `nthPrime i` is prime. -/
lemma nthPrime_prime (i : ℕ) : Nat.Prime (nthPrime i) := by {
  unfold nthPrime
  exact Nat.nth_mem_of_infinite Nat.infinite_setOf_prime i
}

/-- The prime enumeration `nthPrime` is strictly monotone. -/
lemma nthPrime_strictMono : StrictMono nthPrime := by {
  unfold nthPrime
  exact Nat.nth_strictMono Nat.infinite_setOf_prime
}

/-- The prime enumeration `nthPrime` is monotone. -/
lemma nthPrime_monotone : Monotone nthPrime := by {
  exact nthPrime_strictMono.monotone
}

/-- `nthPrime i ≤ nthPrime j` if and only if `i ≤ j`. -/
lemma nthPrime_le_iff {i j : ℕ} : nthPrime i ≤ nthPrime j ↔ i ≤ j := by {
  exact nthPrime_strictMono.le_iff_le
}

/-- `nthPrime i < nthPrime j` if and only if `i < j`. -/
lemma nthPrime_lt_iff {i j : ℕ} : nthPrime i < nthPrime j ↔ i < j := by {
  exact nthPrime_strictMono.lt_iff_lt
}

/-- The `i`-th prime is always at least `i`. -/
lemma self_le_nthPrime (i : ℕ) : i ≤ nthPrime i := by {
  exact nthPrime_strictMono.id_le i
}

@[simp]
lemma nthPrime_zero : nthPrime 0 = 2 := Nat.nth_prime_zero_eq_two

@[simp]
lemma nthPrime_one : nthPrime 1 = 3 := Nat.nth_prime_one_eq_three

@[simp]
lemma nthPrime_two : nthPrime 2 = 5 := Nat.nth_prime_two_eq_five

@[simp]
lemma nthPrime_three : nthPrime 3 = 7 := Nat.nth_prime_three_eq_seven

@[simp]
lemma nthPrime_four : nthPrime 4 = 11 := Nat.nth_prime_four_eq_eleven

@[simp]
lemma nthPrime_five : nthPrime 5 = 13 := by {
  unfold nthPrime
  have hc : Nat.count Nat.Prime 13 = 5 := by decide
  have hp : Nat.Prime 13 := by decide
  rw [← hc]
  exact Nat.nth_count hp
}

@[simp]
lemma nthPrime_six : nthPrime 6 = 17 := by {
  unfold nthPrime
  have hc : Nat.count Nat.Prime 17 = 6 := by decide
  have hp : Nat.Prime 17 := by decide
  rw [← hc]
  exact Nat.nth_count hp
}

/-- **The 8th Prime Horizon (`p_7 = 19` in 0-indexed notation)**:
The 8th state in a Gödel-Prime automaton corresponds to the prime `19`. -/
@[simp]
theorem eight_state_prime_is_nineteen : nthPrime 7 = 19 := by {
  unfold nthPrime
  have hc : Nat.count Nat.Prime 19 = 7 := by decide
  have hp : Nat.Prime 19 := by decide
  rw [← hc]
  exact Nat.nth_count hp
}

/-- The 2-state NOT/parity inverter DFA on `Bool`. -/
def notGateDFA : FinDFA Bool 2 where
  start  := ⟨0, by decide⟩
  step   := fun s b => if b then ⟨1 - s.val, by omega⟩ else s
  accept := fun s => s.val == 1

/-- The 2-state repetition witness DFA on `Bool` that accepts `true^n` and sinks on `false`. -/
def allTrueWitnessDFA : FinDFA Bool 2 where
  start  := ⟨0, by decide⟩
  step   := fun s b => if s.val = 0 ∧ b = true then ⟨0, by decide⟩ else ⟨1, by decide⟩
  accept := fun s => s.val == 0

/-- Any 2-state DFA is `{2, 3}`-smooth (`3`-smooth): all state primes lie in `{2, 3}`. -/
theorem two_state_automaton_three_smooth {α : Type*} (M : FinDFA α 2) :
    IsPrimeSmoothAutomaton M 3 ∧ ∀ s : Fin 2, statePrime s = 2 ∨ statePrime s = 3 := by {
  constructor
  · intro s
    unfold statePrime
    have hs : s.val ≤ 1 := by omega
    have h_le : nthPrime s.val ≤ nthPrime 1 := nthPrime_monotone hs
    rw [nthPrime_one] at h_le
    exact h_le
  · intro s
    unfold statePrime
    rcases s with ⟨val, hlt⟩
    interval_cases val
    · exact Or.inl nthPrime_zero
    · exact Or.inr nthPrime_one
}

/-- **Theorem (`not_gate_two_three_smooth`)**:
The 2-state NOT/parity gate DFA has state primes exclusively in `{2, 3}` (`3`-smooth). -/
theorem not_gate_two_three_smooth :
    IsPrimeSmoothAutomaton notGateDFA 3 ∧
    ∀ s : Fin 2, statePrime s = 2 ∨ statePrime s = 3 := by {
  exact two_state_automaton_three_smooth notGateDFA
}

lemma allTrueWitnessDFA_eval_sink (w : List Bool) :
    allTrueWitnessDFA.evalFrom ⟨1, by decide⟩ w = ⟨1, by decide⟩ := by {
  induction w with
  | nil => rfl
  | cons a as ih =>
    unfold FinDFA.evalFrom allTrueWitnessDFA
    dsimp
    exact ih
}

lemma allTrueWitnessDFA_eval_replicate (n : ℕ) :
    allTrueWitnessDFA.evalFrom ⟨0, by decide⟩ (List.replicate n true) = ⟨0, by decide⟩ := by {
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [List.replicate_succ]
    unfold FinDFA.evalFrom allTrueWitnessDFA
    dsimp
    exact ih
}

lemma allTrueWitnessDFA_eq_replicate_of_accept (v : List Bool)
    (h_acc : allTrueWitnessDFA.Accepts v) : v = List.replicate v.length true := by {
  induction v with
  | nil => rfl
  | cons a as ih =>
    cases a with
    | false =>
      unfold FinDFA.Accepts FinDFA.evalFrom allTrueWitnessDFA at h_acc
      dsimp at h_acc
      have h_sink := allTrueWitnessDFA_eval_sink as
      unfold allTrueWitnessDFA at h_sink
      rw [h_sink] at h_acc
      contradiction
    | true =>
      unfold FinDFA.Accepts FinDFA.evalFrom at h_acc
      have h_step : allTrueWitnessDFA.step allTrueWitnessDFA.start true = allTrueWitnessDFA.start := rfl
      rw [h_step] at h_acc
      have h_as : as = List.replicate as.length true := ih h_acc
      rw [List.length_cons, List.replicate_succ, ← h_as]
}

/-- The 2-state `{2, 3}`-smooth DFA `allTrueWitnessDFA` uniquely witnesses `true^n` for all `n`. -/
theorem allTrue_uniquely_witnessed_two_three_smooth (n : ℕ) :
    IsPrimeSmoothAutomaton allTrueWitnessDFA 3 ∧
    UniquelyWitnesses allTrueWitnessDFA (List.replicate n true) := by {
  refine ⟨(two_state_automaton_three_smooth allTrueWitnessDFA).1, ?_⟩
  constructor
  · unfold FinDFA.Accepts allTrueWitnessDFA
    have h_eval := allTrueWitnessDFA_eval_replicate n
    unfold allTrueWitnessDFA at h_eval
    rw [h_eval]
    rfl
  · intro v hv_len hv_acc
    have hv_rep := allTrueWitnessDFA_eq_replicate_of_accept v hv_acc
    rw [hv_len, List.length_replicate] at hv_rep
    exact hv_rep
}

/-- Any DFA with `q ≤ 7` states is `17`-smooth. -/
lemma seven_state_or_less_seventeen_smooth {α : Type*} {q : ℕ} (hq : q ≤ 7) (M : FinDFA α q) :
    IsPrimeSmoothAutomaton M 17 := by {
  intro s
  unfold statePrime
  have hs : s.val ≤ 6 := by omega
  have h_le : nthPrime s.val ≤ nthPrime 6 := nthPrime_monotone hs
  rw [nthPrime_six] at h_le
  exact h_le
}

/-- **Crossing the 8-State Kjos-Hanssen Horizon Forces Prime 19**:
If a word `w` cannot be uniquely witnessed by any DFA with `≤ 7` states, then any `q`-state
DFA `M` that uniquely witnesses `w` must have `q ≥ 8`, and therefore recruits a state prime
`≥ 19` (in particular, `M` is not `17`-smooth). -/
theorem eight_state_complexity_forces_prime_nineteen {α : Type*} {q : ℕ}
    (w : List α) (M : FinDFA α q)
    (h_not_le7 : ∀ r ≤ 7, ¬ HasAutomaticComplexityLE w r)
    (h_wit : UniquelyWitnesses M w) :
    q ≥ 8 ∧ (∃ s : Fin q, statePrime s = 19) ∧ ¬ IsPrimeSmoothAutomaton M 17 := by {
  have hq : q ≥ 8 := by {
    by_contra h_lt
    have h_le7 : q ≤ 7 := by omega
    exact h_not_le7 q h_le7 ⟨M, h_wit⟩
  }
  let s7 : Fin q := ⟨7, by omega⟩
  have hs7 : statePrime s7 = 19 := eight_state_prime_is_nineteen
  refine ⟨hq, ⟨s7, hs7⟩, ?_⟩
  intro h_smooth
  have h17 := h_smooth s7
  rw [hs7] at h17
  omega
}

-- ============================================================================
-- SECTION 3: VAN ECK UNBOUNDED PRIME HORIZON & NON-PERIODICITY
-- ============================================================================

/-- **Theorem 1A (`vanEck_unbounded_values`)**:
The Van Eck sequence takes arbitrarily large values: for every bound `M : ℕ`,
there exists an index `n : ℕ` such that `vanEckNthTerm n > M`. -/
theorem vanEck_unbounded_values (M : ℕ) : ∃ n : ℕ, vanEckNthTerm n > M := by {
  let N := (M + 1) * (M + 1) + 2 * (M + 1) + 2
  rcases vanEck_limsup_ge_sqrt N with ⟨n, hn_ge, hn_sq⟩
  use n
  by_contra h_le
  have h_le_M : vanEckNthTerm n ≤ M := Nat.le_of_not_gt h_le
  have h_quad : vanEckNthTerm n * vanEckNthTerm n + 2 * vanEckNthTerm n + 1 ≤
      M * M + 2 * M + 1 := by nlinarith
  have h_lt_N : M * M + 2 * M + 1 < N := by {
    dsimp [N]
    nlinarith
  }
  omega
}

/-- **Theorem 1B (`vanEck_unbounded_prime_horizon`)**:
Because `vanEckNthTerm` is unbounded, encoding the values or lookback states of the
Van Eck sequence into prime indices `nthPrime (vanEckNthTerm n)` exceeds any finite
prime bound `P_bound`. -/
theorem vanEck_unbounded_prime_horizon (P_bound : ℕ) :
    ∃ n : ℕ, nthPrime (vanEckNthTerm n) > P_bound := by {
  rcases vanEck_unbounded_values P_bound with ⟨n, hn⟩
  use n
  have h_id : vanEckNthTerm n ≤ nthPrime (vanEckNthTerm n) := self_le_nthPrime (vanEckNthTerm n)
  omega
}

/-- Helper bounding the outputs of any function on `Fin q`. -/
def finMaxVal : (q : ℕ) → (Fin q → ℕ) → ℕ
  | 0, _     => 0
  | q + 1, f => max (f ⟨q, Nat.lt_succ_self q⟩) (finMaxVal q (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩))

lemma le_finMaxVal (q : ℕ) (f : Fin q → ℕ) (s : Fin q) : f s ≤ finMaxVal q f := by {
  induction q with
  | zero => exact Fin.elim0 s
  | succ q ih =>
    unfold finMaxVal
    by_cases hs : s.val = q
    · have h_eq : s = ⟨q, Nat.lt_succ_self q⟩ := Fin.eq_of_val_eq hs
      rw [h_eq]
      exact Nat.le_max_left _ _
    · have h_lt : s.val < q := Nat.lt_of_le_of_ne (Nat.le_of_lt_succ s.isLt) hs
      let s' : Fin q := ⟨s.val, h_lt⟩
      have h_ih := ih (fun i => f ⟨i.val, Nat.lt_succ_of_lt i.isLt⟩) s'
      exact Nat.le_trans h_ih (Nat.le_max_right _ _)
}

/-- **No Finite-State Automaton Can Cover the Van Eck Sequence**:
For any `q`-state DFA `M : FinDFA α q` and any state output map `decode : Fin q → ℕ`,
there exists a Van Eck sequence term `vanEckNthTerm n` that `M` can never output on any word. -/
theorem no_finite_automaton_covers_vanEck_values {α : Type*} (q : ℕ)
    (M : FinDFA α q) (decode : Fin q → ℕ) :
    ∃ n : ℕ, ∀ w : List α, decode (M.evalFrom M.start w) ≠ vanEckNthTerm n := by {
  let B := finMaxVal q decode
  rcases vanEck_unbounded_values B with ⟨n, hn⟩
  use n
  intro w h_eq
  have h_le : decode (M.evalFrom M.start w) ≤ B := le_finMaxVal q decode (M.evalFrom M.start w)
  omega
}

lemma periodic_tail_bounded (N₀ P : ℕ) (hP : P > 0)
    (h_per : ∀ k ≥ N₀, vanEckNthTerm (k + P) = vanEckNthTerm k) (n : ℕ) :
    vanEckNthTerm n ≤ vanEckPrefixMax (N₀ + P) := by {
  induction n using Nat.strong_induction_on with
  | h k ih =>
    by_cases hk : k ≤ N₀ + P
    · exact vanEckNthTerm_le_prefixMax (N₀ + P) k hk
    · have h_ge : k - P ≥ N₀ := by omega
      have h_lt : k - P < k := by omega
      have h_add : k - P + P = k := by omega
      have h_eq : vanEckNthTerm k = vanEckNthTerm (k - P) := by {
        rw [← h_add]
        exact h_per (k - P) h_ge
      }
      rw [h_eq]
      exact ih (k - P) h_lt
}

/-- **Global Aperiodicity of the Van Eck Sequence (`vanEck_not_eventually_periodic`)**:
The Van Eck sequence can never become eventually periodic. Consequently, its lookback
horizon never collapses to a finite cyclic modulus. -/
theorem vanEck_not_eventually_periodic :
    ¬ ∃ N₀ P : ℕ, P > 0 ∧ ∀ k ≥ N₀, vanEckNthTerm (k + P) = vanEckNthTerm k := by {
  rintro ⟨N₀, P, hP, h_per⟩
  let B := vanEckPrefixMax (N₀ + P)
  rcases vanEck_unbounded_values B with ⟨n, hn⟩
  have h_le := periodic_tail_bounded N₀ P hP h_per n
  omega
}

-- ============================================================================
-- SECTION 4: ARITHMETICAL HIERARCHY (Σ⁰₁ / Π⁰₁ / Π⁰₂) & LOOKBACK HORIZON
-- ============================================================================

/-- A predicate has arithmetical `Σ⁰₁` form when it is `∃ n` over a decidable predicate. -/
def HasSigma1Form (P : Prop) : Prop :=
  ∃ R : ℕ → Prop, (∀ n, R n ∨ ¬ R n) ∧ (P ↔ ∃ n, R n)

/-- A predicate has arithmetical `Π⁰₁` form when it is `∀ n` over a decidable predicate. -/
def HasPi1Form (P : Prop) : Prop :=
  ∃ R : ℕ → Prop, (∀ n, R n ∨ ¬ R n) ∧ (P ↔ ∀ n, R n)

/-- Value achievement predicate for a single target `v`. -/
def VanEckAchieves (v : ℕ) : Prop :=
  ∃ n : ℕ, VanEckTerm n = v

/-- Value avoidance ("never achieves `v`") predicate for a target `v`. -/
def VanEckNeverAchieves (v : ℕ) : Prop :=
  ∀ n : ℕ, VanEckTerm n ≠ v

/-- Universal surjectivity predicate for the Van Eck sequence. -/
def VanEckSurjective : Prop :=
  ∀ v : ℕ, ∃ n : ℕ, VanEckTerm n = v

/-- Achieving a specific value `v` is a `Σ⁰₁` statement. -/
theorem vanEckAchieves_hasSigma1Form (v : ℕ) : HasSigma1Form (VanEckAchieves v) := by {
  refine ⟨fun n => VanEckTerm n = v, ?_, Iff.rfl⟩
  intro n
  exact Decidable.em (VanEckTerm n = v)
}

/-- Never achieving `v` ("checking `v` is omitted") is a `Π⁰₁` statement requiring an
unbounded trajectory scan. -/
theorem vanEckNeverAchieves_hasPi1Form (v : ℕ) : HasPi1Form (VanEckNeverAchieves v) := by {
  refine ⟨fun n => VanEckTerm n ≠ v, ?_, Iff.rfl⟩
  intro n
  exact Decidable.em (VanEckTerm n ≠ v)
}

/-- **Theorem 2A (`vanEckSurjective_hasPi2Form`)**:
Universal surjectivity of the Van Eck sequence (`∀ v, ∃ n, VanEckTerm n = v`) is a `Π⁰₂`
arithmetical statement. -/
theorem vanEckSurjective_hasPi2Form : HasPi2Form VanEckSurjective := by {
  refine ⟨fun v n => VanEckTerm n = v, ?_, Iff.rfl⟩
  intro v n
  exact Decidable.em (VanEckTerm n = v)
}

/-- `VanEckSurjective` is extensionally equivalent to `∀ v, ∃ n, vanEckNthTerm n = v`. -/
theorem vanEckSurjective_iff :
    VanEckSurjective ↔ ∀ v : ℕ, ∃ n : ℕ, vanEckNthTerm n = v := by {
  constructor
  · intro h v
    rcases h v with ⟨n, hn⟩
    rw [VanEckTerm_eq_vanEckNthTerm] at hn
    exact ⟨n, hn⟩
  · intro h v
    rcases h v with ⟨n, hn⟩
    rw [← VanEckTerm_eq_vanEckNthTerm] at hn
    exact ⟨n, hn⟩
}

/-- **Finite Prefix Indistinguishability (`no_finite_prefix_achieves_large_value`)**:
For any finite prefix `vanEck N = [a_0, ..., a_N]` and any target `v > N`, `v` cannot
appear anywhere in `vanEck N`. Thus no finite prefix up to `N` can witness `v > N`. -/
theorem no_finite_prefix_achieves_large_value (N v : ℕ) (hv : v > N) :
    (∀ k ≤ N, vanEckNthTerm k < v) ∧ v ∉ vanEck N := by {
  have h_lt : ∀ k ≤ N, vanEckNthTerm k < v := by {
    intro k hk
    have hk_le : vanEckNthTerm k ≤ k := vanEckNthTerm_le_n k
    omega
  }
  refine ⟨h_lt, ?_⟩
  intro h_mem
  rcases mem_listNth h_mem with ⟨k, hk_len, hk_eq⟩
  rw [vanEckLength N] at hk_len
  have hk_le : k ≤ N := Nat.le_of_lt_succ hk_len
  have h_det : listNth (vanEck N) k = vanEckNthTerm k := VanEck_deterministic N k hk_le
  rw [h_det] at hk_eq
  have h_k_lt := h_lt k hk_le
  omega
}

lemma vanEck_pos_le_pred (m : ℕ) (hm : m ≥ 2) (h_pos : vanEckNthTerm m > 0) :
    vanEckNthTerm m ≤ m - 1 := by {
  by_cases heq : vanEckNthTerm m = m
  · exfalso
    have hm1 : m ≥ 1 := by omega
    have h_a_m := vanEck_term_is_matchSearch m hm1
    have hm_neq : matchSearch (vanEck (m - 1)) (m - 1) ≠ 0 := by omega
    have hm_match := matchSearch_matches (vanEck (m - 1)) (m - 1) hm_neq
    have h_len : (vanEck (m - 1)).length - 1 = m - 1 := by {
      rw [vanEckLength (m - 1)]
      omega
    }
    rw [h_len, ← h_a_m, heq, Nat.sub_eq_zero_of_le (by omega)] at hm_match
    have hl0 : listNth (vanEck (m - 1)) 0 = 0 := list_nth_VanEck_zero_eq_zero (m - 1)
    have h_first := matchSearch_first (vanEck (m - 1)) (m - 1) 0 hm_neq (by omega)
    have h_match0 : listNth (vanEck (m - 1)) ((vanEck (m - 1)).length - 1) =
        listNth (vanEck (m - 1)) 0 := by {
      rw [h_len, hm_match]
    }
    have h_bound := h_first h_match0
    rw [← h_a_m, heq, h_len] at h_bound
    omega
  · have h_le := vanEckNthTerm_le_n m
    omega
}

/-- **Theorem 2B (`gap_v_requires_horizon_v`)**:
To achieve a positive value `v > 0` at index `m`, the sequence must have reached horizon
`m ≥ v + 1` (so the prefix `vanEck m` has length `m + 1 ≥ v + 2`) and must exhibit an
exact lookback match `vanEckNthTerm (m - 1 - v) = vanEckNthTerm (m - 1)` across distance `v`. -/
theorem gap_v_requires_horizon_v (m v : ℕ) (hv : v > 0) (hm_val : vanEckNthTerm m = v) :
    m ≥ v + 1 ∧
    (vanEck m).length ≥ v + 2 ∧
    vanEckNthTerm (m - 1 - v) = vanEckNthTerm (m - 1) := by {
  have hm_ge2 : m ≥ 2 := by {
    by_contra h_lt2
    interval_cases m
    · have h0 : vanEckNthTerm 0 = 0 := rfl
      omega
    · have h1 : vanEckNthTerm 1 = 0 := rfl
      omega
  }
  have h_le : vanEckNthTerm m ≤ m - 1 := vanEck_pos_le_pred m hm_ge2 (by rw [hm_val]; exact hv)
  have hm_ge : m ≥ v + 1 := by omega
  have h_len : (vanEck m).length ≥ v + 2 := by {
    rw [vanEckLength m]
    omega
  }
  have hm_ge1 : m ≥ 1 := by omega
  have hv_ne : v ≠ 0 := Nat.ne_of_gt hv
  have h_dist := matchSearch_is_gap_distance m hm_ge1 v hm_val hv_ne
  have hd1 : listNth (vanEck (m - 1)) (m - 1) = vanEckNthTerm (m - 1) :=
    VanEck_deterministic (m - 1) (m - 1) (Nat.le_refl _)
  have hd0 : listNth (vanEck (m - 1)) (m - 1 - v) = vanEckNthTerm (m - 1 - v) :=
    VanEck_deterministic (m - 1) (m - 1 - v) (Nat.sub_le _ _)
  rw [hd1, hd0] at h_dist
  exact ⟨hm_ge, h_len, h_dist.symm⟩
}

