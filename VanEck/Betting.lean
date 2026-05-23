import VanEck
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.BigOperators.Intervals

open Finset
open scoped BigOperators

def sup_n (n : ℕ) (_hn : n ≥ 1) : ℚ := (vanEckPrefixMax n : ℚ) / (n : ℚ)

def na_n (n : ℕ) (_hn : n ≥ 1) : ℚ := 1 - (vanEckNthTerm n : ℚ) / (n : ℚ)

def freq_2 (n : ℕ) (_hn : n ≥ 1) : ℚ := if vanEckNthTerm n = 2 then 1 else 0

def window_sum (M : ∀ n : ℕ, n ≥ 1 → ℚ) (start W : ℕ) (h_start : start ≥ 1) : ℚ :=
  (Ico start (start + W)).attach.sum (fun i => M i.val (by {
    have h1 : start ≤ i.val := (mem_Ico.mp i.property).left
    omega
  }))

def mu_past (M : ∀ n : ℕ, n ≥ 1 → ℚ) (N W : ℕ) (hN : N ≥ W + 1) : ℚ :=
  let start := N - W
  have h_start : start ≥ 1 := by {
    omega
  }
  (window_sum M start W h_start) / (W : ℚ)

def mu_future (M : ∀ n : ℕ, n ≥ 1 → ℚ) (N W : ℕ) (hN : N ≥ 1) : ℚ :=
  (window_sum M N W hN) / (W : ℚ)

def bet_increase_wins (M : ∀ n : ℕ, n ≥ 1 → ℚ) (N W : ℕ) (hN : N ≥ W + 1) : Prop :=
  have h_fut_N : N ≥ 1 := by omega
  mu_future M N W h_fut_N > mu_past M N W hN

def bet_decrease_wins (M : ∀ n : ℕ, n ≥ 1 → ℚ) (N W : ℕ) (hN : N ≥ W + 1) : Prop :=
  have h_fut_N : N ≥ 1 := by omega
  mu_future M N W h_fut_N < mu_past M N W hN

lemma na_n_local_jump {N : ℕ} (h_zero : vanEckNthTerm N = 0) (hN : N ≥ 1) :
  na_n N hN = 1 := by {
    unfold na_n
    rw [h_zero]
    simp
}

lemma sup_n_asymptotic_decay {N : ℕ} (hN : N ≥ 1) (h_bound : vanEckPrefixMax (N + 1) = vanEckPrefixMax N) :
  sup_n (N + 1) (by omega) < sup_n N hN := by {
    sorry
}
