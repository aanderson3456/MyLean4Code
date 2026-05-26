import Mathlib
import VTlean.CuculiereCombinatorial
open Nat Finset

lemma filter_range_two_step (n : Nat) (f : Nat → Nat) :
  ∑ j ∈ (range (n + 3)).filter (fun j => j % 2 = (n + 2) % 2), f j =
  (∑ j ∈ (range (n + 1)).filter (fun j => j % 2 = n % 2), f j) + f (n + 2) := by
  have h_mod : (n + 2) % 2 = n % 2 := by omega
  have h_range : range (n + 3) = insert (n + 2) (insert (n + 1) (range (n + 1))) := by
    ext x
    simp only [mem_range, mem_insert]
    omega
  rw [h_range]
  rw [filter_insert, filter_insert]
  have h_n1 : ¬ ((n + 1) % 2 = (n + 2) % 2) := by omega
  have h_n2 : (n + 2) % 2 = (n + 2) % 2 := rfl
  rw [if_neg h_n1, if_pos h_n2]
  rw [sum_insert]
  · rw [h_mod]
    exact add_comm _ _
  · simp only [mem_filter, mem_range, not_and]
    intro h_lt h_eq
    omega

lemma filter_range_one_step_0 (f : Nat → Nat) :
  ∑ j ∈ (range 1).filter (fun j => j % 2 = 0), f j = f 0 := by
  have hr : range 1 = {0} := rfl
  rw [hr, filter_singleton, if_pos (rfl : 0 % 2 = 0), sum_singleton]

lemma filter_range_one_step_1 (f : Nat → Nat) :
  ∑ j ∈ (range 2).filter (fun j => j % 2 = 1), f j = f 1 := by
  have hr : range 2 = {0, 1} := rfl
  rw [hr]
  have h_filt : ({0, 1} : Finset Nat).filter (fun j => j % 2 = 1) = {1} := by
    ext x
    simp only [mem_filter, mem_insert, mem_singleton]
    omega
  rw [h_filt, sum_singleton]

lemma telescope_sum (S T : Nat → Nat) (h : ∀ k > 0, S k = T k + T (k - 1)) (h0 : S 0 = T 0) :
  ∀ n, ∑ k ∈ range (n + 1), T k = ∑ j ∈ (range (n + 1)).filter (fun j => j % 2 = n % 2), S j := by
  intro n
  induction' n using Nat.twoStepInduction with n ih1 ih2
  · have h_rhs : ∑ j ∈ (range (0 + 1)).filter (fun j => j % 2 = 0 % 2), S j = S 0 := filter_range_one_step_0 S
    rw [h_rhs]
    simp [h0]
  · have h_rhs : ∑ j ∈ (range (1 + 1)).filter (fun j => j % 2 = 1 % 2), S j = S 1 := filter_range_one_step_1 S
    rw [h_rhs]
    have h_lhs : ∑ k ∈ range (1 + 1), T k = T 0 + T 1 := by
      rw [sum_range_succ, sum_range_succ, range_zero, sum_empty, zero_add]
    rw [h_lhs]
    have h1 : S 1 = T 1 + T 0 := h 1 (by omega)
    omega
  · rw [sum_range_succ, sum_range_succ, ih1]
    have hn2 : S (n + 2) = T (n + 2) + T (n + 1) := h (n + 2) (by omega)
    have h_filt := filter_range_two_step n S
    rw [h_filt]
    omega

lemma S_zero_eq_T_zero (n a : Nat) : S n 0 a = T n 0 a := by
  unfold S T S_set T_set
  congr 1
  ext s
  simp only [mem_filter, mem_univ, true_and]
  apply Iff.intro
  · intro h
    refine ⟨h.1, ?_, h.2⟩
    have h_empty : s = ∅ := Finset.card_eq_zero.mp h.1
    rw [h_empty]
    simp
  · intro h
    exact ⟨h.1, h.2.2⟩
