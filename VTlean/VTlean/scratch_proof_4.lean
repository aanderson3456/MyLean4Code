import Mathlib
import VTlean.VTCode
import VTlean.NumOsNumIs
import VTlean.DelCode
import VTlean.CuculiereCombinatorial

open Nat Finset B List.Vector

lemma list_to_subset_sum (X : List B) :
  ∑ i ∈ list_to_subset X, i = List.moment X := by {
  induction X with
  | nil => rfl
  | cons x X' ih =>
    have h_inj : Set.InjOn (· + 1) ↑(list_to_subset X') := by {
      intro a _ b _ hab
      exact Nat.add_right_cancel hab
    }
    have h_sum_add : ∑ i ∈ (list_to_subset X').image (· + 1), i = (∑ i ∈ list_to_subset X', i) + (list_to_subset X').card := by {
      rw [Finset.sum_image h_inj]
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
    }
    cases x
    · change ∑ i ∈ (list_to_subset X').image (· + 1), i = List.moment (B.O :: X')
      rw [h_sum_add, ih, list_to_subset_card X']
      have h_mom := moment_cons B.O X'
      have h_num : num_Is (B.O :: X') = num_Is X' := rfl
      rw [h_num] at h_mom
      exact h_mom.symm
    · change (∑ i ∈ insert 1 ((list_to_subset X').image (· + 1)), i) = List.moment (B.I :: X')
      have h_not_mem : 1 ∉ (list_to_subset X').image (· + 1) := by {
        simp only [mem_image, not_exists, not_and]
        intro a ha h_eq
        have ha_zero : a = 0 := by omega
        rw [ha_zero] at ha
        have hz := list_to_subset_not_zero X'
        exact hz ha
      }
      rw [Finset.sum_insert h_not_mem]
      rw [h_sum_add, ih, list_to_subset_card X']
      have h_mom := moment_cons B.I X'
      have h_num : num_Is (B.I :: X') = num_Is X' + 1 := rfl
      rw [h_num] at h_mom
      omega
}
