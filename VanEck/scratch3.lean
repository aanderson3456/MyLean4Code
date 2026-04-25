import VanEck
import Mathlib.Data.Finset.Basic

open Finset

def zerosCount : ℕ → ℕ
  | 0 => 1
  | m + 1 => if vanEckNthTerm (m + 1) = 0 then zerosCount m + 1 else zerosCount m

def is_bound (n v : ℕ) : Prop := ∀ i ≤ n, vanEckNthTerm i ≤ v

/-- 
The zerosCount counts the number of zeros, which matches the filter cardinality plus 1.
-/
lemma zerosCount_eq_card (m : ℕ) : 
    zerosCount m = ((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)).card + 1 := by
  sorry

/-- 
If two different indices are both followed by a zero, their values must be strictly distinct.
-/
lemma zero_predecessors_inj {i j : ℕ} (hi : vanEckNthTerm (i + 1) = 0) 
    (hj : vanEckNthTerm (j + 1) = 0) (hneq : i ≠ j) : vanEckNthTerm i ≠ vanEckNthTerm j := by
  sorry

/-- 
Because the predecessors are injective, mapping the filter through the sequence preserves cardinality.
-/
lemma zero_predecessors_card (m : ℕ) : 
    ((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)).card = 
    (((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)).image vanEckNthTerm).card := by
  sorry

/-- 
Any element drawn from the predecessor image is bounded by our global max limit v.
-/
lemma zero_predecessors_bounded (m n v : ℕ) (h_le : m ≤ n) (h_bound : is_bound n v) : 
    ∀ x ∈ ((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)).image vanEckNthTerm, x ≤ v := by
  sorry

/-- 
A basic Finset principle: A set of natural numbers bounded by v has size at most v + 1.
-/
lemma subset_range_card (S : Finset ℕ) (v : ℕ) (h_bound : ∀ x ∈ S, x ≤ v) : S.card ≤ v + 1 := by
  sorry

/-- 
Lemma 1: The number of zeros is bounded by v + 2.
Proof Idea: Each zero (after the first) corresponds to a new, distinct number 
in the sequence. Since all numbers are ≤ v, there are at most v + 1 such numbers.
Hence zerosCount m ≤ v + 2.
-/
lemma zerosCount_le_bound (m n v : ℕ) (h_le : m ≤ n) (h_bound : is_bound n v) :
    zerosCount m ≤ v + 2 := by
  -- We establish the structural equivalence of our zeros count to the filter cardinality.
  have h_count := zerosCount_eq_card m
  -- We establish the cardinality of the mapped image set exactly matches the filter.
  have h_img := zero_predecessors_card m
  -- We extract our bounded sequence property localized to the image elements.
  have h_bnd := zero_predecessors_bounded m n v h_le h_bound
  -- We bind our bounding parameter limit to the finite set size principle natively.
  have h_size := subset_range_card (((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)).image vanEckNthTerm) v h_bnd
  -- We substitute the cardinality equivalence to bind our count variable.
  rw [← h_img] at h_size
  -- We algebraically apply the additive bounds across our integer limits.
  have h_add : ((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)).card + 1 ≤ v + 1 + 1 := Nat.add_le_add_right h_size 1
  -- We natively rewrite the count equivalence perfectly.
  rw [← h_count] at h_add
  -- We close the bound.
  exact h_add
