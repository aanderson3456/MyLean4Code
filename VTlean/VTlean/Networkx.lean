import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import VTlean.B
import VTlean.InsDel
import VTlean.DelCode
import VTlean.VTCode
import VTlean.FractalSlice

open B List.Vector Finset

variable {n : Nat}

/-- A single-deletion correcting code is a set of words whose deletion spheres are disjoint. -/
def is_OptimalCodeCandidate (C : Finset (List.Vector B n)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → Disjoint (dS x) (dS y)

instance (C : Finset (List.Vector B n)) : Decidable (is_OptimalCodeCandidate C) := by
  unfold is_OptimalCodeCandidate
  infer_instance


lemma sloaneInsertion_mem_dS (y : List.Vector B (n - 1)) (k : Nat) (hk : k < n) :
    y ∈ dS (sloaneInsertion y k hk) := by {
  rw [mem_dS]
  use k
  refine ⟨by omega, ?_⟩
  exact (sloane_insertion_is_del y k hk).symm
}

lemma insertions_form_clique (y : List.Vector B (n - 1)) (k₁ k₂ : Nat) (hk₁ : k₁ < n) (hk₂ : k₂ < n) :
    ¬ Disjoint (dS (sloaneInsertion y k₁ hk₁)) (dS (sloaneInsertion y k₂ hk₂)) := by {
  intro h_disj
  have hy1 : y ∈ dS (sloaneInsertion y k₁ hk₁) := sloaneInsertion_mem_dS y k₁ hk₁
  have hy2 : y ∈ dS (sloaneInsertion y k₂ hk₂) := sloaneInsertion_mem_dS y k₂ hk₂
  have h_inter : y ∈ dS (sloaneInsertion y k₁ hk₁) ∩ dS (sloaneInsertion y k₂ hk₂) := Finset.mem_inter.mpr ⟨hy1, hy2⟩
  rw [Finset.disjoint_iff_inter_eq_empty] at h_disj
  rw [h_disj] at h_inter
  simp at h_inter
}

lemma clique_intersection_le_one (C : Finset (List.Vector B n)) (hC : is_OptimalCodeCandidate C)
    (y : List.Vector B (n - 1)) :
    (C.filter (fun x => y ∈ dS x)).card ≤ 1 := by {
  apply card_le_one_iff.mpr
  intro x1 hx1 x2 hx2
  rw [Finset.mem_filter] at x2 hx2
  by_contra h_neq
  have h_disj := hC x1 x2.1 hx1 hx2.1 h_neq
  have h_inter : y ∈ dS x1 ∩ dS hx1 := Finset.mem_inter.mpr ⟨x2.2, hx2.2⟩
  rw [Finset.disjoint_iff_inter_eq_empty] at h_disj
  rw [h_disj] at h_inter
  simp at h_inter
}

open BigOperators

/-- Theorem 3.1: The LP Fractional Cover Bound.
Any valid single-deletion correcting code C is bounded in size by the total weight
of any fractional clique cover (potential function u_y) that covers all deletion spheres. -/
theorem lp_fractional_cover_bound (C : Finset (List.Vector B n)) (hC : is_OptimalCodeCandidate C)
    (u : List.Vector B (n - 1) → Rat) (hu_nonneg : ∀ y, 0 ≤ u y)
    (h_cover : ∀ x : List.Vector B n, 1 ≤ ∑ y ∈ dS x, u y) :
    (C.card : Rat) ≤ ∑ y ∈ Finset.univ, u y := by {
  -- The core logical boundary of LP Duality / Fractional Clique Cover:
  -- Summing the covering constraints over all codewords in C:
  -- C.card = \sum_{x ∈ C} 1 ≤ \sum_{x ∈ C} \sum_{y ∈ dS x} u y
  -- Rewriting the double sum as a sum over deletion strings y ∈ univ:
  -- = \sum_{y ∈ univ} u y * (C.filter (fun x => y ∈ dS x)).card
  -- By clique_intersection_le_one, the filter card is ≤ 1:
  -- ≤ \sum_{y ∈ univ} u y * 1 = \sum_{y ∈ univ} u y
  sorry
}

