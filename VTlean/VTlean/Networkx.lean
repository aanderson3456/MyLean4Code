/- Copyright Austin Anderson aided by Gemini 2026 -/
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import VTlean.B
import VTlean.InsDel
import VTlean.DelCode
import VTlean.VTCode
import VTlean.FractalSlice
import Mathlib.Tactic.ApplyFun

open B List.Vector Finset

variable {n : Nat}

/-- A single-deletion correcting code is a set of words whose deletion spheres are disjoint. -/
def is_OptimalCodeCandidate (C : Finset (List.Vector B n)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → Disjoint (dS x) (dS y)

instance (C : Finset (List.Vector B n)) : Decidable (is_OptimalCodeCandidate C) := by {
  unfold is_OptimalCodeCandidate
  infer_instance
}


lemma sloaneInsertion_mem_dS (y : List.Vector B (n - 1)) (k : Nat) (hk : k < n) :
    y ∈ dS (sloaneInsertion y k hk) := by {
  rw [mem_dS]
  use k
  refine ⟨by omega, ?_⟩
  exact (sloane_insertion_is_del y k hk).symm
}

lemma insertions_form_clique (y : List.Vector B (n - 1)) (k₁ k₂ : Nat) (hk₁ : k₁ < n)
    (hk₂ : k₂ < n) :
    ¬ Disjoint (dS (sloaneInsertion y k₁ hk₁)) (dS (sloaneInsertion y k₂ hk₂)) := by {
  intro h_disj
  have hy1 : y ∈ dS (sloaneInsertion y k₁ hk₁) := sloaneInsertion_mem_dS y k₁ hk₁
  have hy2 : y ∈ dS (sloaneInsertion y k₂ hk₂) := sloaneInsertion_mem_dS y k₂ hk₂
  have h_inter : y ∈ dS (sloaneInsertion y k₁ hk₁) ∩ dS (sloaneInsertion y k₂ hk₂) :=
    Finset.mem_inter.mpr ⟨hy1, hy2⟩
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

lemma sum_dS_eq_sum_ite (x : List.Vector B n) (u : List.Vector B (n - 1) → Rat) :
    (∑ y ∈ dS x, u y) = ∑ y ∈ Finset.univ, if y ∈ dS x then u y else 0 := by {
  rw [sum_ite]
  have h_zero : ∑ y ∈ filter (fun y => ¬ y ∈ dS x) univ, (0 : Rat) = 0 := by simp
  rw [h_zero, add_zero]
  have h_filter : filter (fun y => y ∈ dS x) univ = dS x := by {
    ext y
    simp
  }
  rw [h_filter]
}

lemma vector_sDel_eq_sDel_of_getD_eq (x : List.Vector B n) (k : Nat) (hk : k < n) (hk_pos : 0 < k)
    (h_eq : x.val.getD k B.O = x.val.getD (k - 1) B.O) :
    sDel x k = sDel x (k - 1) := by {
  apply Subtype.ext
  change List.sDel x.val k = List.sDel x.val (k - 1)
  apply sDel_eq_sDel_of_getD_eq x.val k
  · have h_len := x.property
    omega
  · exact hk_pos
  · exact h_eq
}

lemma sDel_mem_dS_le_of_getD_eq (x : List.Vector B n) (k : Nat) (hk : k < n) (hk_pos : 0 < k)
    (h_eq : x.val.getD k B.O = x.val.getD (k - 1) B.O) :
    sDel x k ∈ dS_le x (k - 1) := by {
  rw [mem_dS_le]
  use k - 1
  constructor
  · omega
  · exact vector_sDel_eq_sDel_of_getD_eq x k hk hk_pos h_eq
}

lemma cumulativeDels_step_inside_run (x : List.Vector B n) (k' : Nat) (hk : k' + 1 < n)
    (h_eq : x.val.getD (k' + 1) B.O = x.val.getD k' B.O) :
    cumulativeDels x (k' + 2) = cumulativeDels x (k' + 1) := by {
  dsimp [cumulativeDels]
  dsimp [dS_le]
  rw [List.toFinset_cons]
  have h_mem : sDel x (k' + 1) ∈ List.toFinset (dS_le x k') := by {
    rw [List.mem_toFinset]
    exact sDel_mem_dS_le_of_getD_eq x (k' + 1) hk (by omega) h_eq
  }
  exact Finset.insert_eq_of_mem h_mem
}

lemma cumulativeDels_succ (x : List.Vector B n) (k' : Nat) :
    cumulativeDels x (k' + 1) = insert (sDel x k') (cumulativeDels x k') := by {
  cases k' with
  | zero =>
    dsimp [cumulativeDels, dS_le]
    rfl
  | succ k'' =>
    dsimp [cumulativeDels, dS_le]
    rw [List.toFinset_cons]
}

/-- Theorem 3.1: The LP Fractional Cover Bound.
Bounds code size by the total weight of any fractional clique cover. -/
theorem lp_fractional_cover_bound (C : Finset (List.Vector B n)) (hC : is_OptimalCodeCandidate C)
    (u : List.Vector B (n - 1) → Rat) (hu_nonneg : ∀ y, 0 ≤ u y)
    (h_cover : ∀ x : List.Vector B n, 1 ≤ ∑ y ∈ dS x, u y) :
    (C.card : Rat) ≤ ∑ y ∈ Finset.univ, u y := by {
  have h_k : ∀ x : List.Vector B n, ∀ k ≤ n, (cumulativeDels x k).card ≤ k := by {
    intro x k hk
    induction k with
    | zero =>
      simp [cumulativeDels]
    | succ k' ih =>
      have hk' : k' ≤ n := by omega
      have ih' := ih hk'
      rw [cumulativeDels_succ]
      have h_card_le := card_insert_le (sDel x k') (cumulativeDels x k')
      omega
  }
  have h_le1 : (C.card : Rat) ≤ ∑ x ∈ C, ∑ y ∈ dS x, u y := by {
    have h_c_eq : (C.card : Rat) = ∑ x ∈ C, (1 : Rat) := by simp
    rw [h_c_eq]
    apply sum_le_sum
    intro x _
    exact h_cover x
  }
  have h_swap : (∑ x ∈ C, ∑ y ∈ dS x, u y) = ∑ y ∈ Finset.univ, ((C.filter (fun x => y ∈ dS x)).card : Rat) * u y := by {
    have h1 : (∑ x ∈ C, ∑ y ∈ dS x, u y) = ∑ x ∈ C, ∑ y ∈ Finset.univ, if y ∈ dS x then u y else 0 := by {
      apply sum_congr rfl
      intro x _
      exact sum_dS_eq_sum_ite x u
    }
    rw [h1]
    rw [sum_comm]
    apply sum_congr rfl
    intro y _
    rw [sum_ite]
    have h_zero : ∑ x ∈ filter (fun x => ¬ y ∈ dS x) C, (0 : Rat) = 0 := by simp
    rw [h_zero, add_zero]
    rw [sum_const]
    simp
  }
  have h_le2 : (∑ y ∈ Finset.univ, ((C.filter (fun x => y ∈ dS x)).card : Rat) * u y) ≤ ∑ y ∈ Finset.univ, u y := by {
    apply sum_le_sum
    intro y _
    have h_card := clique_intersection_le_one C hC y
    have h_card_rat : ((C.filter (fun x => y ∈ dS x)).card : Rat) ≤ 1 := by {
      exact_mod_cast h_card
    }
    have h_nonneg := hu_nonneg y
    nlinarith
  }
  linarith
}
