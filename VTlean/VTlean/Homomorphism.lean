import Mathlib
import VTlean.DelCode
import VTlean.VTCode
import VTlean.Optimal

open Nat List.Vector Finset

variable {α : Type} [DecidableEq α] [Fintype α]
variable {n : Nat}

/-- Topological proxy for an independent set in the graph $G_n$, 
    implicitly modeled as a DelCode. -/
def IndepSet (n : Nat) :=
  { C : Finset (List.Vector B n) // is_DelCode C }

/-- Topological proxy for the maximal independent set in $G_n$. -/
def is_MaximalIndepSet {n : Nat} (I : IndepSet n) : Prop :=
  ∀ C' : Finset (List.Vector B n), is_DelCode C' → Finset.card C' ≤ Finset.card I.val

/-- Transition vector mapping the differential expansion of the independent set 
    from length $n$ to length $n+1$. -/
structure TransitionVector (n : Nat) where
  source : IndepSet n
  target : IndepSet (n + 1)
  mapping : List.Vector B n → List.Vector B (n + 1)
  valid : ∀ x ∈ source.val, mapping x ∈ target.val

/-- $00w$ prefix logic scaling operation. -/
def prefix_00 {n : Nat} (w : List.Vector B n) : List.Vector B (n + 2) :=
  ⟨B.O :: B.O :: w.val, by rw [List.length_cons, List.length_cons, w.property]⟩

/-- $11w$ prefix logic scaling operation. -/
def prefix_11 {n : Nat} (w : List.Vector B n) : List.Vector B (n + 2) :=
  ⟨B.I :: B.I :: w.val, by rw [List.length_cons, List.length_cons, w.property]⟩

/-- Lifting an independent set using $00w$ prefix logic. -/
def lift_00 {n : Nat} (C : Finset (List.Vector B n)) : Finset (List.Vector B (n + 2)) :=
  C.image prefix_00

/-- Lifting an independent set using $11w$ prefix logic. -/
def lift_11 {n : Nat} (C : Finset (List.Vector B n)) : Finset (List.Vector B (n + 2)) :=
  C.image prefix_11

/-- Pre-requisite cases for prefix mapping using lists to avoid dependent type casts. -/
lemma dS_prefix_00_cases {n : Nat} (x : List.Vector B n) (z : List.Vector B (n + 1)) :
  z ∈ dS (prefix_00 x) → 
  z.val = (B.O :: x.val) ∨ ∃ x', x' ∈ dS x ∧ z.val = (B.O :: B.O :: x'.val) := by {
  sorry
}

lemma dS_prefix_11_cases {n : Nat} (x : List.Vector B n) (z : List.Vector B (n + 1)) :
  z ∈ dS (prefix_11 x) → 
  z.val = (B.I :: x.val) ∨ ∃ x', x' ∈ dS x ∧ z.val = (B.I :: B.I :: x'.val) := by {
  sorry
}

lemma cons_eq_cons_inv_list {b : B} {v1 v2 : List B} :
  (b :: v1 = b :: v2) → (v1 = v2) := by {
  sorry
}

lemma vector_val_eq {n : Nat} {v1 v2 : List.Vector B n} :
  v1.val = v2.val → v1 = v2 := Subtype.ext

lemma mem_dS_of_list_eq_O {n : Nat} {x : List.Vector B n} {y' : List.Vector B (n - 1)} :
  x.val = B.O :: y'.val → y' ∈ dS x := by {
  sorry
}

lemma mem_dS_of_list_eq_I {n : Nat} {x : List.Vector B n} {y' : List.Vector B (n - 1)} :
  x.val = B.I :: y'.val → y' ∈ dS x := by {
  sorry
}

lemma list_O_neq_I {v1 v2 : List B} :
  (B.O :: v1 = B.I :: v2) → False := by {
  sorry
}

lemma dS_nonempty_intersect_self {n : Nat} (x : List.Vector B n) (H : ∀ a ∈ dS x, a ∉ dS x) : False := by {
  sorry
}



/-- Pre-requisite sub-lemma for prefix_00 disjointness -/
lemma dS_prefix_00_disjoint {n : Nat} (x y : List.Vector B n) (H : dS x ∩ dS y = ∅) :
  dS (prefix_00 x) ∩ dS (prefix_00 y) = ∅ := by {
  rw [← Finset.disjoint_iff_inter_eq_empty] at H ⊢
  rw [Finset.disjoint_left] at H ⊢
  intro z hzx hzy
  have hx_cases := dS_prefix_00_cases x z hzx
  have hy_cases := dS_prefix_00_cases y z hzy
  rcases hx_cases with hx_eq1 | ⟨x', hx'_mem, hx'_eq2⟩
  · rcases hy_cases with hy_eq1 | ⟨y', hy'_mem, hy'_eq2⟩
    · have hxy : B.O :: x.val = B.O :: y.val := hx_eq1.symm.trans hy_eq1
      have hxy_eq := cons_eq_cons_inv_list hxy
      have hxy_vec := vector_val_eq hxy_eq
      rw [hxy_vec] at H
      exact dS_nonempty_intersect_self y H
    · have hxy : B.O :: x.val = B.O :: B.O :: y'.val := hx_eq1.symm.trans hy'_eq2
      have hxy_eq : x.val = B.O :: y'.val := cons_eq_cons_inv_list hxy
      have hy'_in_x : y' ∈ dS x := mem_dS_of_list_eq_O hxy_eq
      exact H hy'_in_x hy'_mem
  · rcases hy_cases with hy_eq1 | ⟨y', hy'_mem, hy'_eq2⟩
    · have hyx : B.O :: y.val = B.O :: B.O :: x'.val := hy_eq1.symm.trans hx'_eq2
      have hyx_eq : y.val = B.O :: x'.val := cons_eq_cons_inv_list hyx
      have hx'_in_y : x' ∈ dS y := mem_dS_of_list_eq_O hyx_eq
      exact H hx'_mem hx'_in_y
    · have hx'y' : B.O :: B.O :: x'.val = B.O :: B.O :: y'.val := hx'_eq2.symm.trans hy'_eq2
      have h_inv1 := cons_eq_cons_inv_list hx'y'
      have h_inv2 := cons_eq_cons_inv_list h_inv1
      have hx'y'_eq := vector_val_eq h_inv2
      rw [hx'y'_eq] at hx'_mem
      exact H hx'_mem hy'_mem
}

/-- Sub-lemma 1: The $00w$ prefix mapping preserves the DelCode property (independent set),
    ensuring topological bounds are preserved recursively. -/
lemma is_DelCode_lift_00 {n : Nat} {C : Finset (List.Vector B n)} (HC : is_DelCode C) :
  is_DelCode (lift_00 C) := by {
  unfold is_DelCode at HC ⊢
  unfold lift_00
  intro x' hx' y' hy' hx'y'
  rw [Finset.mem_image] at hx' hy'
  rcases hx' with ⟨x, hx_mem, hx_eq⟩
  rcases hy' with ⟨y, hy_mem, hy_eq⟩
  have hxy : x ≠ y := by
    intro h
    rw [h] at hx_eq
    have h_eq : x' = y' := hx_eq.symm.trans hy_eq
    contradiction
  have H_disj := HC x hx_mem y hy_mem hxy
  have h_disj_mapped := dS_prefix_00_disjoint x y H_disj
  rw [← hx_eq, ← hy_eq]
  exact h_disj_mapped
}

/-- Pre-requisite sub-lemma for prefix_11 disjointness -/
lemma dS_prefix_11_disjoint {n : Nat} (x y : List.Vector B n) (H : dS x ∩ dS y = ∅) :
  dS (prefix_11 x) ∩ dS (prefix_11 y) = ∅ := by {
  rw [← Finset.disjoint_iff_inter_eq_empty] at H ⊢
  rw [Finset.disjoint_left] at H ⊢
  intro z hzx hzy
  have hx_cases := dS_prefix_11_cases x z hzx
  have hy_cases := dS_prefix_11_cases y z hzy
  rcases hx_cases with hx_eq1 | ⟨x', hx'_mem, hx'_eq2⟩
  · rcases hy_cases with hy_eq1 | ⟨y', hy'_mem, hy'_eq2⟩
    · have hxy : B.I :: x.val = B.I :: y.val := hx_eq1.symm.trans hy_eq1
      have hxy_eq := cons_eq_cons_inv_list hxy
      have hxy_vec := vector_val_eq hxy_eq
      rw [hxy_vec] at H
      exact dS_nonempty_intersect_self y H
    · have hxy : B.I :: x.val = B.I :: B.I :: y'.val := hx_eq1.symm.trans hy'_eq2
      have hxy_eq : x.val = B.I :: y'.val := cons_eq_cons_inv_list hxy
      have hy'_in_x : y' ∈ dS x := mem_dS_of_list_eq_I hxy_eq
      exact H hy'_in_x hy'_mem
  · rcases hy_cases with hy_eq1 | ⟨y', hy'_mem, hy'_eq2⟩
    · have hyx : B.I :: y.val = B.I :: B.I :: x'.val := hy_eq1.symm.trans hx'_eq2
      have hyx_eq : y.val = B.I :: x'.val := cons_eq_cons_inv_list hyx
      have hx'_in_y : x' ∈ dS y := mem_dS_of_list_eq_I hyx_eq
      exact H hx'_mem hx'_in_y
    · have hx'y' : B.I :: B.I :: x'.val = B.I :: B.I :: y'.val := hx'_eq2.symm.trans hy'_eq2
      have h_inv1 := cons_eq_cons_inv_list hx'y'
      have h_inv2 := cons_eq_cons_inv_list h_inv1
      have hx'y'_eq := vector_val_eq h_inv2
      rw [hx'y'_eq] at hx'_mem
      exact H hx'_mem hy'_mem
}

/-- Sub-lemma 2: The $11w$ prefix mapping preserves the DelCode property (independent set),
    ensuring topological bounds are preserved recursively. -/
lemma is_DelCode_lift_11 {n : Nat} {C : Finset (List.Vector B n)} (HC : is_DelCode C) :
  is_DelCode (lift_11 C) := by {
  unfold is_DelCode at HC ⊢
  unfold lift_11
  intro x' hx' y' hy' hx'y'
  rw [Finset.mem_image] at hx' hy'
  rcases hx' with ⟨x, hx_mem, hx_eq⟩
  rcases hy' with ⟨y, hy_mem, hy_eq⟩
  have hxy : x ≠ y := by
    intro h
    rw [h] at hx_eq
    have h_eq : x' = y' := hx_eq.symm.trans hy_eq
    contradiction
  have H_disj := HC x hx_mem y hy_mem hxy
  have h_disj_mapped := dS_prefix_11_disjoint x y H_disj
  rw [← hx_eq, ← hy_eq]
  exact h_disj_mapped
}

/-- Disjointness of 00w and 11w lifts. -/
lemma lift_00_11_disjoint {n : Nat} (C : Finset (List.Vector B n)) :
  ∀ x ∈ lift_00 C, ∀ y ∈ lift_11 C, dS x ∩ dS y = ∅ := by {
  intro x hx y hy
  unfold lift_00 at hx
  unfold lift_11 at hy
  rw [Finset.mem_image] at hx
  rw [Finset.mem_image] at hy
  rcases hx with ⟨x', hx'_mem, hx'_eq⟩
  rcases hy with ⟨y', hy'_mem, hy'_eq⟩
  rw [← hx'_eq, ← hy'_eq]
  rw [← Finset.disjoint_iff_inter_eq_empty]
  rw [Finset.disjoint_left]
  intro z hzx hzy
  have hx_cases := dS_prefix_00_cases x' z hzx
  have hy_cases := dS_prefix_11_cases y' z hzy
  rcases hx_cases with hx_eq1 | ⟨x'', hx''_mem, hx''_eq2⟩
  · rcases hy_cases with hy_eq1 | ⟨y'', hy''_mem, hy''_eq2⟩
    · have hxy : B.O :: x'.val = B.I :: y'.val := hx_eq1.symm.trans hy_eq1
      exact list_O_neq_I hxy
    · have hxy : B.O :: x'.val = B.I :: B.I :: y''.val := hx_eq1.symm.trans hy''_eq2
      exact list_O_neq_I hxy
  · rcases hy_cases with hy_eq1 | ⟨y'', hy''_mem, hy''_eq2⟩
    · have hyx : B.O :: B.O :: x''.val = B.I :: y'.val := hx''_eq2.symm.trans hy_eq1
      exact list_O_neq_I hyx
    · have hx'y' : B.O :: B.O :: x''.val = B.I :: B.I :: y''.val := hx''_eq2.symm.trans hy''_eq2
      exact list_O_neq_I hx'y'
}

/-- Union of lifts is a DelCode. -/
lemma is_DelCode_union_lifts {n : Nat} {C : Finset (List.Vector B n)} (HC : is_DelCode C) :
  is_DelCode (lift_00 C ∪ lift_11 C) := by {
  unfold is_DelCode
  intro x hx y hy hxy
  rw [Finset.mem_union] at hx hy
  cases hx with
  | inl hx00 => 
    cases hy with
    | inl hy00 => exact is_DelCode_lift_00 HC x hx00 y hy00 hxy
    | inr hy11 => exact lift_00_11_disjoint C x hx00 y hy11
  | inr hx11 =>
    cases hy with
    | inl hy00 => 
      have h := lift_00_11_disjoint C y hy00 x hx11
      rw [Finset.inter_comm]
      exact h
    | inr hy11 => exact is_DelCode_lift_11 HC x hx11 y hy11 hxy
}

/-- Optional assumption of VT code optimality for general n.
    While proved for n <= 7 in Optimal_VTCode.lean, we state the general premise here. -/
def is_optimal_VT (n : Nat) : Prop :=
  is_optimal (Finset.VTCode n 0) (Finset.DelCode_VTCode n 0)

/-- Capping theorem: The recursive operation multipliers utilizing 11w U 00w 
    cannot multiply the graph's independence number faster than the VT algorithm allows.
    This effectively caps the fundamental growth rate of the independent set. -/
theorem growth_rate_capped_by_VT (n : Nat) (I : IndepSet n) (I_max : is_MaximalIndepSet I) (H_VT_opt : is_optimal_VT (n + 2)) :
  Finset.card (lift_00 I.val ∪ lift_11 I.val) ≤ Finset.card (Finset.VTCode (n + 2) 0) := by {
  have H_union_DelCode : is_DelCode (lift_00 I.val ∪ lift_11 I.val) := is_DelCode_union_lifts I.property
  unfold is_optimal_VT at H_VT_opt
  unfold is_optimal at H_VT_opt
  exact H_VT_opt _ H_union_DelCode
}
