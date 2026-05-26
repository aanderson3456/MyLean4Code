import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import VTlean.B
import VTlean.InsDel
import VTlean.DelCode
import VTlean.VTCode
import VTlean.FractalSlice

open B List.Vector Finset

/-!
# Dream.lean: The Absolute Optimality of VT Codes

This file contains formalized conjecture statements toward proving the absolute 
optimality of the Varshamov-Tenengolts (VT) codes for single-deletion correction.

## The Sloane Hypergraph
The "Sloane Hypergraph" models the deletion channel.
- The **vertices** are all binary strings of length n-1.
- The **hyperedges** are the deletion spheres `dS x` for each string `x` of length n.
- A **single-deletion correcting code** is a set of mutually disjoint hyperedges (a matching).

The ultimate dream is to prove that VT_0 forms the maximum possible matching.
-/

variable {n : Nat}

/-- A single-deletion correcting code is a set of words whose deletion spheres are disjoint. -/
def is_OptimalCodeCandidate (C : Finset (List.Vector B n)) : Prop :=
  ∀ x ∈ C, ∀ y ∈ C, x ≠ y → Disjoint (dS x) (dS y)

lemma mod_helper {A m : Nat} (hm : 0 < m) : (A + m - A % m) % m = 0 := by
  have h_div : A = m * (A / m) + A % m := (Nat.div_add_mod A m).symm
  nth_rewrite 1 [h_div]
  have h_rw : m * (A / m) + A % m + m - A % m = m * (A / m) + m := by omega
  rw [h_rw]
  have h_mul : m * (A / m) + m = m * (A / m + 1) := by ring
  rw [h_mul]
  exact Nat.mul_mod_right m _

lemma sub_mod_add_moment_helper {A a m : Nat} (hm : 0 < m) :
  (A + (a + (m - A % m) % m)) % m = a % m := by
  have h1 : (a + (m - A % m) % m) % m = (a + (m - A % m)) % m := by
    rw [Nat.add_mod, Nat.mod_mod, ←Nat.add_mod]
  have h2 : (A + (a + (m - A % m) % m)) % m = (A + (a + (m - A % m))) % m := by
    rw [Nat.add_mod, h1, ←Nat.add_mod]
  rw [h2]
  have h_lt : A % m < m := Nat.mod_lt A hm
  have h3 : A + (a + (m - A % m)) = a + (A + m - A % m) := by omega
  rw [h3, Nat.add_mod, mod_helper hm, Nat.add_zero, Nat.mod_mod]

lemma sub_mod_add_moment_eq_a_mod (m a : Nat) (hm : 0 < m) (X : List B) :
  (List.moment X + List.sub_mod m a X) % m = a % m := by
  unfold List.sub_mod
  cases Decidable.em (List.moment X < a) with
  | inl hlt =>
    rw [if_pos hlt]
    rw [Nat.add_mod_mod]
    rw [Nat.add_sub_of_le (Nat.le_of_lt hlt)]
  | inr hnlt =>
    rw [if_neg hnlt]
    have h_sub : List.moment X = List.moment X - a + a := by
      exact (Nat.sub_add_cancel (Nat.ge_of_not_lt hnlt)).symm
    nth_rewrite 1 [h_sub]
    rw [Nat.add_assoc]
    exact sub_mod_add_moment_helper hm

lemma sub_mod_lt (m a : Nat) (X : List B) (hm : 0 < m) : List.sub_mod m a X < m := by
  unfold List.sub_mod
  cases Decidable.em (List.moment X < a) with
  | inl hlt =>
    rw [if_pos hlt]
    exact Nat.mod_lt _ hm
  | inr hnlt =>
    rw [if_neg hnlt]
    exact Nat.mod_lt _ hm

lemma max_num_RIs_le_length (X : List B) (i : Nat) : List.max_num_RIs X i ≤ List.length X := by
  induction X generalizing i with
  | nil =>
    unfold List.max_num_RIs
    exact Nat.le_refl _
  | cons x xs ih =>
    unfold List.max_num_RIs
    have h_len : List.length (x :: xs) = List.length xs + 1 := rfl
    cases x
    · split
      · have h := ih i; omega
      · have h := ih i; omega
    · split
      · have h := ih i; omega
      · have h := ih i; omega

lemma min_num_LOs_le_length (X : List B) (i : Nat) : List.min_num_LOs X i ≤ List.length X := by
  induction X generalizing i with
  | nil =>
    unfold List.min_num_LOs
    exact Nat.zero_le _
  | cons x xs ih =>
    have h_len : List.length (x :: xs) = List.length xs + 1 := rfl
    cases x
    · cases i with
      | zero => exact Nat.zero_le _
      | succ n =>
        unfold List.min_num_LOs
        have h := ih n
        omega
    · cases i with
      | zero => exact Nat.zero_le _
      | succ n =>
        unfold List.min_num_LOs
        have h := ih (n + 1)
        omega

lemma decoding_alg_is_insertion (n a : Nat) (y : List.Vector B (n - 1)) (hn : 0 < n) :
  y ∈ dS (decoding_alg n a y) := by
  unfold decoding_alg
  rw [mem_dS]
  cases Decidable.em (List.length y.val = n) with
  | inl hlen =>
    have h_len : List.length y.val = n - 1 := y.property
    omega
  | inr hnlen =>
    cases Decidable.em (List.sub_mod (n + 1) a y.val ≤ List.num_Is y.val) with
    | inl hle =>
      use List.max_num_RIs y.val (List.sub_mod (n + 1) a y.val)
      constructor
      · have h_bound := max_num_RIs_le_length y.val (List.sub_mod (n + 1) a y.val)
        have h_len : List.length y.val = n - 1 := y.property
        omega
      · apply Subtype.ext
        change y.val = List.sDel (List.decoding_alg n a y.val) _
        unfold List.decoding_alg
        rw [if_neg hnlen, if_pos hle]
        exact (List.sDel_sIns_id _ _ _).symm
    | inr hnle =>
      use List.min_num_LOs y.val (List.sub_mod (n + 1) a y.val - List.num_Is y.val - 1)
      constructor
      · have h_bound := min_num_LOs_le_length y.val (List.sub_mod (n + 1) a y.val - List.num_Is y.val - 1)
        have h_len : List.length y.val = n - 1 := y.property
        omega
      · apply Subtype.ext
        change y.val = List.sDel (List.decoding_alg n a y.val) _
        unfold List.decoding_alg
        rw [if_neg hnlen, if_neg hnle]
        exact (List.sDel_sIns_id _ _ _).symm

lemma moment_decoding_alg (n a : Nat) (y : List.Vector B (n - 1)) (hn : 0 < n) :
  moment (decoding_alg n a y) % (n + 1) = a % (n + 1) := by
  unfold decoding_alg moment
  change List.moment (List.decoding_alg n a y.val) % (n + 1) = a % (n + 1)
  unfold List.decoding_alg
  cases Decidable.em (List.length y.val = n) with
  | inl hlen =>
    have h_len : List.length y.val = n - 1 := y.property
    omega
  | inr hnlen =>
    rw [if_neg hnlen]
    cases Decidable.em (List.sub_mod (n + 1) a y.val ≤ List.num_Is y.val) with
    | inl hle =>
      rw [if_pos hle]
      rw [List.moment_sIns_zero]
      rw [List.num_RIs_max_num_RIs y.val _ hle]
      apply sub_mod_add_moment_eq_a_mod (n + 1) a (by omega)
    | inr hnle =>
      rw [if_neg hnle]
      rw [List.moment_sIns_one]
      have h_bound : List.sub_mod (n + 1) a y.val - List.num_Is y.val - 1 ≤ List.num_Os y.val := by
        have h_sub_mod := sub_mod_lt (n + 1) a y.val (by omega)
        have h_num_Os : List.num_Os y.val = n - 1 - List.num_Is y.val := by
          have h1 : List.num_Os y.val + List.num_Is y.val = List.length y.val := List.num_Os_add_num_Is y.val
          have h2 : List.length y.val = n - 1 := y.property
          omega
        omega
      rw [List.num_LOs_min_num_LOs y.val _ h_bound]
      have h_eq : List.moment y.val + (List.sub_mod (n + 1) a y.val - List.num_Is y.val - 1) + List.num_Is y.val + 1 = List.moment y.val + List.sub_mod (n + 1) a y.val := by
        have h_gt : List.num_Is y.val < List.sub_mod (n + 1) a y.val := Nat.lt_of_not_ge hnle
        omega
      rw [h_eq]
      apply sub_mod_add_moment_eq_a_mod (n + 1) a (by omega)

/-- Conjecture 1: The VT codes perfectly partition the hypergraph vertices.
Every string of length n-1 is the deletion of exactly one word in VT_a.
Thus, VT_a forms a *perfect hypergraph matching* covering all 2^{n-1} vertices. -/
theorem vt_perfect_partition (a : Nat) (hn : 0 < n) :
  (Finset.VTCode n a).biUnion dS = (Finset.univ : Finset (List.Vector B (n - 1))) := by
  apply Finset.Subset.antisymm
  · exact Finset.subset_univ _
  · intro y _
    rw [Finset.mem_biUnion]
    use decoding_alg n a y
    constructor
    · rw [Finset.mem_VTCode]
      exact moment_decoding_alg n a y hn
    · exact decoding_alg_is_insertion n a y hn

lemma card_vector_B_eq (m : Nat) : Fintype.card (List.Vector B m) = 2^m := by
  sorry

/-- Conjecture 2: The Canonical Volume Constraint.
Because the hyperedges are disjoint, the sum of their sizes (the number of runs r(x))
is strictly bounded by the total number of vertices in the hypergraph. -/
theorem volume_constraint (C : Finset (List.Vector B n)) (hC : is_OptimalCodeCandidate C) :
  ∑ x ∈ C, (dS x).card ≤ 2^(n - 1) := by
  have h_disj : (C : Set (List.Vector B n)).PairwiseDisjoint dS := by
    intro x hx y hy hne
    exact hC x hx y hy hne
  have h_sum := Finset.card_biUnion h_disj
  rw [← h_sum]
  have h_sub : C.biUnion dS ⊆ (Finset.univ : Finset (List.Vector B (n - 1))) := Finset.subset_univ _
  have h_le := Finset.card_le_card h_sub
  have h_card := card_vector_B_eq (n - 1)
  have h_univ_card : (Finset.univ : Finset (List.Vector B (n - 1))).card = Fintype.card (List.Vector B (n - 1)) := Finset.card_univ
  rw [h_univ_card, h_card] at h_le
  exact h_le

/-- Conjecture 3: Run-Length Lexicographic Domination.
To maximize the number of words |C| within the volume constraint, a code must pack 
hyperedges of small size (words with few runs). We conjecture that VT_0 packs the 
absolute topological maximum number of small-run words possible. -/
def num_words_with_runs (C : Finset (List.Vector B n)) (r : Nat) : Nat :=
  (C.filter (fun x => (dS x).card = r)).card

theorem run_length_domination (C : Finset (List.Vector B n)) (hC : is_OptimalCodeCandidate C) (r : Nat) :
  ∑ i ∈ Finset.Icc 1 r, num_words_with_runs C i ≤ ∑ i ∈ Finset.Icc 1 r, num_words_with_runs (Finset.VTCode n 0) i := by
  sorry

/-- Conjecture 4: THE BIG DREAM - Absolute Optimality.
No single-deletion correcting code can have a strictly larger size than VT_0. -/
theorem absolute_optimality (C : Finset (List.Vector B n)) (hC : is_OptimalCodeCandidate C) :
  C.card ≤ (Finset.VTCode n 0).card := by
  sorry
