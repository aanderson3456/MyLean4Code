import Mathlib
import VTlean.VTCode
import VTlean.CuculiereCombinatorial
import VTlean.DelCode

open Nat Finset List.Vector

/-!
# Mixed Checksum Homogenization

This file formalizes the theoretical homogenization of a mixed-checksum
deletion correcting code into a pure checksum code (like VT_0).
-/

variable {n : Nat}

/-- Partition a generic code C into a specific weight k and moment a modulo (n + 1). -/
def code_partition (C : Finset (List.Vector B n)) (k a : Nat) : Finset (List.Vector B n) :=
  C.filter (fun x => wt x = k ∧ moment x % (n + 1) = a % (n + 1))

/-- Decomposes any code C into a union of its disjoint moment and weight bins. -/
lemma bUnion_code_partition (C : Finset (List.Vector B n)) :
  C = Finset.biUnion (Finset.Iic n) (fun k => Finset.biUnion (Finset.Iic n) (fun a => code_partition C k a)) := by {
  ext x
  simp only [mem_biUnion, mem_Iic, code_partition, mem_filter]
  constructor
  · intro hx
    use wt x
    refine ⟨Vector.wt_le_length x, ?_⟩
    use (moment x % (n + 1))
    refine ⟨by omega, ⟨hx, rfl, rfl⟩⟩
  · rintro ⟨k, _, a, _, hx, _, _⟩
    exact hx
}

/-- The total cardinality of a code C is the sum of the cardinalities of its weight and moment bins. -/
lemma card_code_partition (C : Finset (List.Vector B n)) :
  C.card = ∑ k ∈ Finset.Iic n, ∑ a ∈ Finset.Iic n, (code_partition C k a).card := by {
  have h_bUnion := bUnion_code_partition C
  nth_rw 1 [h_bUnion]
  have h_disj_k : Set.PairwiseDisjoint (↑(Finset.Iic n)) (fun k => Finset.biUnion (Finset.Iic n) (fun a => code_partition C k a)) := by {
    intro k1 _ k2 _ h_neq
    simp only [Function.onFun, disjoint_left, mem_biUnion, mem_Iic, code_partition, mem_filter]
    intro x ⟨a1, _, _, h_wt1, _⟩ ⟨a2, _, _, h_wt2, _⟩
    rw [h_wt1] at h_wt2
    exact h_neq h_wt2
  }
  rw [Finset.card_biUnion h_disj_k]
  apply Finset.sum_congr rfl
  intro k _
  have h_disj_a : Set.PairwiseDisjoint (↑(Finset.Iic n)) (fun a => code_partition C k a) := by {
    intro a1 _ a2 _ h_neq
    simp only [Function.onFun, disjoint_left, code_partition, mem_filter]
    intro x ⟨_, _, h_mom1⟩ ⟨_, _, h_mom2⟩
    have h_eq : a1 % (n + 1) = a2 % (n + 1) := by
      rw [← h_mom1, h_mom2]
    -- Since a1, a2 <= n, their mod (n+1) is themselves
    have h_mod1 : a1 % (n + 1) = a1 := Nat.mod_eq_of_lt (by omega)
    have h_mod2 : a2 % (n + 1) = a2 := Nat.mod_eq_of_lt (by omega)
    rw [h_mod1, h_mod2] at h_eq
    exact h_neq h_eq
  }
  rw [Finset.card_biUnion h_disj_a]
}

/-- A VT code with checksum `a` will naturally have an empty partition for any non-matching checksum `b`. -/
lemma code_partition_VTCode_eq_empty (a b k : Nat) (h_neq : a % (n + 1) ≠ b % (n + 1)) :
  code_partition (Finset.VTCode n a) k b = ∅ := by {
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro x hx
  simp only [code_partition, mem_filter, Finset.mem_VTCode, _root_.mem_VTCode] at hx
  have h_mom1 : moment x % (n + 1) = a % (n + 1) := hx.1.1
  have h_mom2 : moment x % (n + 1) = b % (n + 1) := hx.2.2
  rw [h_mom1] at h_mom2
  exact h_neq h_mom2
}

/-- The size of the VT code partition strictly matches Cuculiere's mathematical subset sum definition T(n, k, a). -/
lemma card_code_partition_VTCode (a k : Nat) :
  (code_partition (Finset.VTCode n a) k a).card = T n k a := by {
  have h_T := vt_wt_eq_T n a k
  have h_eq : code_partition (Finset.VTCode n a) k a = Finset.filter (fun X => wt X = k) (Finset.VTCode n a) := by {
    ext x
    simp only [code_partition, mem_filter, Finset.mem_VTCode, _root_.mem_VTCode]
    constructor
    · rintro ⟨⟨h_mom, h_len⟩, h_wt, _⟩
      exact ⟨⟨h_mom, h_len⟩, h_wt⟩
    · rintro ⟨⟨h_mom, h_len⟩, h_wt⟩
      exact ⟨⟨h_mom, h_len⟩, h_wt, h_mom⟩
  }
  rw [h_eq]
  exact h_T
}

/-- Conjecture: Mixed Checksum Le Pure.
Any single-deletion correcting code (which may have mixed checksums) has cardinality 
less than or equal to VT_0.

NOTE ON ALGEBRAIC HOMOGENIZATION:
The user requested exploring whether the algebraic cyclic shift could be saved by Hamming distance 
collision avoidance. However, this is mathematically FALSE because words of different weights must 
be shifted by DIFFERENT amounts to reach checksum 0. 

Here is a rigorous counter-example for n = 4:
We want to homogenize C_1 (checksum 1 mod 5) into VT_0.
- For weight 2 (k=2), we need 1 + 2d_2 = 0 mod 5 => d_2 = 2.
- For weight 3 (k=3), we need 1 + 3d_3 = 0 mod 5 => d_3 = 3.

Consider two binary strings in C_1:
1. `x = 0101` (Weight 2, Checksum 2+4 = 6 = 1 mod 5). Subset: {2, 4}.
2. `y = 1110` (Weight 3, Checksum 1+2+3 = 6 = 1 mod 5). Subset: {1, 2, 3}.

Check disjointness of deletion spheres:
dS(0101) = {101, 001, 011, 010}
dS(1110) = {110, 111}
Intersection is empty! So a valid optimal code CAN contain both `0101` and `1110`.

Now apply the shifts:
- Shift `x` by d_2 = 2: {2+2, 4+2} = {4, 6} = {4, 1}. No zero dropped. Result: {1, 4}.
- Shift `y` by d_3 = 3: {1+3, 2+3, 3+3} = {4, 5, 6} = {4, 0, 1}. Drop 0. Result: {1, 4}.

BOTH valid code words perfectly map to {1, 4} (which is `1001` in VT_0).
This creates an unavoidable non-injective collision for this specific cyclic shift bijection. 

FUTURE SEED OF POSSIBILITY:
The failure of the naive cyclic shift arises because the single-deletion hypergraph is fundamentally 
linear (deleting a bit shifts subsequent indices left), whereas the subset map is purely cyclic. 
To salvage the Mixed Checksum prospect, one must abandon 1-to-1 deterministic algebraic shifts 
and instead use:
1. Fractional Matchings / Network Flows: Construct a bipartite graph between C and VT_0 where 
   edges represent "valid" structural transformations. If we can prove that the average degree 
   from C to VT_0 is strictly greater than or equal to the reverse, |C| <= |VT_0| follows via 
   Hall's Marriage Theorem generalizations.
2. Difference Equations: Instead of mapping words, use Cuculiere's S(n,k,a) recursive telescoping 
   identities to bound the sum \sum |C_{k,a}| globally, without mapping individual words.
-/
theorem mixed_checksum_le_pure (C : Finset (List.Vector B n)) (hC : is_DelCode C) :
  C.card ≤ (Finset.VTCode n 0).card := by {
  sorry
}
