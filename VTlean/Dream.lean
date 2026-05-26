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

/-- Conjecture 1: The VT codes perfectly partition the hypergraph vertices.
Every string of length n-1 is the deletion of exactly one word in VT_a.
Thus, VT_a forms a *perfect hypergraph matching* covering all 2^{n-1} vertices. -/
theorem vt_perfect_partition (a : Nat) :
  (Finset.VTCode n a).biUnion dS = (Finset.univ : Finset (List.Vector B (n - 1))) := by
  sorry

/-- Conjecture 2: The Canonical Volume Constraint.
Because the hyperedges are disjoint, the sum of their sizes (the number of runs r(x))
is strictly bounded by the total number of vertices in the hypergraph. -/
theorem volume_constraint (C : Finset (List.Vector B n)) (hC : is_OptimalCodeCandidate C) :
  ∑ x ∈ C, (dS x).card ≤ 2^(n - 1) := by
  sorry

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
