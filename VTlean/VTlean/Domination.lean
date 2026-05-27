import VTlean.B
import VTlean.VTCode
import VTlean.Dream
import VTlean.CuculiereCombinatorial
import Mathlib

open Finset List.Vector

namespace VTlean.Domination

variable {n : Nat}

/-- The exact maximum number of unique length n-1 strings that can be generated 
  by all length n strings having exactly r runs. -/
def total_descendants_with_runs (n r : Nat) : Nat :=
  sorry

/-- 
  Any generic code C that is single-deletion correcting 
  (meaning PairwiseDisjoint dS) cannot pack more words of a given run-length 
  than the absolute volume constraint allows.
  Since every word x with r runs contributes exactly r unique length n-1 strings,
  the total contribution is r * num_words_with_runs, which cannot exceed the max.
-/
lemma run_distribution_bound (C : Finset (List.Vector B n)) (hC : is_OptimalCodeCandidate C) (r : Nat) :
  num_words_with_runs C r * r ≤ total_descendants_with_runs n r := by
  sorry

/-- The number of strings in VT_a with exactly r runs.
  Because a string with r runs has r-1 transitions, and the sum of transition indices 
  must equal a mod n+1, this is exactly 2 * S(n, r-1, a). -/
def vt_optimal_distribution (n a r : Nat) : Nat :=
  2 * S n (r - 1) a

/-- 
  VT_0 achieves the theoretical maximum possible density of low-run words 
  due to its modulo arithmetic offset structure. 
-/
lemma vt_run_optimality (r : Nat) :
  num_words_with_runs (Finset.VTCode n 0) r = vt_optimal_distribution n 0 r := by
  sorry

/-- 
  Combining the bounds, VT_0 dominates any arbitrary optimal code candidate C 
  in its packing of low-run words (which have smaller deletion spheres).
-/
theorem run_length_domination_proof (C : Finset (List.Vector B n)) (hC : is_OptimalCodeCandidate C) (r : Nat) :
  ∑ i ∈ Finset.Icc 1 r, num_words_with_runs C i ≤ ∑ i ∈ Finset.Icc 1 r, num_words_with_runs (Finset.VTCode n 0) i := by
  -- Step 1: For each i ≤ r, bound the contribution of C using run_distribution_bound
  -- num_words_with_runs C i ≤ total_descendants_with_runs n i / i
  
  -- Step 2: Use vt_run_optimality to show that VT_0 hits the exact maximum bound
  -- num_words_with_runs (VTCode n 0) i = vt_optimal_distribution n 0 i
  
  -- Step 3: Conclude by summing the bounds over the interval [1, r]
  sorry

end VTlean.Domination
