import VTlean.B
import VTlean.InsDel
import VTlean.DelCode
import VTlean.VTCode
import VTlean.FractalSlice
import VTlean.Networkx

open B List.Vector Finset

variable {n : Nat}

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

/-!
### The Progressive Deletion Potential double-induction schema:
For any rational potential function `u : Vector B (n-1) → Rat` and any `x : Vector B n`,
the progressive potential sum is defined over the prefix length `k` from `0` to `n`:
`P(x, k) = \sum_{y ∈ cumulativeDels x k} u y`

Our empirical constraint-solver simulations show:
1. `Δ P(x, k) = P(x, k) - P(x, k-1) = 0` whenever index `k-1` is inside a run (i.e. `x[k-1] == x[k-2]`).
   This is mathematically guaranteed because deleting a bit inside a run produces a string identical
   to deleting the run's start, meaning no new strings are added to the prefix deletion set.
2. `Δ P(x, k)` is non-zero only at run starts (`k=1` or `x[k-1] != x[k-2]`).
3. Under optimal dual potential weights, the sum of increments over run boundaries evaluates to
   exactly the LP dual bound.

We can proceed by double induction:
- Outer induction: string length `n`.
- Inner induction: prefix index `k` tracking run transitions.
-/
