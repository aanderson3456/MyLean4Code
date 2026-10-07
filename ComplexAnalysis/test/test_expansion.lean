import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open Complex

noncomputable def smoothNumbersBoundedFinset (N K : ℕ) : Finset ℕ :=
  have : DecidablePred (fun n => n > 0 ∧ ∀ p, p.Prime → p ∣ n → p ≤ N ∧ n.factorization p ≤ K) := Classical.decPred _
  (Finset.range ((N.factorial ^ K) + 1)).filter (fun n => n > 0 ∧ ∀ p, p.Prime → p ∣ n → p ≤ N ∧ n.factorization p ≤ K)

lemma euler_product_expand_sum (N K : ℕ) (s : ℂ) :
    ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (∑ k ∈ Finset.range (K + 1), ((p : ℂ) ^ (-s)) ^ k) =
    ∑ n ∈ smoothNumbersBoundedFinset N K, (n : ℂ) ^ (-s) := by
{
  sorry
}
