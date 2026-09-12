import Mathlib.Data.Real.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option linter.style.header false

open Finset
open scoped BigOperators

namespace ProbStats

/-- A finite probability distribution over a sample space of size N. -/
structure FiniteDist (N : ℕ) where
  pmf : Fin N → ℝ
  nonneg : ∀ x, 0 ≤ pmf x
  sums_to_one : ∑ x : Fin N, pmf x = 1

/-- Expected value of a random variable X under distribution P. -/
def expectedValue {N : ℕ} (P : FiniteDist N) (X : Fin N → ℝ) : ℝ :=
  ∑ x : Fin N, P.pmf x * X x

/-- Variance of a random variable X under distribution P. -/
def variance {N : ℕ} (P : FiniteDist N) (X : Fin N → ℝ) : ℝ :=
  let mu := expectedValue P X
  ∑ x : Fin N, P.pmf x * (X x - mu)^2

/-- 
  Standard deviation shrinkage proxy. 
  Scaling the deviation by a factor `c ≤ 1` strictly bounds the new variance.
-/
theorem variance_shrinkage {N : ℕ} (P : FiniteDist N) (X : Fin N → ℝ) {c : ℝ} (hc1 : 0 ≤ c) (hc2 : c ≤ 1) :
  let mu := expectedValue P X;
  let shrunk_var := ∑ x : Fin N, P.pmf x * (c * (X x - mu))^2;
  shrunk_var ≤ variance P X := by {
    intro mu shrunk_var
    have h_le : ∀ x ∈ (univ : Finset (Fin N)), P.pmf x * (c * (X x - mu))^2 ≤ P.pmf x * (X x - mu)^2 := by {
      intro x _hx
      have h_nonneg : 0 ≤ P.pmf x := P.nonneg x
      have h_sq : 0 ≤ (X x - mu)^2 := sq_nonneg (X x - mu)
      have hc2_sq : c ^ 2 ≤ 1 := by nlinarith
      calc
        P.pmf x * (c * (X x - mu))^2 = P.pmf x * (c^2 * (X x - mu)^2) := by ring
        _ ≤ P.pmf x * (1 * (X x - mu)^2) := by {
          apply mul_le_mul_of_nonneg_left
          apply mul_le_mul_of_nonneg_right hc2_sq h_sq
          exact h_nonneg
        }
        _ = P.pmf x * (X x - mu)^2 := by ring
    }
    apply sum_le_sum h_le
}

end ProbStats
