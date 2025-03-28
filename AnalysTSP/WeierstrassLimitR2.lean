import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic -- For abs
import Mathlib.Data.Real.Sqrt -- For Real.sqrt
import Mathlib.Tactic.Linarith -- Useful for proving inequalities

-- Let's work in a new namespace to avoid conflicts
namespace ManualEuclideanR2

-- Define the squared Euclidean distance first (often simpler)
noncomputable def sqDist (x y : ℝ × ℝ) : ℝ :=
  (x.1 - y.1)^2 + (x.2 - y.2)^2

-- Define the Euclidean distance using square root
noncomputable def euclideanDist (x y : ℝ × ℝ) : ℝ :=
  Real.sqrt (sqDist x y)

-- We need to prove basic properties if we want to use metric space tactics,
-- but for just *writing* the definition, we just need the function itself.
-- Let's prove non-negativity as an example.
lemma sqDist_nonneg (x y : ℝ × ℝ) : 0 ≤ sqDist x y := by {
  apply add_nonneg -- Need 0 ≤ (x.1 - y.1)² and 0 ≤ (x.2 - y.2)²
  exact sq_nonneg (x.1 - y.1)
  exact sq_nonneg (x.2 - y.2)
}

lemma euclideanDist_nonneg (x y : ℝ × ℝ) : 0 ≤ euclideanDist x y := by {
  exact Real.sqrt_nonneg (sqDist x y)
}

-- Other axioms (dist_self, eq_of_dist_eq_zero, dist_comm, dist_triangle)
-- would be needed to formally declare a MetricSpace instance, but we
-- can write the limit definition using `euclideanDist` directly.

/-
Our Epsilon-Delta definition, but using our manually defined Euclidean distance
-/
def Limit (f : ℝ × ℝ → ℝ) (a : ℝ × ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ × ℝ,
    0 < euclideanDist x a ∧ euclideanDist x a < δ → abs (f x - L) < ε

/-!
### Example Check
-/
section examples

def proj₁ (p : ℝ × ℝ) : ℝ := p.1
def pt_a : ℝ × ℝ := (2, 3)
def limit_val : ℝ := 2

-- The statement still looks the same, but `Limit` now refers to
-- ManualEuclideanR2.Limit which uses `euclideanDist`.
def example_limit_statement : Prop := Limit proj₁ pt_a limit_val

lemma sq_order_preserve (a b : ℝ) : (0 ≤ a)∧(0 ≤ b)∧(a^2 ≤ b^2) → (a ≤ b) := by {
  intro h
  rcases h with ⟨ha, hb, hab⟩
  have h2 : 2 ≠ 0 := by
    exact Ne.symm (Nat.zero_ne_add_one 1)
  apply (pow_le_pow_iff_left ha hb h2).mp
  exact hab
}

-- To prove this, we would need lemmas relating `euclideanDist`
-- to component differences, e.g., |x.1 - a.1| ≤ euclideanDist x a
lemma abs_fst_sub_fst_le_euclideanDist (x a : ℝ × ℝ) : abs (x.1 - a.1) ≤ euclideanDist x a := by {
  rw [euclideanDist]
  have h1 : 0 ≤ abs (x.1 - a.1) := by
    exact abs_nonneg (x.1 - a.1) -- Need to show (abs (...))^2 <= sqDist x a
  have h2 : 0 ≤ √(sqDist x a) := by
    exact Real.sqrt_nonneg (sqDist x a)
  apply sq_order_preserve
  constructor
  exact h1
  constructor
  exact h2
  simp
  rw [Real.sq_sqrt]
  unfold sqDist
  apply le_add_of_le_of_nonneg
  simp
  exact sq_nonneg (x.2 - a.2)
  exact sqDist_nonneg x a
}

-- Now we can prove the example using this lemma
example : Limit proj₁ pt_a limit_val := by {
  intro ε hε
  use ε -- Choose δ = ε
  constructor
  exact hε
  intro x h_dist_conj
  calc abs (x.1 - pt_a.1)
      ≤ euclideanDist x pt_a := by apply abs_fst_sub_fst_le_euclideanDist
    _ < ε := h_dist_conj.right
}

end examples

end ManualEuclideanR2


-- Check the definition using our manual distance
#check ManualEuclideanR2.Limit
