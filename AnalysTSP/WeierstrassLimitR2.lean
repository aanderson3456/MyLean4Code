import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic -- For abs
import Mathlib.Data.Real.Sqrt -- For Real.sqrt
import Mathlib.Tactic.Linarith -- Useful for proving inequalities
import Mathlib.Data.Set.Basic

variable (x y: (ℝ × ℝ))

#check (x-y)
#check (x-y).1
example : (x-y).1 = x.1 - y.1 := by {
  rfl
}


-- Let's work in a new namespace to avoid conflicts
namespace ManualEuclideanR2

noncomputable def sqNorm (x : ℝ × ℝ) : ℝ := x.1^2 + x.2^2

noncomputable def sqDist (x y : ℝ × ℝ) : ℝ :=
  (x.1 - y.1)^2 + (x.2 - y.2)^2

example : sqDist x y = sqNorm (x-y) := by {
  rfl
}
noncomputable def euclideanNorm (x : ℝ × ℝ) : ℝ :=
  Real.sqrt (sqNorm x)

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

(0 ≤ )

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

def IsOpenR2 (S : Set (ℝ × ℝ)) : Prop :=
  ∀ s ∈ S, ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ × ℝ, euclideanDist s x < δ → x ∈ S

def IsClosedR2 (S : Set (ℝ × ℝ)) : Prop :=
  IsOpenR2 Sᶜ

lemma checkUniv (S : Set (ℝ × ℝ)) : S = Set.univ → IsOpenR2 S := by {
  intro h_S_eq_univ
  unfold IsOpenR2
  -- Substitute S with Set.univ in the goal IsOpenR2 S
  rw [h_S_eq_univ]
  -- Take an arbitrary point s. The condition s ∈ Set.univ is always true for s : ℝ × ℝ
  intro s _hs -- We use _hs as the fact s ∈ Set.univ is trivial and not needed further
  -- We need to provide a δ > 0. Let's choose δ = 1.
  use 1
  -- We now have two goals from the conjunction: 1 > 0 and ∀ x, dist s x < 1 → x ∈ Set.univ
  constructor
  · -- Goal 1: Prove 1 > 0
    exact zero_lt_one -- This is a standard lemma in Mathlib
  · -- Goal 2: Prove ∀ x, dist s x < 1 → x ∈ Set.univ
    -- Take an arbitrary x and assume dist s x < 1
    intro x _hx -- We use _hx as the distance condition is irrelevant
    -- The goal is to prove x ∈ Set.univ
    -- Any element x of type ℝ × ℝ is automatically in Set.univ by definition.
    exact Set.mem_univ x

}

def IsBoundedR2 (s : Set (ℝ × ℝ)) : Prop :=
  ∃ C : ℝ, ∀ x ∈ s, euclideanNorm x ≤ C

def IsCompactR2 (K : Set (ℝ × ℝ)) : Prop :=
  ∀ (ι : Type) (U : ι → Set (ℝ × ℝ)), -- For every index type ι and indexed family of sets U...
    (∀ i : ι, IsOpenR2 (U i)) →        -- ...such that every set U i is open...
    (K ⊆ (⋃ i : ι, U i)) →            -- ...and the family covers K...(note purple parens unnecessary)
    ∃ (s : Finset ι),                 -- ...there exists a finite set of indices s...
      K ⊆ (⋃ i ∈ s, U i)               -- ...such that the corresponding finite subfamily covers K.

#check Metric.ball

end ManualEuclideanR2

-- Check the definition using our manual distance
#check ManualEuclideanR2.Limit
