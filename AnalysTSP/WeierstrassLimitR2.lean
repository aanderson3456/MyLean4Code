--import Mathlib.Data.Real.Basic
import Mathlib.Analysis.Normed.Group.Basic -- For abs
import Mathlib.Data.Real.Sqrt -- For Real.sqrt
import Mathlib.Tactic.Linarith -- Useful for proving inequalities
import Mathlib.Data.Set.Basic
import Mathlib.Logic.Function.Defs


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
def LimitR2toR (f : ℝ × ℝ → ℝ) (a : ℝ × ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ × ℝ,
    0 < euclideanDist x a ∧ euclideanDist x a < δ → abs (f x - L) < ε

def LimitR2toR2 (f : ℝ × ℝ → ℝ × ℝ) (a : ℝ × ℝ) (L : ℝ × ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ × ℝ,
    0 < euclideanDist x a ∧ euclideanDist x a < δ → euclideanDist (f x) L < ε

def LimitRtoR2 (f : ℝ → ℝ × ℝ) (a : ℝ) (L : ℝ × ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ,
    0 < abs (x - a) ∧ abs (x - a) < δ → euclideanDist (f x) L < ε

def ConvergesR2 (seq : ℕ → ℝ × ℝ) (L : ℝ × ℝ): Prop :=
  ∀ ε > 0, ∃ N : ℕ,
    ∀ n ≥ N, euclideanDist L (seq n) < ε
/-!
### Example Check
-/
section examples

def proj₁ (p : ℝ × ℝ) : ℝ := p.1
def pt_a : ℝ × ℝ := (2, 3)
def limit_val : ℝ := 2

-- The statement still looks the same, but `Limit` now refers to
-- ManualEuclideanR2.Limit which uses `euclideanDist`.
def example_limit_statement : Prop := LimitR2toR proj₁ pt_a limit_val

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
example : LimitR2toR proj₁ pt_a limit_val := by {
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

def IsOpenR (S : Set ℝ) : Prop :=
  ∀ s ∈ S, ∃ ε : ℝ, ε > 0 ∧ ∀ x : ℝ, abs (s - x) < ε → x ∈ S

def IsOpenR2 (S : Set (ℝ × ℝ)) : Prop :=
  ∀ s ∈ S, ∃ ε : ℝ, ε > 0 ∧ ∀ x : ℝ × ℝ, euclideanDist s x < ε → x ∈ S

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

def IsOpenCoverR2 (ι : Type) (U : ι → Set (ℝ × ℝ)) (K : Set (ℝ × ℝ)) : Prop :=
    (∀ i : ι, IsOpenR2 (U i)) ∧ (K ⊆ (⋃ i : ι, U i))

def IsCompactR2Subcover (K : Set (ℝ × ℝ)) : Prop :=
  ∀ (ι : Type) (U : ι → Set (ℝ × ℝ)),
    IsOpenCoverR2 ι U K →
    ∃ (s : Finset ι), K ⊆ (⋃ i ∈ s, U i)

def IsCptR2SubcoverCompl (K : Set (ℝ × ℝ)) : Prop :=
  ∀ (ι : Type) (F : ι → Set (ℝ × ℝ)),
    (∀ i : ι, IsClosedR2 (F i)) →
    ∅ = (⋂ i : ι, (F i ∩ K)) →  --careful with bigcap vs cap
    ∃ (s : Finset ι),
      ∅ = (⋂ i : s, (F i ∩ K))

variable {ι : Type*}
variable [Nonempty ι]

lemma SetEmptyComplInter (A B : Set (ℝ × ℝ)) : ∅ = (Aᶜ ∩ B) → B ⊆ A := by {
  intro hEmpty
  have hElements : ∀ (x : ℝ × ℝ), x ∉ (Aᶜ ∩ B) := by {
    exact fun x => of_eq_false (congrFun (id (Eq.symm hEmpty)) x)
    --Lean is automatically applying an empty set definition here
  }
  have hElemToContain : (∀ (x : ℝ × ℝ), x ∈ B → x ∈ A) → B ⊆ A := by {
    exact fun a => a
  }
  apply hElemToContain
  intro xb
  intro hxb
  have hxbNotinAcomplOrB : (xb ∉ Aᶜ) ∨ (xb ∉ B) := by {
    exact Classical.not_and_iff_or_not_not.mp (hElements xb)
  }
  cases' hxbNotinAcomplOrB with hxbNotinAcompl hxbNotinB
  exact Set.not_mem_compl_iff.mp hxbNotinAcompl
  exact False.elim (hxbNotinB hxb)
}

lemma ExistsIntroBcNonempty : ∃ i : ι, True := by {
  rename_i nonTrivialIndex
  exact (exists_const ι).mpr trivial
}

lemma SetNegLeftProj (A B : Set (ℝ × ℝ)) : ∀ (x : (ℝ × ℝ)), x ∉ A → x ∉ (A ∩ B) := by {
  intros x hx
  rw [Set.inter_def]
  refine Set.nmem_setOf_iff.mpr ?_
  exact not_and.mpr fun a b => hx a
}

lemma SetNegRightProj (A B : Set (ℝ × ℝ)) : ∀ (x : (ℝ × ℝ)), x ∉ B → x ∉ (A ∩ B) := by {
  rw [Set.inter_comm]
  apply SetNegLeftProj
}

lemma ComplLemma (K : Set (ℝ × ℝ)) :
  ∀ (U : ι → Set (ℝ × ℝ)),
    (K ⊆ (⋃ i : ι, U i)) ↔ ∅ = (⋂ i : ι, ((U i)ᶜ ∩ K)) := by {
  rename_i nonTrivialIndex
  intros U
  constructor
  intro hu
  apply Eq.symm
  rw [Set.iInter_eq_empty_iff]
  intro x
  have hxCases : x ∈ K ∨ x ∉ K := by {
    exact Classical.em (x ∈ K)
  }
  cases' hxCases with xinK xnotinK
  have hxinSomeUi : ∃ i, x ∈ U i := by {
    exact Set.mem_iUnion.mp (hu xinK)
  }
  cases' hxinSomeUi with j hxinUj
  use j
  have hxnotinUjCompl : x ∉ (U j)ᶜ := by {
    exact fun a => a hxinUj
  }
  apply SetNegLeftProj (U j)ᶜ K
  exact hxnotinUjCompl
  have hxnotinUjComplInterK : ∀ i, x ∉ (U i)ᶜ ∩ K := by {
    intro i
    apply SetNegRightProj
    exact xnotinK
  }
  have hι : ι → ∃ i, x ∉ (U i)ᶜ ∩ K := by {
    intro j
    use j
    exact hxnotinUjComplInterK j
  }
  apply Nonempty.elim nonTrivialIndex
  exact hι
  intro hEmpty
  have h_inter_rewrite : (⋂ i, (U i)ᶜ ∩ K) = (⋂ i, (U i)ᶜ) ∩ K := by {
    exact Eq.symm (Set.iInter_inter K fun i => (U i)ᶜ)
  }
  rw [h_inter_rewrite] at hEmpty
  rw [← Set.compl_iUnion U] at hEmpty
  apply SetEmptyComplInter at hEmpty
  exact hEmpty
}

lemma CptCompl (K : Set (ℝ × ℝ)) : IsCompactR2Subcover K ↔ IsCptR2SubcoverCompl K := by {
  constructor
  intro hA
  unfold IsCompactR2Subcover at hA
  unfold IsCptR2SubcoverCompl

}

--citation: Royden, H.L., Real Analysis, 3rd Ed., Prentice Hall, NJ, 1988
def FiniteIntersectionPropertyR2 (ι : Type) (U : ι → Set (ℝ × ℝ)) : Prop :=
  ∀ (s : Finset ι), Set.Nonempty (⋂ i ∈ s, U i)

def IsCompactR2SeqDef (K : Set (ℝ × ℝ)) : Prop :=
  ∀ (u : ℕ → ℝ × ℝ), (∀ n, u n ∈ K) → ∃ (L : ℝ × ℝ) (φ : ℕ → ℕ),
    (L ∈ K) ∧ (StrictMono φ) ∧ (ConvergesR2 (u ∘ φ) L)

lemma IsCptFiniteIntersections (K : Set (ℝ × ℝ)) :
  ∀ (ι : Type), ∀ (U : ι → Set (ℝ × ℝ)),
    FiniteIntersectionPropertyR2 ι (fun i => (U i ∩ K)) → IsCompactR2Subcover K := by {
  intro index


}

theorem CptEquiv1 (S : Set (ℝ × ℝ)) : IsCompactR2Subcover S ↔ IsCompactR2SeqDef S := by {
  constructor
  intro h1
  unfold IsCompactR2SeqDef
  intro u
  intro hn
  unfold IsCompactR2Subcover at h1
  sorry

}

#check Metric.ball

def LimitSubsetsRtoR2' {X : Set ℝ} {Y : Set (ℝ × ℝ)} (f : X → Y) (a : X) (L : Y) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ (x : X), dist x a < δ ∧ x ≠ a → dist (f x) L < ε

def IsCtsRtoR2 {X : Set ℝ} {Y : Set (ℝ × ℝ)} (f : X → Y) : Prop :=
  ∀ (x : X), LimitSubsetsRtoR2' f x (f x)

def UnitInterval : Set ℝ :=
  { r : ℝ | 0 ≤ r ∧ r ≤ 1 }

def IsPathInR2 (S : Set (ℝ × ℝ)) : Prop :=
  ∃ φ : (UnitInterval → S), Function.Surjective φ ∧ IsCtsRtoR2 φ

lemma CtsOpenInvImagesRtoR2 {X : Set ℝ} {Y : Set (ℝ × ℝ)} (f : X → Y)
  : IsCtsRtoR2 f → IsOpenR X → IsOpenR2 Y := by {
  intros hcts hopen
  unfold IsOpenR2
  unfold IsOpenR at hopen

}

lemma CtsImagesCptRtoR2 {X : Set ℝ} {Y : Set (ℝ × ℝ)} (f : X → Y)
  : IsCtsRtoR2 f → IsCompactRSubcover X → IsCompactR2Subcover Y := by {
    intros hcts hcpt
    sorry
  }

theorem PathsCompact (S : Set (ℝ × ℝ)) : IsPathInR2 S → IsCompactR2Subcover S := by {
  sorry
}

end ManualEuclideanR2

-- Check the definition using our manual distance
#check ManualEuclideanR2.LimitR2toR2

--below fails bc euclideanDist not def on Y ?
--def LimitSubsetsRtoR2 {X : Set ℝ} {Y : Set (ℝ × ℝ)} (f : X → Y) (a : X) (L : Y) : Prop :=
--  ∀ ε > 0, ∃ δ > 0, ∀ x ∈ X,
--    0 < abs (x - a) ∧ abs (x - a) < δ → euclideanDist (f x) L < ε

--below fails bc x ∈ X means x : ℝ ?
--def IsCtsRtoR2 {X : Set ℝ} {Y : Set (ℝ × ℝ)} (f : X → Y) : Prop :=
--  ∀ x ∈ X, LimitSubsetsRtoR2' f x (f x)
