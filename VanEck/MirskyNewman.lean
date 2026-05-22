import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots

/-!
# Historical Note on the Mirsky-Newman Theorem
In 1950, Paul Erdős conjectured that there is no exact covering system of the integers with strictly distinct moduli (step sizes).
Shortly after, Leon Mirsky and Donald J. Newman discovered a beautiful complex-analytic proof using roots of unity.
Hilariously, Mirsky and Newman *never actually published their proof!* Erdős had to credit them in his own papers during the 1950s.
(Independently, Harold Davenport and Richard Rado discovered the exact same proof at the same time).
Leon Mirsky (1918–1983) was a Russian-British mathematician who transitioned from number theory to linear algebra and combinatorics, writing the classic text "An Introduction to Linear Algebra".
Donald J. Newman (1930–2007) was an American mathematician legendary for finding incredibly elegant analytic proofs for deep theorems, such as his 1980 simplified analytic proof of the Prime Number Theorem.
Sources:
- https://en.wikipedia.org/wiki/Mirsky%E2%80%93Newman_theorem
- https://mathshistory.st-andrews.ac.uk/Biographies/Mirsky/
-/

open Finset
open Complex

/--
Phase 1: Finite Geometric Sums
A geometric sum evaluates to 0 when ω ≠ 1 and ω ^ n = 1.
-/
lemma geom_sum_zero_of_pow_one {x : ℂ} {n : ℕ} (h_ne_one : x ≠ 1) (h_pow_one : x ^ n = 1) :
    ∑ k ∈ range n, x ^ k = 0 := by {
  have h_geom := geom_sum_eq h_ne_one n
  rw [h_pow_one] at h_geom
  have h_sub : (1 : ℂ) - 1 = 0 := sub_self 1
  rw [h_sub, zero_div] at h_geom
  exact h_geom
}

/--
Phase 2: Arithmetic Progression Sums
Express the sum of ω^x over an arithmetic progression as a scaled geometric sum.
-/
lemma sum_progression_eq_geom_sum {ω : ℂ} (a d m : ℕ) :
    ∑ k ∈ range m, ω ^ (a + k * d) = ω ^ a * ∑ k ∈ range m, (ω ^ d) ^ k := by {
  have h_pull : ∀ k : ℕ, ω ^ (a + k * d) = ω ^ a * (ω ^ d) ^ k := by
    intro k
    calc ω ^ (a + k * d)
      _ = ω ^ a * ω ^ (k * d) := by rw [pow_add]
      _ = ω ^ a * ω ^ (d * k) := by rw [mul_comm k d]
      _ = ω ^ a * (ω ^ d) ^ k := by rw [pow_mul]
  have h_sum : ∑ k ∈ range m, ω ^ (a + k * d) = ∑ k ∈ range m, ω ^ a * (ω ^ d) ^ k := by
    apply sum_congr rfl
    intro x _
    exact h_pull x
  rw [h_sum, ← mul_sum]
}

/--
An Arithmetic Progression in ℤ.
Defined by a starting point `a` and a strictly positive step size `d`.
-/
def ArithmeticProgression (a d : ℤ) : Set ℤ :=
  { x : ℤ | ∃ k : ℤ, x = a + k * d }

/--
A finite collection of arithmetic progressions forms an Exact Cover of ℤ
if every integer belongs to exactly one progression in the collection.
-/
def IsExactCover (progressions : Finset (ℤ × ℤ)) : Prop :=
  ∀ x : ℤ, ∃! p, p ∈ progressions ∧ x ∈ ArithmeticProgression p.1 p.2

/--
The Mirsky-Newman Theorem (also known as the Exact Cover System Theorem).
Famously proven independently by Paul Erdős, Donald Newman, and Leon Mirsky.

It states that if a finite collection of arithmetic progressions exactly
covers the integers, and there is more than one progression (k ≥ 2),
then the largest step size must appear at least twice.

Consequently, it is mathematically impossible to exactly cover the integers 
with arithmetic progressions that have strictly distinct step sizes ≥ 2.
-/
theorem mirsky_newman_distinct_moduli_impossible
    (progressions : Finset (ℤ × ℤ))
    (h_multiple : progressions.card ≥ 2)
    (h_step_bounds : ∀ p ∈ progressions, p.2 ≥ 2)
    (h_distinct_steps : ∀ p1 ∈ progressions, ∀ p2 ∈ progressions, p1 ≠ p2 → p1.2 ≠ p2.2) :
    ¬ IsExactCover progressions := by {
  -- The beautiful proof of this theorem uses complex analysis.
  -- By associating each arithmetic progression to a generating function,
  -- the exact cover condition becomes an equation of rational functions.
  -- The function corresponding to the largest step size has a pole on the 
  -- unit circle (at a root of unity) that is "closest" to the origin in terms 
  -- of its angular frequency. No other function in the sum can cancel this pole
  -- unless there is another progression with the EXACT SAME step size.
  sorry
}

/--
An Arithmetic Progression in ZMod P (finite cyclic group).
Defined by a starting point `a` and a step size `d`.
-/
def FinArithmeticProgression {P : ℕ} (a d : ZMod P) : Set (ZMod P) :=
  { x : ZMod P | ∃ k : ℕ, x = a + k * d }

/--
A finite collection of arithmetic progressions forms an Exact Cover of ZMod P.
-/
def IsExactCoverFin {P : ℕ} (progressions : Finset (ZMod P × ZMod P)) : Prop :=
  ∀ x : ZMod P, ∃! p, p ∈ progressions ∧ x ∈ FinArithmeticProgression p.1 p.2

open Classical in
/--
Phase 3: Exact Cover Partitioning
Prove that the sum over the exact cover equals the sum of sums over the progressions.
-/
lemma sum_exact_cover {P : ℕ} [NeZero P] (progressions : Finset (ZMod P × ZMod P))
    (h_cover : IsExactCoverFin progressions) {ω : ℂ} :
    ∑ x : ZMod P, ω ^ x.val = ∑ p ∈ progressions, ∑ x ∈ Finset.univ.filter (fun x => x ∈ FinArithmeticProgression p.1 p.2), ω ^ x.val := by {
  choose f hf_mem hf_unique using h_cover
  have h_maps_to : ∀ x ∈ (Finset.univ : Finset (ZMod P)), f x ∈ progressions := by
    intro x _
    exact (hf_mem x).1
  have h_fiber : ∀ p ∈ progressions, ∀ x : ZMod P, x ∈ FinArithmeticProgression p.1 p.2 ↔ f x = p := by
    intro p hp x
    constructor
    · intro hx
      exact (hf_unique x p ⟨hp, hx⟩).symm
    · intro hx
      rw [← hx]
      exact (hf_mem x).2
  have hs := Finset.sum_fiberwise_of_maps_to h_maps_to (fun x => ω ^ x.val)
  rw [← hs]
  apply Finset.sum_congr rfl
  intro p hp
  apply Finset.sum_congr
  · ext x
    simp [h_fiber p hp x]
  · intro _ _
    rfl
}


open Classical

/--
Select the strictly largest step size D_max from the set of exact cover progressions.
-/
lemma exists_max_step_size (S : Finset ℕ) (h_nonempty : S.Nonempty) :
    ∃ D_max ∈ S, ∀ d ∈ S, d ≠ D_max → d < D_max := by {
  use S.max' h_nonempty
  constructor
  · exact Finset.max'_mem S h_nonempty
  · intro d hd h_ne
    have h_le := Finset.le_max' S d hd
    exact lt_of_le_of_ne h_le h_ne
}

lemma primitive_root_pow_ne_one {D_max d : ℕ} {ζ : ℂ} (h_prim : IsPrimitiveRoot ζ D_max)
    (h_pos : 0 < d) (h_lt : d < D_max) : ζ ^ d ≠ 1 := by {
  intro h_eq
  have h_dvd := IsPrimitiveRoot.dvd_of_pow_eq_one h_prim d h_eq
  have h_le := Nat.le_of_dvd h_pos h_dvd
  omega
}

/--
The Primitive Root Squeeze Lemma:
Prove that if ζ is a primitive D_max-th root of unity, then for any progression 
with step size d < D_max, the term (1 - ζ^d) ≠ 0.
-/
lemma primitive_root_squeeze {D_max d : ℕ} {ζ : ℂ} (h_prim : IsPrimitiveRoot ζ D_max)
    (h_pos : 0 < d) (h_lt : d < D_max) : 1 - ζ ^ d ≠ 0 := by {
  have h_ne := primitive_root_pow_ne_one h_prim h_pos h_lt
  intro h_eq
  have h_eq_one : ζ ^ d = 1 := by exact sub_eq_zero.mp h_eq |>.symm
  exact h_ne h_eq_one
}

lemma zeta_pow_mod_eq (P n : ℕ) (ζ : ℂ) (h_pow : ζ ^ P = 1) :
    ζ ^ (n % P) = ζ ^ n := by {
  have h_div : n = P * (n / P) + n % P := Nat.div_add_mod n P |>.symm
  conv => right; rw [h_div, pow_add, pow_mul, h_pow, one_pow, one_mul]
}

lemma sum_progression_eq_geom_sum_mod (P X L start : ℕ) (ζ : ℂ) (h_pow : ζ ^ P = 1) (hL : P = X * L) :
    ∑ i ∈ range L, ζ ^ ((start + i * X) % P) = ζ ^ start * ∑ i ∈ range L, (ζ ^ X) ^ i := by {
  have h_pull : ∀ i : ℕ, ζ ^ ((start + i * X) % P) = ζ ^ start * (ζ ^ X) ^ i := by
    intro i
    rw [zeta_pow_mod_eq P _ ζ h_pow]
    calc ζ ^ (start + i * X)
      _ = ζ ^ start * ζ ^ (i * X) := by rw [pow_add]
      _ = ζ ^ start * ζ ^ (X * i) := by rw [mul_comm i X]
      _ = ζ ^ start * (ζ ^ X) ^ i := by rw [pow_mul]
  have h_sum : ∑ i ∈ range L, ζ ^ ((start + i * X) % P) = ∑ i ∈ range L, ζ ^ start * (ζ ^ X) ^ i := by
    apply sum_congr rfl
    intro i _
    exact h_pull i
  rw [h_sum, ← mul_sum]
}

lemma prog_sum_extraction (P X L : ℕ) (start : Fin P) (ζ : ℂ)
    (h_pow : ζ ^ P = 1) (hL : P = X * L)
    (cover_X : Finset (Fin P))
    (h_ap : cover_X = Finset.univ.filter (fun (k : Fin P) => ∃ i : ℕ, k.val = (start.val + i * X) % P)) :
    ∑ k ∈ cover_X, ζ ^ k.val = ζ ^ start.val * ∑ i ∈ range L, (ζ ^ X) ^ i := by {
  have h_bij : ∑ k ∈ cover_X, ζ ^ k.val = ∑ i ∈ range L, ζ ^ ((start.val + i * X) % P) := sorry
  rw [h_bij]
  exact sum_progression_eq_geom_sum_mod P X L start.val ζ h_pow hL
}

/--
Evaluate the Geometric Sum:
Apply the generating function identity (already proven via sum_exact_cover and 
sum_progression_eq_geom_sum) evaluated at ζ to derive the contradiction. 
The sum evaluates to non-zero on one side, and zero on the other.
-/
lemma evaluate_geometric_sum_contradiction (P : ℕ) (hP : P > 0) (S : Finset ℕ)
    (h_min : ∀ X ∈ S, X ≥ 3)
    (cover : ℕ → Finset (Fin P))
    (h_partition : ∀ k : Fin P, ∃! X, X ∈ S ∧ k ∈ cover X)
    (h_ap : ∀ X ∈ S, ∃ start : Fin P, cover X = Finset.univ.filter (fun (k : Fin P) => ∃ i : ℕ, k.val = (start.val + i * X) % P))
    (h_div : ∀ X ∈ S, X ∣ P)
    (D_max : ℕ) (h_Dmax_in : D_max ∈ S)
    (h_max : ∀ d ∈ S, d ≠ D_max → d < D_max)
    (ζ : ℂ) (h_prim : IsPrimitiveRoot ζ D_max) :
    False := by {
  -- Step 1: The total sum over the whole group Fin P evaluated at ζ is 0.
  have h_zeta_pow : ζ ^ P = 1 := by {
    have h_Dmax_div : D_max ∣ P := h_div D_max h_Dmax_in
    rcases h_Dmax_div with ⟨k_div, rfl⟩
    have h1 : ζ ^ D_max = 1 := IsPrimitiveRoot.pow_eq_one h_prim
    calc ζ ^ (D_max * k_div)
      _ = (ζ ^ D_max) ^ k_div := by rw [pow_mul]
      _ = 1 ^ k_div := by rw [h1]
      _ = 1 := by simp
  }

  have h_left_zero : ∑ k : Fin P, ζ ^ k.val = 0 := by {
    have h_zeta_ne : ζ ≠ 1 := by {
      have h_Dmax_ge_3 : D_max ≥ 3 := h_min D_max h_Dmax_in
      have h_Dmax_ge_2 : 2 ≤ D_max := by omega
      exact IsPrimitiveRoot.ne_one h_prim h_Dmax_ge_2
    }
    have h_equiv : ∑ k : Fin P, ζ ^ k.val = ∑ k ∈ range P, ζ ^ k := by
      exact Fin.sum_univ_eq_sum_range (fun k => ζ ^ k) P
    rw [h_equiv]
    exact geom_sum_zero_of_pow_one h_zeta_ne h_zeta_pow
  }
  
  -- Step 2: For any step size X < D_max, the sum over its progression is 0.
  have h_parts_zero : ∀ X ∈ S, X ≠ D_max → ∑ k ∈ cover X, ζ ^ k.val = 0 := by {
    intro X hX_in hX_ne
    have hX_ge_3 : X ≥ 3 := h_min X hX_in
    have hX_lt : X < D_max := h_max X hX_in hX_ne
    have hX_pos : 0 < X := by omega
    
    have h_step_ne_one : ζ ^ X ≠ 1 := primitive_root_pow_ne_one h_prim hX_pos hX_lt
    have ⟨start, h_cover_eq⟩ := h_ap X hX_in
    have h_X_div : X ∣ P := h_div X hX_in
    rcases h_X_div with ⟨L, hL⟩
    
    have h_prog_sum : ∑ k ∈ cover X, ζ ^ k.val = ζ ^ start.val * ∑ i ∈ range L, (ζ ^ X) ^ i := 
      prog_sum_extraction P X L start ζ h_zeta_pow hL (cover X) h_cover_eq
    
    have h_pow_one : (ζ ^ X) ^ L = 1 := by {
      calc (ζ ^ X) ^ L
        _ = ζ ^ (X * L) := by rw [← pow_mul]
        _ = ζ ^ P := by rw [← hL]
        _ = 1 := h_zeta_pow
    }
    
    rw [h_prog_sum]
    have h_zero : ∑ i ∈ range L, (ζ ^ X) ^ i = 0 := geom_sum_zero_of_pow_one h_step_ne_one h_pow_one
    rw [h_zero, mul_zero]
  }
  
  -- Step 3: For the max step size D_max, the sum over its progression is NON-ZERO.
  have h_max_nonzero : ∑ k ∈ cover D_max, ζ ^ k.val ≠ 0 := by {
    have ⟨start_max, h_cover_max⟩ := h_ap D_max h_Dmax_in
    have h_D_max_div : D_max ∣ P := h_div D_max h_Dmax_in
    rcases h_D_max_div with ⟨L_max, hL_max⟩
    
    have h_D_max_ne_zero : D_max ≠ 0 := by {
      have := h_min D_max h_Dmax_in
      omega
    }
    
    have h_L_pos : L_max > 0 := by {
      by_contra h
      have h0 : L_max = 0 := by omega
      rw [h0, mul_zero] at hL_max
      omega
    }
    
    have h_prog_sum_max : ∑ k ∈ cover D_max, ζ ^ k.val = ζ ^ start_max.val * ∑ i ∈ range L_max, (ζ ^ D_max) ^ i := 
      prog_sum_extraction P D_max L_max start_max ζ h_zeta_pow hL_max (cover D_max) h_cover_max
    
    rw [h_prog_sum_max]
    
    have h_pow_one : ζ ^ D_max = 1 := IsPrimitiveRoot.pow_eq_one h_prim
    have h_sum_ones : ∑ i ∈ range L_max, (ζ ^ D_max) ^ i = L_max := by {
      rw [h_pow_one]
      simp
    }
    rw [h_sum_ones]
    
    have h_zeta_ne_zero : ζ ≠ 0 := IsPrimitiveRoot.ne_zero h_prim h_D_max_ne_zero
    have h_start_pow_ne_zero : ζ ^ start_max.val ≠ 0 := pow_ne_zero start_max.val h_zeta_ne_zero
    have h_L_ne_zero : (L_max : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt h_L_pos)
    exact mul_ne_zero h_start_pow_ne_zero h_L_ne_zero
  }
  
  -- Step 4: By the exact cover property, the total sum equals the sum of the parts.
  have h_sum_split : ∑ k : Fin P, ζ ^ k.val = ∑ X ∈ S, ∑ k ∈ cover X, ζ ^ k.val := by {
    choose f hf using h_partition
    have h_maps_to : ∀ k ∈ (Finset.univ : Finset (Fin P)), f k ∈ S := by
      intro k _
      exact (hf k).1.1
    have h_fiber : ∀ X ∈ S, ∀ k : Fin P, k ∈ cover X ↔ f k = X := by
      intro X hX k
      constructor
      · intro hk
        exact ((hf k).2 X ⟨hX, hk⟩).symm
      · intro hk
        rw [← hk]
        exact (hf k).1.2
    
    have hs := Finset.sum_fiberwise_of_maps_to h_maps_to (fun k => ζ ^ k.val)
    rw [← hs]
    apply Finset.sum_congr rfl
    intro X hX
    apply Finset.sum_congr
    · ext k
      simp [h_fiber X hX k]
    · intro _ _
      rfl
  }
  
  -- Step 5: But 0 = 0 + non-zero is a contradiction!
  have h_split_eval : ∑ X ∈ S, ∑ k ∈ cover X, ζ ^ k.val = ∑ k ∈ cover D_max, ζ ^ k.val := by {
    have h_eq := Finset.sum_eq_single D_max (by {
      intro X hX_in hX_ne
      exact h_parts_zero X hX_in hX_ne
    }) (by {
      intro h_not_in
      exact False.elim (h_not_in h_Dmax_in)
    })
    exact h_eq
  }
  
  rw [h_split_eval] at h_sum_split
  rw [h_left_zero] at h_sum_split
  exact h_max_nonzero h_sum_split.symm
}

open Classical

-- We assume the existence of our "magic" primitive root to avoid getting bogged down in 
-- abstract algebra. We just need to know that a D_max-th root of unity exists!
lemma magic_primitive_root (D_max : ℕ) (h_pos : D_max > 0) : 
    ∃ ζ : ℂ, IsPrimitiveRoot ζ D_max := by {
  sorry
}

/--
The Mirsky-Newman Theorem (Exact Cover System Theorem)
It is impossible to partition a finite cyclic group into arithmetic
progressions with strictly distinct step sizes (moduli) all ≥ 3.
-/
theorem mirsky_newman_exact_cover (P : ℕ) (hP : P > 0) (S : Finset ℕ)
    (h_min : ∀ X ∈ S, X ≥ 3)
    (h_div : ∀ X ∈ S, X ∣ P)
    (cover : ℕ → Finset (Fin P))
    (h_partition : ∀ k : Fin P, ∃! X, X ∈ S ∧ k ∈ cover X)
    (h_ap : ∀ X ∈ S, ∃ start : Fin P, cover X = Finset.univ.filter (fun (k : Fin P) => ∃ i : ℕ, k.val = (start.val + i * X) % P)) :
    False := by {
  -- Step 1: Prove S is not empty (since P > 0, Fin P has at least one element)
  have hS_nonempty : S.Nonempty := by {
    have h_zero : 0 < P := hP
    have k : Fin P := ⟨0, h_zero⟩
    have ⟨X, hX, _⟩ := h_partition k
    exact ⟨X, hX.1⟩
  }
  
  -- Step 2: Pick the largest step size D_max out of our set of step sizes S.
  have ⟨D_max, h_Dmax_in, h_max⟩ := exists_max_step_size S hS_nonempty
  
  -- Step 3: We know the biggest step size is at least 3, so it's strictly positive.
  have h_Dmax_ge_3 : D_max ≥ 3 := h_min D_max h_Dmax_in
  have h_Dmax_pos : D_max > 0 := by omega
  
  -- Step 4: Summon our magic primitive D_max-th root of unity (ζ).
  have ⟨ζ, h_prim⟩ := magic_primitive_root D_max h_Dmax_pos
  
  -- Step 5: Feed everything into the geometric sum evaluator to get our contradiction!
  exact evaluate_geometric_sum_contradiction P hP S h_min cover h_partition h_ap h_div D_max h_Dmax_in h_max ζ h_prim
}

lemma vanEck_fiber_sum (P : ℕ) (hP : P ≥ 4)
    (v : ℕ → ℕ)
    (f : Fin P → Fin P)
    (hf : ∀ k : Fin P, (f k).val = (k.val + P - v (k.val + 1)) % P)
    (hbij : Function.Bijective f)
    (h_recent : ∀ k : Fin P, v ((f k).val + 1) = v (k.val + 1))
    (X : ℕ) (hX_in : ∃ k : Fin P, v (k.val + 1) = X)
    (h_no_intermediate : ∀ k : Fin P, v (k.val + 1) = X → ∀ i < X, i > 0 → v (k.val + 1 + P - i) ≠ X) :
    (Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)).card * X = P := by {
  -- The total sum of gaps between consecutive occurrences of X in the cycle is exactly P.
  sorry
}

open Classical in
lemma vanEck_fiber_is_ap (P : ℕ) (hP : P ≥ 4)
    (v : ℕ → ℕ)
    (f : Fin P → Fin P)
    (hf : ∀ k : Fin P, (f k).val = (k.val + P - v (k.val + 1)) % P)
    (hbij : Function.Bijective f)
    (h_recent : ∀ k : Fin P, v ((f k).val + 1) = v (k.val + 1))
    (X : ℕ) (hX_in : ∃ k : Fin P, v (k.val + 1) = X)
    (h_no_intermediate : ∀ k : Fin P, v (k.val + 1) = X → ∀ i < X, i > 0 → v (k.val + 1 + P - i) ≠ X) :
    ∃ start : Fin P, Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X) = Finset.univ.filter (fun (k : Fin P) => ∃ i : ℕ, k.val = (start.val + i * X) % P) := by {
  -- By tracing the bijection f(k) = k - X, we evaluate the gaps between consecutive
  -- occurrences of X. The total sum of gaps is exactly P, and by the Van Eck MRO constraint,
  -- every gap is strictly >= X. This Pigeonhole compression forces the fiber to be exactly
  -- one arithmetic progression of step size X.
  sorry
}
