/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Sarason.Definitions

/-!
# Sarason - The Riemann Zeta Function and Prime Number Theorem

Initial definitions for the Riemann Zeta Function and Laplace Transforms
as preparation for Newman's Tauberian Theorem and the Prime Number Theorem.
-/

open Complex Filter TopologicalSpace Metric Bornology Classical
open Sarason

namespace Sarason.PNT

/-- 
  The partial sum of the Riemann Zeta function. 
-/
noncomputable def zetaPartialSum (N : ℕ) (s : ℂ) : ℂ :=
  ∑ i ∈ Finset.range N, (if i = 0 then 0 else (i : ℂ) ^ (-s))

/-- 
  The Riemann Zeta function defined via Weierstrass epsilon-delta limit. 
-/
def IsZetaAt_eps (s : ℂ) (L : ℂ) : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ‖zetaPartialSum N s - L‖ < ε

/-- 
  Classical definition of the Zeta function value extracted via choice, 
  or 0 if the series does not converge. 
-/
noncomputable def zeta_eps (s : ℂ) : ℂ :=
  if h : ∃ L, IsZetaAt_eps s L then Classical.choose h else 0

/--
  The partial Euler product up to N for the Riemann Zeta function.
  This is the product over all prime numbers p ≤ N of (1 - p^{-s})^{-1}.
-/
noncomputable def eulerPartialProduct (N : ℕ) (s : ℂ) : ℂ :=
  -- We filter the range `[0, N]` for primes
  ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, 
    -- For each prime, we multiply by the Euler factor
    (1 - (p : ℂ) ^ (-s))⁻¹

/--
  Weierstrass epsilon-delta definition of the Euler Product's convergence.
-/
def IsEulerProductAt_eps (s : ℂ) (L : ℂ) : Prop :=
  ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ‖eulerPartialProduct N s - L‖ < ε

/--
  Classical extraction of the Euler Product limit via the Axiom of Choice.
-/
noncomputable def eulerProduct_eps (s : ℂ) : ℂ :=
  if h : ∃ L, IsEulerProductAt_eps s L then Classical.choose h else 0

/-- 
  The Laplace transform of a function $f: \mathbb{R} \to \mathbb{C}$ 
  evaluated at $z \in \mathbb{C}$. 
  (Placeholder for full integration theory). 
-/
def IsLaplaceTransformAt_eps (f : ℝ → ℂ) (z : ℂ) (L : ℂ) : Prop :=
  ∀ ε > 0, ∃ T₀ > 0, ∀ T ≥ T₀, 
    -- Placeholder limit for integral from 0 to T of f(t) e^{-zt}
    ‖(0 : ℂ) - L‖ < ε -- To be replaced with actual contour integral definition

/-- Limit existence for the Riemann Zeta partial sums -/
lemma zeta_eps_limit (s : ℂ) (hs : 1 < s.re) : ∃ L, IsZetaAt_eps s L := by
{
  sorry
}

/-- Limit existence for the Euler Product -/
lemma eulerProduct_eps_limit (s : ℂ) (hs : 1 < s.re) : ∃ L, IsEulerProductAt_eps s L := by
{
  sorry
}

/-- The partial sums and partial products asymptotically converge to the same value -/
lemma euler_product_approx (s : ℂ) (hs : 1 < s.re) (ε : ℝ) (hε : ε > 0) : 
    ∃ N₀, ∀ N ≥ N₀, ‖zetaPartialSum N s - eulerPartialProduct N s‖ < ε := by
{
  sorry
}

/-- 
  If both limits exist and they asymptotically approximate each other,
  then their classical limit extractions must be equal.
-/
lemma zeta_eps_eq_of_approx (s : ℂ) (hs : 1 < s.re)
    (h_zeta : ∃ L, IsZetaAt_eps s L)
    (h_euler : ∃ L, IsEulerProductAt_eps s L)
    (h_approx : ∀ ε > 0, ∃ N₀, ∀ N ≥ N₀, ‖zetaPartialSum N s - eulerPartialProduct N s‖ < ε) :
    zeta_eps s = eulerProduct_eps s := by
{
  have h_zeta_val : IsZetaAt_eps s (zeta_eps s) := by
  {
    dsimp [zeta_eps]
    rw [dif_pos h_zeta]
    exact Classical.choose_spec h_zeta
  }
  have h_euler_val : IsEulerProductAt_eps s (eulerProduct_eps s) := by
  {
    dsimp [eulerProduct_eps]
    rw [dif_pos h_euler]
    exact Classical.choose_spec h_euler
  }
  -- By metric uniqueness of limits, since the difference tends to 0, they are equal.
  unfold IsZetaAt_eps at h_zeta_val
  unfold IsEulerProductAt_eps at h_euler_val
  
  apply eq_of_norm_sub_le_zero
  apply le_of_forall_pos_le_add
  intro ε hε
  have hε3 : ε / 3 > 0 := div_pos hε (by norm_num)
  rcases h_zeta_val (ε / 3) hε3 with ⟨N1, hN1⟩
  rcases h_euler_val (ε / 3) hε3 with ⟨N2, hN2⟩
  rcases h_approx (ε / 3) hε3 with ⟨N3, hN3⟩
  let N := max N1 (max N2 N3)
  have h1 := hN1 N (le_max_left N1 _)
  have h2 := hN2 N (le_trans (le_max_left N2 N3) (le_max_right N1 _))
  have h3 := hN3 N (le_trans (le_max_right N2 N3) (le_max_right N1 _))
  
  have ht1 : ‖zeta_eps s - eulerProduct_eps s‖ = ‖(zeta_eps s - zetaPartialSum N s) + (zetaPartialSum N s - eulerPartialProduct N s) + (eulerPartialProduct N s - eulerProduct_eps s)‖ := by { congr 1; ring }
  have ht2 : ‖(zeta_eps s - zetaPartialSum N s) + (zetaPartialSum N s - eulerPartialProduct N s) + (eulerPartialProduct N s - eulerProduct_eps s)‖ ≤ ‖(zeta_eps s - zetaPartialSum N s) + (zetaPartialSum N s - eulerPartialProduct N s)‖ + ‖eulerPartialProduct N s - eulerProduct_eps s‖ := norm_add_le _ _
  have ht3 : ‖(zeta_eps s - zetaPartialSum N s) + (zetaPartialSum N s - eulerPartialProduct N s)‖ ≤ ‖zeta_eps s - zetaPartialSum N s‖ + ‖zetaPartialSum N s - eulerPartialProduct N s‖ := norm_add_le _ _
  have h_triangle : ‖zeta_eps s - eulerProduct_eps s‖ ≤ ‖zeta_eps s - zetaPartialSum N s‖ + ‖zetaPartialSum N s - eulerPartialProduct N s‖ + ‖eulerPartialProduct N s - eulerProduct_eps s‖ := by linarith
  
  have h_norm_symm : ‖zeta_eps s - zetaPartialSum N s‖ = ‖zetaPartialSum N s - zeta_eps s‖ := norm_sub_rev _ _
  rw [h_norm_symm] at h_triangle
  
  have h_sum : ‖zetaPartialSum N s - zeta_eps s‖ + ‖zetaPartialSum N s - eulerPartialProduct N s‖ + ‖eulerPartialProduct N s - eulerProduct_eps s‖ < ε := by linarith
  
  have h_lt : ‖zeta_eps s - eulerProduct_eps s‖ < ε := lt_of_le_of_lt h_triangle h_sum
  
  rw [zero_add]
  exact le_of_lt h_lt
}

/--
  The fundamental identity connecting the Riemann Zeta function to the primes:
  For any complex number s with strictly real part > 1, the limit of the partial sums
  is exactly equal to the limit of the Euler product.
  
  This relies on the Fundamental Theorem of Arithmetic (unique prime factorization)
  and the absolute convergence of the geometric series.
-/
lemma zeta_eq_eulerProduct (s : ℂ) (hs : 1 < s.re) :
    zeta_eps s = eulerProduct_eps s := by
{
  apply zeta_eps_eq_of_approx s hs
  · exact zeta_eps_limit s hs
  · exact eulerProduct_eps_limit s hs
  · exact euler_product_approx s hs
}

/--
  Algebraic isolation of the geometric series inverse.
  We express (1 - z)⁻¹ as a finite polynomial sum plus a remainder term.
-/
lemma geom_sum_inv_expansion (z : ℂ) (K : ℕ) (hz : z ≠ 1) :
    (1 - z)⁻¹ = (∑ k ∈ Finset.range K, z ^ k) + z ^ K * (1 - z)⁻¹ := by
{
  have h_ne_zero : 1 - z ≠ 0 := sub_ne_zero.mpr (Ne.symm hz)
  have h_geom : (∑ k ∈ Finset.range K, z ^ k) * (1 - z) = 1 - z ^ K := by
  {
    calc (∑ k ∈ Finset.range K, z ^ k) * (1 - z)
      _ = -((∑ k ∈ Finset.range K, z ^ k) * (z - 1)) := by ring
      _ = -(z ^ K - 1) := by rw [geom_sum_mul z K]
      _ = 1 - z ^ K := by ring
  }
  -- We start with the identity: Sum * (1 - z) = 1 - z^K
  -- Multiply both sides by (1 - z)⁻¹ on the right
  have h_mul : (∑ k ∈ Finset.range K, z ^ k) * (1 - z) * (1 - z)⁻¹ = (1 - z ^ K) * (1 - z)⁻¹ := by rw [h_geom]
  -- The left side simplifies to Sum
  rw [mul_assoc, mul_inv_cancel₀ h_ne_zero, mul_one] at h_mul
  -- The right side expands
  have h_expand : (1 - z ^ K) * (1 - z)⁻¹ = (1 - z)⁻¹ - z ^ K * (1 - z)⁻¹ := by
  {
    calc (1 - z ^ K) * (1 - z)⁻¹
      _ = 1 * (1 - z)⁻¹ - z ^ K * (1 - z)⁻¹ := sub_mul 1 (z ^ K) ((1 - z)⁻¹)
      _ = (1 - z)⁻¹ - z ^ K * (1 - z)⁻¹ := by rw [one_mul]
  }
  rw [h_expand] at h_mul
  -- Now we have Sum = (1 - z)⁻¹ - z^K * (1 - z)⁻¹
  -- Add the remainder to both sides
  calc (1 - z)⁻¹
    _ = (1 - z)⁻¹ - z ^ K * (1 - z)⁻¹ + z ^ K * (1 - z)⁻¹ := by ring
    _ = (∑ k ∈ Finset.range K, z ^ k) + z ^ K * (1 - z)⁻¹ := by rw [← h_mul]
}

/--
  The inverse Euler factor for a single prime expressed as a finite geometric polynomial plus a remainder.
  This allows us to bound the error when truncating the prime geometric series.
-/
lemma prime_euler_factor_inv (p : ℕ) (s : ℂ) (K : ℕ) (hz : (p : ℂ) ^ (-s) ≠ 1) :
    (1 - (p : ℂ) ^ (-s))⁻¹ = (∑ k ∈ Finset.range K, ((p : ℂ) ^ (-s)) ^ k) + (((p : ℂ) ^ (-s)) ^ K) * (1 - (p : ℂ) ^ (-s))⁻¹ := by
{
  exact geom_sum_inv_expansion ((p : ℂ) ^ (-s)) K hz
}

/--
  The set of integers S(N) whose prime factors are all less than or equal to N.
  These are exactly the integers generated by the finite Euler product up to N.
-/
def SmoothNumbers (N : ℕ) : Set ℕ :=
  {n : ℕ | n > 0 ∧ ∀ p, p.Prime → p ∣ n → p ≤ N}

/--
  The Fundamental Theorem of Arithmetic (FTA) Bijection Lemma for Smooth Numbers.
  Every integer in S(N) has a unique factorization supported only on primes ≤ N.
  This formalizes the exact combinatorial bridge needed to turn the Euler product
  into the Zeta partial sums.
-/
lemma smooth_numbers_fta_bijection (N : ℕ) (n : ℕ) (hn : n ∈ SmoothNumbers N) :
    ∃! (f : ℕ →₀ ℕ), (∀ p ∈ f.support, p.Prime ∧ p ≤ N) ∧ f.prod (fun p k => p ^ k) = n := by
{
  -- The existence is witnessed by the standard prime factorization of n
  use n.factorization
  constructor
  · constructor
    · intro p hp
      have h_prime := Nat.prime_of_mem_primeFactors hp
      have h_dvd := Nat.dvd_of_mem_primeFactors hp
      exact ⟨h_prime, hn.right p h_prime h_dvd⟩
    · exact Nat.prod_factorization_pow_eq_self (ne_of_gt hn.left)
  · -- Uniqueness follows from the equivalence between ℕ+ and prime-supported Finsupps
    intro g hg
    have h_prime_supp : ∀ p ∈ g.support, p.Prime := fun p hp => (hg.1 p hp).1
    let g_sub : { f : ℕ →₀ ℕ // ∀ p ∈ f.support, p.Prime } := ⟨g, h_prime_supp⟩
    have h_symm : (Nat.factorizationEquiv.symm g_sub).val = n := by
    {
      have h1 : (Nat.factorizationEquiv.symm g_sub).val = g_sub.val.prod (fun p k => p ^ k) := 
        Nat.factorizationEquiv_symm_apply_coe g_sub
      rw [h1]
      exact hg.2
    }
    let n_pos : ℕ+ := ⟨n, hn.left⟩
    have h_symm_eq : Nat.factorizationEquiv.symm g_sub = n_pos := Subtype.ext h_symm
    have h_equiv := Equiv.apply_symm_apply Nat.factorizationEquiv g_sub
    rw [h_symm_eq] at h_equiv
    have h_val : (Nat.factorizationEquiv n_pos).val = g_sub.val := by rw [h_equiv]
    exact h_val.symm
}

/--
  The finite set of integers generated by prime factors up to N,
  where no prime exponent exceeds K.
-/
noncomputable def smoothNumbersBoundedFinset (N K : ℕ) : Finset ℕ :=
  have : DecidablePred (fun n => n > 0 ∧ ∀ p, p.Prime → p ∣ n → p ≤ N ∧ n.factorization p ≤ K) := Classical.decPred _
  (Finset.range ((N.factorial ^ K) + 1)).filter (fun n => n > 0 ∧ ∀ p, p.Prime → p ∣ n → p ≤ N ∧ n.factorization p ≤ K)

/-- 
  Combinatorial equivalence between sequences of exponents and smooth numbers.
-/
lemma smooth_numbers_finset_equiv (N K : ℕ) :
    -- Placeholder for the Finset.prod_sum geometric equivalence bijection
    True := by
{
  sorry
}

/--
  Expanding the finite Euler product geometrically yields exactly the sum over the bounded smooth numbers.
  This bypasses infinite sets and keeps the analytic bounds cleanly in Finset terrain.
-/
lemma euler_product_expand_sum (N K : ℕ) (s : ℂ) :
    ∏ p ∈ (Finset.range (N + 1)).filter Nat.Prime, (∑ k ∈ Finset.range (K + 1), ((p : ℂ) ^ (-s)) ^ k) =
    ∑ n ∈ smoothNumbersBoundedFinset N K, (n : ℂ) ^ (-s) := by
{
  have h_bijection := smooth_numbers_finset_equiv N K
  -- We commute Finset.prod_sum and map via the FTA bijection.
  sorry
}

end Sarason.PNT
