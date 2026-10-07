import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.Data.Nat.Factorization.Defs

def SmoothNumbers (N : ℕ) : Set ℕ :=
  {n : ℕ | n > 0 ∧ ∀ p, p.Prime → p ∣ n → p ≤ N}

lemma smooth_numbers_fta_bijection (N : ℕ) (n : ℕ) (hn : n ∈ SmoothNumbers N) :
    ∃! (f : ℕ →₀ ℕ), (∀ p ∈ f.support, p.Prime ∧ p ≤ N) ∧ f.prod (fun p k => p ^ k) = n := by
{
  use n.factorization
  constructor
  · constructor
    · intro p hp
      have h_prime := Nat.prime_of_mem_primeFactors hp
      have h_dvd := Nat.dvd_of_mem_primeFactors hp
      exact ⟨h_prime, hn.right p h_prime h_dvd⟩
    · exact Nat.prod_factorization_pow_eq_self (ne_of_gt hn.left)
  · intro g hg
    have h_prime_supp : ∀ p ∈ g.support, p.Prime := fun p hp => (hg.1 p hp).1
    let g_sub : { f : ℕ →₀ ℕ // ∀ p ∈ f.support, p.Prime } := ⟨g, h_prime_supp⟩
    have h_symm : (Nat.factorizationEquiv.symm g_sub).val = n := by
      have h1 : (Nat.factorizationEquiv.symm g_sub).val = g_sub.val.prod (fun p k => p ^ k) := 
        Nat.factorizationEquiv_symm_apply_coe g_sub
      rw [h1]
      exact hg.2
    
    let n_pos : ℕ+ := ⟨n, hn.left⟩
    have h_symm_eq : Nat.factorizationEquiv.symm g_sub = n_pos := Subtype.ext h_symm
    
    have h_equiv := Equiv.apply_symm_apply Nat.factorizationEquiv g_sub
    rw [h_symm_eq] at h_equiv
    have h_val : (Nat.factorizationEquiv n_pos).val = g_sub.val := by rw [h_equiv]
    exact h_val.symm
}
