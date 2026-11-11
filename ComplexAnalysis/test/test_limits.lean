import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex

open Complex Filter TopologicalSpace Metric Bornology Classical

lemma test (a b : ℕ → ℂ) (L1 L2 : ℂ)
  (h_zeta_val : ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ‖a N - L1‖ < ε)
  (h_euler_val : ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ‖b N - L2‖ < ε)
  (h_approx : ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ‖a N - b N‖ < ε) :
  L1 = L2 := by
{
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
  
  have ht1 : ‖L1 - L2‖ = ‖(L1 - a N) + (a N - b N) + (b N - L2)‖ := by { congr 1; ring }
  have ht2 : ‖(L1 - a N) + (a N - b N) + (b N - L2)‖ ≤ ‖(L1 - a N) + (a N - b N)‖ + ‖b N - L2‖ := norm_add_le _ _
  have ht3 : ‖(L1 - a N) + (a N - b N)‖ ≤ ‖L1 - a N‖ + ‖a N - b N‖ := norm_add_le _ _
  have h_triangle : ‖L1 - L2‖ ≤ ‖L1 - a N‖ + ‖a N - b N‖ + ‖b N - L2‖ := by linarith
  
  have h_norm_symm : ‖L1 - a N‖ = ‖a N - L1‖ := norm_sub_rev _ _
  rw [h_norm_symm] at h_triangle
  
  have h_sum : ‖a N - L1‖ + ‖a N - b N‖ + ‖b N - L2‖ < ε := by linarith
  
  have h_lt : ‖L1 - L2‖ < ε := lt_of_le_of_lt h_triangle h_sum
  
  -- The goal is `‖L1 - L2‖ ≤ 0 + ε`, which is `‖L1 - L2‖ ≤ ε`.
  rw [zero_add]
  exact le_of_lt h_lt
}
