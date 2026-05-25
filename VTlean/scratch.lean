import Mathlib
import VTlean.Cuculiere

open Finset Complex

noncomputable def poly_P (n : Nat) : Polynomial ℂ :=
  (Iic (max_vt_checksum n)).sum (fun c => Polynomial.C (cuculiere_get n c : ℂ) * Polynomial.X ^ c)

lemma poly_P_eval_real_nonneg (n : Nat) (j : Nat) (ω : ℂ) (hω : IsPrimitiveRoot ω (n + 1)) :
  0 ≤ (Polynomial.eval (ω ^ j) (poly_P n)).re ∧ (Polynomial.eval (ω ^ j) (poly_P n)).im = 0 := by {
  sorry
}

lemma roots_unity_filter (n : Nat) (a : Nat) (ω : ℂ) (hω : IsPrimitiveRoot ω (n + 1)) :
  (cuculiere_mod_sum_gen n (n + 1) a : ℂ) =
    (1 / (n + 1 : ℂ)) * (range (n + 1)).sum (fun j => ω ^ (-(a : ℤ) * (j : ℤ)) * Polynomial.eval (ω ^ j) (poly_P n)) := by {
  sorry
}

lemma complex_re_im_le (z : ℂ) (hz : ‖z‖ ≤ 1) (y : ℂ) (hy_re : (0 : ℝ) ≤ y.re) (hy_im : y.im = 0) :
  (z * y).re ≤ y.re := by {
  have h_y : y = (y.re : ℂ) := Complex.ext rfl hy_im
  rw [h_y]
  rw [mul_re]
  simp only [ofReal_im, mul_zero, sub_zero, ofReal_re]
  have hz_re : z.re ≤ 1 := (re_le_norm z).trans hz
  exact mul_le_of_le_one_left hy_re hz_re
}

lemma ω_pow_abs_le (n : Nat) (ω : ℂ) (h : IsPrimitiveRoot ω (n + 1)) (a : Nat) (j : Nat) :
  ‖ω ^ (-(a : ℤ) * (j : ℤ))‖ ≤ 1 := by {
  sorry
}

lemma exists_primitive_root (n : Nat) : ∃ ω : ℂ, IsPrimitiveRoot ω (n + 1) := by {
  sorry
}

lemma cuculiere_mod_sum_gen_max (n : Nat) (a : Nat) :
  cuculiere_mod_sum_gen n (n + 1) a ≤ cuculiere_mod_sum_gen n (n + 1) 0 := by {
  rcases exists_primitive_root n with ⟨ω, hω⟩
  have h_cast_a : (cuculiere_mod_sum_gen n (n + 1) a : ℂ) = (cuculiere_mod_sum_gen n (n + 1) a : Nat) := by simp
  have h_cast_0 : (cuculiere_mod_sum_gen n (n + 1) 0 : ℂ) = (cuculiere_mod_sum_gen n (n + 1) 0 : Nat) := by simp
  
  have h_filter_a := roots_unity_filter n a ω hω
  have h_filter_0 := roots_unity_filter n 0 ω hω
  
  have h_re_a : ((cuculiere_mod_sum_gen n (n + 1) a : ℂ)).re = 
    ((1 / (n + 1 : ℂ)) * (range (n + 1)).sum (fun j => ω ^ (-(a : ℤ) * (j : ℤ)) * Polynomial.eval (ω ^ j) (poly_P n))).re := by {
    rw [← h_filter_a]
  }
  have h_re_0 : ((cuculiere_mod_sum_gen n (n + 1) 0 : ℂ)).re = 
    ((1 / (n + 1 : ℂ)) * (range (n + 1)).sum (fun j => ω ^ (-((0 : ℕ) : ℤ) * (j : ℤ)) * Polynomial.eval (ω ^ j) (poly_P n))).re := by {
    rw [← h_filter_0]
  }
  
  have h_sum_le : 
    ((range (n + 1)).sum (fun j => ω ^ (-(a : ℤ) * (j : ℤ)) * Polynomial.eval (ω ^ j) (poly_P n))).re ≤
    ((range (n + 1)).sum (fun j => ω ^ (-((0 : ℕ) : ℤ) * (j : ℤ)) * Polynomial.eval (ω ^ j) (poly_P n))).re := by {
    have h_re_dist (s : Finset ℕ) (f : ℕ → ℂ) : (∑ x ∈ s, f x).re = ∑ x ∈ s, (f x).re := by {
      exact map_sum reAddGroupHom f s
    }
    rw [h_re_dist, h_re_dist]
    apply sum_le_sum
    intro j hj
    have h_nonneg := poly_P_eval_real_nonneg n j ω hω
    have h_abs := ω_pow_abs_le n ω hω a j
    have h_le := complex_re_im_le (ω ^ (-(a : ℤ) * (j : ℤ))) h_abs (Polynomial.eval (ω ^ j) (poly_P n)) h_nonneg.1 h_nonneg.2
    
    have h_zero : ω ^ (-((0 : ℕ) : ℤ) * (j : ℤ)) = 1 := by {
      have h_zero_exp : -((0 : ℕ) : ℤ) * (j : ℤ) = 0 := by ring
      rw [h_zero_exp, zpow_zero]
    }
    rw [h_zero, one_mul]
    exact h_le
  }
  
  have h_div_le :
    ((1 / (n + 1 : ℂ)) * (range (n + 1)).sum (fun j => ω ^ (-(a : ℤ) * (j : ℤ)) * Polynomial.eval (ω ^ j) (poly_P n))).re ≤
    ((1 / (n + 1 : ℂ)) * (range (n + 1)).sum (fun j => ω ^ (-((0 : ℕ) : ℤ) * (j : ℤ)) * Polynomial.eval (ω ^ j) (poly_P n))).re := by {
    have h_factor : (1 / (n + 1 : ℂ)) = ((1 / (n + 1 : ℝ) : ℝ) : ℂ) := by {
      push_cast
      rfl
    }
    rw [h_factor, mul_re, mul_re]
    simp only [ofReal_im, zero_mul, sub_zero, ofReal_re]
    have h_div_pos : 0 ≤ 1 / ((n : ℝ) + 1) := by {
      have h1 : 0 ≤ (n : ℝ) + 1 := by linarith
      exact div_nonneg (by linarith) h1
    }
    exact mul_le_mul_of_nonneg_left h_sum_le h_div_pos
  }
  
  rw [← h_re_a, ← h_re_0] at h_div_le
  exact Nat.cast_le.mp h_div_le
}
