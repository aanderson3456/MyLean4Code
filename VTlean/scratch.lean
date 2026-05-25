import Mathlib

open Finset Complex

lemma test_conj_inv (n : Nat) (j : Nat) (ω : ℂ) (hω : IsPrimitiveRoot ω (n + 1)) :
  0 ≤ (∏ k ∈ range n, (1 + (ω ^ j) ^ (k + 1))).re ∧ (∏ k ∈ range n, (1 + (ω ^ j) ^ (k + 1))).im = 0 := by {
  let y := ω ^ j
  have h_norm_y : ‖y‖ = 1 := by {
    dsimp [y]
    rw [norm_pow]
    have h_norm_ω : ‖ω‖ = 1 := hω.norm'_eq_one (by omega)
    rw [h_norm_ω, one_pow]
  }
  have h_star_y : star y = y⁻¹ := by {
    have h_sq2 : ‖y‖ ^ 2 = (1 : ℝ) ^ 2 := by rw [h_norm_y, one_pow]
    change (Real.sqrt (Complex.normSq y)) ^ 2 = (1 : ℝ) ^ 2 at h_sq2
    rw [Real.sq_sqrt (Complex.normSq_nonneg y)] at h_sq2
    simp only [one_pow] at h_sq2
    have h_mul : star y * y = 1 := by {
      apply Complex.ext
      · simp
        exact h_sq2
      · simp
        ring
    }
    exact eq_inv_of_mul_eq_one_left h_mul
  }
  have h_star_term (k : Nat) : star (1 + y ^ (k + 1)) = 1 + (star y) ^ (k + 1) := by {
    have h_ring : star (1 + y ^ (k + 1)) = starRingEnd ℂ (1 + y ^ (k + 1)) := rfl
    rw [h_ring]
    rw [map_add, map_one, map_pow]
    rfl
  }
  have h_eq_term (k : Nat) (hk : k < n) : star (1 + y ^ (k + 1)) = 1 + y ^ (n - k) := by {
    rw [h_star_term, h_star_y]
    congr 1
    rw [inv_pow]
    have h_prod_one : y ^ (n - k) * y ^ (k + 1) = 1 := by {
      rw [← pow_add]
      have : n - k + (k + 1) = n + 1 := by omega
      rw [this]
      dsimp [y]
      rw [← pow_mul, mul_comm, pow_mul]
      have : ω ^ (n + 1) = 1 := hω.pow_eq_one
      rw [this, one_pow]
    }
    exact (eq_inv_of_mul_eq_one_left h_prod_one).symm
  }
  
  let m := n / 2
  let s1 := filter (fun k => k < m) (range n)
  let s2 := filter (fun k => k > n - 1 - m) (range n)
  let s3 := filter (fun k => k >= m ∧ k <= n - 1 - m) (range n)
  
  have h_union : range n = s1 ∪ s2 ∪ s3 := by {
    ext k
    simp only [mem_range, mem_union, mem_filter, s1, s2, s3]
    omega
  }
  have h_disj1 : Disjoint s1 s2 := by {
    rw [disjoint_filter]
    intro k hk
    omega
  }
  have h_disj2 : Disjoint (s1 ∪ s2) s3 := by {
    rw [disjoint_union_left]
    constructor
    · rw [disjoint_filter]
      intro k hk
      omega
    · rw [disjoint_filter]
      intro k hk
      omega
  }
  have h_prod_split : (∏ k ∈ range n, (1 + y ^ (k + 1))) =
    (∏ k ∈ s1, (1 + y ^ (k + 1))) * (∏ k ∈ s2, (1 + y ^ (k + 1))) * (∏ k ∈ s3, (1 + y ^ (k + 1))) := by {
    rw [h_union]
    rw [prod_union h_disj2]
    rw [prod_union h_disj1]
  }
  
  have h_s2_prod : (∏ k ∈ s2, (1 + y ^ (k + 1))) = star (∏ k ∈ s1, (1 + y ^ (k + 1))) := by {
    have h_ring : star (∏ k ∈ s1, (1 + y ^ (k + 1))) = starRingEnd ℂ (∏ k ∈ s1, (1 + y ^ (k + 1))) := rfl
    rw [h_ring]
    rw [map_prod (starRingEnd ℂ)]
    apply prod_bij (fun k _ => n - 1 - k)
    · -- hi
      intro a ha
      rw [mem_filter, mem_range] at ha ⊢
      dsimp only [s1, s2, m] at ha ⊢
      constructor
      · omega
      · omega
    · -- i_inj
      intro a1 ha1 a2 ha2 h_eq
      rw [mem_filter, mem_range] at ha1 ha2
      omega
    · -- i_surj
      intro b hb
      rw [mem_filter, mem_range] at hb
      use n - 1 - b
      have ha2 : n - 1 - b ∈ s2 := by {
        dsimp only [s2, m]
        rw [mem_filter, mem_range]
        omega
      }
      use ha2
      omega
    · -- h
      intro a ha
      rw [mem_filter, mem_range] at ha
      have h_lt : a < n := ha.1
      change 1 + y ^ (a + 1) = star (1 + y ^ (n - 1 - a + 1))
      rw [h_eq_term (n - 1 - a) (by omega)]
      congr 2
      omega
  }
  
  have h_prod_main : (∏ k ∈ s1, (1 + y ^ (k + 1))) * (∏ k ∈ s2, (1 + y ^ (k + 1))) =
    (Complex.normSq (∏ k ∈ s1, (1 + y ^ (k + 1))) : ℂ) := by {
    rw [h_s2_prod]
    exact Complex.mul_conj (∏ k ∈ s1, (1 + y ^ (k + 1)))
  }
  
  have h_s3_val : (∏ k ∈ s3, (1 + y ^ (k + 1))) = if n % 2 = 1 then (1 + y ^ ((n - 1) / 2 + 1)) else 1 := by {
    by_cases hn : n % 2 = 1
    · rw [if_pos hn]
      have h_s3_eq : s3 = {m} := by {
        ext k
        simp only [mem_filter, mem_range, s3, mem_singleton]
        omega
      }
      rw [h_s3_eq]
      rw [prod_singleton]
      have : (n - 1) / 2 = m := by omega
      rw [this]
    · rw [if_neg hn]
      have h_s3_empty : s3 = ∅ := by {
        rw [Finset.eq_empty_iff_forall_notMem]
        intro k
        simp only [s3, m, mem_filter, mem_range, not_and]
        intro hk hk2 hk3
        have h_mod : n % 2 = 0 := by omega
        have h_div : n = 2 * (n / 2) := by {
          have h_div_mod := Nat.div_add_mod n 2
          omega
        }
        omega
      }
      rw [h_s3_empty]
      rw [prod_empty]
  }
  
  have h_s3_nonneg : 0 ≤ (∏ k ∈ s3, (1 + y ^ (k + 1))).re ∧ (∏ k ∈ s3, (1 + y ^ (k + 1))).im = 0 := by {
    rw [h_s3_val]
    split_ifs with hn
    · -- hn : n % 2 = 1
      have h_y_pow : (y ^ ((n - 1) / 2 + 1)) ^ 2 = 1 := by {
        rw [← pow_mul]
        have : ((n - 1) / 2 + 1) * 2 = n + 1 := by omega
        rw [this]
        dsimp [y]
        rw [← pow_mul, mul_comm, pow_mul]
        have : ω ^ (n + 1) = 1 := hω.pow_eq_one
        rw [this, one_pow]
      }
      have h_y_val : y ^ ((n - 1) / 2 + 1) = 1 ∨ y ^ ((n - 1) / 2 + 1) = -1 := by {
        exact sq_eq_one_iff.mp h_y_pow
      }
      rcases h_y_val with h_one | h_neg_one
      · rw [h_one]
        simp
      · rw [h_neg_one]
        simp
    · simp
  }
  
  have h_final : (∏ k ∈ range n, (1 + y ^ (k + 1))) =
    (Complex.normSq (∏ k ∈ s1, (1 + y ^ (k + 1))) : ℂ) * (∏ k ∈ s3, (1 + y ^ (k + 1))) := by {
    rw [h_prod_split, h_prod_main]
  }
  
  have h_normSq_re : (Complex.normSq (∏ k ∈ s1, (1 + y ^ (k + 1))) : ℂ).re =
    Complex.normSq (∏ k ∈ s1, (1 + y ^ (k + 1))) := Complex.ofReal_re _
  have h_normSq_im : (Complex.normSq (∏ k ∈ s1, (1 + y ^ (k + 1))) : ℂ).im = 0 := Complex.ofReal_im _
  
  constructor
  · rw [h_final]
    rw [mul_re]
    rw [h_normSq_re, h_normSq_im, h_s3_nonneg.2]
    simp only [mul_zero, sub_zero]
    have h_norm_nonneg := Complex.normSq_nonneg (∏ k ∈ s1, (1 + y ^ (k + 1)))
    exact mul_nonneg h_norm_nonneg h_s3_nonneg.1
  · rw [h_final]
    rw [mul_im]
    rw [h_normSq_re, h_normSq_im, h_s3_nonneg.2]
    ring
}
