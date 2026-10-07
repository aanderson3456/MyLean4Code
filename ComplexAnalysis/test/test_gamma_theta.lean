import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import R2

open ComplexAnalysis.R2

lemma cos_sub_one_bound (x : ℝ) : |Real.cos x - 1| ≤ x^2 / 2 := by
{
  have h1 : 1 - x^2 / 2 ≤ Real.cos x := Real.one_sub_sq_div_two_le_cos
  have h2 : Real.cos x ≤ 1 := Real.cos_le_one x
  have h3 : Real.cos x - 1 ≤ 0 := by linarith
  have h4 : Real.cos x - 1 ≥ -(x^2 / 2) := by linarith
  exact abs_le.mpr ⟨by linarith, by linarith⟩
}

lemma sin_sub_id_bound_pos {x : ℝ} (hx : 0 ≤ x) (h_bound : x ≤ 1) : |Real.sin x - x| ≤ x^3 / 4 := by
{
  by_cases h0 : x = 0
  · rw [h0]
    norm_num
  · have hx_pos : 0 < x := lt_of_le_of_ne hx (Ne.symm h0)
    have h1 : x - x^3 / 4 < Real.sin x := Real.sin_gt_sub_cube hx_pos h_bound
    have h2 : Real.sin x ≤ x := Real.sin_le hx
    exact abs_le.mpr ⟨by linarith, by linarith⟩
}

lemma sin_sub_id_bound {x : ℝ} (hx : |x| ≤ 1) : |Real.sin x - x| ≤ |x|^3 / 4 := by
{
  by_cases hpos : 0 ≤ x
  · have h1 : x = |x| := by exact abs_of_nonneg hpos |>.symm
    rw [← h1]
    have h2 : x ≤ 1 := by
    {
      have h3 : x = |x| := by exact abs_of_nonneg hpos |>.symm
      rw [h3]
      exact hx
    }
    exact sin_sub_id_bound_pos hpos h2
  · have hneg : 0 ≤ -x := by linarith
    have h1 : -x = |x| := by
    {
      exact abs_of_neg (not_le.mp hpos) |>.symm
    }
    have h2 : -x ≤ 1 := by
    {
      rw [h1]
      exact hx
    }
    have h3 := sin_sub_id_bound_pos hneg h2
    have h4 : Real.sin (-x) - (-x) = -(Real.sin x - x) := by
    {
      rw [Real.sin_neg]
      ring
    }
    rw [h4, abs_neg] at h3
    rw [← h1]
    exact h3
}

lemma gamma_theta_diff {r₀ θ₀ : ℝ} : 
    HasDerivAt_RtoR2_eps (fun θ => (r₀ * Real.cos θ, r₀ * Real.sin θ)) 
      (-r₀ * Real.sin θ₀, r₀ * Real.cos θ₀) θ₀ := by
{
  unfold HasDerivAt_RtoR2_eps
  intro ε hε
  let M := |r₀| * (3 / 4)
  use min 1 (ε / (M + 1))
  have hM_nonneg : 0 ≤ M := by
  {
    dsimp [M]
    have h_abs : 0 ≤ |r₀| := abs_nonneg _
    linarith
  }
  have h_min_pos : 0 < min 1 (ε / (M + 1)) := by
  {
    apply lt_min
    · exact by norm_num
    · have hM1 : 0 < M + 1 := by linarith
      exact div_pos hε hM1
  }
  use h_min_pos
  intro t ht
  have ht1 : |t - θ₀| < 1 := lt_of_lt_of_le ht.2 (min_le_left _ _)
  have ht2 : |t - θ₀| < ε / (M + 1) := lt_of_lt_of_le ht.2 (min_le_right _ _)
  
  let h := t - θ₀
  have hh_eq : t = θ₀ + h := by
  { dsimp [h]; ring }
  
  have h_target : euclideanDist ((fun θ => (r₀ * Real.cos θ, r₀ * Real.sin θ)) t)
      ((fun θ => (r₀ * Real.cos θ, r₀ * Real.sin θ)) θ₀ +
        ((-r₀ * Real.sin θ₀, r₀ * Real.cos θ₀).1 * (t - θ₀),
          (-r₀ * Real.sin θ₀, r₀ * Real.cos θ₀).2 * (t - θ₀))) = 
      euclideanDist (r₀ * Real.cos (θ₀ + h), r₀ * Real.sin (θ₀ + h))
      ((r₀ * Real.cos θ₀, r₀ * Real.sin θ₀) + (-r₀ * Real.sin θ₀ * h, r₀ * Real.cos θ₀ * h)) := by
  {
    dsimp
    congr 2
    · rw [hh_eq]
    · rw [hh_eq]
  }
  rw [h_target]

  have h_dist : euclideanDist (r₀ * Real.cos (θ₀ + h), r₀ * Real.sin (θ₀ + h))
      ((r₀ * Real.cos θ₀, r₀ * Real.sin θ₀) + (-r₀ * Real.sin θ₀ * h, r₀ * Real.cos θ₀ * h)) =
      euclideanNorm (
        r₀ * (Real.cos (θ₀ + h) - Real.cos θ₀ + h * Real.sin θ₀),
        r₀ * (Real.sin (θ₀ + h) - Real.sin θ₀ - h * Real.cos θ₀)
      ) := by
  {
    unfold euclideanDist sqDist euclideanNorm sqNorm
    congr 1
    have h1 : r₀ * Real.cos (θ₀ + h) - ((r₀ * Real.cos θ₀, r₀ * Real.sin θ₀) + (-r₀ * Real.sin θ₀ * h, r₀ * Real.cos θ₀ * h)).1 = r₀ * (Real.cos (θ₀ + h) - Real.cos θ₀ + h * Real.sin θ₀) := by
    {
      dsimp
      ring
    }
    have h2 : r₀ * Real.sin (θ₀ + h) - ((r₀ * Real.cos θ₀, r₀ * Real.sin θ₀) + (-r₀ * Real.sin θ₀ * h, r₀ * Real.cos θ₀ * h)).2 = r₀ * (Real.sin (θ₀ + h) - Real.sin θ₀ - h * Real.cos θ₀) := by
    {
      dsimp
      ring
    }
    rw [h1, h2]
  }
  rw [h_dist]

  have h_cos_add : Real.cos (θ₀ + h) = Real.cos θ₀ * Real.cos h - Real.sin θ₀ * Real.sin h := Real.cos_add θ₀ h
  have h_sin_add : Real.sin (θ₀ + h) = Real.sin θ₀ * Real.cos h + Real.cos θ₀ * Real.sin h := Real.sin_add θ₀ h
  
  have h_comp1 : r₀ * (Real.cos (θ₀ + h) - Real.cos θ₀ + h * Real.sin θ₀) = r₀ * Real.cos θ₀ * (Real.cos h - 1) - r₀ * Real.sin θ₀ * (Real.sin h - h) := by
  {
    rw [h_cos_add]
    ring
  }
  
  have h_comp2 : r₀ * (Real.sin (θ₀ + h) - Real.sin θ₀ - h * Real.cos θ₀) = r₀ * Real.sin θ₀ * (Real.cos h - 1) + r₀ * Real.cos θ₀ * (Real.sin h - h) := by
  {
    rw [h_sin_add]
    ring
  }
  
  rw [h_comp1, h_comp2]
  
  have h_norm_eq : euclideanNorm (r₀ * Real.cos θ₀ * (Real.cos h - 1) - r₀ * Real.sin θ₀ * (Real.sin h - h), r₀ * Real.sin θ₀ * (Real.cos h - 1) + r₀ * Real.cos θ₀ * (Real.sin h - h)) =
      euclideanNorm (r₀ * (Real.cos h - 1), r₀ * (Real.sin h - h)) := by
  {
    unfold euclideanNorm sqNorm
    congr 1
    calc
      (r₀ * Real.cos θ₀ * (Real.cos h - 1) - r₀ * Real.sin θ₀ * (Real.sin h - h))^2 + (r₀ * Real.sin θ₀ * (Real.cos h - 1) + r₀ * Real.cos θ₀ * (Real.sin h - h))^2
      = (r₀ * (Real.cos h - 1))^2 * Real.cos θ₀^2 + (r₀ * (Real.sin h - h))^2 * Real.sin θ₀^2
        - 2 * (r₀ * Real.cos θ₀ * (Real.cos h - 1)) * (r₀ * Real.sin θ₀ * (Real.sin h - h))
        + (r₀ * (Real.cos h - 1))^2 * Real.sin θ₀^2 + (r₀ * (Real.sin h - h))^2 * Real.cos θ₀^2
        + 2 * (r₀ * Real.sin θ₀ * (Real.cos h - 1)) * (r₀ * Real.cos θ₀ * (Real.sin h - h)) := by ring
      _ = (r₀ * (Real.cos h - 1))^2 * (Real.cos θ₀^2 + Real.sin θ₀^2) + (r₀ * (Real.sin h - h))^2 * (Real.sin θ₀^2 + Real.cos θ₀^2) := by ring
      _ = (r₀ * (Real.cos h - 1))^2 * 1 + (r₀ * (Real.sin h - h))^2 * 1 := by
      {
        rw [Real.cos_sq_add_sin_sq θ₀]
        have h_add2 : Real.sin θ₀^2 + Real.cos θ₀^2 = 1 := by
        {
          rw [add_comm]
          exact Real.cos_sq_add_sin_sq θ₀
        }
        rw [h_add2]
      }
      _ = (r₀ * (Real.cos h - 1))^2 + (r₀ * (Real.sin h - h))^2 := by ring
  }
  rw [h_norm_eq]
  
  let A := r₀ * (Real.cos h - 1)
  let B := r₀ * (Real.sin h - h)
  
  have h_norm_le : euclideanNorm (A, B) ≤ |A| + |B| := by
  {
    unfold euclideanNorm sqNorm
    have h2 : A^2 + B^2 ≤ (|A| + |B|)^2 := by
    {
      have h3 : (|A| + |B|)^2 = |A|^2 + |B|^2 + 2 * |A| * |B| := by ring
      have h4 : A^2 = |A|^2 := by exact sq_abs A |>.symm
      have h5 : B^2 = |B|^2 := by exact sq_abs B |>.symm
      rw [h3, ←h4, ←h5]
      have h6 : 0 ≤ 2 * |A| * |B| := mul_nonneg (mul_nonneg (by norm_num) (abs_nonneg A)) (abs_nonneg B)
      linarith
    }
    have h_sqrt : Real.sqrt (A^2 + B^2) ≤ Real.sqrt ((|A| + |B|)^2) := Real.sqrt_le_sqrt h2
    have h_abs_add : Real.sqrt ((|A| + |B|)^2) = |A| + |B| := Real.sqrt_sq (add_nonneg (abs_nonneg A) (abs_nonneg B))
    rw [h_abs_add] at h_sqrt
    exact h_sqrt
  }
  
  have h_abs1 : |A| = |r₀| * |Real.cos h - 1| := abs_mul r₀ _
  have h_abs2 : |B| = |r₀| * |Real.sin h - h| := abs_mul r₀ _
  rw [h_abs1, h_abs2] at h_norm_le
  
  have hh_le1 : |h| ≤ 1 := by
  {
    dsimp [h]
    exact le_of_lt ht1
  }
  have h_cos_b := cos_sub_one_bound h
  have h_sin_b := sin_sub_id_bound hh_le1
  
  have h_sum_le : |r₀| * |Real.cos h - 1| + |r₀| * |Real.sin h - h| ≤ |r₀| * (h^2 / 2) + |r₀| * (|h|^3 / 4) := by
  {
    have h_le1 : |r₀| * |Real.cos h - 1| ≤ |r₀| * (h^2 / 2) := mul_le_mul_of_nonneg_left h_cos_b (abs_nonneg _)
    have h_le2 : |r₀| * |Real.sin h - h| ≤ |r₀| * (|h|^3 / 4) := mul_le_mul_of_nonneg_left h_sin_b (abs_nonneg _)
    exact add_le_add h_le1 h_le2
  }
  
  have h_sq_le : h^2 / 2 ≤ |h|^2 / 2 := by
  {
    have h1 : h^2 = |h|^2 := by exact sq_abs h |>.symm
    rw [h1]
  }
  
  have h_sum_le2 : |r₀| * (h^2 / 2) + |r₀| * (|h|^3 / 4) ≤ |r₀| * (|h|^2 / 2) + |r₀| * (|h|^3 / 4) := by
  {
    have h_le1 : |r₀| * (h^2 / 2) ≤ |r₀| * (|h|^2 / 2) := mul_le_mul_of_nonneg_left h_sq_le (abs_nonneg _)
    exact add_le_add h_le1 (le_refl _)
  }
  
  have h_sum_le3 : |r₀| * (|h|^2 / 2) + |r₀| * (|h|^3 / 4) ≤ |r₀| * (|h|^2 / 2) + |r₀| * (|h|^2 / 4) := by
  {
    have h_cub_le : |h|^3 / 4 ≤ |h|^2 / 4 := by
    {
      have h1 : |h|^3 = |h|^2 * |h| := by ring
      rw [h1]
      have h2 : |h|^2 * |h| ≤ |h|^2 * 1 := mul_le_mul_of_nonneg_left hh_le1 (sq_nonneg _)
      have h3 : |h|^2 * 1 = |h|^2 := by ring
      rw [h3] at h2
      linarith
    }
    have h_le2 : |r₀| * (|h|^3 / 4) ≤ |r₀| * (|h|^2 / 4) := mul_le_mul_of_nonneg_left h_cub_le (abs_nonneg _)
    exact add_le_add (le_refl _) h_le2
  }
  
  have h_sum_eq : |r₀| * (|h|^2 / 2) + |r₀| * (|h|^2 / 4) = M * |h|^2 := by
  {
    dsimp [M]
    ring
  }
  
  have h_total_le : euclideanNorm (A, B) ≤ M * |h|^2 := by
  {
    calc
      euclideanNorm (A, B) ≤ |r₀| * |Real.cos h - 1| + |r₀| * |Real.sin h - h| := h_norm_le
      _ ≤ |r₀| * (h^2 / 2) + |r₀| * (|h|^3 / 4) := h_sum_le
      _ ≤ |r₀| * (|h|^2 / 2) + |r₀| * (|h|^3 / 4) := h_sum_le2
      _ ≤ |r₀| * (|h|^2 / 2) + |r₀| * (|h|^2 / 4) := h_sum_le3
      _ = M * |h|^2 := h_sum_eq
  }
  
  have h_strict_lt : M * |h|^2 < ε * |t - θ₀| := by
  {
    have h_h_pos : 0 < |h| := ht.1
    have h_t_eq : |t - θ₀| = |h| := by rfl
    rw [h_t_eq]
    
    have h_M_bound : M * |h| < ε := by
    {
      have h1 : ε / (M + 1) * (M + 1) = ε := div_mul_cancel₀ ε (ne_of_gt (by linarith))
      have h2 : |h| < ε / (M + 1) := ht2
      have h3 : M * |h| ≤ M * (ε / (M + 1)) := mul_le_mul_of_nonneg_left (le_of_lt h2) hM_nonneg
      have h4 : M * (ε / (M + 1)) < ε := by
      {
        have h5 : M * (ε / (M + 1)) = (M / (M + 1)) * ε := by ring
        rw [h5]
        have h6 : M / (M + 1) < 1 := by
        {
          have h7 : 0 < M + 1 := by linarith
          exact (div_lt_one h7).mpr (by linarith)
        }
        have h8 : (M / (M + 1)) * ε < 1 * ε := mul_lt_mul_of_pos_right h6 hε
        have h9 : 1 * ε = ε := by ring
        rw [h9] at h8
        exact h8
      }
      exact lt_of_le_of_lt h3 h4
    }
    
    have h_mul : M * |h|^2 = (M * |h|) * |h| := by ring
    rw [h_mul]
    exact mul_lt_mul_of_pos_right h_M_bound h_h_pos
  }
  
  have ht_eq_h : |t - θ₀| = |h| := rfl
  exact lt_of_le_of_lt h_total_le h_strict_lt
}
