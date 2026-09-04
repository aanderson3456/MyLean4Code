import Mathlib.Topology.Basic
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Normed.Group.Basic
import Mathlib.Analysis.Real.Sqrt

namespace ComplexAnalysis.R2
open Complex

noncomputable def sqNorm (x : ℝ × ℝ) : ℝ := x.1^2 + x.2^2

noncomputable def sqDist (x y : ℝ × ℝ) : ℝ :=
  (x.1 - y.1)^2 + (x.2 - y.2)^2

noncomputable def euclideanNorm (x : ℝ × ℝ) : ℝ :=
  Real.sqrt (sqNorm x)

noncomputable def euclideanDist (x y : ℝ × ℝ) : ℝ :=
  Real.sqrt (sqDist x y)

def LimitRtoR2 (f : ℝ → ℝ × ℝ) (a : ℝ) (L : ℝ × ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ, 0 < |x - a| ∧ |x - a| < δ → euclideanDist (f x) L < ε

def LimitR2toR (f : ℝ × ℝ → ℝ) (a : ℝ × ℝ) (L : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ × ℝ, 0 < euclideanDist x a ∧ euclideanDist x a < δ → |f x - L| < ε

def LimitR2toR2 (f : ℝ × ℝ → ℝ × ℝ) (a : ℝ × ℝ) (L : ℝ × ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ × ℝ, 0 < euclideanDist x a ∧ euclideanDist x a < δ → euclideanDist (f x) L < ε

def ConvergesR2 (seq : ℕ → ℝ × ℝ) (L : ℝ × ℝ): Prop :=
  ∀ ε > 0, ∃ N : ℕ, ∀ n ≥ N, euclideanDist (seq n) L < ε

def HasFDerivAt_R2_eps (u v : ℝ × ℝ → ℝ) (ux uy vx vy : ℝ) (a : ℝ × ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ x : ℝ × ℝ,
    0 < euclideanDist x a ∧ euclideanDist x a < δ →
    let dx := x.1 - a.1
    let dy := x.2 - a.2
    let Ldx := ux * dx + uy * dy
    let Ldy := vx * dx + vy * dy
    let err_x := u x - u a - Ldx
    let err_y := v x - v a - Ldy
    euclideanNorm (err_x, err_y) < ε * euclideanDist x a

def DifferentiableAt_R2_eps (u v : ℝ × ℝ → ℝ) (a : ℝ × ℝ) : Prop :=
  ∃ (ux uy vx vy : ℝ), HasFDerivAt_R2_eps u v ux uy vx vy a

def HasDerivAt_RtoR2_eps (f : ℝ → ℝ × ℝ) (f' : ℝ × ℝ) (t₀ : ℝ) : Prop :=
  ∀ ε > 0, ∃ δ > 0, ∀ t : ℝ, 0 < |t - t₀| ∧ |t - t₀| < δ →
    euclideanDist (f t) (f t₀ + (f'.1 * (t - t₀), f'.2 * (t - t₀))) < ε * |t - t₀|

lemma euclideanNorm_eq_norm (x : ℝ × ℝ) :
  euclideanNorm x = ‖Complex.mk x.1 x.2‖ := by {
  unfold euclideanNorm sqNorm
  have h_norm : ‖Complex.mk x.1 x.2‖ = Real.sqrt (x.1^2 + x.2^2) := by {
    rw [Complex.norm_def]
    unfold normSq
    dsimp
    congr 1
    ring
  }
  rw [h_norm]
}

lemma euclideanNormTriangle (x y : ℝ × ℝ) :
  euclideanNorm (x.1 + y.1, x.2 + y.2) ≤ euclideanNorm x + euclideanNorm y := by {
  rw [euclideanNorm_eq_norm, euclideanNorm_eq_norm x, euclideanNorm_eq_norm y]
  have h_add : Complex.mk (x.1 + y.1) (x.2 + y.2) = Complex.mk x.1 x.2 + Complex.mk y.1 y.2 := by {
    apply Complex.ext <;> simp
  }
  rw [h_add]
  exact norm_add_le (Complex.mk x.1 x.2) (Complex.mk y.1 y.2)
}

lemma euclideanDistTriangle (x y z : ℝ × ℝ) :
    euclideanDist x z ≤ euclideanDist x y + euclideanDist y z := by {
  unfold euclideanDist sqDist
  have h1 : x.1 - z.1 = x.1 - y.1 + (y.1 - z.1) := by ring
  have h2 : x.2 - z.2 = x.2 - y.2 + (y.2 - z.2) := by ring
  have h_norm := euclideanNormTriangle (x.1 - y.1, x.2 - y.2) (y.1 - z.1, y.2 - z.2)
  unfold euclideanNorm sqNorm at h_norm
  dsimp at h_norm
  rw [h1, h2]
  exact h_norm
}

lemma euclideanDist_nonneg (x y : ℝ × ℝ) : 0 ≤ euclideanDist x y := by {
  unfold euclideanDist sqDist
  exact Real.sqrt_nonneg _
}

lemma locally_lipschitz_of_hasDerivAt_RtoR2_eps {γ : ℝ → ℝ × ℝ} {γ' : ℝ × ℝ} {t₀ : ℝ}
    (hγ_diff : HasDerivAt_RtoR2_eps γ γ' t₀) :
    ∃ K > 0, ∃ δ > 0, ∀ t : ℝ, |t - t₀| < δ →
      euclideanDist (γ t) (γ t₀) ≤ K * |t - t₀| := by {
  unfold HasDerivAt_RtoR2_eps at hγ_diff
  have h1 := hγ_diff 1 (by norm_num)
  rcases h1 with ⟨δ, hδ_pos, hδ⟩
  
  -- We'll use K = euclideanNorm γ' + 1
  set K := euclideanNorm γ' + 1
  have hK_pos : K > 0 := by {
    have h_norm_nonneg : 0 ≤ euclideanNorm γ' := by {
      unfold euclideanNorm sqNorm
      exact Real.sqrt_nonneg _
    }
    linarith
  }
  
  use K, hK_pos, δ, hδ_pos
  intro t ht
  
  by_cases ht_eq : t = t₀
  · rw [ht_eq]
    have h_dist_0 : euclideanDist (γ t₀) (γ t₀) = 0 := by {
      unfold euclideanDist sqDist
      simp
    }
    rw [h_dist_0, sub_self, abs_zero, mul_zero]
  
  · have ht_pos : 0 < |t - t₀| := abs_pos.mpr (sub_ne_zero.mpr ht_eq)
    have h_bound := hδ t ⟨ht_pos, ht⟩
    
    have h_triangle : euclideanDist (γ t) (γ t₀) ≤ euclideanDist (γ t) (γ t₀ + (γ'.1 * (t - t₀), γ'.2 * (t - t₀))) + euclideanDist (γ t₀ + (γ'.1 * (t - t₀), γ'.2 * (t - t₀))) (γ t₀) := euclideanDistTriangle _ _ _
    
    have h_dist_L : euclideanDist (γ t₀ + (γ'.1 * (t - t₀), γ'.2 * (t - t₀))) (γ t₀) = euclideanNorm γ' * |t - t₀| := by {
      unfold euclideanDist sqDist euclideanNorm sqNorm
      dsimp
      have h1 : (γ t₀).1 + γ'.1 * (t - t₀) - (γ t₀).1 = γ'.1 * (t - t₀) := by ring
      have h2 : (γ t₀).2 + γ'.2 * (t - t₀) - (γ t₀).2 = γ'.2 * (t - t₀) := by ring
      rw [h1, h2]
      have h3 : (γ'.1 * (t - t₀))^2 = γ'.1^2 * (t - t₀)^2 := by ring
      have h4 : (γ'.2 * (t - t₀))^2 = γ'.2^2 * (t - t₀)^2 := by ring
      rw [h3, h4]
      have h5 : γ'.1^2 * (t - t₀)^2 + γ'.2^2 * (t - t₀)^2 = (γ'.1^2 + γ'.2^2) * (t - t₀)^2 := by ring
      rw [h5]
      rw [Real.sqrt_mul (by positivity)]
      rw [Real.sqrt_sq_eq_abs]
    }
    
    have h_bound2 : euclideanDist (γ t) (γ t₀ + (γ'.1 * (t - t₀), γ'.2 * (t - t₀))) + euclideanDist (γ t₀ + (γ'.1 * (t - t₀), γ'.2 * (t - t₀))) (γ t₀) < 1 * |t - t₀| + euclideanNorm γ' * |t - t₀| := by {
      rw [h_dist_L]
      linarith
    }
    
    have h_bound3 : 1 * |t - t₀| + euclideanNorm γ' * |t - t₀| = K * |t - t₀| := by {
      calc 1 * |t - t₀| + euclideanNorm γ' * |t - t₀|
        _ = (1 + euclideanNorm γ') * |t - t₀| := by ring
        _ = K * |t - t₀| := by {
          congr 1
          change 1 + euclideanNorm γ' = euclideanNorm γ' + 1
          ring
        }
    }
    
    rw [h_bound3] at h_bound2
    exact le_of_lt (lt_of_le_of_lt h_triangle h_bound2)
}

lemma abs_le_euclideanNorm_1 (x y : ℝ) : |x| ≤ euclideanNorm (x, y) := by {
  unfold euclideanNorm sqNorm
  have h1 : x^2 ≤ x^2 + y^2 := by {
    have h_y_sq : 0 ≤ y^2 := sq_nonneg y
    linarith
  }
  have h2 : Real.sqrt (x^2) ≤ Real.sqrt (x^2 + y^2) := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq_eq_abs] at h2
  exact h2
}

lemma abs_le_euclideanNorm_2 (x y : ℝ) : |y| ≤ euclideanNorm (x, y) := by {
  unfold euclideanNorm sqNorm
  have h1 : y^2 ≤ x^2 + y^2 := by {
    have h_x_sq : 0 ≤ x^2 := sq_nonneg x
    linarith
  }
  have h2 : Real.sqrt (y^2) ≤ Real.sqrt (x^2 + y^2) := Real.sqrt_le_sqrt h1
  rw [Real.sqrt_sq_eq_abs] at h2
  exact h2
}

lemma euclideanNorm_le_abs_add (x y : ℝ) : euclideanNorm (x, y) ≤ |x| + |y| := by {
  unfold euclideanNorm sqNorm
  have h1 : x^2 + y^2 ≤ (|x| + |y|)^2 := by {
    have h_expand : (|x| + |y|)^2 = |x|^2 + 2 * |x| * |y| + |y|^2 := by ring
    have h_x_sq : |x|^2 = x^2 := sq_abs x
    have h_y_sq : |y|^2 = y^2 := sq_abs y
    rw [h_expand, h_x_sq, h_y_sq]
    have h_nonneg : 0 ≤ 2 * |x| * |y| := by positivity
    linarith
  }
  have h2 : Real.sqrt (x^2 + y^2) ≤ Real.sqrt ((|x| + |y|)^2) := Real.sqrt_le_sqrt h1
  have h_abs_nonneg : 0 ≤ |x| + |y| := by positivity
  rw [Real.sqrt_sq h_abs_nonneg] at h2
  exact h2
}

lemma matrix_bound (ux uy vx vy x y : ℝ) :
  euclideanNorm (ux * x + uy * y, vx * x + vy * y) ≤ 
  (|ux| + |uy| + |vx| + |vy|) * euclideanNorm (x, y) := by {
  have h1 := euclideanNorm_le_abs_add (ux * x + uy * y) (vx * x + vy * y)
  have h2 : |ux * x + uy * y| ≤ |ux * x| + |uy * y| := abs_add_le _ _
  have h3 : |vx * x + vy * y| ≤ |vx * x| + |vy * y| := abs_add_le _ _
  have h_mul1 : |ux * x| = |ux| * |x| := abs_mul _ _
  have h_mul2 : |uy * y| = |uy| * |y| := abs_mul _ _
  have h_mul3 : |vx * x| = |vx| * |x| := abs_mul _ _
  have h_mul4 : |vy * y| = |vy| * |y| := abs_mul _ _
  rw [h_mul1, h_mul2] at h2
  rw [h_mul3, h_mul4] at h3
  
  have hx_le := abs_le_euclideanNorm_1 x y
  have hy_le := abs_le_euclideanNorm_2 x y
  
  have h_term1 : |ux| * |x| ≤ |ux| * euclideanNorm (x, y) := mul_le_mul_of_nonneg_left hx_le (abs_nonneg _)
  have h_term2 : |uy| * |y| ≤ |uy| * euclideanNorm (x, y) := mul_le_mul_of_nonneg_left hy_le (abs_nonneg _)
  have h_term3 : |vx| * |x| ≤ |vx| * euclideanNorm (x, y) := mul_le_mul_of_nonneg_left hx_le (abs_nonneg _)
  have h_term4 : |vy| * |y| ≤ |vy| * euclideanNorm (x, y) := mul_le_mul_of_nonneg_left hy_le (abs_nonneg _)
  
  have h_sum_le : |ux * x + uy * y| + |vx * x + vy * y| ≤ |ux| * euclideanNorm (x, y) + |uy| * euclideanNorm (x, y) + |vx| * euclideanNorm (x, y) + |vy| * euclideanNorm (x, y) := by {
    linarith
  }
  
  have h_distrib : |ux| * euclideanNorm (x, y) + |uy| * euclideanNorm (x, y) + |vx| * euclideanNorm (x, y) + |vy| * euclideanNorm (x, y) = (|ux| + |uy| + |vx| + |vy|) * euclideanNorm (x, y) := by ring
  rw [h_distrib] at h_sum_le
  
  exact le_trans h1 h_sum_le
}

lemma chain_rule_R2 {u v : ℝ × ℝ → ℝ} {ux uy vx vy : ℝ} {a : ℝ × ℝ}
    (h_diff : HasFDerivAt_R2_eps u v ux uy vx vy a)
    (γ : ℝ → ℝ × ℝ) (t₀ : ℝ) (hγ_a : γ t₀ = a)
    (γ' : ℝ × ℝ) (hγ_diff : HasDerivAt_RtoR2_eps γ γ' t₀) :
    HasDerivAt_RtoR2_eps (fun t => (u (γ t), v (γ t))) 
      (ux * γ'.1 + uy * γ'.2, vx * γ'.1 + vy * γ'.2) t₀ := by {
  unfold HasDerivAt_RtoR2_eps at *
  intro ε hε
  
  -- The matrix operator norm is M.
  set M := |ux| + |uy| + |vx| + |vy| + 1
  have hM_pos : M > 0 := by {
    have h1 : 0 ≤ |ux| + |uy| + |vx| + |vy| := by positivity
    linarith
  }
  
  -- K is the Lipschitz constant of γ near t₀.
  have h_lip := locally_lipschitz_of_hasDerivAt_RtoR2_eps hγ_diff
  rcases h_lip with ⟨K, hK_pos, δ_lip, hδ_lip_pos, hδ_lip⟩
  
  -- We'll split ε into ε / (2 * K) for u, v and ε / (2 * M) for γ.
  have hε1_pos : ε / (2 * K) > 0 := div_pos hε (mul_pos (by norm_num) hK_pos)
  have hε2_pos : ε / (2 * M) > 0 := div_pos hε (mul_pos (by norm_num) hM_pos)
  
  unfold HasFDerivAt_R2_eps at h_diff
  rcases h_diff (ε / (2 * K)) hε1_pos with ⟨δ1, hδ1_pos, hδ1⟩
  rcases hγ_diff (ε / (2 * M)) hε2_pos with ⟨δ2, hδ2_pos, hδ2⟩
  
  -- We also need δ so that K * |t - t₀| < δ1. Let δ3 = δ1 / K.
  set δ3 := δ1 / K
  have hδ3_pos : δ3 > 0 := div_pos hδ1_pos hK_pos
  
  -- Our final δ is the min of δ_lip, δ2, and δ3.
  set δ := min (min δ_lip δ2) δ3
  have hδ_pos : δ > 0 := lt_min (lt_min hδ_lip_pos hδ2_pos) hδ3_pos
  
  use δ, hδ_pos
  intro t ht
  
  have h_target : euclideanDist ((fun t => (u (γ t), v (γ t))) t)
      ((fun t => (u (γ t), v (γ t))) t₀ +
        ((ux * γ'.1 + uy * γ'.2, vx * γ'.1 + vy * γ'.2).1 * (t - t₀),
          (ux * γ'.1 + uy * γ'.2, vx * γ'.1 + vy * γ'.2).2 * (t - t₀))) = 
      euclideanDist (u (γ t), v (γ t)) (u a + (ux * γ'.1 + uy * γ'.2) * (t - t₀), v a + (vx * γ'.1 + vy * γ'.2) * (t - t₀)) := by {
    dsimp
    rw [hγ_a]
  }
  rw [h_target]
  
  have ht_lip : |t - t₀| < δ_lip := by {
    have h1 : δ ≤ min δ_lip δ2 := min_le_left _ _
    have h2 : min δ_lip δ2 ≤ δ_lip := min_le_left _ _
    linarith
  }
  have ht2 : |t - t₀| < δ2 := by {
    have h1 : δ ≤ min δ_lip δ2 := min_le_left _ _
    have h2 : min δ_lip δ2 ≤ δ2 := min_le_right _ _
    linarith
  }
  have ht3 : |t - t₀| < δ3 := by {
    have h1 : δ ≤ δ3 := min_le_right _ _
    linarith
  }
  
  have h_lip_bound := hδ_lip t ht_lip
  have h_γ_bound := hδ2 t ⟨ht.1, ht2⟩
  
  -- error terms
  set err_γ := (γ t).1 - ((γ t₀).1 + γ'.1 * (t - t₀))
  set err_γ_2 := (γ t).2 - ((γ t₀).2 + γ'.2 * (t - t₀))
  
  -- The linear terms in γ error 
  have h_err_γ : err_γ = (γ t).1 - a.1 - γ'.1 * (t - t₀) := by { dsimp [err_γ]; rw [hγ_a]; ring }
  have h_err_γ_2 : err_γ_2 = (γ t).2 - a.2 - γ'.2 * (t - t₀) := by { dsimp [err_γ_2]; rw [hγ_a]; ring }
  
  have h_γ_diff_norm : euclideanNorm (err_γ, err_γ_2) = euclideanDist (γ t) (γ t₀ + (γ'.1 * (t - t₀), γ'.2 * (t - t₀))) := by {
    unfold euclideanDist sqDist euclideanNorm sqNorm
    dsimp
  }
  
  have h_γ_bound2 : euclideanNorm (err_γ, err_γ_2) < (ε / (2 * M)) * |t - t₀| := by {
    rw [h_γ_diff_norm]
    exact h_γ_bound
  }
  
  -- We split into two cases: γ t = a and γ t ≠ a.
  by_cases h_dist_0 : euclideanDist (γ t) (γ t₀) = 0
  · -- If γ t = γ t₀, then γ t = a.
    have h_γ_eq : γ t = a := by {
      have h1 : euclideanDist (γ t) (γ t₀) = 0 := h_dist_0
      unfold euclideanDist sqDist at h1
      rw [Real.sqrt_eq_zero] at h1
      · have h2 : (γ t).1 - (γ t₀).1 = 0 := by {
          have h_sq1 : 0 ≤ ((γ t).1 - (γ t₀).1)^2 := sq_nonneg _
          have h_sq2 : 0 ≤ ((γ t).2 - (γ t₀).2)^2 := sq_nonneg _
          have h3 : ((γ t).1 - (γ t₀).1)^2 = 0 := by linarith
          exact sq_eq_zero_iff.mp h3
        }
        have h3 : (γ t).2 - (γ t₀).2 = 0 := by {
          have h_sq1 : 0 ≤ ((γ t).1 - (γ t₀).1)^2 := sq_nonneg _
          have h_sq2 : 0 ≤ ((γ t).2 - (γ t₀).2)^2 := sq_nonneg _
          have h3 : ((γ t).2 - (γ t₀).2)^2 = 0 := by linarith
          exact sq_eq_zero_iff.mp h3
        }
        ext
        · exact sub_eq_zero.mp h2 ▸ (congrArg Prod.fst hγ_a)
        · exact sub_eq_zero.mp h3 ▸ (congrArg Prod.snd hγ_a)
      · positivity
    }
    have h_u_eq : u (γ t) = u a := by rw [h_γ_eq]
    have h_v_eq : v (γ t) = v a := by rw [h_γ_eq]
    
    have h_total_norm : euclideanDist (u (γ t), v (γ t)) (u a + (ux * γ'.1 + uy * γ'.2) * (t - t₀), v a + (vx * γ'.1 + vy * γ'.2) * (t - t₀)) = euclideanNorm (-(ux * γ'.1 + uy * γ'.2) * (t - t₀), -(vx * γ'.1 + vy * γ'.2) * (t - t₀)) := by {
      unfold euclideanDist sqDist euclideanNorm sqNorm
      dsimp
      congr 1
      have h1 : u a - (u a + (ux * γ'.1 + uy * γ'.2) * (t - t₀)) = -(ux * γ'.1 + uy * γ'.2) * (t - t₀) := by ring
      have h2 : v a - (v a + (vx * γ'.1 + vy * γ'.2) * (t - t₀)) = -(vx * γ'.1 + vy * γ'.2) * (t - t₀) := by ring
      rw [h_u_eq, h_v_eq, h1, h2]
    }
    
    have h_total_norm2 : euclideanNorm (-(ux * γ'.1 + uy * γ'.2) * (t - t₀), -(vx * γ'.1 + vy * γ'.2) * (t - t₀)) = euclideanNorm ((ux * γ'.1 + uy * γ'.2) * (t - t₀), (vx * γ'.1 + vy * γ'.2) * (t - t₀)) := by {
      unfold euclideanNorm sqNorm
      dsimp
      congr 1
      ring
    }
    
    rw [h_total_norm, h_total_norm2]
    
    have h_err_γ_zero : err_γ = - γ'.1 * (t - t₀) := by {
      dsimp [err_γ]
      rw [h_γ_eq, hγ_a]
      ring
    }
    have h_err_γ_2_zero : err_γ_2 = - γ'.2 * (t - t₀) := by {
      dsimp [err_γ_2]
      rw [h_γ_eq, hγ_a]
      ring
    }
    
    have h_matrix_zero : euclideanNorm ((ux * γ'.1 + uy * γ'.2) * (t - t₀), (vx * γ'.1 + vy * γ'.2) * (t - t₀)) = euclideanNorm (ux * err_γ + uy * err_γ_2, vx * err_γ + vy * err_γ_2) := by {
      unfold euclideanNorm sqNorm
      dsimp
      congr 1
      rw [h_err_γ_zero, h_err_γ_2_zero]
      ring
    }
    
    rw [h_matrix_zero]
    
    have h_matrix := matrix_bound ux uy vx vy err_γ err_γ_2
    
    have h_bound_mat : (|ux| + |uy| + |vx| + |vy|) * euclideanNorm (err_γ, err_γ_2) ≤ (|ux| + |uy| + |vx| + |vy|) * ((ε / (2 * M)) * |t - t₀|) := by {
      have h1 : 0 ≤ |ux| + |uy| + |vx| + |vy| := by positivity
      exact mul_le_mul_of_nonneg_left (le_of_lt h_γ_bound2) h1
    }
    
    have h_bound_mat2 : (|ux| + |uy| + |vx| + |vy|) * ((ε / (2 * M)) * |t - t₀|) < (ε / 2) * |t - t₀| := by {
      have h_strict : (|ux| + |uy| + |vx| + |vy|) < M := by {
        dsimp [M]
        linarith
      }
      have h_pos : 0 < (ε / (2 * M)) * |t - t₀| := mul_pos hε2_pos ht.1
      have h1 : (|ux| + |uy| + |vx| + |vy|) * ((ε / (2 * M)) * |t - t₀|) < M * ((ε / (2 * M)) * |t - t₀|) := mul_lt_mul_of_pos_right h_strict h_pos
      have h2 : M * ((ε / (2 * M)) * |t - t₀|) = (ε / 2) * |t - t₀| := by {
        calc M * ((ε / (2 * M)) * |t - t₀|)
          _ = M * (ε / (2 * M)) * |t - t₀| := by ring
          _ = M * (1 / M) * (ε / 2) * |t - t₀| := by ring
          _ = (M * (1 / M)) * (ε / 2) * |t - t₀| := by ring
          _ = 1 * (ε / 2) * |t - t₀| := by {
            congr 2
            exact mul_one_div_cancel (ne_of_gt hM_pos)
          }
          _ = (ε / 2) * |t - t₀| := by ring
      }
      rw [h2] at h1
      exact h1
    }
    
    have h_bound_mat3 : euclideanNorm (ux * err_γ + uy * err_γ_2, vx * err_γ + vy * err_γ_2) < (ε / 2) * |t - t₀| := by {
      exact lt_of_le_of_lt h_matrix (lt_of_le_of_lt h_bound_mat h_bound_mat2)
    }
    
    have h_half_lt_full : (ε / 2) * |t - t₀| < ε * |t - t₀| := by {
      have h_half : ε / 2 < ε := by linarith
      exact mul_lt_mul_of_pos_right h_half ht.1
    }
    
    exact lt_of_lt_of_le h_bound_mat3 (le_of_lt h_half_lt_full)

    
  · -- If γ t ≠ a
    have h_dist_pos : 0 < euclideanDist (γ t) a := by {
      have h1 : euclideanDist (γ t) a ≠ 0 := by {
        intro h_contra
        rw [← hγ_a] at h_contra
        exact h_dist_0 h_contra
      }
      exact lt_of_le_of_ne (euclideanDist_nonneg _ _) h1.symm
    }
    
    have h_dist_bound : euclideanDist (γ t) a < δ1 := by {
      rw [← hγ_a]
      have h1 : euclideanDist (γ t) (γ t₀) ≤ K * |t - t₀| := h_lip_bound
      have h2 : K * |t - t₀| < K * δ3 := by {
        exact mul_lt_mul_of_pos_left ht3 hK_pos
      }
      have h3 : K * δ3 = δ1 := mul_div_cancel₀ _ (ne_of_gt hK_pos)
      rw [h3] at h2
      exact lt_of_le_of_lt h1 h2
    }
    
    have h_u_bound := hδ1 (γ t) ⟨h_dist_pos, h_dist_bound⟩
    
    let dx := (γ t).1 - a.1
    let dy := (γ t).2 - a.2
    
    let err_u := u (γ t) - u a - (ux * dx + uy * dy)
    let err_v := v (γ t) - v a - (vx * dx + vy * dy)
    
    have h_total_err_x : u (γ t) - (u a + ((ux * γ'.1 + uy * γ'.2) * (t - t₀))) = err_u + (ux * err_γ + uy * err_γ_2) := by {
      rw [h_err_γ, h_err_γ_2]
      dsimp [err_u, dx, dy]
      ring
    }
    have h_total_err_y : v (γ t) - (v a + ((vx * γ'.1 + vy * γ'.2) * (t - t₀))) = err_v + (vx * err_γ + vy * err_γ_2) := by {
      rw [h_err_γ, h_err_γ_2]
      dsimp [err_v, dx, dy]
      ring
    }
    
    have h_total_norm : euclideanDist (u (γ t), v (γ t)) (u a + (ux * γ'.1 + uy * γ'.2) * (t - t₀), v a + (vx * γ'.1 + vy * γ'.2) * (t - t₀)) = euclideanNorm (u (γ t) - (u a + ((ux * γ'.1 + uy * γ'.2) * (t - t₀))), v (γ t) - (v a + ((vx * γ'.1 + vy * γ'.2) * (t - t₀)))) := by {
      unfold euclideanDist sqDist euclideanNorm sqNorm
      dsimp
    }
    
    have h_triangle_norm := euclideanNormTriangle (err_u, err_v) (ux * err_γ + uy * err_γ_2, vx * err_γ + vy * err_γ_2)
    
    have h_bound_uv : euclideanNorm (err_u, err_v) < (ε / (2 * K)) * euclideanDist (γ t) a := h_u_bound
    
    have h_dist_le : (ε / (2 * K)) * euclideanDist (γ t) a ≤ (ε / (2 * K)) * (K * |t - t₀|) := by {
      have h1 : euclideanDist (γ t) (γ t₀) ≤ K * |t - t₀| := h_lip_bound
      rw [hγ_a] at h1
      exact mul_le_mul_of_nonneg_left h1 (le_of_lt hε1_pos)
    }
    
    have h_bound_uv2 : euclideanNorm (err_u, err_v) < (ε / 2) * |t - t₀| := by {
      have h1 : (ε / (2 * K)) * (K * |t - t₀|) = (ε / 2) * |t - t₀| := by {
        calc (ε / (2 * K)) * (K * |t - t₀|)
          _ = (ε / 2) * (1 / K) * K * |t - t₀| := by ring
          _ = (ε / 2) * ((1 / K) * K) * |t - t₀| := by ring
          _ = (ε / 2) * 1 * |t - t₀| := by {
            congr 2
            exact one_div_mul_cancel (ne_of_gt hK_pos)
          }
          _ = (ε / 2) * |t - t₀| := by ring
      }
      rw [h1] at h_dist_le
      exact lt_of_lt_of_le h_bound_uv h_dist_le
    }
    
    have h_matrix := matrix_bound ux uy vx vy err_γ err_γ_2
    
    have h_bound_mat : (|ux| + |uy| + |vx| + |vy|) * euclideanNorm (err_γ, err_γ_2) ≤ (|ux| + |uy| + |vx| + |vy|) * ((ε / (2 * M)) * |t - t₀|) := by {
      have h1 : 0 ≤ |ux| + |uy| + |vx| + |vy| := by positivity
      exact mul_le_mul_of_nonneg_left (le_of_lt h_γ_bound2) h1
    }
    
    have h_bound_mat2 : (|ux| + |uy| + |vx| + |vy|) * ((ε / (2 * M)) * |t - t₀|) < (ε / 2) * |t - t₀| := by {
      have h_strict : (|ux| + |uy| + |vx| + |vy|) < M := by {
        dsimp [M]
        linarith
      }
      have h_pos : 0 < (ε / (2 * M)) * |t - t₀| := mul_pos hε2_pos ht.1
      have h1 : (|ux| + |uy| + |vx| + |vy|) * ((ε / (2 * M)) * |t - t₀|) < M * ((ε / (2 * M)) * |t - t₀|) := mul_lt_mul_of_pos_right h_strict h_pos
      have h2 : M * ((ε / (2 * M)) * |t - t₀|) = (ε / 2) * |t - t₀| := by {
        calc M * ((ε / (2 * M)) * |t - t₀|)
          _ = M * (ε / (2 * M)) * |t - t₀| := by ring
          _ = M * (1 / M) * (ε / 2) * |t - t₀| := by ring
          _ = (M * (1 / M)) * (ε / 2) * |t - t₀| := by ring
          _ = 1 * (ε / 2) * |t - t₀| := by {
            congr 2
            exact mul_one_div_cancel (ne_of_gt hM_pos)
          }
          _ = (ε / 2) * |t - t₀| := by ring
      }
      rw [h2] at h1
      exact h1
    }
    
    have h_bound_mat3 : euclideanNorm (ux * err_γ + uy * err_γ_2, vx * err_γ + vy * err_γ_2) < (ε / 2) * |t - t₀| := by {
      exact lt_of_le_of_lt h_matrix (lt_of_le_of_lt h_bound_mat h_bound_mat2)
    }
    
    have h_final : euclideanNorm (err_u, err_v) + euclideanNorm (ux * err_γ + uy * err_γ_2, vx * err_γ + vy * err_γ_2) < ε * |t - t₀| := by {
      have h1 : (ε / 2) * |t - t₀| + (ε / 2) * |t - t₀| = ε * |t - t₀| := by ring
      rw [← h1]
      exact add_lt_add h_bound_uv2 h_bound_mat3
    }
    
    have h_final_bound : euclideanNorm (err_u + (ux * err_γ + uy * err_γ_2), err_v + (vx * err_γ + vy * err_γ_2)) < ε * |t - t₀| := lt_of_le_of_lt h_triangle_norm h_final
    
    rw [h_total_norm, h_total_err_x, h_total_err_y]
    exact h_final_bound
}

end ComplexAnalysis.R2
