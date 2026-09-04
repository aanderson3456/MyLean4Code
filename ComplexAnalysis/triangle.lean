    have hxNormNonneg : euclideanNorm x ≥ 0 := by
      exact eucNormNonNegR2 x
    have hyNormNonneg : euclideanNorm y ≥ 0 := by
      exact eucNormNonNegR2 y
    rw [sqNormEqEucNormSq]
    rw [sqNormEqEucNormSq]
    rw [iff_comm]
    exact (sq_le_sq₀ hxNormNonneg hyNormNonneg)
}

lemma addSqsNonnegR (a b : ℝ) : 0 ≤ a^2 + b^2 := by {
  exact Left.add_nonneg (sq_nonneg a) (sq_nonneg b)
}

lemma sqSqrtEqn (a b c d : ℝ) :
  (√(a ^ 2 + b ^ 2) + √(c ^ 2 + d ^ 2))^2
  = a^2 + b^2 + c^2 + d^2 + 2*√(a^2+b^2)*√(c^2+d^2) := by {
    rw [add_sq']
    rw [Real.sq_sqrt]
    rw [Real.sq_sqrt]
    simp
    exact Eq.symm (add_assoc (a ^ 2 + b ^ 2) (c ^ 2) (d ^ 2))
    exact addSqsNonnegR c d
    exact addSqsNonnegR a b
}

#check sq_le_sq₀

lemma algIneq1Rlemma (a b : ℝ) : a ≤ b → 2*a ≤ 2*b := by {
  intro hyp
  linarith
}

lemma babyCauchySchwarzR (a b c d : ℝ) : (a*c + b*d)^2 ≤ (a^2 + b^2)*(c^2 + d^2) := by {
  have h : (a^2 + b^2) * (c^2 + d^2) - (a*c + b*d)^2 = (a*d - b*c)^2 := by ring
  -- Since the right side is a square, it is ≥ 0
  have h_nonneg : 0 ≤ (a*d - b*c)^2 := pow_two_nonneg (a*d - b*c)
  -- Therefore, RHS - LHS ≥ 0 implies LHS ≤ RHS
  linarith
}

#print algIneq1Rlemma

lemma algIneq1R (a b c d : ℝ) :
  2*a*c + 2*b*d ≤ 2*√((a^2+b^2)*(c^2+d^2)) := by {
  --mul_add has trouble without assoc
  have h2ac : 2*a*c = 2*(a*c) := by
    exact mul_assoc 2 a c
  rw [h2ac]
  --now do it for 2bd
  rw [mul_assoc]
      -- Factor out the 2 on the left side
  rw [← mul_add 2 (a*c) (b*d)]
  -- Divide both sides by 2 (since 2 > 0, the inequality direction stays the same)
  apply algIneq1Rlemma
    -- Use the property that x ≤ √y is implied by x² ≤ y (regardless of sign of x)
  apply Real.le_sqrt_of_sq_le
  -- The remaining inequality (ac + bd)² ≤ (a² + b²)(c² + d²) is the Cauchy-Schwarz inequality.
  -- nlinarith can solve this automatically by expanding and cancelling terms.
  exact babyCauchySchwarzR a b c d
}

lemma addIneqBothSidesR (a b c : ℝ) : a ≤ b → c + a ≤ c + b := by {
  intro h
  exact (add_le_add_iff_left c).mpr h
}

lemma hassoc (x y : ℝ × ℝ) :  x.1 ^ 2 + y.1 ^ 2 + 2 * x.1 * y.1 + (x.2 ^ 2 + y.2 ^ 2 + 2 * x.2 * y.2) =
      x.1 ^ 2 + (y.1 ^ 2 + 2 * x.1 * y.1 + (x.2 ^ 2 + y.2 ^ 2 + 2 * x.2 * y.2)) := by {
  ring
}

lemma hassoc2 (x y : ℝ × ℝ) : x.1 ^ 2 + x.2 ^ 2 + y.1 ^ 2 + y.2 ^ 2 + 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2) =
  x.1 ^ 2 + (x.2 ^ 2 + y.1 ^ 2 + y.2 ^ 2 + 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2)) := by {
    ring
}

theorem euclideanNormTriangle (x y : ℝ × ℝ) :
  euclideanNorm (x + y) ≤ euclideanNorm x + euclideanNorm y := by {
    unfold euclideanNorm
    unfold sqNorm
    simp
    have hlpos : 0 ≤ √((x.1 + y.1) ^ 2 + (x.2 + y.2) ^ 2) := by
      apply sqrtNonneg
      exact addSqsNonnegR (x.1+y.1) (x.2+y.2)
    have hrxpos : 0 ≤ √(x.1 ^ 2 + x.2 ^ 2) := by
      apply sqrtNonneg
      exact addSqsNonnegR x.1 x.2
    have hrypos : 0 ≤ √(y.1 ^ 2 + y.2 ^ 2) := by
      apply sqrtNonneg
      exact addSqsNonnegR y.1 y.2
    have hrpos : 0 ≤ √(x.1 ^ 2 + x.2 ^ 2) + √(y.1 ^ 2 + y.2 ^ 2) := by
      exact Left.add_nonneg hrxpos hrypos
    apply (sq_le_sq₀ hlpos hrpos).mp
    --nlinarith and ring are not working at each stage of the following
    rw [sqSqrtEqn]
    rw [Real.sq_sqrt]
    rw [add_sq']
    rw [add_sq']
    rw [hassoc]
    rw [hassoc2]
    apply addIneqBothSidesR (y.1 ^ 2 + 2 * x.1 * y.1 + (x.2 ^ 2 + y.2 ^ 2 + 2 * x.2 * y.2))
      (x.2 ^ 2 + y.1 ^ 2 + y.2 ^ 2 + 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2)) (x.1 ^ 2)
    have hassoc3 : y.1 ^ 2 + 2 * x.1 * y.1 + (x.2 ^ 2 + y.2 ^ 2 + 2 * x.2 * y.2) =
      y.1 ^ 2 + (2 * x.1 * y.1 + (x.2 ^ 2 + y.2 ^ 2 + 2 * x.2 * y.2)) := by
        ring
    rw [hassoc3]
    have hassocComm : x.2 ^ 2 + y.1 ^ 2 + y.2 ^ 2 + 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2) =
      y.1 ^ 2 + (x.2 ^ 2 + y.2 ^ 2 + 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2)) := by
        ring
    rw [hassocComm]
    apply addIneqBothSidesR --finally finds pattern itself
    have hassocComm2 : 2 * x.1 * y.1 + (x.2 ^ 2 + y.2 ^ 2 + 2 * x.2 * y.2) =
      (x.2 ^2 + y.2 ^2) + (2 * x.1 * y.1 + 2 * x.2 * y.2) := by
        ring
    rw [hassocComm2]
    --apply addIneqBothSidesR _ _ (x.2 ^2 + y.2 ^ 2)
    have hassoc4 : x.2 ^ 2 + y.2 ^ 2 + 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2) =
      (x.2 ^ 2 + y.2 ^ 2) + (2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2)) := by
        ring
    rw [hassoc4]
    apply addIneqBothSidesR (2 * x.1 * y.1 + 2 * x.2 * y.2)
      (2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2)) (x.2 ^2 + y.2 ^2)
    have hsqrtMult : √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2) =
      √((x.1 ^ 2 + x.2 ^ 2) * (y.1 ^ 2 + y.2 ^ 2)) := by
        refine Eq.symm (Real.sqrt_mul' (x.1 ^ 2 + x.2 ^ 2) ?_)
        exact addSqsNonnegR y.1 y.2
    have hassoc5 : 2 * √(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2) =
      2 * (√(x.1 ^ 2 + x.2 ^ 2) * √(y.1 ^ 2 + y.2 ^ 2)) := by
        exact mul_assoc 2 √(x.1 ^ 2 + x.2 ^ 2) √(y.1 ^ 2 + y.2 ^ 2)
    rw [hassoc5]
    --annoying how goal display seems to be missing parsing
    rw [hsqrtMult]
    apply algIneq1R x.1 x.2 y.1 y.2
    exact addSqsNonnegR (x.1 + y.1) (x.2 + y.2)
}

lemma euclideanDistTriangle (x y z : ℝ × ℝ) :
    euclideanDist x z ≤ euclideanDist x y + euclideanDist y z := by {
  -- 1. Unfold the definition of distance to work with norms
  -- Note: This assumes sqDist x z is defined as sqNorm (x - z)
  rw [euclideanDist, euclideanDist, euclideanDist]

  -- 2. Use the fact that x - z = (x - y) + (y - z)
  -- This is the "add-zero" trick: x - z = x - y + y - z
  have h : x - z = (x - y) + (y - z) := by simp

  -- 3. Rewrite the target using this identity
  rw [eucDistIsNormDiff]
  rw [h]

  -- 4. Apply your previously proven theorem
  apply euclideanNormTriangle (x - y) (y - z)
}

-- To prove this, we would need lemmas relating `euclideanDist`
