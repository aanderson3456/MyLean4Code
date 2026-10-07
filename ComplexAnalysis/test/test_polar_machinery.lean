import Mathlib

/-- Converts Cartesian partial derivatives (ux, uy) into the polar partial derivative with respect to r. -/
noncomputable def polar_partial_r (ux uy : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  ux (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * Real.cos p.2 +
  uy (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * Real.sin p.2

/-- Converts Cartesian partial derivatives (ux, uy) into the polar partial derivative with respect to θ. -/
noncomputable def polar_partial_theta (ux uy : ℝ × ℝ → ℝ) (p : ℝ × ℝ) : ℝ :=
  -ux (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * p.1 * Real.sin p.2 +
  uy (p.1 * Real.cos p.2, p.1 * Real.sin p.2) * p.1 * Real.cos p.2

/--
  Exercise II.6.3:
  The Cauchy-Riemann equations in polar coordinates.
  If the Cartesian Cauchy-Riemann equations hold, then
  r * u_r = v_θ and r * v_r = -u_θ.
-/
lemma exercise_II_6_3 (ux uy vx vy : ℝ × ℝ → ℝ) (p : ℝ × ℝ)
    (h_CR1 : ux (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = vy (p.1 * Real.cos p.2, p.1 * Real.sin p.2))
    (h_CR2 : uy (p.1 * Real.cos p.2, p.1 * Real.sin p.2) = -vx (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) :
    p.1 * polar_partial_r ux uy p = polar_partial_theta vx vy p ∧
    p.1 * polar_partial_r vx vy p = -polar_partial_theta ux uy p := by
{
  constructor
  · unfold polar_partial_r polar_partial_theta
    rw [h_CR1, h_CR2]
    ring
  · unfold polar_partial_r polar_partial_theta
    rw [h_CR1, h_CR2]
    ring
}

/--
  Exercise II.15.2:
  The Laplacian in polar coordinates.
  r^2 * U_rr + r * U_r + U_θθ = r^2 * (u_xx + u_yy).
-/
lemma exercise_II_15_2 (ux uy uxx uxy uyy : ℝ × ℝ → ℝ) (p : ℝ × ℝ) :
  let U_r := polar_partial_r ux uy p
  let U_rr := Real.cos p.2 * polar_partial_r uxx uxy p + Real.sin p.2 * polar_partial_r uxy uyy p
  let U_thetatheta := -p.1 * Real.cos p.2 * ux (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
                      - p.1 * Real.sin p.2 * polar_partial_theta uxx uxy p
                      - p.1 * Real.sin p.2 * uy (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
                      + p.1 * Real.cos p.2 * polar_partial_theta uxy uyy p
  p.1^2 * U_rr + p.1 * U_r + U_thetatheta =
    p.1^2 * (uxx (p.1 * Real.cos p.2, p.1 * Real.sin p.2) + uyy (p.1 * Real.cos p.2, p.1 * Real.sin p.2)) := by
{
  intros U_r U_rr U_thetatheta
  dsimp [U_r, U_rr, U_thetatheta, polar_partial_r, polar_partial_theta]
  set X := uxx (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
  set Y := uyy (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
  set XY := uxy (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
  set x := ux (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
  set y := uy (p.1 * Real.cos p.2, p.1 * Real.sin p.2)
  set S := Real.sin p.2
  set C := Real.cos p.2
  have hCS : C^2 + S^2 = 1 := by linarith [Real.sin_sq_add_cos_sq p.2]
  have h_eq : p.1^2 * (C * (X * C + XY * S) + S * (XY * C + Y * S)) +
              p.1 * (x * C + y * S) +
              (-p.1 * C * x - p.1 * S * (-X * p.1 * S + XY * p.1 * C) - p.1 * S * y + p.1 * C * (-XY * p.1 * S + Y * p.1 * C)) =
              p.1^2 * X * (C^2 + S^2) + p.1^2 * Y * (C^2 + S^2) := by ring
  rw [h_eq]
  rw [hCS]
  ring
}
