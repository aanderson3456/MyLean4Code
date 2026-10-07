import Mathlib

noncomputable def Ur_alg (ux uy : ℝ × ℝ → ℝ) (r θ : ℝ) : ℝ :=
  ux (r * Real.cos θ, r * Real.sin θ) * Real.cos θ +
  uy (r * Real.cos θ, r * Real.sin θ) * Real.sin θ

noncomputable def Utheta_alg (ux uy : ℝ × ℝ → ℝ) (r θ : ℝ) : ℝ :=
  -ux (r * Real.cos θ, r * Real.sin θ) * r * Real.sin θ +
  uy (r * Real.cos θ, r * Real.sin θ) * r * Real.cos θ

noncomputable def Urr_alg (uxx uxy uyy : ℝ × ℝ → ℝ) (r θ : ℝ) : ℝ :=
  uxx (r * Real.cos θ, r * Real.sin θ) * (Real.cos θ)^2 +
  2 * uxy (r * Real.cos θ, r * Real.sin θ) * Real.cos θ * Real.sin θ +
  uyy (r * Real.cos θ, r * Real.sin θ) * (Real.sin θ)^2

noncomputable def Uthetatheta_alg (ux uy uxx uxy uyy : ℝ × ℝ → ℝ) (r θ : ℝ) : ℝ :=
  uxx (r * Real.cos θ, r * Real.sin θ) * r^2 * (Real.sin θ)^2 -
  2 * uxy (r * Real.cos θ, r * Real.sin θ) * r^2 * Real.sin θ * Real.cos θ +
  uyy (r * Real.cos θ, r * Real.sin θ) * r^2 * (Real.cos θ)^2 -
  ux (r * Real.cos θ, r * Real.sin θ) * r * Real.cos θ -
  uy (r * Real.cos θ, r * Real.sin θ) * r * Real.sin θ

lemma exercise_II_15_2_alg (ux uy uxx uxy uyy : ℝ × ℝ → ℝ) (r θ : ℝ) :
  r^2 * Urr_alg uxx uxy uyy r θ + r * Ur_alg ux uy r θ + Uthetatheta_alg ux uy uxx uxy uyy r θ =
  r^2 * (uxx (r * Real.cos θ, r * Real.sin θ) + uyy (r * Real.cos θ, r * Real.sin θ)) := by
{
  dsimp [Ur_alg, Utheta_alg, Urr_alg, Uthetatheta_alg]
  set X := uxx (r * Real.cos θ, r * Real.sin θ)
  set Y := uyy (r * Real.cos θ, r * Real.sin θ)
  set XY := uxy (r * Real.cos θ, r * Real.sin θ)
  set x := ux (r * Real.cos θ, r * Real.sin θ)
  set y := uy (r * Real.cos θ, r * Real.sin θ)
  set S := Real.sin θ
  set C := Real.cos θ
  have hCS : C^2 + S^2 = 1 := by linarith [Real.sin_sq_add_cos_sq θ]
  have h_eq : r^2 * (X * C^2 + 2 * XY * C * S + Y * S^2) + r * (x * C + y * S) + (X * r^2 * S^2 - 2 * XY * r^2 * S * C + Y * r^2 * C^2 - x * r * C - y * r * S) = r^2 * X * (C^2 + S^2) + r^2 * Y * (C^2 + S^2) := by ring
  rw [h_eq]
  rw [hCS]
  ring
}
