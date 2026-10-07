import Mathlib
open Complex Classical

noncomputable def newmanModifier (R : ℝ) (z : ℂ) : ℂ :=
  1 / z + z / (R : ℂ)^2

lemma newmanModifier_eq_on_circle (R : ℝ) (z : ℂ) (hz : z * star z = (R : ℂ)^2) (hz0 : z ≠ 0) :
    newmanModifier R z = (z + star z) / (R : ℂ)^2 := by
{
  unfold newmanModifier
  -- We know 1/z = star z / (z * star z) = star z / R^2
  have h_inv : 1 / z = star z / (R : ℂ)^2 := by
  {
    have h1 : (1 : ℂ) / z = (star z * 1) / (star z * z) := by
    {
      rw [div_eq_div_iff]
      · ring
      · exact hz0
      · exact mul_ne_zero (star_ne_zero.mpr hz0) hz0
    }
    have h2 : (1 : ℂ) / z = star z / (z * star z) := by
    {
      rw [h1]
      ring
    }
    rw [h2, hz]
  }
  rw [h_inv]
  -- Now we just add the fractions
  ring
}
