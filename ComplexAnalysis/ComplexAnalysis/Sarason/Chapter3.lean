/-
  This formalization of complex analysis is spearheaded by Austin Anderson, aided by Gemini.
  Donald Sarason holds the copyright on his "Notes on Complex Function Theory".
  Donald Sarason is Austin Anderson's mathematical genealogy grandfather.
-/
import Mathlib.Analysis.Complex.Basic
import Mathlib.Topology.Compactification.OnePoint.ProjectiveLine

/-!
# Sarason - Chapter 3: Linear-Fractional Transformations

Formalization of Section III of Donald Sarason's "Notes on Complex Function Theory".
Focus: Complex projective space, linear-fractional transformations (Möbius transformations),
and decomposition into basic translations, scaling, and inversion.

Credit: Donald Sarason
-/

open Complex OnePoint MatrixGroups Matrix

namespace Sarason.Ch3

--  The standard division-ring one-point compactification action specializes to ℂ.
--  For a matrix g in GL(2, ℂ) and a complex number z in ℂ (embedded in OnePoint ℂ as `some z`),
--  the Möbius transformation maps z to:
--  - infinity if the denominator g 1 0 * z + g 1 1 = 0
--  - (g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) otherwise.
theorem moebius_apply_some (g : GL (Fin 2) ℂ) (z : ℂ) :
    g • (z : OnePoint ℂ) =
      if g 1 0 * z + g 1 1 = 0 then ∞ else ((g 0 0 * z + g 0 1) / (g 1 0 * z + g 1 1) : ℂ) := by {
  exact OnePoint.smul_some_eq_ite
}

--  Action of Möbius transformations on the point at infinity.
--  The Möbius transformation maps infinity to:
--  - infinity if g 1 0 = 0
--  - g 0 0 / g 1 0 otherwise.
theorem moebius_apply_infty (g : GL (Fin 2) ℂ) :
    g • (∞ : OnePoint ℂ) =
      if g 1 0 = 0 then ∞ else (g 0 0 / g 1 0 : ℂ) := by {
  exact OnePoint.smul_infty_eq_ite g
}

/-- The matrix for the translation z ↦ z + b. -/
noncomputable def translationMatrix (b : ℂ) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, b; 0, 1] (by {
    simp [det_fin_two]
  })

--  Applying the translation matrix to a complex number z yields z + b.
theorem translation_apply (b : ℂ) (z : ℂ) :
    translationMatrix b • (z : OnePoint ℂ) = (z + b : ℂ) := by {
  rw [moebius_apply_some]
  have h_den : (translationMatrix b) 1 0 * z + (translationMatrix b) 1 1 = 1 := by {
    simp [translationMatrix]
  }
  rw [h_den]
  simp [translationMatrix]
}

/-- The matrix for the scaling z ↦ a * z (for a ≠ 0). -/
noncomputable def scalingMatrix (a : ℂ) (ha : a ≠ 0) : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![a, 0; 0, 1] (by {
    simp [det_fin_two, ha]
  })

--  Applying the scaling matrix to a complex number z yields a * z.
theorem scaling_apply (a : ℂ) (ha : a ≠ 0) (z : ℂ) :
    scalingMatrix a ha • (z : OnePoint ℂ) = (a * z : ℂ) := by {
  rw [moebius_apply_some]
  have h_den : (scalingMatrix a ha) 1 0 * z + (scalingMatrix a ha) 1 1 = 1 := by {
    simp [scalingMatrix]
  }
  rw [h_den]
  simp [scalingMatrix]
}

/-- The matrix for the inversion z ↦ 1 / z. -/
noncomputable def inversionMatrix : GL (Fin 2) ℂ :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero !![0, 1; 1, 0] (by {
    simp [det_fin_two]
  })

--  Applying the inversion matrix to a non-zero complex number z yields 1 / z.
theorem inversion_apply_some (z : ℂ) (hz : z ≠ 0) :
    inversionMatrix • (z : OnePoint ℂ) = (z⁻¹ : ℂ) := by {
  rw [moebius_apply_some]
  have h_den : (inversionMatrix) 1 0 * z + (inversionMatrix) 1 1 = z := by {
    simp [inversionMatrix]
  }
  rw [h_den]
  split_ifs with h
  · contradiction
  · have h_num : (inversionMatrix) 0 0 * z + (inversionMatrix) 0 1 = 1 := by {
      simp [inversionMatrix]
    }
    rw [h_num]
    rw [one_div]
}

--  Applying the inversion matrix to 0 yields infinity.
theorem inversion_apply_zero :
    inversionMatrix • ((0 : ℂ) : OnePoint ℂ) = ∞ := by {
  rw [moebius_apply_some]
  have h_den : (inversionMatrix) 1 0 * 0 + (inversionMatrix) 1 1 = 0 := by {
    simp [inversionMatrix]
  }
  rw [h_den]
  simp
}

--  Applying the inversion matrix to infinity yields 0.
theorem inversion_apply_infty :
    inversionMatrix • (∞ : OnePoint ℂ) = (0 : ℂ) := by {
  rw [moebius_apply_infty]
  have h_den : (inversionMatrix) 1 0 = 1 := by {
    simp [inversionMatrix]
  }
  rw [h_den]
  simp [inversionMatrix]
}

end Sarason.Ch3
