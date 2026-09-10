import ComplexAnalysis.Sarason.Chapter2

open ComplexAnalysis.R2
open Complex

noncomputable def linear_path (z v : ℂ) : path_in_C (z - v/2) (z + v/2) where
  toFun t := z + (t - (1/2 : ℝ) : ℂ) * v
  continuous_toFun := Continuous.add continuous_const (Continuous.mul (Continuous.sub continuous_ofReal continuous_const) continuous_const)
  source' := by { dsimp; push_cast; ring }
  target' := by { dsimp; push_cast; ring }

lemma linear_path_extend_half (z v : ℂ) : (linear_path z v).extend (1/2) = z := by {
  unfold Path.extend
  dsimp [linear_path]
  have h1 : ¬ (1/2 : ℝ) ≤ 0 := by norm_num
  have h2 : (1/2 : ℝ) ≤ 1 := by norm_num
  simp [h1, h2]
  push_cast
  ring
}

