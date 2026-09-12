import ComplexAnalysis.Sarason.Chapter2
open Classical

noncomputable def translated_path {x y : ℂ} (c : ℂ) (γ : path_in_C x y) : path_in_C (c + x) (c + y) where
  toFun := fun t => c + γ.toFun t
  continuous_toFun := Continuous.add continuous_const γ.continuous_toFun
  source' := by { dsimp; exact γ.source' }
  target' := by { dsimp; exact γ.target' }

lemma translated_path_extend {x y : ℂ} (c : ℂ) (γ : path_in_C x y) (t : ℝ) :
  (translated_path c γ).extend t = c + γ.extend t := by {
  change c + γ.toFun (Set.projIcc 0 1 zero_le_one t) = c + ⇑γ (Set.projIcc 0 1 zero_le_one t)
  rfl
}
