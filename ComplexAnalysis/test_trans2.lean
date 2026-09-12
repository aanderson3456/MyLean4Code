import ComplexAnalysis.Sarason.Chapter2
open Classical

noncomputable def translated_path {x y : ℂ} (c : ℂ) (γ : path_in_C x y) : path_in_C (c + x) (c + y) where
  toFun := fun t => c + γ.extend (t : ℝ)
  continuous_toFun := by {
    apply Continuous.add continuous_const
    exact (Path.continuous_extend γ).comp continuous_subtype_val
  }
  source' := by {
    dsimp
    have h : γ.extend 0 = x := by exact γ.source'
    rw [h]
  }
  target' := by {
    dsimp
    have h : γ.extend 1 = y := by exact γ.target'
    rw [h]
  }

lemma translated_path_extend {x y : ℂ} (c : ℂ) (γ : path_in_C x y) (t : ℝ) :
  (translated_path c γ).extend t = c + γ.extend t := by {
  unfold Path.extend
  dsimp [Set.IccExtend, translated_path]
  congr 1
  -- we need to prove γ.extend (Set.projIcc 0 1 t) = γ.extend t
  -- Set.IccExtend is idempotent essentially
  sorry
}
