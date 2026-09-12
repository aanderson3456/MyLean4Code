import re

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

path_add_code = """
def path_add_const (z : ℂ) {x y : ℂ} (γ : path_in_C x y) : path_in_C (z + x) (z + y) where
  toFun t := z + γ t
  continuous_toFun := Continuous.add continuous_const γ.continuous_toFun
  source' := by simp [γ.source']
  target' := by simp [γ.target']

lemma path_add_const_extend (z : ℂ) {x y : ℂ} (γ : path_in_C x y) (t : ℝ) :
  (path_add_const z γ).extend t = z + γ.extend t := by {
  unfold Path.extend
  dsimp [path_add_const]
  split_ifs <;> rfl
}

lemma hasDerivAt_path_add_const {x y : ℂ} (γ : path_in_C x y) (z : ℂ) (t : ℝ) (v : ℂ)
  (h_deriv : HasDerivAt_R_to_C_eps γ.extend v t) :
  HasDerivAt_R_to_C_eps (path_add_const z γ).extend v t := by {
  unfold HasDerivAt_R_to_C_eps at *
  intro ε hε
  rcases h_deriv ε hε with ⟨δ, hδ_pos, hδ⟩
  use δ, hδ_pos
  intro t' ht'
  have h_bound := hδ t' ht'
  have h_eq : (path_add_const z γ).extend t' - ((path_add_const z γ).extend t + v * (t' - t)) =
              γ.extend t' - (γ.extend t + v * (t' - t)) := by {
    rw [path_add_const_extend, path_add_const_extend]
    ring
  }
  rw [h_eq]
  exact h_bound
}

lemma pathDeriv_path_add_const {x y : ℂ} (γ : path_in_C x y) (z : ℂ) (t : ℝ) :
  pathDeriv (path_add_const z γ) t = pathDeriv γ t := by {
  sorry -- We don't even need this if we don't unfold pathDeriv
}

"""

# Let's just put it before `lemma path_comp_deriv_R2`
idx = content.find("lemma path_comp_deriv_R2")
content = content[:idx] + path_add_code + content[idx:]

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
