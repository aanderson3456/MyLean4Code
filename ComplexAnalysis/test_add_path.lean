import ComplexAnalysis.Sarason.Chapter2

open ComplexAnalysis.R2
open Complex
open Sarason
open Sarason.Ch2

def path_add_const (z : ℂ) {x y : ℂ} (γ : path_in_C x y) : path_in_C (z + x) (z + y) where
  toFun t := z + (γ : Path x y) t
  continuous_toFun := Continuous.add continuous_const (γ : Path x y).continuous_toFun
  source' := by { dsimp; rw [(γ : Path x y).source'] }
  target' := by { dsimp; rw [(γ : Path x y).target'] }

lemma path_add_const_extend (z : ℂ) {x y : ℂ} (γ : path_in_C x y) (t : ℝ) :
  (path_add_const z γ : Path (z + x) (z + y)).extend t = z + (γ : Path x y).extend t := by {
  unfold Path.extend
  dsimp [path_add_const]
  split_ifs <;> rfl
}

lemma hasDerivAt_path_add_const {x y : ℂ} (γ : path_in_C x y) (z : ℂ) (t : ℝ) (v : ℂ)
  (h_deriv : HasDerivAt_R_to_C_eps (fun t => (γ : Path x y).extend t) v t) :
  HasDerivAt_R_to_C_eps (fun t => (path_add_const z γ : Path (z + x) (z + y)).extend t) v t := by {
  unfold HasDerivAt_R_to_C_eps at *
  intro ε hε
  rcases h_deriv ε hε with ⟨δ, hδ_pos, hδ⟩
  use δ, hδ_pos
  intro t' ht'
  have h_bound := hδ t' ht'
  have h_eq : (path_add_const z γ : Path (z + x) (z + y)).extend t' - ((path_add_const z γ : Path (z + x) (z + y)).extend t + v * (t' - t)) =
              (γ : Path x y).extend t' - ((γ : Path x y).extend t + v * (t' - t)) := by {
    rw [path_add_const_extend, path_add_const_extend]
    ring
  }
  rw [h_eq]
  exact h_bound
}
