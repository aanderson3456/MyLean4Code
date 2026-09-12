import ProbStats.NeuralNet

open ProbStats

variable {V : Type} [Fintype V] [DecidableEq V]

/-- A simple test theorem to verify GNN match cost optimal structure. -/
theorem test_gnn_optimal_bound (G1 G2 : FeatureGraph V ℝ) : 
  ∃ pi, ∀ pi', match_cost G1 G2 pi ≤ match_cost G1 G2 pi' := by {
  use (gnn_match G1 G2)
  apply gnn_match_optimal
}
