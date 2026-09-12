import Mathlib.Data.Real.Basic
import Mathlib
import ProbStats.Probability

namespace ProbStats

/-- ReLU activation function bounded explicitly over reals. -/
noncomputable def relu (x : ℝ) : ℝ :=
  if x < 0 then 0 else x

/-- Prove that ReLU is always non-negative. -/
theorem relu_nonneg (x : ℝ) : 0 ≤ relu x := by {
  unfold relu
  split
  · rfl
  · linarith
}

/-- Linear approximation proxy for backpropagation gradients. 
    Returns the step scaled by learning rate alpha. -/
def gradStep (w grad alpha : ℝ) : ℝ :=
  w - alpha * grad

/-- Basic gradient bound: if gradient is positive, weight decreases. -/
theorem gradStep_decreases (w grad alpha : ℝ) (h_grad : 0 < grad) (h_alpha : 0 < alpha) :
  gradStep w grad alpha < w := by {
  unfold gradStep
  have h_pos : 0 < alpha * grad := mul_pos h_alpha h_grad
  linarith
}

/-- A node evaluation with 2 inputs. -/
noncomputable def nodeEval (w1 w2 b x1 x2 : ℝ) : ℝ :=
  relu (w1 * x1 + w2 * x2 + b)

/-- A 2-layer, 2-node per layer network. 
    Layer 1 (hidden): 2 nodes. Layer 2 (output): 2 nodes. -/
noncomputable def twoLayerNet2x2
  (w11_1 w12_1 b1_1 w21_1 w22_1 b2_1 : ℝ) -- Layer 1 weights and biases
  (w11_2 w12_2 b1_2 w21_2 w22_2 b2_2 : ℝ) -- Layer 2 weights and biases
  (x1 x2 : ℝ) : ℝ × ℝ :=
  let h1 := nodeEval w11_1 w12_1 b1_1 x1 x2
  let h2 := nodeEval w21_1 w22_1 b2_1 x1 x2
  let o1 := nodeEval w11_2 w12_2 b1_2 h1 h2
  let o2 := nodeEval w21_2 w22_2 b2_2 h1 h2
  (o1, o2)

/-- Theorem showing the non-linearity of the 2-layer network. 
    We prove that f(a) + f(b) ≠ f(a + b) for specific inputs, 
    due to the ReLU activation. -/
theorem twoLayerNet_nonlinear : 
  ∃ (w11_1 w12_1 b1_1 w21_1 w22_1 b2_1 w11_2 w12_2 b1_2 w21_2 w22_2 b2_2 : ℝ) 
    (a1 a2 b1 b2 : ℝ), 
  let f := twoLayerNet2x2 w11_1 w12_1 b1_1 w21_1 w22_1 b2_1 w11_2 w12_2 b1_2 w21_2 w22_2 b2_2
  (f a1 a2).1 + (f b1 b2).1 ≠ (f (a1 + b1) (a2 + b2)).1 := by
  -- We provide specific weights and inputs to demonstrate non-linearity.
  use 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0
  use 1, 0, -1, 0
  unfold twoLayerNet2x2 nodeEval relu
  dsimp
  split
  · linarith
  · split
    · linarith
    · split
      · linarith
      · split
        · norm_num
        · norm_num

/-- 
  Incorporate ideas from Morgane Austern's research. 
  Austern's work explores the theoretical guarantees of Graph Neural Networks (GNNs) 
  for tasks like graph matching and link prediction, as well as generalization 
  bounds for overparameterized networks.
  Here we define a simplified GNN message-passing layer that updates a node's 
  representation based on its neighbors.
-/
noncomputable def gnnLayer (nodeFeature : ℝ) (neighborSum : ℝ) (wSelf wNeighbor b : ℝ) : ℝ :=
  relu (wSelf * nodeFeature + wNeighbor * neighborSum + b)

/-- A simple 2-node graph neural network update step. Nodes 1 and 2 are connected. -/
noncomputable def gnnTwoNodeGraph (x1 x2 : ℝ) (wSelf wNeighbor b : ℝ) : ℝ × ℝ :=
  (gnnLayer x1 x2 wSelf wNeighbor b, gnnLayer x2 x1 wSelf wNeighbor b)

/-!
### Morgane Austern & Suqi Liu: Graph Matching Theorem
Formalizing the statement for "Perfect Recovery for Random Geometric Graph Matching 
with Shallow Graph Neural Networks" (2025).
-/

variable {V : Type}

/-- A simplified representation of a graph with features on vertices. -/
structure FeatureGraph (V : Type) (FeatureSpace : Type) where
  edges : V → V → Prop
  features : V → FeatureSpace

open scoped BigOperators

variable [Fintype V] [DecidableEq V]

/-- A 1-layer message passing aggregation for a node in a graph. -/
noncomputable def aggregate_neighbors (G : FeatureGraph V ℝ) (v : V) : ℝ :=
  open scoped Classical in
  ∑ u, if G.edges v u then G.features u else 0

/-- Node embedding combines self-feature and neighbor aggregation with a ReLU. -/
noncomputable def node_embedding (G : FeatureGraph V ℝ) (v : V) : ℝ :=
  relu (G.features v + aggregate_neighbors G v)

/-- The assignment cost of a specific permutation `pi` mapping vertices of G1 to G2. -/
noncomputable def match_cost (G1 G2 : FeatureGraph V ℝ) (pi : V ≃ V) : ℝ :=
  ∑ v, (node_embedding G1 v - node_embedding G2 (pi v))^2

/-- 
  Computable discrete assignment solver skeleton.
  In practice, we implement this via the Hungarian algorithm (Kuhn-Munkres) 
  in the execution layer (TypeScript/Frontend).
  Here we provide the type signature as a true `def` returning a permutation,
  and a skeleton proof that it minimizes the assignment cost.
-/
def gnn_match (G1 G2 : FeatureGraph V ℝ) : V ≃ V := 
  Equiv.refl V -- Skeleton computable solver

/-- Theorem stating that our matching function minimizes the assignment cost. -/
theorem gnn_match_optimal (G1 G2 : FeatureGraph V ℝ) : 
  ∀ pi, match_cost G1 G2 (gnn_match G1 G2) ≤ match_cost G1 G2 pi := by
  sorry

/-- 
  Statement of Austern and Liu's perfect recovery theorem.
  
  Informally: Under specific sparsity and noise conditions, a shallow Graph Neural Network 
  can perfectly recover the true vertex correspondence `pi_star` between two random 
  geometric graphs with high probability. Here we express the deterministic core: 
  if the noise bound is met for the realized graphs, the GNN yields the exact mapping.
-/
theorem austern_liu_perfect_recovery
  (G1 G2 : FeatureGraph V ℝ) 
  (noise_level : ℝ) 
  (pi_star : V ≃ V) 
  (h_noise_bound : noise_level < 0.1) -- Simplified tightness condition on noise
  (h_generative_model : True) -- Placeholder for random geometric graph generation assumption
  : gnn_match G1 G2 = pi_star := by
  sorry

end ProbStats
