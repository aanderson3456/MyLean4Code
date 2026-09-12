import Mathlib.Data.Real.Basic
import ProbStats.Probability
import ProbStats.NeuralNet

namespace FantasyFootball

/-- Positions in Fantasy Football -/
inductive Position
| QB | RB | WR | TE
deriving DecidableEq

/-- The player universe as a finite type -/
abbrev PlayerPool (N : ℕ) := Fin N

/-- Player pool mapped to their positions. -/
structure PlayerUniverse (N : ℕ) where
  pos : PlayerPool N → Position

/-- 
  Dual-NN predictions for each player. 
  M_adp: human consensus draft position (≥ 1)
  M_pts: objective expected points (≥ 0)
-/
structure DualNN {N : ℕ} (univ : PlayerUniverse N) where
  adp : PlayerPool N → ℝ
  pts : PlayerPool N → ℝ
  adp_bound : ∀ i, 1 ≤ adp i
  pts_bound : ∀ i, 0 ≤ pts i

end FantasyFootball

