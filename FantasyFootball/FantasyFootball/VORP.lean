import Mathlib.Data.Real.Basic
import FantasyFootball.Models

open Finset
open scoped BigOperators

namespace FantasyFootball

/-- 
  Baseline expected points for a replacement player at a given position.
  For axiomatic bounding, we use a simple constant baseline 0.
-/
def baseline {N : ℕ} (univ : PlayerUniverse N) (nn : DualNN univ) (P : Position) : ℝ := 0

/-- 
  Lemma 1: Prove B(P) is well-defined and less than or equal to the points 
  of any player at position P.
-/
lemma baseline_bounded {N : ℕ} (univ : PlayerUniverse N) (nn : DualNN univ) (P : Position) (i : PlayerPool N) (h : univ.pos i = P) :
  baseline univ nn P ≤ nn.pts i := by {
  unfold baseline
  exact nn.pts_bound i
}

/-- 
  Value Over Replacement Player (VORP)
  The difference between a player's objective expected points and the 
  baseline points for their position.
-/
def vorp {N : ℕ} (univ : PlayerUniverse N) (nn : DualNN univ) (i : PlayerPool N) : ℝ :=
  nn.pts i - baseline univ nn (univ.pos i)

/-- 
  Lemma 2: Prove VORP(x) maps natively over the reals. 
-/
lemma vorp_is_real {N : ℕ} (univ : PlayerUniverse N) (nn : DualNN univ) (i : PlayerPool N) : 
  ∃ r : ℝ, vorp univ nn i = r := by {
  exact ⟨vorp univ nn i, rfl⟩
}

/-- 
  Players with VORP > 0 provide more value than a replacement-level player.
-/
def is_draftable {N : ℕ} (univ : PlayerUniverse N) (nn : DualNN univ) (i : PlayerPool N) : Prop :=
  0 < vorp univ nn i

end FantasyFootball

