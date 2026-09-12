import Mathlib.Data.Real.Basic
import Mathlib.Data.Finset.Basic
import FantasyFootball.VORP
import ProbStats.Probability

open Finset
open scoped BigOperators
open ProbStats

namespace FantasyFootball

/-- A draft strategy selects a subset of size K from the player pool. -/
def DraftStrategy {N : ℕ} (K : ℕ) (univ : PlayerUniverse N) := 
  { s : Finset (PlayerPool N) // s.card = K }

/-- Total VORP of a draft strategy. -/
def total_vorp {N K : ℕ} (univ : PlayerUniverse N) (nn : DualNN univ) (s : DraftStrategy K univ) : ℝ :=
  ∑ i ∈ s.val, vorp univ nn i

/-- 
  Lemma 3: Value Discrepancy Theory
  If VORP(x) > VORP(y) but M_adp(x) > M_adp(y), drafting x instead of y 
  strictly increases the total VORP of the team, yielding a higher expected 
  objective value. 
-/
lemma value_discrepancy {N K : ℕ} (univ : PlayerUniverse N) (nn : DualNN univ) 
  (s : DraftStrategy K univ) (x y : PlayerPool N) 
  (hx_not_in : x ∉ s.val) (hy_in : y ∈ s.val) 
  (h_vorp : vorp univ nn x > vorp univ nn y)
  (h_adp : nn.adp x > nn.adp y) : 
  ∑ i ∈ (erase s.val y ∪ {x}), vorp univ nn i > total_vorp univ nn s := by {
  unfold total_vorp
  have h_disj : Disjoint (erase s.val y) {x} := by {
    rw [disjoint_singleton_right]
    intro h_err
    have h_mem : x ∈ s.val := mem_of_mem_erase h_err
    contradiction
  }
  have h_sum1 : ∑ i ∈ (erase s.val y ∪ {x}), vorp univ nn i = (∑ i ∈ erase s.val y, vorp univ nn i) + vorp univ nn x := by {
    rw [sum_union h_disj, sum_singleton]
  }
  have h_sum2 : ∑ i ∈ s.val, vorp univ nn i = (∑ i ∈ erase s.val y, vorp univ nn i) + vorp univ nn y := by {
    symm
    apply sum_erase_add
    exact hy_in
  }
  linarith
}

/-- 
  Tying into ProbStats: 
  We model the expected points contribution over a probability distribution 
  of games/outcomes (FiniteDist).
-/
def team_expected_points {N K : ℕ} (univ : PlayerUniverse N) (nn : DualNN univ) 
  (s : DraftStrategy K univ) (dist : FiniteDist N) : ℝ :=
  expectedValue dist (fun i => if i ∈ s.val then nn.pts i else 0)

end FantasyFootball

