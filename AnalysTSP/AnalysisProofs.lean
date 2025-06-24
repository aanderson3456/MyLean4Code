import Mathlib.Data.Nat.Defs
import Mathlib.Tactic.Ring.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean


theorem ZeroPlusNisN (n : ℕ) : 0 + n = n := by {
  induction' n with d hd
  rfl
  rw [← hd]
  rw [Nat.add_assoc]
  simp
}

#print ZeroPlusNisN

open Nat

theorem TwoPlusTwoNeqFive : succ (succ 0) + succ (succ 0) ≠ succ (succ (succ (succ (succ 0)))) := by {
  simp
}

#print TwoPlusTwoNeqFive

def LowerBoundReal (r : ℝ) (A : Set ℝ) : Prop :=
  (∀ a ∈ A, a ≥ r)

def GreatestLowerBoundReal (r: ℝ) (A : Set ℝ) : Prop :=
  (LowerBoundReal r A) ∧ (∀ s : ℝ, (LowerBoundReal s A) → r ≥ s)

def reciprocalsOfNaturalNumbers : Set ℝ :=
  { r : ℝ | ∃ n : ℕ, n ≠ 0 ∧ r = 1 / n }

--I think the lemma below can be writting without the ↑ but needs the :ℝ
lemma lemma0 (N : ℕ) : ((↑N : ℝ) > 0) → (N ≠ 0) := by {
  intro h_N_pos_real
    -- Assume for contradiction that N = 0.
  by_contra h_N_eq_zero
  -- If N is 0, then casting N to a real number should also be 0.
  have h_N_real_eq_zero : (↑N : ℝ) = 0 := by
    -- We can substitute `N` with `0` using `rw` and the assumption `h_N_eq_zero`.
    rw [h_N_eq_zero]
    -- The goal is now `(0 : ℝ) = 0`, which requires casting.
    exact AddMonoidWithOne.natCast_zero
  -- We can substitute `(N : ℝ)` with `0` in `h_N_pos_real` using `h_N_real_eq_zero`.
  rw [← h_N_real_eq_zero] at h_N_pos_real
  -- This transforms `h_N_pos_real` into `(0 : ℝ) > 0`.
  -- This is a contradiction, as `0` cannot be strictly greater than `0`.
  -- We can use `lt_irrefl` which states that `¬ (a < a)`.
  exact lt_irrefl (↑N : ℝ) h_N_pos_real
}

lemma lemma1 (s : ℝ) : (0 < s) → ∃ n : ℕ, ((n ≠ 0) ∧ (1/n < s)) := by {
  intro hs
  have h_exists_n_gt_inv_s : ∃ N : ℕ, N > (1/s) := exists_nat_gt (1/s)
  cases' h_exists_n_gt_inv_s with N hN
  -- We need to ensure that `N` is not zero.
  -- If `1/s` is non-positive, then `N` could be 0 or 1 etc.
  -- Since `s > 0`, `1/s > 0`.
  have h_inv_s_pos : 0 < 1/s := one_div_pos.mpr hs
  have h_inv_s_pos_flip : (1/s) > 0 := by {
    exact h_inv_s_pos
  }
  -- Since `N > 1/s` and `1/s > 0`, we have `N > 0`.
  have hN_pos : (↑N : ℝ) > 0 := by {
    apply gt_trans hN h_inv_s_pos_flip
  }
  -- Since `N` is a natural number and `N > 0`, `N` cannot be zero.
  use N
  constructor
  exact lemma0 N hN_pos
  exact (one_div_lt hs hN_pos).mp hN
}

lemma lemmaP (a : ℝ) (P : (ℝ → Prop)) : ¬ (∀ a, P a) → ∃ a, (¬(P a)) := by {
  intro h
  exact not_forall.mp h
}

lemma lemmaLogic1 (p q : Prop) : (p → q) ∧ (¬ q) → ¬ p := by {
  intro h --when proving R → S, intro h makes h : R (assumes R)
  cases' h with hl hr --split ∧ into right and left
  --goal: ¬ p, means p → False
  --use hl : p → q, and hr : q → False. hr hl is fxn composition p → q → False
  intro hp
  --goal: False, have q → False, so apply q → False gives new goal of q
  apply hr
  --goal: q, so apply p → q get p
  apply hl
  exact hp
}

lemma lemmaLogic2 (p q r : Prop) : (p → q → r) ↔ ((p ∧ q) → r) := by {
  constructor -- creates two new subgoals: one for fowards and one for backwards
  intro h1 pq -- h1: p → q → r is the assumption, pq: p ∧ q is the input we must turn into r
  cases pq with -- Think of this as opening the package
  |intro hp hq => -- hp becomes name for proof of p, hq becomes name for proof of q
  exact h1 hp hq --applying h1 to hp and hq gives a proof of r

}

lemma lemma2 : GreatestLowerBoundReal 0 reciprocalsOfNaturalNumbers := by {
  unfold GreatestLowerBoundReal
  constructor
  unfold LowerBoundReal
  unfold reciprocalsOfNaturalNumbers
  intro a
  intro ha
  cases' ha with n hn
  cases' hn with hn_ne_zero hr_eq_inv_n
  rw [hr_eq_inv_n]
  apply div_nonneg
  exact zero_le_one' ℝ
  exact Nat.cast_nonneg' n
  intro s
  unfold LowerBoundReal reciprocalsOfNaturalNumbers
  intro ha
  by_contra h_contra
  simp at h_contra
  apply lemma1 at h_contra
  apply not_forall.mpr at ha
  exact ha
  cases' h_contra with n h_contra
  use ((1/↑n) : ℝ)
  cases' h_contra with hca hcb
  have han : ((1 / ↑n) : ℝ) ∈ {r : ℝ | ∃ n : ℕ, n ≠ 0 ∧ r = ((1/↑n) : ℝ)} → 1 / ↑n ≥ s := by {
    apply ha ((1/↑n) : ℝ)
  }
  have hanpre : (1/↑n : ℝ) ∈ {r | ∃ (n : ℕ), n ≠ 0 ∧ r = (1/↑n : ℝ)} := by {
    apply Set.mem_setOf.mpr
    use n
  }
  apply han at hanpre
  linarith
}

#print lemma2
