import Mathlib.Data.Set.Countable
import Mathlib.Data.Set.Function
import Mathlib.Data.Rat.Init
import Mathlib.Data.Rat.Cast.CharZero
import Mathlib.Data.Finset.Basic
import Mathlib.Logic.Function.Basic
import Mathlib.Algebra.BigOperators.Group.Finset
import Init.Data.Int
import Init.Prelude
import Lean.Meta.Tactic.LibrarySearch
import Mathlib.Algebra.CharZero.Lemmas
import Mathlib.Algebra.Ring.Parity
import Mathlib.Algebra.Group.Even
import Mathlib.Algebra.Group.Basic

--The ultimate goal is to show there exists no rectifiable path
--covering ℚ×ℚ ∩ [0,1]×[0,1] in the plane, as an example
--of a bounded countable set for which no solution to the
--analyst's travelling salesman problem exists. We build
--countability of the set from elementary principles and use a
--compactness argument.

variable (A : Set ℚ)

lemma nat_to_int_eq (a b : ℕ) : (a = b) → ((↑a : ℤ) = (↑b : ℤ)) := by {
  exact fun a_1 ↦ congrArg Nat.cast a_1
}

lemma nat_to_rat_eq (a b : ℕ) : (a = b) → ((↑a : ℚ) = (↑b : ℚ)) := by {
  exact fun a_1 ↦ congrArg Nat.cast a_1
}

lemma dist_cast_rat (a b : ℕ) : ((↑(a+b)) : ℚ) = ((↑a) : ℚ) + ((↑b) : ℚ) := by {
  simp
}

lemma dist_cast_n_1 (n : ℕ): (↑(n+1) : ℚ) = (↑n : ℚ) + (1 : ℚ) := by {
  simp
}


lemma flip_neg (a b : ℤ) : (a = -b) ↔ (-a = b) := by {
  exact Iff.symm neg_eq_iff_eq_neg
}



--z.sign is funky
def neg_fit_part (z : ℤ) : ℕ :=
  match z with
  | 0 => 0
  | 1 => 0
  | (-1) => 1
  | x => 2 --should never occur

def neg_fit (z : ℤ) : ℕ :=
  neg_fit_part (Int.sign z)

#eval neg_fit (-12)

lemma neg_fit_eq_zero_or_one (z : ℤ) : (neg_fit z = 0) ∨ (neg_fit z = 1) := by {
  cases' z with n
  have h : (Int.sign (Int.ofNat n) = 0) ∨ (Int.sign (Int.ofNat n) = 1) := by
    cases' n with n
    simp
    simp
  cases' h with ha
  apply Or.inl
  unfold neg_fit
  rw [ha]
  rfl
  rename_i h
  apply Or.inl
  unfold neg_fit
  rw [h]
  rfl
  rename_i a
  apply Or.inr
  unfold neg_fit
  simp
  rfl
}


lemma sign_nonneg_iff_natAbs_eq (z : ℤ) :
(z.natAbs = z) ↔ ((z.sign = 0) ∨ (z.sign = 1)) := by {
  apply Iff.intro
  intro h
  cases' z with x
  cases' x with y
  simp
  simp
  simp
  rename_i a
  rw [Int.natAbs_negSucc a] at h
  have h2 : Int.negSucc a < 0 := by
    · apply Int.negSucc_lt_zero a
  rw [← h] at h2
  exact (Int.negSucc_not_nonneg (a + 1)).mp h2
  intro h
  cases' h with h1 h2
  apply (Int.sign_eq_zero_iff_zero z).mp at h1
  rw [h1]
  simp
  apply (Int.sign_eq_one_iff_pos z).mp at h2
  have h3 : 0 ≤ z := by exact Int.le_of_lt h2
  apply (Int.natAbs_of_nonneg h3)
}

--#print sign_nonneg_iff_natAbs_eq

lemma neg_fit_iff_pos (z : ℤ) : (z.natAbs = z) ↔ ((neg_fit z) = 0) := by {
  apply Iff.intro
  cases hna : z.natAbs
  intro h0
  rw [← h0]
  rfl
  intro ha
  rw [← ha]
  rfl
  intro hpa
  cases hna : z.natAbs
  rw [Int.natAbs_eq_zero] at hna
  simp
  rw [hna]
  rename_i n
  unfold neg_fit at hpa
  unfold neg_fit_part at hpa
  have hs : (z.sign = 0) ∨ (z.sign = 1) := by
    cases' z with a
    cases' a with b
    simp
    simp
    rename_i a
    simp at hpa
  have hs2 : (z.natAbs = z) := by
    exact (sign_nonneg_iff_natAbs_eq z).mpr hs
  rw [← hs2]
  rw [hna]
}

--#eval ((-4).sign)
--#eval (neg_fit (-4))

def spread_fun (z : ℤ) : ℕ := 2*z.natAbs + neg_fit z
#eval spread_fun (-12)

theorem t1 : spread_fun.Injective := by {
  unfold Function.Injective
  intro a1 a2
  unfold spread_fun
  intro h
  cases h1: neg_fit a1
  cases h2: neg_fit a2
  have h1b : a1.natAbs = a1 := by
    apply (neg_fit_iff_pos a1).mpr at h1
    exact h1
  have h2b : a2.natAbs = a2 := by
    apply (neg_fit_iff_pos a2).mpr at h2
    exact h2
  rw [h1] at h
  rw [h2] at h
  simp at h
  rw [← h1b]
  rw [← h2b]
  exact congrArg Nat.cast h
  rename_i n
  exfalso  --wish for WLOG symmetric argument
  have hzo : (neg_fit a2 = 0) ∨ (neg_fit a2 = 1) := by
    exact neg_fit_eq_zero_or_one a2
  cases' hzo with hzo
  rw [h2] at hzo
  absurd hzo
  simp
  rename_i ho
  rw [h1] at h
  rw [ho] at h
  simp at h
  have hodd : (Odd (2*a2.natAbs + 1)) := by
    simp
  rw [← h] at hodd
  absurd hodd
  simp
  rename_i n1
  cases h2: neg_fit a2 --start symmetric argument
  have hzo2 : (neg_fit a1 = 0) ∨ (neg_fit a1 = 1) := by
    exact neg_fit_eq_zero_or_one a1
  cases' hzo2 with hzo2
  rw [h1] at hzo2
  absurd hzo2
  simp
  rename_i ho2
  rw [h2] at h
  rw [ho2] at h
  simp at h
  have hodd2 : (Odd (2*a1.natAbs + 1)) := by
    simp
  rw [h] at hodd2
  absurd hodd2
  simp
  rename_i n  --below for ha1 copied later
  have ha1 : (a1 = a1.natAbs) ∨ (a1 = -↑(a1.natAbs)) := by
    apply Int.natAbs_eq a1
  have hn1 : neg_fit a1 = 1 := by
    have h01 : (neg_fit a1 = 0) ∨ (neg_fit a1 = 1) := by
      exact neg_fit_eq_zero_or_one a1
    cases' h01 with h01
    rw [h1] at h01
    simp at h01
    rename_i h01a
    exact h01a
  have hn2 : neg_fit a2 = 1 := by
    have h02 : (neg_fit a2 = 0) ∨ (neg_fit a2 = 1) := by
      exact neg_fit_eq_zero_or_one a2
    cases' h02 with h02
    rw [h2] at h02
    simp at h02
    rename_i h02a
    exact h02a
  have ha1not0 : ¬(neg_fit a1 = 0) := by
    rw [hn1]
    simp
  have ha1notl : ¬(a1 = a1.natAbs) := by
    contrapose ha1not0
    simp
    --simp at ha1not0
    apply (neg_fit_iff_pos a1).mp
    simp
    simp at ha1not0
    rw [← ha1not0]
  have ha1r : a1 = -↑a1.natAbs := by
    cases' ha1 with ha1
    rw [← ha1] at ha1notl
    absurd ha1notl
    rfl
    rename_i ha1
    exact ha1
  clear h1 h2 --copy part of above for ha2r
  have ha2 : (a2 = a2.natAbs) ∨ (a2 = -↑(a2.natAbs)) := by
    apply Int.natAbs_eq a2
  have ha2not0 : ¬(neg_fit a2 = 0) := by
    rw [hn2]
    simp
  have ha2notl : ¬(a2 = a2.natAbs) := by
    contrapose ha2not0
    simp
    simp at ha2not0
    apply (neg_fit_iff_pos a2).mp
    simp
    rw [← ha2not0]
  have ha2r : a2 = -↑a2.natAbs := by
    cases' ha2 with ha2
    rw [← ha2] at ha2notl
    absurd ha2notl
    rfl
    rename_i ha2
    exact ha2
  clear ha1 ha2 ha1notl ha2notl
  rw [hn1, hn2] at h
  have ha1rb : a1.natAbs = -a1 := by
    rw [flip_neg a1.natAbs a1]
    rw [← ha1r]
  have ha2rb : a2.natAbs = -a2 := by
    rw [flip_neg a2.natAbs a2]
    rw [← ha2r]
  simp at h
  apply nat_to_int_eq at h
  rw [ha1rb] at h
  rw [ha2rb] at h
  simp at h
  exact h
}

--We'll use triangular numbers for the diagonal function.
--worried about pathological division in ℕ but this doesn't solve it
lemma baby_Gauss_cast_rat (n : ℕ) : (↑(∑ x ∈ Finset.range (n+1), x) : ℚ) = (↑(n*(n+1)/2) : ℚ) := by {
  induction' n with n hn
  rfl
  rw [Finset.sum_range_succ]
  simp [add_comm]
  rw [hn]
  rw [← dist_cast_n_1]
  rw [← dist_cast_rat (n+1) (n*(n+1)/2)]
  calc
    (n+1 + n*(n+1)/2) = ((n+1)*(1 + ))


  --'norm_cast', 'rw [add_comm, add_comm (n * (n + 1)), add_comm n, add_comm (n * (n + 1)), ← add_assoc,\\n  add_div_right_comm, mul_add]', 'rw [← hn, Finset.add_sum_range_succ]', 'rw [add_comm]']\n"

  --,  ← Nat.cast_add_one, Nat.cast_add_one]
  --have hstep : ↑(∑ i ∈ Finset.range (n + 1 + 1), i)
  --= ↑(∑ i ∈ Finset.range (n + 1), i) + ↑(n+1) := by
  --  induction' n with n h2
  --  rfl
  --  rw [Finset.sum_range_succ]
  --rw [hstep]

  sorry

}
--below using lean3 Stackoverflow post from Kevin Buzzard
lemma baby_Gauss' (n : ℕ) : 2 * (∑ i ∈ Finset.range (n + 1), i) = n * (n + 1) := by {
  sorry
}

--def diag_fun (q : ℚ) : ℤ := q.sign*(q.num*q.num + (q.den-q.num))
--#eval diag_fun (4/2)

--instance : Countable Rat := inferInstance

variable (B : Set ℤ)

theorem int_countable : Set.Countable B := by {
  apply (Set.countable_iff_exists_injOn).mpr
  use spread_fun
  apply Set.injOn_of_injective
  apply t1
}

--  example (a b c d : ℝ) (h : c = b*a - d) (h' : d = a*b) : c = 0 := by {
--    calc
--      c = b*a - d   := by rw [h]
--      _ = b*a - a*b := by rw [h']
--      _ = 0         := by ring
--  }
  --Nat.not_succ_le_zero
    --apply Int.natAbs_negOfNat
rw [h2]
  rw [hn]
  have h3 : n*(n+1) = n*n + n*1 := by
    exact Nat.mul_add n n 1
  rw [h3]
  have h4 : (n+1)*(1 + (n+1)) = n+1 + (n+1)*(n+1) := by
    exact
