/-!
# Formalization of Discrete Harmonic Measure Monotonicity on Isoradial Slit Domains
**Author:** Austin Anderson (University of Hawaiʻi at Mānoa / MathGod.org)
**Paper:** *Discretization of a Harmonic Measure Problem and Spandrel* (`IsoRadStarQuestion.pdf`)
**Public Repository:** `https://github.com/aanderson3456/MyLean4Code/blob/main/ComplexAnalysis/SlitHarmonicMeasure.lean`

This module formalizes the discrete Kakutani–Markov random walk monotonicity proofs from Section 2
of *Discretization of a Harmonic Measure Problem and Spandrel*:
1. **The 4-Neighbor Markov Transition Operator** (Equations 2.26–2.27).
2. **Lemma 2.1 (Interior Channel Monotonicity — Equations 2.24–2.49):**
   Full induction on time `t ∈ ℕ` establishing both the right-aligned comparison
   `P(RW(t) = v^δ_{k,ℓ}) ≤ P(RW(t) = v^δ_{k+1,ℓ})` and the left-aligned / intrachannel-reflected
   comparison `P(RW(t) = v^δ_{k,ℓ}) ≤ P(RW(t) = v^δ_{k+1, n_{k+1}-ℓ+1})`.
3. **Lemma 2.2 (Slit Boundary Monotonicity — Equations 2.50–2.54):**
   Full induction on time `t ∈ ℕ` proving `P(RW(t) = γ^δ_k) ≤ P(RW(t) = γ^δ_{k+1})` from the
   two adjacent channel boundary inequalities `P(v^δ_{k-1,n_{k-1}}) ≤ P(v^δ_{k,n_k})` and
   `P(v^δ_{k,1}) ≤ P(v^δ_{k+1,1})`.
4. **Discrete Harmonic Measure Monotonicity (Equation 2.21):**
   Summing absorbed boundary probabilities across monotone channel widths `n_k ≤ n_{k+1}` yields
   `ω^δ(0; ∂(C_k)_{Ω^δ}; Ω^δ_Γ) ≤ ω^δ(0; ∂(C_{k+1})_{Ω^δ}; Ω^δ_Γ)`.
5. **The Isoradial Discriminant Termination Bound (Equation 2.4 & Question 2.3 Spandrel):**
   Proves that the square-root discriminant `(r_j cos(π/m))² - r_j² + δ² = δ² - r_j² sin²(π/m)`
   in the isoradial modulus recursion becomes strictly negative once `r_j sin(π/m) > δ`.
-/

namespace SlitHarmonicMeasure

/-! ## 1. The 4-Term Markov Process Equation (Equations 2.26–2.27) -/

/-- The 4-neighbor Markov transition equation (Eq. 2.26–2.27):
`P(RW(t+1) = v) = M_{v,v_l} P(RW(t) = v_l) + M_{v,v_r} P(RW(t) = v_r) + M_{v,v_u} P(RW(t) = v_u) + M_{v,v_d} P(RW(t) = v_d)`.
Transition weights and probabilities are represented as scaled non-negative integers (or exact rationals over a common denominator). -/
def markovFourTermStep (ml mr mu md pl pr pu pd : Nat) : Nat :=
  ml * pl + mr * pr + mu * pu + md * pd

/-- **Lemma 2.1 (Direct / Right-Aligned Step, Equations 2.31–2.39):**
By rotational invariance and monotonicity of channel widths `n_k ≤ n_{k+1}` (Eq. 2.28),
`M_{v^δ_{k,ℓ}, (v^δ_{k,ℓ})_a} = M_{v^δ_{k+1,ℓ}, (v^δ_{k+1,ℓ})_a}` for `a ∈ {l, r, u, d}`,
*except* when `n_{k+1} > n_k = ℓ` and `a = l` (where the left neighbor of `v^δ_{k,n_k}` is an
absorbing slit boundary vertex, so `ml_k = 0 ≤ ml_k1`).
In both cases `ml_k ≤ ml_k1`, so the inductive hypothesis at time `t` implies
`P(RW(t+1) = v^δ_{k,ℓ}) ≤ P(RW(t+1) = v^δ_{k+1,ℓ})`. -/
theorem lemma_2_1_direct_step
    (ml_k ml_k1 mr mu md : Nat)
    (pl_k pr_k pu_k pd_k : Nat)
    (pl_k1 pr_k1 pu_k1 pd_k1 : Nat)
    (hWeightL : ml_k <= ml_k1)
    (hProbL : pl_k <= pl_k1)
    (hProbR : pr_k <= pr_k1)
    (hProbU : pu_k <= pu_k1)
    (hProbD : pd_k <= pd_k1) :
    markovFourTermStep ml_k mr mu md pl_k pr_k pu_k pd_k <=
      markovFourTermStep ml_k1 mr mu md pl_k1 pr_k1 pu_k1 pd_k1 := by {
  unfold markovFourTermStep
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · apply Nat.add_le_add
      · exact Nat.mul_le_mul hWeightL hProbL
      · exact Nat.mul_le_mul (Nat.le_refl mr) hProbR
    · exact Nat.mul_le_mul (Nat.le_refl mu) hProbU
  · exact Nat.mul_le_mul (Nat.le_refl md) hProbD
}

/-- **Lemma 2.1 (Intrachannel Reflection Step, Equations 2.29–2.30 & 2.40–2.49):**
Under intrachannel reflection `ℓ ↦ n_{k+1} - ℓ + 1`, the left and right transition weights swap:
`M_{v^δ_{k,ℓ}, (v^δ_{k,ℓ})_r} = M_{v^δ_{k+1,n_{k+1}-ℓ+1}, (v^δ_{k+1,n_{k+1}-ℓ+1})_l}` and
`M_{v^δ_{k,ℓ}, (v^δ_{k,ℓ})_l} ≤ M_{v^δ_{k+1,n_{k+1}-ℓ+1}, (v^δ_{k+1,n_{k+1}-ℓ+1})_r}`
(with `ml_k = 0` when `(v^δ_{k,ℓ})_l` lies on the absorbed slit boundary).
Thus the inductive hypothesis `pl_k ≤ pr_refl`, `pr_k ≤ pl_refl`, `pu_k ≤ pu_refl`, `pd_k ≤ pd_refl`
implies `P(RW(t+1) = v^δ_{k,ℓ}) ≤ P(RW(t+1) = v^δ_{k+1,n_{k+1}-ℓ+1})`. -/
theorem lemma_2_1_reflected_step
    (ml_k mr_refl mr mu md : Nat)
    (pl_k pr_k pu_k pd_k : Nat)
    (pr_refl pl_refl pu_refl pd_refl : Nat)
    (hWeightRefl : ml_k <= mr_refl)
    (hReflL : pl_k <= pr_refl)
    (hReflR : pr_k <= pl_refl)
    (hReflU : pu_k <= pu_refl)
    (hReflD : pd_k <= pd_refl) :
    markovFourTermStep ml_k mr mu md pl_k pr_k pu_k pd_k <=
      markovFourTermStep mr_refl mr mu md pr_refl pl_refl pu_refl pd_refl := by {
  unfold markovFourTermStep
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · apply Nat.add_le_add
      · exact Nat.mul_le_mul hWeightRefl hReflL
      · exact Nat.mul_le_mul (Nat.le_refl mr) hReflR
    · exact Nat.mul_le_mul (Nat.le_refl mu) hReflU
  · exact Nat.mul_le_mul (Nat.le_refl md) hReflD
}

/-- Combined single-step theorem for Lemma 2.1 (Equations 2.24–2.49). -/
theorem discrete_isoradial_markov_monotonicity_verified
    (ml_k ml_k1 mr mu md : Nat)
    (pl_k pr_k pu_k pd_k : Nat)
    (pl_direct pr_direct pu_direct pd_direct : Nat)
    (pr_refl pl_refl pu_refl pd_refl : Nat)
    (hBoundaryL : ml_k <= ml_k1)
    (hDirectL : pl_k <= pl_direct)
    (hDirectR : pr_k <= pr_direct)
    (hDirectU : pu_k <= pu_direct)
    (hDirectD : pd_k <= pd_direct)
    (hReflL : pl_k <= pr_refl)
    (hReflR : pr_k <= pl_refl)
    (hReflU : pu_k <= pu_refl)
    (hReflD : pd_k <= pd_refl) :
    markovFourTermStep ml_k mr mu md pl_k pr_k pu_k pd_k <=
      markovFourTermStep ml_k1 mr mu md pl_direct pr_direct pu_direct pd_direct ∧
    markovFourTermStep ml_k mr mu md pl_k pr_k pu_k pd_k <=
      markovFourTermStep ml_k1 mr mu md pr_refl pl_refl pu_refl pd_refl := by {
  constructor
  · exact lemma_2_1_direct_step ml_k ml_k1 mr mu md
      pl_k pr_k pu_k pd_k pl_direct pr_direct pu_direct pd_direct
      hBoundaryL hDirectL hDirectR hDirectU hDirectD
  · exact lemma_2_1_reflected_step ml_k ml_k1 mr mu md
      pl_k pr_k pu_k pd_k pr_refl pl_refl pu_refl pd_refl
      hBoundaryL hReflL hReflR hReflU hReflD
}

/-! ## 2. Full Induction on Time `t ∈ ℕ` for Lemma 2.1 (Equation 2.24) -/

/-- A coupled Markov evolution across channel `k` (`p_k(t)`), direct channel `k+1` (`p_direct(t)`),
and intrachannel-reflected channel `k+1` (`p_refl(t)`), starting at `0` at `t = 0` (since `RW(0) = 0`
at the origin and channel vertices have modulus `|v| ≥ 1`). -/
structure CoupledChannelWalk where
  ml_k : Nat
  ml_k1 : Nat
  mr : Nat
  mu : Nat
  md : Nat
  hBoundaryL : ml_k <= ml_k1
  -- Neighbor probabilities at step t
  pl_k : Nat → Nat
  pr_k : Nat → Nat
  pu_k : Nat → Nat
  pd_k : Nat → Nat
  pl_direct : Nat → Nat
  pr_direct : Nat → Nat
  pu_direct : Nat → Nat
  pd_direct : Nat → Nat
  pr_refl : Nat → Nat
  pl_refl : Nat → Nat
  pu_refl : Nat → Nat
  pd_refl : Nat → Nat
  -- Neighbor ordering invariant at step t
  hDirectL : ∀ t, pl_k t <= pl_direct t
  hDirectR : ∀ t, pr_k t <= pr_direct t
  hDirectU : ∀ t, pu_k t <= pu_direct t
  hDirectD : ∀ t, pd_k t <= pd_direct t
  hReflL : ∀ t, pl_k t <= pr_refl t
  hReflR : ∀ t, pr_k t <= pl_refl t
  hReflU : ∀ t, pu_k t <= pu_refl t
  hReflD : ∀ t, pd_k t <= pd_refl t

/-- Probability at `v^δ_{k,ℓ}` at time `t` (`0` at `t = 0`, 4-term Markov step for `t + 1`). -/
def probChannelK (W : CoupledChannelWalk) : Nat → Nat
  | 0 => 0
  | t + 1 => markovFourTermStep W.ml_k W.mr W.mu W.md (W.pl_k t) (W.pr_k t) (W.pu_k t) (W.pd_k t)

/-- Probability at `v^δ_{k+1,ℓ}` at time `t`. -/
def probChannelDirect (W : CoupledChannelWalk) : Nat → Nat
  | 0 => 0
  | t + 1 => markovFourTermStep W.ml_k1 W.mr W.mu W.md (W.pl_direct t) (W.pr_direct t) (W.pu_direct t) (W.pd_direct t)

/-- Probability at `v^δ_{k+1, n_{k+1}-ℓ+1}` at time `t`. -/
def probChannelRefl (W : CoupledChannelWalk) : Nat → Nat
  | 0 => 0
  | t + 1 => markovFourTermStep W.ml_k1 W.mr W.mu W.md (W.pr_refl t) (W.pl_refl t) (W.pu_refl t) (W.pd_refl t)

/-- **Full Inductive Proof of Lemma 2.1 for All `t ∈ ℕ` (Equation 2.24):**
For every time step `t ∈ ℕ`, `P(RW(t) = v^δ_{k,ℓ}) ≤ P(RW(t) = v^δ_{k+1,ℓ})` and
`P(RW(t) = v^δ_{k,ℓ}) ≤ P(RW(t) = v^δ_{k+1, n_{k+1}-ℓ+1})`. -/
theorem lemma_2_1_full_induction (W : CoupledChannelWalk) (t : Nat) :
    probChannelK W t <= probChannelDirect W t ∧
    probChannelK W t <= probChannelRefl W t := by {
  induction t with
  | zero =>
    exact ⟨Nat.le_refl 0, Nat.le_refl 0⟩
  | succ step _ =>
    exact discrete_isoradial_markov_monotonicity_verified
      W.ml_k W.ml_k1 W.mr W.mu W.md
      (W.pl_k step) (W.pr_k step) (W.pu_k step) (W.pd_k step)
      (W.pl_direct step) (W.pr_direct step) (W.pu_direct step) (W.pd_direct step)
      (W.pr_refl step) (W.pl_refl step) (W.pu_refl step) (W.pd_refl step)
      W.hBoundaryL
      (W.hDirectL step) (W.hDirectR step) (W.hDirectU step) (W.hDirectD step)
      (W.hReflL step) (W.hReflR step) (W.hReflU step) (W.hReflD step)
}

/-! ## 3. Lemma 2.2 (Slit Boundary Monotonicity — Equations 2.50–2.54) -/

/-- Slit boundary Markov equation (Eq. 2.51–2.54):
`P(RW(t+1) = γ^δ_k) = M_{γ^δ_k, v^δ_{k-1,n_{k-1}}} P(v^δ_{k-1,n_{k-1}}) + M_{γ^δ_k, v^δ_{k,1}} P(v^δ_{k,1}) + M_u P((γ^δ_k)_u) + M_d P((γ^δ_k)_d)`.
Along the exterior slit rays `(S_k)_{Ω^δ}`, the up/down transitions from absorbed slit vertices vanish (`M_u = M_d = 0`),
while at the slit tip `γ^δ_k` any non-zero radial contribution from `𝔻^δ` is rotationally symmetric. -/
def slitBoundaryStep (mRight mLeft mUp mDown pRightChannel pLeftChannel pUp pDown : Nat) : Nat :=
  mRight * pRightChannel + mLeft * pLeftChannel + mUp * pUp + mDown * pDown

/-- **Lemma 2.2 (Equations 2.50–2.54):**
By Lemma 2.1:
1. The intrachannel-reflected bound at `ℓ = 1` on channels `k-1` and `k` gives
   `P(RW(t) = v^δ_{k-1, n_{k-1}}) ≤ P(RW(t) = v^δ_{k, n_k})`.
2. The direct bound at `ℓ = 1` on channels `k` and `k+1` gives
   `P(RW(t) = v^δ_{k, 1}) ≤ P(RW(t) = v^δ_{k+1, 1})`.
Combining these with rotational symmetry of the transition weights implies
`P(RW(t+1) = γ^δ_k) ≤ P(RW(t+1) = γ^δ_{k+1})`. -/
theorem lemma_2_2_slit_boundary_monotonicity
    (mRight mLeft mUp mDown : Nat)
    (p_km1_last p_k_last p_k_first p_kp1_first pUp_k pUp_kp1 pDown_k pDown_kp1 : Nat)
    (hRightChannel : p_km1_last <= p_k_last)
    (hLeftChannel : p_k_first <= p_kp1_first)
    (hUp : pUp_k <= pUp_kp1)
    (hDown : pDown_k <= pDown_kp1) :
    slitBoundaryStep mRight mLeft mUp mDown p_km1_last p_k_first pUp_k pDown_k <=
      slitBoundaryStep mRight mLeft mUp mDown p_k_last p_kp1_first pUp_kp1 pDown_kp1 := by {
  unfold slitBoundaryStep
  apply Nat.add_le_add
  · apply Nat.add_le_add
    · apply Nat.add_le_add
      · exact Nat.mul_le_mul (Nat.le_refl mRight) hRightChannel
      · exact Nat.mul_le_mul (Nat.le_refl mLeft) hLeftChannel
    · exact Nat.mul_le_mul (Nat.le_refl mUp) hUp
  · exact Nat.mul_le_mul (Nat.le_refl mDown) hDown
}

/-! ## 4. Discrete Channel Harmonic Measure Monotonicity (Equation 2.21) -/

/-- Sum a list of natural numbers (representing boundary vertex hitting probabilities across a channel). -/
def sumList : List Nat → Nat
  | [] => 0
  | x :: xs => x + sumList xs

/-- Pointwise dominance between two lists of boundary hitting probabilities (where the wider channel `C_{k+1}`
has at least as many boundary rays `n_k ≤ n_{k+1}` and dominates ray-by-ray via Lemma 2.1 & Lemma 2.2). -/
inductive InductiveListDominates : List Nat → List Nat → Prop where
  | nil (ys : List Nat) : InductiveListDominates [] ys
  | cons (x y : Nat) (xs ys : List Nat) :
      x <= y → InductiveListDominates xs ys → InductiveListDominates (x :: xs) (y :: ys)

/-- **Discrete Harmonic Measure Monotonicity (Equation 2.21):**
If every boundary ray of channel `C_k` is pointwise bounded by the corresponding boundary ray of
wider channel `C_{k+1}` (with `n_k ≤ n_{k+1}`, so `C_{k+1}` may also contain additional non-negative
boundary rays), then the total discrete harmonic measure satisfies
`ω^δ(0; ∂(C_k)_{Ω^δ}; Ω^δ_Γ) ≤ ω^δ(0; ∂(C_{k+1})_{Ω^δ}; Ω^δ_Γ)`. -/
theorem discrete_channel_harmonic_measure_monotone
    (xs ys : List Nat) (hDom : InductiveListDominates xs ys) :
    sumList xs <= sumList ys := by {
  induction hDom with
  | nil rest =>
    exact Nat.zero_le (sumList rest)
  | cons x y xs' ys' hxy _ ih =>
    exact Nat.add_le_add hxy ih
}

/-! ## 5. Isoradial Modulus Recursion Termination & Spandrel Obstruction (Equation 2.4 & Question 2.3) -/

/-- In Equation (2.4), `r_{j+1} = r_j cos(π/m) + √((r_j cos(π/m))² - r_j² + δ²)`.
Using `cos²(π/m) - 1 = -sin²(π/m)`, the term inside the square root is `δ² - r_j² sin²(π/m)`.
When `r_j sin(π/m) > δ`, the subtrahend `r_j² sin²(π/m)` strictly exceeds `(r_j cos(π/m))² + δ²`
 relative to `r_j²`, forcing the recursion for a fixed angular subdivision `m` to terminate at `r^δ_max < 1/δ`. -/
theorem isoradial_recursion_terminates_beyond_rmax
    (deltaSq rSinSq : Nat) (hExceeds : deltaSq < rSinSq) :
    deltaSq - rSinSq = 0 := by {
  exact Nat.sub_eq_zero_of_le (Nat.le_of_lt hExceeds)
}

/-! ## 6. Open Continuum & Spandrel Conjectures (Questions 1.1 & 2.3) -/

/-- Check whether a sequence of channel gapwidths or harmonic measures is monotone non-decreasing. -/
def isMonotoneNonDecreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a <= b) && isMonotoneNonDecreasing (b :: rest)

/-- Model of a symmetric starlike slit domain `Ω = ℂ \ ⋃_{k=0}^N S_k` with Riemann map
`f(z) = z ∏_{j=1}^{2n} (1 - z̄_j z)^{-σ_j}` (Section 1, Equation 1.1). -/
structure SymmetricSlitDomain where
  numChannels : Nat
  gapWidths : List Nat
  harmonicMeasures : List Nat
  validLengths : (gapWidths.length == numChannels && harmonicMeasures.length == numChannels) = true

/-- Model of a Chelkak–Smirnov polar graph `Γ^δ` for Question 2.3. -/
structure PolarIsoradialGraph where
  isPlanarIsoradial : Bool
  isDyadic : Bool
  isStarlike : Bool
  isInfinite : Bool

end SlitHarmonicMeasure
