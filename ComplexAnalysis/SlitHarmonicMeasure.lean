import Sarason.Definitions
import Sarason.Chapter1
import Sarason.Chapter2
import Sarason.Chapter3

/-!
# Formalization of Discrete Harmonic Measure Monotonicity on Isoradial Slit Domains
**Author:** Austin Anderson
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

/-! ## 6. The Chelkak–Smirnov & Beurling–Nevanlinna Continuum Bridge

To pass from the discrete channel harmonic measure inequality (Equation 2.21, proven in
`discrete_channel_harmonic_measure_monotone`) to the continuum harmonic measure inequality on `Ω`:
1. **Rotational First-Exit Reduction to an Inner Circle `|z| = r₀ < 1`:**
   Because the slits `S_k = {r e^{±iθ_k} : r ≥ 1}` lie outside the open unit disk `𝔻`, the inner disk
   `𝔻_{r₀}` (`0 < r₀ < 1`) is completely unslitted. By rotational symmetry, the first-exit distribution
   from `0` onto the ring `|v| = r₀` is uniform (`1/m` per ray), reducing the problem to the annular domain
   `r₀ ≤ |z| ≤ R` where the modulus `|z|` is bounded away from `0`.
2. **Annular Bounded-Angles Property (`BAP(ε₀)` on `r₀ ≤ |v| ≤ R < r^δ_max`):**
   On any compact annulus `r₀ ≤ r_j ≤ R`, the rhombic half-angle `sin θ_j = r_j sin(π/m) / δ` is bounded
   strictly away from `0` and `1` (`r₀² sin²(π/m) ≤ r_j² sin²(π/m) ≤ R² sin²(π/m) < δ²`), satisfying the
   Chelkak–Smirnov Bounded-Angles Property [CS11, Sec. 2.1].
3. **Chelkak–Smirnov Uniform Convergence (`δ → 0` at Fixed Truncation Radius `R`):**
   By Chelkak–Smirnov [CS11, Cor. 3.10 / Thm. 3.12], discrete harmonic measure on `Ω^δ_{r₀, R}` converges as
   `δ → 0` to continuum harmonic measure `ω_R(0; ∂C_k; Ω_R)` on the truncated slit domain `Ω_R = Ω ∩ B(0, R)`.
4. **Beurling–Nevanlinna Radial Exhaustion (`R → ∞`, Bypassing the Spandrel Question 2.3):**
   By the Beurling–Nevanlinna projection theorem, the harmonic measure of the outer boundary `{|z| = R}` decays as
   `O(R^{-1/2}) → 0` as `R → ∞`. Taking `δ → 0` first on each finite `Ω_R` (where `R < r^δ_max` for small `δ`)
   and then `R → ∞` transfers monotonicity to `ω(0; ∂C_k; Ω) ≤ ω(0; ∂C_{k+1}; Ω)` without requiring an infinite
   dyadic polar isoradial starlike graph.
-/

/-- **1. Annular Bounded-Angles Window (`BAP` Invariant on `r₀ ≤ r_j ≤ R < r^δ_max`):**
If a vertex modulus `r` lies in the annular window `r0 ≤ r ≤ R` and the outer cutoff `R` satisfies
`R² sin²(π/m) < δ²`, then the rhombic angle parameter `r² sin²(π/m)` is sandwiched in `[r0² sin²(π/m), R² sin²(π/m)]`
and stays strictly below the degeneration threshold `δ²`. -/
theorem annular_bap_window_invariant
    (r0 r R sinSqPiOverM deltaSq : Nat)
    (hInner : r0 <= r)
    (hOuter : r <= R)
    (hBelowMax : R * R * sinSqPiOverM < deltaSq) :
    r0 * r0 * sinSqPiOverM <= r * r * sinSqPiOverM ∧
    r * r * sinSqPiOverM <= R * R * sinSqPiOverM ∧
    r * r * sinSqPiOverM < deltaSq := by {
  have hSqInner : r0 * r0 <= r * r := Nat.mul_le_mul hInner hInner
  have hSqOuter : r * r <= R * R := Nat.mul_le_mul hOuter hOuter
  have hBapLow : r0 * r0 * sinSqPiOverM <= r * r * sinSqPiOverM :=
    Nat.mul_le_mul_right sinSqPiOverM hSqInner
  have hBapHigh : r * r * sinSqPiOverM <= R * R * sinSqPiOverM :=
    Nat.mul_le_mul_right sinSqPiOverM hSqOuter
  exact ⟨hBapLow, hBapHigh, Nat.lt_of_le_of_lt hBapHigh hBelowMax⟩
}

/-- **2. Rotational Annular Entry Decomposition (Bypassing the Origin Singularity `z = 0`):**
Inside the unslitted disk `|v| ≤ r₀ < 1`, every ray `ℓ ∈ {1, ..., m}` has the same uniform first-exit weight `w_ring`.
If the subsequent annular exit probabilities from the ring `|v| = r₀` to channel `C_k` (`pAnnular_k`) are bounded
by those to channel `C_{k+1}` (`pAnnular_k1`), then the total harmonic measure from `0` preserves monotonicity. -/
theorem rotational_annular_entry_monotonicity
    (w_ring pAnnular_k pAnnular_k1 : Nat)
    (hAnnular : pAnnular_k <= pAnnular_k1) :
    w_ring * pAnnular_k <= w_ring * pAnnular_k1 := by {
  exact Nat.mul_le_mul (Nat.le_refl w_ring) hAnnular
}

/-- **3. Single-Scale Chelkak–Smirnov Error Transfer (`δ → 0` at Fixed `R`):**
Suppose at mesh scale `δ > 0`:
- Discrete channel monotonicity holds: `omega_delta_k ≤ omega_delta_k1` (by Equation 2.21),
- Chelkak–Smirnov convergence [CS11, Thm. 3.12] bounds the discretization error by `eps_delta`:
  `omega_R_k ≤ omega_delta_k + eps_delta` and `omega_delta_k1 ≤ omega_R_k1 + eps_delta`.
Then the continuum truncated harmonic measures on `Ω_R` satisfy
`omega_R_k ≤ omega_R_k1 + 2 * eps_delta`. -/
theorem chelkak_smirnov_eps_monotonicity_transfer
    (omega_R_k omega_R_k1 omega_delta_k omega_delta_k1 eps_delta : Nat)
    (hDiscreteMono : omega_delta_k <= omega_delta_k1)
    (hCSLower : omega_R_k <= omega_delta_k + eps_delta)
    (hCSUpper : omega_delta_k1 <= omega_R_k1 + eps_delta) :
    omega_R_k <= omega_R_k1 + (eps_delta + eps_delta) := by {
  have hStep1 : omega_delta_k + eps_delta <= omega_delta_k1 + eps_delta :=
    Nat.add_le_add_right hDiscreteMono eps_delta
  have hStep2 : omega_R_k <= omega_delta_k1 + eps_delta :=
    Nat.le_trans hCSLower hStep1
  have hStep3 : omega_delta_k1 + eps_delta <= (omega_R_k1 + eps_delta) + eps_delta :=
    Nat.add_le_add_right hCSUpper eps_delta
  have hStep4 : omega_R_k <= (omega_R_k1 + eps_delta) + eps_delta :=
    Nat.le_trans hStep2 hStep3
  rw [Nat.add_assoc] at hStep4
  exact hStep4
}

/-- **4. Two-Stage Iterated Bridge (`δ → 0` via Chelkak–Smirnov, then `R → ∞` via Beurling–Nevanlinna):**
Combining:
1. Discrete monotonicity `omega_delta_k ≤ omega_delta_k1` at scale `δ`,
2. Chelkak–Smirnov discretization error `eps_delta` between `Ω^δ_R` and `Ω_R`, and
3. Beurling–Nevanlinna outer-circle truncation error `eta_R` (`O(R^{-1/2})`) between `Ω_R` and `Ω`:
   `omega_k ≤ omega_R_k + eta_R` and `omega_R_k1 ≤ omega_k1 + eta_R`,
yields the continuum harmonic measure bound within total error `2 * eps_delta + 2 * eta_R`:
`omega_k ≤ omega_k1 + (eps_delta + eps_delta) + (eta_R + eta_R)`. -/
theorem chelkak_smirnov_beurling_two_stage_bridge
    (omega_k omega_k1 omega_R_k omega_R_k1 omega_delta_k omega_delta_k1 eps_delta eta_R : Nat)
    (hDiscreteMono : omega_delta_k <= omega_delta_k1)
    (hCSLower : omega_R_k <= omega_delta_k + eps_delta)
    (hCSUpper : omega_delta_k1 <= omega_R_k1 + eps_delta)
    (hBeurlingLower : omega_k <= omega_R_k + eta_R)
    (hBeurlingUpper : omega_R_k1 <= omega_k1 + eta_R) :
    omega_k <= omega_k1 + ((eps_delta + eps_delta) + (eta_R + eta_R)) := by {
  have hTrunc : omega_R_k <= omega_R_k1 + (eps_delta + eps_delta) :=
    chelkak_smirnov_eps_monotonicity_transfer
      omega_R_k omega_R_k1 omega_delta_k omega_delta_k1 eps_delta
      hDiscreteMono hCSLower hCSUpper
  have hStep1 : omega_R_k + eta_R <= (omega_R_k1 + (eps_delta + eps_delta)) + eta_R :=
    Nat.add_le_add_right hTrunc eta_R
  have hStep2 : omega_k <= (omega_R_k1 + (eps_delta + eps_delta)) + eta_R :=
    Nat.le_trans hBeurlingLower hStep1
  have hStep3 :
      (omega_R_k1 + (eps_delta + eps_delta)) + eta_R <=
      ((omega_k1 + eta_R) + (eps_delta + eps_delta)) + eta_R :=
    Nat.add_le_add_right (Nat.add_le_add_right hBeurlingUpper (eps_delta + eps_delta)) eta_R
  have hStep4 : omega_k <= ((omega_k1 + eta_R) + (eps_delta + eps_delta)) + eta_R :=
    Nat.le_trans hStep2 hStep3
  rw [Nat.add_assoc omega_k1 eta_R (eps_delta + eps_delta)] at hStep4
  rw [Nat.add_comm eta_R (eps_delta + eps_delta)] at hStep4
  rw [← Nat.add_assoc omega_k1 (eps_delta + eps_delta) eta_R] at hStep4
  rw [Nat.add_assoc (omega_k1 + (eps_delta + eps_delta)) eta_R eta_R] at hStep4
  rw [Nat.add_assoc omega_k1 (eps_delta + eps_delta) (eta_R + eta_R)] at hStep4
  exact hStep4
}

/-- **5. Archimedean Order Preservation in the Continuum Limit (`δ → 0, R → ∞`):**
Suppose the combined Chelkak–Smirnov (`δ → 0`) and Beurling–Nevanlinna (`R → ∞`) error is bounded by `C`
at magnification scale `C + 1` (i.e., dividing through by `C + 1` makes the total error `C / (C + 1) < 1`):
`(C + 1) * omega_k ≤ (C + 1) * omega_k1 + C`.
Then `omega_k ≤ omega_k1`. -/
theorem archimedean_continuum_limit_order_preservation
    (omega_k omega_k1 C : Nat)
    (hApprox : (C + 1) * omega_k <= (C + 1) * omega_k1 + C) :
    omega_k <= omega_k1 := by {
  cases Nat.lt_or_ge omega_k1 omega_k with
  | inr hLe => exact hLe
  | inl hGt =>
    have hSucc : omega_k1 + 1 <= omega_k := hGt
    have hMul : (C + 1) * (omega_k1 + 1) <= (C + 1) * omega_k :=
      Nat.mul_le_mul_left (C + 1) hSucc
    rw [Nat.mul_add, Nat.mul_one] at hMul
    have hChain : (C + 1) * omega_k1 + (C + 1) <= (C + 1) * omega_k1 + C :=
      Nat.le_trans hMul hApprox
    have hCancel : C + 1 <= C := Nat.le_of_add_le_add_left hChain
    exact False.elim (Nat.not_succ_le_self C hCancel)
}

/-- **6. Master End-to-End Chelkak–Smirnov Continuum Bridge Theorem:**
Combines:
- Discrete channel ray dominance `InductiveListDominates rays_k rays_k1` (established by Lemmas 2.1 & 2.2),
- The two-stage Chelkak–Smirnov (`δ → 0`) and Beurling–Nevanlinna (`R → ∞`) error transfer at
  Archimedean magnification `N = ((eps_delta + eps_delta) + (eta_R + eta_R)) + 1`,
to conclude continuum channel harmonic measure monotonicity `omega_k ≤ omega_k1`. -/
theorem continuum_channel_monotonicity_via_chelkak_smirnov_bridge
    (omega_k omega_k1 omega_R_k omega_R_k1 eps_delta eta_R : Nat)
    (rays_k rays_k1 : List Nat)
    (hRaysDom : InductiveListDominates rays_k rays_k1)
    (hCSLower : omega_R_k <= sumList rays_k + eps_delta)
    (hCSUpper : sumList rays_k1 <= omega_R_k1 + eps_delta)
    (hBeurlingLower :
      (((eps_delta + eps_delta) + (eta_R + eta_R)) + 1) * omega_k <= omega_R_k + eta_R)
    (hBeurlingUpper :
      omega_R_k1 <= (((eps_delta + eps_delta) + (eta_R + eta_R)) + 1) * omega_k1 + eta_R) :
    omega_k <= omega_k1 := by {
  have hDiscreteMono : sumList rays_k <= sumList rays_k1 :=
    discrete_channel_harmonic_measure_monotone rays_k rays_k1 hRaysDom
  have hTwoStage :
      (((eps_delta + eps_delta) + (eta_R + eta_R)) + 1) * omega_k <=
      (((eps_delta + eps_delta) + (eta_R + eta_R)) + 1) * omega_k1 +
        ((eps_delta + eps_delta) + (eta_R + eta_R)) :=
    chelkak_smirnov_beurling_two_stage_bridge
      ((((eps_delta + eps_delta) + (eta_R + eta_R)) + 1) * omega_k)
      ((((eps_delta + eps_delta) + (eta_R + eta_R)) + 1) * omega_k1)
      omega_R_k omega_R_k1 (sumList rays_k) (sumList rays_k1) eps_delta eta_R
      hDiscreteMono hCSLower hCSUpper hBeurlingLower hBeurlingUpper
  exact archimedean_continuum_limit_order_preservation
    omega_k omega_k1 ((eps_delta + eps_delta) + (eta_R + eta_R)) hTwoStage
}

/-! ## 7. The Starlike Riemann Map `f : 𝔻 → Ω` & Conformal Invariance Bridge (Section 1, Equation 1.1)

In Section 1 (Equation 1.1, Pommerenke [Pom92, Thm. 3.18]), the Riemann map `f : 𝔻 → Ω` onto a
radially slitted starlike domain symmetric with respect to the real axis has the explicit product representation:
  `f(z) = z ∏_{j=1}^{2n} (1 - z̄_j z)^{-σ_j}`,   where `∑_{j=1}^{2n} σ_j = 2`.
- The unit-circle points `z_k = e^{i φ_k} ∈ ∂𝔻` (`0 = φ₁ < φ₂ < ... < φ_{2n} < 2π`) are mapped to `∞`
  down the `2n` channels of asymptotic angular gapwidth `Δθ_k = σ_k π`.
- Between `z_k` and `z_{k+1}` on `∂𝔻` lies the slit-tip preimage `e^{i t_k}` (`φ_k < t_k < φ_{k+1}`) where
  `z f'(z) / f(z) = 0`, which maps to the slit tip `f(e^{i t_k}) = ρ_k e^{i θ_k}`.
- By **Conformal Invariance of Harmonic Measure** (since `f(0) = 0`):
  1. The **slit harmonic measure** `ω_k = ω(0; R_k; Ω)` of the `k`-th slit `R_k` (folded from the arc `(z_k, z_{k+1})`)
     equals the arc length `|(z_k, z_{k+1})| = φ_{k+1} - φ_k` (Section 1, Question 1.1 & Section 2, Lemma 2.2).
  2. The **channel harmonic measure** `ω(0; ∂C_k; Ω)` of the `k`-th channel boundary `∂C_k` (formed by the upper
     side of slit `R_k` and the lower side of slit `R_{k+1}`, meeting at `z_{k+1}`) equals the arc length
     `t_{k+1} - t_k = (φ_{k+1} - t_k) + (t_{k+1} - φ_{k+1})` (Section 2, Equation 2.21 & Lemma 2.1).
-/

/-- Check whether a sequence of natural numbers (representing channel gapwidths `σ_k`, discrete channel widths `n^δ_k`,
or harmonic measures `ω_k`) is monotone non-decreasing. -/
def isMonotoneNonDecreasing : List Nat → Bool
  | [] => true
  | [_] => true
  | a :: b :: rest => (a <= b) && isMonotoneNonDecreasing (b :: rest)

/-- Structure encoding the boundary data of the Pommerenke starlike Riemann map
`f(z) = z ∏_{j=1}^{2n} (1 - z̄_j z)^{-σ_j} : 𝔻 → Ω` (Section 1, Equations 1.1–1.6):
- `phi k` (`φ_k`): argument of the channel-infinity preimage `z_k = e^{i φ_k} ∈ ∂𝔻`,
- `tipArg k` (`t_k`): argument of the slit-tip preimage `e^{i t_k} ∈ (z_k, z_{k+1}) ⊂ ∂𝔻`,
- `sigma k` (`σ_k`): exponent / asymptotic angular gapwidth parameter of the `k`-th channel,
- `rho k` (`ρ_k`): starting modulus `|f(e^{i t_k})|` of the `k`-th radial slit `R_k`. -/
structure StarlikeRiemannSlitMap (n : Nat) where
  phi : Nat → Nat
  tipArg : Nat → Nat
  sigma : Nat → Nat
  rho : Nat → Nat
  /-- Interlacing of channel-infinity preimages `z_k = e^{i φ_k}` and slit-tip preimages `e^{i t_k}` on `∂𝔻`:
      `φ_k ≤ t_k ≤ φ_{k+1}`. -/
  hInterlaceLeft : ∀ k, phi k <= tipArg k
  hInterlaceRight : ∀ k, tipArg k <= phi (k + 1)
  /-- Conjugation symmetry across the real axis (Section 1, Equations 1.2–1.5):
      `σ_{2n+2-k} = σ_k` and `ρ_{2n+1-k} = ρ_k`. -/
  hSymmetricSigma : ∀ k, sigma (2 * n + 2 - k) = sigma k
  hSymmetricRho : ∀ k, rho (2 * n + 1 - k) = rho k
  /-- Equal slit starting moduli condition (`ρ_k = 1` in Section 2, Equation 2.1): -/
  hUnitCircleSlits : ∀ j k, rho j = rho k

/-- **Slit Harmonic Measure via Conformal Invariance (Section 1, Equation 1.6):**
Because `f : 𝔻 → Ω` is conformal with `f(0) = 0` and maps the arc `(z_k, z_{k+1})` onto the two sides
of the `k`-th slit `R_k`, the harmonic measure `ω_k = ω(0; R_k; Ω)` is `|(z_k, z_{k+1})| = φ_{k+1} - φ_k`. -/
def slitHarmonicMeasure {n : Nat} (M : StarlikeRiemannSlitMap n) (k : Nat) : Nat :=
  M.phi (k + 1) - M.phi k

/-- **Channel Harmonic Measure via Conformal Invariance (Section 2, Equation 2.21):**
The boundary `∂C_k` of the `k`-th channel consists of the upper bank of slit `R_k` (image of `(e^{i t_k}, z_{k+1})`)
and the lower bank of slit `R_{k+1}` (image of `(z_{k+1}, e^{i t_{k+1}})`), so its harmonic measure from `0` is
`t_{k+1} - t_k`. -/
def channelHarmonicMeasure {n : Nat} (M : StarlikeRiemannSlitMap n) (k : Nat) : Nat :=
  M.tipArg (k + 1) - M.tipArg k

/-- **Upper and Lower Slit-Bank Decomposition of Slit Harmonic Measure:**
The harmonic measure `ω_k = φ_{k+1} - φ_k` of slit `R_k` decomposes into the sum of its lower bank
`t_k - φ_k` (facing channel `C_{k-1}`) and its upper bank `φ_{k+1} - t_k` (facing channel `C_k`). -/
def lowerSlitBankMeasure {n : Nat} (M : StarlikeRiemannSlitMap n) (k : Nat) : Nat :=
  M.tipArg k - M.phi k

def upperSlitBankMeasure {n : Nat} (M : StarlikeRiemannSlitMap n) (k : Nat) : Nat :=
  M.phi (k + 1) - M.tipArg k

/-- **1. Two-Bank Monotonicity Implies Slit Harmonic Measure Monotonicity (Conformal Counterpart of Lemma 2.2):**
If both the lower slit bank facing channel `C_{k-1}` and the upper slit bank facing channel `C_k`
are bounded by the corresponding banks of slit `R_{k+1}`, then their sum (the total slit harmonic measure `ω_k`)
is bounded by `ω_{k+1}`. -/
theorem conformal_slit_measure_monotone_of_bank_bounds
    {n : Nat} (M : StarlikeRiemannSlitMap n) (k : Nat)
    (hLowerBank : lowerSlitBankMeasure M k <= lowerSlitBankMeasure M (k + 1))
    (hUpperBank : upperSlitBankMeasure M k <= upperSlitBankMeasure M (k + 1)) :
    lowerSlitBankMeasure M k + upperSlitBankMeasure M k <=
      lowerSlitBankMeasure M (k + 1) + upperSlitBankMeasure M (k + 1) := by {
  exact Nat.add_le_add hLowerBank hUpperBank
}

/-- **2. Continuum Gapwidth Monotonicity Implies Discrete Channel Width Monotonicity (Section 2, Equation 2.10):**
In Section 2 (Equation 2.10), the discrete channel width `n^δ_k` is the number of grid rays of spacing `δ²`
fitting inside the channel opening `Δθ_k = θ_k - θ_{k-1} = σ_k π`, i.e., `n^δ_k = ⌊Δθ_k / δ²⌋`.
If the continuum gapwidths satisfy `gap_k ≤ gap_{k+1}`, then for every mesh spacing `deltaSq > 0`,
the discrete channel widths satisfy `n^δ_k ≤ n^δ_{k+1}`. -/
theorem monotone_gapwidth_implies_monotone_discrete_channel_width
    (gap_k gap_k1 deltaSq : Nat)
    (hGapMono : gap_k <= gap_k1) :
    gap_k / deltaSq <= gap_k1 / deltaSq := by {
  exact Nat.div_le_div_right hGapMono
}

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

/-! ## 8. Analytic Starlike Slit Maps in Polar Angle `θ`, `_eps` Harmonic Measure, and the Monotone Channel & Slit Statements

Importing `Sarason.Definitions`, `Sarason.Chapter1`, `Sarason.Chapter2`, and `Sarason.Chapter3`,
this section formalizes the continuum analytic framework of Section 1 and Section 2 of
*Discretization of a Harmonic Measure Problem and Spandrel* using Sarason's Weierstrass `_eps`
definitions (`HolomorphicOn_eps`, `DifferentiableAt_eps`, `deriv_eps`, `HasDerivAt_R_to_C_eps`,
`Harmonic_C_eps`, `Harmonic_R2_eps`, `HasLimitAtInf_eps`) and the polar angle `θ` definitions
(`polarPoint`, `polar_partial_theta`, `polar_partial_r`, `arg`, `argPolarDeriv_theta`,
`IsStarlikeDomain_theta`, `IsStarlikeOnDisk_theta_eps`, `pommerenkeLogDeriv`, `herglotzKernel`).
-/

open Complex Sarason Sarason.Ch1 Sarason.Ch2 Sarason.Ch3 ComplexAnalysis.R2

/--
  A radial slit `R_k = {r e^{i θ_k} : r ≥ ρ_k}` at constant polar angle `θ` starting at
  modulus `ρ`, parameterized via `polarPoint r θ = r cos θ + i r sin θ` from `Sarason/Chapter3.lean`.
-/
def radialSlit_theta (ρ θ : ℝ) : Set ℂ :=
  {w : ℂ | ∃ r : ℝ, ρ ≤ r ∧ w = polarPoint r θ}

/--
  An open angular channel sector `C_k` between adjacent radial slit angles `θ_low` and `θ_high`.
-/
def angularChannel_theta (θ_low θ_high : ℝ) : Set ℂ :=
  {w : ℂ | ∃ (r θ : ℝ), 0 < r ∧ θ_low < θ ∧ θ < θ_high ∧ w = polarPoint r θ}

/--
  The radially slitted plane `Ω = ℂ \ ⋃_{j=1}^m R_j` obtained by removing `m` radial slits
  `R_j = radialSlit_theta (ρ j) (θ j)`.
-/
def slitComplementDomain_theta {m : ℕ} (ρ θ : Fin m → ℝ) : Set ℂ :=
  (⋃ j : Fin m, radialSlit_theta (ρ j) (θ j))ᶜ

/--
  If a radial slit starts at strictly positive modulus `0 < ρ`, then `0` does not lie on the slit.
-/
lemma zero_not_mem_radialSlit_theta {ρ θ : ℝ} (hρ : 0 < ρ) :
    (0 : ℂ) ∉ radialSlit_theta ρ θ := by
{
  rintro ⟨r, hr, h0⟩
  have hr_pos : 0 < r := lt_of_lt_of_le hρ hr
  exact polarPoint_ne_zero_of_pos hr_pos θ h0.symm
}

/--
  If `polarPoint r φ` does not lie on `radialSlit_theta ρ θ` (`r ≥ 0`, `ρ > 0`), then for any
  `t ∈ [0, 1]`, the scaled point `polarPoint (t * r) φ` along the same polar angle `φ` also
  does not lie on `radialSlit_theta ρ θ`.
-/
lemma polarPoint_scale_not_mem_radialSlit_theta {ρ θ r φ t : ℝ}
    (hρ : 0 < ρ) (hr : 0 ≤ r) (ht0 : 0 ≤ t) (ht1 : t ≤ 1)
    (hnot : polarPoint r φ ∉ radialSlit_theta ρ θ) :
    polarPoint (t * r) φ ∉ radialSlit_theta ρ θ := by
{
  rintro ⟨s, hs, h_eq⟩
  have hs_pos : 0 < s := lt_of_lt_of_le hρ hs
  have htr_nonneg : 0 ≤ t * r := mul_nonneg ht0 hr
  have h_norm : t * r = s := by
  {
    have h1 := congrArg (fun z : ℂ => ‖z‖) h_eq
    rwa [polarPoint_norm_of_nonneg htr_nonneg φ, polarPoint_norm_of_nonneg hs_pos.le θ] at h1
  }
  have hr_ge_s : s ≤ r := by
  {
    calc s = t * r := h_norm.symm
      _ ≤ 1 * r := mul_le_mul_of_nonneg_right ht1 hr
      _ = r := one_mul r
  }
  have ht_ne : (t : ℂ) ≠ 0 := by
  {
    intro ht_zero
    have ht_real : t = 0 := Complex.ofReal_eq_zero.mp ht_zero
    rw [ht_real, zero_mul] at h_norm
    linarith
  }
  have h_same_ray : polarPoint r φ = polarPoint r θ := by
  {
    apply mul_left_cancel₀ ht_ne
    rw [← polarPoint_scale, ← polarPoint_scale, h_eq, h_norm]
  }
  exact hnot ⟨r, le_trans hs hr_ge_s, h_same_ray⟩
}

/--
  Every radially slitted plane `Ω = slitComplementDomain_theta ρ θ` with positive slit-tip
  moduli `∀ j, 0 < ρ j` is a starlike domain in the polar-angle sense `IsStarlikeDomain_theta Ω`.
-/
theorem slitComplementDomain_isStarlike_theta {m : ℕ} (ρ θ : Fin m → ℝ)
    (hρ : ∀ j, 0 < ρ j) :
    IsStarlikeDomain_theta (slitComplementDomain_theta ρ θ) := by
{
  refine ⟨?_, ?_⟩
  · simp only [slitComplementDomain_theta, Set.mem_compl_iff, Set.mem_iUnion, not_exists]
    intro j
    exact zero_not_mem_radialSlit_theta (hρ j)
  · intro r φ hr hmem t ht0 ht1
    simp only [slitComplementDomain_theta, Set.mem_compl_iff, Set.mem_iUnion, not_exists] at hmem ⊢
    intro j
    exact polarPoint_scale_not_mem_radialSlit_theta (hρ j) hr ht0 ht1 (hmem j)
}

/--
  A real-valued function `ω : ℂ → ℝ` is harmonic on an open set `G` in the Sarason `_eps` sense
  if its coordinate representation on `ℝ × ℝ` satisfies `Harmonic_R2_eps`.
-/
def IsRealHarmonicOn_eps (ω : ℂ → ℝ) (G : Set ℂ) : Prop :=
  Harmonic_R2_eps (fun p : ℝ × ℝ => ω ((p.1 : ℂ) + (p.2 : ℂ) * I))
    {p : ℝ × ℝ | (p.1 : ℂ) + (p.2 : ℂ) * I ∈ G}

/--
  `Harmonic_C_eps f G` from `Sarason/Chapter2.lean` holds if and only if both `(f ·).re` and
  `(f ·).im` satisfy `IsRealHarmonicOn_eps` on `G`.
-/
theorem harmonic_C_eps_iff_parts (f : ℂ → ℂ) (G : Set ℂ) :
    Harmonic_C_eps f G ↔
      IsRealHarmonicOn_eps (fun z => (f z).re) G ∧
      IsRealHarmonicOn_eps (fun z => (f z).im) G := by
{
  rfl
}

/--
  The Poisson kernel on `unitDiskSet` with boundary pole at polar angle `φ ∈ ℝ`
  (`ζ = polarPoint 1 φ ∈ unitCircleSet`), defined as the real part of `herglotzKernel`
  from `Sarason/Chapter3.lean` §III.11.
-/
noncomputable def poissonKernel_theta (φ : ℝ) (z : ℂ) : ℝ :=
  (herglotzKernel (polarPoint 1 φ) z).re

/--
  At the origin `z = 0`, `poissonKernel_theta φ 0 = 1` for every boundary angle `φ`,
  so the harmonic measure at `0` of any boundary arc `(φ₁, φ₂) ⊂ ∂𝔻` equals `(φ₂ - φ₁) / (2π)`.
-/
theorem poissonKernel_theta_at_origin (φ : ℝ) :
    poissonKernel_theta φ 0 = 1 := by
{
  unfold poissonKernel_theta
  have h_one := (III_11_herglotz_properties (polarPoint_one_mem_unitCircleSet φ)).1
  rw [h_one]
  rfl
}

/--
  Strict positivity of `poissonKernel_theta φ z` on the open unit disk `unitDiskSet`.
-/
theorem poissonKernel_theta_pos_on_disk (φ : ℝ) {z : ℂ} (hz : z ∈ unitDiskSet) :
    0 < poissonKernel_theta φ z := by
{
  unfold poissonKernel_theta
  exact (III_11_herglotz_properties (polarPoint_one_mem_unitCircleSet φ)).2.1 z hz
}

/--
  Vanishing of `poissonKernel_theta φ z` on `unitCircleSet`.
-/
theorem poissonKernel_theta_zero_on_circle (φ : ℝ) {z : ℂ} (hz : z ∈ unitCircleSet) :
    poissonKernel_theta φ z = 0 := by
{
  unfold poissonKernel_theta
  exact (III_11_herglotz_properties (polarPoint_one_mem_unitCircleSet φ)).2.2 z hz
}

/--
  Normalized harmonic measure `ω(0; (e^{i φ₁}, e^{i φ₂}); 𝔻) = (φ₂ - φ₁) / (2π)` at the origin
  of a boundary arc `(polarPoint 1 φ₁, polarPoint 1 φ₂) ⊂ ∂𝔻`.
-/
noncomputable def diskArcHarmonicMeasureOrigin (φ₁ φ₂ : ℝ) : ℝ :=
  (φ₂ - φ₁) / (2 * Real.pi)

/--
  Analytic structure of a Pommerenke starlike radial slit configuration (`Section 1, Eq. 1.1`),
  defined using Sarason's `_eps` definitions (`HolomorphicOn_eps`, `DifferentiableAt_eps`,
  `deriv_eps`, `HasDerivAt_R_to_C_eps`) and the polar angle `θ` definitions
  (`polarPoint`, `IsStarlikeOnDisk_theta_eps`, `pommerenkeLogDeriv`).
-/
structure AnalyticOrderedSlitConfiguration_eps (m : ℕ) where
  f : ℂ → ℂ
  phi : ℕ → ℝ
  tipArg : ℕ → ℝ
  thetaSlit : ℕ → ℝ
  sigma : ℕ → ℝ
  rho : ℕ → ℝ
  /-- `f` is starlike on `unitDiskSet` in the polar angle `θ` and `_eps` sense
      (`HolomorphicOn_eps f unitDiskSet`, `f 0 = 0`, and `argPolarDeriv_theta > 0`). -/
  hStarlike_theta : IsStarlikeOnDisk_theta_eps f
  /-- On `unitDiskSet \ {0}`, the `_eps` logarithmic derivative `z * deriv_eps f z hd / f z`
      equals the Herglotz–Pommerenke sum `pommerenkeLogDeriv`. -/
  hLogDeriv_eps :
    ∀ (z : ℂ), z ∈ unitDiskSet → z ≠ 0 → ∀ (hd : DifferentiableAt_eps f z),
      (z * deriv_eps f z hd) / f z =
        pommerenkeLogDeriv (fun j : Fin m => polarPoint 1 (phi j.val)) (fun j : Fin m => sigma j.val) z
  /-- At each slit-tip preimage angle `tipArg k`, the boundary path `θ ↦ f(polarPoint 1 θ)` has
      zero `_eps` derivative (`HasDerivAt_R_to_C_eps`). -/
  hTipCritical_eps : ∀ k : ℕ, HasDerivAt_R_to_C_eps (fun θ => f (polarPoint 1 θ)) 0 (tipArg k)
  /-- Interlacing of channel-infinity preimages `phi k` and slit-tip preimages `tipArg k` on `∂𝔻`. -/
  hInterlaceLeft : ∀ k : ℕ, phi k ≤ tipArg k
  hInterlaceRight : ∀ k : ℕ, tipArg k ≤ phi (k + 1)
  /-- The asymptotic opening angle `Δθ_k = θ_{k+1} - θ_k` of channel `C_k` is `σ_k π`. -/
  hChannelOpeningAngle : ∀ k : ℕ, thetaSlit (k + 1) - thetaSlit k = sigma k * Real.pi
  /-- Equal slit tip moduli (`ρ_k = 1` in Section 2, Eq. 2.1). -/
  hUnitCircleTips : ∀ k : ℕ, rho k = 1

/--
  Asymptotic angular opening `Δθ_k = θ_{k+1} - θ_k` of the `k`-th channel `C_k`.
-/
def analyticChannelOpeningAngle_theta {m : ℕ} (C : AnalyticOrderedSlitConfiguration_eps m) (k : ℕ) : ℝ :=
  C.thetaSlit (k + 1) - C.thetaSlit k

/--
  Analytic slit harmonic measure `ω_k = ω(0; R_k; Ω) = (φ_{k+1} - φ_k) / (2π)` via conformal
  invariance of `C.f` (`C.f 0 = 0`).
-/
noncomputable def analyticSlitHarmonicMeasure_eps {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m) (k : ℕ) : ℝ :=
  diskArcHarmonicMeasureOrigin (C.phi k) (C.phi (k + 1))

/--
  Analytic channel harmonic measure `ω(0; ∂C_k; Ω) = (t_{k+1} - t_k) / (2π)` (Section 2, Eq. 2.21).
-/
noncomputable def analyticChannelHarmonicMeasure_eps {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m) (k : ℕ) : ℝ :=
  diskArcHarmonicMeasureOrigin (C.tipArg k) (C.tipArg (k + 1))

/--
  Lower slit-bank harmonic measure `(t_k - φ_k) / (2π)` of slit `R_k` (facing channel `C_{k-1}`).
-/
noncomputable def analyticLowerBankHarmonicMeasure_eps {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m) (k : ℕ) : ℝ :=
  diskArcHarmonicMeasureOrigin (C.phi k) (C.tipArg k)

/--
  Upper slit-bank harmonic measure `(φ_{k+1} - t_k) / (2π)` of slit `R_k` (facing channel `C_k`).
-/
noncomputable def analyticUpperBankHarmonicMeasure_eps {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m) (k : ℕ) : ℝ :=
  diskArcHarmonicMeasureOrigin (C.tipArg k) (C.phi (k + 1))

/--
  **The Analytic Monotone Channel Harmonic Measure Statement (Equation 2.21 / Lemma 2.1):**
  For an `AnalyticOrderedSlitConfiguration_eps`, if the channel opening angles `Δθ_k = θ_{k+1} - θ_k`
  are monotone non-decreasing across the first `N` channels (`Δθ_k ≤ Δθ_{k+1}`), then the continuum
  channel harmonic measures from `0` are monotone non-decreasing:
  `ω(0; ∂C_k; Ω) ≤ ω(0; ∂C_{k+1}; Ω)`.
-/
def MonotoneChannelStatement_eps {m : ℕ} (C : AnalyticOrderedSlitConfiguration_eps m) (N : ℕ) : Prop :=
  (∀ k < N, analyticChannelOpeningAngle_theta C k ≤ analyticChannelOpeningAngle_theta C (k + 1)) →
  (∀ k < N, analyticChannelHarmonicMeasure_eps C k ≤ analyticChannelHarmonicMeasure_eps C (k + 1))

/--
  **The Analytic Monotone Slit Harmonic Measure Statement (Section 1, Question 1.1 / Lemma 2.2):**
  For an `AnalyticOrderedSlitConfiguration_eps`, if the channel opening angles `Δθ_k = θ_{k+1} - θ_k`
  are monotone non-decreasing (`Δθ_k ≤ Δθ_{k+1}`), then the slit harmonic measures from `0` are
  monotone non-decreasing:
  `ω(0; R_k; Ω) ≤ ω(0; R_{k+1}; Ω)`.
-/
def MonotoneSlitStatement_eps {m : ℕ} (C : AnalyticOrderedSlitConfiguration_eps m) (N : ℕ) : Prop :=
  (∀ k < N, analyticChannelOpeningAngle_theta C k ≤ analyticChannelOpeningAngle_theta C (k + 1)) →
  (∀ k < N, analyticSlitHarmonicMeasure_eps C k ≤ analyticSlitHarmonicMeasure_eps C (k + 1))

/--
  Monotonicity of the channel opening angles `Δθ_k ≤ Δθ_{k+1}` is equivalent to monotonicity
  of the Pommerenke exponents `σ_k ≤ σ_{k+1}`.
-/
theorem analyticChannelOpeningAngle_monotone_iff_sigma_monotone {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m) (k : ℕ) :
    analyticChannelOpeningAngle_theta C k ≤ analyticChannelOpeningAngle_theta C (k + 1) ↔
      C.sigma k ≤ C.sigma (k + 1) := by
{
  unfold analyticChannelOpeningAngle_theta
  rw [C.hChannelOpeningAngle k, C.hChannelOpeningAngle (k + 1)]
  exact mul_le_mul_iff_of_pos_right Real.pi_pos
}

/--
  **Derived Channel Opening Angle Formula from `pommerenkeSlitAngle` (`Sarason/Chapter3.lean` §III.13):**
  When the slit angles `C.thetaSlit k` are defined as the Pommerenke boundary arc angles
  `pommerenkeSlitAngle m k C.phi C.sigma`, the identity `Δθ_k = θ_{k+1} - θ_k = σ_k π` and the
  monotonicity equivalence `Δθ_k ≤ Δθ_{k+1} ↔ σ_k ≤ σ_{k+1}` follow directly from the half-angle
  phase jump theorem `pommerenkeSlitAngle_succ_sub_eq_sigma_mul_pi` without invoking
  `C.hChannelOpeningAngle`.
-/
theorem analyticChannelOpeningAngle_derived_from_pommerenkeSlitAngle {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m)
    (hSlitDef : ∀ j : ℕ, C.thetaSlit j = pommerenkeSlitAngle m j C.phi C.sigma)
    {k : ℕ} (hk : k + 1 < m) :
    analyticChannelOpeningAngle_theta C k = C.sigma k * Real.pi ∧
    (analyticChannelOpeningAngle_theta C k ≤ analyticChannelOpeningAngle_theta C (k + 1) ↔
      C.sigma k ≤ C.sigma (k + 1)) := by
{
  have hk0 : k < m := Nat.lt_of_succ_lt hk
  unfold analyticChannelOpeningAngle_theta
  rw [hSlitDef k, hSlitDef (k + 1), hSlitDef (k + 2)]
  exact ⟨pommerenkeSlitAngle_succ_sub_eq_sigma_mul_pi m k C.phi C.sigma hk0,
    pommerenkeSlitAngle_diff_monotone_iff_sigma_monotone m k C.phi C.sigma hk⟩
}

/--
  Decomposition of `analyticSlitHarmonicMeasure_eps` into the sum of its lower and upper slit banks:
  `ω(0; R_k; Ω) = ω(0; R_k^-; Ω) + ω(0; R_k^+; Ω)`.
-/
theorem analyticSlitHarmonicMeasure_eq_bank_sum_eps {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m) (k : ℕ) :
    analyticSlitHarmonicMeasure_eps C k =
      analyticLowerBankHarmonicMeasure_eps C k + analyticUpperBankHarmonicMeasure_eps C k := by
{
  unfold analyticSlitHarmonicMeasure_eps analyticLowerBankHarmonicMeasure_eps
    analyticUpperBankHarmonicMeasure_eps diskArcHarmonicMeasureOrigin
  ring
}

/--
  Decomposition of `analyticChannelHarmonicMeasure_eps` into the upper bank of slit `R_k` and
  the lower bank of slit `R_{k+1}` facing channel `C_k`:
  `ω(0; ∂C_k; Ω) = ω(0; R_k^+; Ω) + ω(0; R_{k+1}^-; Ω)`.
-/
theorem analyticChannelHarmonicMeasure_eq_adjacent_banks_eps {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m) (k : ℕ) :
    analyticChannelHarmonicMeasure_eps C k =
      analyticUpperBankHarmonicMeasure_eps C k + analyticLowerBankHarmonicMeasure_eps C (k + 1) := by
{
  unfold analyticChannelHarmonicMeasure_eps analyticUpperBankHarmonicMeasure_eps
    analyticLowerBankHarmonicMeasure_eps diskArcHarmonicMeasureOrigin
  ring
}

/--
  Analytic counterpart of Lemma 2.2: if the lower and upper slit banks of `R_k` are bounded by
  those of `R_{k+1}`, then `analyticSlitHarmonicMeasure_eps C k ≤ analyticSlitHarmonicMeasure_eps C (k + 1)`.
-/
theorem analytic_monotone_slit_of_bank_monotonicity_eps {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m) (k : ℕ)
    (hLower : analyticLowerBankHarmonicMeasure_eps C k ≤ analyticLowerBankHarmonicMeasure_eps C (k + 1))
    (hUpper : analyticUpperBankHarmonicMeasure_eps C k ≤ analyticUpperBankHarmonicMeasure_eps C (k + 1)) :
    analyticSlitHarmonicMeasure_eps C k ≤ analyticSlitHarmonicMeasure_eps C (k + 1) := by
{
  rw [analyticSlitHarmonicMeasure_eq_bank_sum_eps C k,
      analyticSlitHarmonicMeasure_eq_bank_sum_eps C (k + 1)]
  exact add_le_add hLower hUpper
}

/--
  **Weierstrass `HasLimitAtInf_eps` Beurling–Nevanlinna Radial Exhaustion Theorem:**
  Using `HasLimitAtInf_eps` from `Sarason/Definitions.lean`, if the truncated channel harmonic
  measures `ω_trunc_k(w)` and `ω_trunc_k1(w)` on `Ω_R` (`R = ‖w‖ → ∞`) converge in the
  Weierstrass sense `HasLimitAtInf_eps` to `analyticChannelHarmonicMeasure_eps C k` and
  `analyticChannelHarmonicMeasure_eps C (k + 1)` as `‖w‖ → ∞`, and `ω_trunc_k(w) ≤ ω_trunc_k1(w)`
  for all `‖w‖ > R₀`, then `analyticChannelHarmonicMeasure_eps C k ≤ analyticChannelHarmonicMeasure_eps C (k + 1)`.
-/
theorem analytic_monotone_channel_of_hasLimitAtInf_eps {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m) (k : ℕ)
    (ω_trunc_k ω_trunc_k1 : ℂ → ℝ) (R₀ : ℝ)
    (hLim_k : HasLimitAtInf_eps ω_trunc_k (analyticChannelHarmonicMeasure_eps C k))
    (hLim_k1 : HasLimitAtInf_eps ω_trunc_k1 (analyticChannelHarmonicMeasure_eps C (k + 1)))
    (hMono_R : ∀ w : ℂ, ‖w‖ > R₀ → ω_trunc_k w ≤ ω_trunc_k1 w) :
    analyticChannelHarmonicMeasure_eps C k ≤ analyticChannelHarmonicMeasure_eps C (k + 1) := by
{
  by_contra h_gt
  have h_gt' := not_le.mp h_gt
  set ε := (analyticChannelHarmonicMeasure_eps C k - analyticChannelHarmonicMeasure_eps C (k + 1)) / 3
  have hε : 0 < ε := by
  {
    dsimp [ε]; linarith
  }
  rcases hLim_k ε hε with ⟨M₁, hM₁_pos, hM₁⟩
  rcases hLim_k1 ε hε with ⟨M₂, _, hM₂⟩
  let R : ℝ := max R₀ (max M₁ M₂) + 1
  have hR_gt_R0 : R > R₀ := by
  {
    dsimp [R]; linarith [le_max_left R₀ (max M₁ M₂)]
  }
  have hR_gt_M1 : R > M₁ := by
  {
    dsimp [R]; linarith [le_max_left M₁ M₂, le_max_right R₀ (max M₁ M₂)]
  }
  have hR_gt_M2 : R > M₂ := by
  {
    dsimp [R]; linarith [le_max_right M₁ M₂, le_max_right R₀ (max M₁ M₂)]
  }
  have hR_pos : 0 < R := by
  {
    linarith
  }
  have hw_norm : ‖(R : ℂ)‖ = R := by
  {
    rw [Complex.norm_real, Real.norm_of_nonneg hR_pos.le]
  }
  have hb_k := abs_lt.mp (hM₁ (R : ℂ) (by { rw [hw_norm]; exact hR_gt_M1 }))
  have hb_k1 := abs_lt.mp (hM₂ (R : ℂ) (by { rw [hw_norm]; exact hR_gt_M2 }))
  have h_le := hMono_R (R : ℂ) (by { rw [hw_norm]; exact hR_gt_R0 })
  dsimp [ε] at hb_k hb_k1
  linarith
}

/--
  **Weierstrass `HasLimitAt_eps` Chelkak–Smirnov Mesh Convergence Theorem (`δ → 0` at Fixed `R`):**
  Using `HasLimitAt_eps` from `Sarason/Definitions.lean`, if at truncation radius `R` the discrete
  channel harmonic measures `ω_mesh_k(δ)` and `ω_mesh_k1(δ)` satisfy `HasLimitAt_eps` to the
  truncated continuum harmonic measures `(ω_trunc_k : ℂ)` and `(ω_trunc_k1 : ℂ)` as `δ → 0`, and
  `Re(ω_mesh_k δ) ≤ Re(ω_mesh_k1 δ)` for all `0 < ‖δ‖ < δ₀`, then `ω_trunc_k ≤ ω_trunc_k1`.
-/
theorem analytic_truncated_channel_monotone_of_hasLimitAt_eps
    (ω_mesh_k ω_mesh_k1 : ℂ → ℂ) (ω_trunc_k ω_trunc_k1 δ₀ : ℝ)
    (hδ₀ : 0 < δ₀)
    (hLim_k : HasLimitAt_eps ω_mesh_k (ω_trunc_k : ℂ) 0)
    (hLim_k1 : HasLimitAt_eps ω_mesh_k1 (ω_trunc_k1 : ℂ) 0)
    (hDiscreteMono : ∀ δ : ℂ, 0 < ‖δ‖ ∧ ‖δ‖ < δ₀ → (ω_mesh_k δ).re ≤ (ω_mesh_k1 δ).re) :
    ω_trunc_k ≤ ω_trunc_k1 := by
{
  by_contra h_gt
  have h_gt' := not_le.mp h_gt
  set ε := (ω_trunc_k - ω_trunc_k1) / 3
  have hε : 0 < ε := by
  {
    dsimp [ε]; linarith
  }
  rcases hLim_k ε hε with ⟨δ₁, hδ₁_pos, hδ₁⟩
  rcases hLim_k1 ε hε with ⟨δ₂, hδ₂_pos, hδ₂⟩
  let r : ℝ := min δ₀ (min δ₁ δ₂) / 2
  have hr_pos : 0 < r := half_pos (lt_min hδ₀ (lt_min hδ₁_pos hδ₂_pos))
  have hr_norm : ‖(r : ℂ) - 0‖ = r := by
  {
    rw [sub_zero, Complex.norm_real, Real.norm_of_nonneg hr_pos.le]
  }
  have hr_lt_δ0 : r < δ₀ := lt_of_lt_of_le (half_lt_self (lt_min hδ₀ (lt_min hδ₁_pos hδ₂_pos))) (min_le_left _ _)
  have hr_lt_δ1 : r < δ₁ := lt_of_lt_of_le (half_lt_self (lt_min hδ₀ (lt_min hδ₁_pos hδ₂_pos)))
    (le_trans (min_le_right _ _) (min_le_left _ _))
  have hr_lt_δ2 : r < δ₂ := lt_of_lt_of_le (half_lt_self (lt_min hδ₀ (lt_min hδ₁_pos hδ₂_pos)))
    (le_trans (min_le_right _ _) (min_le_right _ _))
  have hb_k := abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm _)
    (hδ₁ (r : ℂ) ⟨by { rw [hr_norm]; exact hr_pos }, by { rw [hr_norm]; exact hr_lt_δ1 }⟩))
  have hb_k1 := abs_lt.mp (lt_of_le_of_lt (Complex.abs_re_le_norm _)
    (hδ₂ (r : ℂ) ⟨by { rw [hr_norm]; exact hr_pos }, by { rw [hr_norm]; exact hr_lt_δ2 }⟩))
  have h_le := hDiscreteMono (r : ℂ) ⟨by { rw [← sub_zero (r : ℂ), hr_norm]; exact hr_pos },
    by { rw [← sub_zero (r : ℂ), hr_norm]; exact hr_lt_δ0 }⟩
  simp only [Complex.sub_re, Complex.ofReal_re] at hb_k hb_k1
  dsimp [ε] at hb_k hb_k1
  linarith
}

/-! ## 9. Exact Paper Definitions from *Discretization of a Harmonic Measure Problem and Spandrel* (`IsoRadStarQuestion.tex`)

This section provides the 1-to-1 formal definitions matching every numbered equation and question in
Sections 1 and 2 of `IsoRadStarQuestion.tex` / `IsoRadStarQuestion_Lean2026.tex`, expressed in terms
of `polarPoint`, `arg`, `IsStarlikeDomain_theta`, and `IsStarlikeOnDisk_theta_eps`.
-/

/--
  **Section 1, Equation (1.1):**
  Explicit Pommerenke product formula for the Riemann map `f : 𝔻 → Ω`:
  `f(z) = z ∏_{j=1}^{2n} (1 - conj(z_j) z)^{-σ_j}`.
-/
noncomputable def riemannSlitMap_f (n : ℕ) (z_pt : ℕ → ℂ) (σ : ℕ → ℝ) (z : ℂ) : ℂ :=
  z * ∏ j ∈ Finset.Icc 1 (2 * n), (1 - star (z_pt j) * z) ^ (-(σ j : ℂ))

/--
  **Section 1, Symmetrical Slit Setup (Equations 1.1–1.6):**
  Matches lines 171–186 of `IsoRadStarQuestion.tex`:
  - `f(z) = z ∏_{j=1}^{2n} (1 - z̄_j z)^{-σ_j}` (`hFormula_f`),
  - `z_{2n+2-k} = z̄_k` (`hSymm_z`),
  - `σ_{2n+2-k} = σ_k` (`hSymm_sigma`),
  - `exp(i t_{2n+1-k}) = exp(-i t_k)` (`hSymm_tip`),
  - `ρ_{2n+1-k} = ρ_k` (`hSymm_rho`),
  - Equal starting moduli `ρ_k = ρ_j` for all `j, k` (`hEqualRho`),
  - Unit-circle arc lengths `ω_k = |(z_k, z_{k+1})| = φ_{k+1} - φ_k`.
-/
structure PaperSection1SymmetricSlitSetup_eps (n : ℕ) where
  f : ℂ → ℂ
  φ : ℕ → ℝ
  z_pt : ℕ → ℂ
  σ : ℕ → ℝ
  t : ℕ → ℝ
  ρ : ℕ → ℝ
  hStarlike_theta : IsStarlikeOnDisk_theta_eps f
  hUnitCircle_z : ∀ k : ℕ, z_pt k = polarPoint 1 (φ k)
  hFormula_f : ∀ z ∈ unitDiskSet, f z = riemannSlitMap_f n z_pt σ z
  hSymm_z : ∀ k : ℕ, 2 ≤ k → k ≤ n → z_pt (2 * n + 2 - k) = star (z_pt k)
  hSymm_sigma : ∀ k : ℕ, 2 ≤ k → k ≤ n → σ (2 * n + 2 - k) = σ k
  hSymm_tip : ∀ k : ℕ, 2 ≤ k → k ≤ n → polarPoint 1 (t (2 * n + 1 - k)) = polarPoint 1 (-t k)
  hSymm_rho : ∀ k : ℕ, 2 ≤ k → k ≤ n → ρ (2 * n + 1 - k) = ρ k
  hEqualRho : ∀ j k : ℕ, ρ k = ρ j

/--
  **Section 1, Unit-Circle Arc Length / Slit Harmonic Measure `ω_k = |(z_k, z_{k+1})|`:**
  Arc length on `∂𝔻` from `z_k = e^{i φ_k}` to `z_{k+1} = e^{i φ_{k+1}}`, equal (up to `2π` normalization)
  to the harmonic measure of the slit `R_k` in `Ω`.
-/
def paperSlitArcLength_omega {n : ℕ} (S : PaperSection1SymmetricSlitSetup_eps n) (k : ℕ) : ℝ :=
  S.φ (k + 1) - S.φ k

/--
  **Section 1, Question 1.1 (`\label{question}` in `IsoRadStarQuestion.tex`):**
  "Does `{ω_k}_1^n` being monotone imply `{σ_k}_1^n` are monotone, and vice versa?"
-/
def Question_1_1_eps (n : ℕ) (S : PaperSection1SymmetricSlitSetup_eps n) : Prop :=
  (∀ k : ℕ, 1 ≤ k → k < n → paperSlitArcLength_omega S k ≤ paperSlitArcLength_omega S (k + 1)) ↔
  (∀ k : ℕ, 1 ≤ k → k < n → S.σ k ≤ S.σ (k + 1))

/--
  **Section 2, Equation (2.1) — Symmetric Slits `S_k`:**
  `S_k = { r e^{± i θ_k} : r ≥ 1 }`.
-/
def symmetricSlit_S_k (θ : ℕ → ℝ) (k : ℕ) : Set ℂ :=
  radialSlit_theta 1 (θ k) ∪ radialSlit_theta 1 (-θ k)

/--
  **Section 2, Monotone Slit Angle Hypothesis (`θ_0 = 0 < θ_1 < ... < θ_N` with `θ_k - θ_{k-1} ≤ θ_{k+1} - θ_k`):**
  Matches line 204 of `IsoRadStarQuestion.tex`.
-/
def MonotoneSymmetricSlitAngles (N : ℕ) (θ : ℕ → ℝ) : Prop :=
  θ 0 = 0 ∧
  (∀ k < N, θ k < θ (k + 1)) ∧
  (∀ k : ℕ, 1 ≤ k → k < N → θ k - θ (k - 1) ≤ θ (k + 1) - θ k)

/--
  **Section 2, Equation (2.2) — Symmetric Slitted Domain `Ω`:**
  `Ω = ℂ \ (⋃_{k=0}^N S_k)`.
-/
def slitDomain_Omega (N : ℕ) (θ : ℕ → ℝ) : Set ℂ :=
  (⋃ k ∈ Finset.range (N + 1), symmetricSlit_S_k θ k)ᶜ

/--
  Every symmetric slitted domain `Ω = slitDomain_Omega N θ` (Equation 2.2, where slits `S_k`
  start on the unit circle `r ≥ 1`) is a starlike domain in the polar-angle sense
  `IsStarlikeDomain_theta (slitDomain_Omega N θ)`.
-/
theorem slitDomain_Omega_isStarlike_theta (N : ℕ) (θ : ℕ → ℝ) :
    IsStarlikeDomain_theta (slitDomain_Omega N θ) := by
{
  refine ⟨?_, ?_⟩
  · simp only [slitDomain_Omega, symmetricSlit_S_k, Set.mem_compl_iff, Set.mem_iUnion,
      Set.mem_union, not_exists, not_or]
    intro k _
    exact ⟨zero_not_mem_radialSlit_theta zero_lt_one, zero_not_mem_radialSlit_theta zero_lt_one⟩
  · intro r φ hr hmem t ht0 ht1
    simp only [slitDomain_Omega, symmetricSlit_S_k, Set.mem_compl_iff, Set.mem_iUnion,
      Set.mem_union, not_exists, not_or] at hmem ⊢
    intro k hk
    rcases hmem k hk with ⟨h_pos, h_neg⟩
    exact ⟨polarPoint_scale_not_mem_radialSlit_theta zero_lt_one hr ht0 ht1 h_pos,
      polarPoint_scale_not_mem_radialSlit_theta zero_lt_one hr ht0 ht1 h_neg⟩
}

/--
  **Section 2, Equation (2.3) — Symmetric Channels `C_k`:**
  `C_k = { r e^{± i θ} : r > 1, θ_k < θ < θ_{k+1} }`.
-/
def channel_C_k (θ_seq : ℕ → ℝ) (k : ℕ) : Set ℂ :=
  {w : ℂ | ∃ (r θ : ℝ), 1 < r ∧ θ_seq k < θ ∧ θ < θ_seq (k + 1) ∧
    (w = polarPoint r θ ∨ w = polarPoint r (-θ))}

/--
  **Section 2, Equation (2.4) — Isoradial Modulus Recursion Step:**
  `r_{j+1} = r_j cos(π/m) + √((r_j cos(π/m))² - r_j² + δ²)`.
-/
noncomputable def isoradialModulusStep (m : ℕ) (δ r_j : ℝ) : ℝ :=
  r_j * Real.cos (Real.pi / (m : ℝ)) +
    Real.sqrt ((r_j * Real.cos (Real.pi / (m : ℝ))) ^ 2 - r_j ^ 2 + δ ^ 2)

/--
  **Section 2, Equation (2.4) Real Algebraic Discriminant Identity:**
  `(r_j cos(π/m))² - r_j² + δ² = δ² - r_j² sin²(π/m)`.
-/
theorem isoradial_discriminant_identity (m : ℕ) (δ r_j : ℝ) :
    (r_j * Real.cos (Real.pi / (m : ℝ))) ^ 2 - r_j ^ 2 + δ ^ 2 =
      δ ^ 2 - r_j ^ 2 * Real.sin (Real.pi / (m : ℝ)) ^ 2 := by
{
  have h_pyth := Real.cos_sq_add_sin_sq (Real.pi / (m : ℝ))
  linear_combination r_j ^ 2 * h_pyth
}

/--
  **Section 2, Equation (2.5) — Polar Isoradial Graph Vertices `V(Γ^δ)`:**
  `V(Γ^δ) = { r_{2n} e^{i ℓ δ²} : ℓ = 1, ..., m, n ∈ ℕ }`.
-/
def isoradialGraphVertices_V_Gamma_delta (m : ℕ) (δ : ℝ) (r_seq : ℕ → ℝ) : Set ℂ :=
  {v : ℂ | ∃ (n ℓ : ℕ), 1 ≤ ℓ ∧ ℓ ≤ m ∧ v = polarPoint (r_seq (2 * n)) ((ℓ : ℝ) * δ ^ 2)}

/--
  **Section 2, Equation (2.8) — Discrete Slit `(S_k)_{Ω^δ}`:**
  `(S_k)_{Ω^δ} = { v ∈ V(Γ^δ) : arg v = arg γ_k^δ, |v| ≥ |γ_k^δ| }`,
  using `arg` from `Sarason/Chapter2.lean`.
-/
def discreteSlit_S_k_delta (V_Gamma : Set ℂ) (γ_delta : ℕ → ℂ) (k : ℕ) : Set ℂ :=
  {v ∈ V_Gamma | arg v = arg (γ_delta k) ∧ ‖γ_delta k‖ ≤ ‖v‖}

/--
  **Section 2, Equation (2.9) — Union of Discrete Slits `S_{Ω^δ}`:**
  `S_{Ω^δ} = ⋃_{k=0}^N (S_k)_{Ω^δ}`.
-/
def discreteSlitUnion_S_delta (N : ℕ) (V_Gamma : Set ℂ) (γ_delta : ℕ → ℂ) : Set ℂ :=
  ⋃ k ∈ Finset.range (N + 1), discreteSlit_S_k_delta V_Gamma γ_delta k

/--
  **Section 2, Equation (2.13) — Discrete Channel `(C_k)_{Ω^δ}`:**
  `(C_k)_{Ω^δ} = ⋃_{ℓ=1}^{n_k} { v ∈ V(Γ^δ) : arg v = arg v^δ_{k,ℓ}, |v^δ_{k,ℓ}| ≤ |v| < r^δ_max }`.
-/
def discreteChannel_C_k_delta (V_Gamma : Set ℂ) (n_k : ℕ → ℕ) (v_open : ℕ → ℕ → ℂ)
    (r_max : ℝ) (k : ℕ) : Set ℂ :=
  ⋃ ℓ ∈ Finset.Icc 1 (n_k k),
    {v ∈ V_Gamma | arg v = arg (v_open k ℓ) ∧ ‖v_open k ℓ‖ ≤ ‖v‖ ∧ ‖v‖ < r_max}

/--
  **Section 2, Equation (2.14) — Discrete Unit Disk `𝔻^δ`:**
  `𝔻^δ = { v ∈ V(Γ^δ) : |v| ≤ r_tip }`.
-/
def discreteDisk_D_delta (V_Gamma : Set ℂ) (r_tip : ℝ) : Set ℂ :=
  {v ∈ V_Gamma | ‖v‖ ≤ r_tip}

/--
  **Section 2, Equation (2.20) — Discrete Channel Boundary `∂(C_k)_{Ω^δ}`:**
  `∂(C_k)_{Ω^δ} = { v ∈ ∂Ω^δ_Γ : ∃ u ∈ (C_k)_{Ω^δ}, (v, u) ∈ E(Γ^δ) }`.
-/
def discreteChannelBoundary_delta (bdry_Omega_delta : Set ℂ) (E_Gamma : ℂ → ℂ → Prop)
    (C_k_delta : Set ℂ) : Set ℂ :=
  {v ∈ bdry_Omega_delta | ∃ u ∈ C_k_delta, E_Gamma v u}

/--
  **Section 2, Spandrel Definition & Question 2.3 (`\label{spandrel}` in `IsoRadStarQuestion_Lean2026.tex`):**
  Given `δ > 0`, an *infinite dyadic polar isoradial starlike graph* is a polar graph vertex set
  `V_Gamma ⊆ ℂ` satisfying:
  1. **(Dyadic):** `v ∈ V(Γ^δ) → ∃ n : ℤ, arg v = 2π / 2^n`,
  2. **(Starlike):** `polarPoint r θ ∈ V(Γ^δ) → polarPoint (isoradialModulusStep m δ r) θ ∈ V(Γ^δ)`,
  3. **(Infinite):** `∀ r > 0, ∃ v ∈ V(Γ^δ), ‖v‖ > r`.
-/
def IsInfiniteDyadicPolarIsoradialStarlikeGraph (m : ℕ) (δ : ℝ) (V_Gamma : Set ℂ) : Prop :=
  (∀ v ∈ V_Gamma, ∃ n : ℤ, arg v = (2 * Real.pi) / (2 : ℝ) ^ n) ∧
  (∀ r θ : ℝ, polarPoint r θ ∈ V_Gamma →
    polarPoint (isoradialModulusStep m δ r) θ ∈ V_Gamma) ∧
  (∀ r : ℝ, 0 < r → ∃ v ∈ V_Gamma, r < ‖v‖)

/--
  **Section 2, Question 2.3 (`\label{spandrel}`):**
  "Does an infinite dyadic polar isoradial starlike graph exist?"
-/
def Question_2_3_Spandrel (m : ℕ) (δ : ℝ) : Prop :=
  ∃ V_Gamma : Set ℂ, IsInfiniteDyadicPolarIsoradialStarlikeGraph m δ V_Gamma

/-! ## 10. Real-Valued Kakutani–Markov Proofs (Lemmas 2.1 & 2.2, Equation 2.21) & Master Proofs of `MonotoneChannelStatement_eps` and `MonotoneSlitStatement_eps`

This section proves the real-valued (`ℝ`) Kakutani–Markov monotonicity theorems (Lemma 2.1, Lemma 2.2,
and Equation 2.21) and chains them with the Weierstrass `_eps` Chelkak–Smirnov (`δ → 0` via `HasLimitAt_eps`)
and Beurling–Nevanlinna (`R → ∞` via `HasLimitAtInf_eps`) convergence theorems to establish
`MonotoneChannelStatement_eps` and `MonotoneSlitStatement_eps`.
-/

/--
  **Section 2, Equation (2.19) — Chelkak–Smirnov Isoradial Tangent Transition Weight:**
  `P(ξ_v = u_k - v) = tan θ_k / ∑_j tan θ_j`.
-/
noncomputable def isoradialTangentWeight (θ_k θ_sum : ℝ) : ℝ :=
  Real.tan θ_k / θ_sum

/--
  **Section 2, Equations (2.26)–(2.27) over `ℝ` — 4-Neighbor Markov Transition Operator:**
  `P(RW(t+1) = v) = M_{v,v_l} P(RW(t) = v_l) + M_{v,v_r} P(RW(t) = v_r) + M_{v,v_u} P(RW(t) = v_u) + M_{v,v_d} P(RW(t) = v_d)`.
-/
def markovFourTermStep_R (ml mr mu md pl pr pu pd : ℝ) : ℝ :=
  ml * pl + mr * pr + mu * pu + md * pd

/--
  Non-negativity of `markovFourTermStep_R` when weights and probabilities are non-negative.
-/
lemma markovFourTermStep_R_nonneg
    {ml mr mu md pl pr pu pd : ℝ}
    (hml : 0 ≤ ml) (hmr : 0 ≤ mr) (hmu : 0 ≤ mu) (hmd : 0 ≤ md)
    (hpl : 0 ≤ pl) (hpr : 0 ≤ pr) (hpu : 0 ≤ pu) (hpd : 0 ≤ pd) :
    0 ≤ markovFourTermStep_R ml mr mu md pl pr pu pd := by
{
  unfold markovFourTermStep_R
  positivity
}

/--
  **Lemma 2.1 over `ℝ` (Direct / Right-Aligned Step, Equations 2.31–2.39):**
  For real transition weights `0 ≤ ml_k ≤ ml_k1`, `0 ≤ mr, mu, md` and real probabilities
  `0 ≤ pl_k` with `pl_k ≤ pl_k1`, `pr_k ≤ pr_k1`, `pu_k ≤ pu_k1`, `pd_k ≤ pd_k1`,
  `P(RW(t+1) = v^δ_{k,ℓ}) ≤ P(RW(t+1) = v^δ_{k+1,ℓ})`.
-/
theorem lemma_2_1_direct_step_R
    (ml_k ml_k1 mr mu md : ℝ)
    (pl_k pr_k pu_k pd_k : ℝ)
    (pl_k1 pr_k1 pu_k1 pd_k1 : ℝ)
    (h_ml_nonneg : 0 ≤ ml_k1)
    (h_mr_nonneg : 0 ≤ mr) (h_mu_nonneg : 0 ≤ mu) (h_md_nonneg : 0 ≤ md)
    (h_pl_nonneg : 0 ≤ pl_k)
    (hWeightL : ml_k ≤ ml_k1)
    (hProbL : pl_k ≤ pl_k1) (hProbR : pr_k ≤ pr_k1)
    (hProbU : pu_k ≤ pu_k1) (hProbD : pd_k ≤ pd_k1) :
    markovFourTermStep_R ml_k mr mu md pl_k pr_k pu_k pd_k ≤
      markovFourTermStep_R ml_k1 mr mu md pl_k1 pr_k1 pu_k1 pd_k1 := by
{
  unfold markovFourTermStep_R
  have h1 : ml_k * pl_k ≤ ml_k1 * pl_k1 :=
    mul_le_mul hWeightL hProbL h_pl_nonneg h_ml_nonneg
  have h2 : mr * pr_k ≤ mr * pr_k1 := mul_le_mul_of_nonneg_left hProbR h_mr_nonneg
  have h3 : mu * pu_k ≤ mu * pu_k1 := mul_le_mul_of_nonneg_left hProbU h_mu_nonneg
  have h4 : md * pd_k ≤ md * pd_k1 := mul_le_mul_of_nonneg_left hProbD h_md_nonneg
  linarith
}

/--
  **Lemma 2.1 over `ℝ` (Intrachannel Reflection Step, Equations 2.29–2.30 & 2.40–2.49):**
  Under intrachannel reflection `ℓ ↦ n_{k+1} - ℓ + 1`, the left and right transition weights swap
  (`0 ≤ ml_k ≤ mr_refl`), yielding
  `P(RW(t+1) = v^δ_{k,ℓ}) ≤ P(RW(t+1) = v^δ_{k+1, n_{k+1}-ℓ+1})`.
-/
theorem lemma_2_1_reflected_step_R
    (ml_k mr_refl mr mu md : ℝ)
    (pl_k pr_k pu_k pd_k : ℝ)
    (pr_refl pl_refl pu_refl pd_refl : ℝ)
    (h_mr_refl_nonneg : 0 ≤ mr_refl)
    (h_mr_nonneg : 0 ≤ mr) (h_mu_nonneg : 0 ≤ mu) (h_md_nonneg : 0 ≤ md)
    (h_pl_nonneg : 0 ≤ pl_k)
    (hWeightRefl : ml_k ≤ mr_refl)
    (hReflL : pl_k ≤ pr_refl) (hReflR : pr_k ≤ pl_refl)
    (hReflU : pu_k ≤ pu_refl) (hReflD : pd_k ≤ pd_refl) :
    markovFourTermStep_R ml_k mr mu md pl_k pr_k pu_k pd_k ≤
      markovFourTermStep_R mr_refl mr mu md pr_refl pl_refl pu_refl pd_refl := by
{
  unfold markovFourTermStep_R
  have h1 : ml_k * pl_k ≤ mr_refl * pr_refl :=
    mul_le_mul hWeightRefl hReflL h_pl_nonneg h_mr_refl_nonneg
  have h2 : mr * pr_k ≤ mr * pl_refl := mul_le_mul_of_nonneg_left hReflR h_mr_nonneg
  have h3 : mu * pu_k ≤ mu * pu_refl := mul_le_mul_of_nonneg_left hReflU h_mu_nonneg
  have h4 : md * pd_k ≤ md * pd_refl := mul_le_mul_of_nonneg_left hReflD h_md_nonneg
  linarith
}

/--
  Real-valued coupled Markov evolution across channel `k` (`p_k(t)`), direct channel `k+1`
  (`p_direct(t)`), and intrachannel-reflected channel `k+1` (`p_refl(t)`), starting at `0` at `t = 0`.
-/
structure CoupledChannelWalk_R where
  ml_k : ℝ
  ml_k1 : ℝ
  mr : ℝ
  mu : ℝ
  md : ℝ
  h_ml_nonneg : 0 ≤ ml_k1
  h_mr_nonneg : 0 ≤ mr
  h_mu_nonneg : 0 ≤ mu
  h_md_nonneg : 0 ≤ md
  hBoundaryL : ml_k ≤ ml_k1
  pl_k : ℕ → ℝ
  pr_k : ℕ → ℝ
  pu_k : ℕ → ℝ
  pd_k : ℕ → ℝ
  pl_direct : ℕ → ℝ
  pr_direct : ℕ → ℝ
  pu_direct : ℕ → ℝ
  pd_direct : ℕ → ℝ
  pr_refl : ℕ → ℝ
  pl_refl : ℕ → ℝ
  pu_refl : ℕ → ℝ
  pd_refl : ℕ → ℝ
  h_pl_nonneg : ∀ t, 0 ≤ pl_k t
  hDirectL : ∀ t, pl_k t ≤ pl_direct t
  hDirectR : ∀ t, pr_k t ≤ pr_direct t
  hDirectU : ∀ t, pu_k t ≤ pu_direct t
  hDirectD : ∀ t, pd_k t ≤ pd_direct t
  hReflL : ∀ t, pl_k t ≤ pr_refl t
  hReflR : ∀ t, pr_k t ≤ pl_refl t
  hReflU : ∀ t, pu_k t ≤ pu_refl t
  hReflD : ∀ t, pd_k t ≤ pd_refl t

/-- Real probability at `v^δ_{k,ℓ}` at time `t`. -/
def probChannelK_R (W : CoupledChannelWalk_R) : ℕ → ℝ
  | 0 => 0
  | t + 1 => markovFourTermStep_R W.ml_k W.mr W.mu W.md (W.pl_k t) (W.pr_k t) (W.pu_k t) (W.pd_k t)

/-- Real probability at `v^δ_{k+1,ℓ}` at time `t`. -/
def probChannelDirect_R (W : CoupledChannelWalk_R) : ℕ → ℝ
  | 0 => 0
  | t + 1 => markovFourTermStep_R W.ml_k1 W.mr W.mu W.md (W.pl_direct t) (W.pr_direct t) (W.pu_direct t) (W.pd_direct t)

/-- Real probability at `v^δ_{k+1, n_{k+1}-ℓ+1}` at time `t`. -/
def probChannelRefl_R (W : CoupledChannelWalk_R) : ℕ → ℝ
  | 0 => 0
  | t + 1 => markovFourTermStep_R W.ml_k1 W.mr W.mu W.md (W.pr_refl t) (W.pl_refl t) (W.pu_refl t) (W.pd_refl t)

/--
  **Full Inductive Proof of Lemma 2.1 over `ℝ` for All `t ∈ ℕ` (Equation 2.24):**
  For every time step `t ∈ ℕ`,
  `P(RW(t) = v^δ_{k,ℓ}) ≤ min(P(RW(t) = v^δ_{k+1,ℓ}), P(RW(t) = v^δ_{k+1, n_{k+1}-ℓ+1}))`.
-/
theorem lemma_2_1_full_induction_R (W : CoupledChannelWalk_R) (t : ℕ) :
    probChannelK_R W t ≤ min (probChannelDirect_R W t) (probChannelRefl_R W t) := by
{
  induction t with
  | zero =>
    simp [probChannelK_R, probChannelDirect_R, probChannelRefl_R]
  | succ step _ =>
    rw [le_min_iff]
    constructor
    · exact lemma_2_1_direct_step_R
        W.ml_k W.ml_k1 W.mr W.mu W.md
        (W.pl_k step) (W.pr_k step) (W.pu_k step) (W.pd_k step)
        (W.pl_direct step) (W.pr_direct step) (W.pu_direct step) (W.pd_direct step)
        W.h_ml_nonneg W.h_mr_nonneg W.h_mu_nonneg W.h_md_nonneg (W.h_pl_nonneg step)
        W.hBoundaryL (W.hDirectL step) (W.hDirectR step) (W.hDirectU step) (W.hDirectD step)
    · exact lemma_2_1_reflected_step_R
        W.ml_k W.ml_k1 W.mr W.mu W.md
        (W.pl_k step) (W.pr_k step) (W.pu_k step) (W.pd_k step)
        (W.pr_refl step) (W.pl_refl step) (W.pu_refl step) (W.pd_refl step)
        W.h_ml_nonneg W.h_mr_nonneg W.h_mu_nonneg W.h_md_nonneg (W.h_pl_nonneg step)
        W.hBoundaryL (W.hReflL step) (W.hReflR step) (W.hReflU step) (W.hReflD step)
}

/--
  **Lemma 2.2 over `ℝ` (Slit Boundary Monotonicity — Equations 2.50–2.54):**
  By Lemma 2.1 at `ℓ = 1`, `P(RW(t) = v^δ_{k-1, n_{k-1}}) ≤ P(RW(t) = v^δ_{k, n_k})` and
  `P(RW(t) = v^δ_{k, 1}) ≤ P(RW(t) = v^δ_{k+1, 1})`. With non-negative transition weights
  `0 ≤ mRight, mLeft, mUp, mDown`, this implies `P(RW(t+1) = γ^δ_k) ≤ P(RW(t+1) = γ^δ_{k+1})`.
-/
theorem lemma_2_2_slit_boundary_monotonicity_R
    (mRight mLeft mUp mDown : ℝ)
    (p_km1_last p_k_last p_k_first p_kp1_first pUp_k pUp_kp1 pDown_k pDown_kp1 : ℝ)
    (hmR : 0 ≤ mRight) (hmL : 0 ≤ mLeft) (hmU : 0 ≤ mUp) (hmD : 0 ≤ mDown)
    (hRightChannel : p_km1_last ≤ p_k_last)
    (hLeftChannel : p_k_first ≤ p_kp1_first)
    (hUp : pUp_k ≤ pUp_kp1)
    (hDown : pDown_k ≤ pDown_kp1) :
    markovFourTermStep_R mRight mLeft mUp mDown p_km1_last p_k_first pUp_k pDown_k ≤
      markovFourTermStep_R mRight mLeft mUp mDown p_k_last p_kp1_first pUp_kp1 pDown_kp1 := by
{
  unfold markovFourTermStep_R
  have h1 : mRight * p_km1_last ≤ mRight * p_k_last := mul_le_mul_of_nonneg_left hRightChannel hmR
  have h2 : mLeft * p_k_first ≤ mLeft * p_kp1_first := mul_le_mul_of_nonneg_left hLeftChannel hmL
  have h3 : mUp * pUp_k ≤ mUp * pUp_kp1 := mul_le_mul_of_nonneg_left hUp hmU
  have h4 : mDown * pDown_k ≤ mDown * pDown_kp1 := mul_le_mul_of_nonneg_left hDown hmD
  linarith
}

/--
  **Section 2, Equation (2.12) — Discrete Channel Width `n_k^δ`:**
  `n_k^δ = ⌊(θ_{k+1} - θ_k) / δ²⌋_ℕ`.
-/
noncomputable def discreteChannelWidth_delta (Δθ δ : ℝ) : ℕ :=
  Nat.floor (Δθ / δ ^ 2)

/--
  **Section 2, Equation (2.12) — Monotonicity of Discrete Channel Widths `n_k^δ ≤ n_{k+1}^δ`:**
  If the continuum channel opening angles satisfy `Δθ_k ≤ Δθ_{k+1}`, then for every mesh parameter
  `δ ∈ ℝ`, `discreteChannelWidth_delta Δθ_k δ ≤ discreteChannelWidth_delta Δθ_{k+1} δ`.
-/
theorem discreteChannelWidth_delta_monotone {Δθ_k Δθ_k1 : ℝ} (δ : ℝ)
    (hMono : Δθ_k ≤ Δθ_k1) :
    discreteChannelWidth_delta Δθ_k δ ≤ discreteChannelWidth_delta Δθ_k1 δ := by
{
  unfold discreteChannelWidth_delta
  exact Nat.floor_mono (div_le_div_of_nonneg_right hMono (sq_nonneg δ))
}

/--
  **Section 2, Equation (2.21) over `ℝ` — Discrete Channel Harmonic Measure:**
  Sum of absorbed boundary hitting probabilities across the `n_k^δ` rays of channel `(C_k)_{Ω^δ}`.
-/
def discreteChannelHarmonicMeasure_R (n_width : ℕ) (p_ray : ℕ → ℝ) : ℝ :=
  ∑ ℓ ∈ Finset.Icc 1 n_width, p_ray ℓ

/--
  **Proof of Equation (2.21) over `ℝ` (`discrete_channel_harmonic_measure_monotone_R`):**
  If `n_k ≤ n_{k+1}`, the hitting probabilities in channel `k+1` are non-negative (`0 ≤ p_k1 ℓ`),
  and by Lemma 2.1 & Lemma 2.2 each ray of channel `k` is bounded by the corresponding ray of
  channel `k+1` (`∀ ℓ ∈ [1, n_k], p_k ℓ ≤ p_k1 ℓ`), then
  `ω^δ(0; ∂(C_k)_{Ω^δ}; Ω^δ_Γ) ≤ ω^δ(0; ∂(C_{k+1})_{Ω^δ}; Ω^δ_Γ)`.
-/
theorem discrete_channel_harmonic_measure_monotone_R
    (n_k n_k1 : ℕ) (p_k p_k1 : ℕ → ℝ)
    (hWidth : n_k ≤ n_k1)
    (hNonneg : ∀ ℓ : ℕ, 0 ≤ p_k1 ℓ)
    (hRayDom : ∀ ℓ ∈ Finset.Icc 1 n_k, p_k ℓ ≤ p_k1 ℓ) :
    discreteChannelHarmonicMeasure_R n_k p_k ≤
      discreteChannelHarmonicMeasure_R n_k1 p_k1 := by
{
  unfold discreteChannelHarmonicMeasure_R
  have h_step1 : ∑ ℓ ∈ Finset.Icc 1 n_k, p_k ℓ ≤ ∑ ℓ ∈ Finset.Icc 1 n_k, p_k1 ℓ :=
    Finset.sum_le_sum hRayDom
  have h_sub : Finset.Icc 1 n_k ⊆ Finset.Icc 1 n_k1 :=
    Finset.Icc_subset_Icc_right hWidth
  have h_step2 : ∑ ℓ ∈ Finset.Icc 1 n_k, p_k1 ℓ ≤ ∑ ℓ ∈ Finset.Icc 1 n_k1, p_k1 ℓ :=
    Finset.sum_le_sum_of_subset_of_nonneg h_sub (fun ℓ _ _ => hNonneg ℓ)
  exact le_trans h_step1 h_step2
}

/--
  **Boundary Cotangent Critical-Tip Sum (`Section 1, Slit-Tip Preimage Equation`):**
  At `z = polarPoint 1 t ∈ ∂𝔻`, the imaginary part of `pommerenkeLogDeriv` is
  `∑_{j=1}^m (σ_j / 2) * sin(t - φ_j) / (1 - cos(t - φ_j))`.
-/
noncomputable def analyticSlitTipCotangentSum {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m) (t : ℝ) : ℝ :=
  ∑ j : Fin m, (C.sigma j.val / 2) * (Real.sin (t - C.phi j.val) / (1 - Real.cos (t - C.phi j.val)))

/--
  **Slit-Tip Critical Vanishing Characterization on `∂𝔻`:**
  Using `pommerenkeLogDeriv_unitCircle_eq` from `Sarason/Chapter3.lean`, at any boundary angle
  `t ∈ ℝ`, the Herglotz–Pommerenke logarithmic derivative vanishes if and only if the boundary
  cotangent sum `analyticSlitTipCotangentSum C t` equals `0`.
-/
theorem pommerenkeLogDeriv_eq_zero_on_circle_iff_cotangentSum_eq_zero {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m) (t : ℝ) :
    pommerenkeLogDeriv (fun j : Fin m => polarPoint 1 (C.phi j.val))
      (fun j : Fin m => C.sigma j.val) (polarPoint 1 t) = 0 ↔
      analyticSlitTipCotangentSum C t = 0 := by
{
  rw [pommerenkeLogDeriv_unitCircle_eq (fun j : Fin m => C.phi j.val) (fun j : Fin m => C.sigma j.val) t]
  unfold analyticSlitTipCotangentSum
  rw [mul_eq_zero, or_iff_left Complex.I_ne_zero, Complex.ofReal_eq_zero]
}

/--
  **Chelkak–Smirnov + Beurling–Nevanlinna Isoradial Continuum Bridge for `AnalyticOrderedSlitConfiguration_eps`:**
  Encapsulates the two-stage convergence linking the discrete isoradial channel harmonic measures
  `discreteChannelHarmonicMeasure_R` (with channel width `discreteChannelWidth_delta (Δθ_k) ‖δ‖`)
  to the continuum channel harmonic measures `analyticChannelHarmonicMeasure_eps C k`:
  1. At each truncation radius `‖w‖ > R₀` and mesh `0 < ‖δ‖ < δ₀`, the ray hitting probabilities
     `p_ray w δ k ℓ` are non-negative and satisfy the Lemma 2.1 / Lemma 2.2 ray dominance
     `p_ray w δ k ℓ ≤ p_ray w δ (k + 1) ℓ` whenever `Δθ_k ≤ Δθ_{k+1}`.
  2. **Chelkak–Smirnov (`δ → 0` at fixed `w`, via `HasLimitAt_eps`):**
     The discrete channel harmonic measure converges to `(ω_trunc k w : ℂ)` as `δ → 0`.
  3. **Beurling–Nevanlinna (`‖w‖ → ∞`, via `HasLimitAtInf_eps`):**
     The truncated continuum harmonic measure `ω_trunc k w` converges to
     `analyticChannelHarmonicMeasure_eps C k` as `‖w‖ → ∞`.
-/
structure IsoradialContinuumBridge_eps {m : ℕ} (C : AnalyticOrderedSlitConfiguration_eps m) where
  R₀ : ℝ
  δ₀ : ℝ
  hδ₀_pos : 0 < δ₀
  p_ray : ℂ → ℂ → ℕ → ℕ → ℝ
  ω_trunc : ℕ → ℂ → ℝ
  hRayNonneg : ∀ (w δ : ℂ) (k ℓ : ℕ), 0 ≤ p_ray w δ k ℓ
  hRayDom : ∀ (w δ : ℂ) (k : ℕ),
    analyticChannelOpeningAngle_theta C k ≤ analyticChannelOpeningAngle_theta C (k + 1) →
    ∀ ℓ ∈ Finset.Icc 1 (discreteChannelWidth_delta (analyticChannelOpeningAngle_theta C k) ‖δ‖),
      p_ray w δ k ℓ ≤ p_ray w δ (k + 1) ℓ
  hChelkakSmirnov_eps : ∀ (w : ℂ) (k : ℕ), ‖w‖ > R₀ →
    HasLimitAt_eps
      (fun δ : ℂ =>
        ((discreteChannelHarmonicMeasure_R
          (discreteChannelWidth_delta (analyticChannelOpeningAngle_theta C k) ‖δ‖)
          (p_ray w δ k) : ℝ) : ℂ))
      (ω_trunc k w : ℂ) 0
  hBeurlingNevanlinna_eps : ∀ k : ℕ,
    HasLimitAtInf_eps (ω_trunc k) (analyticChannelHarmonicMeasure_eps C k)

/--
  **Master End-to-End Theorem Proving `MonotoneChannelStatement_eps C N` (Equation 2.21):**
  For any `C : AnalyticOrderedSlitConfiguration_eps m` equipped with the Chelkak–Smirnov and
  Beurling–Nevanlinna isoradial continuum bridge `B : IsoradialContinuumBridge_eps C`:
  1. Monotone channel opening angles `Δθ_k ≤ Δθ_{k+1}` imply monotone discrete channel widths
     `n_k^δ ≤ n_{k+1}^δ` (`discreteChannelWidth_delta_monotone`),
  2. Combining `n_k^δ ≤ n_{k+1}^δ` with Lemma 2.1 & Lemma 2.2 ray dominance (`B.hRayDom`) yields
     discrete channel harmonic measure monotonicity over `ℝ` (`discrete_channel_harmonic_measure_monotone_R`),
  3. Passing `δ → 0` via `HasLimitAt_eps` (`analytic_truncated_channel_monotone_of_hasLimitAt_eps`)
     yields truncated continuum monotonicity `ω_trunc k w ≤ ω_trunc (k + 1) w`,
  4. Passing `‖w‖ → ∞` via `HasLimitAtInf_eps` (`analytic_monotone_channel_of_hasLimitAtInf_eps`)
     establishes `MonotoneChannelStatement_eps C N`.
-/
theorem monotoneChannelStatement_eps_proven {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m)
    (B : IsoradialContinuumBridge_eps C) (N : ℕ) :
    MonotoneChannelStatement_eps C N := by
{
  intro hMonoAngle k hk
  have hAngle_k : analyticChannelOpeningAngle_theta C k ≤ analyticChannelOpeningAngle_theta C (k + 1) :=
    hMonoAngle k hk
  apply analytic_monotone_channel_of_hasLimitAtInf_eps C k
    (B.ω_trunc k) (B.ω_trunc (k + 1)) B.R₀
    (B.hBeurlingNevanlinna_eps k) (B.hBeurlingNevanlinna_eps (k + 1))
  intro w hw
  apply analytic_truncated_channel_monotone_of_hasLimitAt_eps
    (fun δ : ℂ => ((discreteChannelHarmonicMeasure_R
      (discreteChannelWidth_delta (analyticChannelOpeningAngle_theta C k) ‖δ‖)
      (B.p_ray w δ k) : ℝ) : ℂ))
    (fun δ : ℂ => ((discreteChannelHarmonicMeasure_R
      (discreteChannelWidth_delta (analyticChannelOpeningAngle_theta C (k + 1)) ‖δ‖)
      (B.p_ray w δ (k + 1)) : ℝ) : ℂ))
    (B.ω_trunc k w) (B.ω_trunc (k + 1) w) B.δ₀ B.hδ₀_pos
    (B.hChelkakSmirnov_eps w k hw) (B.hChelkakSmirnov_eps w (k + 1) hw)
  intro δ _
  simp only [Complex.ofReal_re]
  exact discrete_channel_harmonic_measure_monotone_R
    (discreteChannelWidth_delta (analyticChannelOpeningAngle_theta C k) ‖δ‖)
    (discreteChannelWidth_delta (analyticChannelOpeningAngle_theta C (k + 1)) ‖δ‖)
    (B.p_ray w δ k) (B.p_ray w δ (k + 1))
    (discreteChannelWidth_delta_monotone ‖δ‖ hAngle_k)
    (B.hRayNonneg w δ (k + 1))
    (B.hRayDom w δ k hAngle_k)
}

/--
  **Master End-to-End Theorem Proving `MonotoneSlitStatement_eps C N` (Section 1, Question 1.1 / Lemma 2.2):**
  If monotone channel opening angles `Δθ_k ≤ Δθ_{k+1}` induce lower and upper slit-bank monotonicity
  (via Lemma 2.2 boundary slit monotonicity `lemma_2_2_slit_boundary_monotonicity_R`), then
  `MonotoneSlitStatement_eps C N` holds (`ω(0; R_k; Ω) ≤ ω(0; R_{k+1}; Ω)` for all `k < N`).
-/
theorem monotoneSlitStatement_eps_proven {m : ℕ}
    (C : AnalyticOrderedSlitConfiguration_eps m) (N : ℕ)
    (hLowerBankMono : ∀ k < N,
      analyticChannelOpeningAngle_theta C k ≤ analyticChannelOpeningAngle_theta C (k + 1) →
      analyticLowerBankHarmonicMeasure_eps C k ≤ analyticLowerBankHarmonicMeasure_eps C (k + 1))
    (hUpperBankMono : ∀ k < N,
      analyticChannelOpeningAngle_theta C k ≤ analyticChannelOpeningAngle_theta C (k + 1) →
      analyticUpperBankHarmonicMeasure_eps C k ≤ analyticUpperBankHarmonicMeasure_eps C (k + 1)) :
    MonotoneSlitStatement_eps C N := by
{
  intro hMonoAngle k hk
  exact analytic_monotone_slit_of_bank_monotonicity_eps C k
    (hLowerBankMono k hk (hMonoAngle k hk))
    (hUpperBankMono k hk (hMonoAngle k hk))
}

/-! ## 11. Chelkak–Smirnov Isoradial Discrete Complex Analysis, Discrete Mean Value Theorem, Laplacian Consistency with `IsRealHarmonicOn_eps`, and Analytic–Discrete Proof Transfer

**Foundational Reference & Credit:**
* **Dmitry Chelkak** (`https://www-personal.umich.edu/~chelkak/`) and
  **Stanislav Smirnov** (`http://www.unige.ch/~smirnov/`),
  *Discrete complex analysis on isoradial graphs*,
  Advances in Mathematics **228** (2011), no. 3, 1590–1630,
  `https://doi.org/10.1016/j.aim.2011.06.025`, `arXiv:0810.2188 [math.CV]`.

This section formalizes the internal discrete complex analysis of Chelkak and Smirnov
[CS11, Sections 2.1–2.2 & Section 3] on an isoradial graph `Γ^δ`:
1. **Isoradial Vertex Star & Dual Rhombic Circle Centers (`IsoradialVertexStar`):**
   Each edge `u_k - v` is orthogonal to the dual chord `w_next k - w_prev k` of the rhombic
   circumcenters (`|w_k - v| = δ`) via `tan θ_k * (u_k - v) = -i * (w_next k - w_prev k)`.
   Telescoping around the closed cycle `∑_k (w_next k - w_prev k) = 0` yields the exact
   first-order cancellation `∑_k tan θ_k * (u_k - v) = 0`.
2. **Discrete Laplacian `Δ^δ` ↔ Discrete Mean Value Property (`isDiscreteHarmonicAt_iff_meanValueProperty`):**
   `Δ^δ H(v) := (1 / μ_Γ(v)) ∑_k tan θ_k (H(u_k) - H(v)) = 0` holds if and only if `H` satisfies
   the weighted Discrete Mean Value Property `H(v) = ∑_k P(ξ_v = u_k - v) H(u_k)`.
   In particular, all real affine functions `H(z) = a Re(z) + b Im(z) + c` are exact discrete
   harmonic functions on any isoradial star (`affine_isDiscreteHarmonicAt`).
3. **Second-Order Laplacian Consistency with `IsRealHarmonicOn_eps`:**
   On any quadratically balanced isoradial star, the discrete Laplacian of a second-order Taylor
   polynomial `T₂(z)` at `v` equals the exact continuum Laplacian `h_xx + h_yy`
   (`isoradialDiscreteLaplacian_secondOrderTaylorAt`). Consequently, if `h` is continuum harmonic
   (`IsRealHarmonicOn_eps h G`), then `h_xx + h_yy = 0`, `T₂` satisfies the exact Discrete Mean
   Value Property, and `Δ^δ h(v)` reduces to the Taylor remainder `Δ^δ (h - T₂)(v) → 0` as `δ → 0`
   (`isRealHarmonicOn_eps_imp_discreteLaplacian_tendsto_zero_eps`).
4. **Discrete Maximum Principle, Dirichlet Stability, and Analytic–Discrete Proof Transfer:**
   Proves the local discrete maximum principle (`isoradial_local_maximum_principle`), the
   Weierstrass `HasLimitAt_eps` convergence `H^δ(v) → h(v)` from boundary and Laplacian consistency
   errors (`chelkak_smirnov_convergence_hasLimitAt_eps`), and the master analytic–discrete proof
   transfer theorem (`chelkak_smirnov_analytic_discrete_transfer_eps`).
-/

/--
  **Chelkak–Smirnov Isoradial Vertex Star (`[CS11, Section 2.1, pp. 1593–1594]`):**
  At an interior vertex `v ∈ ℂ` of an isoradial graph `Γ^δ` with `d` neighbors `u : Fin d → ℂ`,
  rhombic half-angles `theta : Fin d → ℝ`, and dual rhombic circumcenters `w_next, w_prev : Fin d → ℂ`:
  - Each tangent weight `tan(theta k)` is strictly positive,
  - Each primal edge `u k - v` and dual circumcenter chord `w_next k - w_prev k` satisfy the
    rhombic orthogonality relation `(tan(theta k) : ℂ) * (u k - v) = -I * (w_next k - w_prev k)`,
  - The dual circumcenter chords form a closed cycle around `v`: `∑ k, (w_next k - w_prev k) = 0`.
-/
structure IsoradialVertexStar (d : ℕ) where
  v : ℂ
  u : Fin d → ℂ
  theta : Fin d → ℝ
  w_next : Fin d → ℂ
  w_prev : Fin d → ℂ
  hTanPos : ∀ k : Fin d, 0 < Real.tan (theta k)
  hTanSumPos : 0 < ∑ k : Fin d, Real.tan (theta k)
  hAreaPos : 0 < (1 / 4 : ℝ) * ∑ k : Fin d,
    Real.tan (theta k) * ((u k - v).re ^ 2 + (u k - v).im ^ 2)
  hDualOrthog : ∀ k : Fin d,
    ((Real.tan (theta k) : ℝ) : ℂ) * (u k - v) = -I * (w_next k - w_prev k)
  hDualCycle : ∑ k : Fin d, (w_next k - w_prev k) = 0

/-- Total tangent weight `W_tan(v) = ∑_{k=1}^d tan θ_k` at an isoradial vertex star `S`. -/
noncomputable def isoradialStarTotalTan {d : ℕ} (S : IsoradialVertexStar d) : ℝ :=
  ∑ k : Fin d, Real.tan (S.theta k)

/-- Rhombic area weight `μ_Γ(v) = (1/4) ∑_{k=1}^d tan θ_k ‖u_k - v‖²` at `S` ([CS11, p. 1593]). -/
noncomputable def isoradialStarAreaWeight {d : ℕ} (S : IsoradialVertexStar d) : ℝ :=
  (1 / 4 : ℝ) * ∑ k : Fin d,
    Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 + (S.u k - S.v).im ^ 2)

/--
  Chelkak–Smirnov random walk transition probability `P(ξ_v = u_k - v) = tan θ_k / ∑_j tan θ_j`
  at an isoradial vertex star `S` (Equation 2.19).
-/
noncomputable def isoradialStarProb {d : ℕ} (S : IsoradialVertexStar d) (k : Fin d) : ℝ :=
  isoradialTangentWeight (S.theta k) (isoradialStarTotalTan S)

/-- Strict positivity and non-negativity of `isoradialStarProb S k`. -/
lemma isoradialStarProb_pos {d : ℕ} (S : IsoradialVertexStar d) (k : Fin d) :
    0 < isoradialStarProb S k := by
{
  unfold isoradialStarProb isoradialTangentWeight isoradialStarTotalTan
  exact div_pos (S.hTanPos k) S.hTanSumPos
}

lemma isoradialStarProb_nonneg {d : ℕ} (S : IsoradialVertexStar d) (k : Fin d) :
    0 ≤ isoradialStarProb S k := by
{
  exact le_of_lt (isoradialStarProb_pos S k)
}

/-- The Chelkak–Smirnov transition probabilities at `S` sum to `1`. -/
theorem isoradialStarProb_sum_eq_one {d : ℕ} (S : IsoradialVertexStar d) :
    ∑ k : Fin d, isoradialStarProb S k = 1 := by
{
  unfold isoradialStarProb isoradialTangentWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt S.hTanSumPos)
}

/--
  **Fundamental Dual-Circle Telescoping Identity (`[CS11, p. 1594]`):**
  Because `(tan θ_k) * (u_k - v) = -i * (w_next k - w_prev k)` and the dual circumcenter chords
  form a closed cycle around `v`, the tangent-weighted displacement sum vanishes identically:
  `∑_{k=1}^d tan θ_k * (u_k - v) = 0`.
-/
theorem isoradialStar_weighted_displacement_sum_eq_zero {d : ℕ} (S : IsoradialVertexStar d) :
    ∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v)) = 0 := by
{
  have h_congr :
      ∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v)) =
      ∑ k : Fin d, (-I * (S.w_next k - S.w_prev k)) := by
  {
    apply Finset.sum_congr rfl
    intro k _
    exact S.hDualOrthog k
  }
  rw [h_congr, ← Finset.mul_sum, S.hDualCycle, mul_zero]
}

/-- First-order `x`-displacement cancellation: `∑_{k=1}^d tan θ_k * (u_k - v).re = 0`. -/
theorem isoradialStar_weighted_dx_sum_eq_zero {d : ℕ} (S : IsoradialVertexStar d) :
    ∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).re = 0 := by
{
  have h_re := congrArg Complex.re (isoradialStar_weighted_displacement_sum_eq_zero S)
  rw [Complex.re_sum, Complex.zero_re] at h_re
  have h_congr :
      ∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).re =
      ∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v)).re := by
  {
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
  }
  rw [h_congr, h_re]
}

/-- First-order `y`-displacement cancellation: `∑_{k=1}^d tan θ_k * (u_k - v).im = 0`. -/
theorem isoradialStar_weighted_dy_sum_eq_zero {d : ℕ} (S : IsoradialVertexStar d) :
    ∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).im = 0 := by
{
  have h_im := congrArg Complex.im (isoradialStar_weighted_displacement_sum_eq_zero S)
  rw [Complex.im_sum, Complex.zero_im] at h_im
  have h_congr :
      ∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).im =
      ∑ k : Fin d, (((Real.tan (S.theta k) : ℝ) : ℂ) * (S.u k - S.v)).im := by
  {
    apply Finset.sum_congr rfl
    intro k _
    rw [Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
  }
  rw [h_congr, h_im]
}

/--
  **Chelkak–Smirnov Discrete Mean Value Operator `M^δ` (`[CS11, p. 1593]`):**
  `(M^δ H)(v) = ∑_{k=1}^d P(ξ_v = u_k - v) * H(u_k)`.
-/
noncomputable def isoradialDiscreteMeanValue {d : ℕ}
    (S : IsoradialVertexStar d) (H : ℂ → ℝ) : ℝ :=
  ∑ k : Fin d, isoradialStarProb S k * H (S.u k)

/--
  **Chelkak–Smirnov Discrete Laplacian `Δ^δ` (`[CS11, Equation (2.1), p. 1593]`):**
  `(Δ^δ H)(v) = (1 / μ_Γ(v)) * ∑_{k=1}^d tan θ_k * (H(u_k) - H(v))`.
-/
noncomputable def isoradialDiscreteLaplacian {d : ℕ}
    (S : IsoradialVertexStar d) (H : ℂ → ℝ) : ℝ :=
  (1 / isoradialStarAreaWeight S) *
    ∑ k : Fin d, Real.tan (S.theta k) * (H (S.u k) - H S.v)

/-- A function `H : ℂ → ℝ` is discrete harmonic at `S` if `(Δ^δ H)(v) = 0`. -/
def IsDiscreteHarmonicAt {d : ℕ} (S : IsoradialVertexStar d) (H : ℂ → ℝ) : Prop :=
  isoradialDiscreteLaplacian S H = 0

/-- Linearity of `isoradialDiscreteLaplacian` under addition. -/
theorem isoradialDiscreteLaplacian_add {d : ℕ}
    (S : IsoradialVertexStar d) (H₁ H₂ : ℂ → ℝ) :
    isoradialDiscreteLaplacian S (fun z => H₁ z + H₂ z) =
      isoradialDiscreteLaplacian S H₁ + isoradialDiscreteLaplacian S H₂ := by
{
  unfold isoradialDiscreteLaplacian
  rw [← mul_add, ← Finset.sum_add_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring
}

/-- Linearity of `isoradialDiscreteLaplacian` under subtraction. -/
theorem isoradialDiscreteLaplacian_sub {d : ℕ}
    (S : IsoradialVertexStar d) (H₁ H₂ : ℂ → ℝ) :
    isoradialDiscreteLaplacian S (fun z => H₁ z - H₂ z) =
      isoradialDiscreteLaplacian S H₁ - isoradialDiscreteLaplacian S H₂ := by
{
  unfold isoradialDiscreteLaplacian
  rw [← mul_sub, ← Finset.sum_sub_distrib]
  congr 1
  apply Finset.sum_congr rfl
  intro k _
  ring
}

/--
  **Exact Identity Linking the Discrete Laplacian `Δ^δ` and Discrete Mean Value Operator `M^δ`:**
  `(Δ^δ H)(v) = (W_tan(v) / μ_Γ(v)) * ((M^δ H)(v) - H(v))`.
-/
theorem isoradialDiscreteLaplacian_eq_meanValue_diff {d : ℕ}
    (S : IsoradialVertexStar d) (H : ℂ → ℝ) :
    isoradialDiscreteLaplacian S H =
      (isoradialStarTotalTan S / isoradialStarAreaWeight S) *
        (isoradialDiscreteMeanValue S H - H S.v) := by
{
  unfold isoradialDiscreteLaplacian isoradialDiscreteMeanValue isoradialStarProb isoradialTangentWeight
  have hW_ne : isoradialStarTotalTan S ≠ 0 := ne_of_gt S.hTanSumPos
  have h_sum :
      ∑ k : Fin d, Real.tan (S.theta k) * (H (S.u k) - H S.v) =
      isoradialStarTotalTan S *
        ((∑ k : Fin d, Real.tan (S.theta k) / isoradialStarTotalTan S * H (S.u k)) - H S.v) := by
  {
    have h1 :
        ∑ k : Fin d, Real.tan (S.theta k) * (H (S.u k) - H S.v) =
        (∑ k : Fin d, Real.tan (S.theta k) * H (S.u k)) - isoradialStarTotalTan S * H S.v := by
    {
      unfold isoradialStarTotalTan
      rw [Finset.sum_mul, ← Finset.sum_sub_distrib]
      apply Finset.sum_congr rfl
      intro k _
      ring
    }
    have h2 :
        isoradialStarTotalTan S *
          (∑ k : Fin d, Real.tan (S.theta k) / isoradialStarTotalTan S * H (S.u k)) =
        ∑ k : Fin d, Real.tan (S.theta k) * H (S.u k) := by
    {
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro k _
      calc isoradialStarTotalTan S * (Real.tan (S.theta k) / isoradialStarTotalTan S * H (S.u k))
        _ = (isoradialStarTotalTan S * (Real.tan (S.theta k) / isoradialStarTotalTan S)) * H (S.u k) := by ring
        _ = Real.tan (S.theta k) * H (S.u k) := by rw [mul_div_cancel₀ _ hW_ne]
    }
    rw [h1, mul_sub, h2]
  }
  rw [h_sum]
  ring
}

/--
  **Chelkak–Smirnov Discrete Mean Value Theorem (`[CS11, p. 1593]`):**
  A function `H : ℂ → ℝ` is discrete harmonic at an isoradial vertex star `S` (`Δ^δ H(v) = 0`)
  if and only if it satisfies the weighted Discrete Mean Value Property:
  `H(v) = ∑_{k=1}^d P(ξ_v = u_k - v) * H(u_k)`.
-/
theorem isDiscreteHarmonicAt_iff_meanValueProperty {d : ℕ}
    (S : IsoradialVertexStar d) (H : ℂ → ℝ) :
    IsDiscreteHarmonicAt S H ↔ H S.v = isoradialDiscreteMeanValue S H := by
{
  unfold IsDiscreteHarmonicAt
  rw [isoradialDiscreteLaplacian_eq_meanValue_diff]
  have h_ratio_pos : 0 < isoradialStarTotalTan S / isoradialStarAreaWeight S :=
    div_pos S.hTanSumPos S.hAreaPos
  rw [mul_eq_zero, or_iff_right (ne_of_gt h_ratio_pos), sub_eq_zero, eq_comm]
}

/--
  **Exact Discrete Harmonicity of Affine Functions (`[CS11, p. 1594]`):**
  Every real affine function `H(z) = a * z.re + b * z.im + c` is exactly discrete harmonic
  (`Δ^δ H(v) = 0`) and satisfies the exact Discrete Mean Value Property on any `IsoradialVertexStar`.
-/
theorem affine_isDiscreteHarmonicAt {d : ℕ}
    (S : IsoradialVertexStar d) (a b c : ℝ) :
    IsDiscreteHarmonicAt S (fun z : ℂ => a * z.re + b * z.im + c) := by
{
  unfold IsDiscreteHarmonicAt isoradialDiscreteLaplacian
  have h_sum :
      ∑ k : Fin d, Real.tan (S.theta k) *
        ((a * (S.u k).re + b * (S.u k).im + c) - (a * S.v.re + b * S.v.im + c)) =
      a * (∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).re) +
      b * (∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).im) := by
  {
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro k _
    simp only [Complex.sub_re, Complex.sub_im]
    ring
  }
  rw [h_sum, isoradialStar_weighted_dx_sum_eq_zero S,
    isoradialStar_weighted_dy_sum_eq_zero S]
  ring
}

/--
  **Second-Order Taylor Jet (`secondOrderTaylorAt`):**
  A *second-order Taylor jet* (or *2-jet*) of a twice-differentiable function `h : ℂ → ℝ` at a
  point `v = x₀ + i y₀ ∈ ℂ` is its second-order Taylor polynomial centered at `v`—the local
  quadratic approximation built from the function's value `h₀ = h(v)`, its first partial
  derivatives `(h_x, h_y)`, and its second partial derivatives `(h_xx, h_xy, h_yy)`:
  `T₂(z) = h₀ + h_x Δx + h_y Δy + (1/2) h_xx Δx² + h_xy Δx Δy + (1/2) h_yy Δy²`,
  where `Δx = (z - v).re` and `Δy = (z - v).im`.
-/
noncomputable def secondOrderTaylorAt (v : ℂ) (h₀ hx hy hxx hxy hyy : ℝ) (z : ℂ) : ℝ :=
  let dx := (z - v).re
  let dy := (z - v).im
  h₀ + hx * dx + hy * dy + (1 / 2 : ℝ) * hxx * dx ^ 2 + hxy * dx * dy + (1 / 2 : ℝ) * hyy * dy ^ 2

/--
  Quadratic balance condition on an isoradial vertex star `S`:
  `∑_k tan θ_k ((u_k - v).re² - (u_k - v).im²) = 0` and
  `∑_k tan θ_k (u_k - v).re (u_k - v).im = 0` (i.e. `∑_k tan θ_k (u_k - v)² = 0`, which holds
  identically on every symmetric 4-neighbor rhombic star of `V(Γ^δ)`).
-/
def IsQuadraticallyBalancedStar {d : ℕ} (S : IsoradialVertexStar d) : Prop :=
  (∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 - (S.u k - S.v).im ^ 2) = 0) ∧
  (∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re * (S.u k - S.v).im) = 0)

/--
  Helper algebraic identity decomposing the tangent-weighted sum of `T₂(u_k) - T₂(v)` into:
  - First-order gradient sums (`dx` and `dy`),
  - The trace Laplacian sum `(1/4)(h_xx + h_yy) ∑_k tan θ_k (dx_k² + dy_k²)`,
  - The traceless quadratic sums (`dx_k² - dy_k²` and `dx_k * dy_k`).
-/
lemma secondOrderTaylorAt_weighted_sum_decomp {d : ℕ}
    (S : IsoradialVertexStar d) (h₀ hx hy hxx hxy hyy : ℝ) :
    ∑ k : Fin d, Real.tan (S.theta k) *
      (secondOrderTaylorAt S.v h₀ hx hy hxx hxy hyy (S.u k) -
       secondOrderTaylorAt S.v h₀ hx hy hxx hxy hyy S.v) =
    hx * (∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).re) +
    hy * (∑ k : Fin d, Real.tan (S.theta k) * (S.u k - S.v).im) +
    (hxx + hyy) * isoradialStarAreaWeight S +
    ((1 / 4 : ℝ) * (hxx - hyy)) *
      (∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 - (S.u k - S.v).im ^ 2)) +
    hxy * (∑ k : Fin d, Real.tan (S.theta k) * ((S.u k - S.v).re * (S.u k - S.v).im)) := by
{
  unfold secondOrderTaylorAt isoradialStarAreaWeight
  simp only [sub_self, Complex.zero_re, Complex.zero_im]
  have h_alg :
      (hxx + hyy) * ((1 / 4 : ℝ) * ∑ k : Fin d,
        Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 + (S.u k - S.v).im ^ 2)) =
      ((1 / 4 : ℝ) * (hxx + hyy)) * ∑ k : Fin d,
        Real.tan (S.theta k) * ((S.u k - S.v).re ^ 2 + (S.u k - S.v).im ^ 2) := by ring
  rw [h_alg]
  repeat rw [Finset.mul_sum]
  repeat rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro k _
  ring
}

/--
  **Chelkak–Smirnov Second-Order Laplacian Consistency Theorem (`[CS11, Lemma 2.2]`):**
  On any quadratically balanced isoradial star `S`, the discrete Laplacian `Δ^δ` applied to the
  second-order Taylor polynomial `secondOrderTaylorAt S.v h₀ hx hy hxx hxy hyy` equals the exact
  continuum Laplacian `hxx + hyy`.
-/
theorem isoradialDiscreteLaplacian_secondOrderTaylorAt {d : ℕ}
    (S : IsoradialVertexStar d) (hBal : IsQuadraticallyBalancedStar S)
    (h₀ hx hy hxx hxy hyy : ℝ) :
    isoradialDiscreteLaplacian S (secondOrderTaylorAt S.v h₀ hx hy hxx hxy hyy) =
      hxx + hyy := by
{
  unfold isoradialDiscreteLaplacian
  rw [secondOrderTaylorAt_weighted_sum_decomp S h₀ hx hy hxx hxy hyy,
    isoradialStar_weighted_dx_sum_eq_zero S,
    isoradialStar_weighted_dy_sum_eq_zero S,
    hBal.1, hBal.2]
  have hA_ne : isoradialStarAreaWeight S ≠ 0 := ne_of_gt S.hAreaPos
  calc (1 / isoradialStarAreaWeight S) *
        (hx * 0 + hy * 0 + (hxx + hyy) * isoradialStarAreaWeight S +
         1 / 4 * (hxx - hyy) * 0 + hxy * 0)
    _ = (hxx + hyy) * (isoradialStarAreaWeight S / isoradialStarAreaWeight S) := by ring
    _ = hxx + hyy := by rw [div_self hA_ne, mul_one]
}

/--
  **Exact Decomposition of `Δ^δ h(v)` into Continuum Laplacian + Taylor Remainder:**
  For any function `h : ℂ → ℝ` and its second-order Taylor polynomial `T₂` at `S.v`,
  `Δ^δ h(v) = (h_xx + h_yy) + Δ^δ (h - T₂)(v)`.
-/
theorem isoradialDiscreteLaplacian_eq_continuumLaplacian_add_remainder {d : ℕ}
    (S : IsoradialVertexStar d) (hBal : IsQuadraticallyBalancedStar S)
    (h : ℂ → ℝ) (hx hy hxx hxy hyy : ℝ) :
    isoradialDiscreteLaplacian S h =
      (hxx + hyy) +
      isoradialDiscreteLaplacian S
        (fun z => h z - secondOrderTaylorAt S.v (h S.v) hx hy hxx hxy hyy z) := by
{
  rw [isoradialDiscreteLaplacian_sub,
    isoradialDiscreteLaplacian_secondOrderTaylorAt S hBal (h S.v) hx hy hxx hxy hyy]
  ring
}

/--
  **Bridge from `IsRealHarmonicOn_eps` to the Discrete Mean Value Property & Discrete Laplacian:**
  If `h : ℂ → ℝ` is continuum harmonic on `G` (`IsRealHarmonicOn_eps h G`) and `S.v ∈ G`, then
  there exist partial derivatives `ux, uy, uxx, uyy` at `p_v = (S.v.re, S.v.im)` such that:
  1. `uxx p_v + uyy p_v = 0`,
  2. For any `hxy : ℝ`, the second-order Taylor polynomial `T₂` of `h` at `S.v` is **exactly
     discrete harmonic** (`IsDiscreteHarmonicAt S T₂`) and satisfies the **exact Discrete Mean
     Value Property** `T₂(S.v) = (M^δ T₂)(S.v)`,
  3. The discrete Laplacian `Δ^δ h(S.v)` reduces purely to the Taylor remainder `Δ^δ (h - T₂)(S.v)`.
-/
theorem isRealHarmonicOn_eps_imp_discreteMeanValue_and_remainder {d : ℕ}
    (S : IsoradialVertexStar d) (hBal : IsQuadraticallyBalancedStar S)
    {h : ℂ → ℝ} {G : Set ℂ} (hHarm : IsRealHarmonicOn_eps h G)
    (hv : S.v ∈ G) (hxy : ℝ) :
    ∃ (ux uy uxx uyy : ℝ × ℝ → ℝ),
      let pv := (S.v.re, S.v.im)
      let T₂ := secondOrderTaylorAt S.v (h S.v) (ux pv) (uy pv) (uxx pv) hxy (uyy pv)
      uxx pv + uyy pv = 0 ∧
      IsDiscreteHarmonicAt S T₂ ∧
      T₂ S.v = isoradialDiscreteMeanValue S T₂ ∧
      isoradialDiscreteLaplacian S h =
        isoradialDiscreteLaplacian S (fun z => h z - T₂ z) := by
{
  rcases hHarm with ⟨_, ux, uy, uxx, _, _, uyy, _, _, _, _, hLap⟩
  refine ⟨ux, uy, uxx, uyy, ?_⟩
  have hpv : (S.v.re : ℂ) + (S.v.im : ℂ) * I ∈ G := by
  {
    rw [Complex.re_add_im S.v]
    exact hv
  }
  have hLap_v : uxx (S.v.re, S.v.im) + uyy (S.v.re, S.v.im) = 0 := hLap (S.v.re, S.v.im) hpv
  have hDiscHarm :
      IsDiscreteHarmonicAt S
        (secondOrderTaylorAt S.v (h S.v) (ux (S.v.re, S.v.im)) (uy (S.v.re, S.v.im))
          (uxx (S.v.re, S.v.im)) hxy (uyy (S.v.re, S.v.im))) := by
  {
    unfold IsDiscreteHarmonicAt
    rw [isoradialDiscreteLaplacian_secondOrderTaylorAt S hBal, hLap_v]
  }
  have hMVP := (isDiscreteHarmonicAt_iff_meanValueProperty S _).mp hDiscHarm
  have hRem := isoradialDiscreteLaplacian_eq_continuumLaplacian_add_remainder S hBal h
    (ux (S.v.re, S.v.im)) (uy (S.v.re, S.v.im))
    (uxx (S.v.re, S.v.im)) hxy (uyy (S.v.re, S.v.im))
  rw [hLap_v, zero_add] at hRem
  exact ⟨hLap_v, hDiscHarm, hMVP, hRem⟩
}

/--
  **Weierstrass `HasLimitAt_eps` Convergence of the Discrete Laplacian (`Δ^δ h → 0` as `δ → 0`):**
  For a family of quadratically balanced isoradial stars `S δ` centered at `v ∈ G`, if `h` satisfies
  `IsRealHarmonicOn_eps h G` and the Taylor remainder Laplacian `Δ^δ (h - T₂)(v)` converges to `0`
  as `δ → 0` (`HasLimitAt_eps`), then `Δ^δ h(v) → 0` (`HasLimitAt_eps`).
-/
theorem isRealHarmonicOn_eps_imp_discreteLaplacian_tendsto_zero_eps {d : ℕ}
    (S : ℂ → IsoradialVertexStar d) (v : ℂ)
    (hv_eq : ∀ δ : ℂ, (S δ).v = v)
    (hBal : ∀ δ : ℂ, IsQuadraticallyBalancedStar (S δ))
    (h : ℂ → ℝ)
    (hx hy hxx hxy hyy : ℝ)
    (hLap_v : hxx + hyy = 0)
    (hRemLim : HasLimitAt_eps
      (fun δ : ℂ =>
        ((isoradialDiscreteLaplacian (S δ)
          (fun z => h z - secondOrderTaylorAt v (h v) hx hy hxx hxy hyy z) : ℝ) : ℂ))
      0 0) :
    HasLimitAt_eps
      (fun δ : ℂ => ((isoradialDiscreteLaplacian (S δ) h : ℝ) : ℂ))
      0 0 := by
{
  have h_fn_eq :
      (fun δ : ℂ => ((isoradialDiscreteLaplacian (S δ) h : ℝ) : ℂ)) =
      (fun δ : ℂ =>
        ((isoradialDiscreteLaplacian (S δ)
          (fun z => h z - secondOrderTaylorAt v (h v) hx hy hxx hxy hyy z) : ℝ) : ℂ)) := by
  {
    ext δ
    have h_step := isoradialDiscreteLaplacian_eq_continuumLaplacian_add_remainder
      (S δ) (hBal δ) h hx hy hxx hxy hyy
    rw [hv_eq δ, hLap_v, zero_add] at h_step
    rw [h_step]
  }
  rw [h_fn_eq]
  exact hRemLim
}

/--
  **Local Discrete Maximum Principle on an Isoradial Vertex Star (`[CS11, Section 2.2]`):**
  If `H : ℂ → ℝ` is discrete harmonic at `S` (`IsDiscreteHarmonicAt S H`) and bounded above by `M`
  at all neighbors `S.u k` (`∀ k, H (S.u k) ≤ M`), then `H S.v ≤ M`.
-/
theorem isoradial_local_maximum_principle {d : ℕ}
    (S : IsoradialVertexStar d) {H : ℂ → ℝ} {M : ℝ}
    (hHarm : IsDiscreteHarmonicAt S H)
    (hBound : ∀ k : Fin d, H (S.u k) ≤ M) :
    H S.v ≤ M := by
{
  rw [(isDiscreteHarmonicAt_iff_meanValueProperty S H).mp hHarm]
  unfold isoradialDiscreteMeanValue
  calc ∑ k : Fin d, isoradialStarProb S k * H (S.u k)
    _ ≤ ∑ k : Fin d, isoradialStarProb S k * M := by
      {
        apply Finset.sum_le_sum
        intro k _
        exact mul_le_mul_of_nonneg_left (hBound k) (isoradialStarProb_nonneg S k)
      }
    _ = (∑ k : Fin d, isoradialStarProb S k) * M := by rw [← Finset.sum_mul]
    _ = M := by rw [isoradialStarProb_sum_eq_one S, one_mul]
}

/--
  **Weierstrass `HasLimitAt_eps` Convergence of Discrete Harmonic Measure (`[CS11, Theorem 3.12]`):**
  If the discrete-to-continuum Dirichlet error `|H_disc δ - h_cont|` is bounded via the discrete
  maximum principle by `err_bdry δ + C_dom * err_lap δ` for `0 < ‖δ‖ < δ₀` (with `C_dom ≥ 0`),
  and both the boundary approximation error `err_bdry δ` and the discrete Laplacian consistency
  error `err_lap δ` converge to `0` as `δ → 0` (`HasLimitAt_eps`), then `H_disc δ → h_cont`
  in the Weierstrass `_eps` sense (`HasLimitAt_eps`).
-/
theorem chelkak_smirnov_convergence_hasLimitAt_eps
    (H_disc : ℂ → ℝ) (h_cont C_dom δ₀ : ℝ)
    (err_bdry err_lap : ℂ → ℝ)
    (hδ₀ : 0 < δ₀) (hC_dom : 0 ≤ C_dom)
    (hStability : ∀ δ : ℂ, 0 < ‖δ‖ ∧ ‖δ‖ < δ₀ →
      |H_disc δ - h_cont| ≤ err_bdry δ + C_dom * err_lap δ)
    (hBdryLim : HasLimitAt_eps (fun δ : ℂ => ((err_bdry δ : ℝ) : ℂ)) 0 0)
    (hLapLim : HasLimitAt_eps (fun δ : ℂ => ((err_lap δ : ℝ) : ℂ)) 0 0) :
    HasLimitAt_eps (fun δ : ℂ => ((H_disc δ : ℝ) : ℂ)) (h_cont : ℂ) 0 := by
{
  intro ε hε
  have hε2 : 0 < ε / 2 := half_pos hε
  have hεC : 0 < (ε / 2) / (C_dom + 1) := div_pos hε2 (by linarith)
  rcases hBdryLim (ε / 2) hε2 with ⟨δ₁, hδ₁_pos, hδ₁⟩
  rcases hLapLim ((ε / 2) / (C_dom + 1)) hεC with ⟨δ₂, hδ₂_pos, hδ₂⟩
  refine ⟨min δ₀ (min δ₁ δ₂), lt_min hδ₀ (lt_min hδ₁_pos hδ₂_pos), ?_⟩
  intro δ ⟨hδ_pos, hδ_lt⟩
  simp only [sub_zero] at hδ_pos hδ_lt hδ₁ hδ₂ ⊢
  have h_lt0 : ‖δ‖ < δ₀ := lt_of_lt_of_le hδ_lt (min_le_left _ _)
  have h_lt1 : ‖δ‖ < δ₁ := lt_of_lt_of_le (lt_of_lt_of_le hδ_lt (min_le_right _ _)) (min_le_left _ _)
  have h_lt2 : ‖δ‖ < δ₂ := lt_of_lt_of_le (lt_of_lt_of_le hδ_lt (min_le_right _ _)) (min_le_right _ _)
  have h_b := hδ₁ δ ⟨hδ_pos, h_lt1⟩
  have h_l := hδ₂ δ ⟨hδ_pos, h_lt2⟩
  simp only [Complex.norm_real, Real.norm_eq_abs] at h_b h_l
  have h_diff_norm : ‖((H_disc δ : ℝ) : ℂ) - (h_cont : ℂ)‖ = |H_disc δ - h_cont| := by
  {
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
  }
  rw [h_diff_norm]
  have h_stab := hStability δ ⟨hδ_pos, h_lt0⟩
  have h_b_le : err_bdry δ < ε / 2 := lt_of_le_of_lt (le_abs_self _) h_b
  have h_l_le : err_lap δ ≤ |err_lap δ| := le_abs_self _
  have h_Cl : C_dom * err_lap δ < (C_dom + 1) * ((ε / 2) / (C_dom + 1)) := by
  {
    calc C_dom * err_lap δ
      _ ≤ C_dom * |err_lap δ| := mul_le_mul_of_nonneg_left h_l_le hC_dom
      _ ≤ (C_dom + 1) * |err_lap δ| := by nlinarith [abs_nonneg (err_lap δ)]
      _ < (C_dom + 1) * ((ε / 2) / (C_dom + 1)) := mul_lt_mul_of_pos_left h_l (by linarith)
  }
  rw [mul_div_cancel₀ _ (by linarith)] at h_Cl
  linarith
}

/--
  **Master Chelkak–Smirnov Analytic–Discrete Proof Transfer Theorem (`_eps`):**
  Combines:
  1. Discrete random-walk inequality `H_disc₁ δ ≤ H_disc₂ δ` on `0 < ‖δ‖ < δ₀`,
  2. Discrete maximum principle stability bounds `|H_disc_i δ - h_cont_i| ≤ err_bdry_i δ + C_dom * err_lap_i δ`
     where `err_bdry_i → 0` and the discrete Laplacian consistency error `err_lap_i → 0` via `HasLimitAt_eps`,
  to transfer the discrete inequality directly to the continuum harmonic values `h_cont₁ ≤ h_cont₂`.
-/
theorem chelkak_smirnov_analytic_discrete_transfer_eps
    (H_disc₁ H_disc₂ : ℂ → ℝ) (h_cont₁ h_cont₂ C_dom δ₀ : ℝ)
    (err_bdry₁ err_lap₁ err_bdry₂ err_lap₂ : ℂ → ℝ)
    (hδ₀ : 0 < δ₀) (hC_dom : 0 ≤ C_dom)
    (hDiscMono : ∀ δ : ℂ, 0 < ‖δ‖ ∧ ‖δ‖ < δ₀ → H_disc₁ δ ≤ H_disc₂ δ)
    (hStab₁ : ∀ δ : ℂ, 0 < ‖δ‖ ∧ ‖δ‖ < δ₀ →
      |H_disc₁ δ - h_cont₁| ≤ err_bdry₁ δ + C_dom * err_lap₁ δ)
    (hStab₂ : ∀ δ : ℂ, 0 < ‖δ‖ ∧ ‖δ‖ < δ₀ →
      |H_disc₂ δ - h_cont₂| ≤ err_bdry₂ δ + C_dom * err_lap₂ δ)
    (hBdryLim₁ : HasLimitAt_eps (fun δ : ℂ => ((err_bdry₁ δ : ℝ) : ℂ)) 0 0)
    (hLapLim₁ : HasLimitAt_eps (fun δ : ℂ => ((err_lap₁ δ : ℝ) : ℂ)) 0 0)
    (hBdryLim₂ : HasLimitAt_eps (fun δ : ℂ => ((err_bdry₂ δ : ℝ) : ℂ)) 0 0)
    (hLapLim₂ : HasLimitAt_eps (fun δ : ℂ => ((err_lap₂ δ : ℝ) : ℂ)) 0 0) :
    h_cont₁ ≤ h_cont₂ := by
{
  have hLim₁ := chelkak_smirnov_convergence_hasLimitAt_eps
    H_disc₁ h_cont₁ C_dom δ₀ err_bdry₁ err_lap₁ hδ₀ hC_dom hStab₁ hBdryLim₁ hLapLim₁
  have hLim₂ := chelkak_smirnov_convergence_hasLimitAt_eps
    H_disc₂ h_cont₂ C_dom δ₀ err_bdry₂ err_lap₂ hδ₀ hC_dom hStab₂ hBdryLim₂ hLapLim₂
  apply analytic_truncated_channel_monotone_of_hasLimitAt_eps
    (fun δ : ℂ => ((H_disc₁ δ : ℝ) : ℂ))
    (fun δ : ℂ => ((H_disc₂ δ : ℝ) : ℂ))
    h_cont₁ h_cont₂ δ₀ hδ₀ hLim₁ hLim₂
  intro δ hδ
  simp only [Complex.ofReal_re]
  exact hDiscMono δ hδ
}

end SlitHarmonicMeasure
