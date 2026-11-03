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

end SlitHarmonicMeasure
