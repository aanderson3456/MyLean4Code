import Mathlib
import PNT

open Filter Topology Real

def build_seq_rec (g : ℝ → ℝ) : ℕ → ℝ
| 0 => g 2
| n + 1 => g (build_seq_rec g n)

lemma build_seq {f : ℝ → ℝ} {L : ℝ} (hf : ∃ᶠ x in atTop, L < f x) :
    ∃ seq : ℕ → ℝ, (∀ n, 1 < seq n) ∧ Tendsto seq atTop atTop ∧ ∀ n, L < f (seq n) := by
{
  have hf2 : ∀ a, ∃ b, a + 1 ≤ b ∧ L < f b := by
  {
    intro a
    have h1 : ∃ᶠ x in atTop, L < f x := hf
    rw [Filter.frequently_atTop] at h1
    rcases h1 (max a 1 + 1) with ⟨b, hb1, hb2⟩
    use b
    refine ⟨?_, hb2⟩
    have h_max : a ≤ max a 1 := le_max_left a 1
    linarith
  }
  choose g hg1 hg2 using hf2
  let seq := build_seq_rec g
  have h_seq_ge : ∀ n : ℕ, (n : ℝ) + 2 ≤ seq n := by
  {
    intro n
    induction' n with n ih
    · dsimp [seq, build_seq_rec]
      have h1 := hg1 2
      have h2 : ((0 : ℕ) : ℝ) + 2 = 2 := by push_cast; ring
      linarith
    · dsimp [seq, build_seq_rec]
      have h1 := hg1 (build_seq_rec g n)
      have h2 : (n:ℝ) + 2 + 1 ≤ seq n + 1 := by linarith
      have h3 : ((n + 1 : ℕ) : ℝ) + 2 = (n:ℝ) + 2 + 1 := by push_cast; ring
      linarith
  }
  have h_seq : ∀ n, 1 < seq n := by
  {
    intro n
    have h1 := h_seq_ge n
    have h2 : (1:ℝ) < (n:ℝ) + 2 := by
    {
      have h3 : 0 ≤ (n:ℝ) := Nat.cast_nonneg n
      linarith
    }
    linarith
  }
  have h_tendsto : Tendsto seq atTop atTop := by
  {
    apply tendsto_atTop_mono h_seq_ge
    have h1 : Tendsto (fun n : ℕ => (n : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    exact Tendsto.atTop_add h1 tendsto_const_nhds
  }
  have h_eval : ∀ n, L < f (seq n) := by
  {
    intro n
    cases n
    · dsimp [seq, build_seq_rec]
      exact hg2 2
    · dsimp [seq, build_seq_rec]
      exact hg2 (build_seq_rec g _)
  }
  use seq
  exact ⟨h_seq, h_tendsto, h_eval⟩
}
