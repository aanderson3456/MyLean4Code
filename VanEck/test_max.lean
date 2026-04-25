/-
Copyright (c) 2022, 2026 Justin Kong, Austin Anderson

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/
import VanEck
open Nat

lemma h_VE_ms (k : ℕ) (hk : k ≥ 1) : vanEckNthTerm k = matchSearch (vanEck (k-1)) (k-1) := by {
  have hk1 : k = k - 1 + 1 := (Nat.sub_add_cancel hk).symm
  -- Rewrite ONLY the first two occurrences of k
  -- Instead of generic rewrite, we can just prove it
  have eq : vanEckNthTerm (k - 1 + 1) = matchSearch (vanEck (k - 1)) (k - 1) := by
    unfold vanEckNthTerm
    exact list_nth_VE_eq_ms (k - 1)
  have eq2 : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [eq2] at eq
  exact eq
}

lemma h_listNth_ve (n d : ℕ) (h : d ≤ n) : listNth (vanEck n) d = vanEckNthTerm d := by {
  unfold vanEckNthTerm
  exact (VanEck_deterministic n d h)
}

lemma max_value_implies_M_eq_one_aux (n M k : ℕ) (h_bound : ∀ j ≥ n, vanEckNthTerm j ≤ M)
    (hk : k ≥ n + M)
    (h_kM : vanEckNthTerm k = M)
    (h_no_zeros : ∀ j ≥ n, vanEckNthTerm j ≠ 0) : M = 1 := by {
  have hk_pos : k ≥ 1 := by
    -- k >= n + M. Since h_kM is M, we need to show M \neq 0.
    have h1 : vanEckNthTerm k ≠ 0 := h_no_zeros k (Nat.le_trans (Nat.le_add_right n M) hk)
    rw [h_kM] at h1
    have hM_pos : M > 0 := Nat.pos_of_ne_zero h1
    -- k >= n + M >= M >= 1
    have h2 : k ≥ M := Nat.le_trans (Nat.le_add_left M n) hk
    exact Nat.le_trans hM_pos h2
  
  have hM_pos : M > 0 := by
    have h1 : vanEckNthTerm k ≠ 0 := h_no_zeros k (Nat.le_trans (Nat.le_add_right n M) hk)
    rw [h_kM] at h1
    exact Nat.pos_of_ne_zero h1

  have h_vanEck_len : (vanEck (k - 1)).length - 1 = k - 1 := by
    rw [vanEckLength (k - 1), Nat.add_sub_cancel]

  have hm_ms : matchSearch (vanEck (k-1)) (k-1) = M := by
    have h1 := h_VE_ms k hk_pos
    rw [← h_kM]
    exact h1.symm

  have h_match : listNth (vanEck (k-1)) (k-1) = listNth (vanEck (k-1)) (k-1-M) := by
    have h_neq : matchSearch (vanEck (k-1)) (k-1) ≠ 0 := by rw [hm_ms]; exact Nat.ne_of_gt hM_pos
    have h1 := matchSearch_matches (vanEck (k-1)) (k-1) h_neq
    rw [h_vanEck_len] at h1
    rw [hm_ms] at h1
    exact h1

  -- To prove M = 1, we use a forward bounded loop tracking.
  -- Rather than manually evaluating index collisions, we know the sequence must be periodic!
  sorry
}
