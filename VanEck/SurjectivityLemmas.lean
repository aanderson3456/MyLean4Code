import VanEck
import ImpossiblePatterns
import LimSup
import Mathlib

lemma vanEck_surjective_zero : ∃ m, vanEckNthTerm m = 0 := by {
  use 0
  exact vanEck_head_eq_zero 0
}

lemma vanEck_surjective_one : ∃ m, vanEckNthTerm m = 1 := by {
  use 2
  rfl
}

lemma vanEck_surjective_two : ∃ m, vanEckNthTerm m = 2 := by {
  use 4
  rfl
}

lemma new_value_next_is_zero (m : ℕ) (h_new : ∀ i < m, vanEckNthTerm i ≠ vanEckNthTerm m) :
    vanEckNthTerm (m + 1) = 0 := by {
  have h_iff := (vanEck_mth_term_eq_zero_iff_prev_term_new m).mpr
  exact h_iff h_new
}

lemma pos_value_implies_gap (m n : ℕ) (hm : m ≥ 2) (h_val : vanEckNthTerm m = n) (h_pos : n > 0) :
    m > n ∧ vanEckNthTerm (m - 1 - n) = vanEckNthTerm (m - 1) := by {
  have h_le : vanEckNthTerm m ≤ m - 1 := a_le_idx_minus_one hm (by rw [h_val]; exact h_pos)
  rw [h_val] at h_le
  have h_m_gt_n : m > n := Nat.lt_of_le_of_lt h_le (Nat.sub_lt (Nat.lt_of_succ_le hm) Nat.zero_lt_one)
  
  have hm_sub : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.le_trans (by decide) hm)
  have h_match : vanEckNthTerm (m - 1 + 1) = matchSearch (vanEck (m - 1)) (m - 1) := vanEck_term_is_matchSearch m (Nat.le_trans (by decide) hm)
  rw [hm_sub] at h_match
  have h_match_eq : matchSearch (vanEck (m - 1)) (m - 1) = n := by
    rw [← h_match]
    exact h_val
  have h_neq : matchSearch (vanEck (m - 1)) (m - 1) ≠ 0 := by
    rw [h_match_eq]
    exact Nat.ne_of_gt h_pos
  have hm_match := matchSearch_matches (vanEck (m - 1)) (m - 1)
  have h_eval := hm_match h_neq
  have h_len : (vanEck (m - 1)).length = m := by
    have h1 := vanEckLength (m - 1)
    rw [hm_sub] at h1
    exact h1
  have h_len_sub_1 : (vanEck (m - 1)).length - 1 = m - 1 := by rw [h_len]
  rw [h_len_sub_1] at h_eval
  rw [h_match_eq] at h_eval
  
  have hd1 : listNth (vanEck (m - 1)) (m - 1) = vanEckNthTerm (m - 1) := by
    exact VanEck_deterministic (m - 1) (m - 1) (Nat.le_refl _)
    
  have hd0 : listNth (vanEck (m - 1)) (m - 1 - n) = vanEckNthTerm (m - 1 - n) := by
    have h_le_n : m - 1 - n ≤ m - 1 := Nat.sub_le _ _
    exact VanEck_deterministic (m - 1) (m - 1 - n) h_le_n
    
  rw [hd1, hd0] at h_eval
  
  exact ⟨h_m_gt_n, h_eval.symm⟩
}

/-!
# Surjectivity Open Problem - Progressive Conjectures

The following 5 theorems represent increasing levels of difficulty towards proving the
full surjectivity of the Van Eck sequence (that it contains every natural number).
-/

/--
Level 1 Conjecture (Easy): The Van Eck sequence is unbounded. 
Since we previously proved that the limsup of a(n)/sqrt(n) >= 1, we know the sequence 
must take arbitrarily large values.
-/
theorem vanEck_unbounded (N : ℕ) : ∃ m : ℕ, vanEckNthTerm m > N := by {
  let N_sq := N * N + 2 * N + 2
  have h_bound := vanEck_limsup_ge_sqrt N_sq
  rcases h_bound with ⟨m, hm_le, hm_ineq⟩
  use m
  by_contra hc
  have h_le : vanEckNthTerm m ≤ N := Nat.le_of_not_lt hc
  have h_ineq_contra : vanEckNthTerm m * vanEckNthTerm m + 2 * vanEckNthTerm m + 1 ≤ N * N + 2 * N + 1 := by nlinarith
  have h_contra : m ≤ N * N + 2 * N + 1 := Nat.le_trans hm_ineq h_ineq_contra
  have h_m_gt : m ≥ N * N + 2 * N + 2 := hm_le
  nlinarith
}

/--
Level 2 Conjecture (Easy): The sequence is not eventually periodic.
Any periodic sequence is bounded. Since we know the sequence is unbounded, 
it cannot be periodic.
-/
theorem vanEck_not_periodic (p : ℕ) (hp : p > 0) : ∀ N, ∃ m > N, vanEckNthTerm m ≠ vanEckNthTerm (m + p) := by {
  intro N
  by_contra hc
  have h_per : ∀ m > N, vanEckNthTerm m = vanEckNthTerm (m + p) := by
    intro m hm
    have h1 : ¬(vanEckNthTerm m ≠ vanEckNthTerm (m + p)) := by
      intro h_neq
      have h_ex : ∃ m > N, vanEckNthTerm m ≠ vanEckNthTerm (m + p) := ⟨m, hm, h_neq⟩
      exact hc h_ex
    exact Classical.not_not.mp h1
    
  have h_per_k : ∀ k m, m > N → vanEckNthTerm m = vanEckNthTerm (m + k * p) := by
    intro k
    induction k with
    | zero => 
      intro m hm
      have hz : m + 0 * p = m := by rw [Nat.zero_mul, Nat.add_zero]
      rw [hz]
    | succ k ih =>
      intro m hm
      have hs : m + (k + 1) * p = m + k * p + p := by
        rw [Nat.add_mul, Nat.one_mul]
        exact (Nat.add_assoc m (k * p) p).symm
      rw [hs]
      have hm_gt : m + k * p > N := Nat.lt_of_lt_of_le hm (Nat.le_add_right m (k * p))
      have h_step := (h_per (m + k * p) hm_gt).symm
      have h_ih := ih m hm
      exact h_ih.trans h_step
      
  let B := vanEckPrefixMax (N + p)
  
  have h_bound : ∀ m > N, vanEckNthTerm m ≤ B := by
    intro m hm
    let d := m - (N + 1)
    let k := d / p
    let r := d % p
    have hd : m = N + 1 + d := (Nat.add_sub_cancel' hm).symm
    have hdr : d = k * p + r := (Nat.div_add_mod d p).symm
    have hr_lt : r < p := Nat.mod_lt d hp
    
    have hm_eq : m = N + 1 + r + k * p := by
      calc m = N + 1 + d := hd
           _ = N + 1 + (k * p + r) := by rw [hdr]
           _ = N + 1 + r + k * p := by rw [Nat.add_assoc, Nat.add_comm (k * p) r, ← Nat.add_assoc]
           
    have h_base_gt : N + 1 + r > N := by
      calc N + 1 + r ≥ N + 1 := Nat.le_add_right (N + 1) r
           _ > N := Nat.lt_succ_self N
           
    have h_eval : vanEckNthTerm (N + 1 + r) = vanEckNthTerm (N + 1 + r + k * p) := h_per_k k (N + 1 + r) h_base_gt
    
    have h_m_val : vanEckNthTerm m = vanEckNthTerm (N + 1 + r) := by
      rw [hm_eq]
      exact h_eval.symm
      
    have h_idx_le : N + 1 + r ≤ N + p := by
      have h1 : r + 1 ≤ p := hr_lt
      calc N + 1 + r = N + (r + 1) := by rw [Nat.add_assoc, Nat.add_comm 1 r]
           _ ≤ N + p := Nat.add_le_add_left h1 N
           
    have h_B : vanEckNthTerm (N + 1 + r) ≤ B := vanEckNthTerm_le_prefixMax (N + p) (N + 1 + r) h_idx_le
    
    rw [h_m_val]
    exact h_B
    
  have h_unb := vanEck_unbounded (max B (vanEckPrefixMax N))
  rcases h_unb with ⟨m, hm_gt⟩
  
  have h_max_B : B ≤ max B (vanEckPrefixMax N) := Nat.le_max_left _ _
  have h_max_N : vanEckPrefixMax N ≤ max B (vanEckPrefixMax N) := Nat.le_max_right _ _
  
  by_cases hm_N : m > N
  · have h1 : vanEckNthTerm m ≤ B := h_bound m hm_N
    have h2 : B < vanEckNthTerm m := Nat.lt_of_le_of_lt h_max_B hm_gt
    have h3 := Nat.lt_of_le_of_lt h1 h2
    exact Nat.lt_irrefl _ h3
  · have hm_le : m ≤ N := Nat.le_of_not_lt hm_N
    have h1 : vanEckNthTerm m ≤ vanEckPrefixMax N := vanEckNthTerm_le_prefixMax N m hm_le
    have h2 : vanEckPrefixMax N < vanEckNthTerm m := Nat.lt_of_le_of_lt h_max_N hm_gt
    have h3 := Nat.lt_of_le_of_lt h1 h2
    exact Nat.lt_irrefl _ h3
}

/--
Intermediate Lemma 1 for `vanEck_not_periodic2`:
If the sequence is eventually periodic with period `p`, then its values in the periodic tail 
are strictly bounded by `p`. This holds because any sequence value $a(m) = x > 0$ represents 
the exact distance to the most recent previous occurrence. Since the sequence is periodic, 
every element must re-appear within `p` steps, capping the maximum possible gap at `p`.
-/
lemma periodic_implies_bounded_by_period (p N : ℕ) (hp : p > 0)
    (h_per : ∀ m > N, vanEckNthTerm m = vanEckNthTerm (m + p)) :
    ∀ m > N + p + 1, vanEckNthTerm m ≤ p := by {
  intro m hm
  by_cases h0 : vanEckNthTerm m = 0
  · rw [h0]; exact Nat.zero_le p
  · have hm_pos : m ≥ 2 := by
      calc m > N + p + 1 := hm
           _ ≥ 0 + 1 + 1 := Nat.add_le_add (Nat.add_le_add (Nat.zero_le N) hp) (Nat.le_refl 1)
           _ = 2 := rfl
    have h_a_def : vanEckNthTerm m = matchSearch (vanEck (m - 1)) (m - 1) := vanEck_term_is_matchSearch m (Nat.lt_of_succ_lt hm_pos)
    have h_ms_neq : matchSearch (vanEck (m - 1)) (m - 1) ≠ 0 := by
      rw [← h_a_def]
      exact h0
      
    have hm_sub_p_gt : m - 1 - p > N := by
      calc m - 1 - p > N + p + 1 - 1 - p := Nat.sub_lt_sub_right (by decide) (Nat.sub_lt_sub_right hp hm)
           _ = N := rfl
    have h_per_val : vanEckNthTerm (m - 1 - p) = vanEckNthTerm (m - 1 - p + p) := h_per (m - 1 - p) hm_sub_p_gt
    have h_p_cancel : m - 1 - p + p = m - 1 := by
      have h1 : p ≤ m - 1 := Nat.le_trans (Nat.le_add_left p N) (Nat.le_of_lt (Nat.sub_lt_sub_right (by decide) hm))
      exact Nat.sub_add_cancel h1
    rw [h_p_cancel] at h_per_val
    have h_match_val : vanEckNthTerm (m - 1) = vanEckNthTerm (m - 1 - p) := h_per_val.symm
    
    have h_L_len : (vanEck (m - 1)).length = m := by
      have h1 := vanEckLength (m - 1)
      have h2 : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.le_trans (by decide) hm_pos)
      rw [h2] at h1
      exact h1
    have h_L_len1 : (vanEck (m - 1)).length - 1 = m - 1 := by rw [h_L_len]
    
    have hd_last : listNth (vanEck (m - 1)) (m - 1) = vanEckNthTerm (m - 1) := by
      exact VanEck_deterministic (m - 1) (m - 1) (Nat.le_refl _)
    have hd_prev : listNth (vanEck (m - 1)) (m - 1 - p) = vanEckNthTerm (m - 1 - p) := by
      have hle : m - 1 - p ≤ m - 1 := Nat.sub_le _ _
      exact VanEck_deterministic (m - 1) (m - 1 - p) hle
      
    have h_match : listNth (vanEck (m - 1)) ((vanEck (m - 1)).length - 1) = listNth (vanEck (m - 1)) (m - 1 - p) := by
      rw [h_L_len1, hd_last, hd_prev]
      exact h_match_val
      
    have hk_lt_n : m - 1 - p < m - 1 := Nat.sub_lt_self hp (Nat.lt_of_succ_lt hm_pos)
    
    have h_bound := matchSearch_first (vanEck (m - 1)) (m - 1) (m - 1 - p) h_ms_neq hk_lt_n h_match
    rw [h_L_len1] at h_bound
    have h_sub_sub : m - 1 - (m - 1 - p) = p := by
      have h1 : p ≤ m - 1 := Nat.le_trans (Nat.le_add_left p N) (Nat.le_of_lt (Nat.sub_lt_sub_right (by decide) hm))
      exact Nat.sub_sub_self h1
    rw [h_sub_sub] at h_bound
    
    rw [h_a_def]
    exact h_bound
}

/--
Level 2 Alternative Conjecture: The sequence is not eventually periodic, proved directly via the 
infinite zeroes property. If a sequence is periodic, its maximum gap is bounded. 
By Pigeonholing the number of elements against this maximum gap, we can force a contradiction.
-/
theorem vanEck_not_periodic2 (p : ℕ) (hp : p > 0) : ∀ N, ∃ m > N, vanEckNthTerm m ≠ vanEckNthTerm (m + p) := by {
  intro N
  by_contra hc
  have h_per : ∀ m > N, vanEckNthTerm m = vanEckNthTerm (m + p) := by
    intro m hm
    exact Classical.not_not.mp (by intro hneq; exact hc ⟨m, hm, hneq⟩)
    
  have h_zeros := infinite_zeros_vanEck (N + p + 2)
  rcases h_zeros with ⟨Z, hZ_gt, hZ_zero⟩
  
  -- Z > N + p + 2.
  have hZ_p_gt : Z + p > N := by
    calc Z + p > N + p + 2 + p := Nat.add_lt_add_right hZ_gt p
         _ ≥ N := Nat.le_add_right _ _
         
  have h_Z_eq : vanEckNthTerm Z = vanEckNthTerm (Z + p) := h_per Z (Nat.lt_trans (by decide) hZ_gt)
  
  have hZ_p_zero : vanEckNthTerm (Z + p) = 0 := by
    rw [← h_Z_eq]
    exact hZ_zero
    
  have hZ_prev_gt : Z - 1 > N := by
    calc Z - 1 > N + p + 2 - 1 := Nat.sub_lt_sub_right (by decide) hZ_gt
         _ = N + p + 1 := rfl
         _ ≥ N := Nat.le_add_right _ _
         
  have h_prev_eq : vanEckNthTerm (Z - 1) = vanEckNthTerm (Z - 1 + p) := h_per (Z - 1) hZ_prev_gt
  
  have h_add_comm : Z - 1 + p = Z + p - 1 := by
    have h1 : Z ≥ 1 := Nat.le_trans (by decide) hZ_gt
    exact Nat.add_sub_assoc h1 p
  rw [h_add_comm] at h_prev_eq
  
  -- Now we evaluate a(Z+p)
  have hZp_pos : Z + p ≥ 2 := by
    calc Z + p > N + p + 2 + p := Nat.add_lt_add_right hZ_gt p
         _ ≥ 2 := Nat.le_add_left 2 _
         
  have haZp := vanEck_term_is_matchSearch (Z + p) (Nat.lt_of_succ_lt hZp_pos)
  rw [hZ_p_zero] at haZp
  have h_ms_zero : matchSearch (vanEck (Z + p - 1)) (Z + p - 1) = 0 := haZp.symm
  
  let L := vanEck (Z + p - 1)
  have h_len : L.length = Z + p := by
    have hl1 := vanEckLength (Z + p - 1)
    have hl2 : Z + p - 1 + 1 = Z + p := Nat.sub_add_cancel (Nat.le_trans (by decide) hZp_pos)
    rw [hl2] at hl1
    exact hl1
    
  have hlen2 : L.length ≥ 2 := by rw [h_len]; exact hZp_pos
  
  let n := p - 1
  have hn_lt : n < L.length - 1 := by
    rw [h_len]
    -- p - 1 < Z + p - 1
    have h1 : p - 1 + 1 = p := Nat.sub_add_cancel hp
    have h2 : Z + p - 1 + 1 = Z + p := Nat.sub_add_cancel (Nat.le_trans (by decide) hZp_pos)
    have h3 : p < Z + p := Nat.lt_add_of_pos_left (Nat.lt_of_lt_of_le (by decide) hZ_gt)
    exact Nat.sub_lt_sub_right (by decide) h3
    
  have hd_last : listNth L (L.length - 1) = vanEckNthTerm (Z + p - 1) := by
    have hl1 : L.length - 1 = Z + p - 1 := by rw [h_len]
    rw [hl1]
    exact VanEck_deterministic (Z + p - 1) (Z + p - 1) (Nat.le_refl _)
    
  have h_idx : L.length - 2 - n = Z - 1 := by
    rw [h_len]
    -- Z + p - 2 - (p - 1) = Z - 1
    have h1 : Z + p - 2 = Z - 1 + (p - 1) := by
      have hz : Z ≥ 1 := Nat.le_trans (by decide) hZ_gt
      calc Z + p - 2 = Z + p - 1 - 1 := rfl
           _ = Z - 1 + p - 1 := by rw [Nat.add_sub_assoc hz]
           _ = Z - 1 + (p - 1) := by rw [Nat.add_assoc]
    rw [h1]
    exact Nat.add_sub_cancel (Z - 1) (p - 1)
    
  have hd_prev : listNth L (L.length - 2 - n) = vanEckNthTerm (Z - 1) := by
    rw [h_idx]
    have hle : Z - 1 ≤ Z + p - 1 := Nat.sub_le_sub_right (Nat.le_add_right Z p) 1
    exact VanEck_deterministic (Z + p - 1) (Z - 1) hle
    
  have h_match : listNth L (L.length - 2 - n) = listNth L (L.length - 1) := by
    rw [hd_last, hd_prev]
    exact h_prev_eq
    
  have h_ge1 := if_match_then_match_search_at_end_ge_1 n L hlen2 hn_lt h_match
  
  have h_L_len1 : L.length - 1 = Z + p - 1 := by rw [h_len]
  rw [h_L_len1] at h_ge1
  
  rw [h_ms_zero] at h_ge1
  exact Nat.not_lt_zero 0 h_ge1
}

/--
If an element `x` never appears after index `Z`, then no element after `Z+1` can have its previous occurrence exactly `x` steps ago.
-/
lemma never_appears_again_implies_no_gap_x (x Z : ℕ) (hx : ∀ k > Z, vanEckNthTerm k ≠ x) :
    ∀ k > Z + 1, listNth (vanEck (k - 1)) (k - 1) ≠ listNth (vanEck (k - 1)) (k - 1 - x) := by {
  sorry
}

/--
If two consecutive gaps between zeros are identical, the sequence deterministically produces a 1.
This provides the mathematical bridge linking zero gap patterns to occurrences of 1.
-/
lemma vanEck_consecutive_gaps_imply_one (Z1 Z2 d : ℕ) 
  (hZ1 : vanEckNthTerm Z1 = 0)
  (hZ2 : vanEckNthTerm Z2 = 0)
  (hd : d = Z2 - Z1)
  (hd_pos : d > 0)
  (hZ1_lt : Z1 < Z2)
  (haZ1 : vanEckNthTerm (Z1 + 1) = d)
  (haZ2 : vanEckNthTerm (Z2 + 1) = d)
  (h_no_d : ∀ k, Z1 + 1 < k → k < Z2 + 1 → vanEckNthTerm k ≠ d) :
  vanEckNthTerm (Z2 + 3) = 1 := by {
  have hZ2_pos : Z2 ≥ 1 := Nat.le_trans (by decide) hZ1_lt
  
  let L := vanEck (Z2 + 1)
  have h_len : L.length = Z2 + 2 := by
    have hl := vanEckLength (Z2 + 1)
    have hz : Z2 + 1 + 1 = Z2 + 2 := rfl
    rw [hz] at hl
    exact hl
    
  have ha2 : vanEckNthTerm (Z2 + 2) = matchSearch L (Z2 + 1) := by
    have h1 : Z2 + 2 = Z2 + 1 + 1 := rfl
    rw [h1]
    exact vanEck_term_is_matchSearch (Z2 + 2) (Nat.le_add_left 2 Z2)
    
  have hd_last : listNth L (L.length - 1) = d := by
    have hl : L.length - 1 = Z2 + 1 := by rw [h_len]; rfl
    rw [hl]
    have h_det := VanEck_deterministic (Z2 + 1) (Z2 + 1) (Nat.le_refl _)
    rw [h_det]
    exact haZ2
    
  have hd_start : listNth L (Z1 + 1) = d := by
    have h_le : Z1 + 1 ≤ Z2 + 1 := Nat.add_le_add_right (Nat.le_of_lt hZ1_lt) 1
    have h_det := VanEck_deterministic (Z2 + 1) (Z1 + 1) h_le
    rw [h_det]
    exact haZ1
    
  have h_match : listNth L (L.length - 1) = listNth L (Z1 + 1) := by
    rw [hd_last, hd_start]
    
  have h_fail : ∀ k, 1 ≤ k → k ≤ d - 1 → listNth L (L.length - 1) ≠ listNth L (Z1 + 1 + k) := by
    intro k hk1 hkd
    rw [hd_last]
    have h_idx_le : Z1 + 1 + k ≤ Z2 + 1 := by
      calc Z1 + 1 + k ≤ Z1 + 1 + (d - 1) := Nat.add_le_add_left hkd _
           _ = Z1 + 1 + d - 1 := rfl
           _ = Z1 + d + 1 - 1 := by rw [Nat.add_right_comm Z1 1 d]
           _ = Z2 + 1 - 1 := by rw [← hd, Nat.add_sub_cancel' (Nat.le_of_lt hZ1_lt)]
           _ = Z2 := rfl
           _ ≤ Z2 + 1 := Nat.le_add_right _ _
           
    have h_det := VanEck_deterministic (Z2 + 1) (Z1 + 1 + k) h_idx_le
    rw [h_det]
    intro heq
    have h_symm : vanEckNthTerm (Z1 + 1 + k) = d := heq.symm
    
    have h_gt : Z1 + 1 < Z1 + 1 + k := Nat.lt_add_of_pos_right hk1
    have h_lt : Z1 + 1 + k < Z2 + 1 := by
      calc Z1 + 1 + k ≤ Z1 + 1 + (d - 1) := Nat.add_le_add_left hkd _
           _ = Z1 + 1 + d - 1 := rfl
           _ = Z1 + d + 1 - 1 := by rw [Nat.add_right_comm Z1 1 d]
           _ = Z2 + 1 - 1 := by rw [← hd, Nat.add_sub_cancel' (Nat.le_of_lt hZ1_lt)]
           _ = Z2 := rfl
           _ < Z2 + 1 := Nat.lt_succ_self Z2
           
    exact h_no_d (Z1 + 1 + k) h_gt h_lt h_symm
    
  have h_ms := matchSearch_eq_dist L (Z1 + 1) (d - 1) h_match h_fail
  
  have h_arg : Z1 + 1 + (d - 1) + 1 = Z2 + 1 := by
    calc Z1 + 1 + (d - 1) + 1 = Z1 + 1 + d - 1 + 1 := rfl
         _ = Z1 + d + 1 - 1 + 1 := by rw [Nat.add_right_comm Z1 1 d]
         _ = Z2 + 1 - 1 + 1 := by rw [← hd, Nat.add_sub_cancel' (Nat.le_of_lt hZ1_lt)]
         _ = Z2 + 1 := Nat.sub_add_cancel (by decide)
         
  rw [h_arg] at h_ms
  
  have h_val : L.length - 1 - (Z1 + 1) = d := by
    rw [h_len]
    have h1 : Z2 + 2 - 1 = Z2 + 1 := rfl
    rw [h1]
    have h2 : Z2 + 1 - (Z1 + 1) = Z2 - Z1 := by
      rw [Nat.add_sub_add_right]
    rw [h2]
    exact hd
    
  rw [h_val] at h_ms
  
  have h_a_eq : vanEckNthTerm (Z2 + 2) = d := by
    rw [ha2, h_ms]
    
  have h_cons : vanEckNthTerm (Z2 + 1) = vanEckNthTerm (Z2 + 2) := by
    rw [haZ2, h_a_eq]
    
  have h_final := vanEck_consecutive_eq_implies_next_one (Z2 + 1) h_cons
  have h_idx_eq : Z2 + 1 + 1 = Z2 + 2 := rfl
  have h_idx_eq2 : Z2 + 1 + 2 = Z2 + 3 := rfl
  rw [h_idx_eq, h_idx_eq2] at h_final
  exact h_final
}

/--
The gaps between consecutive zeros in the Van Eck sequence must be unbounded.
If the gaps were bounded, some gap size `d` would appear infinitely often. 
The distance between occurrences of `d` would form the elements immediately preceding the zeros.
Since the gaps are bounded, these distances would be bounded, and therefore repeat.
However, the element immediately preceding a zero MUST be a new, never-before-seen number.
This contradiction proves the zero-gaps are unbounded.
-/
lemma vanEck_zero_gaps_unbounded (B : ℕ) :
    ∃ Z1 Z2, vanEckNthTerm Z1 = 0 ∧ vanEckNthTerm Z2 = 0 ∧ Z1 < Z2 ∧ 
    (∀ k, Z1 < k → k < Z2 → vanEckNthTerm k ≠ 0) ∧ Z2 - Z1 > B := by {
  sorry
}

/--
A "strict" gap of exactly n exists if two identical terms are separated by exactly n indices,
and the value does not appear anywhere inside the gap.
-/
def has_strict_gap (n : ℕ) : Prop :=
  ∃ m, vanEckNthTerm m = vanEckNthTerm (m + n) ∧ 
       ∀ k, m < k → k < m + n → vanEckNthTerm k ≠ vanEckNthTerm m

/--
If a strict gap of exactly n exists, then the term immediately following the second occurrence will be precisely n.
This mathematically bridges the gap structure directly to the sequence's output values.
-/
lemma strict_gap_implies_value (n : ℕ) (hn : n > 0) (h : has_strict_gap n) : 
  ∃ k, vanEckNthTerm k = n := by {
  rcases h with ⟨m, h_eq, h_strict⟩
  use m + n + 1
  have h_pos : m + n + 1 ≥ 2 := by
    have h1 : m + n ≥ 1 := Nat.le_add_left 1 (m + n)
    have h2 : m + n + 1 ≥ 1 + 1 := Nat.add_le_add h1 (Nat.le_refl 1)
    exact h2
         
  have ha := vanEck_term_is_matchSearch (m + n + 1) (Nat.lt_of_succ_lt h_pos)
  have h_len : (vanEck (m + n)).length = m + n + 1 := by
    have hl := vanEckLength (m + n)
    have hz : m + n + 1 = m + n + 1 := rfl
    exact hl
    
  let L := vanEck (m + n)
  have h_match : listNth L (L.length - 1) = listNth L m := by
    have h1 : L.length - 1 = m + n := by rw [h_len]; rfl
    rw [h1]
    have hd1 := VanEck_deterministic (m + n) (m + n) (Nat.le_refl _)
    have hd2 := VanEck_deterministic (m + n) m (Nat.le_add_right m n)
    rw [hd1, hd2]
    exact h_eq.symm
    
  have h_fail : ∀ k, 1 ≤ k → k ≤ n - 1 → listNth L (L.length - 1) ≠ listNth L (m + k) := by
    intro k hk1 hkn
    have h1 : L.length - 1 = m + n := by rw [h_len]; rfl
    rw [h1]
    have h_idx_le : m + k ≤ m + n := by
      have h2 : m + k ≤ m + (n - 1) := Nat.add_le_add_left hkn m
      have h3 : m + (n - 1) = m + n - 1 := by
        have h_ge : n ≥ 1 := hn
        exact (Nat.add_sub_assoc h_ge m).symm
      rw [h3] at h2
      have h4 : m + n - 1 ≤ m + n := Nat.sub_le _ _
      exact Nat.le_trans h2 h4
           
    have hd1 := VanEck_deterministic (m + n) (m + n) (Nat.le_refl _)
    have hd2 := VanEck_deterministic (m + n) (m + k) h_idx_le
    rw [hd1, hd2]
    intro heq
    have heq_symm : vanEckNthTerm (m + k) = vanEckNthTerm (m + n) := heq.symm
    have h_eq_val : vanEckNthTerm (m + k) = vanEckNthTerm m := by
      rw [heq_symm]
      exact h_eq.symm
      
    have h_gt : m < m + k := Nat.lt_add_of_pos_right hk1
    have h_lt : m + k < m + n := by
      have h2 : m + k ≤ m + (n - 1) := Nat.add_le_add_left hkn m
      have h3 : m + (n - 1) = m + n - 1 := by
        have h_ge : n ≥ 1 := hn
        exact (Nat.add_sub_assoc h_ge m).symm
      rw [h3] at h2
      have h4 : m + n - 1 < m + n := Nat.sub_lt (Nat.add_pos_right m hn) (by decide)
      exact Nat.lt_of_le_of_lt h2 h4
    exact h_strict (m + k) h_gt h_lt h_eq_val
    
  have h_ms := matchSearch_eq_dist L m (n - 1) h_match h_fail
  
  have h_arg : m + (n - 1) + 1 = m + n := by
    have h1 : m + (n - 1) + 1 = m + (n - 1 + 1) := by rw [← Nat.add_assoc]
    have h2 : n - 1 + 1 = n := Nat.sub_add_cancel hn
    rw [h1, h2]
         
  rw [h_arg] at h_ms
  
  have h_val : L.length - 1 - m = n := by
    rw [h_len]
    have h1 : m + n + 1 - 1 = m + n := rfl
    rw [h1]
    exact Nat.add_sub_cancel_left m n
    
  rw [h_val] at h_ms
  have h_ha : vanEckNthTerm (m + n + 1) = matchSearch L (m + n) := by
    have h_idx : m + n + 1 - 1 = m + n := rfl
    rw [h_idx] at ha
    exact ha
  rw [h_ha]
  exact h_ms
}

/--
If 1 only appears finitely many times, there is a point after which no two consecutive elements are equal.
-/
lemma finite_ones_implies_no_consecutive_equal (h_finite : ∃ Z, ∀ k > Z, vanEckNthTerm k ≠ 1) :
    ∃ Z, ∀ k > Z, vanEckNthTerm k ≠ vanEckNthTerm (k + 1) := by {
  rcases h_finite with ⟨Z, hZ⟩
  use Z
  intro k hk
  intro heq
  have h_next := vanEck_consecutive_eq_implies_next_one k heq
  have hk_add : k + 2 > Z := Nat.lt_trans hk (Nat.lt_add_of_pos_right (by decide))
  have h_not_one := hZ (k + 2) hk_add
  exact h_not_one h_next
}

/--
Level 3 Conjecture (Hard): Every value that appears in the sequence appears infinitely many times.
We know 0 appears infinitely often, but it is an open question whether an arbitrary 
value like 1 or 2 appears infinitely often.
-/
theorem vanEck_all_seen_appear_infinitely (n : ℕ) : (∃ m, vanEckNthTerm m = n) → ∀ N, ∃ k > N, vanEckNthTerm k = n := by {
  sorry
}

/--
Level 4 Conjecture (Very Hard): For any natural number n, there exist two identical terms separated by exactly n indices.
This is a necessary precursor to surjectivity, stating that every possible gap length exists.
-/
theorem vanEck_any_gap_exists (n : ℕ) : ∃ m : ℕ, vanEckNthTerm m = vanEckNthTerm (m + n) := by {
  sorry
}

/--
Level 5 Conjecture (Equivalent to Surjectivity): For any positive n, there exists a "strict" gap of exactly n indices between identical values, meaning the value does not appear anywhere inside the gap. 
If this holds, the term immediately following the second occurrence will be precisely `n`. This is mathematically equivalent to the conjecture that the sequence takes on every natural number.
-/
/--
Theorem: For all n, there exists m such that vanEckNthTerm m = n.
This is the open problem: Does every number appear in the Van Eck sequence?
-/
theorem vanEck_surjective (n : ℕ) : ∃ m : ℕ, vanEckNthTerm m = n := by {
  sorry
}

-- ============================================================================
-- MISSING NUMBER DENSITY CONSTRAINTS
-- ============================================================================

lemma missing_number_implies_no_gap (s : ℕ) (h_pos : s > 0)
  (h_missing : ∀ k, vanEckNthTerm k ≠ s) :
  ∀ m, vanEckNthTerm m ≠ vanEckNthTerm (m + s) ∨ 
  ∃ k, m < k ∧ k < m + s ∧ vanEckNthTerm k = vanEckNthTerm m := by {
  intro m
  by_contra hc
  push_neg at hc
  have h_eq : vanEckNthTerm m = vanEckNthTerm (m + s) := hc.1
  have h_strict : ∀ k, m < k → k < m + s → vanEckNthTerm k ≠ vanEckNthTerm m := hc.2
  
  have h_gap : has_strict_gap s := by
    use m
    exact ⟨h_eq, h_strict⟩
    
  have h_val := strict_gap_implies_value s h_pos h_gap
  rcases h_val with ⟨k, hk⟩
  exact h_missing k hk
}

lemma exists_strict_gap_of_eq (m s : ℕ) (h_pos : s > 0) (h_eq : vanEckNthTerm m = vanEckNthTerm (m + s)) : 
  ∃ d, 0 < d ∧ d ≤ s ∧ vanEckNthTerm m = vanEckNthTerm (m + d) ∧ 
  ∀ k, m < k → k < m + d → vanEckNthTerm k ≠ vanEckNthTerm m := by {
  -- This requires finding the MINIMUM index > m that equals a(m).
  -- Since m+s is such an index, the set is non-empty and bounded below, so a minimum exists.
  sorry
}

/--
Missing Number Density Constraint:
If the numbers 1 through n never appear in the sequence,
then any contiguous block of n + 1 elements consists entirely of distinct values.
-/
lemma missing_numbers_imply_distinct_window (n : ℕ) 
  (h_missing : ∀ k, ∀ s, 1 ≤ s → s ≤ n → vanEckNthTerm k ≠ s) :
  ∀ m : ℕ, ∀ i j, i ≤ n → j ≤ n → i < j → vanEckNthTerm (m + i) ≠ vanEckNthTerm (m + j) := by {
  intro m i j hi hj h_lt h_eq
  have h_s : j - i > 0 := Nat.sub_pos_of_lt h_lt
  have h_s_le : j - i ≤ n := by
    calc j - i ≤ j := Nat.sub_le j i
         _ ≤ n := hj
         
  have h_idx : m + j = m + i + (j - i) := by
    rw [Nat.add_assoc]
    have h_sub : i + (j - i) = j := Nat.add_sub_cancel' (Nat.le_of_lt h_lt)
    rw [h_sub]
    
  have h_eq2 : vanEckNthTerm (m + i) = vanEckNthTerm (m + i + (j - i)) := by
    rw [← h_idx]
    exact h_eq
    
  have h_strict_ex := exists_strict_gap_of_eq (m + i) (j - i) h_s h_eq2
  rcases h_strict_ex with ⟨d, hd_pos, hd_le, hd_eq, hd_strict⟩
  
  have h_d_le_n : d ≤ n := Nat.le_trans hd_le h_s_le
  
  have h_no_gap := missing_number_implies_no_gap d hd_pos (h_missing · d hd_pos h_d_le_n) (m + i)
  cases h_no_gap with
  | inl h_not => exact h_not hd_eq
  | inr h_ex =>
    rcases h_ex with ⟨k, h_k_gt, h_k_lt, h_k_eq⟩
    exact hd_strict k h_k_gt h_k_lt h_k_eq
}

lemma pigeonhole_n_plus_one (n : ℕ) (f : Fin (n + 1) → Fin n) : ∃ i j, i ≠ j ∧ f i = f j := by {
  have h_card : Fintype.card (Fin n) < Fintype.card (Fin (n + 1)) := by
    simp
  exact Fintype.exists_ne_map_eq_of_card_lt f h_card
}

lemma bounded_distinct_elements (n : ℕ) (hn : n > 0)
  (a : Fin (n + 1) → ℕ)
  (h_dist : ∀ i j, i ≠ j → a i ≠ a j)
  (h_excl : ∀ i, a i = 0 ∨ a i > n) :
  ∃ i, a i ≥ 2 * n := by {
  by_contra hc
  push Not at hc
  
  let g : Fin (n + 1) → Fin n := fun i => 
    let x := a i
    if hx : x = 0 then
      ⟨0, hn⟩
    else
      have h_gt : x > n := by
        cases (h_excl i) with
        | inl h0 => exact False.elim (hx h0)
        | inr hgt => exact hgt
      have h_lt : x < 2 * n := hc i
      have h_lt2 : x < n + n := by
        have h_two : 2 * n = n + n := Nat.two_mul n
        rw [h_two] at h_lt
        exact h_lt
      have h_sub : x - n < n := by
        exact Nat.sub_lt_left_of_lt_add (Nat.le_of_lt h_gt) h_lt2
      ⟨x - n, h_sub⟩
      
  have h_pig := pigeonhole_n_plus_one n g
  rcases h_pig with ⟨i, j, h_neq, h_geq⟩
  
  have h_eq : a i = a j := by
    dsimp [g] at h_geq
    split at h_geq
    · rename_i hx_i
      split at h_geq
      · rename_i hx_j
        rw [hx_i, hx_j]
      · rename_i hx_j
        have h_val : 0 = a j - n := Fin.ext_iff.mp h_geq
        have h_gt_j : a j > n := by
          cases (h_excl j) with
          | inl h0 => exact False.elim (hx_j h0)
          | inr hgt => exact hgt
        have h_sub_pos : a j - n > 0 := Nat.sub_pos_of_lt h_gt_j
        rw [← h_val] at h_sub_pos
        exact False.elim (Nat.lt_irrefl 0 h_sub_pos)
    · rename_i hx_i
      split at h_geq
      · rename_i hx_j
        have h_val : a i - n = 0 := Fin.ext_iff.mp h_geq
        have h_gt_i : a i > n := by
          cases (h_excl i) with
          | inl h0 => exact False.elim (hx_i h0)
          | inr hgt => exact hgt
        have h_sub_pos : a i - n > 0 := Nat.sub_pos_of_lt h_gt_i
        rw [h_val] at h_sub_pos
        exact False.elim (Nat.lt_irrefl 0 h_sub_pos)
      · rename_i hx_j
        have h_val : a i - n = a j - n := Fin.ext_iff.mp h_geq
        have h_gt_i : a i > n := by
          cases (h_excl i) with
          | inl h0 => exact False.elim (hx_i h0)
          | inr hgt => exact hgt
        have h_gt_j : a j > n := by
          cases (h_excl j) with
          | inl h0 => exact False.elim (hx_j h0)
          | inr hgt => exact hgt
        have h_add : a i - n + n = a j - n + n := by rw [h_val]
        rw [Nat.sub_add_cancel (Nat.le_of_lt h_gt_i)] at h_add
        rw [Nat.sub_add_cancel (Nat.le_of_lt h_gt_j)] at h_add
        exact h_add
        
  exact h_dist i j h_neq h_eq
}

/--
Bounding the Gap Growth based on Missing Numbers:
If the numbers 1 through n never appear, then in any window of n + 1 elements,
all elements are distinct and cannot be 1..n. 
This forces the maximum value in any window of length n + 1 to be at least 2n.
This establishes a strict linear lower bound on the local values based on missing elements.
-/
lemma missing_numbers_force_local_growth (n : ℕ) (hn : n > 0)
  (h_missing : ∀ k, ∀ s, 1 ≤ s → s ≤ n → vanEckNthTerm k ≠ s) :
  ∀ m : ℕ, ∃ k, m ≤ k ∧ k ≤ m + n ∧ vanEckNthTerm k ≥ 2 * n := by {
  intro m
  let a : Fin (n + 1) → ℕ := fun i => vanEckNthTerm (m + i.val)
  
  have h_dist : ∀ i j : Fin (n + 1), i ≠ j → a i ≠ a j := by
    intro i j h_neq
    have hi_le : i.val ≤ n := Nat.le_of_lt_succ i.isLt
    have hj_le : j.val ≤ n := Nat.le_of_lt_succ j.isLt
    have h_tri := Nat.lt_trichotomy i.val j.val
    cases h_tri with
    | inl h_lt =>
      exact missing_numbers_imply_distinct_window n h_missing m i.val j.val hi_le hj_le h_lt
    | inr h_eq_or_gt =>
      cases h_eq_or_gt with
      | inl h_eq =>
        have h_eq_fin : i = j := Fin.eq_of_val_eq h_eq
        exact False.elim (h_neq h_eq_fin)
      | inr h_gt =>
        have h_ne := missing_numbers_imply_distinct_window n h_missing m j.val i.val hj_le hi_le h_gt
        exact h_ne.symm
    
  have h_excl : ∀ i : Fin (n + 1), a i = 0 ∨ a i > n := by
    intro i
    have h_val := a i
    cases h_val with
    | zero => exact Or.inl rfl
    | succ v =>
      have h_pos : a i > 0 := Nat.succ_pos v
      by_cases h_le : a i ≤ n
      · have h_not := h_missing (m + i.val) (a i) h_pos h_le
        exact False.elim (h_not rfl)
      · exact Or.inr (Nat.lt_of_not_le h_le)
      
  have h_bound := bounded_distinct_elements n hn a h_dist h_excl
  rcases h_bound with ⟨i, hi⟩
  use m + i.val
  exact ⟨Nat.le_add_right m i.val, Nat.add_le_add_left i.isLt m, hi⟩
}

lemma missing_numbers_dense_large_gaps (n : ℕ) (hn : n > 0)
  (h_missing : ∀ k, ∀ s, 1 ≤ s → s ≤ n → vanEckNthTerm k ≠ s) :
  ∀ m : ℕ, ∃ k, m ≤ k ∧ k ≤ m + n ∧ 
  ∃ d, d ≥ 2 * n ∧ vanEckNthTerm k = d ∧
  k ≥ d + 1 ∧ vanEckNthTerm (k - 1) = vanEckNthTerm (k - 1 - d) := by {
  intro m
  have h_local := missing_numbers_force_local_growth n hn h_missing m
  rcases h_local with ⟨k, hk_ge, hk_le, hk_val⟩
  
  -- Since k >= m >= 0, we need to be careful if k = 0.
  -- But if k = 0, a(0) = 0. But a(k) >= 2n >= 2 > 0.
  -- So k > 0.
  have hk_pos : k > 0 := by
    by_contra h0
    push Not at h0
    have hz : k = 0 := Nat.eq_zero_of_le_zero h0
    rw [hz] at hk_val
    have ha0 : vanEckNthTerm 0 = 0 := rfl
    rw [ha0] at hk_val
    have hn_pos : 2 * n > 0 := Nat.mul_pos (by decide) hn
    exact False.elim (Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hn_pos hk_val))
    
  let d := vanEckNthTerm k
  use k
  refine ⟨hk_ge, hk_le, d, hk_val, rfl, ?_⟩
  
  have hd_pos : d > 0 := by
    have hn_pos : 2 * n > 0 := Nat.mul_pos (by decide) hn
    exact Nat.lt_of_lt_of_le hn_pos hk_val
    
  have hd_pos_ne : d ≠ 0 := Nat.pos_iff_ne_zero.mp hd_pos
  
  have h_gap := matchSearch_is_gap_distance k hk_pos d hk_val hd_pos_ne
  
  have h_k_ge : k ≥ d + 1 := by
    have h_len : matchSearch (vanEck (k - 1)) (k - 1) ≤ k := by
      have h1 := matchSearch_le (k - 1)
      have h2 : k - 1 + 1 = k := Nat.sub_add_cancel hk_pos
      rw [h2] at h1
      exact h1
    have h_val_ms := vanEck_term_is_matchSearch k hk_pos
    rw [hk_val.symm] at h_val_ms
    rw [h_val_ms] at hk_val
    have h_d_le_k : d ≤ k := by rw [hk_val.symm]; exact h_len
    have h1 : d ≤ k - 1 := by sorry
    exact Nat.add_le_of_le_sub hk_pos h1
    
  exact ⟨h_k_ge, h_gap⟩
}

lemma vanEck_le_index (k : ℕ) (hk : k > 0) : vanEckNthTerm k ≤ k := by {
  have ha := vanEck_term_is_matchSearch k hk
  have h_le := matchSearch_le (k - 1)
  have hk_sub : k - 1 + 1 = k := Nat.sub_add_cancel hk
  rw [ha]
  rw [hk_sub] at h_le
  exact h_le
}

/--
The Monkey Bars Collapse (Rung 5 directly):
If the numbers 1 through n never appear, the very first window of length n + 1
must contain an element >= 2n. But the Van Eck sequence can never generate a 
value greater than its own index! Thus, the local growth bound violently 
collides with the absolute bounding envelope of the sequence on the very first window.
-/
lemma missing_numbers_pigeonhole_contradiction (n : ℕ) (hn : n > 0)
  (h_missing : ∀ k, ∀ s, 1 ≤ s → s ≤ n → vanEckNthTerm k ≠ s) : False := by {
  -- Get the local growth bound for the very first window (m = 0)
  have h_growth := missing_numbers_force_local_growth n hn h_missing 0
  rcases h_growth with ⟨k, hk_ge, hk_le, hk_val⟩
  
  -- Since k <= n, and vanEckNthTerm k <= k, we have vanEckNthTerm k <= n.
  -- We must be careful if k = 0.
  by_cases hk0 : k = 0
  · rw [hk0] at hk_val
    have ha0 : vanEckNthTerm 0 = 0 := rfl
    rw [ha0] at hk_val
    have hn_pos : 2 * n > 0 := Nat.mul_pos (by decide) hn
    exact False.elim (Nat.lt_irrefl 0 (Nat.lt_of_lt_of_le hn_pos hk_val))
  · have hk_pos : k > 0 := Nat.pos_of_ne_zero hk0
    have h_bound := vanEck_le_index k hk_pos
    have h_le_n : vanEckNthTerm k ≤ n := by
      have hk_le_n : k ≤ n := by
        have h_zero_add : 0 + n = n := Nat.zero_add n
        rw [← h_zero_add]
        exact hk_le
      exact Nat.le_trans h_bound hk_le_n
      
    -- Now we have 2n <= a(k) <= n.
    have h_contra : 2 * n ≤ n := Nat.le_trans hk_val h_le_n
    have h_2n : 2 * n = n + n := Nat.two_mul n
    rw [h_2n] at h_contra
    have h_zero : n ≤ 0 := Nat.le_of_add_le_add_right h_contra
    exact False.elim (Nat.not_lt_of_le h_zero hn)
}
