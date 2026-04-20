import VanEck

variable {n M P : ℕ}

lemma gap_determines_value (k : ℕ) (hk : k ≥ n) (x : ℕ) (hn_pos : n ≥ 1)
    (hx : vanEckNthTerm (k + 1) = x) (hx_pos : x ≠ 0) :
    vanEckNthTerm k = vanEckNthTerm (k - x) := by
  have hk1 : k + 1 ≥ 1 := Nat.le_trans hn_pos (Nat.le_trans hk (Nat.le_succ k))
  have ht := matchSearch_is_gap_distance (k + 1) hk1 x hx hx_pos
  have hk_sub : k + 1 - 1 = k := Nat.add_sub_cancel k 1
  rw [hk_sub] at ht
  have h_left : listNth (vanEck k) k = vanEckNthTerm k := rfl
  have h_lt : k - x ≤ k := Nat.sub_le k x
  have h_right : listNth (vanEck k) (k - x) = vanEckNthTerm (k - x) := VanEck_deterministic k (k - x) h_lt
  rw [← h_left, ← h_right]
  exact ht

-- Window Property: Maximum Distance Equivalence
lemma max_gap_le_M (h_bound : ∀ k ≥ n, vanEckNthTerm k ≤ M) (k : ℕ) (hk : k ≥ n) : 
    vanEckNthTerm (k + 1) ≤ M := h_bound (k + 1) (Nat.le_trans hk (Nat.le_add_right k 1))

-- Bouncing element density constraints
-- If `X` exists, it MUST appear exactly within any sliding window of length `M`!
lemma element_in_window (h_bound : ∀ k ≥ n, vanEckNthTerm k ≤ M)
    (h_no_zeros : ∀ k ≥ n, vanEckNthTerm k ≠ 0)
    (X : ℕ) (k : ℕ) (hk : k ≥ n) (hn_pos : n ≥ 1) (hX : ∃ j ≥ k, vanEckNthTerm j = X) :
    ∃ j, k ≤ j ∧ j < k + M ∧ vanEckNthTerm j = X := by
  let p := λ j => j ≥ k ∧ vanEckNthTerm j = X
  have hX_p : ∃ j, p j := hX
  let j_min := Nat.find hX_p
  have h_jmin_prop : p j_min := Nat.find_spec hX_p
  have h_min : ∀ m < j_min, ¬ p m := λ m hm => Nat.find_min hX_p hm
  have h_ge_k : j_min ≥ k := h_jmin_prop.1
  have h_eq_X : vanEckNthTerm j_min = X := h_jmin_prop.2
  by_cases h_jmin_lt : j_min < k + M
  · exact ⟨j_min, h_ge_k, h_jmin_lt, h_eq_X⟩
  · exfalso
    have h_jmin_ge : j_min ≥ k + M := Nat.le_of_not_lt h_jmin_lt
    have hjn : j_min ≥ n := Nat.le_trans hk h_ge_k
    let d := vanEckNthTerm (j_min + 1)
    have hd_pos : d ≠ 0 := h_no_zeros (j_min + 1) (Nat.le_trans hjn (Nat.le_add_right j_min 1))
    have hd_bound : d ≤ M := max_gap_le_M h_bound j_min hjn
    have h_gap := gap_determines_value j_min hjn d hn_pos rfl hd_pos
    have h_prev_X : vanEckNthTerm (j_min - d) = X := by
      rw [← h_gap]
      exact h_eq_X
    have hd_le_jmin : d ≤ j_min := Nat.le_trans hd_bound (Nat.le_trans (Nat.le_add_left M k) h_jmin_ge)
    have hd_lt_jmin : j_min - d < j_min := by
      apply lt_of_le_of_ne (Nat.sub_le j_min d)
      intro heq
      have heq2 : j_min - d + d = j_min + d := congrArg (· + d) heq
      rw [Nat.sub_add_cancel hd_le_jmin] at heq2
      have heq3 : j_min + 0 = j_min + d := by
        calc
          j_min + 0 = j_min := by rw [Nat.add_zero]
          _         = j_min + d := heq2
      have h_d0 : 0 = d := Nat.add_left_cancel heq3
      exact hd_pos h_d0.symm
    have h_prev_ge_k : j_min - d ≥ k := by
      have h1 : j_min ≥ k + d := Nat.le_trans (Nat.add_le_add_left hd_bound k) h_jmin_ge
      have h2 : j_min - d ≥ k + d - d := Nat.sub_le_sub_right h1 d
      rw [Nat.add_sub_cancel] at h2
      exact h2
    have h_contra := h_min (j_min - d) hd_lt_jmin
    have h_both : p (j_min - d) := ⟨h_prev_ge_k, h_prev_X⟩
    exact h_contra h_both

-- Because `M` itself is evaluated, `M` appears recursively backwards bounding identical limits.
lemma M_occurrence_bounds (h_bound : ∀ k ≥ n, vanEckNthTerm k ≤ M)
    (h_no_zeros : ∀ k ≥ n, vanEckNthTerm k ≠ 0)
    (k : ℕ) (hk : k ≥ n + M + 1) (hn_pos : n ≥ 1) (hX : vanEckNthTerm (k + 1) = M) :
    vanEckNthTerm k = vanEckNthTerm (k - M) := by
  have hk_n : k ≥ n := Nat.le_trans (Nat.le_add_right n (M + 1)) hk
  have h_nz : vanEckNthTerm (k + 1) ≠ 0 := h_no_zeros (k + 1) (Nat.le_trans hk_n (Nat.le_add_right k 1))
  have hd_pos : M ≠ 0 := by
    intro h
    rw [h] at hX
    exact h_nz hX
  have h_gap := gap_determines_value k hk_n M hn_pos hX hd_pos
  exact h_gap

-- Inner Density Exclusion
lemma maximum_bounds_collision_collapse 
    (h_per : ∀ k ≥ n, vanEckNthTerm k = vanEckNthTerm (k + P))
    (h_bound : ∀ k ≥ n, vanEckNthTerm k ≤ M)
    (h_no_zeros : ∀ k ≥ n, vanEckNthTerm k ≠ 0)
    (hn_pos : n ≥ 1)
    (hM_exists : ∃ k ≥ n + M + 1, vanEckNthTerm k = M)
    (hM2 : M ≥ 2) : False := by
  sorry

-- The $M \le 1$ Homogeneity Collapse Native Closure!
lemma sequence_homogeneity_collapse_native 
    (h_per : ∀ k ≥ n, vanEckNthTerm k = vanEckNthTerm (k + P))
    (h_bound : ∀ k ≥ n, vanEckNthTerm k ≤ M)
    (h_no_zeros : ∀ k ≥ n, vanEckNthTerm k ≠ 0)
    (hn_pos : n ≥ 1)
    (hM_exists : ∃ k ≥ n + M + 1, vanEckNthTerm k = M) : 
    M ≤ 1 := by
  by_cases hM : M ≤ 1
  · exact hM
  · exfalso
    have hM2 : M ≥ 2 := Nat.lt_of_not_le hM
    exact maximum_bounds_collision_collapse h_per h_bound h_no_zeros hn_pos hM_exists hM2
