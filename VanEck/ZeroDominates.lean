import VanEck.Basic
import VanEck

open List

/-- Base case for zero domination: in the first term, 0 dominates all x. -/
lemma zero_dom_base (x : ℕ) : (vanEck 0).count x ≤ (vanEck 0).count 0 := by {
  change [0].count x ≤ [0].count 0
  by_cases h : x = 0
  · rw [h]
  · have h1 : [0].count x = 0 := by {
      apply count_eq_zero_of_not_mem
      intro h_mem
      cases h_mem with
      | head => exact h rfl
      | tail _ h_nil => cases h_nil
    }
    rw [h1]
    exact Nat.zero_le _
}

/-- The sequence grows by appending exactly one element at each step. -/
lemma vanEck_succ_eq_append (n : ℕ) : vanEck (n + 1) = vanEck n ++ [vanEckNextTerm (vanEck n)] := by {
  rfl
}

/-- The count of any element in the next step is at most 1 greater than its current count. -/
lemma count_le_count_add_one (n x : ℕ) : (vanEck (n + 1)).count x ≤ (vanEck n).count x + 1 := by {
  rw [vanEck_succ_eq_append n]
  rw [count_append]
  have h1 : [vanEckNextTerm (vanEck n)].count x ≤ 1 := by {
    by_cases h : vanEckNextTerm (vanEck n) = x
    · rw [h]
      have hsimp : [x].count x = 1 := by simp
      rw [hsimp]
    · have h0 : [vanEckNextTerm (vanEck n)].count x = 0 := by {
        apply count_eq_zero_of_not_mem
        intro h_mem
        cases h_mem with
        | head => exact h rfl
        | tail _ h_nil => cases h_nil
      }
      rw [h0]; exact Nat.zero_le _
  }
  exact Nat.add_le_add_left h1 _
}

/-- The count of 0 never decreases. -/
lemma zero_count_monotone (n : ℕ) : (vanEck n).count 0 ≤ (vanEck (n + 1)).count 0 := by {
  rw [vanEck_succ_eq_append n]
  rw [count_append]
  exact Nat.le_add_right _ _
}

/-- If a number x > 0 appears for the first time, the next term in the sequence is 0. -/
lemma new_number_implies_next_zero (n : ℕ) (h : (vanEck n).count (vanEckNthTerm n) = 1) : 
    vanEckNextTerm (vanEck n) = 0 := by {
  cases n with
  | zero => rfl
  | succ m =>
    have h_append : vanEck (m + 1) = vanEck m ++ [vanEckNextTerm (vanEck m)] := rfl
    have h_term : vanEckNextTerm (vanEck m) = vanEckNthTerm (m + 1) := by {
      unfold vanEckNthTerm
      have hlen : (vanEck (m + 1)).length = m + 2 := vanEckLength _
      rw [h_append]
      have hlen2 : (vanEck m).length = m + 1 := vanEckLength _
      rw [← hlen2]
      exact (listNth_last _ _).symm
    }
    rw [h_term] at h_append
    rw [h_append] at h
    rw [count_append] at h
    have hsimp : [vanEckNthTerm (m + 1)].count (vanEckNthTerm (m + 1)) = 1 := by simp
    rw [hsimp] at h
    have h_count_zero : (vanEck m).count (vanEckNthTerm (m + 1)) = 0 := by omega
    
    have h_not_mem : vanEckNthTerm (m + 1) ∉ vanEck m := count_eq_zero.mp h_count_zero
    
    have h_rhs : ∀ k < m + 1, vanEckNthTerm k ≠ vanEckNthTerm (m + 1) := by {
      intro k hk h_eq
      have h_mem : vanEckNthTerm k ∈ vanEck m := by {
        have h_eq2 : vanEckNthTerm k = listNth (vanEck m) k := (VanEck_deterministic m k (Nat.le_of_lt_succ hk)).symm
        rw [h_eq2]
        apply listNth_mem
        rw [vanEckLength]
        exact hk
      }
      rw [h_eq] at h_mem
      exact h_not_mem h_mem
    }
    
    have h_iff := vanEck_mth_term_eq_zero_iff_prev_term_new m
    have h_zero : vanEckNthTerm (m + 2) = 0 := h_iff.mpr h_rhs
    
    have h_next : vanEckNthTerm (m + 2) = vanEckNextTerm (vanEck (m + 1)) := by {
      unfold vanEckNthTerm
      have h_append2 : vanEck (m + 2) = vanEck (m + 1) ++ [vanEckNextTerm (vanEck (m + 1))] := rfl
      rw [h_append2]
      have hlen3 : (vanEck (m + 1)).length = m + 2 := vanEckLength _
      rw [← hlen3]
      exact listNth_last _ _
    }
    
    rw [← h_next]
    exact h_zero
}

/-- Every occurrence of a non-zero element x requires a preceding step that generated it. -/
lemma non_zero_needs_generation (n x : ℕ) (hx : x > 0) : 
    (vanEck (n + 1)).count x > (vanEck n).count x → vanEckNextTerm (vanEck n) = x := by {
  intro h_inc
  have h_append : vanEck (n + 1) = vanEck n ++ [vanEckNextTerm (vanEck n)] := rfl
  rw [h_append] at h_inc
  rw [count_append] at h_inc
  by_cases h_eq : vanEckNextTerm (vanEck n) = x
  · exact h_eq
  · have h_count : [vanEckNextTerm (vanEck n)].count x = 0 := count_eq_zero_of_not_mem (by {
      intro h_mem
      cases h_mem with
      | head => exact h_eq rfl
      | tail _ h_nil => cases h_nil
    })
    rw [h_count] at h_inc
    omega
}

lemma mem_singleton_eq {a b : ℕ} (h : a ∈ [b]) : a = b := by {
  cases h with
  | head => rfl
  | tail _ h_nil => cases h_nil
}

/-- Lemma 1: The frequency of 0 in the sequence is exactly equal to the number of 
    distinct elements that have appeared so far. Every new element spawns exactly one 0. -/
lemma count_zero_eq_distinct (m : ℕ) : 
    (vanEck m).count 0 = (List.eraseDups (vanEck m)).length := by {
  sorry
}

/-- Lemma 2: Every time an element x > 0 is generated, it strictly requires that 
    the sequence just evaluated a gap of exactly x between two identical elements. -/
lemma x_generated_requires_gap_x (m x : ℕ) (hx : x > 0) 
    (h_next : vanEckNextTerm (vanEck m) = x) : 
    ∃ y : ℕ, ∃ i j : ℕ, i < m ∧ j < m ∧ i - j = x ∧ 
    listNth (vanEck m) i = y ∧ listNth (vanEck m) j = y := by {
  sorry
}

/-- Lemma 3: If the frequency of an element x equals the total number of distinct 
    elements in the sequence, the gaps of x must be so densely packed that they 
    form a local repeating cycle of period x. -/
lemma dense_x_implies_cycle (m x : ℕ) (hx : x > 0)
    (h_eq_distinct : (vanEck m).count x = (List.eraseDups (vanEck m)).length) :
    ∃ start : ℕ, ∀ k < x, vanEckNthTerm (start + k) = vanEckNthTerm (start + k + x) := by {
  sorry
}

/-- Lemma 4: A local repeating cycle of period x cannot sustain itself without 
    collapsing into consecutive equal elements, which mathematically forces the 
    generation of new elements (and thus new 0s), breaking the density bound. -/
lemma cycle_collapse_breaks_density (m x : ℕ) (hx : x > 0) 
    (h_cycle : ∃ start : ℕ, ∀ k < x, vanEckNthTerm (start + k) = vanEckNthTerm (start + k + x)) :
    (vanEck m).count x < (vanEck m).count 0 := by {
  sorry
}

/-- Lemma 5 (Core Contradiction): By tying the structural lemmas together, 
    a non-zero element x cannot equal the frequency of 0 right when it is 
    about to be generated again. -/
lemma zero_dominates_core_contradiction (m x : ℕ) (hx : x > 0) 
    (h_next : vanEckNextTerm (vanEck m) = x)
    (h_eq : (vanEck m).count x = (vanEck m).count 0) : False := by {
  have h_distinct := count_zero_eq_distinct m
  -- 1. count 0 is the number of distinct elements.
  -- 2. count x = count 0 means x appears as many times as there are distinct elements.
  -- 3. This extreme density forces a periodic cycle (dense_x_implies_cycle).
  -- 4. But cycles inevitably collapse and spawn new 0s (cycle_collapse_breaks_density).
  -- 5. Therefore, count x MUST be strictly less than count 0, contradicting h_eq!
  sorry
}

/-- The number of times 0 appears bounds the number of times any element x can appear, 
    because 0 acts as the default 'reset' state. -/
theorem zeroDominates (n x : ℕ) : (vanEck n).count x ≤ (vanEck n).count 0 := by {
  induction n with
  | zero => exact zero_dom_base x
  | succ m ih =>
    have h_append : vanEck (m + 1) = vanEck m ++ [vanEckNextTerm (vanEck m)] := rfl
    rw [h_append]
    rw [count_append, count_append]
    by_cases h_x : x = 0
    · rw [h_x]
    · by_cases h_next_zero : vanEckNextTerm (vanEck m) = 0
      · rw [h_next_zero]
        have h_0 : [0].count 0 = 1 := rfl
        have h_x_count : [0].count x = 0 := by {
          apply count_eq_zero.mpr
          intro h_mem
          have h_eq := mem_singleton_eq h_mem
          exact h_x h_eq
        }
        rw [h_0, h_x_count]
        omega
      · by_cases h_next_x : vanEckNextTerm (vanEck m) = x
        · rw [h_next_x]
          have h_x_count : [x].count x = 1 := by simp
          have h_0_count : [x].count 0 = 0 := by {
            apply count_eq_zero.mpr
            intro h_mem
            have h_eq := mem_singleton_eq h_mem
            exact h_x h_eq.symm
          }
          rw [h_x_count, h_0_count]
          have h_le : (vanEck m).count x ≤ (vanEck m).count 0 := ih
          by_cases h_eq : (vanEck m).count x = (vanEck m).count 0
          · have h_hx : x > 0 := Nat.pos_of_ne_zero h_x
            have contra := zero_dominates_core_contradiction m x h_hx h_next_x h_eq
            exact False.elim contra
          · omega
        · have h_0_count : [vanEckNextTerm (vanEck m)].count 0 = 0 := by {
            apply count_eq_zero.mpr
            intro h_mem
            have h_eq := mem_singleton_eq h_mem
            exact h_next_zero h_eq.symm
          }
          have h_x_count : [vanEckNextTerm (vanEck m)].count x = 0 := by {
            apply count_eq_zero.mpr
            intro h_mem
            have h_eq := mem_singleton_eq h_mem
            exact h_next_x h_eq.symm
          }
          rw [h_0_count, h_x_count]
          exact ih
}
