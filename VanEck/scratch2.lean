import VanEck

def zerosCount : ℕ → ℕ
  | 0 => 1
  | m + 1 => if vanEckNthTerm (m + 1) = 0 then zerosCount m + 1 else zerosCount m

def lastZero : ℕ → ℕ
  | 0 => 0
  | m + 1 => if vanEckNthTerm (m + 1) = 0 then m + 1 else lastZero m

def is_bound (n v : ℕ) : Prop := ∀ i ≤ n, vanEckNthTerm i ≤ v

lemma zerosCount_pos (m : ℕ) : zerosCount m ≥ 1 := by
  induction m with
  | zero => exact Nat.le_refl 1
  | succ m ih =>
    unfold zerosCount
    split
    · exact Nat.le_trans ih (Nat.le_add_right _ _)
    · exact ih

lemma vanEck_distance_to_prev_zero (m : ℕ) (hz : vanEckNthTerm (m + 1) = 0) :
    vanEckNthTerm (m + 2) = m + 1 - lastZero m := sorry

lemma lastZero_le_gaps (m v : ℕ) (h_bound : ∀ i ≤ m + 1, vanEckNthTerm i ≤ v) :
    lastZero m ≤ (zerosCount m - 1) * v := by
  induction m with
  | zero =>
    unfold lastZero
    unfold zerosCount
    have h_sub : 1 - 1 = 0 := rfl
    rw [h_sub]
    exact Nat.zero_le _
  | succ m ih =>
    by_cases hz : vanEckNthTerm (m + 1) = 0
    · unfold lastZero
      rw [if_pos hz]
      unfold zerosCount
      rw [if_pos hz]
      have hs : zerosCount m + 1 - 1 = zerosCount m := Nat.add_sub_cancel (zerosCount m) 1
      rw [hs]
      have h_bound_m : ∀ i ≤ m + 1, vanEckNthTerm i ≤ v := fun i hi => h_bound i (Nat.le_trans hi (Nat.le_succ _))
      have h_ih := ih h_bound_m
      have hd := vanEck_distance_to_prev_zero m hz
      have h_val := h_bound (m + 2) (Nat.le_refl _)
      rw [hd] at h_val
      have h_add : m + 1 ≤ v + lastZero m := Nat.le_add_of_sub_le h_val
      have h_mul : v + (zerosCount m - 1) * v = (1 + (zerosCount m - 1)) * v := by
        rw [Nat.add_mul, Nat.one_mul]
      have h_sub_add : 1 + (zerosCount m - 1) = zerosCount m := by
        have h_pos := zerosCount_pos m
        rw [Nat.add_comm]
        exact Nat.sub_add_cancel h_pos
      rw [h_sub_add] at h_mul
      have h_trans : v + lastZero m ≤ v + (zerosCount m - 1) * v := Nat.add_le_add_left h_ih v
      rw [h_mul] at h_trans
      exact Nat.le_trans h_add h_trans
    · unfold lastZero
      rw [if_neg hz]
      unfold zerosCount
      rw [if_neg hz]
      have h_bound_m : ∀ i ≤ m + 1, vanEckNthTerm i ≤ v := fun i hi => h_bound i (Nat.le_trans hi (Nat.le_succ _))
      exact ih h_bound_m
