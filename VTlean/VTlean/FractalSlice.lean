/- Copyright Austin Anderson aided by Gemini 2026 -/
import VTlean.B
import VTlean.InsDel
import VTlean.DelCode
import VTlean.VTCode

open B List.Vector Finset

/-- The cumulative set of deletions of `x` restricted to the first `k` positions -/
def cumulativeDels {n : Nat} (x : List.Vector B n) (k : Nat) :
    Finset (List.Vector B (n - 1)) :=
  match k with
  | 0 => ∅
  | k' + 1 => List.toFinset (dS_le x k')

/-- Let's construct a simple vector of length 3 to build intuition. -/
def v_example : List.Vector B 3 := ⟨[B.O, B.I, B.O], rfl⟩

-- cumulativeDels takes a vector and a position `k` and returns all the sub-vectors
-- formed by deleting the bit at indices 0, 1, ..., up to k-1.
#check cumulativeDels v_example 1
#eval cumulativeDels v_example 0  -- ∅
#eval cumulativeDels v_example 1  -- {[B.I, B.O]} (deleted index 0)
#eval cumulativeDels v_example 2  -- {[B.O, B.O], [B.I, B.O]} (deleted index 0 and 1)
#eval cumulativeDels v_example 3  -- {[B.O, B.I], [B.O, B.O], [B.I, B.O]} (deleted index 0, 1, 2)


/-- B_k(x, y) holds if y is in the k-th deletion set but not in the cumulative (k-1)-th set -/
def isIncrementalDel {n : Nat} (x : List.Vector B n) (y : List.Vector B (n - 1)) (k : Nat) :
    Prop :=
  sDel x k = y ∧ y ∉ cumulativeDels x k

/-- The transition subset at index k -/
def TransitionSubset {n : Nat} (k : Nat) : Finset (List.Vector B n) :=
  Finset.univ.filter (fun x => x.val.getD k B.O ≠ x.val.getD (k - 1) B.O)

lemma sDel_eq_sDel_of_getD_eq {α : Type} [DecidableEq α] [Inhabited α] (X : List α) (k : Nat) (hk : k < X.length) (hk_pos : 0 < k)
  (h_eq : X.getD k default = X.getD (k - 1) default) :
  List.sDel X k = List.sDel X (k - 1) := by
  revert k
  induction X with
  | nil =>
    intro k hk hk_pos h_eq
    contradiction
  | cons x X' ih =>
    intro k hk hk_pos h_eq
    cases k with
    | zero => contradiction
    | succ k' =>
      cases k' with
      | zero =>
        cases X' with
        | nil => contradiction
        | cons x' X'' =>
          change List.sDel (x :: x' :: X'') 1 = List.sDel (x :: x' :: X'') 0
          have h_eq2 : x' = x := h_eq
          rw [h_eq2]
          cases X'' with
          | nil => rfl
          | cons x'' X''' => rfl
      | succ k'' =>
        cases X' with
        | nil => contradiction
        | cons x' X'' =>
          change x :: List.sDel (x' :: X'') (k'' + 1) = x :: List.sDel (x' :: X'') k''
          congr 1
          apply ih
          · have hlen : (x :: x' :: X'').length = (x' :: X'').length + 1 := rfl
            rw [hlen] at hk
            exact Nat.lt_of_succ_lt_succ hk
          · exact Nat.succ_pos k''
          · exact h_eq

/-- Theorem 1: B_k(x, y) implies x belongs to the transition subset (for k >= 1) -/
theorem incremental_del_impl_transition {n : Nat} {k : Nat} (_hk : 0 < k ∧ k < n)
    (x : List.Vector B n) (y : List.Vector B (n - 1)) (h_del : isIncrementalDel x y k) :
    x ∈ TransitionSubset k := by
  unfold TransitionSubset
  rw [Finset.mem_filter]
  refine ⟨Finset.mem_univ x, ?_⟩
  intro h_eq
  unfold isIncrementalDel at h_del
  rcases h_del with ⟨h_sdel_k, h_not_in_cumul⟩
  have h_k_pos : 0 < k := _hk.1
  cases hk_cases : k with
  | zero => omega
  | succ k' =>
    unfold cumulativeDels at h_not_in_cumul
    rw [hk_cases] at h_not_in_cumul
    have h_mem : y ∈ List.toFinset (dS_le x k') := by
      have h_sdel_eq : sDel x k = sDel x k' := by
        apply Subtype.ext
        change List.sDel x.val k = List.sDel x.val k'
        have h_k_eq : k' = k - 1 := by omega
        rw [h_k_eq]
        apply sDel_eq_sDel_of_getD_eq
        · have h_len : x.val.length = n := x.2
          omega
        · exact h_k_pos
        · exact h_eq
      rw [List.mem_toFinset]
      rw [mem_dS_le]
      use k'
      refine ⟨Nat.le_refl k', ?_⟩
      rw [← h_sdel_eq]
      exact h_sdel_k.symm
    contradiction

/-- The closed-form insertion bijection f_k(y) -/
def sloaneInsertion {n : Nat} (y : List.Vector B (n - 1)) (k : Nat) (hk : k < n) :
    List.Vector B n :=
  ⟨y.val.take k ++ [B.flip (y.val.getD (k - 1) B.O)] ++ y.val.drop k, by {
    rw [List.length_append, List.length_append, List.length_take, List.length_drop, y.2,
        List.length_singleton]
    omega
  }⟩

/-- Theorem 2 (Part 1): Deleting the k-th position of f_k(y) always yields y -/
theorem sloane_insertion_is_del {n : Nat} (y : List.Vector B (n - 1)) (k : Nat) (hk : k < n) :
    sDel (sloaneInsertion y k hk) k = y := by
  apply Subtype.ext
  dsimp [sloaneInsertion, sDel]
  have h_take_len : (y.val.take k).length = k := by {
    have h_k : k ≤ n - 1 := by omega
    rw [List.length_take]
    have h_len : y.val.length = n - 1 := y.2
    rw [h_len]
    exact min_eq_left h_k
  }
  have h_append_ge :
      List.sDel (y.val.take k ++ ([B.flip (y.val.getD (k - 1) B.O)] ++ y.val.drop k)) k =
      y.val.take k ++ List.sDel ([B.flip (y.val.getD (k - 1) B.O)] ++ y.val.drop k)
        (k - (y.val.take k).length) := by {
    apply List.sDel_append_of_ge
    · rw [h_take_len]
    · intro h_nil
      contradiction
  }
  rw [List.append_assoc]
  rw [h_append_ge, h_take_len, Nat.sub_self]
  change y.val.take k ++ List.sDel (B.flip (y.val.getD (k - 1) B.O) :: y.val.drop k) 0 = y.val
  rw [List.sDel_zero]
  exact List.take_append_drop k y.val

/-- Predicate expressing that index `k` is a transition point of `y` (bits differ at k‑1 and k). -/
def isTransitionIndex {n : Nat} (y : List.Vector B (n - 1)) (k : Nat) : Prop :=
  k < n ∧ y.val.getD (k - 1) B.O ≠ y.val.getD k B.O
/-- The moment change incurred by performing Sloane insertion at index `k`. -/
def sloaneInsertionChange {n : Nat} (y : List.Vector B (n - 1)) (k : Nat) : Nat :=
  match B.flip (y.val.getD (k - 1) B.O) with
  | B.O => num_RIs y k
  | B.I => num_LOs y k + wt y + 1

lemma sloaneInsertionChange_le_n {n : Nat} (hn : 0 < n) (y : List.Vector B (n - 1)) (k : Nat) :
    sloaneInsertionChange y k ≤ n := by {
  unfold sloaneInsertionChange
  change (match B.flip (y.toList.getD (k - 1) B.O) with
    | B.O => List.num_RIs y.toList k
    | B.I => List.num_LOs y.toList k + List.num_Is y.toList + 1) ≤ n
  split
  · have h_le := List.num_RIs_le_num_Is y.toList k
    have h_wt := List.num_Is_le_length y.toList
    have h_ylen : y.toList.length = n - 1 := y.2
    omega
  · have h_lo := List.num_LOs_le_num_Os y.toList k
    have h_os := List.num_Os_add_num_Is y.toList
    have h_ylen : y.toList.length = n - 1 := y.2
    have h_sum : List.num_LOs y.toList k + List.num_Is y.toList ≤ List.num_Os y.toList + List.num_Is y.toList := by omega
    rw [h_os] at h_sum
    rw [h_ylen] at h_sum
    have h_final : List.num_LOs y.toList k + List.num_Is y.toList + 1 ≤ n := by omega
    exact h_final
}


lemma List_getD_eq_getD_of_lt {α : Type} (l : List α) (i : Nat) (d₁ d₂ : α) (h : i < l.length) :
    l.getD i d₁ = l.getD i d₂ := by {
  revert i
  induction l with
  | nil => intro i h; contradiction
  | cons x xs ih =>
    intro i h
    cases i with
    | zero => rfl
    | succ i' =>
      change xs.getD i' d₁ = xs.getD i' d₂
      have h_len : i' < xs.length := by {
        dsimp [List.length] at h
        omega
      }
      exact ih i' h_len
}

lemma num_LOs_add_one (X : List B) (i : Nat) :
    List.num_LOs X (i + 1) = List.num_LOs X i + match X.getD i B.I with | B.O => 1 | B.I => 0 := by {
  revert i
  induction X with
  | nil =>
    intro i; rfl
  | cons x X' ih =>
    intro i
    cases i with
    | zero =>
      cases x with
      | O =>
        dsimp [List.num_LOs, List.getD]
        rw [List.num_LOs_zero X' 0]
        rfl
      | I =>
        dsimp [List.num_LOs, List.getD]
        rw [List.num_LOs_zero X' 0]
        rfl
    | succ i' =>
      cases x with
      | O =>
        dsimp [List.num_LOs, List.getD]
        rw [ih i']
        have h_eq : X'.getD i' B.I = X'[i']?.getD B.I := rfl
        rw [h_eq]
        omega
      | I =>
        dsimp [List.num_LOs, List.getD]
        rw [ih i']
        have h_eq : X'.getD i' B.I = X'[i']?.getD B.I := rfl
        rw [h_eq]
}

lemma num_LOs_monotone (X : List B) (k₁ k₂ : Nat) (h : k₁ ≤ k₂) :
    List.num_LOs X k₁ ≤ List.num_LOs X k₂ := by {
  induction h with
  | refl => exact Nat.le_refl _
  | step h_le ih =>
    rename_i m
    rw [num_LOs_add_one X m]
    omega
}

lemma num_LOs_strict_monotone {n : Nat} (y : List.Vector B (n - 1))
    (k₁ k₂ : Nat) (hk₂ : k₂ < n) (hkt : k₁ < k₂) (h_bit : y.toList.getD (k₂ - 1) B.O = B.O) :
    List.num_LOs y.toList k₁ < List.num_LOs y.toList k₂ := by {
  have h_le : k₁ ≤ k₂ - 1 := by omega
  have h_mon := num_LOs_monotone y.toList k₁ (k₂ - 1) h_le
  have h_eq_succ : k₂ = (k₂ - 1) + 1 := by omega
  rw [h_eq_succ]
  rw [num_LOs_add_one]
  have h_getD : y.toList.getD (k₂ - 1) B.I = B.O := by {
    have h_in_bounds : k₂ - 1 < y.toList.length := by {
      have h_len : y.toList.length = n - 1 := y.2
      omega
    }
    rw [List_getD_eq_getD_of_lt _ _ _ _ h_in_bounds]
    exact h_bit
  }
  rw [h_getD]
  dsimp
  omega
}

lemma num_RIs_add_one (X : List B) (i : Nat) :
    List.num_RIs X i = List.num_RIs X (i + 1) + match X.getD i B.O with | B.I => 1 | B.O => 0 := by {
  revert i
  induction X with
  | nil =>
    intro i; rfl
  | cons x X' ih =>
    intro i
    cases i with
    | zero =>
      cases x with
      | O =>
        dsimp [List.num_RIs, List.getD]
        rw [List.num_RIs_zero]
        rfl
      | I =>
        dsimp [List.num_RIs, List.getD]
        rw [List.num_RIs_zero]
        rfl
    | succ i' =>
      dsimp [List.num_RIs, List.getD]
      rw [ih i']
      rfl
}

lemma num_RIs_monotone (X : List B) (k₁ k₂ : Nat) (h : k₁ ≤ k₂) :
    List.num_RIs X k₂ ≤ List.num_RIs X k₁ := by {
  induction h with
  | refl => exact Nat.le_refl _
  | step h_le ih =>
    rename_i m
    have h_next : List.num_RIs X (m + 1) ≤ List.num_RIs X m := by {
      rw [num_RIs_add_one X m]
      omega
    }
    have h_eq : m.succ = m + 1 := rfl
    rw [h_eq]
    omega
}

lemma num_RIs_strict_monotone {n : Nat} (y : List.Vector B (n - 1))
    (k₁ k₂ : Nat) (_hk₂ : k₂ < n) (hkt : k₁ < k₂) (h_bit : y.toList.getD (k₂ - 1) B.O = B.I) :
    List.num_RIs y.toList k₂ < List.num_RIs y.toList k₁ := by {
  have h_le : k₁ ≤ k₂ - 1 := by omega
  have h_mon := num_RIs_monotone y.toList k₁ (k₂ - 1) h_le
  have h_rec := num_RIs_add_one y.toList (k₂ - 1)
  have h_eq_succ : k₂ = (k₂ - 1) + 1 := by omega
  rw [← h_eq_succ] at h_rec
  rw [h_rec] at h_mon
  rw [h_bit] at h_mon
  dsimp at h_mon
  omega
}

lemma sloaneInsertionChange_inj {n : Nat} (y : List.Vector B (n - 1))
    (k₁ k₂ : Nat) (hk₁ : k₁ < n) (hk₂ : k₂ < n) (hkt : k₁ < k₂) :
    sloaneInsertionChange y k₁ ≠ sloaneInsertionChange y k₂ := by {
  unfold sloaneInsertionChange
  change (match B.flip (y.toList.getD (k₁ - 1) B.O) with
    | B.O => List.num_RIs y.toList k₁
    | B.I => List.num_LOs y.toList k₁ + List.num_Is y.toList + 1) ≠
         (match B.flip (y.toList.getD (k₂ - 1) B.O) with
    | B.O => List.num_RIs y.toList k₂
    | B.I => List.num_LOs y.toList k₂ + List.num_Is y.toList + 1)
  generalize h₁ : B.flip (y.toList.getD (k₁ - 1) B.O) = b₁
  generalize h₂ : B.flip (y.toList.getD (k₂ - 1) B.O) = b₂
  cases b₁ <;> cases b₂
  · -- Case: b₁ = B.O, b₂ = B.O
    have h_bit : y.toList.getD (k₂ - 1) B.O = B.I := by { apply B.eq_of_flip_eq; rw [h₂]; rfl }
    have h_lt := num_RIs_strict_monotone y k₁ k₂ hk₂ hkt h_bit
    exact (ne_of_lt h_lt).symm
  · -- Case: b₁ = B.O, b₂ = B.I
    intro h_eq
    have h_le := List.num_RIs_le_num_Is y.toList k₁
    have h_lt : List.num_RIs y.toList k₁ < List.num_LOs y.toList k₂ + List.num_Is y.toList + 1 := by linarith
    exact (ne_of_lt h_lt) h_eq
  · -- Case: b₁ = B.I, b₂ = B.O
    intro h_eq
    have h_le := List.num_RIs_le_num_Is y.toList k₂
    have h_lt : List.num_RIs y.toList k₂ < List.num_LOs y.toList k₁ + List.num_Is y.toList + 1 := by linarith
    exact (ne_of_lt h_lt) h_eq.symm
  · -- Case: b₁ = B.I, b₂ = B.I
    have h_bit : y.toList.getD (k₂ - 1) B.O = B.O := by { apply B.eq_of_flip_eq; rw [h₂]; rfl }
    have h_lt := num_LOs_strict_monotone y k₁ k₂ hk₂ hkt h_bit
    intro h_eq
    have h_lt_eq : List.num_LOs y.toList k₁ + List.num_Is y.toList + 1 < List.num_LOs y.toList k₂ + List.num_Is y.toList + 1 := by linarith
    exact (ne_of_lt h_lt_eq) h_eq
}


lemma List_getD_take {α : Type} (l : List α) (n m : Nat) (d : α) (h : m < n) :
    (l.take n).getD m d = l.getD m d := by {
  revert m
  induction n generalizing l with
  | zero => intro m h; contradiction
  | succ n' ih =>
    intro m h
    cases l with
    | nil => rfl
    | cons x xs =>
      cases m with
      | zero => rfl
      | succ m' =>
        change (xs.take n').getD m' d = xs.getD m' d
        apply ih
        omega
}

lemma getD_sloaneInsertion {n k : Nat} (hk : k < n) (hk_pos : 0 < k) (y : List.Vector B (n - 1)) :
  (sloaneInsertion y k hk).val.getD (k - 1) B.O = y.val.getD (k - 1) B.O ∧
  (sloaneInsertion y k hk).val.getD k B.O = B.flip (y.val.getD (k - 1) B.O) := by
  have h_take_len : (y.val.take k).length = k := by
    have h_k : k ≤ n - 1 := by omega
    rw [List.length_take]
    have h_len : y.val.length = n - 1 := y.2
    rw [h_len]
    exact min_eq_left h_k
  have h1 : (sloaneInsertion y k hk).val = y.val.take k ++ (B.flip (y.val.getD (k - 1) B.O) :: y.val.drop k) := by
    change y.val.take k ++ [B.flip (y.val.getD (k - 1) B.O)] ++ y.val.drop k = _
    rw [List.append_assoc]
    rfl
  constructor
  · rw [h1]
    have h_lt : k - 1 < (y.val.take k).length := by omega
    rw [List.getD_append _ _ _ _ h_lt]
    apply List_getD_take
    omega
  · rw [h1]
    have h2 : ((y.val.take k) ++ (B.flip (y.val.getD (k - 1) B.O) :: y.val.drop k)).getD k B.O = (B.flip (y.val.getD (k - 1) B.O) :: y.val.drop k).getD (k - (y.val.take k).length) B.O := by
      apply List.getD_append_right
      omega
    rw [h2, h_take_len, Nat.sub_self]
    rfl

lemma sIns_eq_take_drop {α : Type} (X : List α) (k : Nat) (b : α) (hk : k ≤ X.length) :
  List.sIns X k b = X.take k ++ [b] ++ X.drop k := by
  revert k
  induction X with
  | nil =>
    intro k hk
    change k ≤ 0 at hk
    have hk0 : k = 0 := by omega
    rw [hk0]
    rfl
  | cons x X' ih =>
    intro k hk
    cases k with
    | zero => rfl
    | succ k' =>
      change x :: List.sIns X' k' b = (x :: X'.take k') ++ [b] ++ X'.drop k'
      change x :: List.sIns X' k' b = x :: (X'.take k' ++ [b] ++ X'.drop k')
      congr 1
      apply ih
      have h_len : (x :: X').length = X'.length + 1 := rfl
      rw [h_len] at hk
      exact Nat.le_of_succ_le_succ hk

lemma sDel_getD {α : Type} [Inhabited α] (X : List α) (k : Nat) (hk_pos : 0 < k) (hk_lt : k < X.length) (d : α) :
  (List.sDel X k).getD (k - 1) d = X.getD (k - 1) d := by
  revert k
  induction X with
  | nil => intro k _ hk_lt; contradiction
  | cons x X' ih =>
    intro k hk_pos hk_lt
    cases k with
    | zero => contradiction
    | succ k' =>
      cases k' with
      | zero =>
        cases X' with
        | nil => contradiction
        | cons x' X'' =>
          change (x :: List.sDel (x' :: X'') 0).getD 0 d = (x :: x' :: X'').getD 0 d
          rfl
      | succ k'' =>
        cases X' with
        | nil => contradiction
        | cons x' X'' =>
          change (x :: List.sDel (x' :: X'') (k'' + 1)).getD (k'' + 1) d = (x :: x' :: X'').getD (k'' + 1) d
          change (List.sDel (x' :: X'') (k'' + 1)).getD k'' d = (x' :: X'').getD k'' d
          apply ih
          · exact Nat.succ_pos k''
          · have hlen : (x :: x' :: X'').length = (x' :: X'').length + 1 := rfl
            rw [hlen] at hk_lt
            exact Nat.lt_of_succ_lt_succ hk_lt

lemma sIns_sDel_eq_self {α : Type} [DecidableEq α] [Inhabited α] (X : List α) (k : Nat)
  (hk : k < X.length) :
  List.sIns (List.sDel X k) k (X.getD k default) = X := by
  revert k
  induction X with
  | nil => intro k hk; contradiction
  | cons x X' ih =>
    intro k hk
    cases k with
    | zero =>
      change List.sIns (List.sDel (x :: X') 0) 0 ((x :: X').getD 0 default) = x :: X'
      rw [List.sDel_zero]
      change List.sIns X' 0 x = x :: X'
      rw [List.sIns_zero]
    | succ k' =>
      cases X' with
      | nil =>
        change k' + 1 < 1 at hk
        omega
      | cons x' X'' =>
        change List.sIns (List.sDel (x :: x' :: X'') (k' + 1)) (k' + 1) ((x :: x' :: X'').getD (k' + 1) default) = x :: x' :: X''
        have h_sdel : List.sDel (x :: x' :: X'') (k' + 1) = x :: List.sDel (x' :: X'') k' := rfl
        rw [h_sdel]
        have h_sins : List.sIns (x :: List.sDel (x' :: X'') k') (k' + 1) ((x :: x' :: X'').getD (k' + 1) default) = x :: List.sIns (List.sDel (x' :: X'') k') k' ((x' :: X'').getD k' default) := rfl
        rw [h_sins]
        congr 1
        apply ih
        have h_len : (x :: x' :: X'').length = (x' :: X'').length + 1 := rfl
        rw [h_len] at hk
        exact Nat.lt_of_succ_lt_succ hk

lemma sloaneInsertion_sDel_eq_self {n : Nat} (x : List.Vector B n) (k : Nat) (hk : k < n) (hk_pos : 0 < k)
  (h_neq : x.val.getD k B.O ≠ x.val.getD (k - 1) B.O) :
  sloaneInsertion (sDel x k) k hk = x := by
  apply Subtype.ext
  have h1 : (sloaneInsertion (sDel x k) k hk).val = (sDel x k).val.take k ++ [B.flip ((sDel x k).val.getD (k - 1) B.O)] ++ (sDel x k).val.drop k := rfl
  rw [h1]

  have h_sdel_getD : (sDel x k).val.getD (k - 1) B.O = x.val.getD (k - 1) B.O := by
    change (List.sDel x.val k).getD (k - 1) B.O = x.val.getD (k - 1) B.O
    have h_lt : k < x.val.length := by
      have hlen : x.val.length = n := x.2
      omega
    exact sDel_getD x.val k hk_pos h_lt B.O

  rw [h_sdel_getD]
  have h_flip : B.flip (x.val.getD (k - 1) B.O) = x.val.getD k B.O := B.flip_of_ne h_neq.symm
  rw [h_flip]

  have h_sins : (sDel x k).val.take k ++ [x.val.getD k B.O] ++ (sDel x k).val.drop k = List.sIns (sDel x k).val k (x.val.getD k B.O) := by
    have h_len : k ≤ (sDel x k).val.length := by
      have hlen1 : x.val.length = n := x.2
      have hlen2 : (sDel x k).val.length = n - 1 := (sDel x k).2
      rw [hlen2]
      omega
    exact (sIns_eq_take_drop (sDel x k).val k (x.val.getD k B.O) h_len).symm

  rw [h_sins]
  change List.sIns (List.sDel x.val k) k (x.val.getD k B.O) = x.val
  have h_lt : k < x.val.length := by
    have hlen : x.val.length = n := x.2
    omega
  exact sIns_sDel_eq_self x.val k h_lt

/-- Theorem 2 (Part 2): The Sloane insertion is a bijection to the transition subset -/
def sloane_bijection_to_transition {n : Nat} (k : Nat) (_hk : 0 < k ∧ k < n) :
    Equiv (List.Vector B (n - 1)) { x : List.Vector B n // x ∈ TransitionSubset k } where
  toFun := fun y => ⟨sloaneInsertion y k _hk.2, by
    unfold TransitionSubset
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have h_getD := getD_sloaneInsertion _hk.2 _hk.1 y
    rw [h_getD.1, h_getD.2]
    have h_flip := B.flip_ne_self (y.val.getD (k - 1) B.O)
    exact h_flip.symm
  ⟩
  invFun := fun x => sDel x.1 k
  left_inv := fun y => sloane_insertion_is_del y k _hk.2
  right_inv := fun x => Subtype.ext (by
    have h_mem := x.2
    unfold TransitionSubset at h_mem
    rw [Finset.mem_filter] at h_mem
    exact sloaneInsertion_sDel_eq_self x.1 k _hk.2 _hk.1 h_mem.2
  )

/-- Helper: For positive lengths, cumulativeDels of length n equals dS -/
lemma cumulativeDels_self {n : Nat} (hn : 0 < n) (x : List.Vector B n) :
    cumulativeDels x n = dS x := by
  cases n with
  | zero => contradiction
  | succ n' => rfl

/-- Theorem 3: Distinct VT0 codewords have disjoint deletion sets. -/
theorem vt0_dels_disjoint
  {n : Nat} (hn : 0 < n) (x1 x2 : List.Vector B n)
  (hx1 : x1 ∈ Finset.VTCode n 0) (hx2 : x2 ∈ Finset.VTCode n 0) (h_ne : x1 ≠ x2) :
  Disjoint (cumulativeDels x1 n) (cumulativeDels x2 n) := by
  rw [cumulativeDels_self hn, cumulativeDels_self hn]
  have h_delcode := DelCode_VTCode n 0
  unfold is_DelCode at h_delcode
  have h_inter := h_delcode x1 hx1 x2 hx2 h_ne
  rw [Finset.disjoint_iff_inter_eq_empty]
  exact h_inter

lemma moment_sIns {n : Nat} (X : List.Vector B n) (i : Nat) (b : B) :
  moment (sIns X i b) = moment X + match b with
    | B.O => num_RIs X i
    | B.I => num_LOs X i + wt X + 1 := by
  cases b
  · have h := moment_sIns_zero X (i:=i)
    exact h
  · have h := moment_sIns_one X (i:=i)
    dsimp
    omega

lemma moment_sloaneInsertion {n : Nat} (y : List.Vector B (n - 1)) (k : Nat) (hk : k < n) :
  moment (sloaneInsertion y k hk) = moment y + match B.flip (y.val.getD (k - 1) B.O) with
    | B.O => num_RIs y k
    | B.I => num_LOs y k + wt y + 1 := by {
  have h_val : (sloaneInsertion y k hk).val = (sIns y k (B.flip (y.val.getD (k - 1) B.O))).val := by
    have h_len : k ≤ y.val.length := by {
      have h_ylen : y.val.length = n - 1 := y.2
      omega
    }
    exact (sIns_eq_take_drop y.val k (B.flip (y.val.getD (k - 1) B.O)) h_len).symm
  change List.moment (sloaneInsertion y k hk).val = _
  rw [h_val]
  have h_moment_sIns := moment_sIns y k (B.flip (y.val.getD (k - 1) B.O))
  change List.moment (sIns y k (B.flip (y.val.getD (k - 1) B.O))).val = _ at h_moment_sIns
  exact h_moment_sIns
}


lemma moment_sloaneInsertion_eq_change {n : Nat} (y : List.Vector B (n - 1)) (k : Nat) (hk : k < n) :
    moment (sloaneInsertion y k hk) = moment y + sloaneInsertionChange y k := by {
  unfold sloaneInsertionChange
  exact moment_sloaneInsertion y k hk
}

lemma mod_add_ne_mod {A D m : Nat} (hD_pos : 0 < D) (hD_lt : D < m) :
    A % m ≠ (A + D) % m := by {
  intro h_eq
  have h_modeq : Nat.ModEq m A (A + D) := h_eq
  have h_modeq2 : Nat.ModEq m (0 + A) (D + A) := by {
    rw [Nat.zero_add, Nat.add_comm D A]
    exact h_modeq
  }
  have h_d : Nat.ModEq m 0 D := Nat.ModEq.add_right_cancel' A h_modeq2
  have h_d2 : 0 % m = D % m := h_d
  have hm_pos : 0 < m := by omega
  rw [Nat.zero_mod m, Nat.mod_eq_of_lt hD_lt] at h_d2
  omega
}

/-- Injectivity of the moment modulo n + 1 under `sloaneInsertion`. For any `y` and distinct
indices `k₁ ≠ k₂`, their moments are distinct modulo `n + 1`. -/
lemma moment_sloaneInsertion_inj {n : Nat} (y : List.Vector B (n - 1))
    (k₁ k₂ : Nat) (hk₁ : k₁ < n) (hk₂ : k₂ < n) (h_ne : k₁ ≠ k₂) :
    moment (sloaneInsertion y k₁ hk₁) % (n + 1) ≠ moment (sloaneInsertion y k₂ hk₂) % (n + 1) := by {
  have hn_pos : 0 < n := by omega
  rcases Nat.lt_or_gt_of_ne h_ne with hkt | hkt
  · -- Case 1: k₁ < k₂
    have h_ch_inj := sloaneInsertionChange_inj y k₁ k₂ hk₁ hk₂ hkt
    rw [moment_sloaneInsertion_eq_change y k₁ hk₁, moment_sloaneInsertion_eq_change y k₂ hk₂]
    have hC₁_le := sloaneInsertionChange_le_n hn_pos y k₁
    have hC₂_le := sloaneInsertionChange_le_n hn_pos y k₂
    generalize hC₁ : sloaneInsertionChange y k₁ = C₁ at *
    generalize hC₂ : sloaneInsertionChange y k₂ = C₂ at *
    rcases Nat.lt_or_gt_of_ne h_ch_inj with h_ch_lt | h_ch_lt
    · -- Sub-case 1.1: C₁ < C₂
      let D := C₂ - C₁
      have hD_pos : 0 < D := by omega
      have hC₂_eq : C₂ = C₁ + D := by omega
      have hD_lt : D < n + 1 := by omega
      rw [hC₂_eq, ← Nat.add_assoc]
      exact mod_add_ne_mod hD_pos hD_lt
    · -- Sub-case 1.2: C₂ < C₁
      let D := C₁ - C₂
      have hD_pos : 0 < D := by omega
      have hC₁_eq : C₁ = C₂ + D := by omega
      have hD_lt : D < n + 1 := by omega
      rw [hC₁_eq, ← Nat.add_assoc]
      intro h_eq
      exact mod_add_ne_mod hD_pos hD_lt h_eq.symm
  · -- Case 2: k₂ < k₁
    have h_ch_inj := sloaneInsertionChange_inj y k₂ k₁ hk₂ hk₁ hkt
    rw [moment_sloaneInsertion_eq_change y k₁ hk₁, moment_sloaneInsertion_eq_change y k₂ hk₂]
    have hC₁_le := sloaneInsertionChange_le_n hn_pos y k₁
    have hC₂_le := sloaneInsertionChange_le_n hn_pos y k₂
    generalize hC₁ : sloaneInsertionChange y k₁ = C₁ at *
    generalize hC₂ : sloaneInsertionChange y k₂ = C₂ at *
    rcases Nat.lt_or_gt_of_ne h_ch_inj.symm with h_ch_lt | h_ch_lt
    · -- Sub-case 2.1: C₁ < C₂
      let D := C₂ - C₁
      have hD_pos : 0 < D := by omega
      have hC₂_eq : C₂ = C₁ + D := by omega
      have hD_lt : D < n + 1 := by omega
      rw [hC₂_eq, ← Nat.add_assoc]
      exact mod_add_ne_mod hD_pos hD_lt
    · -- Sub-case 2.2: C₂ < C₁
      let D := C₁ - C₂
      have hD_pos : 0 < D := by omega
      have hC₁_eq : C₁ = C₂ + D := by omega
      have hD_lt : D < n + 1 := by omega
      rw [hC₁_eq, ← Nat.add_assoc]
      intro h_eq
      exact mod_add_ne_mod hD_pos hD_lt h_eq.symm
}
