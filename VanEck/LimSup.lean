import VanEck
import Mathlib.Data.Finset.Basic
import Mathlib.Algebra.Order.Ring.Defs

open Finset

/-!
# Credits
The sequence of logic implemented here natively traces the structure 
established by Jordan Linus in their June 2019 commentary.
Reference to the Van Eck Sequence: OEIS A181391
-/

/-!
# Van Eck Sequence LimSup Theorem

This file formalizes the proof that the limsup of a(n)/sqrt(n) >= 1.
We prove this by showing that whenever a(n) = 0, there exists some m ≤ n + 1
such that a(m) * a(m) is on the order of n.

The proof relies on two cases based on the number of zeros up to n.
-/

/-- Number of zeros up to index m -/
def zerosCount : ℕ → ℕ
  | 0 => 1
  | m + 1 => if vanEckNthTerm (m + 1) = 0 then zerosCount m + 1 else zerosCount m

/-- Index of the most recent zero up to index m -/
def lastZero : ℕ → ℕ
  | 0 => 0
  | m + 1 => if vanEckNthTerm (m + 1) = 0 then m + 1 else lastZero m

/-- We define a max sequence value upper bound v. -/
def is_bound (n v : ℕ) : Prop := ∀ i ≤ n, vanEckNthTerm i ≤ v

/-- 
The zerosCount counts the number of zeros, which matches the filter cardinality plus 1.
-/
lemma zerosCount_eq_card (m : ℕ) : 
    zerosCount m = ((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)).card + 1 := by {
  induction m with
  | zero =>
    unfold zerosCount
    have h : Finset.range 0 = ∅ := rfl
    rw [h, Finset.filter_empty, Finset.card_empty, Nat.zero_add]
  | succ m ih =>
    unfold zerosCount
    have h_range : Finset.range (m + 1) = insert m (Finset.range m) := Finset.range_add_one
    rw [h_range]
    rw [Finset.filter_insert]
    split
    · rename_i hz
      rw [Finset.card_insert_of_notMem]
      · rw [ih]
      · intro h_mem
        have h_lt : m < m := by
          have h_mem2 : m ∈ Finset.range m := Finset.mem_filter.mp h_mem |>.1
          exact Finset.mem_range.mp h_mem2
        exact Nat.lt_irrefl m h_lt
    · rename_i hz
      simp [ih]

}

/-- 
If two different indices are both followed by a zero, their values must be strictly distinct.
-/
lemma zero_predecessors_inj {i j : ℕ} (hi : vanEckNthTerm (i + 1) = 0) 
    (hj : vanEckNthTerm (j + 1) = 0) (hneq : i ≠ j) : vanEckNthTerm i ≠ vanEckNthTerm j := by {
  cases i
  case zero =>
    cases j
    case zero => contradiction
    case succ j =>
      have hj_iff := (vanEck_mth_term_eq_zero_iff_prev_term_new j).mp hj
      have h_eval := hj_iff 0 (Nat.zero_lt_succ j)
      exact h_eval
  case succ i =>
    cases j
    case zero =>
      have hi_iff := (vanEck_mth_term_eq_zero_iff_prev_term_new i).mp hi
      have h_eval := hi_iff 0 (Nat.zero_lt_succ i)
      exact h_eval.symm
    case succ j =>
      have hi_iff := (vanEck_mth_term_eq_zero_iff_prev_term_new i).mp hi
      have hj_iff := (vanEck_mth_term_eq_zero_iff_prev_term_new j).mp hj
      rcases Nat.lt_trichotomy (i + 1) (j + 1) with hlt | heq | hgt
      · have h_eval := hj_iff (i + 1) hlt
        exact h_eval
      · exfalso
        have heq2 : i = j := Nat.succ.inj heq
        exact hneq (congrArg Nat.succ heq2)
      · have h_eval := hi_iff (j + 1) hgt
        exact h_eval.symm

}

/-- 
Because the predecessors are injective, mapping the filter through the sequence preserves cardinality.
-/
lemma zero_predecessors_card (m : ℕ) : 
    ((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)).card = 
    (((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)).image vanEckNthTerm).card := by {
  have h_inj : Set.InjOn vanEckNthTerm ((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)) := by
    intro i hi j hj h_eq
    have hi_mem := Finset.mem_filter.mp hi
    have hj_mem := Finset.mem_filter.mp hj
    by_contra h_neq
    have h_inj_res := zero_predecessors_inj hi_mem.2 hj_mem.2 h_neq
    exact h_inj_res h_eq
  exact (Finset.card_image_of_injOn h_inj).symm

}

/-- 
Any element drawn from the predecessor image is bounded by our global max limit v.
-/
lemma zero_predecessors_bounded (m n v : ℕ) (h_le : m ≤ n) (h_bound : is_bound n v) : 
    ∀ x ∈ ((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)).image vanEckNthTerm, x ≤ v := by {
  intro x hx
  have h_mem := Finset.mem_image.mp hx
  rcases h_mem with ⟨i, hi, heq⟩
  have h_range := Finset.mem_filter.mp hi |>.1
  have h_lt := Finset.mem_range.mp h_range
  have h_i_le_n : i ≤ n := Nat.le_trans (Nat.le_of_lt h_lt) h_le
  rw [← heq]
  exact h_bound i h_i_le_n

}

/-- 
A basic Finset principle: A set of natural numbers bounded by v has size at most v + 1.
-/
lemma subset_range_card (S : Finset ℕ) (v : ℕ) (h_bound : ∀ x ∈ S, x ≤ v) : S.card ≤ v + 1 := by {
  have h_sub : S ⊆ Finset.range (v + 1) := by
    intro x hx
    have hx_le := h_bound x hx
    exact Finset.mem_range.mpr (Nat.lt_succ_of_le hx_le)
  have h_card := Finset.card_le_card h_sub
  have h_range_card : (Finset.range (v + 1)).card = v + 1 := Finset.card_range (v + 1)
  rw [h_range_card] at h_card
  exact h_card

}

/-- 
Lemma 1: The number of zeros is bounded by v + 2.
Proof Idea: Each zero (after the first) corresponds to a new, distinct number 
in the sequence. Since all numbers are ≤ v, there are at most v + 1 such numbers.
Hence zerosCount m ≤ v + 2.
-/
lemma zerosCount_le_bound (m n v : ℕ) (h_le : m ≤ n) (h_bound : is_bound n v) :
    zerosCount m ≤ v + 2 := by {
  -- We establish the structural equivalence of our zeros count to the filter cardinality.
  have h_count := zerosCount_eq_card m
  -- We establish the cardinality of the mapped image set exactly matches the filter.
  have h_img := zero_predecessors_card m
  -- We extract our bounded sequence property localized to the image elements.
  have h_bnd := zero_predecessors_bounded m n v h_le h_bound
  -- We bind our bounding parameter limit to the finite set size principle natively.
  have h_size := subset_range_card (((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)).image vanEckNthTerm) v h_bnd
  -- We substitute the cardinality equivalence to bind our count variable.
  rw [← h_img] at h_size
  -- We algebraically apply the additive bounds across our integer limits.
  have h_add : ((Finset.range m).filter (fun i => vanEckNthTerm (i + 1) = 0)).card + 1 ≤ v + 1 + 1 := Nat.add_le_add_right h_size 1
  -- We natively rewrite the count equivalence perfectly.
  rw [← h_count] at h_add
  -- We close the bound natively.
  exact h_add

}

lemma matchSearch_zero_eq_dist (m : ℕ) (hz : vanEckNthTerm (m + 1) = 0) :
    ∀ n ≤ m + 1, matchSearch (vanEck (m + 1)) n = if n = 0 then 0 else m + 1 - lastZero (n - 1) := by {
  intro n
  induction n with
  | zero =>
    intro _
    rw [ms_zero]
    exact rfl
  | succ k ih =>
    intro h_le
    have h_le_k : k ≤ m + 1 := Nat.le_trans (Nat.le_succ _) h_le
    have ih_k := ih h_le_k
    have h_len : (vanEck (m + 1)).length - 1 = m + 1 := by
      rw [vanEckLength, Nat.add_sub_cancel]
    have h_term_m1 : listNth (vanEck (m + 1)) ((vanEck (m + 1)).length - 1) = 0 := by
      rw [h_len]
      have hd : listNth (vanEck (m + 1)) (m + 1) = vanEckNthTerm (m + 1) := by
        exact (VanEck_deterministic (m + 1) (m + 1) (Nat.le_refl _)).symm
      rw [hd]
      exact hz
    have h_if_simp : (if k + 1 = 0 then 0 else m + 1 - lastZero (k + 1 - 1)) = m + 1 - lastZero k := by
      have hk_neq : k + 1 ≠ 0 := Nat.succ_ne_zero k
      rw [if_neg hk_neq, Nat.add_sub_cancel]
    rw [h_if_simp]
    by_cases h_ak : vanEckNthTerm k = 0
    · have h_ak_list : listNth (vanEck (m + 1)) k = 0 := by
        have hd : listNth (vanEck k) k = listNth (vanEck (m + 1)) k := (VanEck_deterministic (m + 1) k h_le_k).symm
        unfold vanEckNthTerm at h_ak
        rw [← hd]
        exact h_ak
      have h_pos : listNth (vanEck (m + 1)) ((vanEck (m + 1)).length - 1) = listNth (vanEck (m + 1)) k := by
        rw [h_term_m1, h_ak_list]
      rw [ms_succ_ifpos (vanEck (m + 1)) k h_pos]
      rw [h_len]
      have hl : lastZero k = k := by
        cases k with
        | zero => rfl
        | succ k' => rw [lastZero]; rw [if_pos h_ak]
      rw [hl]
    · have h_ak_list : listNth (vanEck (m + 1)) k ≠ 0 := by
        have hd : listNth (vanEck k) k = listNth (vanEck (m + 1)) k := (VanEck_deterministic (m + 1) k h_le_k).symm
        unfold vanEckNthTerm at h_ak
        rw [← hd]
        exact h_ak
      have h_neg : listNth (vanEck (m + 1)) ((vanEck (m + 1)).length - 1) ≠ listNth (vanEck (m + 1)) k := by
        rw [h_term_m1]
        exact Ne.symm h_ak_list
      rw [ms_succ_ifneg (vanEck (m + 1)) k h_neg]
      have hk0 : k ≠ 0 := by
        intro hk0_eq
        rw [hk0_eq] at h_ak
        have h0 : vanEckNthTerm 0 = 0 := vanEck_head_eq_zero 0
        exact h_ak h0
      have hl : lastZero k = lastZero (k - 1) := by
        cases k with
        | zero => contradiction
        | succ k' => 
          have hsub : k' + 1 - 1 = k' := rfl
          rw [hsub]
          rw [lastZero]
          rw [if_neg h_ak]
      rw [hl]
      have ih_simp : matchSearch (vanEck (m + 1)) k = m + 1 - lastZero (k - 1) := by
        have ih_eval := ih_k
        rw [if_neg hk0] at ih_eval
        exact ih_eval
      exact ih_simp

}

/-- 
The element directly following a zero represents the distance to the previous zero natively.
-/
lemma vanEck_distance_to_prev_zero (m : ℕ) (hz : vanEckNthTerm (m + 1) = 0) :
    vanEckNthTerm (m + 2) = m + 1 - lastZero m := by {
  have hm := vanEck_term_is_matchSearch (m + 2) (Nat.zero_lt_succ (m + 1))
  have h_sub : m + 2 - 1 = m + 1 := rfl
  rw [h_sub] at hm
  rw [hm]
  have h_eval := matchSearch_zero_eq_dist m hz (m + 1) (Nat.le_refl _)
  have h_neq : m + 1 ≠ 0 := Nat.succ_ne_zero m
  rw [if_neg h_neq] at h_eval
  have h_sub2 : m + 1 - 1 = m := rfl
  rw [h_sub2] at h_eval
  exact h_eval


}

/-- 
Every sequence fundamentally starts with at least one zero at the index 0.
-/
lemma zerosCount_pos (m : ℕ) : zerosCount m ≥ 1 := by {
  -- We proceed by structural induction on m.
  induction m with
  | zero =>
    -- Base case natively evaluates to 1.
    exact Nat.le_refl 1
  | succ m ih =>
    -- Unfold the definition for the next step.
    unfold zerosCount
    -- Branch on the if condition.
    split
    · -- The count strictly increments, keeping it positive.
      exact Nat.le_trans ih (Nat.le_add_right _ _)
    · -- The count remains structurally identical.
      exact ih

}

/-- 
Lemma 2: The index of the last zero is bounded by (zerosCount m - 1) * v.
Proof Idea: The distance between any two consecutive zeros is a term in the sequence, 
which is bounded by v. Summing these gaps telescopes to the last zero index.
-/
lemma lastZero_le_gaps (m v : ℕ) (h_bound : ∀ i ≤ m + 1, vanEckNthTerm i ≤ v) :
    lastZero m ≤ (zerosCount m - 1) * v := by {
  -- We proceed by mathematical induction on the upper bound m.
  induction m with
  | zero =>
    -- We unfold the definition of the last zero index.
    unfold lastZero
    -- We unfold the count of zeroes.
    unfold zerosCount
    -- We state the trivial natural number property.
    have h_sub : 1 - 1 = 0 := rfl
    -- We apply the property to simplify the bound.
    rw [h_sub]
    -- We close the base case trivially.
    exact Nat.zero_le (0 * v)
  | succ m ih =>
    -- We branch on whether the current element is a zero.
    by_cases hz : vanEckNthTerm (m + 1) = 0
    · -- We unfold the last zero index.
      unfold lastZero
      -- We rewrite utilizing our positive zero branch.
      rw [if_pos hz]
      -- We unfold the zeroes count.
      unfold zerosCount
      -- We rewrite utilizing our positive zero branch.
      rw [if_pos hz]
      -- We simplify the addition and subtraction structurally.
      have hs : zerosCount m + 1 - 1 = zerosCount m := Nat.add_sub_cancel (zerosCount m) 1
      -- We apply the simplification natively.
      rw [hs]
      -- We establish our bounded property scoped purely to m.
      have h_bound_m : ∀ i ≤ m + 1, vanEckNthTerm i ≤ v := fun i hi => h_bound i (Nat.le_trans hi (Nat.le_succ _))
      -- We extract the inductive hypothesis safely.
      have h_ih := ih h_bound_m
      -- We invoke our distance sequence lemma.
      have hd := vanEck_distance_to_prev_zero m hz
      -- We extract the maximal bound strictly applied to the gap element.
      have h_val := h_bound (m + 2) (Nat.le_refl _)
      -- We rewrite the distance evaluation into the bounded property.
      rw [hd] at h_val
      -- We algebraically translate the subtraction into additive bounds natively.
      have h_add : m + 1 ≤ v + lastZero m := Nat.le_add_of_sub_le h_val
      -- We factor out the multiplier mathematically.
      have h_mul : v + (zerosCount m - 1) * v = (1 + (zerosCount m - 1)) * v := by
        rw [Nat.add_mul, Nat.one_mul]
      -- We simplify the additive constant natively.
      have h_sub_add : 1 + (zerosCount m - 1) = zerosCount m := by
        have h_pos := zerosCount_pos m
        rw [Nat.add_comm]
        exact Nat.sub_add_cancel h_pos
      -- We lock the structural equation.
      rw [h_sub_add] at h_mul
      -- We enforce the additive bound upon the inductive hypothesis.
      have h_trans : v + lastZero m ≤ v + (zerosCount m - 1) * v := Nat.add_le_add_left h_ih v
      -- We rewrite the evaluation into the boundary comparison.
      rw [h_mul] at h_trans
      -- We close the branch via transitivity.
      exact Nat.le_trans h_add h_trans
    · -- We unfold the last zero index.
      unfold lastZero
      -- We rewrite utilizing our negative zero branch.
      rw [if_neg hz]
      -- We unfold the zeroes count.
      unfold zerosCount
      -- We rewrite utilizing our negative zero branch.
      rw [if_neg hz]
      -- We establish our bounded property scoped purely to m.
      have h_bound_m : ∀ i ≤ m + 1, vanEckNthTerm i ≤ v := fun i hi => h_bound i (Nat.le_trans hi (Nat.le_succ _))
      -- We close the branch perfectly with our inductive hypothesis.
      exact ih h_bound_m

}

lemma listMax_mem {L : List ℕ} (h : L ≠ []) : listMax L ∈ L := by {
  induction L with
  | nil => contradiction
  | cons x xs ih =>
    unfold listMax
    by_cases hxs : xs = []
    · rw [hxs]
      unfold listMax
      have hmax : max x 0 = x := Nat.max_zero x
      rw [hmax]
      exact List.Mem.head _
    · have h_max := max_choice x (listMax xs)
      cases h_max with
      | inl h1 =>
        rw [h1]
        exact List.Mem.head _
      | inr h2 =>
        rw [h2]
        exact List.Mem.tail _ (ih hxs)

}

lemma vanEckPrefixMax_mem (n : ℕ) : ∃ m ≤ n, vanEckNthTerm m = vanEckPrefixMax n := by {
  have h_len : (vanEck n).length = n + 1 := vanEckLength n
  have h_not_nil : vanEck n ≠ [] := by
    intro hc
    have h_len2 : (vanEck n).length = 0 := by rw [hc]; rfl
    rw [h_len] at h_len2
    contradiction
  have h_mem := listMax_mem h_not_nil
  unfold vanEckPrefixMax at h_mem
  have h_ex := mem_listNth h_mem
  rcases h_ex with ⟨k, hk, hk_eq⟩
  have h_k_le : k ≤ n := by
    rw [h_len] at hk
    exact Nat.le_of_lt_succ hk
  have h_term := VanEck_deterministic n k h_k_le
  use k
  constructor
  · exact h_k_le
  · unfold vanEckNthTerm
    rw [← h_term]
    exact hk_eq.symm

}

/-- 
For any n where a(n) = 0, there exists a term a(m) (with m ≤ n + 1)
that is at least roughly sqrt(n). We express this purely in ℕ as m^2 bounds.
-/
theorem vanEck_limsup_bound (n : ℕ) (hn : vanEckNthTerm n = 0) (hn_pos : n > 0) :
    ∃ m ≤ n + 1, (vanEckNthTerm m * vanEckNthTerm m + 2 * vanEckNthTerm m + 1 ≥ n) ∧ 
                 (vanEckNthTerm m * vanEckNthTerm m + 2 * vanEckNthTerm m + 1 ≥ m) := by {
  let v := vanEckPrefixMax (n + 1)
  have h_bound_all : ∀ i ≤ n + 1, vanEckNthTerm i ≤ v := fun i hi => vanEckNthTerm_le_prefixMax (n + 1) i hi
  have h_zc : zerosCount n ≤ v + 2 := zerosCount_le_bound n (n+1) v (Nat.le_succ n) h_bound_all
  have h_lz : lastZero n ≤ (zerosCount n - 1) * v := lastZero_le_gaps n v h_bound_all
  have h_lz_eq : lastZero n = n := by
    cases n with
    | zero => contradiction
    | succ n' =>
      rw [lastZero]
      rw [if_pos hn]
  rw [h_lz_eq] at h_lz
  have h_zc_sub : zerosCount n - 1 ≤ v + 1 := by
    exact Nat.sub_le_of_le_add (by
      have h1 : zerosCount n ≤ v + 2 := h_zc
      exact h1
    )
  have h_mul : (zerosCount n - 1) * v ≤ (v + 1) * v := Nat.mul_le_mul_right v h_zc_sub
  have h_n_le : n ≤ (v + 1) * v := Nat.le_trans h_lz h_mul
  have h_sq : (v + 1) * v ≤ v * v + 2 * v + 1 := by nlinarith
  have h_n_le_sq : n ≤ v * v + 2 * v + 1 := Nat.le_trans h_n_le h_sq
  
  have h_ex := vanEckPrefixMax_mem (n + 1)
  rcases h_ex with ⟨m, hm_le, hm_eq⟩
  use m
  constructor
  · exact hm_le
  · constructor
    · rw [hm_eq]
      exact h_n_le_sq
    · rw [hm_eq]
      have h_calc : m ≤ v * v + 2 * v + 1 := by nlinarith
      exact h_calc

}

/-- The main theorem concluding limsup a(n)/sqrt(n) >= 1. -/
theorem vanEck_limsup_ge_sqrt :
    ∀ N, ∃ m ≥ N, vanEckNthTerm m * vanEckNthTerm m + 2 * vanEckNthTerm m + 1 ≥ m := by {
  -- We introduce our arbitrary lower bound N for the index m.
  intro N
  -- We calculate the square-like expansion for our search boundary.
  let N_sq := N * N + 2 * N + 1
  -- We rely on the infinite zeroes theorem to find a zero past our boundary.
  have h_zero := infinite_zeros_vanEck N_sq
  -- We extract the specific index n and the guarantees of it being a zero.
  rcases h_zero with ⟨n, hn_gt, hn_zero⟩
  -- We establish that n is strictly positive natively.
  have hn_pos : n > 0 := Nat.lt_of_le_of_lt (Nat.zero_le N_sq) hn_gt
  -- We invoke our core bounding lemma to find our target m up to n + 1.
  have h_bound := vanEck_limsup_bound n hn_zero hn_pos
  -- We destruct the bound to access the index m and the squared inequality.
  rcases h_bound with ⟨m, hm_le, hm_ineq_n, hm_ineq_m⟩
  -- We provide m as the witness for our existential claim.
  use m
  -- We split our goal into verifying m >= N and the mathematical inequality.
  constructor
  · -- We prove m >= N using strictly structural relations avoiding omega.
    have h_a_le_m : vanEckNthTerm m ≤ m := vanEckNthTerm_le_n m
    have h1 : m * m + 2 * m + 1 ≥ N * N + 2 * N + 2 := by
      calc m * m + 2 * m + 1 ≥ vanEckNthTerm m * vanEckNthTerm m + 2 * vanEckNthTerm m + 1 := by nlinarith
        _ ≥ n := hm_ineq_n
        _ ≥ N_sq + 1 := hn_gt
        _ = N * N + 2 * N + 1 + 1 := rfl
        _ = N * N + 2 * N + 2 := rfl
    nlinarith
  · -- We prove the sequence element squared bounds m natively.
    -- We bind the upper limit algebraically against n natively.
    exact hm_ineq_m
}
