import VanEck.Basic

/-- Extracting the explicit nth term directly from the VanEck generated sequence. -/
def vanEckNthTerm (n : ℕ) : ℕ := listNth (vanEck n) n

example : vanEckNthTerm 0 = 0 := by rfl

/-- The length of the first n iterations of the VanEck sequence is strictly n+1. -/
lemma vanEckLength (n : ℕ) : (vanEck n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n IH =>
    unfold vanEck
    rw [List.length_append]
    rw [IH]
    rfl

/-- The backward search trace natively bounded by n+1 iterating strictly locally. -/
lemma matchSearch_le (n : ℕ) : matchSearch (vanEck n) n ≤ n + 1 := by
  have H := matchSearch_le_length (vanEck n) n
  rw [vanEckLength n] at H
  exact H

/-- Recursively prove extraction explicitly targeting the directly appended back index. -/
lemma listNth_last (a : ℕ) (L : List ℕ) : listNth (L ++ [a]) L.length = a := by
  induction L with
  | nil => rfl
  | cons _ L IH => exact IH

/-- Central sequence trace theorem proving index scaling bounding limits exclusively natively. -/
theorem vanEckNthTerm_le_n (n : ℕ) : vanEckNthTerm n ≤ n := by
  cases n with
  | zero => exact Nat.zero_le 0
  | succ n =>
    unfold vanEckNthTerm
    unfold vanEck
    have hLen : (vanEck n).length = n + 1 := vanEckLength n
    rw [← hLen]
    rw [listNth_last]
    unfold vanEckNextTerm
    rw [hLen]
    have hSub : n + 1 - 1 = n := rfl
    rw [hSub]
    exact matchSearch_le n

variable {α : Type*} (p : α → Prop)

lemma logic1 (h : ∀ x, ¬ p x) : ¬ ∃ x, p x := by
  intro hyp
  rcases hyp with ⟨x, hx⟩
  specialize h x
  exact h hx

lemma logic2 (h : ¬ ∃ x, p x) : ∀ x, ¬ p x := by
  intro x
  change (∃ x, p x) → False at h
  intro h1
  apply h
  exact ⟨x, h1⟩

lemma logic3 (h : ¬ ∀ x, p x) : ∃ x, ¬ p x := by
  by_contra h_not
  apply h
  intro x
  by_contra h_px
  apply h_not
  exact ⟨x, h_px⟩

lemma logic4 (h : ∀ x, p x) : ¬ ∃ x, ¬ p x := by
  rintro ⟨x, hx⟩
  exact hx (h x)

lemma logic5 (h : ¬ (∀ x, ¬ (p x))) : ∃ x, p x := by
  by_contra h_not
  apply h
  intro x
  intro hx
  apply h_not
  exact ⟨x, hx⟩

lemma contrapositive {P Q : Prop} (h : P → Q) : ¬Q → ¬P := by
  intro hnq hp
  exact hnq (h hp)

lemma silly1 (m : ℕ) : m + 1 - m = 0 → False := by
  intro h
  have h1 : m + 1 - m = 1 := Nat.add_sub_cancel_left m 1
  rw [h1] at h
  contradiction

lemma splitting_le (c d : ℕ) : (c ≤ d) ↔ c < d ∨ c = d := by
  apply Iff.intro
  · intro h
    exact Nat.lt_or_eq_of_le h
  · intro h
    rcases h with hlt | heq
    · exact Nat.le_of_lt hlt
    · exact Nat.le_of_eq heq

-- Manabu's lemmas
lemma list_nth_zero (n : ℕ) : listNth [] n = 0 := rfl
lemma list_nth_l_zero (a : ℕ) (l : List ℕ) : listNth (a::l) 0 = a := rfl
lemma list_nth_l_succ (a : ℕ) (l : List ℕ) (n : ℕ) : listNth (a::l) (n+1) = listNth l n := rfl
lemma ms_zero (L : List ℕ) : matchSearch L 0 = 0 := rfl
lemma ms_succ_ifpos (L : List ℕ) (n : ℕ) (Hpos : listNth L (L.length - 1) = listNth L n) :
    matchSearch L (n + 1) = (L.length - 1) - n := matchSearch_ite_tt L n Hpos
lemma ms_succ_ifneg (L : List ℕ) (n : ℕ) (Hneg : listNth L (L.length - 1) ≠ listNth L n) :
    matchSearch L (n + 1) = matchSearch L n := matchSearch_ite_ff L n Hneg
lemma ms_or (L : List ℕ) (n : ℕ) :
    (matchSearch L (n + 1) = (L.length - 1) - n) ∨ (matchSearch L (n + 1) = matchSearch L n) := by
  by_cases H : listNth L (L.length - 1) = listNth L n
  · exact Or.inl (ms_succ_ifpos L n H)
  · exact Or.inr (ms_succ_ifneg L n H)

-- VanEck zeroes Logic
lemma listNth_append_zero (A B : List ℕ) : A.length ≥ 1 → listNth (A ++ B) 0 = listNth A 0 := by
  intro h
  cases A with
  | nil => exfalso; exact Nat.not_lt_zero 0 h
  | cons a A' => rfl

lemma vanEck_eq_head_plus_tail (n : ℕ) : ∃ x : ℕ, vanEck n = x :: listNthTail (vanEck n) 0 := by
  apply list_length_ge_one_has_head
  rw [vanEckLength]
  exact Nat.le_add_left 1 n

lemma list_nth_VanEck_zero_eq_zero (n : ℕ) : listNth (vanEck n) 0 = 0 := by
  induction n with
  | zero => rfl
  | succ n IH =>
    unfold vanEck
    rw [listNth_append_zero]
    · exact IH
    · rw [vanEckLength]
      exact Nat.le_add_left 1 n

lemma vanEck_head_eq_zero (n : ℕ) : listNth (vanEck n) 0 = 0 :=
  list_nth_VanEck_zero_eq_zero n

-- Deterministic Determinism Lemmas (Block 5)
lemma list_nth_match_prepend (b n : ℕ) (L : List ℕ) : n ≥ 1 → listNth (b::L) n = listNth L (n - 1) := by
  intro h
  cases n with
  | zero => exfalso; exact Nat.not_lt_zero 0 h
  | succ m => rfl

lemma list_nth_eq_of_append_past_n (a n : ℕ) :
    ∀ L : List ℕ, L.length ≥ n + 1 → listNth (L ++ [a]) n = listNth L n := by
  induction n with
  | zero =>
    intro L h
    cases L with
    | nil =>
      exfalso
      have h0 : ([] : List ℕ).length = 0 := rfl
      rw [h0] at h
      exact Nat.not_succ_le_zero 0 h
    | cons x L' => rfl
  | succ n hn =>
    intro L h
    cases L with
    | nil =>
      exfalso
      have h0 : ([] : List ℕ).length = 0 := rfl
      rw [h0] at h
      exact Nat.not_succ_le_zero (n + 1) h
    | cons b L' =>
      unfold listNth
      have h2 : (b :: L').length = L'.length + 1 := rfl
      rw [h2] at h
      have h3 : L'.length ≥ n + 1 := Nat.le_of_succ_le_succ h
      exact hn L' h3

lemma list_nth_VE_eq_VE_next (n : ℕ) :
    listNth (vanEck (n + 1)) (n + 1) = vanEckNextTerm (vanEck n) := by
  have h_unfold : vanEck (n + 1) = vanEck n ++ [vanEckNextTerm (vanEck n)] := rfl
  rw [h_unfold]
  have h1 : listNth (vanEck n ++ [vanEckNextTerm (vanEck n)]) (vanEck n).length = vanEckNextTerm (vanEck n) := listNth_last _ _
  rw [vanEckLength] at h1
  exact h1

lemma list_nth_VE_eq_ms (n : ℕ) :
    listNth (vanEck (n + 1)) (n + 1) = matchSearch (vanEck n) n := by
  rw [list_nth_VE_eq_VE_next]
  unfold vanEckNextTerm
  rw [vanEckLength]
  rfl

lemma VanEck_deterministic_step (d m : ℕ) :
    listNth (vanEck d) d = listNth (vanEck (d + m)) d := by
  induction m with
  | zero => rfl
  | succ m hm =>
    have h1 : d + (m + 1) = d + m + 1 := by rw [Nat.add_assoc, Nat.add_comm m 1, ← Nat.add_assoc]
    rw [h1]
    have h_unfold : vanEck (d + m + 1) = vanEck (d + m) ++ [vanEckNextTerm (vanEck (d + m))] := rfl
    rw [h_unfold]
    have h2 : (vanEck (d + m)).length = d + m + 1 := vanEckLength _
    have h3 : (vanEck (d + m)).length ≥ d + 1 := by
      rw [h2]
      exact Nat.add_le_add_right (Nat.le_add_right d m) 1
    have h4 : listNth (vanEck (d + m) ++ [vanEckNextTerm (vanEck (d + m))]) d = listNth (vanEck (d + m)) d :=
      list_nth_eq_of_append_past_n (vanEckNextTerm (vanEck (d + m))) d _ h3
    rw [h4]
    exact hm

lemma VanEck_deterministic (n d : ℕ) :
    n ≥ d → listNth (vanEck n) d = listNth (vanEck d) d := by
  intro h
  have h1 : ∃ m : ℕ, n = d + m := Nat.exists_eq_add_of_le h
  rcases h1 with ⟨m, hm⟩
  rw [hm]
  exact (VanEck_deterministic_step d m).symm

lemma list_nth_VanEck_one_eq_zero (n : ℕ) :
    n ≥ 1 → listNth (vanEck n) 1 = 0 := by
  intro h
  have hb : listNth (vanEck 1) 1 = 0 := rfl
  rw [VanEck_deterministic n 1 h]
  exact hb

-- After starting, the nth term is zero iff a new number is found.
lemma vanEck_mth_term_eq_zero_iff_prev_term_new (m : ℕ) :
    vanEckNthTerm (m + 2) = 0 ↔ (∀ n < m + 1, vanEckNthTerm n ≠ vanEckNthTerm (m + 1)) := by
  apply Iff.intro
  · intro h
    unfold vanEckNthTerm at h
    have h_ms : listNth (vanEck (m + 2)) (m + 2) = matchSearch (vanEck (m + 1)) (m + 1) := list_nth_VE_eq_ms (m + 1)
    rw [h_ms] at h
    intro n hn
    by_contra hc
    unfold vanEckNthTerm at hc
    have h1 : listNth (vanEck n) n = listNth (vanEck (m + 1)) n := by
      have hle : m + 1 ≥ n := Nat.le_of_lt hn
      exact (VanEck_deterministic (m+1) n hle).symm
    
    have h0 : matchSearch (vanEck (m + 1)) (n + 1) ≥ 1 := by
      have H_if : listNth (vanEck (m+1)) ((vanEck (m+1)).length - 1) = listNth (vanEck (m+1)) n := by
        rw [vanEckLength (m+1)]
        have h_len_sub : m + 2 - 1 = m + 1 := rfl
        rw [h_len_sub]
        rw [← h1]
        exact hc.symm
      have h_eval : matchSearch (vanEck (m+1)) (n+1) = (vanEck (m+1)).length - 1 - n := matchSearch_ite_tt (vanEck (m+1)) n H_if
      rw [h_eval]
      rw [vanEckLength]
      have h_sub : m + 2 - 1 = m + 1 := rfl
      rw [h_sub]
      exact obv17 m n hn

    by_cases he : n = m
    · rw [he] at h0
      rw [h] at h0
      exfalso
      exact Nat.not_lt_zero 0 h0
    · have h2 : n < m := by
        have hle : n ≤ m := Nat.le_of_lt_succ hn
        have hor : n < m ∨ n = m := (splitting_le n m).mp hle
        cases hor with
        | inl hlt => exact hlt
        | inr heq => exfalso; exact he heq

      have h00 : matchSearch (vanEck (m+1)) (n+1) ≠ 0 := obv16 _ h0
      have h_index : (vanEck (m+1)).length - 1 - (m - n) = n + 1 := by
        rw [vanEckLength]
        have h_sub : m + 2 - 1 = m + 1 := rfl
        rw [h_sub]
        exact obv20 m n h2
      
      have h_trigger : matchSearch (vanEck (m+1)) ((vanEck (m+1)).length - 1 - (m - n)) ≠ 0 := by
        rw [h_index]
        exact h00
      
      have h_res : matchSearch (vanEck (m+1)) ((vanEck (m+1)).length - 1) ≠ 0 :=
        match_search_nonzero_after_match_before_end (m - n) (vanEck (m+1)) h_trigger
      
      have h_len_eval : (vanEck (m+1)).length - 1 = m + 1 := by
        rw [vanEckLength]
        rfl
      rw [h_len_eval] at h_res
      exact h_res h

  · unfold vanEckNthTerm
    intro hn
    have h_ms : listNth (vanEck (m + 2)) (m + 2) = matchSearch (vanEck (m + 1)) (m + 1) := list_nth_VE_eq_ms (m + 1)
    rw [h_ms]
    have hnomatch : ∀ x ≤ m + 1, matchSearch (vanEck (m + 1)) x = 0 := by
      intro x
      induction x with
      | zero =>
        intro _
        exact ms_zero _
      | succ x hni =>
        intro hsuc
        have h_le : x ≤ m + 1 := Nat.le_of_succ_le hsuc
        have IH := hni h_le
        have Hneg : listNth (vanEck (m+1)) ((vanEck (m+1)).length - 1) ≠ listNth (vanEck (m+1)) x := by
          rw [vanEckLength]
          have h_sub : m + 2 - 1 = m + 1 := rfl
          rw [h_sub]
          have hsuc2 : x < m + 1 := Nat.lt_of_succ_le hsuc
          have hd : listNth (vanEck x) x = listNth (vanEck (m+1)) x := by
            have hle2 : m + 1 ≥ x := Nat.le_of_lt hsuc2
            exact (VanEck_deterministic (m+1) x hle2).symm
          rw [← hd]
          have hn_eval := hn x hsuc2
          unfold vanEckNthTerm at hn_eval
          exact Ne.symm hn_eval
        rw [matchSearch_ite_ff _ _ Hneg]
        exact IH
    exact hnomatch (m + 1) (Nat.le_refl _)

--Suppose there are not infinitely many zeros.
--Then from a certain point on, no new terms appear, 
--so the sequence is bounded and nonzero.
lemma bounded_if_tail_eq_nonzero (N : ℕ) : 
    (∀ m > N, vanEckNthTerm m ≠ 0) → (∃ B : ℕ, ∀ n : ℕ, vanEckNthTerm n < B) := by
  intro h
  sorry

theorem infinite_zeros_vanEck (N : ℕ) : ∃ m : ℕ, m > N ∧ vanEckNthTerm m = 0 := by
  by_contra Hyp
  have h1 : ∀ (m : ℕ), ¬ (m > N ∧ vanEckNthTerm m = 0) := by
    apply logic2; exact Hyp
  change (∃ m : ℕ, m > N ∧ vanEckNthTerm m = 0) → False at Hyp
  apply Hyp
  sorry
