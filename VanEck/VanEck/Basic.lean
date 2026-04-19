import Mathlib.Data.Nat.Basic
import Mathlib.Tactic

-- The goal of this code is to produce the VanEck sequence

variable (a b : ℕ)

lemma flip_le (c d : ℕ) : (c ≤ d) ↔ (d ≥ c) := by
  apply Iff.intro
  · intro h; exact h
  · intro h; exact h

lemma splitting_ge (c d : ℕ) : (c ≥ d) ↔ d < c ∨ d = c := by
  apply Iff.intro
  · intro h
    exact Nat.lt_or_eq_of_le h
  · intro h
    rcases h with hlt | heq
    · exact Nat.le_of_lt hlt
    · exact Nat.le_of_eq heq

lemma obv : a ≥ 1 → a - 1 + 1 = a := by
  intro h
  exact Nat.sub_add_cancel h

lemma obv2 : a ≥ 2 → a - 2 + 1 = a - 1 := by
  intro h
  have h1 : a - 2 + 1 = a - (1 + 1) + 1 := by rfl
  have h2 : a - (1 + 1) = a - 1 - 1 := by rfl
  rw [h1, h2]
  apply obv
  exact Nat.le_sub_of_add_le h

lemma obv3 : a + 1 ≤ b → b - (a + 1) + 1 = b - a := by
  intro h
  have h_sub : b - (a + 1) = b - a - 1 := rfl
  rw [h_sub]
  have h_pos : 0 < b - a := Nat.sub_pos_of_lt h
  exact Nat.sub_add_cancel h_pos

lemma obv4 : a ≤ b → a - b = 0 := by
  intro h
  exact Nat.sub_eq_zero_of_le h

lemma obv5 : a ≥ 1 → a - (b + 1) < a := by
  intro h
  have h1 : a - b ≤ a := Nat.sub_le a b
  have h2 : a - (b + 1) = a - b - 1 := rfl
  rw [h2]
  have h3 : a - 1 < a := Nat.sub_lt h (by decide)
  have h4 : a - b - 1 ≤ a - 1 := Nat.sub_le_sub_right h1 1
  exact Nat.lt_of_le_of_lt h4 h3

lemma obv6 : a - 1 - (a - 1 - (b + 1)) ≠ 0 ∨ a - 1 = 0 := by
  by_cases hn : a - 1 = 0
  · exact Or.inr hn
  · exact Or.inl (by
      have h1 : a - 1 ≥ 1 := Nat.pos_of_ne_zero hn
      have h2 : a - 1 - (b + 1) < a - 1 := obv5 (a - 1) b h1
      exact Nat.ne_of_gt (Nat.sub_pos_of_lt h2))

lemma obv7 : a < b ↔ b > a := by
  exact Iff.rfl

lemma obv7a : a ≤ b ↔ b ≥ a := by
  exact Iff.rfl

lemma obv8 (m n : ℕ) : m ≤ n ↔ n - m + m = n := by
  apply Iff.intro
  · exact Nat.sub_add_cancel
  · intro h
    have h_le : m ≤ n - m + m := Nat.le_add_left m (n - m)
    rw [h] at h_le
    exact h_le

lemma obv9 (L : List ℕ) (n : ℕ) : L.length - n - 2 ≥ 2
  → L.length - n - 2 = L.length - (n + 1) - 2 + 1 := by
  intro h
  have h1 : L.length - (n + 1) = L.length - n - 1 := rfl
  rw [h1]
  have h2 : L.length - n - 1 - 2 = L.length - n - 2 - 1 := by
    rw [Nat.sub_right_comm (L.length - n) 1 2]
  rw [h2]
  have h_one_le : 1 ≤ L.length - n - 2 := Nat.le_trans (by decide) h
  exact (Nat.sub_add_cancel h_one_le).symm

lemma obv10 (L : List ℕ) (n : ℕ) : L.length - n - 2 ≥ 1
  ↔ L.length - n - 2 = L.length - (n + 1) - 2 + 1 := by
  apply Iff.intro
  · intro h
    have h1 : L.length - (n + 1) = L.length - n - 1 := rfl
    rw [h1]
    have h2 : L.length - n - 1 - 2 = L.length - n - 2 - 1 := by
      rw [Nat.sub_right_comm (L.length - n) 1 2]
    rw [h2]
    exact (Nat.sub_add_cancel h).symm
  · intro h
    rw [h]
    exact Nat.le_add_left 1 (L.length - (n + 1) - 2)

lemma obv11 (L : List ℕ) (n : ℕ) : 0 < L.length - n - 2 → 1 ≤ L.length - n - 2 := by
  intro h
  exact h

lemma obv12 (L : List ℕ) (n : ℕ) : L.length - 1 - n - 1 = L.length - n - 1 - 1 := by
  rw [Nat.sub_right_comm (L.length) 1 n]

lemma obv13 (L : List ℕ) (n : ℕ) (hyp : L.length ≥ 2)
  (hyp2 : n + 1 < L.length - 1) : L.length - 1 - (L.length - 2 - (n + 1)) ≠ 0 := by
  have h1 : L.length - 2 - (n + 1) < L.length - 1 := by
    have hz : L.length - 2 - (n + 1) ≤ L.length - 2 := Nat.sub_le _ _
    have hz2 : L.length - 2 < L.length - 1 := by
      have hlen1 : 1 ≤ L.length - 1 := Nat.le_sub_of_add_le hyp
      have hlen2 : L.length - 2 = L.length - 1 - 1 := by rw [Nat.sub_sub]
      rw [hlen2]
      exact Nat.sub_lt hlen1 (by decide)
    exact Nat.lt_of_le_of_lt hz hz2
  exact Nat.ne_of_gt (Nat.sub_pos_of_lt h1)

lemma obv14 (L : List ℕ) (n : ℕ) : L.length - 2 - n = L.length - 1 - (n + 1) := by
  have h1 : L.length - 1 - (n + 1) = L.length - 1 - n - 1 := rfl
  rw [h1]
  rw [Nat.sub_right_comm (L.length - 1) n 1]
  have h2 : L.length - 1 - 1 = L.length - 2 := rfl
  rw [h2]

lemma obv15 : a ≠ 0 → a ≥ 1 := by
  intro h
  exact Nat.pos_of_ne_zero h

lemma obv16 : a ≥ 1 → a ≠ 0 := by
  intro h
  exact Nat.ne_of_gt h

lemma obv17 (m n : ℕ) : n < m + 1 → 1 ≤ m + 1 - n := by
  intro h
  exact Nat.sub_pos_of_lt h

lemma obv18 (m n : ℕ) : n ≤ m → m - (m - n) = n := by
  intro h
  exact Nat.sub_sub_self h

lemma obv19 : a ≤ b → (1 + b) - a = 1 + (b - a) := by
  intro h
  exact Nat.add_sub_assoc h 1

lemma obv20 (m n : ℕ) : n < m → m + 1 - (m - n) = n + 1 := by
  intro h
  have h1 : m + 1 - (m - n) = 1 + m - (m - n) := by rw [Nat.add_comm m 1]
  rw [h1]
  have h_le : m - n ≤ m := Nat.sub_le m n
  have h2 : 1 + m - (m - n) = 1 + (m - (m - n)) := obv19 (m - n) m h_le
  rw [h2]
  have h3 : m - (m - n) = n := obv18 m n (Nat.le_of_lt h)
  rw [h3]
  exact Nat.add_comm 1 n

lemma weird (L : List ℕ) (h : L.length ≥ 2) : L.length - 2 + 1 = L.length - 1 := by
  exact obv2 L.length h

/--
Function to extract the nth term of a list.
Note that the position count starts from 0 exactly.
-/
def listNth : List ℕ → ℕ → ℕ
  | [], _ => 0
  | x::_, 0 => x
  | _::xs, n+1 => listNth xs n

-- Here's a brief check: extracting the term at position 3 (0-based) from [1,2,3,4,5] gives 4.
example : listNth [1, 2, 3, 4, 5] 3 = 4 := by rfl

/--
This takes a list L and searches back from position n for a match to its final term.
It outputs the distance from the end; if no match is found, it safely outputs 0.
-/
def matchSearch : List ℕ → ℕ → ℕ
  | _, 0 => 0
  | L, n+1 => if listNth L (L.length - 1) = listNth L n
              then (L.length - 1) - n
              else matchSearch L n

/--
If the last term matches the term at position n,
then matchSearch at n+1 correctly returns the distance.
-/
lemma matchSearch_ite_tt (L : List ℕ) (n : ℕ) :
    listNth L (L.length - 1) = listNth L n →
    matchSearch L (n + 1) = (L.length - 1) - n := by
  intro H
  unfold matchSearch
  rw [if_pos H]

/--
If the last term does not match the term at position n,
then matchSearch at n+1 continues the search recursively at n.
-/
lemma matchSearch_ite_ff (L : List ℕ) (n : ℕ) :
    listNth L (L.length - 1) ≠ listNth L n →
    matchSearch L (n + 1) = matchSearch L n := by
  intro H
  conv => lhs; unfold matchSearch
  rw [if_neg H]

/--
The matchSearch function result is never greater than the length of the list.
This bounded sequence simplifies two separate Lean 3 lemmas into one clean unified induction.
-/
lemma matchSearch_le_length (L : List ℕ) (n : ℕ) :
    matchSearch L n ≤ L.length := by
  induction n with
  | zero =>
    unfold matchSearch
    exact Nat.zero_le _
  | succ n IH =>
    by_cases H : listNth L (L.length - 1) = listNth L n
    · rw [matchSearch_ite_tt L n H]
      exact Nat.le_trans (Nat.sub_le _ _) (Nat.sub_le _ _)
    · rw [matchSearch_ite_ff L n H]
      exact IH

lemma match_search_nonzero_after_match_before_end_base_case (n : ℕ) :
  ∀ L : List ℕ, (matchSearch L 0 ≠ 0) → (matchSearch L (L.length - 1) ≠ 0) := by
  intro L h
  exfalso
  exact h rfl

lemma match_search_nonzero_after_match_before_end (n : ℕ) :
  ∀ L : List ℕ, (matchSearch L (L.length - 1 - n) ≠ 0)
    → (matchSearch L (L.length - 1) ≠ 0) := by
  induction n with
  | zero =>
    intro L h
    exact h
  | succ n hn =>
    intro L h
    by_cases c1 : n + 1 ≤ L.length - 1
    · have h1 : L.length - 1 - (n + 1) + 1 = L.length - 1 - n := obv3 _ _ c1
      apply hn L
      rw [← h1]
      by_cases hpos : listNth L (L.length - 1) = listNth L (L.length - 1 - (n + 1))
      · rw [matchSearch_ite_tt L (L.length - 1 - (n + 1)) hpos]
        have h2 : L.length - 1 - (L.length - 1 - (n + 1)) ≠ 0 ∨ L.length - 1 = 0 := obv6 L.length n
        cases h2 with
        | inl h2n => exact h2n
        | inr h2e =>
          have h2e1 : L.length - 1 - (n + 1) = 0 := by rw [h2e, Nat.zero_sub]
          rw [h2e1] at h
          exfalso
          exact h rfl
      · rw [matchSearch_ite_ff L (L.length - 1 - (n + 1)) hpos]
        exact h
    · have c2 : L.length - 1 ≤ n := Nat.le_of_lt_succ (Nat.lt_of_not_ge c1)
      have hfalse : L.length - 1 - (n + 1) = 0 := obv4 _ _ (Nat.le_trans c2 (Nat.le_succ n))
      rw [hfalse] at h
      exfalso
      exact h rfl

lemma if_match_then_match_search_at_end_ge_1 (n : ℕ) (L : List ℕ) (hlen : L.length ≥ 2)
    (hn : n < L.length - 1) : (listNth L (L.length - 2 - n) = listNth L (L.length - 1))
    → matchSearch L (L.length - 1) ≥ 1 := by
  intro hyp
  induction n with
  | zero =>
    -- Base case n = 0.
    have hsucc : L.length - 1 = L.length - 2 + 1 := (weird L hlen).symm
    have heq : listNth L (L.length - 1) = listNth L (L.length - 2) := hyp.symm
    -- We evaluate matchSearch at L.length - 1 changed to L.length - 2 + 1 to find the match.
    have h_eval : matchSearch L (L.length - 2 + 1) = (L.length - 1) - (L.length - 2) := by
      exact matchSearch_ite_tt L (L.length - 2) heq
    rw [hsucc]
    rw [h_eval]
    have h_sub : L.length - 1 - (L.length - 2) = 1 := by
      rw [hsucc]
      exact Nat.add_sub_cancel_left (L.length - 2) 1
    exact Nat.le_of_eq h_sub.symm
  | succ n _ =>
    -- First, we establish that the target spot L.length - 2 - n is just one index
    -- ahead of L.length - 2 - (n + 1) using obv10.
    have hil0 : L.length - 2 - n = L.length - 2 - (n + 1) + 1 := by
      have h_lt : n + 1 < L.length - 1 := hn
      have h_pos : 0 < L.length - 1 - (n + 1) := Nat.sub_pos_of_lt h_lt
      have h_sub_eq : L.length - 1 - (n + 1) = L.length - (n + 1) - 1 := by rw [Nat.sub_right_comm (L.length) 1 (n + 1)]
      rw [h_sub_eq] at h_pos
      have h_sub2 : L.length - (n + 1) - 1 = L.length - n - 2 := by rw [Nat.sub_sub]; rfl
      rw [h_sub2] at h_pos
      have obv10_res := (obv10 L n).mp h_pos
      rw [Nat.sub_right_comm L.length n 2] at obv10_res
      rw [Nat.sub_right_comm L.length (n + 1) 2] at obv10_res
      exact obv10_res

    -- Now that we have `L.length - 2 - n = X + 1`, we can naturally construct the matchSearch if-statement natively without unfolding heavily.
    have hmatch : matchSearch L (L.length - 2 - n) = L.length - 1 - (L.length - 2 - (n + 1)) := by
      rw [hil0]
      have heq : listNth L (L.length - 1) = listNth L (L.length - 2 - (n + 1)) := hyp.symm
      exact matchSearch_ite_tt L (L.length - 2 - (n + 1)) heq

    -- Output distance is guaranteed non-zero by obv13 bounds testing.
    have hneq0 : L.length - 1 - (L.length - 2 - (n + 1)) ≠ 0 := by
      apply obv13 L n hlen hn

    -- Using the match location, we apply our previous backwards depth search hook verification
    have hmatch2 : matchSearch L (L.length - 1) ≠ 0 := by
      have hm3 : matchSearch L (L.length - 2 - n) ≠ 0 := by
        rw [hmatch]
        exact hneq0
      have h4 : L.length - 2 - n = L.length - 1 - (n + 1) := obv14 L n
      rw [h4] at hm3
      exact match_search_nonzero_after_match_before_end (n+1) L hm3

    -- Having proven matchSearch is not 0 natively, it must be at least 1 trivially.
    exact obv15 _ hmatch2

def listNthTail : List ℕ → ℕ → List ℕ
  | [], _ => []
  | _ :: X, 0 => X
  | _ :: X, n + 1 => listNthTail X n

def listNthHead : List ℕ → ℕ → List ℕ
  | [], _ => []
  | x :: _, 0 => [x]
  | x :: X, n + 1 => x :: listNthHead X n

lemma list_length_ge_one_has_head (L : List ℕ) :
  L.length ≥ 1 → ∃ x : ℕ, L = x :: listNthTail L 0 := by
  intro h
  cases L with
  | nil =>
    exfalso
    exact Nat.not_lt_zero 0 h
  | cons x _ =>
    unfold listNthTail
    exact ⟨x, rfl⟩

lemma list_nth_head_past_length_eq_list (n : ℕ) :
  ∀ L : List ℕ, L.length ≤ n → listNthHead L n = L := by
  induction n with
  | zero =>
    intro L h
    have h0 : L.length = 0 := Nat.eq_zero_of_le_zero h
    have h2 : L = [] := List.length_eq_zero_iff.mp h0
    rw [h2]
    rfl
  | succ n hn =>
    intro L h
    cases L with
    | nil => rfl
    | cons b L' =>
      unfold listNthHead
      have h2 : (b :: L').length = L'.length + 1 := rfl
      rw [h2] at h
      have h3 : L'.length ≤ n := Nat.le_of_succ_le_succ h
      rw [hn L' h3]

lemma list_nth_tail_minus_one (L : List ℕ) (n : ℕ) :
  listNth L (n + 1) = listNth (listNthTail L 0) n := by
  cases L with
  | nil => rfl
  | cons _ L' => rfl

lemma listNth_drop (d i : ℕ) : ∀ L : List ℕ, listNth (L.drop d) i = listNth L (d + i) := by
  induction d with
  | zero => intro L; rw [Nat.zero_add]; rfl
  | succ d hd =>
    intro L
    cases L with
    | nil =>
      have h1 : ([] : List ℕ).drop (d + 1) = [] := rfl
      rw [h1]
      rfl
    | cons x xs =>
      have h1 : (x :: xs).drop (d + 1) = xs.drop d := rfl
      rw [h1]
      have h2 : listNth (x :: xs) (d + 1 + i) = listNth xs (d + i) := by
      have hd1i : d + 1 + i = d + i + 1 := Nat.add_right_comm d 1 i
      rw [hd1i]
      rfl
    rw [h2]
    exact hd xs

lemma matchSearch_eq_dist (L : List ℕ) (start d : ℕ)
    (h_match : listNth L (L.length - 1) = listNth L start)
    (h_fail : ∀ k, 1 ≤ k → k ≤ d → listNth L (L.length - 1) ≠ listNth L (start + k)) :
    matchSearch L (start + d + 1) = L.length - 1 - start := by
  induction d with
  | zero =>
    have h1 : start + 0 + 1 = start + 1 := rfl
    rw [h1, matchSearch_ite_tt L start h_match]
  | succ d ih =>
    have h1 : start + (d + 1) + 1 = start + d + 1 + 1 := by omega
    rw [h1]
    have h_fail_succ := h_fail (d + 1) (by omega) (by omega)
    have heq : start + d + 1 = start + (d + 1) := by omega
    have h_neq : listNth L (L.length - 1) ≠ listNth L (start + d + 1) := by
      rw [heq]
      exact h_fail_succ
    rw [matchSearch_ite_ff L (start + d + 1) h_neq]
    apply ih
    intro k hk1 hkd
    have h_le : k ≤ d + 1 := by omega
    exact h_fail k hk1 h_le

/--
Provides the next term of the VanEck sequence given the previously existing list of terms.
-/
def vanEckNextTerm (L : List ℕ) : ℕ := matchSearch L (L.length - 1)

/--
Input a number n.
Output is the first n+1 terms of VanEck sequence as a list.
-/
def vanEck : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => (vanEck n) ++ [vanEckNextTerm (vanEck n)]

-- Verify our sequence structurally matches the expected literal trace natively.
example : vanEck 10 = [0, 0, 1, 0, 2, 0, 2, 2, 1, 6, 0] := by rfl
