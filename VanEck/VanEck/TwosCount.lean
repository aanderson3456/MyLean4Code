/-
Copyright (c) 2026 Austin Anderson
SPDX-License-Identifier: MIT

Kernel-checked count of the `2`s among the first `1000` Van Eck terms.

The naive `vanEck` list implementation is cubic, so we introduce an equivalent
"reversed-prefix" implementation `revVE` (most recent term first), prove
`revVE n = (vanEck n).reverse`, and let the kernel evaluate the fast version
via `decide +kernel` (no `native_decide`, no extra axioms).
-/
import VanEck
import Mathlib

namespace TwosCount

/-- Search a reversed prefix for `x`, returning the (1-based, offset by `d`) distance. -/
def revFind (x : ℕ) : List ℕ → ℕ → ℕ
  | [], _ => 0
  | y :: ys, d => if x = y then d else revFind x ys (d + 1)

/-- One Van Eck step on a reversed prefix. -/
def revStep : List ℕ → List ℕ
  | [] => [0]
  | x :: xs => revFind x xs 1 :: x :: xs

/-- The reversed Van Eck prefix of length `n + 1`. -/
def revVE : ℕ → List ℕ
  | 0 => [0]
  | n + 1 => revStep (revVE n)

lemma listNth_eq_getD (l : List ℕ) (j : ℕ) : listNth l j = l.getD j 0 := by {
  induction l generalizing j with
  | nil => rfl
  | cons a l ih =>
    cases j with
    | zero => rfl
    | succ j => exact ih j
}

lemma listNth_append_lt (P : List ℕ) (x j : ℕ) (hj : j < P.length) :
    listNth (P ++ [x]) j = listNth P j := by {
  rw [listNth_eq_getD, listNth_eq_getD, List.getD_append _ _ _ _ hj]
}

lemma take_succ_reverse (P : List ℕ) (j : ℕ) (hj : j < P.length) :
    (P.take (j + 1)).reverse = listNth P j :: (P.take j).reverse := by {
  rw [List.take_add_one, List.getElem?_eq_getElem hj, listNth_eq_getD,
    List.getD_eq_getElem _ _ hj]
  simp
}

lemma matchSearch_append_eq_revFind (P : List ℕ) (x : ℕ) :
    ∀ j ≤ P.length,
      matchSearch (P ++ [x]) j = revFind x (P.take j).reverse (P.length - j + 1) := by {
  intro j
  induction j with
  | zero =>
    intro _
    rfl
  | succ j ih =>
    intro hj
    have hlen : (P ++ [x]).length - 1 = P.length := by {
      simp
    }
    have hdist : P.length - j = P.length - (j + 1) + 1 := by {
      omega
    }
    simp only [matchSearch, hlen, listNth_last, listNth_append_lt P x j (by omega)]
    rw [take_succ_reverse P j (by omega), revFind, ← hdist, ← ih (by omega)]
}

lemma vanEckNextTerm_eq (P : List ℕ) (x : ℕ) :
    vanEckNextTerm (P ++ [x]) = revFind x P.reverse 1 := by {
  have h := matchSearch_append_eq_revFind P x P.length (le_refl _)
  rw [List.take_length, Nat.sub_self] at h
  have hlen : (P ++ [x]).length - 1 = P.length := by {
    simp
  }
  unfold vanEckNextTerm
  rw [hlen]
  exact h
}

lemma vanEck_ne_nil (n : ℕ) : vanEck n ≠ [] := by {
  intro h
  have hl := vanEckLength n
  rw [h] at hl
  simp at hl
}

lemma revVE_eq_reverse (n : ℕ) : revVE n = (vanEck n).reverse := by {
  induction n with
  | zero => rfl
  | succ n ih =>
    obtain ⟨P, x, hPx⟩ := List.eq_nil_or_concat (vanEck n) |>.resolve_left (vanEck_ne_nil n)
    rw [List.concat_eq_append] at hPx
    have hstep : vanEck (n + 1) = vanEck n ++ [vanEckNextTerm (vanEck n)] := rfl
    rw [hstep, hPx, vanEckNextTerm_eq, revVE, ih, hPx]
    simp [revStep]
}

lemma vanEckNthTerm_succ (n : ℕ) :
    vanEckNthTerm (n + 1) = vanEckNextTerm (vanEck n) := by {
  have h := listNth_last (vanEckNextTerm (vanEck n)) (vanEck n)
  rw [vanEckLength] at h
  exact h
}

lemma card_filter_eq_count (v n : ℕ) :
    ((Finset.range (n + 1)).filter (fun k => vanEckNthTerm k = v)).card =
      (vanEck n).count v := by {
  induction n with
  | zero =>
    have h1 : vanEck 0 = [0] := rfl
    rw [h1, Finset.range_one, Finset.filter_singleton]
    by_cases h : vanEckNthTerm 0 = v
    · rw [if_pos h, ← h]
      decide
    · rw [if_neg h, Finset.card_empty, List.count_eq_zero.mpr]
      simp only [List.mem_singleton]
      intro h'
      apply h
      rw [h']
      rfl
  | succ n ih =>
    have hstep : vanEck (n + 1) = vanEck n ++ [vanEckNextTerm (vanEck n)] := rfl
    rw [Finset.range_add_one, Finset.filter_insert, hstep, List.count_append, ← ih,
      ← vanEckNthTerm_succ]
    by_cases h : vanEckNthTerm (n + 1) = v
    · rw [if_pos h, Finset.card_insert_of_notMem (by simp), h, List.count_singleton_self]
    · have hc : [vanEckNthTerm (n + 1)].count v = 0 := by {
        apply List.count_eq_zero.mpr
        simp only [List.mem_singleton]
        exact Ne.symm h
      }
      rw [if_neg h, hc]
      omega
}

lemma revVE_count_two : (revVE 999).count 2 = 18 := by {
  decide +kernel
}

/-- **Milestone A3.** Exactly `18` of the indices `n < 1000` satisfy `a(n) = 2`
(kernel-checked through the verified fast implementation `revVE`). -/
theorem count_twos_below_1000 :
    ((Finset.range 1000).filter (fun n => vanEckNthTerm n = 2)).card = 18 := by {
  have h := card_filter_eq_count 2 999
  rw [h, ← List.count_reverse, ← revVE_eq_reverse]
  exact revVE_count_two
}

end TwosCount
