import VanEck.Basic
import VanEck

open List

lemma mem_implies_count_pos {L : List ℕ} {x : ℕ} (h : x ∈ L) : L.count x > 0 := by {
  induction h with
  | head as =>
    rw [List.count_cons]
    simp
  | tail a as h_tail ih =>
    rw [List.count_cons]
    by_cases ha : a = x
    · simp [ha]
    · simp [ha]
      exact ih
}
