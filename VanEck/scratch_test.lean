import VanEck.Basic
import VanEck

open List

lemma mem_implies_count_pos {L : List ℕ} {x : ℕ} (h : x ∈ L) : L.count x ≥ 1 := by {
  induction L with
  | nil => cases h
  | cons a as ih =>
    cases h with
    | head _ => 
      rw [List.count_cons]
      have ha : a = x := rfl
      simp [ha]
    | tail _ h_tail => 
      have ih_res := ih h_tail
      rw [List.count_cons]
      by_cases ha : a = x
      · simp [ha]
      · simp [ha]
        exact ih_res
}
