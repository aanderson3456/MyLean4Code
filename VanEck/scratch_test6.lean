import VanEck.Basic
import VanEck

open List

lemma mem_implies_count_pos {L : List ℕ} {x : ℕ} (h : x ∈ L) : L.count x > 0 := by {
  induction L with
  | nil => cases h
  | cons a as ih =>
    rw [List.count_cons]
    cases h with
    | head => 
      simp
    | tail _ h_tail => 
      cases hb : (a == x)
      · simp [hb]
        exact ih h_tail
      · simp [hb]
}
