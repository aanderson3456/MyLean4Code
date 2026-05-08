import VanEck.Basic
import VanEck

open List

lemma mem_implies_count_pos {L : List ℕ} {x : ℕ} (h : x ∈ L) : L.count x > 0 := by {
  induction h with
  | head as =>
    rw [List.count_cons]
    have h1 : (x == x) = true := by exact Nat.beq_refl _
    simp [h1]
    exact Nat.zero_lt_succ _
  | tail b h_tail ih =>
    rw [List.count_cons]
    cases hb : (b == x)
    · simp [hb]
      exact ih
    · simp [hb]
      exact Nat.zero_lt_succ _
}
