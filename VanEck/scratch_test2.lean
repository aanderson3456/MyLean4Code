import VanEck.Basic
import VanEck

open List

lemma test_not_mem {L : List ℕ} {x : ℕ} (h : L.count x = 0) : x ∉ L := by {
  intro h_mem
  have h_pos : L.count x > 0 := by {
    induction L with
    | nil => cases h_mem
    | cons a as ih =>
      cases h_mem with
      | head => 
        rw [List.count_cons]
        simp
        exact Nat.zero_lt_succ _
      | tail _ h_tail => 
        have ih_res := ih h_tail
        rw [List.count_cons]
        by_cases ha : a = x
        · simp [ha]
          exact Nat.zero_lt_succ _
        · simp [ha]
          exact ih_res
  }
  omega
}
