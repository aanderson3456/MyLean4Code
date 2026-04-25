import VanEck
import Mathlib

lemma lem1 (m N : ℕ) (h1 : m * m + 2 * m + 1 > N * N + 2 * N + 1) : m > N := by
  have h_add : m * m + 2 * m + 1 = (m + 1) * (m + 1) := by ring
  have h_add_N : N * N + 2 * N + 1 = (N + 1) * (N + 1) := by ring
  rw [h_add, h_add_N] at h1
  exact Nat.lt_of_succ_lt_succ (Nat.lt_of_mul_lt_mul_left h1 (Nat.zero_le _)) -- wait, need a proper lemma for squares
