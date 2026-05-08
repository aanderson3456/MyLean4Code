import Mathlib
example (x P v : ℕ) (h2 : v ≤ P) : v ≤ x + 1 + P := by
  have h_le : 1 + P ≤ x + 1 + P := by
    rw [Nat.add_assoc]
    exact Nat.le_add_left (1 + P) x
  exact le_trans (le_trans h2 (Nat.le_add_left P 1)) h_le
