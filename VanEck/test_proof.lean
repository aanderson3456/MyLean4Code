import Mathlib.Data.Nat.Basic

lemma test (P A B : ℕ) (heq : A % P = B % P) : (A + 1) % P = (B + 1) % P := by {
  calc (A + 1) % P
    _ = (A % P + 1 % P) % P := by rw [Nat.add_mod]
    _ = (B % P + 1 % P) % P := by rw [heq]
    _ = (B + 1) % P := by rw [← Nat.add_mod]
}
