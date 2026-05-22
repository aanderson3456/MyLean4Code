import Mathlib

lemma test_omega (C P sum : ℕ) (hC : C ≥ 2) (hP : P ≥ 4) (h1 : sum = P) (h2 : sum = C * P) : False := by {
  nlinarith
}
