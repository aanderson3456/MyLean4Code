import Mathlib

lemma ap_from_shift (P : ℕ) (hP : P ≥ 4) (X : ℕ) (hX : X ≥ 1)
    (C : Finset (Fin P))
    (f : Fin P → Fin P)
    (hC : C.card * X = P)
    (hf : ∀ k : Fin P, (f k).val = (k.val + 1 + P - X) % P)
    (h_inv : ∀ k ∈ C, f k ∈ C) :
    ∃ start : Fin P, C = Finset.univ.filter (fun k => ∃ i : ℕ, k.val = (start.val + i * X) % P) := by {
  sorry
}
