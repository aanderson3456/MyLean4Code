import Mathlib

lemma test_sum (P : ℕ) (f : Fin P → Fin P) (hf : Function.Bijective f) :
  ∑ k : Fin P, (f k).val = ∑ k : Fin P, k.val := by {
    have heq : ∑ k : Fin P, (f k).val = ∑ k : Fin P, (fun x => x.val) (f k) := rfl
    rw [heq]
    exact Equiv.sum_comp (Equiv.ofBijective f hf) (fun k => k.val)
}
