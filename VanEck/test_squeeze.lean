import Mathlib

axiom mirsky_newman_exact_cover (P : ℕ) (S : Finset ℕ)
    (h_min : ∀ X ∈ S, X ≥ 3)
    (cover : ℕ → Finset (Fin P))
    (h_partition : ∀ k : Fin P, ∃! X, X ∈ S ∧ k ∈ cover X)
    (h_ap : ∀ X ∈ S, ∃ start : Fin P, cover X = Finset.univ.filter (fun k => ∃ i : ℕ, k.val = (start.val + i * X) % P)) :
    False

lemma vanEck_fiber_sum (P : ℕ) (hP : P ≥ 4)
    (v : ℕ → ℕ)
    (f : Fin P → Fin P)
    (hf : ∀ k : Fin P, (f k).val = (k.val + 1 + P - v (k.val + 1)) % P)
    (hbij : Function.Bijective f)
    (h_recent : ∀ k : Fin P, v (f k).val = v (k.val + 1))
    (X : ℕ) (hX_in : ∃ k : Fin P, v (k.val + 1) = X) :
    (Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)).card * X = P := by sorry

lemma combinatorial_squeeze (P : ℕ) (hP : P ≥ 4)
    (v : ℕ → ℕ)
    (f : Fin P → Fin P)
    (hv1 : ∀ k : Fin P, 1 ≤ v (k.val + 1))
    (hvP : ∀ k : Fin P, v (k.val + 1) ≤ P)
    (h_no2 : ∀ k : Fin P, v (k.val + 1) ≠ 2)
    (hf : ∀ k : Fin P, (f k).val = (k.val + 1 + P - v (k.val + 1)) % P)
    (hbij : Function.Bijective f)
    (h_recent : ∀ k : Fin P, v (f k).val = v (k.val + 1)) :
    False := by {
  let S := Finset.univ.image (fun k : Fin P => v (k.val + 1))
  let cover := fun X => Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)
  
  have h_min : ∀ X ∈ S, X ≥ 3 := by {
    intro X hX
    simp only [Finset.mem_image, Finset.mem_univ, true_and] at hX
    rcases hX with ⟨k, hk⟩
    -- we need X != 1, but we don't have it!
    sorry
  }
  sorry
}
