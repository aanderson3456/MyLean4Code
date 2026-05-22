import Mathlib

open Classical

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
    (h_no1 : ∃ k : Fin P, v (k.val + 1) ≠ 1)
    (hf : ∀ k : Fin P, (f k).val = (k.val + 1 + P - v (k.val + 1)) % P)
    (hbij : Function.Bijective f)
    (h_recent : ∀ k : Fin P, v (f k).val = v (k.val + 1)) :
    False := by {
  let S := Finset.univ.image (fun k : Fin P => v (k.val + 1))
  let cover : ℕ → Finset (Fin P) := fun X => Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)
  
  have h_min : ∀ X ∈ S, X ≥ 3 := by {
    intro X hX
    have hX_in : ∃ k : Fin P, v (k.val + 1) = X := by {
      have h1 := Finset.mem_image.mp hX
      rcases h1 with ⟨k, hk_in, hk_eq⟩
      exact ⟨k, hk_eq⟩
    }
    rcases hX_in with ⟨k, hk⟩
    have hv := hv1 k
    have hn2 := h_no2 k
    by_cases hX1 : X = 1
    · rw [← hk] at hX1
      have h1_in : ∃ k : Fin P, v (k.val + 1) = 1 := ⟨k, hX1⟩
      have h_sum := vanEck_fiber_sum P hP v f hf hbij h_recent 1 h1_in
      rw [mul_one] at h_sum
      have h_all_1 : ∀ k : Fin P, v (k.val + 1) = 1 := by {
        intro x
        have h_card_univ : Finset.card (Finset.univ : Finset (Fin P)) = P := Fintype.card_fin P
        have h_subset : cover 1 ⊆ Finset.univ := Finset.filter_subset _ _
        have h_eq : cover 1 = Finset.univ := by {
          apply Finset.eq_of_subset_of_card_le h_subset
          rw [h_sum, h_card_univ]
        }
        have hx_in : x ∈ cover 1 := by {
          rw [h_eq]
          exact Finset.mem_univ x
        }
        have hx_filter := Finset.mem_filter.mp hx_in
        exact hx_filter.right
      }
      rcases h_no1 with ⟨k1, hk1⟩
      have hk1_1 := h_all_1 k1
      omega
    · omega
  }
  
  have h_partition : ∀ k : Fin P, ∃! X, X ∈ S ∧ k ∈ cover X := by {
    intro k
    use v (k.val + 1)
    constructor
    · constructor
      · apply Finset.mem_image.mpr
        exact ⟨k, Finset.mem_univ k, rfl⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ k, rfl⟩
    · intro y hy
      rcases hy with ⟨hy1, hy2⟩
      have hy_filter := Finset.mem_filter.mp hy2
      exact hy_filter.right.symm
  }
  
  have h_ap : ∀ X ∈ S, ∃ start : Fin P, cover X = Finset.univ.filter (fun k => ∃ i : ℕ, k.val = (start.val + i * X) % P) := by {
    intro X hX
    -- sorry this for now to see if we can just push it into combinatorial_squeeze.
    sorry
  }
  
  exact mirsky_newman_exact_cover P S h_min cover h_partition h_ap
}
