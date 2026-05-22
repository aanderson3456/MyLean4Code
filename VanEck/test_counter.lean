import Mathlib

lemma vanEck_fiber_sum_is_false : ¬ (∀ (P : ℕ) (hP : P ≥ 4)
    (v : ℕ → ℕ)
    (f : Fin P → Fin P)
    (hf : ∀ k : Fin P, (f k).val = (k.val + P - v (k.val + 1)) % P)
    (hbij : Function.Bijective f)
    (h_recent : ∀ k : Fin P, v ((f k).val + 1) = v (k.val + 1))
    (X : ℕ) (hX_in : ∃ k : Fin P, v (k.val + 1) = X),
    (Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)).card * X = P) := by {
  intro h_all
  let P := 4
  have hP : P ≥ 4 := by decide
  let v : ℕ → ℕ := fun _ => 2
  let f : Fin 4 → Fin 4 := fun k => ⟨(k.val + 4 - 2) % 4, by omega⟩
  have hf : ∀ k : Fin 4, (f k).val = (k.val + 4 - v (k.val + 1)) % 4 := by {
    intro k
    rfl
  }
  have hbij : Function.Bijective f := by {
    have h_inj : Function.Injective f := by decide
    exact Finite.injective_iff_bijective.mp h_inj
  }
  have h_recent : ∀ k : Fin 4, v ((f k).val + 1) = v (k.val + 1) := by {
    intro k
    rfl
  }
  let X := 2
  have hX_in : ∃ k : Fin 4, v (k.val + 1) = X := ⟨⟨0, by decide⟩, rfl⟩
  
  have h_result := h_all 4 hP v f hf hbij h_recent X hX_in
  
  have h_card : (Finset.univ.filter (fun k : Fin 4 => v (k.val + 1) = X)).card = 4 := by {
    have h_filter_univ : (Finset.univ.filter (fun k : Fin 4 => v (k.val + 1) = X)) = Finset.univ := by {
      apply Finset.filter_true_of_mem
      intro k _
      rfl
    }
    rw [h_filter_univ]
    exact Fintype.card_fin 4
  }
  
  rw [h_card] at h_result
  revert h_result
  decide
}
