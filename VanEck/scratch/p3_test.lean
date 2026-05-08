import InfiniteTwos

lemma fin_sum_three {n : ℕ} (hn : n = 3) (f : Fin n → ℕ) :
  ∑ k : Fin n, f k = f ⟨0, by omega⟩ + f ⟨1, by omega⟩ + f ⟨2, by omega⟩ := by {
  subst hn
  exact Fin.sum_univ_three f
}

lemma period_three_forces_all_threes (a b c C : ℕ)
  (ha13 : a = 1 ∨ a = 3)
  (hb13 : b = 1 ∨ b = 3)
  (hc13 : c = 1 ∨ c = 3)
  (hC2 : C ≥ 2)
  (h_sum : a + b + c = C * 3) : a = 3 ∧ b = 3 ∧ c = 3 := by {
  have ha_eq : a = 3 := by {
    rcases ha13 with rfl | rfl <;> rcases hb13 with rfl | rfl <;> rcases hc13 with rfl | rfl <;> omega
  }
  have hb_eq : b = 3 := by {
    rcases ha13 with rfl | rfl <;> rcases hb13 with rfl | rfl <;> rcases hc13 with rfl | rfl <;> omega
  }
  have hc_eq : c = 3 := by {
    rcases ha13 with rfl | rfl <;> rcases hb13 with rfl | rfl <;> rcases hc13 with rfl | rfl <;> omega
  }
  exact ⟨ha_eq, hb_eq, hc_eq⟩
}
