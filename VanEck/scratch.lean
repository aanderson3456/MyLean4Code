import Mathlib

lemma mod_cases (P : ℕ) (A : ℕ) (hA : A < 2 * P) : (A < P ∧ A % P = A) ∨ (P ≤ A ∧ A % P = A - P) := by {
  rcases lt_or_ge A P with hlt | hge
  · left
    exact ⟨hlt, Nat.mod_eq_of_lt hlt⟩
  · right
    have h_sub : A - P < P := by omega
    have h_mod : A % P = (A - P) % P := by {
      have h1 : A = P + (A - P) := by omega
      nth_rw 1 [h1]
      rw [Nat.add_mod_left]
    }
    rw [h_mod]
    exact ⟨hge, Nat.mod_eq_of_lt h_sub⟩
}

lemma mod_eq_cases (P : ℕ) (A B : ℕ) (hA : A < 2 * P) (hB : B < 2 * P) (heq : A % P = B % P) :
  A = B ∨ A = B + P ∨ B = A + P := by {
  have hA_cases := mod_cases P A hA
  have hB_cases := mod_cases P B hB
  rcases hA_cases with ⟨hA_lt, hA_eq⟩ | ⟨hA_ge, hA_eq⟩ <;> rcases hB_cases with ⟨hB_lt, hB_eq⟩ | ⟨hB_ge, hB_eq⟩
  · rw [hA_eq, hB_eq] at heq; left; exact heq
  · rw [hA_eq, hB_eq] at heq; right; right; omega
  · rw [hA_eq, hB_eq] at heq; right; left; omega
  · rw [hA_eq, hB_eq] at heq; left; omega
}

lemma vanEck_fiber_upper_bound_inj (P X : ℕ) (hX_le : X ≤ P) (k : Fin P) (i j : Fin X)
    (heq : (k.val + P - i.val) % P = (k.val + P - j.val) % P) : i = j := by {
  have hA_lt : k.val + P - i.val < 2 * P := by {
    have hk_lt : k.val < P := k.isLt
    omega
  }
  have hB_lt : k.val + P - j.val < 2 * P := by {
    have hk_lt : k.val < P := k.isLt
    omega
  }
  have h_cases := mod_eq_cases P (k.val + P - i.val) (k.val + P - j.val) hA_lt hB_lt heq
  
  rcases h_cases with h1 | h2 | h3
  · have h_eq : i.val = j.val := by omega
    exact Fin.eq_of_val_eq h_eq
  · have hi_lt : i.val < P := Nat.lt_of_lt_of_le i.isLt hX_le
    have hj_lt : j.val < P := Nat.lt_of_lt_of_le j.isLt hX_le
    omega
  · have hi_lt : i.val < P := Nat.lt_of_lt_of_le i.isLt hX_le
    have hj_lt : j.val < P := Nat.lt_of_lt_of_le j.isLt hX_le
    omega
}
