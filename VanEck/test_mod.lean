import Mathlib

lemma mod_eq_cases (A B P : ℕ) (hP : P > 0) (hA : A < 2 * P) (hB : B < 2 * P) (hc : A % P = B % P) :
    A = B ∨ A + P = B ∨ B + P = A := by {
  have h2P : 2 * P = P + P := Nat.two_mul P
  rw [h2P] at hA hB
  by_cases hA_lt : A < P
  · have hA_mod : A % P = A := Nat.mod_eq_of_lt hA_lt
    by_cases hB_lt : B < P
    · have hB_mod : B % P = B := Nat.mod_eq_of_lt hB_lt
      rw [hA_mod, hB_mod] at hc
      left; exact hc
    · push Not at hB_lt
      have h1 : B - P < P := Nat.sub_lt_left_of_lt_add hB_lt hB
      have hB_mod : B % P = B - P := by {
        have hB_add : B = B - P + P := (Nat.sub_add_cancel hB_lt).symm
        nth_rw 1 [hB_add]
        have h_add := Nat.add_mod_right (B - P) P
        rw [Nat.mod_eq_of_lt h1] at h_add
        exact h_add
      }
      rw [hA_mod, hB_mod] at hc
      right; left
      omega
  · push Not at hA_lt
    have h1 : A - P < P := Nat.sub_lt_left_of_lt_add hA_lt hA
    have hA_mod : A % P = A - P := by {
      have hA_add : A = A - P + P := (Nat.sub_add_cancel hA_lt).symm
      nth_rw 1 [hA_add]
      have h_add := Nat.add_mod_right (A - P) P
      rw [Nat.mod_eq_of_lt h1] at h_add
      exact h_add
    }
    by_cases hB_lt : B < P
    · have hB_mod : B % P = B := Nat.mod_eq_of_lt hB_lt
      rw [hA_mod, hB_mod] at hc
      right; right
      omega
    · push Not at hB_lt
      have h2 : B - P < P := Nat.sub_lt_left_of_lt_add hB_lt hB
      have hB_mod : B % P = B - P := by {
        have hB_add : B = B - P + P := (Nat.sub_add_cancel hB_lt).symm
        nth_rw 1 [hB_add]
        have h_add := Nat.add_mod_right (B - P) P
        rw [Nat.mod_eq_of_lt h2] at h_add
        exact h_add
      }
      rw [hA_mod, hB_mod] at hc
      left
      omega
}
