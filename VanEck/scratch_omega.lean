import Mathlib
import VanEck

open Finset

lemma fin_sum_mod_P_multiple (P : ℕ) (hP : P > 0) (v : Fin P → ℕ) 
    (hv1 : ∀ k, 1 ≤ v k) (hvP : ∀ k, v k ≤ P)
    (f : Fin P → Fin P)
    (hf : ∀ k, (f k).val = (k.val + 1 + P - v k) % P)
    (hbij : Function.Bijective f) :
    ∃ C : ℕ, ∑ k : Fin P, v k = C * P := by {
  have h_sum_f : ∑ k : Fin P, (f k).val = ∑ k : Fin P, k.val := by
    have heq : ∑ k : Fin P, (f k).val = ∑ k : Fin P, (fun x => x.val) (f k) := rfl
    rw [heq]
    exact Equiv.sum_comp (Equiv.ofBijective f hbij) (fun k => k.val)

  let d := fun (k : Fin P) => (k.val + 1 + P - v k) / P

  have h_div_mod : ∀ k, (k.val + 1 + P - v k) = P * d k + (f k).val := by {
    intro k
    have h_mod := Nat.div_add_mod (k.val + 1 + P - v k) P
    have hfk := hf k
    have hd_def : d k = (k.val + 1 + P - v k) / P := rfl
    omega
  }

  have h_sum1 : ∑ k : Fin P, (k.val + 1 + P - v k) = ∑ k : Fin P, (P * d k + (f k).val) := by {
    apply Finset.sum_congr rfl
    intro x _
    exact h_div_mod x
  }

  have h_sum_left : ∑ k : Fin P, (k.val + 1 + P - v k) + ∑ k : Fin P, v k = ∑ k : Fin P, (k.val + 1 + P) := by {
    rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro x _
    have h2 := hvP x
    omega
  }

  have h_sum_right : ∑ k : Fin P, (P * d k + (f k).val) = P * ∑ k : Fin P, d k + ∑ k : Fin P, (f k).val := by {
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
  }

  have h_sum_1P : ∑ k : Fin P, (k.val + 1 + P) = ∑ k : Fin P, k.val + P * (P + 1) := by {
    have h1 : ∑ k : Fin P, (k.val + 1 + P) = ∑ k : Fin P, k.val + ∑ k : Fin P, (1 + P) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _; omega
    rw [h1]
    have h2 : ∑ k : Fin P, (1 + P) = P * (P + 1) := by
      have hz : ∑ k : Fin P, (1 + P) = (Finset.card (Finset.univ : Finset (Fin P))) * (1 + P) := by
        exact Finset.sum_const (1 + P)
      have hc : Finset.card (Finset.univ : Finset (Fin P)) = P := Fintype.card_fin P
      rw [hc] at hz
      rw [hz]
      ring
    omega
  }

  have h_eq1 : ∑ k : Fin P, (k.val + 1 + P - v k) = P * ∑ k : Fin P, d k + ∑ k : Fin P, k.val := by {
    rw [h_sum1, h_sum_right, h_sum_f]
  }

  have h_eq2 : P * ∑ k : Fin P, d k + ∑ k : Fin P, k.val + ∑ k : Fin P, v k = ∑ k : Fin P, k.val + P * (P + 1) := by {
    have hr : P * ∑ k : Fin P, d k + ∑ k : Fin P, k.val + ∑ k : Fin P, v k = ∑ k : Fin P, (k.val + 1 + P - v k) + ∑ k : Fin P, v k := by rw [h_eq1]
    rw [hr, h_sum_left]
    exact h_sum_1P
  }

  have h_eq3 : (∑ k : Fin P, k.val) + (P * ∑ k : Fin P, d k + ∑ k : Fin P, v k) = (∑ k : Fin P, k.val) + P * (P + 1) := by {
    omega
  }

  have h_eq4 : P * ∑ k : Fin P, d k + ∑ k : Fin P, v k = P * (P + 1) := Nat.add_left_cancel h_eq3

  have h_eq5 : ∑ k : Fin P, v k = P * (P + 1) - P * ∑ k : Fin P, d k := by omega

  have h_eq6 : ∑ k : Fin P, v k = ((P + 1) - ∑ k : Fin P, d k) * P := by {
    rw [h_eq5]
    have hz : P * (P + 1) - P * ∑ k : Fin P, d k = P * ((P + 1) - ∑ k : Fin P, d k) := by
      exact (Nat.mul_sub_left_distrib P (P + 1) (∑ k : Fin P, d k)).symm
    rw [hz]
    ring
  }

  exact ⟨((P + 1) - ∑ k : Fin P, d k), h_eq6⟩
}
