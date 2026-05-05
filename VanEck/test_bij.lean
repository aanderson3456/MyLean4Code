import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finite.Defs

lemma test_bij (P n_2 : ℕ) (h_P_pos : P ≥ 1) (vanEckNthTerm : ℕ → ℕ) 
  (f_inj : ∀ i j, 1 ≤ i → i ≤ P → 1 ≤ j → j ≤ P → i < j → 
    (i + P - vanEckNthTerm (n_2 + i)) % P ≠ (j + P - vanEckNthTerm (n_2 + j)) % P) :
  Function.Bijective (fun (k : Fin P) => (⟨(k.val + 1 + P - vanEckNthTerm (n_2 + k.val + 1)) % P, Nat.mod_lt _ h_P_pos⟩ : Fin P)) := by {
    have h_inj : Function.Injective (fun (k : Fin P) => (⟨(k.val + 1 + P - vanEckNthTerm (n_2 + k.val + 1)) % P, Nat.mod_lt _ h_P_pos⟩ : Fin P)) := by {
      intro i j heq
      have h1 : 1 ≤ i.val + 1 := Nat.le_add_left 1 i.val
      have h2 : i.val + 1 ≤ P := i.isLt
      have h3 : 1 ≤ j.val + 1 := Nat.le_add_left 1 j.val
      have h4 : j.val + 1 ≤ P := j.isLt
      by_cases hlt : i.val + 1 < j.val + 1
      · have hc := f_inj (i.val + 1) (j.val + 1) h1 h2 h3 h4 hlt
        have heq_val := congr_arg Fin.val heq
        exact False.elim (hc heq_val)
      · by_cases hlt2 : j.val + 1 < i.val + 1
        · have hc := f_inj (j.val + 1) (i.val + 1) h3 h4 h1 h2 hlt2
          have heq_val := congr_arg Fin.val heq
          exact False.elim (hc heq_val.symm)
        · have heq_val : i.val + 1 = j.val + 1 := by 
            have h_not_lt1 : ¬(i.val + 1 < j.val + 1) := hlt
            have h_not_lt2 : ¬(j.val + 1 < i.val + 1) := hlt2
            exact Nat.le_antisymm (Nat.le_of_not_lt h_not_lt2) (Nat.le_of_not_lt h_not_lt1)
          exact Fin.eq_of_val_eq (Nat.add_right_cancel heq_val)
    }
    rw [← Finite.injective_iff_bijective]
    exact h_inj
}
