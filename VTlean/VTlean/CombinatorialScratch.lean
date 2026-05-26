import Mathlib
import VTlean.VTCode
import VTlean.CuculiereCombinatorial

open Nat Finset

lemma S_set_disjoint_union (n k a : Nat) :
  S_set n k a = (S_set n k a).filter (fun s => (0 : Fin (n + 1)) ∉ s) ∪ (S_set n k a).filter (fun s => (0 : Fin (n + 1)) ∈ s) := by
  ext s
  simp
  tauto

lemma S_set_filter_not_mem_zero (n k a : Nat) :
  (S_set n k a).filter (fun s => (0 : Fin (n + 1)) ∉ s) = T_set n k a := by
  ext s
  simp [S_set, T_set]
  tauto

lemma S_set_filter_mem_zero_card (n k a : Nat) (hk : k > 0) :
  ((S_set n k a).filter (fun s => (0 : Fin (n + 1)) ∈ s)).card = (T_set n (k - 1) a).card := by
  apply Finset.card_bij (fun s _ => s.erase 0)
  · intro s hs
    simp only [mem_filter, S_set] at hs
    have hs_mem : (0 : Fin (n + 1)) ∈ s := hs.2
    have hs_card : s.card = k := hs.1.2.1
    have hs_sum : (∑ x ∈ s, x.val) % (n + 1) = a % (n + 1) := hs.1.2.2
    simp only [mem_filter, mem_univ, true_and, T_set]
    refine ⟨?_, ⟨Finset.notMem_erase 0 s, ?_⟩⟩
    · rw [Finset.card_erase_of_mem hs_mem, hs_card]
    · have h_val_zero : (0 : Fin (n + 1)).val = 0 := rfl
      have h_sum : ∑ x ∈ s.erase 0, x.val = ∑ x ∈ s, x.val := by
        have h_eq : s = insert 0 (s.erase 0) := (Finset.insert_erase hs_mem).symm
        nth_rw 2 [h_eq]
        rw [Finset.sum_insert (Finset.notMem_erase 0 s), h_val_zero, zero_add]
      rw [h_sum]
      exact hs_sum
  · intro s₁ hs₁ s₂ hs₂ h_eq
    simp only [mem_filter, S_set] at hs₁ hs₂
    have hs₁_mem : (0 : Fin (n + 1)) ∈ s₁ := hs₁.2
    have hs₂_mem : (0 : Fin (n + 1)) ∈ s₂ := hs₂.2
    have h1 : insert 0 (s₁.erase 0) = s₁ := Finset.insert_erase hs₁_mem
    have h2 : insert 0 (s₂.erase 0) = s₂ := Finset.insert_erase hs₂_mem
    rw [← h1, ← h2, h_eq]
  · intro t ht
    simp only [mem_filter, T_set] at ht
    have ht_card : t.card = k - 1 := ht.2.1
    have ht_not_mem : (0 : Fin (n + 1)) ∉ t := ht.2.2.1
    have ht_sum : (∑ x ∈ t, x.val) % (n + 1) = a % (n + 1) := ht.2.2.2
    use insert 0 t
    refine ⟨?_, ?_⟩
    · simp only [mem_filter, S_set, mem_univ, true_and]
      refine ⟨⟨?_, ?_⟩, Finset.mem_insert_self 0 t⟩
      · rw [Finset.card_insert_of_notMem ht_not_mem, ht_card]
        omega
      · have h_val_zero : (0 : Fin (n + 1)).val = 0 := rfl
        have h_sum : ∑ x ∈ insert 0 t, x.val = ∑ x ∈ t, x.val := by
          rw [Finset.sum_insert ht_not_mem, h_val_zero, zero_add]
        rw [h_sum]
        exact ht_sum
    · exact Finset.erase_insert ht_not_mem

theorem inclusion_exclusion_proof (n k a : Nat) (hk : k > 0) :
  S n k a = T n k a + T n (k - 1) a := by
  unfold S T
  have h_union := S_set_disjoint_union n k a
  have h_disjoint : Disjoint ((S_set n k a).filter (fun s => (0 : Fin (n + 1)) ∉ s)) ((S_set n k a).filter (fun s => (0 : Fin (n + 1)) ∈ s)) := by
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy h_eq
    simp only [mem_filter] at hx hy
    rw [h_eq] at hx
    exact hx.2 hy.2
  rw [h_union, card_union_of_disjoint h_disjoint]
  rw [S_set_filter_not_mem_zero, S_set_filter_mem_zero_card n k a hk]
