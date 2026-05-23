with open('MirskyNewman.lean', 'r') as f:
    content = f.read()

helpers = """
lemma zmod_eq (P : ℕ) [NeZero P] (A B : ℕ) : (A : ZMod P) = (B : ZMod P) ↔ A % P = B % P := by {
  constructor
  · intro h
    have h1 : (A : ZMod P).val = (B : ZMod P).val := by rw [h]
    rw [ZMod.val_natCast, ZMod.val_natCast] at h1
    exact h1
  · intro h
    apply ZMod.val_injective P
    rw [ZMod.val_natCast, ZMod.val_natCast]
    exact h
}

lemma mod_sub_inj (P : ℕ) [NeZero P] (k X : ℕ) (hX : X ≤ P) (i j : ℕ) (hi : i < X) (hj : j < X)
    (h_eq : (k + P - i) % P = (k + P - j) % P) : i = j := by {
  have h_zmod : ((k + P - i : ℕ) : ZMod P) = ((k + P - j : ℕ) : ZMod P) := by {
    apply (zmod_eq P _ _).mpr h_eq
  }
  have hi_le : i ≤ k + P := by omega
  have hj_le : j ≤ k + P := by omega
  rw [Nat.cast_sub hi_le, Nat.cast_sub hj_le] at h_zmod
  have h_cancel : (i : ZMod P) = (j : ZMod P) := by {
    calc (i : ZMod P)
      _ = ((k + P : ℕ) : ZMod P) - (((k + P : ℕ) : ZMod P) - (i : ZMod P)) := by ring
      _ = ((k + P : ℕ) : ZMod P) - (((k + P : ℕ) : ZMod P) - (j : ZMod P)) := by rw [h_zmod]
      _ = (j : ZMod P) := by ring
  }
  have hi_lt : i < P := by omega
  have hj_lt : j < P := by omega
  have h_val : (i : ZMod P).val = (j : ZMod P).val := by rw [h_cancel]
  rw [ZMod.val_natCast, ZMod.val_natCast] at h_val
  rw [Nat.mod_eq_of_lt hi_lt, Nat.mod_eq_of_lt hj_lt] at h_val
  exact h_val
}

lemma disjoint_helper (P : ℕ) [NeZero P] (X : ℕ) (hX : X ≤ P) (v : ℕ → ℕ)
    (h_no_intermediate : ∀ k : Fin P, v (k.val + 1) = X → ∀ i < X, i > 0 → v ((k.val + P - i) % P + 1) ≠ X)
    (k1 k2 : Fin P) (hk1 : v (k1.val + 1) = X) (hk2 : v (k2.val + 1) = X)
    (i1 i2 : ℕ) (hi1 : i1 < X) (hi2 : i2 < X)
    (h_eq : (k1.val + P - i1) % P = (k2.val + P - i2) % P)
    (h_ge : i1 ≥ i2) : k1 = k2 := by {
  let j := i1 - i2
  have hj_lt : j < X := by omega
  have h_zmod : ((k1.val + P - i1 : ℕ) : ZMod P) = ((k2.val + P - i2 : ℕ) : ZMod P) := by {
    apply (zmod_eq P _ _).mpr h_eq
  }
  have hi1_le : i1 ≤ k1.val + P := by omega
  have hi2_le : i2 ≤ k2.val + P := by omega
  rw [Nat.cast_sub hi1_le, Nat.cast_sub hi2_le] at h_zmod
  
  have h_k2_eq : (k2.val : ZMod P) = (k1.val : ZMod P) - (j : ZMod P) := by {
    calc (k2.val : ZMod P)
      _ = (k2.val : ZMod P) + (P : ZMod P) := by {
        have hp : (P : ZMod P) = 0 := ZMod.natCast_self P
        rw [hp, add_zero]
      }
      _ = ((k2.val + P : ℕ) : ZMod P) := by push_cast; rfl
      _ = ((k2.val + P : ℕ) : ZMod P) - (i2 : ZMod P) + (i2 : ZMod P) := by ring
      _ = ((k1.val + P : ℕ) : ZMod P) - (i1 : ZMod P) + (i2 : ZMod P) := by rw [← h_zmod]
      _ = (k1.val : ZMod P) + (P : ZMod P) - (i1 : ZMod P) + (i2 : ZMod P) := by push_cast; rfl
      _ = (k1.val : ZMod P) + 0 - (i1 : ZMod P) + (i2 : ZMod P) := by {
        have hp : (P : ZMod P) = 0 := ZMod.natCast_self P
        rw [hp]
      }
      _ = (k1.val : ZMod P) - ((i1 : ZMod P) - (i2 : ZMod P)) := by ring
      _ = (k1.val : ZMod P) - (j : ZMod P) := by {
        have hj_cast : (j : ZMod P) = (i1 : ZMod P) - (i2 : ZMod P) := by {
          have hj_eq : i1 = i2 + j := by omega
          nth_rw 1 [hj_eq]
          push_cast
          ring
        }
        rw [hj_cast]
      }
  }
  
  by_cases h_j_pos : j > 0
  · have h_k2_val : k2.val % P = (k1.val + P - j) % P := by {
      apply (zmod_eq P _ _).mp
      have h_sub : j ≤ k1.val + P := by omega
      rw [Nat.cast_sub h_sub, Nat.cast_add]
      have hp : (P : ZMod P) = 0 := ZMod.natCast_self P
      rw [hp]
      calc (k2.val : ZMod P)
        _ = (k1.val : ZMod P) - (j : ZMod P) := h_k2_eq
        _ = (k1.val : ZMod P) + 0 - (j : ZMod P) := by ring
    }
    rw [Nat.mod_eq_of_lt k2.isLt] at h_k2_val
    have h_contra := h_no_intermediate k1 hk1 j hj_lt h_j_pos
    rw [← h_k2_val] at h_contra
    exact False.elim (h_contra hk2)
  · have h_j0 : j = 0 := by omega
    have h_j_zmod : (j : ZMod P) = 0 := by rw [h_j0, Nat.cast_zero]
    rw [h_j_zmod] at h_k2_eq
    have h_k1k2 : (k1.val : ZMod P) = (k2.val : ZMod P) := by {
      calc (k1.val : ZMod P)
        _ = (k1.val : ZMod P) - 0 := by ring
        _ = (k2.val : ZMod P) := h_k2_eq.symm
    }
    have h_val_eq : k1.val = k2.val := by {
      have h1 : (k1.val : ZMod P).val = (k2.val : ZMod P).val := by rw [h_k1k2]
      rw [ZMod.val_natCast, ZMod.val_natCast] at h1
      rw [Nat.mod_eq_of_lt k1.isLt, Nat.mod_eq_of_lt k2.isLt] at h1
      exact h1
    }
    exact Fin.eq_of_val_eq h_val_eq
}

lemma vanEck_fiber_upper_bound (P : ℕ) (hP : P ≥ 4) (v : ℕ → ℕ) (f : Fin P → Fin P)"""

target = "lemma vanEck_fiber_upper_bound (P : ℕ) (hP : P ≥ 4) (v : ℕ → ℕ) (f : Fin P → Fin P)"
content = content.replace(target, helpers, 1)

old_sorry = """  sorry
}"""
new_proof = """  let C := Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)
  let S (k : Fin P) := Finset.image (fun i : Fin X => (⟨(k.val + P - i.val) % P, by { apply Nat.mod_lt; omega }⟩ : Fin P)) Finset.univ
  
  have h_S_card : ∀ k ∈ C, (S k).card = X := by {
    intro k hk
    have h_inj : Function.Injective (fun i : Fin X => (⟨(k.val + P - i.val) % P, by { apply Nat.mod_lt; omega }⟩ : Fin P)) := by {
      intro i j h_eq
      have h_val : (k.val + P - i.val) % P = (k.val + P - j.val) % P := by injection h_eq
      have h_P_ne_zero : NeZero P := ⟨by omega⟩
      have h_eq_nat := mod_sub_inj P k.val X hX_le i.val j.val i.isLt j.isLt h_val
      exact Fin.eq_of_val_eq h_eq_nat
    }
    rw [Finset.card_image_of_injective Finset.univ h_inj, Finset.card_univ, Fintype.card_fin]
  }

  have h_disjoint : ∀ k1 ∈ C, ∀ k2 ∈ C, k1 ≠ k2 → Disjoint (S k1) (S k2) := by {
    intro k1 hk1 k2 hk2 h_ne
    rw [Finset.disjoint_left]
    intro y hy1 hy2
    rw [Finset.mem_image] at hy1 hy2
    rcases hy1 with ⟨i1, _, h_y1⟩
    rcases hy2 with ⟨i2, _, h_y2⟩
    rw [← h_y2] at h_y1
    have h_val : (k1.val + P - i1.val) % P = (k2.val + P - i2.val) % P := by injection h_y1
    have hk1_v : v (k1.val + 1) = X := (Finset.mem_filter.mp hk1).2
    have hk2_v : v (k2.val + 1) = X := (Finset.mem_filter.mp hk2).2
    have h_P_ne_zero : NeZero P := ⟨by omega⟩
    
    have h_contra : k1 = k2 := by {
      by_cases h_ge : i1.val ≥ i2.val
      · exact disjoint_helper P X hX_le v h_no_intermediate k1 k2 hk1_v hk2_v i1.val i2.val i1.isLt i2.isLt h_val h_ge
      · have h_ge2 : i2.val ≥ i1.val := by omega
        exact (disjoint_helper P X hX_le v h_no_intermediate k2 k1 hk2_v hk1_v i2.val i1.val i2.isLt i1.isLt h_val.symm h_ge2).symm
    }
    exact h_ne h_contra
  }

  have h_union_card : (Finset.biUnion C S).card = C.card * X := by {
    have h1 : (Finset.biUnion C S).card = ∑ k ∈ C, (S k).card := Finset.card_biUnion h_disjoint
    have h2 : ∑ k ∈ C, (S k).card = ∑ _k ∈ C, X := Finset.sum_congr rfl (fun k hk => h_S_card k hk)
    rw [h1, h2, Finset.sum_const, smul_eq_mul]
  }

  have h_subset : Finset.biUnion C S ⊆ Finset.univ := Finset.subset_univ _
  have h_bound : (Finset.biUnion C S).card ≤ (Finset.univ : Finset (Fin P)).card := Finset.card_le_card h_subset
  rw [Finset.card_univ, Fintype.card_fin] at h_bound
  rw [h_union_card] at h_bound
  exact h_bound
}"""
content = content.replace(old_sorry, new_proof, 1)

with open('MirskyNewman.lean', 'w') as f:
    f.write(content)
