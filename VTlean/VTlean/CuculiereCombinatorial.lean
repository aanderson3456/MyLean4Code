import Mathlib
import VTlean.VTCode
import VTlean.Cuculiere
import VTlean.NumOsNumIs
import VTlean.DelCode

open Nat Finset

/-!
# Cuculiere's Combinatorial Approach

This file formalizes the combinatorial "necklace" approach to proving Cuculiere's Theorem,
which avoids complex analysis and polynomials by mapping binary VT codewords to
mathematical subset sums.

Let `S(n, k, a)` be the number of `k`-element subsets of the cyclic group `Z_{n+1}`
whose sum modulo `n+1` is exactly `a`.

Let `T(n, k, a)` be the number of `k`-element subsets of the non-zero elements `{1, ..., n}`
whose sum modulo `n+1` is exactly `a`.
-/

/-- S_set(k, a): The set of k-element subsets of Z_{n+1} whose sum modulo n+1 is a. -/
def S_set (n k a : Nat) : Finset (Finset (Fin (n + 1))) :=
  univ.filter (fun s => s.card = k ∧ (∑ x ∈ s, x.val) % (n + 1) = a % (n + 1))

/-- S(k, a): Number of k-element subsets of Z_{n+1} whose sum modulo n+1 is a. -/
def S (n k a : Nat) : Nat := (S_set n k a).card

/-- T_set(k, a): The set of k-element subsets of Z_{n+1} \ {0} whose sum modulo n+1 is a. -/
def T_set (n k a : Nat) : Finset (Finset (Fin (n + 1))) :=
  univ.filter (fun s => s.card = k ∧ (0 : Fin (n + 1)) ∉ s ∧ (∑ x ∈ s, x.val) % (n + 1) = a % (n + 1))

/-- T(k, a): Number of k-element subsets of Z_{n+1} \ {0} whose sum modulo n+1 is a. -/
def T (n k a : Nat) : Nat := (T_set n k a).card

lemma S_set_disjoint_union (n k a : Nat) :
  S_set n k a = (S_set n k a).filter (fun s => (0 : Fin (n + 1)) ∉ s) ∪ (S_set n k a).filter (fun s => (0 : Fin (n + 1)) ∈ s) := by {
  ext s
  simp
  tauto
}

lemma S_set_filter_not_mem_zero (n k a : Nat) :
  (S_set n k a).filter (fun s => (0 : Fin (n + 1)) ∉ s) = T_set n k a := by {
  ext s
  simp [S_set, T_set]
  tauto
}

lemma S_set_filter_mem_zero_card (n k a : Nat) (hk : k > 0) :
  ((S_set n k a).filter (fun s => (0 : Fin (n + 1)) ∈ s)).card = (T_set n (k - 1) a).card := by {
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
      have h_sum : ∑ x ∈ s.erase 0, x.val = ∑ x ∈ s, x.val := by {
        have h_eq : s = insert 0 (s.erase 0) := (Finset.insert_erase hs_mem).symm
        nth_rw 2 [h_eq]
        rw [Finset.sum_insert (Finset.notMem_erase 0 s), h_val_zero, zero_add]
      }
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
        have h_sum : ∑ x ∈ insert 0 t, x.val = ∑ x ∈ t, x.val := by {
          rw [Finset.sum_insert ht_not_mem, h_val_zero, zero_add]
        }
        rw [h_sum]
        exact ht_sum
    · exact Finset.erase_insert ht_not_mem
}

/-- Conjecture 1: The Inclusion-Exclusion Property
A subset of Z_{n+1} either contains 0 or it doesn't.
Since adding 0 to a subset doesn't change its sum modulo n+1, we get a perfect recurrence relation. -/
theorem inclusion_exclusion (n k a : Nat) (hk : k > 0) :
  S n k a = T n k a + T n (k - 1) a := by {
  unfold S T
  have h_union := S_set_disjoint_union n k a
  have h_disjoint : Disjoint ((S_set n k a).filter (fun s => (0 : Fin (n + 1)) ∉ s)) ((S_set n k a).filter (fun s => (0 : Fin (n + 1)) ∈ s)) := by {
    rw [Finset.disjoint_iff_ne]
    intro x hx y hy h_eq
    simp only [mem_filter] at hx hy
    rw [h_eq] at hx
    exact hx.2 hy.2
  }
  rw [h_union, card_union_of_disjoint h_disjoint]
  rw [S_set_filter_not_mem_zero, S_set_filter_mem_zero_card n k a hk]
}

lemma fin_add_val_zmod {n : Nat} (x y : Fin (n + 1)) :
  (((x + y).val : Nat) : ZMod (n + 1)) = (x.val : ZMod (n + 1)) + (y.val : ZMod (n + 1)) := by {
  have h1 : (x + y).val = (x.val + y.val) % (n + 1) := Fin.val_add x y
  rw [h1]
  have h2 : (((x.val + y.val) % (n + 1) : Nat) : ZMod (n + 1)) = ((x.val + y.val : Nat) : ZMod (n + 1)) := by {
    exact ZMod.natCast_mod (x.val + y.val) (n + 1)
  }
  rw [h2]
  push_cast
  rfl
}

lemma fin_add_one_val_zmod {n : Nat} (x : Fin (n + 1)) :
  (((x + 1).val : Nat) : ZMod (n + 1)) = (x.val : ZMod (n + 1)) + 1 := by {
  have h := fin_add_val_zmod x 1
  rw [h]
  have h1 : (1 : Fin (n+1)).val = 1 % (n+1) := rfl
  rw [h1]
  have h2 : (((1 % (n+1) : Nat) : ZMod (n+1))) = ((1 : Nat) : ZMod (n+1)) := ZMod.natCast_mod 1 (n+1)
  rw [h2]
  push_cast
  rfl
}

def shift_subset {n : Nat} (s : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  s.map (Equiv.addRight (1 : Fin (n + 1))).toEmbedding

def unshift_subset {n : Nat} (s : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  s.map (Equiv.addRight (-1 : Fin (n + 1))).toEmbedding

lemma shift_subset_card {n : Nat} (s : Finset (Fin (n + 1))) :
  (shift_subset s).card = s.card := by {
  exact Finset.card_map _
}

lemma unshift_subset_card {n : Nat} (s : Finset (Fin (n + 1))) :
  (unshift_subset s).card = s.card := by {
  exact Finset.card_map _
}

lemma shift_unshift {n : Nat} (s : Finset (Fin (n + 1))) :
  shift_subset (unshift_subset s) = s := by {
  unfold shift_subset unshift_subset
  rw [Finset.map_map]
  have h : (Equiv.toEmbedding (Equiv.addRight (-1 : Fin (n + 1)))).trans (Equiv.toEmbedding (Equiv.addRight (1 : Fin (n + 1)))) = Function.Embedding.refl _ := by {
    ext x
    simp
  }
  rw [h, Finset.map_refl]
}

lemma unshift_shift {n : Nat} (s : Finset (Fin (n + 1))) :
  unshift_subset (shift_subset s) = s := by {
  unfold shift_subset unshift_subset
  rw [Finset.map_map]
  have h : (Equiv.toEmbedding (Equiv.addRight (1 : Fin (n + 1)))).trans (Equiv.toEmbedding (Equiv.addRight (-1 : Fin (n + 1)))) = Function.Embedding.refl _ := by {
    ext x
    simp
  }
  rw [h, Finset.map_refl]
}

lemma mod_add_cancel_right {a b k m : Nat} (h : (a + k) % m = (b + k) % m) : a % m = b % m := by {
  have h_zmod : ((a + k : Nat) : ZMod m) = ((b + k : Nat) : ZMod m) := by {
    exact (ZMod.natCast_eq_natCast_iff (a + k) (b + k) m).mpr h
  }
  push_cast at h_zmod
  have h_zmod2 : (a : ZMod m) = (b : ZMod m) := add_right_cancel h_zmod
  exact (ZMod.natCast_eq_natCast_iff a b m).mp h_zmod2
}

lemma shift_subset_sum {n : Nat} (s : Finset (Fin (n + 1))) :
  (∑ x ∈ shift_subset s, x.val) % (n + 1) = ((∑ x ∈ s, x.val) + s.card) % (n + 1) := by {
  apply (ZMod.natCast_eq_natCast_iff _ _ (n + 1)).mp
  push_cast
  unfold shift_subset
  rw [Finset.sum_map]
  have h_sum : (∑ a ∈ s, (((Equiv.toEmbedding (Equiv.addRight (1 : Fin (n + 1)))) a).val : ZMod (n + 1))) = ∑ a ∈ s, ((a.val : ZMod (n + 1)) + 1) := by {
    apply Finset.sum_congr rfl
    intro x hx
    change (((x + 1).val : Nat) : ZMod (n + 1)) = (x.val : ZMod (n + 1)) + 1
    exact fin_add_one_val_zmod x
  }
  rw [h_sum]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]
}

/-- Conjecture 2: The Cyclic Shift Bijection
If you take a subset of Z_{n+1} of size k and cyclically shift every element by +1,
the total sum of the subset strictly increases by exactly k modulo n+1. -/
theorem cyclic_shift_bijection (n k a : Nat) :
  S n k a = S n k (a + k) := by {
  unfold S
  apply Finset.card_bij (fun s _ => shift_subset s)
  · intro s hs
    simp only [mem_filter, S_set] at hs ⊢
    refine ⟨mem_univ _, ?_, ?_⟩
    · rw [shift_subset_card, hs.2.1]
    · have h_sum := shift_subset_sum s
      have h1 : (∑ x ∈ s, x.val) % (n + 1) = a % (n + 1) := hs.2.2
      have h2 : s.card = k := hs.2.1
      have h3 : ((∑ x ∈ s, x.val) + s.card) % (n + 1) = (a + k) % (n + 1) := by {
        rw [h2]
        have hm : ((∑ x ∈ s, x.val) + k) % (n + 1) = ((∑ x ∈ s, x.val) % (n + 1) + k % (n + 1)) % (n + 1) := Nat.add_mod _ _ _
        rw [hm, h1]
        exact (Nat.add_mod a k (n + 1)).symm
      }
      rw [h3] at h_sum
      exact h_sum
  · intro s1 hs1 s2 hs2 heq
    unfold shift_subset at heq
    exact Finset.map_injective _ heq
  · intro t ht
    use unshift_subset t
    simp only [mem_filter, S_set] at ht ⊢
    refine ⟨⟨mem_univ _, ?_, ?_⟩, shift_unshift t⟩
    · rw [unshift_subset_card, ht.2.1]
    · have h_sum := shift_subset_sum (unshift_subset t)
      rw [shift_unshift t, unshift_subset_card, ht.2.1] at h_sum
      have h1 : ((∑ x ∈ unshift_subset t, x.val) + k) % (n + 1) = (a + k) % (n + 1) := by {
        rw [← h_sum]
        exact ht.2.2
      }
      exact mod_add_cancel_right h1
}

lemma S_add_mul_k (n k a x : Nat) : S n k a = S n k (a + x * k) := by {
  induction x with
  | zero => simp
  | succ x ih =>
    rw [add_mul, one_mul]
    have h1 : a + (x * k + k) = (a + x * k) + k := by omega
    rw [h1]
    have h2 := cyclic_shift_bijection n k (a + x * k)
    rw [← h2]
    exact ih
}

lemma S_mod_eq (n k a b : Nat) (h : a % (n + 1) = b % (n + 1)) : S n k a = S n k b := by {
  unfold S S_set
  congr 1
  ext s
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.trans h⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.trans h.symm⟩
}

lemma coprime_exists_mul_add_eq (n k a b : Nat) (h_coprime : k.Coprime (n + 1)) :
  ∃ x : Nat, (a + x * k) % (n + 1) = b % (n + 1) := by {
  let u := ZMod.unitOfCoprime k h_coprime
  let k_inv := u⁻¹
  let x_val : ZMod (n + 1) := ((b : ZMod (n + 1)) - (a : ZMod (n + 1))) * k_inv
  use x_val.val
  have h_zmod : ((a + x_val.val * k : Nat) : ZMod (n + 1)) = (b : ZMod (n + 1)) := by {
    push_cast
    have hx : (x_val.val : ZMod (n + 1)) = x_val := ZMod.natCast_zmod_val x_val
    rw [hx]
    dsimp [x_val, k_inv]
    have hu : (k : ZMod (n + 1)) = ↑u := (ZMod.coe_unitOfCoprime k h_coprime).symm
    rw [hu]
    have h_mul : (((b : ZMod (n + 1)) - (a : ZMod (n + 1))) * ↑(u⁻¹)) * ↑u = (b : ZMod (n + 1)) - (a : ZMod (n + 1)) := by {
      rw [mul_assoc]
      simp
    }
    rw [h_mul]
    ring
  }
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h_zmod
}

/-- Conjecture 3: Uniformity of Coprimes
Because of the cyclic shift bijection, the values of S(k, a) trace out orbits of step size k.
If the subset size k is coprime to n+1, the orbit covers all possible residues,
so the subsets are perfectly uniformly distributed. -/
theorem uniformity_of_coprimes (n k a b : Nat) (h_coprime : k.Coprime (n + 1)) :
  S n k a = S n k b := by {
  obtain ⟨x, hx⟩ := coprime_exists_mul_add_eq n k a b h_coprime
  have h1 := S_add_mul_k n k a x
  have h2 := S_mod_eq n k (a + x * k) b hx
  rw [h1, h2]
}

lemma filter_range_two_step (n : Nat) (f : Nat → Nat) :
  ∑ j ∈ (range (n + 3)).filter (fun j => j % 2 = (n + 2) % 2), f j =
  (∑ j ∈ (range (n + 1)).filter (fun j => j % 2 = n % 2), f j) + f (n + 2) := by {
  have h_mod : (n + 2) % 2 = n % 2 := by omega
  have h_range : range (n + 3) = insert (n + 2) (insert (n + 1) (range (n + 1))) := by {
    ext x
    simp only [mem_range, mem_insert]
    omega
  }
  rw [h_range]
  rw [filter_insert, filter_insert]
  have h_n1 : ¬ ((n + 1) % 2 = (n + 2) % 2) := by omega
  have h_n2 : (n + 2) % 2 = (n + 2) % 2 := rfl
  rw [if_neg h_n1, if_pos h_n2]
  rw [sum_insert]
  · rw [h_mod]
    exact add_comm _ _
  · simp only [mem_filter, mem_range, not_and]
    intro h_lt h_eq
    omega
}

lemma filter_range_one_step_0 (f : Nat → Nat) :
  ∑ j ∈ (range 1).filter (fun j => j % 2 = 0), f j = f 0 := by {
  have hr : range 1 = {0} := rfl
  rw [hr, filter_singleton, if_pos (rfl : 0 % 2 = 0), sum_singleton]
}

lemma filter_range_one_step_1 (f : Nat → Nat) :
  ∑ j ∈ (range 2).filter (fun j => j % 2 = 1), f j = f 1 := by {
  have hr : range 2 = {0, 1} := rfl
  rw [hr]
  have h_filt : ({0, 1} : Finset Nat).filter (fun j => j % 2 = 1) = {1} := by {
    ext x
    simp only [mem_filter, mem_insert, mem_singleton]
    omega
  }
  rw [h_filt, sum_singleton]
}

lemma telescope_sum (S T : Nat → Nat) (h : ∀ k > 0, S k = T k + T (k - 1)) (h0 : S 0 = T 0) :
  ∀ n, ∑ k ∈ range (n + 1), T k = ∑ j ∈ (range (n + 1)).filter (fun j => j % 2 = n % 2), S j := by {
  intro n
  induction' n using Nat.twoStepInduction with n ih1 ih2
  · have h_rhs : ∑ j ∈ (range (0 + 1)).filter (fun j => j % 2 = 0 % 2), S j = S 0 := filter_range_one_step_0 S
    rw [h_rhs]
    simp [h0]
  · have h_rhs : ∑ j ∈ (range (1 + 1)).filter (fun j => j % 2 = 1 % 2), S j = S 1 := filter_range_one_step_1 S
    rw [h_rhs]
    have h_lhs : ∑ k ∈ range (1 + 1), T k = T 0 + T 1 := by {
      rw [sum_range_succ, sum_range_succ, range_zero, sum_empty, zero_add]
    }
    rw [h_lhs]
    have h1 : S 1 = T 1 + T 0 := h 1 (by omega)
    omega
  · rw [sum_range_succ, sum_range_succ, ih1]
    have hn2 : S (n + 2) = T (n + 2) + T (n + 1) := h (n + 2) (by omega)
    have h_filt := filter_range_two_step n S
    rw [h_filt]
    omega
}

lemma S_zero_eq_T_zero (n a : Nat) : S n 0 a = T n 0 a := by {
  unfold S T S_set T_set
  congr 1
  ext s
  simp only [mem_filter, mem_univ, true_and]
  apply Iff.intro
  · intro h
    refine ⟨h.1, ?_, h.2⟩
    have h_empty : s = ∅ := Finset.card_eq_zero.mp h.1
    rw [h_empty]
    simp
  · intro h
    exact ⟨h.1, h.2.2⟩
}

/-- Any binary string can be partitioned into subsets by its weight. -/
lemma vt_size_partition_by_wt (n a : Nat) :
  (Finset.VTCode n a).card = ∑ k ∈ Finset.Iic n, (Finset.filter (fun X => wt X = k) (Finset.VTCode n a)).card := by {
  have h_bUnion : Finset.VTCode n a = Finset.biUnion (Finset.Iic n) (fun k => Finset.filter (fun X => wt X = k) (Finset.VTCode n a)) := by {
    ext X
    simp only [mem_biUnion, mem_Iic, mem_filter]
    apply Iff.intro
    · intro hX
      use wt X
      refine ⟨Vector.wt_le_length X, hX, rfl⟩
    · intro h
      rcases h with ⟨k, _, hX, _⟩
      exact hX
  }
  have h_disj : Set.PairwiseDisjoint (↑(Finset.Iic n)) (fun k => Finset.filter (fun X => wt X = k) (Finset.VTCode n a)) := by {
    intro k1 _ k2 _ h_neq
    simp only [Function.onFun, disjoint_left, mem_filter]
    intro X ⟨_, h1⟩ ⟨_, h2⟩
    rw [h1] at h2
    exact h_neq h2
  }
  nth_rw 1 [h_bUnion]
  exact Finset.card_biUnion h_disj
}

open B List.Vector

def vector_to_subset (n : Nat) (X : List.Vector B n) : Finset (Fin (n + 1)) :=
  (Finset.univ).filter (fun (i : Fin (n + 1)) => i.val ≠ 0 ∧ X.val.getD (i.val - 1) B.O = B.I)

def subset_to_vector (n : Nat) (s : Finset (Fin (n + 1))) : List.Vector B n :=
  ⟨List.ofFn (fun (i : Fin n) => if Fin.mk (i.val + 1) (by omega) ∈ s then B.I else B.O), by simp⟩

#eval vector_to_subset 5 ⟨[B.O, B.I, B.O, B.I, B.I], rfl⟩
-- Evaluates to {2, 4, 5}
#eval subset_to_vector 5 {2, 4, 5}
-- Evaluates to ⟨[B.O, B.I, B.O, B.I, B.I], rfl⟩


def list_to_subset : List B → Finset Nat
| [] => ∅
| B.O :: X => (list_to_subset X).image (· + 1)
| B.I :: X => insert 1 ((list_to_subset X).image (· + 1))

lemma list_to_subset_not_zero (X : List B) :
  0 ∉ list_to_subset X := by {
  induction X with
  | nil =>
    exact Finset.not_mem_empty 0
  | cons x X' ih =>
    cases x
    · simp only [list_to_subset, mem_image, not_exists, not_and]
      intro a _ h_eq
      omega
    · simp only [list_to_subset, mem_insert, not_or, mem_image, not_exists, not_and]
      apply And.intro
      · omega
      · intro a _ h_eq
        omega
}

lemma list_to_subset_sum (X : List B) :
  ∑ i ∈ list_to_subset X, i = List.moment X := by {
  induction X with
  | nil => rfl
  | cons x X' ih =>
    have h_inj : Set.InjOn (· + 1) ↑(list_to_subset X') := by {
      intro a _ b _ hab
      exact Nat.add_right_cancel hab
    }
    have h_sum_add : ∑ i ∈ (list_to_subset X').image (· + 1), i = (∑ i ∈ list_to_subset X', i) + (list_to_subset X').card := by {
      rw [Finset.sum_image h_inj]
      simp only [sum_add_distrib, sum_const, nsmul_eq_mul, mul_one]
    }
    cases x
    · change ∑ i ∈ (list_to_subset X').image (· + 1), i = List.moment (B.O :: X')
      rw [h_sum_add, ih, list_to_subset_card X']
      have h_mom := moment_cons B.O X'
      have h_num : num_Is (B.O :: X') = num_Is X' := rfl
      rw [h_num] at h_mom
      exact h_mom.symm
    · change (∑ i ∈ insert 1 ((list_to_subset X').image (· + 1)), i) = List.moment (B.I :: X')
      have h_not_mem : 1 ∉ (list_to_subset X').image (· + 1) := by {
        simp only [mem_image, not_exists, not_and]
        intro a ha h_eq
        have ha_zero : a = 0 := by omega
        rw [ha_zero] at ha
        have hz := list_to_subset_not_zero X'
        exact hz ha
      }
      rw [Finset.sum_insert h_not_mem]
      rw [h_sum_add, ih, list_to_subset_card X']
      have h_mom := moment_cons B.I X'
      have h_num : num_Is (B.I :: X') = num_Is X' + 1 := rfl
      rw [h_num] at h_mom
      omega
}

lemma vector_to_subset_sum (n : Nat) (X : List.Vector B n) :
  (∑ x ∈ vector_to_subset n X, x.val) % (n + 1) = (moment X) % (n + 1) := by {
  have h_inj : Set.InjOn (@Fin.val (n + 1)) ↑(vector_to_subset n X) := by {
    intro a _ b _ hab
    exact Fin.ext hab
  }
  have h_sum := Finset.sum_image h_inj (g := id)
  simp only [id_eq] at h_sum
  have h_sum_eq : ∑ x ∈ vector_to_subset n X, x.val = ∑ x ∈ (vector_to_subset n X).image Fin.val, x := by {
    exact h_sum.symm
  }
  rw [h_sum_eq, vector_to_subset_eq_list_subset n X]
  rw [list_to_subset_sum X.val]
  rfl
}

lemma list_to_subset_card (X : List B) :
  (list_to_subset X).card = List.num_Is X := by {
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · change ((list_to_subset X').image (· + 1)).card = List.num_Is X'
      have h_inj : Set.InjOn (· + 1) ↑(list_to_subset X') := by {
        intro a _ b _ hab
        exact Nat.add_right_cancel hab
      }
      rw [Finset.card_image_of_injOn h_inj, ih]
    · change (insert 1 ((list_to_subset X').image (· + 1))).card = List.num_Is X' + 1
      have h_not_mem : 1 ∉ (list_to_subset X').image (· + 1) := by {
        simp only [mem_image, not_exists, not_and]
        intro a ha h_eq
        have ha_zero : a = 0 := by omega
        rw [ha_zero] at ha
        have hz := list_to_subset_not_zero X'
        exact hz ha
      }
      rw [Finset.card_insert_of_notMem h_not_mem]
      have h_inj : Set.InjOn (· + 1) ↑(list_to_subset X') := by {
        intro a _ b _ hab
        exact Nat.add_right_cancel hab
      }
      rw [Finset.card_image_of_injOn h_inj, ih]
}

lemma mem_list_to_subset (X : List B) (i : Nat) :
  i ∈ list_to_subset X ↔ i ≠ 0 ∧ i ≤ X.length ∧ X.getD (i - 1) B.O = B.I := by {
  induction X generalizing i with
  | nil =>
    simp only [list_to_subset, List.length_nil, nonpos_iff_eq_zero, false_and, and_false]
    exact Iff.intro (fun h => (Finset.not_mem_empty i h).elim) (fun h => h.1.elim)
  | cons x X' ih =>
    cases x
    · apply Iff.intro
      · intro h
        rw [list_to_subset] at h
        simp only [mem_image] at h
        rcases h with ⟨a, ha, rfl⟩
        rw [ih a] at ha
        refine ⟨by omega, by omega, ?_⟩
        have ha_sub : a + 1 - 1 = a := by omega
        rw [ha_sub]
        cases a
        · omega
        · exact ha.2.2
      · intro ⟨h1, h2, h3⟩
        rw [list_to_subset]
        simp only [mem_image]
        use i - 1
        have hi_sub : i - 1 + 1 = i := by omega
        refine ⟨?_, hi_sub⟩
        rw [ih (i - 1)]
        refine ⟨by omega, by omega, ?_⟩
        cases i
        · omega
        case succ k =>
          have hk_sub : k + 1 - 1 = k := by omega
          rw [hk_sub] at h3
          exact h3
    · apply Iff.intro
      · intro h
        rw [list_to_subset] at h
        simp only [mem_insert, mem_image] at h
        cases h with
        | inl heq =>
          rw [heq]
          refine ⟨by omega, by omega, rfl⟩
        | inr h_img =>
          rcases h_img with ⟨a, ha, rfl⟩
          rw [ih a] at ha
          refine ⟨by omega, by omega, ?_⟩
          cases a
          · omega
          · exact ha.2.2
      · intro ⟨h1, h2, h3⟩
        rw [list_to_subset]
        simp only [mem_insert, mem_image]
        cases i
        · omega
        case succ k =>
          cases k
          · left; rfl
          · right
            use k + 1
            have hk_sub : k + 1 + 1 = k + 2 := by omega
            refine ⟨?_, hk_sub⟩
            rw [ih (k + 1)]
            refine ⟨by omega, by omega, ?_⟩
            exact h3
}

lemma vector_to_subset_eq_list_subset (n : Nat) (X : List.Vector B n) :
  (vector_to_subset n X).image Fin.val = list_to_subset X.val := by {
  ext i
  simp only [vector_to_subset, mem_image, mem_filter, mem_univ, true_and]
  rw [mem_list_to_subset]
  apply Iff.intro
  · rintro ⟨a, ⟨ha1, ha2⟩, rfl⟩
    have ha_lt := a.isLt
    have hX_len := X.property
    refine ⟨ha1, by omega, ha2⟩
  · rintro ⟨h1, h2, h3⟩
    have hX_len := X.property
    have hi_lt : i < n + 1 := by omega
    use ⟨i, hi_lt⟩
    refine ⟨⟨h1, h3⟩, rfl⟩
}

lemma vector_to_subset_card (n : Nat) (X : List.Vector B n) :
  (vector_to_subset n X).card = wt X := by {
  have h_inj : Set.InjOn (@Fin.val (n + 1)) ↑(vector_to_subset n X) := by {
    intro a _ b _ hab
    exact Fin.ext hab
  }
  have h_card := Finset.card_image_of_injOn h_inj
  rw [vector_to_subset_eq_list_subset n X] at h_card
  rw [← h_card, list_to_subset_card]
  rfl
}

lemma vector_to_subset_sum (n : Nat) (X : List.Vector B n) :
  (vector_to_subset n X).sum (fun i => i.val) = List.Vector.moment X := by {
  sorry
}

/-- The number of VT codewords of weight k exactly equals the number of subsets of {1..n}
    of size k that sum to a (which is T_set). -/
lemma vt_wt_eq_T (n a k : Nat) :
  (Finset.filter (fun X => wt X = k) (Finset.VTCode n a)).card = T n k a := by {
  unfold T
  apply Finset.card_bij (fun X _ => vector_to_subset n X)
  · intro X hX
    simp only [mem_filter, Finset.mem_VTCode, _root_.mem_VTCode] at hX
    have h_wt : wt X = k := hX.2
    have h_mom : List.Vector.moment X % (n + 1) = a % (n + 1) := hX.1
    simp only [T_set, mem_filter, mem_univ, true_and]
    refine ⟨?_, ?_, ?_⟩
    · rw [vector_to_subset_card]
      exact h_wt
    · intro h_zero
      simp only [vector_to_subset, mem_filter, mem_univ, true_and] at h_zero
      have h_not : (0 : Fin (n + 1)).val ≠ 0 := h_zero.1
      contradiction
    · rw [vector_to_subset_sum]
      exact h_mom
  · -- Injectivity
    intro X hX Y hY h_eq
    apply Subtype.ext
    have hX_len := X.property
    have hY_len := Y.property
    apply List.ext_get
    · rw [hX_len, hY_len]
    · intro i h1 h2
      have hin : i < n := by omega
      have h_fin : (Fin.mk (i + 1) (by omega) : Fin (n + 1)) ∈ vector_to_subset n X ↔ (Fin.mk (i + 1) (by omega) : Fin (n + 1)) ∈ vector_to_subset n Y := by {
        rw [h_eq]
      }
      unfold vector_to_subset at h_fin
      simp only [mem_filter, mem_univ, true_and] at h_fin
      have hi_neq : i + 1 ≠ 0 := by omega
      have hi_sub : i + 1 - 1 = i := by omega
      have hX_eq : X.val.getD i B.O = X.val.get ⟨i, h1⟩ := by {
        have h := List.getD_eq_getElem X.val (d := B.O) h1
        exact h
      }
      have hY_eq : Y.val.getD i B.O = Y.val.get ⟨i, h2⟩ := by {
        have h := List.getD_eq_getElem Y.val (d := B.O) h2
        exact h
      }
      have h_fin2 : ((i + 1 ≠ 0) ∧ X.val.getD i B.O = B.I) ↔ ((i + 1 ≠ 0) ∧ Y.val.getD i B.O = B.I) := by {
        have h_subX : (Fin.mk (i + 1) (by omega) : Fin (n + 1)).val - 1 = i := hi_sub
        rw [h_subX] at h_fin
        exact h_fin
      }
      rw [hX_eq, hY_eq] at h_fin2
      have h_iff : X.val.get ⟨i, h1⟩ = B.I ↔ Y.val.get ⟨i, h2⟩ = B.I := by {
        apply Iff.intro
        · intro hX
          exact (h_fin2.mp ⟨hi_neq, hX⟩).right
        · intro hY
          exact (h_fin2.mpr ⟨hi_neq, hY⟩).right
      }
      cases hX_val : X.val.get ⟨i, h1⟩ <;> cases hY_val : Y.val.get ⟨i, h2⟩
      · rfl
      · have h_false := h_iff.mpr hY_val
        rw [hX_val] at h_false
        contradiction
      · have h_false := h_iff.mp hX_val
        rw [hY_val] at h_false
        contradiction
      · rfl
  · -- Surjectivity
    intro s hs
    simp only [T_set, mem_filter, mem_univ, true_and] at hs
    use subset_to_vector n s
    have hs_card : s.card = k := hs.1
    have hs_not_zero : (0 : Fin (n + 1)) ∉ s := hs.2.1
    have hs_sum : (∑ x ∈ s, x.val) % (n + 1) = a % (n + 1) := hs.2.2
    
    have h_eq : vector_to_subset n (subset_to_vector n s) = s := by {
      ext i
      simp only [vector_to_subset, subset_to_vector, mem_filter, mem_univ, true_and]
      apply Iff.intro
      · rintro ⟨hi_not_zero, hi_get⟩
        have hi_sub : i.val - 1 < n := by {
          have h_lt : i.val < n + 1 := i.isLt
          omega
        }
        have hi_sub_eq : i.val - 1 + 1 = i.val := by omega
        have h_len : (List.ofFn fun (i_1 : Fin n) => if (Fin.mk (i_1.val + 1) (by omega) : Fin (n + 1)) ∈ s then B.I else B.O).length = n := by simp
        have h_idx : i.val - 1 < (List.ofFn fun (i_1 : Fin n) => if (Fin.mk (i_1.val + 1) (by omega) : Fin (n + 1)) ∈ s then B.I else B.O).length := by {
          rw [h_len]
          exact hi_sub
        }
        have h_get := hi_get
        rw [List.getD_eq_getElem _ _ h_idx] at h_get
        rw [List.getElem_ofFn] at h_get
        dsimp at h_get
        have h_idx_eq : (Fin.mk (i.val - 1 + 1) (by omega) : Fin (n + 1)).val = i.val := hi_sub_eq
        have h_fin_eq : (Fin.mk (i.val - 1 + 1) (by omega) : Fin (n + 1)) = i := Fin.ext h_idx_eq
        rw [h_fin_eq] at h_get
        split at h_get
        · assumption
        · contradiction
      · intro hi
        have hi_not_zero : i.val ≠ 0 := by {
          intro h_zero
          have h_eq : i = 0 := Fin.ext h_zero
          rw [h_eq] at hi
          exact hs_not_zero hi
        }
        refine ⟨hi_not_zero, ?_⟩
        have hi_sub : i.val - 1 < n := by {
          have h_lt : i.val < n + 1 := i.isLt
          omega
        }
        have hi_sub_eq : i.val - 1 + 1 = i.val := by omega
        have h_len : (List.ofFn fun (i_1 : Fin n) => if (Fin.mk (i_1.val + 1) (by omega) : Fin (n + 1)) ∈ s then B.I else B.O).length = n := by simp
        have h_idx : i.val - 1 < (List.ofFn fun (i_1 : Fin n) => if (Fin.mk (i_1.val + 1) (by omega) : Fin (n + 1)) ∈ s then B.I else B.O).length := by {
          rw [h_len]
          exact hi_sub
        }
        rw [List.getD_eq_getElem _ _ h_idx]
        rw [List.getElem_ofFn]
        dsimp
        have h_idx_eq : (Fin.mk (i.val - 1 + 1) (by omega) : Fin (n + 1)).val = i.val := hi_sub_eq
        have h_fin_eq : (Fin.mk (i.val - 1 + 1) (by omega) : Fin (n + 1)) = i := Fin.ext h_idx_eq
        rw [h_fin_eq]
        rw [if_pos hi]
    }
    
    refine ⟨?_, h_eq⟩
    simp only [mem_filter, Finset.mem_VTCode, _root_.mem_VTCode]
    refine ⟨?_, ?_⟩
    · rw [← vector_to_subset_sum, h_eq]
      exact hs_sum
    · rw [← vector_to_subset_card, h_eq]
      exact hs_card
}

/-- Helper for Conjecture 4: The total size of the VT code is exactly the sum of
all subsets of non-zero elements that sum to `a` (which is T).
This maps binary VT strings of weight k to subsets of size k. -/
theorem vt_size_eq_sum_T (n a : Nat) :
  (Finset.VTCode n a).card = ∑ k ∈ Finset.Iic n, T n k a := by {
  rw [vt_size_partition_by_wt]
  apply sum_congr rfl
  intro k _
  exact vt_wt_eq_T n a k
}

/-- Conjecture 4: Telescoping to VT Size
Using the relation T(k, a) = S(k, a) - T(k-1, a), we can expand the VT size summation.
The entire size of the VT code telescopes down to depending strictly on the subsets
of Z_{n+1}, specifically where the size has the same parity as n. -/
theorem vt_size_telescoping (n a : Nat) :
  (Finset.VTCode n a).card = ∑ j ∈ (Finset.Iic n).filter (fun j => j % 2 = n % 2), S n j a := by {
  rw [vt_size_eq_sum_T]
  have h_Iic : Finset.Iic n = range (n + 1) := by {
    ext x
    simp only [mem_Iic, mem_range]
    omega
  }
  rw [h_Iic]
  apply telescope_sum (S n · a) (T n · a)
  · intro k hk
    exact inclusion_exclusion n k a hk
  · exact S_zero_eq_T_zero n a
}

/-- Absolute Optimality via the Hybrid Path
We established that `|VTCode|` decomposes purely into subset sums `S n j a` (Conjecture 4).
However, for `gcd(j, n+1) > 1`, the combinatorial counting of orbits is severely entangled.
Therefore, we hybridize: we import the Complex Polynomial evaluation of the overall sizes
from `Cuculiere.lean` which rigorously proves `cuculiere_mod_sum_gen_max`, yielding this result. -/
theorem absolute_optimality (n a : Nat) :
  (Finset.VTCode n a).card ≤ (Finset.VTCode n 0).card := by {
  exact VTCode_zero_is_max n a
}
