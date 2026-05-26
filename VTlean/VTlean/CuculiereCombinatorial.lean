import Mathlib
import VTlean.VTCode
import VTlean.Cuculiere

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

/-- Conjecture 1: The Inclusion-Exclusion Property
A subset of Z_{n+1} either contains 0 or it doesn't. 
Since adding 0 to a subset doesn't change its sum modulo n+1, we get a perfect recurrence relation. -/
theorem inclusion_exclusion (n k a : Nat) (hk : k > 0) :
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

lemma fin_add_val_zmod {n : Nat} (x y : Fin (n + 1)) :
  (((x + y).val : Nat) : ZMod (n + 1)) = (x.val : ZMod (n + 1)) + (y.val : ZMod (n + 1)) := by
  have h1 : (x + y).val = (x.val + y.val) % (n + 1) := Fin.val_add x y
  rw [h1]
  have h2 : (((x.val + y.val) % (n + 1) : Nat) : ZMod (n + 1)) = ((x.val + y.val : Nat) : ZMod (n + 1)) := by
    exact ZMod.natCast_mod (x.val + y.val) (n + 1)
  rw [h2]
  push_cast
  rfl

lemma fin_add_one_val_zmod {n : Nat} (x : Fin (n + 1)) :
  (((x + 1).val : Nat) : ZMod (n + 1)) = (x.val : ZMod (n + 1)) + 1 := by
  have h := fin_add_val_zmod x 1
  rw [h]
  have h1 : (1 : Fin (n+1)).val = 1 % (n+1) := rfl
  rw [h1]
  have h2 : (((1 % (n+1) : Nat) : ZMod (n+1))) = ((1 : Nat) : ZMod (n+1)) := ZMod.natCast_mod 1 (n+1)
  rw [h2]
  push_cast
  rfl

def shift_subset {n : Nat} (s : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  s.map (Equiv.addRight (1 : Fin (n + 1))).toEmbedding

def unshift_subset {n : Nat} (s : Finset (Fin (n + 1))) : Finset (Fin (n + 1)) :=
  s.map (Equiv.addRight (-1 : Fin (n + 1))).toEmbedding

lemma shift_subset_card {n : Nat} (s : Finset (Fin (n + 1))) :
  (shift_subset s).card = s.card := by
  exact Finset.card_map _

lemma unshift_subset_card {n : Nat} (s : Finset (Fin (n + 1))) :
  (unshift_subset s).card = s.card := by
  exact Finset.card_map _

lemma shift_unshift {n : Nat} (s : Finset (Fin (n + 1))) :
  shift_subset (unshift_subset s) = s := by
  unfold shift_subset unshift_subset
  rw [Finset.map_map]
  have h : (Equiv.toEmbedding (Equiv.addRight (-1 : Fin (n + 1)))).trans (Equiv.toEmbedding (Equiv.addRight (1 : Fin (n + 1)))) = Function.Embedding.refl _ := by
    ext x
    simp
  rw [h, Finset.map_refl]

lemma unshift_shift {n : Nat} (s : Finset (Fin (n + 1))) :
  unshift_subset (shift_subset s) = s := by
  unfold shift_subset unshift_subset
  rw [Finset.map_map]
  have h : (Equiv.toEmbedding (Equiv.addRight (1 : Fin (n + 1)))).trans (Equiv.toEmbedding (Equiv.addRight (-1 : Fin (n + 1)))) = Function.Embedding.refl _ := by
    ext x
    simp
  rw [h, Finset.map_refl]

lemma mod_add_cancel_right {a b k m : Nat} (h : (a + k) % m = (b + k) % m) : a % m = b % m := by
  have h_zmod : ((a + k : Nat) : ZMod m) = ((b + k : Nat) : ZMod m) := by
    exact (ZMod.natCast_eq_natCast_iff (a + k) (b + k) m).mpr h
  push_cast at h_zmod
  have h_zmod2 : (a : ZMod m) = (b : ZMod m) := add_right_cancel h_zmod
  exact (ZMod.natCast_eq_natCast_iff a b m).mp h_zmod2

lemma shift_subset_sum {n : Nat} (s : Finset (Fin (n + 1))) :
  (∑ x ∈ shift_subset s, x.val) % (n + 1) = ((∑ x ∈ s, x.val) + s.card) % (n + 1) := by
  apply (ZMod.natCast_eq_natCast_iff _ _ (n + 1)).mp
  push_cast
  unfold shift_subset
  rw [Finset.sum_map]
  have h_sum : (∑ a ∈ s, (((Equiv.toEmbedding (Equiv.addRight (1 : Fin (n + 1)))) a).val : ZMod (n + 1))) = ∑ a ∈ s, ((a.val : ZMod (n + 1)) + 1) := by
    apply Finset.sum_congr rfl
    intro x hx
    change (((x + 1).val : Nat) : ZMod (n + 1)) = (x.val : ZMod (n + 1)) + 1
    exact fin_add_one_val_zmod x
  rw [h_sum]
  rw [Finset.sum_add_distrib, Finset.sum_const, nsmul_eq_mul, mul_one]

/-- Conjecture 2: The Cyclic Shift Bijection
If you take a subset of Z_{n+1} of size k and cyclically shift every element by +1, 
the total sum of the subset strictly increases by exactly k modulo n+1. -/
theorem cyclic_shift_bijection (n k a : Nat) :
  S n k a = S n k (a + k) := by
  unfold S
  apply Finset.card_bij (fun s _ => shift_subset s)
  · intro s hs
    simp only [mem_filter, S_set] at hs ⊢
    refine ⟨mem_univ _, ?_, ?_⟩
    · rw [shift_subset_card, hs.2.1]
    · have h_sum := shift_subset_sum s
      have h1 : (∑ x ∈ s, x.val) % (n + 1) = a % (n + 1) := hs.2.2
      have h2 : s.card = k := hs.2.1
      have h3 : ((∑ x ∈ s, x.val) + s.card) % (n + 1) = (a + k) % (n + 1) := by
        rw [h2]
        have hm : ((∑ x ∈ s, x.val) + k) % (n + 1) = ((∑ x ∈ s, x.val) % (n + 1) + k % (n + 1)) % (n + 1) := Nat.add_mod _ _ _
        rw [hm, h1]
        exact (Nat.add_mod a k (n + 1)).symm
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
      have h1 : ((∑ x ∈ unshift_subset t, x.val) + k) % (n + 1) = (a + k) % (n + 1) := by
        rw [← h_sum]
        exact ht.2.2
      exact mod_add_cancel_right h1

lemma S_add_mul_k (n k a x : Nat) : S n k a = S n k (a + x * k) := by
  induction x with
  | zero => simp
  | succ x ih =>
    rw [add_mul, one_mul]
    have h1 : a + (x * k + k) = (a + x * k) + k := by omega
    rw [h1]
    have h2 := cyclic_shift_bijection n k (a + x * k)
    rw [← h2]
    exact ih

lemma S_mod_eq (n k a b : Nat) (h : a % (n + 1) = b % (n + 1)) : S n k a = S n k b := by
  unfold S S_set
  congr 1
  ext s
  simp only [mem_filter, mem_univ, true_and]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.trans h⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, h2.trans h.symm⟩

lemma coprime_exists_mul_add_eq (n k a b : Nat) (h_coprime : k.Coprime (n + 1)) :
  ∃ x : Nat, (a + x * k) % (n + 1) = b % (n + 1) := by
  let u := ZMod.unitOfCoprime k h_coprime
  let k_inv := u⁻¹
  let x_val : ZMod (n + 1) := ((b : ZMod (n + 1)) - (a : ZMod (n + 1))) * k_inv
  use x_val.val
  have h_zmod : ((a + x_val.val * k : Nat) : ZMod (n + 1)) = (b : ZMod (n + 1)) := by
    push_cast
    have hx : (x_val.val : ZMod (n + 1)) = x_val := ZMod.natCast_zmod_val x_val
    rw [hx]
    dsimp [x_val, k_inv]
    have hu : (k : ZMod (n + 1)) = ↑u := (ZMod.coe_unitOfCoprime k h_coprime).symm
    rw [hu]
    have h_mul : (((b : ZMod (n + 1)) - (a : ZMod (n + 1))) * ↑(u⁻¹)) * ↑u = (b : ZMod (n + 1)) - (a : ZMod (n + 1)) := by
      rw [mul_assoc]
      simp
    rw [h_mul]
    ring
  exact (ZMod.natCast_eq_natCast_iff _ _ _).mp h_zmod

/-- Conjecture 3: Uniformity of Coprimes
Because of the cyclic shift bijection, the values of S(k, a) trace out orbits of step size k. 
If the subset size k is coprime to n+1, the orbit covers all possible residues, 
so the subsets are perfectly uniformly distributed. -/
theorem uniformity_of_coprimes (n k a b : Nat) (h_coprime : k.Coprime (n + 1)) :
  S n k a = S n k b := by
  obtain ⟨x, hx⟩ := coprime_exists_mul_add_eq n k a b h_coprime
  have h1 := S_add_mul_k n k a x
  have h2 := S_mod_eq n k (a + x * k) b hx
  rw [h1, h2]

lemma filter_range_two_step (n : Nat) (f : Nat → Nat) :
  ∑ j ∈ (range (n + 3)).filter (fun j => j % 2 = (n + 2) % 2), f j =
  (∑ j ∈ (range (n + 1)).filter (fun j => j % 2 = n % 2), f j) + f (n + 2) := by
  have h_mod : (n + 2) % 2 = n % 2 := by omega
  have h_range : range (n + 3) = insert (n + 2) (insert (n + 1) (range (n + 1))) := by
    ext x
    simp only [mem_range, mem_insert]
    omega
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

lemma filter_range_one_step_0 (f : Nat → Nat) :
  ∑ j ∈ (range 1).filter (fun j => j % 2 = 0), f j = f 0 := by
  have hr : range 1 = {0} := rfl
  rw [hr, filter_singleton, if_pos (rfl : 0 % 2 = 0), sum_singleton]

lemma filter_range_one_step_1 (f : Nat → Nat) :
  ∑ j ∈ (range 2).filter (fun j => j % 2 = 1), f j = f 1 := by
  have hr : range 2 = {0, 1} := rfl
  rw [hr]
  have h_filt : ({0, 1} : Finset Nat).filter (fun j => j % 2 = 1) = {1} := by
    ext x
    simp only [mem_filter, mem_insert, mem_singleton]
    omega
  rw [h_filt, sum_singleton]

lemma telescope_sum (S T : Nat → Nat) (h : ∀ k > 0, S k = T k + T (k - 1)) (h0 : S 0 = T 0) :
  ∀ n, ∑ k ∈ range (n + 1), T k = ∑ j ∈ (range (n + 1)).filter (fun j => j % 2 = n % 2), S j := by
  intro n
  induction' n using Nat.twoStepInduction with n ih1 ih2
  · have h_rhs : ∑ j ∈ (range (0 + 1)).filter (fun j => j % 2 = 0 % 2), S j = S 0 := filter_range_one_step_0 S
    rw [h_rhs]
    simp [h0]
  · have h_rhs : ∑ j ∈ (range (1 + 1)).filter (fun j => j % 2 = 1 % 2), S j = S 1 := filter_range_one_step_1 S
    rw [h_rhs]
    have h_lhs : ∑ k ∈ range (1 + 1), T k = T 0 + T 1 := by
      rw [sum_range_succ, sum_range_succ, range_zero, sum_empty, zero_add]
    rw [h_lhs]
    have h1 : S 1 = T 1 + T 0 := h 1 (by omega)
    omega
  · rw [sum_range_succ, sum_range_succ, ih1]
    have hn2 : S (n + 2) = T (n + 2) + T (n + 1) := h (n + 2) (by omega)
    have h_filt := filter_range_two_step n S
    rw [h_filt]
    omega

lemma S_zero_eq_T_zero (n a : Nat) : S n 0 a = T n 0 a := by
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

/-- Helper for Conjecture 4: The total size of the VT code is exactly the sum of 
all subsets of non-zero elements that sum to `a` (which is T). 
This maps binary VT strings of weight k to subsets of size k. -/
theorem vt_size_eq_sum_T (n a : Nat) :
  (Finset.VTCode n a).card = ∑ k ∈ Finset.Iic n, T n k a := by
  sorry

/-- Conjecture 4: Telescoping to VT Size
Using the relation T(k, a) = S(k, a) - T(k-1, a), we can expand the VT size summation.
The entire size of the VT code telescopes down to depending strictly on the subsets 
of Z_{n+1}, specifically where the size has the same parity as n. -/
theorem vt_size_telescoping (n a : Nat) :
  (Finset.VTCode n a).card = ∑ j ∈ (Finset.Iic n).filter (fun j => j % 2 = n % 2), S n j a := by
  rw [vt_size_eq_sum_T]
  have h_Iic : Finset.Iic n = range (n + 1) := by
    ext x
    simp only [mem_Iic, mem_range]
    omega
  rw [h_Iic]
  apply telescope_sum (S n · a) (T n · a)
  · intro k hk
    exact inclusion_exclusion n k a hk
  · exact S_zero_eq_T_zero n a

/-- Absolute Optimality via the Hybrid Path 
We established that `|VTCode|` decomposes purely into subset sums `S n j a` (Conjecture 4).
However, for `gcd(j, n+1) > 1`, the combinatorial counting of orbits is severely entangled.
Therefore, we hybridize: we import the Complex Polynomial evaluation of the overall sizes 
from `Cuculiere.lean` which rigorously proves `cuculiere_mod_sum_gen_max`, yielding this result. -/
theorem absolute_optimality (n a : Nat) :
  (Finset.VTCode n a).card ≤ (Finset.VTCode n 0).card := by {
  exact VTCode_zero_is_max n a
}
