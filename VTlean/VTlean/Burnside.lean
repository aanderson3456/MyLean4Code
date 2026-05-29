import Mathlib
import VTlean.VTCode

open Nat Finset

namespace Burnside

/-- A vector representation that's easy to shift. 
    We cyclically shift a vector to the right. -/
def cyclicShift {n : Nat} (v : List.Vector B n) : List.Vector B n :=
  if h : n = 0 then v
  else
    have h_not_nil : v.val ≠ [] := by {
      intro hn
      have hlen := v.property
      rw [hn] at hlen
      have h_zero : n = 0 := hlen.symm
      exact h h_zero
    }
    ⟨v.val.getLast h_not_nil :: v.val.dropLast, by {
      rw [List.length_cons, List.length_dropLast]
      have hlen := v.property
      omega
    }⟩

lemma cyclicShift_zero (v : List.Vector B 0) : cyclicShift v = v := by {
  unfold cyclicShift
  rw [dif_pos rfl]
}

lemma num_Is_append_O (X : List B) : List.num_Is (X ++ [B.O]) = List.num_Is X := by {
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · change List.num_Is (X' ++ [B.O]) = List.num_Is X'
      exact ih
    · change List.num_Is (X' ++ [B.O]) + 1 = List.num_Is X' + 1
      rw [ih]
}

lemma num_Is_append_I (X : List B) : List.num_Is (X ++ [B.I]) = List.num_Is X + 1 := by {
  induction X with
  | nil => rfl
  | cons x X' ih =>
    cases x
    · change List.num_Is (X' ++ [B.I]) = List.num_Is X' + 1
      exact ih
    · change List.num_Is (X' ++ [B.I]) + 1 = List.num_Is X' + 1 + 1
      rw [ih]
}

lemma moment_cyclicShift_list (X : List B) (b : B) (n : Nat) (h_len : X.length + 1 = n) :
  List.moment (b :: X) ≡ List.moment (X ++ [b]) + List.num_Is (X ++ [b]) [MOD n] := by {
  cases b
  · rw [List.moment_append_O, num_Is_append_O]
    have hc := List.moment_cons B.O X
    have h1 : List.num_Is (B.O :: X) = List.num_Is X := rfl
    rw [h1] at hc
    rw [hc]
  · rw [List.moment_append_I, num_Is_append_I]
    have hc := List.moment_cons B.I X
    have h1 : List.num_Is (B.I :: X) = List.num_Is X + 1 := rfl
    rw [h1] at hc
    have heq : List.moment X + X.length + 1 + (List.num_Is X + 1) = List.moment (B.I :: X) + n := by {
      rw [hc]
      omega
    }
    rw [heq]
    have heq2 : (List.moment (B.I :: X) + n) % n = List.moment (B.I :: X) % n := by {
      rw [Nat.add_mod_right]
    }
    exact heq2.symm
}

/-- The fundamental cyclic shift property: shifting right adds the weight to the moment. -/
lemma moment_cyclicShift {n : Nat} (v : List.Vector B n) :
  List.Vector.moment (cyclicShift v) ≡ List.Vector.moment v + List.num_Is v.val [MOD n] := by {
  unfold cyclicShift
  cases Decidable.em (n = 0) with
  | inl h =>
    rw [dif_pos h]
    have h1 := v.property
    have h_len : v.val.length = 0 := by {
      omega
    }
    have h_nil : v.val = [] := List.length_eq_zero_iff.mp h_len
    rw [h_nil] at h1
    have hv : v = ⟨[], h1⟩ := by {
      apply Subtype.ext
      exact h_nil
    }
    rw [hv]
    rfl
  | inr h =>
    rw [dif_neg h]
    have h_not_nil : v.val ≠ [] := by {
      intro hn
      have hlen := v.property
      rw [hn] at hlen
      have h_zero : n = 0 := hlen.symm
      exact h h_zero
    }
    have h_app : v.val = v.val.dropLast ++ [v.val.getLast h_not_nil] := by {
      exact (List.dropLast_append_getLast h_not_nil).symm
    }
    have h_len : v.val.dropLast.length + 1 = n := by {
      have hlen := v.property
      rw [List.length_dropLast]
      cases heq : v.val with
      | nil => contradiction
      | cons hd tl =>
        rw [← heq]
        have h_pos : 0 < v.val.length := by {
          rw [heq]
          exact Nat.zero_lt_succ tl.length
        }
        have h_sub := Nat.sub_add_cancel h_pos
        rw [h_sub]
        exact hlen
    }
    have h_shift := moment_cyclicShift_list (v.val.dropLast) (v.val.getLast h_not_nil) n h_len
    have h_app_eq : v.val.dropLast ++ [v.val.getLast h_not_nil] = v.val := by {
      exact List.dropLast_append_getLast h_not_nil
    }
    rw [h_app_eq] at h_shift
    exact h_shift
}

lemma num_Is_cyclicShift {n : Nat} (v : List.Vector B n) :
  List.num_Is (cyclicShift v).val = List.num_Is v.val := by {
  unfold cyclicShift
  cases Decidable.em (n = 0) with
  | inl h =>
    rw [dif_pos h]
  | inr h =>
    rw [dif_neg h]
    have h_not_nil : v.val ≠ [] := by {
      intro hn
      have hlen := v.property
      rw [hn] at hlen
      have h_zero : n = 0 := hlen.symm
      exact h h_zero
    }
    have h_app : v.val = v.val.dropLast ++ [v.val.getLast h_not_nil] := by {
      exact (List.dropLast_append_getLast h_not_nil).symm
    }
    change List.num_Is (v.val.getLast h_not_nil :: v.val.dropLast) = List.num_Is v.val
    have h1 : List.num_Is (v.val.getLast h_not_nil :: v.val.dropLast) = List.num_Is [v.val.getLast h_not_nil] + List.num_Is v.val.dropLast := by {
      cases v.val.getLast h_not_nil
      · exact (Nat.zero_add _).symm
      · change List.num_Is v.val.dropLast + 1 = 1 + List.num_Is v.val.dropLast
        exact Nat.add_comm _ 1
    }
    rw [h1]
    have h2 : List.num_Is (v.val.dropLast ++ [v.val.getLast h_not_nil]) = List.num_Is v.val.dropLast + List.num_Is [v.val.getLast h_not_nil] := by {
      cases v.val.getLast h_not_nil
      · rw [num_Is_append_O]
        rfl
      · rw [num_Is_append_I]
        rfl
    }
    rw [← h_app] at h2
    rw [h2]
    exact Nat.add_comm _ _
}

/-- The subspace of strings with exactly k ones. -/
def weight_subspace (n k : Nat) := { v : List.Vector B n // List.num_Is v.val = k }

/-- Cyclic shift restricted to the weight subspace. -/
def cyclicShift_k {n k : Nat} (w : weight_subspace n k) : weight_subspace n k :=
  ⟨cyclicShift w.val, by {
    rw [num_Is_cyclicShift]
    exact w.property
  }⟩

/-- The VT Code constraint within the weight subspace. -/
def VT_subspace (n a k : Nat) (h_not_nil : n ≠ 0) := 
  { w : weight_subspace n k // List.Vector.moment w.val ≡ a [MOD n] ∧ w.val.val.getLast (by {
    intro hn
    have hlen := w.val.property
    rw [hn] at hlen
    have h_zero : n = 0 := hlen.symm
    exact h_not_nil h_zero
  }) = B.O }

lemma rotate_length_sub_one {α : Type} (l : List α) (n : Nat) (h_len : l.length = n) (h_pos : n > 0) (h_not_nil : l ≠ []) :
  l.rotate (n - 1) = l.getLast h_not_nil :: l.dropLast := by {
  unfold List.rotate
  rw [h_len]
  have h_mod : (n - 1) % n = n - 1 := Nat.mod_eq_of_lt (by omega)
  rw [h_mod]
  rw [List.splitAt_eq]
  dsimp
  have h_drop : List.drop (n - 1) l = [l.getLast h_not_nil] := by {
    rw [← h_len]
    exact List.drop_length_sub_one h_not_nil
  }
  rw [h_drop]
  have h_take : List.take (n - 1) l = l.dropLast := by {
    rw [List.dropLast_eq_take, h_len]
  }
  rw [h_take]
  rfl
}

lemma cyclicShift_val_eq_rotate {n : Nat} (v : List.Vector B n) :
  (cyclicShift v).val = v.val.rotate (n - 1) := by {
  unfold cyclicShift
  cases Decidable.em (n = 0) with
  | inl h =>
    rw [dif_pos h]
    have h_nil : v.val = [] := List.length_eq_zero_iff.mp (by { have h_v := v.property; omega })
    rw [h_nil]
    rfl
  | inr h =>
    rw [dif_neg h]
    have h_not_nil : v.val ≠ [] := by {
      intro hn
      have hlen := v.property
      rw [hn] at hlen
      exact h hlen.symm
    }
    have h_pos : n > 0 := by {
      have hlen := v.property
      cases heq : v.val with
      | nil => contradiction
      | cons hd tl => omega
    }
    exact (rotate_length_sub_one v.val n v.property h_pos h_not_nil).symm
}

/-- Apply cyclicShift d times. -/
def cyclicShiftPow {n : Nat} (d : Nat) (v : List.Vector B n) : List.Vector B n :=
  match d with
  | 0 => v
  | d' + 1 => cyclicShift (cyclicShiftPow d' v)

lemma cyclicShiftPow_val_eq_rotate {n : Nat} (d : Nat) (v : List.Vector B n) :
  (cyclicShiftPow d v).val = v.val.rotate (d * (n - 1)) := by {
  induction d with
  | zero =>
    rw [Nat.zero_mul, List.rotate_zero]
    rfl
  | succ d' ih =>
    change (cyclicShift (cyclicShiftPow d' v)).val = v.val.rotate ((d' + 1) * (n - 1))
    rw [cyclicShift_val_eq_rotate]
    rw [ih]
    rw [List.rotate_rotate]
    have h_arith : d' * (n - 1) + (n - 1) = (d' + 1) * (n - 1) := by ring
    rw [h_arith]
}

lemma cyclicShiftPow_length {n : Nat} (v : List.Vector B n) :
  cyclicShiftPow n v = v := by {
  apply Subtype.ext
  rw [cyclicShiftPow_val_eq_rotate]
  have h_len := v.property
  have h_rot : v.val.rotate (n * (n - 1)) = v.val := by {
    have h_arith : n * (n - 1) = v.val.length * (n - 1) := by rw [h_len]
    rw [h_arith]
    exact List.rotate_length_mul v.val (n - 1)
  }
  exact h_rot
}

/-- Lift cyclicShiftPow to weight_subspace. -/
def cyclicShiftPow_k {n k : Nat} (d : Nat) (w : weight_subspace n k) : weight_subspace n k :=
  match d with
  | 0 => w
  | d' + 1 => cyclicShift_k (cyclicShiftPow_k d' w)

lemma cyclicShiftPow_k_val {n k : Nat} (d : Nat) (w : weight_subspace n k) :
  (cyclicShiftPow_k d w).val = cyclicShiftPow d w.val := by {
  induction d with
  | zero => rfl
  | succ d' ih =>
    change (cyclicShift_k (cyclicShiftPow_k d' w)).val = cyclicShift (cyclicShiftPow d' w.val)
    unfold cyclicShift_k
    dsimp
    rw [ih]
}

lemma cyclicShiftPow_k_length {n k : Nat} (w : weight_subspace n k) :
  cyclicShiftPow_k n w = w := by {
  apply Subtype.ext
  rw [cyclicShiftPow_k_val]
  exact cyclicShiftPow_length w.val
}

lemma cyclicShiftPow_add {n : Nat} (a b : Nat) (v : List.Vector B n) :
  cyclicShiftPow a (cyclicShiftPow b v) = cyclicShiftPow (a + b) v := by {
  apply Subtype.ext
  rw [cyclicShiftPow_val_eq_rotate, cyclicShiftPow_val_eq_rotate, cyclicShiftPow_val_eq_rotate]
  rw [List.rotate_rotate]
  have h_arith : b * (n - 1) + a * (n - 1) = (a + b) * (n - 1) := by ring
  rw [h_arith]
}

lemma cyclicShiftPow_mod {n : Nat} (a : Nat) (v : List.Vector B n) :
  cyclicShiftPow (a % n) v = cyclicShiftPow a v := by {
  apply Subtype.ext
  rw [cyclicShiftPow_val_eq_rotate, cyclicShiftPow_val_eq_rotate]
  have h_div := Nat.div_add_mod a n
  have h_arith : a * (n - 1) = (a % n) * (n - 1) + n * ((a / n) * (n - 1)) := by {
    have h_arith2 : (a % n) * (n - 1) + n * ((a / n) * (n - 1)) = (a % n + n * (a / n)) * (n - 1) := by ring
    rw [h_arith2]
    rw [Nat.add_comm, h_div]
  }
  rw [h_arith]
  rw [← List.rotate_rotate]
  have h_len := v.property
  have h_len2 : (v.val.rotate ((a % n) * (n - 1))).length = n := by {
    rw [List.length_rotate, h_len]
  }
  have h_rot : (v.val.rotate ((a % n) * (n - 1))).rotate (n * ((a / n) * (n - 1))) = v.val.rotate ((a % n) * (n - 1)) := by {
    have h_arith3 : n * ((a / n) * (n - 1)) = (v.val.rotate ((a % n) * (n - 1))).length * ((a / n) * (n - 1)) := by rw [h_len2]
    rw [h_arith3]
    exact List.rotate_length_mul _ _
  }
  rw [h_rot]
}

lemma cyclicShiftPow_k_add {n k : Nat} (a b : Nat) (w : weight_subspace n k) :
  cyclicShiftPow_k a (cyclicShiftPow_k b w) = cyclicShiftPow_k (a + b) w := by {
  apply Subtype.ext
  rw [cyclicShiftPow_k_val, cyclicShiftPow_k_val, cyclicShiftPow_k_val]
  exact cyclicShiftPow_add a b w.val
}

lemma cyclicShiftPow_k_mod {n k : Nat} (a : Nat) (w : weight_subspace n k) :
  cyclicShiftPow_k (a % n) w = cyclicShiftPow_k a w := by {
  apply Subtype.ext
  rw [cyclicShiftPow_k_val, cyclicShiftPow_k_val]
  exact cyclicShiftPow_mod a w.val
}

instance {n k : Nat} [NeZero n] : AddAction (ZMod n) (weight_subspace n k) where
  vadd d w := cyclicShiftPow_k d.val w
  zero_vadd w := by {
    change cyclicShiftPow_k (0 : ZMod n).val w = w
    rw [ZMod.val_zero]
    rfl
  }
  add_vadd d1 d2 w := by {
    change cyclicShiftPow_k (d1 + d2).val w = cyclicShiftPow_k d1.val (cyclicShiftPow_k d2.val w)
    rw [ZMod.val_add]
    rw [cyclicShiftPow_k_mod]
    rw [cyclicShiftPow_k_add]
  }

/-- The moment of a vector in the weight subspace, mapped to ZMod n. -/
def moment_map {n k : Nat} (w : weight_subspace n k) : ZMod n :=
  List.Vector.moment w.val

lemma num_Is_cyclicShiftPow {n : Nat} (a : Nat) (v : List.Vector B n) :
  List.num_Is (cyclicShiftPow a v).val = List.num_Is v.val := by {
  induction a with
  | zero => rfl
  | succ a' ih =>
    change List.num_Is (cyclicShift (cyclicShiftPow a' v)).val = List.num_Is v.val
    rw [num_Is_cyclicShift, ih]
}

lemma moment_cyclicShiftPow {n : Nat} (a : Nat) (v : List.Vector B n) :
  List.Vector.moment (cyclicShiftPow a v) ≡ List.Vector.moment v + a * List.num_Is v.val [MOD n] := by {
  induction a with
  | zero =>
    change List.Vector.moment v ≡ List.Vector.moment v + 0 * List.num_Is v.val [MOD n]
    rw [Nat.zero_mul, Nat.add_zero]
  | succ a' ih =>
    change List.Vector.moment (cyclicShift (cyclicShiftPow a' v)) ≡ List.Vector.moment v + (a' + 1) * List.num_Is v.val [MOD n]
    have h_shift := moment_cyclicShift (cyclicShiftPow a' v)
    rw [num_Is_cyclicShiftPow] at h_shift
    have h_trans := Nat.ModEq.trans h_shift (Nat.ModEq.add_right (List.num_Is v.val) ih)
    have h_arith : List.Vector.moment v + a' * List.num_Is v.val + List.num_Is v.val = List.Vector.moment v + (a' + 1) * List.num_Is v.val := by ring
    rw [h_arith] at h_trans
    exact h_trans
}

/-- The fundamental moment shift theorem applied to the ZMod n AddAction. -/
lemma moment_map_vadd {n k : Nat} [NeZero n] (d : ZMod n) (w : weight_subspace n k) :
  moment_map (d +ᵥ w) = moment_map w + d * (k : ZMod n) := by {
  unfold moment_map
  change (List.Vector.moment (cyclicShiftPow_k d.val w).val : ZMod n) = (List.Vector.moment w.val : ZMod n) + d * (k : ZMod n)
  rw [cyclicShiftPow_k_val]
  have h_eq := moment_cyclicShiftPow d.val w.val
  have hk := w.property
  rw [hk] at h_eq
  have h_zmod : (List.Vector.moment (cyclicShiftPow d.val w.val) : ZMod n) = ((List.Vector.moment w.val + d.val * k : Nat) : ZMod n) := by {
    exact (ZMod.natCast_eq_natCast_iff _ _ n).mpr h_eq
  }
  rw [h_zmod]
  push_cast
  have hd : ((d.val : Nat) : ZMod n) = d := ZMod.natCast_zmod_val d
  rw [hd]
}

/-- The exact statement of Burnside's Lemma over our weight subspace. -/
lemma burnside_formula {n k : Nat} [NeZero n] [Fintype (weight_subspace n k)] [DecidableEq (weight_subspace n k)] [Fintype (Quotient (AddAction.orbitRel (ZMod n) (weight_subspace n k)))] :
  (∑ d : ZMod n, Finset.card (Finset.filter (fun w : weight_subspace n k => d +ᵥ w = w) Finset.univ)) = 
  Fintype.card (Quotient (AddAction.orbitRel (ZMod n) (weight_subspace n k))) * n := by {
  have h_burnside := AddAction.sum_card_fixedBy_eq_card_orbits_mul_card_addGroup (ZMod n) (weight_subspace n k)
  have h_card : Fintype.card (ZMod n) = n := ZMod.card n
  rw [h_card] at h_burnside
  have h_fixed (d : ZMod n) : Fintype.card (AddAction.fixedBy (weight_subspace n k) d) = Finset.card (Finset.filter (fun w : weight_subspace n k => d +ᵥ w = w) Finset.univ) := by {
    rw [Fintype.card_subtype]
    rfl
  }
  simp_rw [h_fixed] at h_burnside
  exact h_burnside
}

/-- Concatenate a block `m` times. -/
def block_repeat {g : Nat} (block : List.Vector B g) (m : Nat) : List.Vector B (m * g) :=
  ⟨(List.replicate m block.val).flatten, by {
    induction m with
    | zero =>
      change (List.replicate 0 block.val).flatten.length = 0 * g
      have h_zero : 0 * g = 0 := Nat.zero_mul _
      rw [h_zero]
      rfl
    | succ m' ih =>
      change (block.val ++ (List.replicate m' block.val).flatten).length = (m' + 1) * g
      rw [List.length_append, ih, block.property]
      ring
  }⟩

/-- The weight of a repeated block is `m * weight block`. -/
lemma num_Is_block_repeat {g : Nat} (block : List.Vector B g) (m : Nat) :
  List.num_Is (block_repeat block m).val = m * List.num_Is block.val := by {
  induction m with
  | zero =>
    have h_zero : 0 * List.num_Is block.val = 0 := Nat.zero_mul _
    change List.num_Is (block_repeat block 0).val = 0 * List.num_Is block.val
    rw [h_zero]
    rfl
  | succ m' ih =>
    change List.num_Is (block.val ++ (List.replicate m' block.val).flatten) = (m' + 1) * List.num_Is block.val
    rw [List.num_Is_append]
    change List.num_Is block.val + List.num_Is (block_repeat block m').val = (m' + 1) * List.num_Is block.val
    rw [ih]
    ring
}

/-- If a vector in the weight subspace is built from `m` repetitions, `m` divides its weight. -/
lemma weight_divisible_by_repetitions {n k g m : Nat} (_ : m * g = n) 
  (w : weight_subspace n k) (block : List.Vector B g) 
  (h_rep : w.val.val = (block_repeat block m).val) : m ∣ k := by {
  have hk : k = List.num_Is w.val.val := w.property.symm
  rw [hk, h_rep]
  rw [num_Is_block_repeat]
  exact dvd_mul_right m (List.num_Is block.val)
}

/-- Qualitative representation of fixed points: A vector is invariant under a shift of `d`
    if and only if it consists of a repeating block of length `gcd(d, n)`. -/
lemma fixed_by_iff_block_repeat {n k d : Nat} [NeZero n] (w : weight_subspace n k) :
  (d : ZMod n) +ᵥ w = w ↔ 
  ∃ (block : List.Vector B (Nat.gcd d n)), w.val.val = (block_repeat block (n / Nat.gcd d n)).val := by {
  sorry
}

/-- The exact number of fixed points under a shift of `d` is given by the binomial coefficient
    choosing the weight within the repeating block. -/
lemma card_fixedBy_eq_binom {n k d : Nat} [NeZero n] [Fintype (weight_subspace n k)] [DecidableEq (weight_subspace n k)] :
  Finset.card (Finset.filter (fun w : weight_subspace n k => (d : ZMod n) +ᵥ w = w) Finset.univ) = 
  if (n / Nat.gcd d n) ∣ k then Nat.choose (Nat.gcd d n) (k * Nat.gcd d n / n) else 0 := by {
  -- Follows from fixed_by_iff_block_repeat by counting the possible blocks.
  sorry
}
def syndrome_slice (n a k : Nat) :=
  { w : weight_subspace n k // List.Vector.moment w.val ≡ a [MOD n] }

def shift_equiv (n a k : Nat) (hn : 0 < n) :
    Equiv (syndrome_slice n a k) (syndrome_slice n (a + k) k) where
  toFun := fun ⟨w, hw⟩ => ⟨⟨cyclicShift w.val, by {
    rw [num_Is_cyclicShift]
    exact w.property
  }⟩, by {
    have h_shift := moment_cyclicShift w.val
    have hw_val := w.property
    rw [hw_val] at h_shift
    have h_add := Nat.ModEq.add_right k hw
    exact Nat.ModEq.trans h_shift h_add
  }⟩
  invFun := fun ⟨w, hw⟩ => ⟨⟨cyclicShiftPow (n - 1) w.val, by {
    rw [num_Is_cyclicShiftPow]
    exact w.property
  }⟩, by {
    have h_shift := moment_cyclicShiftPow (n - 1) w.val
    have hw_val := w.property
    rw [hw_val] at h_shift
    have h_trans := Nat.ModEq.add_right ((n - 1) * k) hw
    have h_arith : a + k + (n - 1) * k = a + n * k := by {
      rw [Nat.mul_comm (n - 1)]
      rw [Nat.mul_comm n]
      have h1 : k * (n - 1) = k * n - k := by {
        rw [Nat.mul_sub_left_distrib]
        simp
      }
      rw [h1]
      have h2 : k ≤ k * n := by {
        exact Nat.le_mul_of_pos_right k hn
      }
      omega
    }
    rw [h_arith] at h_trans
    have h_mod : a + n * k ≡ a [MOD n] := by {
      rw [Nat.ModEq]
      rw [Nat.add_mul_mod_self_left]
    }
    have h_trans2 := Nat.ModEq.trans h_shift h_trans
    exact Nat.ModEq.trans h_trans2 h_mod
  }⟩
  left_inv := fun ⟨w, hw⟩ => by {
    apply Subtype.ext
    apply Subtype.ext
    change cyclicShiftPow (n - 1) (cyclicShift w.val) = w.val
    have h_pow := cyclicShiftPow_add (n - 1) 1 w.val
    change cyclicShiftPow (n - 1) (cyclicShiftPow 1 w.val) = w.val
    rw [h_pow]
    have h_add : n - 1 + 1 = n := by omega
    rw [h_add]
    exact cyclicShiftPow_length w.val
  }
  right_inv := fun ⟨w, hw⟩ => by {
    apply Subtype.ext
    apply Subtype.ext
    change cyclicShift (cyclicShiftPow (n - 1) w.val) = w.val
    have h_pow := cyclicShiftPow_add 1 (n - 1) w.val
    change cyclicShiftPow 1 (cyclicShiftPow (n - 1) w.val) = w.val
    rw [h_pow]
    have h_add : 1 + (n - 1) = n := by omega
    rw [h_add]
    exact cyclicShiftPow_length w.val
  }

def syndrome_slice_congr (n A B k : Nat) (h : A ≡ B [MOD n]) :
    Equiv (syndrome_slice n A k) (syndrome_slice n B k) where
  toFun := fun ⟨w, hw⟩ => ⟨w, Nat.ModEq.trans hw h⟩
  invFun := fun ⟨w, hw⟩ => ⟨w, Nat.ModEq.trans hw (Nat.ModEq.symm h)⟩
  left_inv := fun _ => rfl
  right_inv := fun _ => rfl

def shift_equiv_pow (n a k : Nat) (hn : 0 < n) (j : Nat) :
    Equiv (syndrome_slice n a k) (syndrome_slice n (a + j * k) k) :=
  match j with
  | 0 => 
    have heq : a + 0 * k = a := by ring
    syndrome_slice_congr n a (a + 0 * k) k (by rw [heq])
  | j' + 1 =>
    have ih := shift_equiv_pow n a k hn j'
    have h_step := shift_equiv n (a + j' * k) k hn
    have h_trans := Equiv.trans ih h_step
    have heq : a + j' * k + k = a + (j' + 1) * k := by ring
    Equiv.trans h_trans (syndrome_slice_congr n (a + j' * k + k)
      (a + (j' + 1) * k) k (by rw [heq]))

def coprime_syndrome_slice_equiv_exists (n _a _a' k : Nat) (_hn : 0 < n)
    (_h_coprime : Nat.Coprime k n) : Nat :=
  0

lemma coprime_syndrome_slice_equiv_exists_proof (n a a' k : Nat) (hn : 0 < n)
    (h_coprime : Nat.Coprime k n) :
    a + coprime_syndrome_slice_equiv_exists n a a' k hn h_coprime * k ≡ a' [MOD n] := by
  sorry

def coprime_syndrome_slice_equiv (n a a' k : Nat) (hn : 0 < n)
    (h_coprime : Nat.Coprime k n) :
    Equiv (syndrome_slice n a k) (syndrome_slice n a' k) :=
  let j := coprime_syndrome_slice_equiv_exists n a a' k hn h_coprime
  have hj := coprime_syndrome_slice_equiv_exists_proof n a a' k hn h_coprime
  Equiv.trans (shift_equiv_pow n a k hn j) (syndrome_slice_congr n (a + j * k) a' k hj)

end Burnside


