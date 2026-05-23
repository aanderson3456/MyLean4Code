import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Field.GeomSum
import Mathlib.RingTheory.RootsOfUnity.Basic
import Mathlib.Algebra.Polynomial.Basic
import Mathlib.RingTheory.RootsOfUnity.PrimitiveRoots
import Mathlib.RingTheory.RootsOfUnity.Complex

open scoped Classical
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

lemma zmod_cast_sub_mul (P : ℕ) [NeZero P] (k0 X n : ℕ) :
    ( ((k0 + P - (n * X) % P) % P : ℕ) : ZMod P ) = (k0 : ZMod P) - (n : ZMod P) * (X : ZMod P) := by {
  have h_sub : (n * X) % P ≤ k0 + P := by {
    have h1 : (n * X) % P < P := Nat.mod_lt _ (NeZero.pos P)
    omega
  }
  rw [ZMod.natCast_mod, Nat.cast_sub h_sub, Nat.cast_add]
  have h_mod : ((n * X) % P : ZMod P) = (n : ZMod P) * (X : ZMod P) := by {
    have h1 : ((n * X) % P : ZMod P) = ((n * X : ℕ) : ZMod P) := by rw [ZMod.natCast_mod]
    rw [h1]
    push_cast
    rfl
  }
  rw [h_mod]
  have hp : (P : ZMod P) = 0 := ZMod.natCast_self P
  rw [hp]
  ring
}

lemma mod_step_eq (P : ℕ) [NeZero P] (k0 X m : ℕ) (hX : X ≤ P) :
    ((((k0 + P - (m * X) % P) % P) + P - X) % P) =
    ((k0 + P - ((m + 1) * X) % P) % P) := by {
  apply (zmod_eq P _ _).mp
  have h_lhs : ( (((k0 + P - (m * X) % P) % P) + P - X : ℕ) : ZMod P ) = (k0 : ZMod P) - (m : ZMod P) * (X : ZMod P) - (X : ZMod P) := by {
    have h_sub1 : X ≤ (((k0 + P - (m * X) % P) % P) + P) := by omega
    rw [Nat.cast_sub h_sub1, Nat.cast_add, ZMod.natCast_mod]
    have h_sub2 : (m * X) % P ≤ k0 + P := by {
      have h1 : (m * X) % P < P := Nat.mod_lt _ (NeZero.pos P)
      omega
    }
    rw [Nat.cast_sub h_sub2, Nat.cast_add]
    have h_mod : ((m * X) % P : ZMod P) = (m : ZMod P) * (X : ZMod P) := by {
      have h1 : ((m * X) % P : ZMod P) = ((m * X : ℕ) : ZMod P) := by rw [ZMod.natCast_mod]
      rw [h1]
      push_cast
      rfl
    }
    rw [h_mod]
    have hp : (P : ZMod P) = 0 := ZMod.natCast_self P
    rw [hp]
    ring
  }
  have h_rhs : ( ((k0 + P - ((m + 1) * X) % P) : ℕ) : ZMod P ) = (k0 : ZMod P) - ((m + 1) : ZMod P) * (X : ZMod P) := by {
    have h_sub : ((m + 1) * X) % P ≤ k0 + P := by {
      have h1 : ((m + 1) * X) % P < P := Nat.mod_lt _ (NeZero.pos P)
      omega
    }
    rw [Nat.cast_sub h_sub, Nat.cast_add]
    have h_mod : (((m + 1) * X) % P : ZMod P) = ((m + 1) : ZMod P) * (X : ZMod P) := by {
      have h1 : (((m + 1) * X) % P : ZMod P) = (((m + 1) * X : ℕ) : ZMod P) := by rw [ZMod.natCast_mod]
      rw [h1]
      push_cast
      rfl
    }
    rw [h_mod]
    have hp : (P : ZMod P) = 0 := ZMod.natCast_self P
    rw [hp]
    ring
  }
  rw [h_lhs, h_rhs]
  ring
}

def orbitSeq (P : ℕ) (f : Fin P → Fin P) (k0 : Fin P) : ℕ → Fin P
| 0 => k0
| (n + 1) => f (orbitSeq P f k0 n)

lemma orbitSeq_v (P : ℕ) (v : ℕ → ℕ) (f : Fin P → Fin P)
    (h_recent : ∀ k : Fin P, v ((f k).val + 1) = v (k.val + 1))
    (X : ℕ) (k0 : Fin P) (hk0 : v (k0.val + 1) = X) (n : ℕ) :
    v ((orbitSeq P f k0 n).val + 1) = X := by {
  induction n with
  | zero => exact hk0
  | succ m ih =>
    have h1 := h_recent (orbitSeq P f k0 m)
    rw [ih] at h1
    exact h1
}

lemma orbitSeq_val (P : ℕ) [NeZero P] (v : ℕ → ℕ) (f : Fin P → Fin P)
    (hf : ∀ k : Fin P, (f k).val = (k.val + P - v (k.val + 1)) % P)
    (h_recent : ∀ k : Fin P, v ((f k).val + 1) = v (k.val + 1))
    (X : ℕ) (hX : X ≤ P) (k0 : Fin P) (hk0 : v (k0.val + 1) = X) (n : ℕ) :
    (orbitSeq P f k0 n).val = (k0.val + P - (n * X) % P) % P := by {
  induction n with
  | zero =>
    unfold orbitSeq
    have h1 : 0 * X = 0 := Nat.zero_mul X
    rw [h1]
    have h2 : 0 % P = 0 := Nat.zero_mod P
    rw [h2]
    have h3 : k0.val + P - 0 = k0.val + P := Nat.sub_zero _
    rw [h3]
    have h4 : k0.val + P = P + k0.val := Nat.add_comm _ _
    rw [h4, Nat.add_mod_left, Nat.mod_eq_of_lt k0.isLt]
  | succ m ih =>
    unfold orbitSeq
    have h_v := orbitSeq_v P v f h_recent X k0 hk0 m
    have h_f := hf (orbitSeq P f k0 m)
    rw [h_v] at h_f
    rw [ih] at h_f
    rw [h_f]
    exact mod_step_eq P k0.val X m hX
}

lemma cycle_injectivity (P X : ℕ) [NeZero P] (n1 n2 : ℕ) (hn1 : n1 < P / Nat.gcd P X) (hn2 : n2 < P / Nat.gcd P X)
    (heq : (n1 * X) % P = (n2 * X) % P) : n1 = n2 := by {
  have h_modeq : n1 * X ≡ n2 * X [MOD P] := heq
  have h_pos : 0 < P := by {
    have h : P ≠ 0 := NeZero.ne P
    omega
  }
  have h_modeq2 : n1 ≡ n2 [MOD P / Nat.gcd P X] := Nat.ModEq.cancel_right_div_gcd h_pos h_modeq
  exact h_modeq2.eq_of_lt_of_lt hn1 hn2
}

lemma orbit_inj (P : ℕ) [NeZero P] (k0 X : ℕ) (n1 n2 : ℕ) (hn1 : n1 < P / Nat.gcd P X) (hn2 : n2 < P / Nat.gcd P X)
    (h_eq : (k0 + P - (n1 * X) % P) % P = (k0 + P - (n2 * X) % P) % P) : n1 = n2 := by {
  have h_zmod : ( ((k0 + P - (n1 * X) % P) % P : ℕ) : ZMod P ) = ( ((k0 + P - (n2 * X) % P) % P : ℕ) : ZMod P ) := by {
    rw [h_eq]
  }
  have h_lhs : ( ((k0 + P - (n1 * X) % P) % P : ℕ) : ZMod P ) = (k0 : ZMod P) - (n1 : ZMod P) * (X : ZMod P) := by {
    exact zmod_cast_sub_mul P k0 X n1
  }
  have h_rhs : ( ((k0 + P - (n2 * X) % P) % P : ℕ) : ZMod P ) = (k0 : ZMod P) - (n2 : ZMod P) * (X : ZMod P) := by {
    exact zmod_cast_sub_mul P k0 X n2
  }
  rw [h_lhs, h_rhs] at h_zmod
  have h_cancel : (n1 : ZMod P) * (X : ZMod P) = (n2 : ZMod P) * (X : ZMod P) := by {
    calc (n1 : ZMod P) * (X : ZMod P)
      _ = (k0 : ZMod P) - ((k0 : ZMod P) - (n1 : ZMod P) * (X : ZMod P)) := by ring
      _ = (k0 : ZMod P) - ((k0 : ZMod P) - (n2 : ZMod P) * (X : ZMod P)) := by rw [h_zmod]
      _ = (n2 : ZMod P) * (X : ZMod P) := by ring
  }
  have h_mod_eq : (n1 * X) % P = (n2 * X) % P := by {
    apply (zmod_eq P (n1 * X) (n2 * X)).mp
    push_cast
    exact h_cancel
  }
  exact cycle_injectivity P X n1 n2 hn1 hn2 h_mod_eq
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

/--
Combinatorial Upper Bound for Van Eck Fibers
In a hypothetical cyclic exact cover system modelling the Van Eck sequence behavior over a bounded window,
every evaluation `v(k.val + 1) = X` casts a "shadow" of size exactly `X` (the elements `k, k-1, \dots, k-X+1`).
By hypothesis `h_no_intermediate`, these shadows contain no other elements mapping to `X`.
Hence, the shadows are perfectly disjoint.
Since the entire ambient space has size `P`, the union of these disjoint sets of size `X` cannot exceed `P`.
Therefore, `|C_X| * X \le P`, establishing a combinatorial upper bound for the cardinality of the fiber `C_X`.
-/
lemma vanEck_fiber_upper_bound (P : ℕ) (hP : P ≥ 4) (v : ℕ → ℕ) (f : Fin P → Fin P)
    (hf : ∀ k : Fin P, (f k).val = (k.val + P - v (k.val + 1)) % P)
    (hbij : Function.Bijective f)
    (h_recent : ∀ k : Fin P, v ((f k).val + 1) = v (k.val + 1))
    (X : ℕ) (hX_pos : X > 0) (hX_le : X ≤ P)
    (h_no_intermediate : ∀ k : Fin P, v (k.val + 1) = X → ∀ i < X, i > 0 → v ((k.val + P - i) % P + 1) ≠ X) :
    (Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)).card * X ≤ P := by {
  let C := Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)
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
}

/--
Cycle Length Lower Bound for Van Eck Fibers
Since `v` maps elements backward by exactly `v(k+1)`, the orbit of any element mapping to `X` 
forms a cycle stepping by `-X \pmod P`. 
Because the sequence of jumps evaluates over the finite cyclic group `Z/PZ`, 
the orbit length is exactly `P / \gcd(P, X)`. 
Since the orbit is entirely contained within the fiber `C_X`, the fiber must have at least this many elements.
Thus, `|C_X| \ge P / \gcd(P, X)`.
-/
lemma vanEck_fiber_cycle_length (P : ℕ) (hP : P ≥ 4) (v : ℕ → ℕ) (f : Fin P → Fin P)
    (hf : ∀ k : Fin P, (f k).val = (k.val + P - v (k.val + 1)) % P)
    (hbij : Function.Bijective f)
    (h_recent : ∀ k : Fin P, v ((f k).val + 1) = v (k.val + 1))
    (X : ℕ) (hX_pos : X > 0) (hX_le : X ≤ P) (hX_in : ∃ k : Fin P, v (k.val + 1) = X) :
    (Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)).card ≥ P / Nat.gcd P X := by {
  let C := Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)
  have ⟨k0, hk0⟩ := hX_in
  
  let L := P / Nat.gcd P X
  let orbit : Finset (Fin P) := Finset.image (fun n : Fin L => ⟨(k0.val + P - (n.val * X) % P) % P, by {
    apply Nat.mod_lt; omega
  }⟩) Finset.univ
  
  have h_P_ne_zero : NeZero P := ⟨by omega⟩
  
  have h_orbit_in : orbit ⊆ C := by {
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨n, _, hn_eq⟩
    have h_seq := orbitSeq_val P v f hf h_recent X hX_le k0 hk0 n.val
    have h_v := orbitSeq_v P v f h_recent X k0 hk0 n.val
    have h_x_val : x.val = (k0.val + P - (n.val * X) % P) % P := by {
      have h1 : x.val = (⟨(k0.val + P - (n.val * X) % P) % P, by { apply Nat.mod_lt; omega }⟩ : Fin P).val := by rw [hn_eq]
      exact h1
    }
    rw [← h_seq] at h_x_val
    have h_x_v : v (x.val + 1) = X := by {
      rw [h_x_val]
      exact h_v
    }
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h_x_v⟩
  }
  
  have h_orbit_size : orbit.card = L := by {
    have h_inj : Function.Injective (fun n : Fin L => (⟨(k0.val + P - (n.val * X) % P) % P, by {
      apply Nat.mod_lt; omega
    }⟩ : Fin P)) := by {
      intro n1 n2 h_eq
      have h_val : (k0.val + P - (n1.val * X) % P) % P = (k0.val + P - (n2.val * X) % P) % P := by {
        injection h_eq
      }
      have h_eq_nat := orbit_inj P k0.val X n1.val n2.val n1.isLt n2.isLt h_val
      exact Fin.eq_of_val_eq h_eq_nat
    }
    rw [Finset.card_image_of_injective Finset.univ h_inj, Finset.card_univ, Fintype.card_fin]
  }
  
  have h_bound : orbit.card ≤ C.card := Finset.card_le_card h_orbit_in
  rw [h_orbit_size] at h_bound
  exact h_bound
}

/--
Exact Fiber Density Match (The Squeeze)
Using the upper bound `|C_X| * X \le P` and the lower bound `|C_X| \ge P / \gcd(P, X)`, 
we know that `|C_X| * X \ge P * (X / \gcd(P, X)) \ge P`.
The only way these two bounds can simultaneously hold is if `|C_X| * X = P`.
This forces `X` to divide `P` exactly, and perfectly locks the density of the fiber.
-/
lemma vanEck_fiber_sum (P : ℕ) (hP : P ≥ 4)
    (v : ℕ → ℕ)
    (f : Fin P → Fin P)
    (hf : ∀ k : Fin P, (f k).val = (k.val + P - v (k.val + 1)) % P)
    (hbij : Function.Bijective f)
    (h_recent : ∀ k : Fin P, v ((f k).val + 1) = v (k.val + 1))
    (X : ℕ) (hX_pos : X > 0) (hX_le : X ≤ P) (hX_in : ∃ k : Fin P, v (k.val + 1) = X)
    (h_no_intermediate : ∀ k : Fin P, v (k.val + 1) = X → ∀ i < X, i > 0 → v ((k.val + P - i) % P + 1) ≠ X) :
    (Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)).card * X = P := by {
  have h_le := vanEck_fiber_upper_bound P hP v f hf hbij h_recent X hX_pos hX_le h_no_intermediate
  have h_ge := vanEck_fiber_cycle_length P hP v f hf hbij h_recent X hX_pos hX_le hX_in
  
  let C_card := (Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)).card
  have h_gcd_div_X : Nat.gcd P X ∣ X := Nat.gcd_dvd_right P X
  have h_gcd_div_P : Nat.gcd P X ∣ P := Nat.gcd_dvd_left P X
  have h_gcd_pos : Nat.gcd P X > 0 := Nat.gcd_pos_of_pos_right P hX_pos
  
  have h_ge_mul : C_card * X ≥ (P / Nat.gcd P X) * X := Nat.mul_le_mul_right X h_ge
  
  have h_P_le : P ≤ (P / Nat.gcd P X) * X := by {
    have h_gcd_pos : Nat.gcd P X > 0 := Nat.gcd_pos_of_pos_right P hX_pos
    have h_P_eq : P = (P / Nat.gcd P X) * Nat.gcd P X := by {
      exact Nat.div_mul_cancel (Nat.gcd_dvd_left P X) |>.symm
    }
    have h_gcd_le_X : Nat.gcd P X ≤ X := Nat.gcd_le_right P hX_pos
    nth_rw 1 [h_P_eq]
    exact Nat.mul_le_mul_left (P / Nat.gcd P X) h_gcd_le_X
  }
  have h_C_ge_P : C_card * X ≥ P := Nat.le_trans h_P_le h_ge_mul
  exact Nat.le_antisymm h_le h_C_ge_P
}

open scoped Classical
/--
Fiber Arithmetic Progression Uniqueness
Given that `|C_X| * X = P`, the cardinality of the fiber is exactly `P / X`.
Since `X` divides `P`, we have `\gcd(P, X) = X`, making the orbit length exactly `P / X`.
Therefore, the single cycle orbit of length `P / X` completely covers the entire fiber `C_X`.
This proves that the set of elements jumping by `X` forms exactly one arithmetic progression.
-/
lemma vanEck_fiber_is_ap (P : ℕ) (hP : P ≥ 4)
    (v : ℕ → ℕ)
    (f : Fin P → Fin P)
    (hf : ∀ k : Fin P, (f k).val = (k.val + P - v (k.val + 1)) % P)
    (hbij : Function.Bijective f)
    (h_recent : ∀ k : Fin P, v ((f k).val + 1) = v (k.val + 1))
    (X : ℕ) (hX_pos : X > 0) (hX_le : X ≤ P) (hX_in : ∃ k : Fin P, v (k.val + 1) = X)
    (h_no_intermediate : ∀ k : Fin P, v (k.val + 1) = X → ∀ i < X, i > 0 → v ((k.val + P - i) % P + 1) ≠ X) :
    let L := P / Nat.gcd P X;
    let k0 := Classical.choose hX_in;
    Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X) = 
    Finset.image (fun n : Fin L => ⟨(k0.val + P - (n.val * X) % P) % P, by {
      apply Nat.mod_lt; omega
    }⟩) Finset.univ := by {
  let L := P / Nat.gcd P X;
  let k0 := Classical.choose hX_in;
  have hk0 : v (k0.val + 1) = X := Classical.choose_spec hX_in;
  let C := Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)
  let orbit : Finset (Fin P) := Finset.image (fun n : Fin L => ⟨(k0.val + P - (n.val * X) % P) % P, by {
    apply Nat.mod_lt; omega
  }⟩) Finset.univ
  
  have h_P_ne_zero : NeZero P := ⟨by omega⟩
  
  have h_subset1 : orbit ⊆ C := by {
    intro x hx
    rw [Finset.mem_image] at hx
    rcases hx with ⟨n, _, hn_eq⟩
    have h_seq := orbitSeq_val P v f hf h_recent X hX_le k0 hk0 n.val
    have h_v := orbitSeq_v P v f h_recent X k0 hk0 n.val
    have h_x_val : x.val = (k0.val + P - (n.val * X) % P) % P := by {
      have h1 : x.val = (⟨(k0.val + P - (n.val * X) % P) % P, by { apply Nat.mod_lt; omega }⟩ : Fin P).val := by rw [hn_eq]
      exact h1
    }
    rw [← h_seq] at h_x_val
    have h_x_v : v (x.val + 1) = X := by {
      rw [h_x_val]
      exact h_v
    }
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h_x_v⟩
  }
  
  have h_orbit_size : orbit.card = L := by {
    have h_inj : Function.Injective (fun n : Fin L => (⟨(k0.val + P - (n.val * X) % P) % P, by {
      apply Nat.mod_lt; omega
    }⟩ : Fin P)) := by {
      intro n1 n2 h_eq
      have h_val : (k0.val + P - (n1.val * X) % P) % P = (k0.val + P - (n2.val * X) % P) % P := by {
        injection h_eq
      }
      have h_eq_nat := orbit_inj P k0.val X n1.val n2.val n1.isLt n2.isLt h_val
      exact Fin.eq_of_val_eq h_eq_nat
    }
    rw [Finset.card_image_of_injective Finset.univ h_inj, Finset.card_univ, Fintype.card_fin]
  }
  
  have h_eq : orbit = C := by {
    have h_sum := vanEck_fiber_sum P hP v f hf hbij h_recent X hX_pos hX_le hX_in h_no_intermediate
    have h_size_le : C.card ≤ L := by {
      have h_gcd_le : Nat.gcd P X ≤ X := Nat.gcd_le_right P hX_pos
      have h_mul_le : C.card * Nat.gcd P X ≤ P := by {
        calc C.card * Nat.gcd P X
          _ ≤ C.card * X := Nat.mul_le_mul_left C.card h_gcd_le
          _ = P := h_sum
      }
      have h_gcd_pos : Nat.gcd P X > 0 := Nat.gcd_pos_of_pos_right P hX_pos
      exact (Nat.le_div_iff_mul_le h_gcd_pos).mpr h_mul_le
    }
    have h_orbit_le_C : orbit.card ≤ C.card := Finset.card_le_card h_subset1
    have h_C_le_orbit : C.card ≤ orbit.card := by {
      calc C.card
        _ ≤ L := h_size_le
        _ = orbit.card := h_orbit_size.symm
    }
    have h_card_eq : orbit.card = C.card := le_antisymm h_orbit_le_C h_C_le_orbit
    exact Finset.eq_of_subset_of_card_le h_subset1 (le_of_eq h_card_eq.symm)
  }
  exact h_eq.symm
}


/--
The Mirsky-Newman Theorem (Exact Cover System Theorem)
It is impossible to partition a finite cyclic group into arithmetic
progressions with strictly distinct step sizes (moduli) all ≥ 3.
-/
theorem mirsky_newman_exact_cover (P : ℕ) (hP : P > 0) (S : Finset ℕ)
    (h_min : ∀ X ∈ S, X ≥ 3)
    (h_div : ∀ X ∈ S, X ∣ P)
    (cover : ℕ → Finset (Fin P))
    (h_partition : ∀ k : Fin P, ∃! X, X ∈ S ∧ k ∈ cover X)
    (h_ap : ∀ X ∈ S, ∃ start : Fin P, cover X = Finset.filter (fun (k : Fin P) => ∃ i : ℕ, k.val = (start.val + i * X) % P) Finset.univ) :
    False := by {
  sorry
}
