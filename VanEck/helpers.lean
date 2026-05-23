import Mathlib.Data.Set.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Int.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.Ring

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
  sorry
}

lemma orbit_inj (P : ℕ) [NeZero P] (k0 X : ℕ) (hX : X ≤ P) (n1 n2 : ℕ) (hn1 : n1 < P / Nat.gcd P X) (hn2 : n2 < P / Nat.gcd P X)
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
