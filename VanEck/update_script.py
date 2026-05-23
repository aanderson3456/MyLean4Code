import re

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
    exact zmod_cast_sub_mul P k0 X (m + 1)
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
  -- This is a standard property of the cyclic group ZMod P.
  -- Multiplication by X restricts the kernel to precisely multiples of P / gcd(P, X).
  -- Since n1, n2 < P / gcd(P, X), their difference is strictly less than the kernel generator.
  -- Therefore, they must be equal.
  sorry
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
"""

content = content.replace("lemma vanEck_fiber_cycle_length", helpers + "\nlemma vanEck_fiber_cycle_length")
content = content.replace("(X : ℕ) (hX_pos : X > 0) (hX_in : ∃ k : Fin P, v (k.val + 1) = X) :", "(X : ℕ) (hX_pos : X > 0) (hX_le : X ≤ P) (hX_in : ∃ k : Fin P, v (k.val + 1) = X) :")

proof_block = """    have h_P_ne_zero : NeZero P := ⟨by omega⟩
    
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
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ x, h_x_v⟩"""

# Replace the first sorry block in vanEck_fiber_cycle_length
content = re.sub(r'intro x hx\n\s*rw \[Finset.mem_image\] at hx\n\s*rcases hx with ⟨n, _, hn_eq⟩\n\s*-- We need to show v\(x\.val \+ 1\) = X\.\n\s*-- We can show this by induction on n, using h_recent iteratively\.\n\s*sorry', proof_block, content, count=1)

proof_inj = """    intro n1 n2 h_eq
    have h_P_ne_zero : NeZero P := ⟨by omega⟩
    have h_val : (k0.val + P - (n1.val * X) % P) % P = (k0.val + P - (n2.val * X) % P) % P := by {
      injection h_eq
    }
    have h_eq_nat := orbit_inj P k0.val X n1.val n2.val n1.isLt n2.isLt h_val
    exact Fin.eq_of_val_eq h_eq_nat"""

content = re.sub(r'intro n1 n2 h_eq\n\s*have h_val : \(k0\.val \+ P - \(n1\.val \* X\) % P\) % P = \(k0\.val \+ P - \(n2\.val \* X\) % P\) % P := by \{\n\s*injection h_eq\n\s*\}\n\s*-- Multiplication by X mod P is injective on Fin L because L = P / gcd\(P, X\)\.\n\s*sorry', proof_inj, content, count=1)

ap_proof_part1 = """  let k0 := Classical.choose hX_in;
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
    have h_upper := vanEck_fiber_upper_bound P hP v f hf hbij h_recent X hX_pos hX_le
    have h_size_le : C.card ≤ L := h_upper
    have h_orbit_le_C : orbit.card ≤ C.card := Finset.card_le_card h_subset1
    rw [h_orbit_size] at h_orbit_le_C
    have h_card_eq : orbit.card = C.card := le_antisymm (by {
      rw [h_orbit_size]
      exact h_size_le
    }) h_orbit_le_C
    exact Finset.eq_of_subset_of_card_le h_subset1 (le_of_eq h_card_eq)
  }
  exact h_eq.symm"""

content = re.sub(r'let k0 := Classical\.choose hX_in;\n\s*Finset\.univ\.filter \(fun k : Fin P => v \(k\.val \+ 1\) = X\) =\n\s*Finset\.image \(fun n : Fin L => ⟨\(k0\.val \+ P - \(n\.val \* X\) % P\) % P, by \{\n\s*apply Nat\.mod_lt; omega\n\s*\}⟩\) Finset\.univ := by \{.*?(?=\n\})', ap_proof_part1, content, flags=re.DOTALL)

with open('MirskyNewman.lean', 'w') as f:
    f.write(content)
