import Mathlib
import VTlean.VTCode

open Nat Finset

/-- Recurrence for Pascal's triangle. Models the distribution of binary weights. -/
def pascal : Nat → List Nat
| 0 => [1]
| n + 1 =>
  let prev := pascal n
  let shifted := 0 :: prev
  let padded := prev ++ [0]
  List.zipWith (· + ·) padded shifted

/-- A helper to safely access elements from the pascal list. -/
lemma getD_zipWith_add_of_length_eq (l1 l2 : List Nat) (hl : l1.length = l2.length) (k : Nat) :
  (List.zipWith (· + ·) l1 l2).getD k 0 = l1.getD k 0 + l2.getD k 0 := by {
  induction k generalizing l1 l2 with
  | zero =>
    cases l1 with
    | nil => 
      cases l2 with
      | nil => rfl
      | cons _ _ => contradiction
    | cons h1 t1 =>
      cases l2 with
      | nil => contradiction
      | cons h2 t2 => rfl
  | succ k ih =>
    cases l1 with
    | nil => 
      cases l2 with
      | nil => rfl
      | cons _ _ => contradiction
    | cons h1 t1 =>
      cases l2 with
      | nil => contradiction
      | cons h2 t2 =>
        dsimp
        exact ih t1 t2 (by exact Nat.succ.inj hl)
}

def pascal_get (n c : Nat) : Nat :=
  (pascal n).getD c 0

lemma pascal_get_zero (n : Nat) : pascal_get n 0 = 1 := by
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold pascal_get pascal
    cases h : pascal n with
    | nil => 
      have h1 : pascal_get n 0 = 0 := by rw [pascal_get, h]; rfl
      rw [h1] at ih
      contradiction
    | cons hd tl =>
      have h_ih : hd = 1 := by 
        have h_get : pascal_get n 0 = hd := by rw [pascal_get, h]; rfl
        rw [←ih]
        exact Eq.symm h_get
      rw [h_ih]
      rfl

lemma pascal_get_successor (n k : Nat) :
  pascal_get (n + 1) (k + 1) = pascal_get n (k + 1) + pascal_get n k := by {
  unfold pascal_get
  have h_pascal_succ : pascal (n + 1) = List.zipWith (·+·) (pascal n ++ [0]) (0 :: pascal n) := rfl
  rw [h_pascal_succ]
  generalize hl : pascal n = l
  have h_len : (l ++ [0]).length = (0 :: l).length := by simp
  rw [getD_zipWith_add_of_length_eq _ _ h_len]
  have h_shift : (0 :: l).getD (k + 1) 0 = l.getD k 0 := rfl
  rw [h_shift]
  have h_pad : ∀ l c, (l ++ [0]).getD c 0 = l.getD c 0 := by {
    intro l c
    induction l generalizing c with
    | nil =>
      cases c with
      | zero => rfl
      | succ c => rfl
    | cons hd tl ih =>
      cases c with
      | zero => rfl
      | succ c => exact ih c
  }
  rw [h_pad l (k + 1)]
}

/-- Formal theorem stating that Pascal's triangle elements equal the binomial coefficients. -/
theorem pascal_eq_choose (n k : Nat) :
  pascal_get n k = Nat.choose n k := by {
  induction n generalizing k with
  | zero => 
    cases k
    · rfl
    · rfl
  | succ n ih =>
    cases k
    · rw [pascal_get_zero, Nat.choose_zero_right]
    · rw [pascal_get_successor, Nat.choose_succ_succ, ih, ih, Nat.add_comm]
}

/-- Recurrence for Cuculiere's triangle (generating function coefficients of \prod_{i=1}^n (1+x^i)).
    It models the frequency distribution of raw VT code checksums for length n. -/
def cuculiere : Nat → List Nat
| 0 => [1]
| n + 1 =>
  let prev := cuculiere n
  let shifted := List.replicate (n + 1) 0 ++ prev
  let padded := prev ++ List.replicate (n + 1) 0
  List.zipWith (· + ·) padded shifted

/-- The maximum possible raw VT checksum for vectors of length n,
    which is also the length of the cuculiere list minus 1.
    Max sum is 1 + 2 + ... + n = n * (n + 1) / 2. -/
def max_vt_checksum (n : Nat) : Nat :=
  n * (n + 1) / 2

lemma max_vt_checksum_mono (n : Nat) : max_vt_checksum n ≤ max_vt_checksum (n + 1) := by {
  unfold max_vt_checksum
  apply Nat.div_le_div_right
  nlinarith
}

lemma max_vt_checksum_succ (n : Nat) : max_vt_checksum (n + 1) = max_vt_checksum n + n + 1 := by {
  unfold max_vt_checksum
  have h1 : (n + 1) * (n + 1 + 1) = n * (n + 1) + (n + 1) * 2 := by ring
  rw [h1]
  rw [Nat.add_mul_div_right]
  · omega
  · omega
}

/-- A helper to safely access elements from the cuculiere list, 
    returning 0 if out of bounds. -/
def cuculiere_get (n c : Nat) : Nat :=
  (cuculiere n).getD c 0

/-- Computes the cardinality of the VT code by mapping to Finset and summing.
    We iterate over all possible raw checksums c from 0 to max_vt_checksum n,
    filter for those where c % (n + 1) = a % (n + 1), and sum the corresponding frequencies. -/
noncomputable def cuculiere_mod_sum (n a : Nat) : Nat :=
  let domain := Finset.Iic (max_vt_checksum n)
  let valid_cs := domain.filter (fun c => c % (n + 1) = a % (n + 1))
  Finset.sum valid_cs (fun c => cuculiere_get n c)

/-- A generalized version of the modular sum for an arbitrary modulus `m`.
    This allows us to state recurrences where the modulus doesn't perfectly match `n + 1`. -/
noncomputable def cuculiere_mod_sum_gen (n m a : Nat) : Nat :=
  let domain := Finset.Iic (max_vt_checksum n)
  let valid_cs := domain.filter (fun c => c % m = a % m)
  Finset.sum valid_cs (fun c => cuculiere_get n c)

lemma cuculiere_mod_sum_eq_gen (n a : Nat) :
  cuculiere_mod_sum n a = cuculiere_mod_sum_gen n (n + 1) a := rfl

lemma getD_append_replicate (n c : Nat) (prev : List Nat) :
  (prev ++ List.replicate n 0).getD c 0 = prev.getD c 0 := by {
  revert c
  induction prev with
  | nil =>
    intro c
    rw [List.nil_append]
    induction n generalizing c with
    | zero => rfl
    | succ n ih =>
      cases c
      · rfl
      · apply ih
  | cons hd tl ih =>
    intro c
    cases c
    · rfl
    · apply ih
}

lemma getD_replicate_append (n c : Nat) (prev : List Nat) :
  (List.replicate n 0 ++ prev).getD c 0 = if c < n then 0 else prev.getD (c - n) 0 := by {
  induction n generalizing c with
  | zero => 
    have h : c - 0 = c := Nat.sub_zero c
    rw [h]
    have h2 : ¬ (c < 0) := Nat.not_lt_zero c
    simp [h2]
  | succ n ih =>
    cases c with
    | zero => rfl
    | succ c =>
      change (0 :: (List.replicate n 0 ++ prev)).getD (c + 1) 0 = _
      change (List.replicate n 0 ++ prev).getD c 0 = _
      rw [ih]
      split
      · have h_lt : c + 1 < n + 1 := by omega
        simp [h_lt]
      · have h_nlt : ¬ (c + 1 < n + 1) := by omega
        simp [h_nlt]
}

lemma cuculiere_get_successor (n c : Nat) :
  cuculiere_get (n + 1) c =
    cuculiere_get n c + if c < n + 1 then 0 else cuculiere_get n (c - (n + 1)) := by {
  unfold cuculiere_get
  have h_cuc_succ : cuculiere (n + 1) =
    List.zipWith (·+·) (cuculiere n ++ List.replicate (n + 1) 0)
      (List.replicate (n + 1) 0 ++ cuculiere n) := rfl
  rw [h_cuc_succ]
  generalize hl : cuculiere n = l
  have h_len : (l ++ List.replicate (n + 1) 0).length = (List.replicate (n + 1) 0 ++ l).length :=
    by simp [Nat.add_comm]
  rw [getD_zipWith_add_of_length_eq _ _ h_len]
  rw [getD_append_replicate]
  rw [getD_replicate_append (n + 1) c l]
}

lemma cuculiere_length (n : Nat) :
  (cuculiere n).length = max_vt_checksum n + 1 := by {
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold cuculiere
    dsimp
    rw [List.length_zipWith]
    rw [List.length_append, List.length_append, List.length_replicate, ih]
    have h_comm : n + 1 + (max_vt_checksum n + 1) = max_vt_checksum n + 1 + (n + 1) := Nat.add_comm _ _
    rw [h_comm]
    rw [Nat.min_self]
    rw [max_vt_checksum_succ]
    omega
}

lemma cuculiere_get_out_of_bounds (n c : Nat) (h : max_vt_checksum n < c) : 
  cuculiere_get n c = 0 := by {
  unfold cuculiere_get
  have h_len : (cuculiere n).length = max_vt_checksum n + 1 := cuculiere_length n
  have h_le : (cuculiere n).length ≤ c := by omega
  exact List.getD_eq_default _ _ h_le
}

lemma cuculiere_mod_sum_gen_successor (n m a : Nat) :
  cuculiere_mod_sum_gen (n + 1) m (a + n + 1) =
  cuculiere_mod_sum_gen n m (a + n + 1) + cuculiere_mod_sum_gen n m a := by {
  unfold cuculiere_mod_sum_gen
  have h_succ : ∀ c, cuculiere_get (n + 1) c =
    cuculiere_get n c + if c < n + 1 then 0 else cuculiere_get n (c - (n + 1)) := cuculiere_get_successor n
  
  -- Step 1: Substitute the recurrence into the sum over the (n+1) domain
  have h1 : (∑ c ∈ (Iic (max_vt_checksum (n + 1))).filter (fun c => c % m = (a + n + 1) % m), cuculiere_get (n + 1) c) =
    (∑ c ∈ (Iic (max_vt_checksum (n + 1))).filter (fun c => c % m = (a + n + 1) % m), (cuculiere_get n c + if c < n + 1 then 0 else cuculiere_get n (c - (n + 1)))) := by {
      apply sum_congr rfl
      intro c _
      rw [h_succ c]
    }
  rw [h1]

  -- Step 2: Distribute the sum over addition
  rw [sum_add_distrib]

  -- Step 3: The first half of the sum reduces to the sum over the n domain,
  -- because cuculiere_get n c = 0 for c > max_vt_checksum n.
  have h2 : (∑ c ∈ (Iic (max_vt_checksum (n + 1))).filter (fun c => c % m = (a + n + 1) % m), cuculiere_get n c) =
    ∑ c ∈ (Iic (max_vt_checksum n)).filter (fun c => c % m = (a + n + 1) % m), cuculiere_get n c := by {
    apply Eq.symm
    apply sum_subset
    · intro x hx
      rw [mem_filter] at hx ⊢
      constructor
      · rw [mem_Iic] at hx ⊢
        have h_max_le := max_vt_checksum_mono n
        omega
      · exact hx.2
    · intro x hx hnx
      rw [mem_filter] at hx
      have h_gt : max_vt_checksum n < x := by {
        by_contra h_le
        push Not at h_le
        have : x ∈ Iic (max_vt_checksum n) := by rwa [mem_Iic]
        have h_in_smaller : x ∈ (Iic (max_vt_checksum n)).filter (fun c => c % m = (a + n + 1) % m) := by {
          rw [mem_filter]
          exact ⟨this, hx.2⟩
        }
        exact hnx h_in_smaller
      }
      exact cuculiere_get_out_of_bounds n x h_gt
  }
  rw [h2]

  -- Step 4: The second half of the sum evaluates to the shifted a residue class.
  -- The index shift `k = c - (n + 1)` exactly maps the condition `c % m = (a + n + 1) % m`
  -- to `k % m = a % m`.
  have h3 : (∑ c ∈ (Iic (max_vt_checksum (n + 1))).filter (fun c => c % m = (a + n + 1) % m), if c < n + 1 then 0 else cuculiere_get n (c - (n + 1))) =
    ∑ k ∈ (Iic (max_vt_checksum n)).filter (fun k => k % m = a % m), cuculiere_get n k := by {
    have h_ite : ∀ c, (if c < n + 1 then 0 else cuculiere_get n (c - (n + 1))) = if n + 1 ≤ c then cuculiere_get n (c - (n + 1)) else 0 := by {
      intro c
      by_cases h: c < n + 1
      · have : ¬(n + 1 ≤ c) := by omega
        simp [h, this]
      · have : n + 1 ≤ c := by omega
        simp [h, this]
    }
    have h1 : (∑ c ∈ (Iic (max_vt_checksum (n + 1))).filter (fun c => c % m = (a + n + 1) % m), if c < n + 1 then 0 else cuculiere_get n (c - (n + 1))) =
      ∑ c ∈ (Iic (max_vt_checksum (n + 1))).filter (fun c => c % m = (a + n + 1) % m), if n + 1 ≤ c then cuculiere_get n (c - (n + 1)) else 0 := by {
      apply sum_congr rfl
      intro c _
      rw [h_ite c]
    }
    rw [h1]
    rw [← sum_filter]

    apply sum_bij (fun c _ => c - (n + 1))
    · -- 1. hi: c - (n + 1) ∈ t
      intro c hc
      simp only [mem_filter, mem_Iic] at hc ⊢
      rcases hc with ⟨⟨hc_max, hc_mod⟩, hc_le⟩
      constructor
      · have h_succ := max_vt_checksum_succ n
        omega
      · have heq : c = (c - (n + 1)) + (n + 1) := by omega
        have hmod : ((c - (n + 1)) + (n + 1)) ≡ (a + (n + 1)) [MOD m] := by {
          rw [← heq]
          exact hc_mod
        }
        exact Nat.ModEq.add_right_cancel' (n + 1) hmod
    · -- 2. i_inj: injective
      intro c1 hc1 c2 hc2 h_eq
      simp only [mem_filter, mem_Iic] at hc1 hc2
      have h1_le := hc1.2
      have h2_le := hc2.2
      omega
    · -- 3. i_surj: surjective
      intro k hk
      simp only [mem_filter, mem_Iic] at hk
      rcases hk with ⟨hk_max, hk_mod⟩
      exact ⟨k + n + 1, ⟨by {
        simp only [mem_filter, mem_Iic]
        constructor
        · constructor
          · have h_succ := max_vt_checksum_succ n
            omega
          · have heq : k ≡ a [MOD m] := hk_mod
            exact Nat.ModEq.add_right (n + 1) heq
        · omega
      }, by omega⟩⟩
    · -- 4. h_eq: f c = g (c - (n + 1))
      intro c hc
      rfl
  }
  rw [h3]
}

lemma zipWith_add_comm (A B : List Nat) :
  List.zipWith (·+·) A B = List.zipWith (·+·) B A := by {
  rw [List.zipWith_comm]
  congr
  funext a b
  exact Eq.symm (Nat.add_comm a b)
}

lemma cuculiere_reverse (n : Nat) :
  (cuculiere n).reverse = cuculiere n := by {
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold cuculiere
    generalize hl : cuculiere n = L
    have h_len : (L ++ List.replicate (n + 1) 0).length = (List.replicate (n + 1) 0 ++ L).length := by simp [Nat.add_comm]
    have h_rev_A : (L ++ List.replicate (n + 1) 0).reverse = List.replicate (n + 1) 0 ++ L.reverse := by simp
    have h_rev_B : (List.replicate (n + 1) 0 ++ L).reverse = L.reverse ++ List.replicate (n + 1) 0 := by simp
    rw [← hl] at h_rev_A h_rev_B
    rw [ih] at h_rev_A h_rev_B
    rw [hl] at h_rev_A h_rev_B
    rw [List.reverse_zipWith h_len]
    rw [h_rev_A, h_rev_B]
    exact zipWith_add_comm _ _
}

/-- The elements of Cuculiere's triangle are symmetric. -/
lemma cuculiere_get_symm (n c : Nat) (hc : c ≤ max_vt_checksum n) :
  cuculiere_get n c = cuculiere_get n (max_vt_checksum n - c) := by {
  unfold cuculiere_get
  have h_len : (cuculiere n).length = max_vt_checksum n + 1 := cuculiere_length n
  have h_lt : c < (cuculiere n).length := by omega
  have h_rev : (cuculiere n).reverse = cuculiere n := cuculiere_reverse n
  have h_getD : (cuculiere n).reverse.getD c 0 = (cuculiere n).getD ((cuculiere n).length - 1 - c) 0 := congrFun (List.getD_reverse c h_lt) 0
  rw [h_rev] at h_getD
  have h_sub : (cuculiere n).length - 1 - c = max_vt_checksum n - c := by omega
  rw [h_sub] at h_getD
  exact h_getD
}

lemma cuculiere_get_zero_eq_one (n : Nat) :
  cuculiere_get n 0 = 1 := by {
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [cuculiere_get_successor]
    have h : 0 < n + 1 := Nat.zero_lt_succ n
    simp [h]
    exact ih
}

lemma cuculiere_get_max_eq_one (n : Nat) :
  cuculiere_get n (max_vt_checksum n) = 1 := by {
  rw [cuculiere_get_symm n (max_vt_checksum n) (Nat.le_refl _)]
  have h_sub : max_vt_checksum n - max_vt_checksum n = 0 := Nat.sub_self _
  rw [h_sub]
  exact cuculiere_get_zero_eq_one n
}
lemma cuculiere_mod_sum_gen_zero (m a : Nat) :
  cuculiere_mod_sum_gen 0 m a ≤ cuculiere_mod_sum_gen 0 m 0 := by {
  unfold cuculiere_mod_sum_gen max_vt_checksum
  dsimp
  have h_Iic : Finset.Iic 0 = {0} := rfl
  simp only [h_Iic]
  cases Decidable.em (0 % m = a % m) with
  | inl h =>
    have h_filt1 : (Finset.filter (fun c => c % m = a % m) {0}) = {0} := by {
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, _⟩; rfl
      · rintro rfl; exact ⟨rfl, h⟩
    }
    have h_filt2 : (Finset.filter (fun c => c % m = 0) {0}) = {0} := by {
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, _⟩; rfl
      · rintro rfl; exact ⟨rfl, Nat.zero_mod _⟩
    }
    rw [h_filt1, h_filt2]
  | inr h =>
    have h_filt1 : (Finset.filter (fun c => c % m = a % m) {0}) = ∅ := by {
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, h_eq⟩
        exact False.elim (h h_eq)
      · intro h_in
        simp at h_in
    }
    have h_filt2 : (Finset.filter (fun c => c % m = 0) {0}) = {0} := by {
      ext x
      simp only [Finset.mem_filter, Finset.mem_singleton]
      constructor
      · rintro ⟨rfl, _⟩; rfl
      · rintro rfl; exact ⟨rfl, Nat.zero_mod _⟩
    }
    rw [h_filt1, h_filt2]
    dsimp
    exact Nat.zero_le _
}



/-- The core inductive inequality proving that the 0-th residue class is maximal.
    This works by fixing the modulus `m = n + 1`, and performing induction on the
    sequence length `k` from `0` to `n`. At each step `k`, we use `cuculiere_mod_sum_gen_successor`
    to show that the combination of `S(k, m, a) + S(k, m, a - (k+1))` preserves the maximality at 0. -/
lemma cuculiere_mod_sum_gen_max (n : Nat) (k : Nat) (a : Nat) (hk : k ≤ n) :
  cuculiere_mod_sum_gen k (n + 1) a ≤ cuculiere_mod_sum_gen k (n + 1) 0 := by {
  induction k with
  | zero =>
    exact cuculiere_mod_sum_gen_zero (n + 1) a
  | succ k' ih =>
    -- Inductive step
    sorry
}

lemma vector_card_split (n : Nat) (P : List.Vector B (n + 1) → Prop) [DecidablePred P] :
  Finset.card (Finset.filter P univ) = 
  Finset.card (Finset.filter (fun v => P (List.Vector.push v B.O)) univ) + 
  Finset.card (Finset.filter (fun v => P (List.Vector.push v B.I)) univ) := by {
  let f0 (v : List.Vector B n) : List.Vector B (n + 1) := List.Vector.push v B.O
  let f1 (v : List.Vector B n) : List.Vector B (n + 1) := List.Vector.push v B.I
  have h_inj0 : Function.Injective f0 := by
    intro v w hvw
    have h : v.val ++ [B.O] = w.val ++ [B.O] := congrArg Subtype.val hvw
    have h2 : (v.val ++ [B.O]).dropLast = (w.val ++ [B.O]).dropLast := by rw [h]
    rw [List.dropLast_concat, List.dropLast_concat] at h2
    exact Subtype.ext h2
  have h_inj1 : Function.Injective f1 := by
    intro v w hvw
    have h : v.val ++ [B.I] = w.val ++ [B.I] := congrArg Subtype.val hvw
    have h2 : (v.val ++ [B.I]).dropLast = (w.val ++ [B.I]).dropLast := by rw [h]
    rw [List.dropLast_concat, List.dropLast_concat] at h2
    exact Subtype.ext h2
  have h_disj : Disjoint (univ.image f0) (univ.image f1) := by
    rw [Finset.disjoint_left]
    intro x hx0 hx1
    simp only [f0, f1, List.Vector.push, Finset.mem_univ, Finset.mem_image, true_and] at hx0 hx1
    rcases hx0 with ⟨v, hv⟩
    rcases hx1 with ⟨w, hw⟩
    have h_eq : v.val ++ [B.O] = w.val ++ [B.I] := by
      have h1 : x.val = v.val ++ [B.O] := congrArg Subtype.val hv.symm
      have h2 : x.val = w.val ++ [B.I] := congrArg Subtype.val hw.symm
      have h1' : v.val ++ [B.O] = x.val := h1.symm
      exact h1'.trans h2
    have hl1 : (v.val ++ [B.O]).getLast (by simp) = B.O := List.getLast_concat
    simp [h_eq] at hl1
  have h_cov : univ = (univ.image f0) ∪ (univ.image f1) := by
    ext ⟨l, hl⟩
    simp only [f0, f1, List.Vector.push, Finset.mem_univ, Finset.mem_union,
       Finset.mem_image, true_and, true_iff]
    have h_not_empty : l ≠ [] := by
      intro h_emp
      rw [h_emp] at hl
      contradiction
    have h_l : l = l.dropLast ++ [l.getLast h_not_empty] :=
      (List.dropLast_append_getLast h_not_empty).symm
    have h_len2 : l.dropLast.length = n := by
      rw [List.length_dropLast]
      omega
    cases h_b : l.getLast h_not_empty
    · left
      use ⟨l.dropLast, h_len2⟩
      exact Subtype.ext (by
        dsimp [List.Vector.push]
        have h_l_copy := h_l
        rw [h_b] at h_l_copy
        exact h_l_copy.symm)
    · right
      use ⟨l.dropLast, h_len2⟩
      exact Subtype.ext (by
        dsimp [List.Vector.push]
        have h_l_copy := h_l
        rw [h_b] at h_l_copy
        exact h_l_copy.symm)
  
  have h_filter : Finset.filter P univ = (Finset.filter P (univ.image f0)) ∪
    (Finset.filter P (univ.image f1)) := by
    rw [h_cov]
    exact Finset.filter_union _ _ _
    
  have h_filter_disj : Disjoint (Finset.filter P (univ.image f0))
    (Finset.filter P (univ.image f1)) := by
    exact Finset.disjoint_filter_filter h_disj
    
  rw [h_filter, Finset.card_union_of_disjoint h_filter_disj]
  
  have h_eq0 : Finset.card (Finset.filter P (univ.image f0)) =
    Finset.card (Finset.filter (fun v => P (f0 v)) univ) := by
    rw [Finset.filter_image]
    exact Finset.card_image_of_injective _ h_inj0
    
  have h_eq1 : Finset.card (Finset.filter P (univ.image f1)) =
    Finset.card (Finset.filter (fun v => P (f1 v)) univ) := by
    rw [Finset.filter_image]
    exact Finset.card_image_of_injective _ h_inj1
    
  rw [h_eq0, h_eq1]
}

/-- Lemma: The frequency of elements with a specific checksum `c` equals the `c`-th element. -/
lemma moment_eq_cuculiere (n c : Nat) :
  Finset.card (Finset.filter (fun (x : List.Vector B n) => List.Vector.moment x = c) univ) =
    cuculiere_get n c := by {
  induction n generalizing c with
  | zero =>
    cases c with
    | zero => rfl
    | succ c =>
      have h : Finset.filter (fun (x : List.Vector B 0) => List.Vector.moment x = c + 1) univ =
        ∅ := by {
        rw [Finset.filter_eq_empty_iff]
        intro x hx
        have hx_eq : x = ⟨[], rfl⟩ := by {
          cases x with
          | mk val property =>
            cases val with
            | nil => rfl
            | cons hd tl => contradiction
        }
        rw [hx_eq]
        dsimp [List.Vector.moment, List.moment, List.moment_sub]
        omega
      }
      rw [h]
      rfl
  | succ n ih =>
    rw [cuculiere_get_successor n c]
    rw [vector_card_split n (fun x => List.Vector.moment x = c)]
    have h1 : Finset.card (Finset.filter
                (fun (v : List.Vector B n) => List.Vector.moment (List.Vector.push v B.O) =
                  c) univ) = 
              Finset.card (Finset.filter
                (fun (v : List.Vector B n) => List.Vector.moment v = c) univ) := by {
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [List.Vector.moment_push_O]
    }
    
    have h2 : Finset.card (Finset.filter
                (fun (v : List.Vector B n) => List.Vector.moment (List.Vector.push v B.I) =
                  c) univ) =
              if c < n + 1 then 0 else cuculiere_get n (c - (n + 1)) := by {
      split
      · have h_empty : Finset.filter
                  (fun (v : List.Vector B n) => List.Vector.moment (List.Vector.push v B.I) =
                    c) univ = ∅ := by {
          rw [Finset.filter_eq_empty_iff]
          intro v hv
          rw [List.Vector.moment_push_I]
          omega
        }
        rw [h_empty]
        rfl
      · have h_eq : Finset.card (Finset.filter
                      (fun (v : List.Vector B n) => List.Vector.moment (List.Vector.push v B.I) =
                        c) univ) = 
                    Finset.card (Finset.filter
                      (fun (v : List.Vector B n) => List.Vector.moment v = c - (n + 1)) univ) :=
                        by {
          congr 1
          ext v
          simp only [Finset.mem_filter, Finset.mem_univ, true_and]
          rw [List.Vector.moment_push_I]
          omega
        }
        rw [h_eq]
        rw [ih (c - (n + 1))]
    }
    rw [h1, h2, ih c]
}

lemma moment_mul_two_le_max_vt_checksum_list (l : List B) :
  List.moment l * 2 ≤ l.length * (l.length + 1) := by {
  induction l with
  | nil => rfl
  | cons b l' ih =>
    rw [List.moment_cons]
    have h_num : List.num_Is (b :: l') ≤ l'.length + 1 := by
      cases b
      · have h_num2 : List.num_Is (B.O :: l') = List.num_Is l' := rfl
        rw [h_num2]
        have h_len : List.num_Is l' ≤ l'.length := List.num_Is_le_length l'
        omega
      · have h_num2 : List.num_Is (B.I :: l') = List.num_Is l' + 1 := rfl
        rw [h_num2]
        have h_len : List.num_Is l' ≤ l'.length := List.num_Is_le_length l'
        omega
    have h_len2 : (b :: l').length = l'.length + 1 := rfl
    rw [h_len2]
    nlinarith
}

lemma moment_le_max_vt_checksum_list (l : List B) :
  List.moment l ≤ l.length * (l.length + 1) / 2 := by {
  have h := moment_mul_two_le_max_vt_checksum_list l
  omega
}

lemma moment_le_max_vt_checksum {n : Nat} (v : List.Vector B n) :
  List.Vector.moment v ≤ max_vt_checksum n := by {
  unfold List.Vector.moment max_vt_checksum
  have h := moment_le_max_vt_checksum_list v.val
  have h_len : v.val.length = n := v.property
  rw [h_len] at h
  exact h
}

/-- Formal theorem stating that the cardinality of the VT code exactly matches
    the subset summation over Cuculiere's triangle modulo n+1. -/
theorem card_VTCode_eq_cuculiere (n a : Nat) :
  Finset.card (Finset.VTCode n a) = cuculiere_mod_sum n a := by {
  unfold Finset.VTCode _root_.VTCode cuculiere_mod_sum
  have h_eq : Finset.card (Finset.filter
                (fun (v : List.Vector B n) => List.Vector.moment v % (n + 1) = a % (n + 1))
                (univ : Finset (List.Vector B n))) =
    Finset.sum (Finset.filter (fun c => c % (n + 1) =
      a % (n + 1)) (Finset.Iic (max_vt_checksum n)))
      (fun c => Finset.card (Finset.filter (fun (v : List.Vector B n) => List.Vector.moment v = c)
        (univ : Finset (List.Vector B n)))) := by
    have h_partition : Finset.filter
                         (fun (v : List.Vector B n) => List.Vector.moment v % (n + 1) =
                           a % (n + 1))
                         (univ : Finset (List.Vector B n)) = 
      Finset.biUnion (Finset.filter (fun c => c % (n + 1) = a % (n + 1))
        (Finset.Iic (max_vt_checksum n)))
        (fun c => Finset.filter (fun (v : List.Vector B n) => List.Vector.moment v = c)
          (univ : Finset (List.Vector B n))) := by
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_biUnion, Finset.mem_Iic]
      constructor
      · intro h
        use List.Vector.moment v
        have h_le : List.Vector.moment v ≤ max_vt_checksum n := moment_le_max_vt_checksum v
        exact ⟨⟨h_le, h⟩, rfl⟩
      · rintro ⟨c, ⟨_, hc_mod⟩, hv_c⟩
        rw [hv_c]
        exact hc_mod
    rw [h_partition]
    apply Finset.card_biUnion
    intro c1 _ c2 _ h_neq
    dsimp only [Function.onFun]
    rw [Finset.disjoint_filter]
    intro v _ h1 h2
    rw [h1] at h2
    exact h_neq h2
  
  have h_eq2 : (fun c => Finset.card (Finset.filter
                 (fun (v : List.Vector B n) => List.Vector.moment v = c) univ)) =
               (fun c => cuculiere_get n c) := by
    ext c
    exact moment_eq_cuculiere n c
  rw [h_eq2] at h_eq
  exact h_eq
}

/-- Tidbits from OEIS A053632 to formalize later:
    1. Row sums give A000079 (powers of 2).
    2. Sum_{k>=0} k * T(n,k) = A001788(n).
    3. T(n,k) is the number of strict partitions of k into parts <= n.
    4. max_{k>=0} T(n,k) = A025591(n). -/
lemma cuculiere_sum (n : Nat) : (cuculiere n).sum = 2^n := by {
  induction n with
  | zero => rfl
  | succ n ih =>
    unfold cuculiere
    have h_len : (cuculiere n ++ List.replicate (n + 1) 0).length =
                 (List.replicate (n + 1) 0 ++ cuculiere n).length := by
      simp [List.length_append]
      omega
    have h_zip := List.sum_add_sum_eq_sum_zipWith_of_length_eq _ _ h_len
    rw [← h_zip]
    simp [ih]
    ring
}

-- lemma cuculiere_weighted_sum (n : Nat) :
--   Finset.sum (Finset.range (max_vt_checksum n + 1)) (fun k => k * cuculiere_get n k) = 
--   if n < 2 then (if n = 0 then 0 else 1) else n * (n + 1) * 2^(n - 2) := by {
--   sorry
-- }

-- Computations for verification:
#eval cuculiere 3
-- Expected: [1, 1, 1, 2, 1, 1, 1]

#eval cuculiere 4
-- Expected: [1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1]

/-- Theorem: VT(0) has the maximum cardinality among all VT codes of length n.
    This corresponds to the sum of the 0-th residue class mod n+1 being strictly
    maximal in Cuculiere's triangle. 

    FUTURE WORK: The `cuculiere_mod_sum_gen_max` roadblock must be proven. 
    There are two primary pathways to formally prove it:

    1. The Complex Analysis Route (Elegant but requires Complex Polynomials):
       Evaluating the generating function P_n(x) = \prod_{k=1}^n (1+x^k) at the 
       (n+1)-th roots of unity \omega^j. The sum over residue class a is:
       S_a = \frac{1}{n+1} \sum_{j=0}^n \omega^{-aj} P_n(\omega^j)
       Since \omega^j are roots of z^{n+1}-1 = 0, P_n(\omega^j) remarkably evaluates 
       to 1 if n is even, and 0 if n is odd (for j \neq 0).
       This instantly evaluates the sizes:
       - If n is odd, S_a = 2^n / (n+1) for ALL a. (Perfectly equal!)
       - If n is even, S_0 = (2^n + n) / (n+1) and S_a = (2^n - 1) / (n+1).
       This immediately proves S_0 is maximal, without bounding or bijections.

    2. The Combinatorial Route (The "Necklace" Weeds):
       Proving S_0 \ge S_a combinatorially requires understanding how shifting 
       bits changes the checksum. If you cyclically shift a binary string of weight k
       by 1 position, its moment (checksum) changes by exactly +k \pmod{n+1}.
       Therefore, the cyclic group Z_{n+1} acts on the strings.
       - If \gcd(k, n+1) = 1, the cyclic shifts perfectly distribute the strings 
         of weight k across ALL n+1 residue classes equally.
       - The roadblock arises when \gcd(k, n+1) > 1 (which always happens for 
         some k if n+1 is not prime). We must use Burnside's Lemma to track the 
         sizes of the fixed-point stabilizers of these orbits, and meticulously 
         count the excess to show that the 0-th class always absorbs the positive 
         excess when n is even. 
       This requires formalizing cyclic group actions on Lists, orbit stabilizers,
       and gcd constraints, making the combinatorial route deeply entangled. -/
theorem VTCode_zero_is_max (n a : Nat) :
  Finset.card (Finset.VTCode n a) ≤ Finset.card (Finset.VTCode n 0) := by {
  rw [card_VTCode_eq_cuculiere n a]
  rw [card_VTCode_eq_cuculiere n 0]
  rw [cuculiere_mod_sum_eq_gen n a]
  rw [cuculiere_mod_sum_eq_gen n 0]
  exact cuculiere_mod_sum_gen_max n n a (Nat.le_refl n)
}

/- Note: An alternative, purely combinatorial proof of VTCode_zero_is_max 
   is formalized in Burnside.lean using cyclic shift orbits and Burnside's Lemma. -/

