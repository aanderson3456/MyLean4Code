import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Vector.Basic
import VTlean.FractalSlice
import VTlean.CuculiereCombinatorial

open Nat Finset List.Vector B

def A_mat (n : Nat) (k : Nat) : Matrix (List.Vector B n) (List.Vector B (n - 1)) Nat :=
  fun x y => if y ∈ cumulativeDels x k then 1 else 0

def B_mat (n : Nat) (k : Nat) : Matrix (List.Vector B n) (List.Vector B (n - 1)) Nat :=
  fun x y => if y ∈ cumulativeDels x k ∧ y ∉ cumulativeDels x (k - 1) then 1 else 0

lemma A_mat_eq_sum_B_mat (n : Nat) (k : Nat) :
  A_mat n k = fun x y => ∑ j ∈ Iic k, B_mat n j x y := by {
  ext x y
  induction' k with k ih
  · dsimp [A_mat, B_mat]
    -- Iic 0 is just {0}
    have h_Iic : Iic 0 = {0} := rfl
    rw [h_Iic, Finset.sum_singleton]
    simp [cumulativeDels]
  · have h_Iic : Iic (k + 1) = insert (k + 1) (Iic k) := by {
      ext j
      simp only [mem_Iic, mem_insert]
      omega
    }
    have h_not_in : (k + 1) ∉ Iic k := by simp
    rw [h_Iic, Finset.sum_insert h_not_in]
    have h_ih_eval : A_mat n k x y = ∑ j ∈ Iic k, B_mat n j x y := by {
      change A_mat n k x y = (fun x y => ∑ j ∈ Iic k, B_mat n j x y) x y
      rw [ih]
    }
    rw [← h_ih_eval]
    dsimp [A_mat, B_mat]
    have h_subset : ∀ y, y ∈ cumulativeDels x k → y ∈ cumulativeDels x (k + 1) := by {
      intro y' hy'
      cases' k with k'
      · simp [cumulativeDels] at hy'
      · dsimp [cumulativeDels] at hy' ⊢
        simp only [List.mem_toFinset] at hy' ⊢
        have h_ds : dS_le x (k' + 1) = sDel x (k' + 1) :: dS_le x k' := rfl
        rw [h_ds]
        exact List.mem_cons_of_mem _ hy'
    }
    by_cases h_k_in : y ∈ cumulativeDels x k
    · have h_k1_in : y ∈ cumulativeDels x (k + 1) := h_subset y h_k_in
      simp [h_k_in, h_k1_in]
    · by_cases h_k1_in : y ∈ cumulativeDels x (k + 1)
      · simp [h_k_in, h_k1_in]
      · simp [h_k_in, h_k1_in]
}

def is_perfect_algebraic (n : Nat) (c : List.Vector B n → Nat) : Prop :=
  ∀ y, ∑ x : List.Vector B n, A_mat n n x y * c x = 1

def appendBit {n : Nat} (v : List.Vector B n) (b : B) : List.Vector B (n + 1) :=
  ⟨v.val ++ [b], by {
    rw [List.length_append, v.property, List.length_singleton]
  }⟩

def appendBit_sub_add {n : Nat} (hn : 0 < n) (v : List.Vector B (n - 1)) (b : B) : List.Vector B (n + 1 - 1) :=
  ⟨v.val ++ [b], by {
    rw [List.length_append, v.property, List.length_singleton]
    omega
  }⟩

lemma sDel_appendBit_le {n : Nat} (hn : 0 < n) (x' : List.Vector B n) (b : B) (k : Nat) (hk : k < n) :
  sDel (appendBit x' b) k = appendBit_sub_add hn (sDel x' k) b := by {
    apply Subtype.ext
    dsimp [sDel, appendBit, appendBit_sub_add]
    have h_len : x'.val.length = n := x'.2
    have hk_list : k + 1 ≤ x'.val.length := by omega
    rw [List.sDel_append_of_lt x'.val [b] k hk_list]
}

lemma cumulativeDels_appendBit_le {n : Nat} (hn : 0 < n) (x' : List.Vector B n) (b : B) (k : Nat) (hk : k ≤ n) :
  cumulativeDels (appendBit x' b) k = (cumulativeDels x' k).image (fun y' => appendBit_sub_add hn y' b) := by {
    cases k with
    | zero =>
      simp [cumulativeDels]
      rfl
    | succ k' =>
      dsimp [cumulativeDels]
      ext y
      simp only [List.mem_toFinset, mem_image]
      constructor
      · intro hy
        have hy' := Iff.mp (mem_dS_le (appendBit x' b) y k') hy
        obtain ⟨i, hi_le, hi_eq⟩ := hy'
        have h_i_lt : i < n := by omega
        use sDel x' i
        constructor
        · apply Iff.mpr (mem_dS_le x' (sDel x' i) k')
          use i
        · rw [hi_eq]
          exact (sDel_appendBit_le hn x' b i h_i_lt).symm
      · rintro ⟨y', hy', hy_eq⟩
        have hy'' := Iff.mp (mem_dS_le x' y' k') hy'
        obtain ⟨i, hi_le, hi_eq⟩ := hy''
        have h_i_lt : i < n := by omega
        apply Iff.mpr (mem_dS_le (appendBit x' b) y k')
        use i
        refine ⟨hi_le, ?_⟩
        rw [← hy_eq, hi_eq]
        exact (sDel_appendBit_le hn x' b i h_i_lt).symm
}

lemma appendBit_sub_add_inj {n : Nat} (hn : 0 < n) (y z : List.Vector B (n - 1)) (b c : B) :
  appendBit_sub_add hn y b = appendBit_sub_add hn z c ↔ y = z ∧ b = c := by {
  constructor
  · intro h
    have h_val : (appendBit_sub_add hn y b).val = (appendBit_sub_add hn z c).val := by rw [h]
    dsimp [appendBit_sub_add] at h_val
    have h_len : y.val.length = z.val.length := by rw [y.property, z.property]
    have h_inj := List.append_inj h_val h_len
    rcases h_inj with ⟨hy, hc⟩
    constructor
    · exact Subtype.ext hy
    · cases b <;> cases c <;> simp at hc <;> simp
  · rintro ⟨rfl, rfl⟩
    rfl
}

lemma B_mat_appendBit_eq {n : Nat} (hn : 0 < n) (x' : List.Vector B n) (bx : B) (y' : List.Vector B (n - 1)) (by_ : B) (k : Nat) (hk : k ≤ n) :
  B_mat (n + 1) k (appendBit x' bx) (appendBit_sub_add hn y' by_) = if bx = by_ then B_mat n k x' y' else 0 := by {
    dsimp [B_mat]
    have h_cumul := cumulativeDels_appendBit_le hn x' bx k hk
    have h_cumul_prev : cumulativeDels (appendBit x' bx) (k - 1) = (cumulativeDels x' (k - 1)).image (fun y => appendBit_sub_add hn y bx) := by {
      apply cumulativeDels_appendBit_le hn x' bx (k - 1)
      omega
    }
    have h_iff : (appendBit_sub_add hn y' by_ ∈ cumulativeDels (appendBit x' bx) k) ↔ (y' ∈ cumulativeDels x' k ∧ bx = by_) := by {
      rw [h_cumul]
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨a, ha, h_eq⟩
        have h_inj := Iff.mp (appendBit_sub_add_inj hn a y' bx by_) h_eq
        rw [h_inj.1] at ha
        exact ⟨ha, h_inj.2⟩
      · rintro ⟨hy, rfl⟩
        use y'
    }
    have h_iff_prev : (appendBit_sub_add hn y' by_ ∈ cumulativeDels (appendBit x' bx) (k - 1)) ↔ (y' ∈ cumulativeDels x' (k - 1) ∧ bx = by_) := by {
      rw [h_cumul_prev]
      simp only [Finset.mem_image]
      constructor
      · rintro ⟨a, ha, h_eq⟩
        have h_inj := Iff.mp (appendBit_sub_add_inj hn a y' bx by_) h_eq
        rw [h_inj.1] at ha
        exact ⟨ha, h_inj.2⟩
      · rintro ⟨hy, rfl⟩
        use y'
    }
    have h_cond : (appendBit_sub_add hn y' by_ ∈ cumulativeDels (appendBit x' bx) k ∧ appendBit_sub_add hn y' by_ ∉ cumulativeDels (appendBit x' bx) (k - 1)) ↔ (bx = by_ ∧ y' ∈ cumulativeDels x' k ∧ y' ∉ cumulativeDels x' (k - 1)) := by {
      rw [h_iff, h_iff_prev]
      tauto
    }
    clear h_cumul h_cumul_prev h_iff h_iff_prev
    split_ifs <;> tauto
}

lemma cumulativeDels_succ {n : Nat} (x : List.Vector B n) (k : Nat) :
  cumulativeDels x (k + 1) = insert (sDel x k) (cumulativeDels x k) := by {
    cases k with
    | zero =>
      dsimp [cumulativeDels]
      have h : dS_le x 0 = [sDel x 0] := rfl
      rw [h]
      simp
    | succ k' =>
      dsimp [cumulativeDels]
      have h : dS_le x (k' + 1) = sDel x (k' + 1) :: dS_le x k' := rfl
      rw [h]
      simp
}

lemma y_in_cumulativeDels_appendBit_sub_add {n : Nat} (hn : 0 < n) (y' : List.Vector B (n - 1)) (b : B) :
  y' ∈ cumulativeDels (appendBit_sub_add hn y' b) n := by {
    cases n with
    | zero => contradiction
    | succ n' =>
      have h_sDel : sDel (appendBit_sub_add hn y' b) n' = y' := by {
        apply Subtype.ext
        dsimp [sDel, appendBit_sub_add]
        have h_len : y'.val.length = n' := y'.2
        have h_sDel_append : List.sDel (y'.val ++ [b]) n' = y'.val ++ List.sDel [b] (n' - y'.val.length) := by {
          apply List.sDel_append_of_ge
          · omega
          · exact List.cons_ne_nil b []
        }
        rw [h_sDel_append, h_len]
        have h_sub : n' - n' = 0 := by omega
        rw [h_sub]
        have h_nil : List.sDel [b] 0 = [] := rfl
        rw [h_nil, List.append_nil]
      }
      dsimp [cumulativeDels]
      have h_mem : y' ∈ dS_le (appendBit_sub_add hn y' b) n' := by {
        have h_iff := mem_dS_le (X := appendBit_sub_add hn y' b) (Y := y') (k := n')
        apply h_iff.mpr
        use n'
        exact ⟨le_refl _, h_sDel.symm⟩
      }
      exact List.mem_toFinset.mpr h_mem
}

lemma B_mat_n_plus_1_appendBit_eq {n : Nat} (hn : 0 < n) (x' : List.Vector B n) (bx : B) (y' : List.Vector B (n - 1)) (by_ : B) :
  B_mat (n + 1) (n + 1) (appendBit x' bx) (appendBit_sub_add hn y' by_) =
    if x' = appendBit_sub_add hn y' by_ ∧ bx ≠ by_ then 1 else 0 := by {
    dsimp [B_mat]
    have h_cumul := cumulativeDels_succ (appendBit x' bx) n
    rw [h_cumul]
    have h_sDel : sDel (appendBit x' bx) n = x' := by {
      apply Subtype.ext
      dsimp [sDel, appendBit]
      have h_len : x'.val.length = n := x'.2
      have h_sDel_append : List.sDel (x'.val ++ [bx]) n = x'.val ++ List.sDel [bx] (n - x'.val.length) := by {
        apply List.sDel_append_of_ge
        · omega
        · exact List.cons_ne_nil bx []
      }
      rw [h_sDel_append, h_len]
      have h_sub : n - n = 0 := by omega
      rw [h_sub]
      have h_nil : List.sDel [bx] 0 = [] := rfl
      rw [h_nil, List.append_nil]
    }
    rw [h_sDel]
    have h_iff : (appendBit_sub_add hn y' by_ ∈ insert x' (cumulativeDels (appendBit x' bx) n) ∧
      appendBit_sub_add hn y' by_ ∉ cumulativeDels (appendBit x' bx) n) ↔
      (x' = appendBit_sub_add hn y' by_ ∧ bx ≠ by_) := by {
      constructor
      · rintro ⟨h_in_insert, h_not_in⟩
        have h_in_insert_or : appendBit_sub_add hn y' by_ = x' ∨ appendBit_sub_add hn y' by_ ∈ cumulativeDels (appendBit x' bx) n := Finset.mem_insert.mp h_in_insert
        rcases h_in_insert_or with h_eq | h_in
        · refine ⟨h_eq.symm, ?_⟩
          intro hbx
          rw [hbx] at h_not_in
          have h_in_cumul : appendBit_sub_add hn y' by_ ∈ cumulativeDels (appendBit x' by_) n := by {
            rw [h_eq.symm]
            have h_img := cumulativeDels_appendBit_le hn (appendBit_sub_add hn y' by_) by_ n (le_refl n)
            rw [h_img]
            apply Finset.mem_image_of_mem
            exact y_in_cumulativeDels_appendBit_sub_add hn y' by_
          }
          exact h_not_in h_in_cumul
        · contradiction
      · rintro ⟨rfl, hbx⟩
        refine ⟨Finset.mem_insert_self _ _, ?_⟩
        intro h_in
        have h_img := cumulativeDels_appendBit_le hn (appendBit_sub_add hn y' by_) bx n (le_refl n)
        rw [h_img] at h_in
        simp only [mem_image] at h_in
        rcases h_in with ⟨z, hz_in, hz_eq⟩
        have h_inj := (appendBit_sub_add_inj hn y' z by_ bx).mp hz_eq.symm
        obtain ⟨_, h_eq⟩ := h_inj
        exact hbx h_eq.symm
    }
    split_ifs
    · rfl
    · tauto
    · tauto
    · rfl
}

lemma A_mat_n_appendBit_eq {n : Nat} (hn : 0 < n) (x' : List.Vector B n) (bx : B) (y' : List.Vector B (n - 1)) (by_ : B) :
  A_mat (n + 1) n (appendBit x' bx) (appendBit_sub_add hn y' by_) = if bx = by_ then A_mat n n x' y' else 0 := by {
    rw [A_mat_eq_sum_B_mat (n + 1) n, A_mat_eq_sum_B_mat n n]
    split_ifs with hbx
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Iic] at hk
      rw [B_mat_appendBit_eq hn x' bx y' by_ k hk, if_pos hbx]
    · have h_zero : ∑ j ∈ Iic n, 0 = 0 := by simp
      rw [← h_zero]
      apply Finset.sum_congr rfl
      intro k hk
      rw [Finset.mem_Iic] at hk
      rw [B_mat_appendBit_eq hn x' bx y' by_ k hk, if_neg hbx]
}

lemma A_mat_n_plus_1_eq {n : Nat} (x : List.Vector B (n + 1)) (y : List.Vector B n) :
  A_mat (n + 1) (n + 1) x y = A_mat (n + 1) n x y + B_mat (n + 1) (n + 1) x y := by {
    rw [A_mat_eq_sum_B_mat (n + 1) (n + 1), A_mat_eq_sum_B_mat (n + 1) n]
    dsimp only []
    have h_Iic : Iic (n + 1) = insert (n + 1) (Iic n) := by {
      ext j
      simp only [mem_Iic, mem_insert]
      omega
    }
    have h_not_in : (n + 1) ∉ Iic n := by simp
    rw [h_Iic, Finset.sum_insert h_not_in]
    exact add_comm _ _
}

def vectorAppendEquiv {n : Nat} : List.Vector B n × B ≃ List.Vector B (n + 1) where
  toFun := fun ⟨x, b⟩ => appendBit x b
  invFun := fun x => ⟨⟨x.val.take n, by {
    have hlen : x.val.length = n + 1 := x.2
    rw [List.length_take, hlen]
    exact Nat.min_eq_left (by omega)
  }⟩, x.val.getLast (by {
    have hlen : x.val.length = n + 1 := x.2
    intro h
    rw [h] at hlen
    contradiction
  })⟩
  left_inv := by {
    rintro ⟨x, b⟩
    apply Prod.ext
    · apply Subtype.ext
      dsimp [appendBit]
      have hlen : x.val.length = n := x.2
      have h_take : (x.val ++ [b]).take x.val.length = x.val := List.take_left
      rw [hlen] at h_take
      exact h_take
    · dsimp [appendBit]
      simp
  }
  right_inv := by {
    rintro ⟨x_val, h_len⟩
    apply Subtype.ext
    dsimp [appendBit]
    have h_dropLast : x_val.take n = x_val.dropLast := by {
      have h_len_minus_1 : n = x_val.length - 1 := by omega
      rw [h_len_minus_1]
      exact List.dropLast_eq_take.symm
    }
    rw [h_dropLast]
    exact List.dropLast_append_getLast (by {
      intro h
      have h2 : x_val.length = 0 := by rw [h]; rfl
      omega
    })
  }

lemma sum_appendBit_aux {n : Nat} (f : List.Vector B (n + 1) → Nat) :
  ∑ x : List.Vector B (n + 1), f x = ∑ p : (List.Vector B n × B), f (vectorAppendEquiv p) := by {
    exact (Equiv.sum_comp vectorAppendEquiv f).symm
  }

lemma sum_appendBit_aux2 {n : Nat} (f : List.Vector B (n + 1) → Nat) :
  ∑ p : List.Vector B n × B, f (vectorAppendEquiv p) = (∑ x' : List.Vector B n, f (vectorAppendEquiv (x', B.O))) + (∑ x' : List.Vector B n, f (vectorAppendEquiv (x', B.I))) := by {
    have h_prod : ∑ p : List.Vector B n × B, f (vectorAppendEquiv p) = ∑ x' : List.Vector B n, ∑ b : B, f (vectorAppendEquiv (x', b)) := by {
      have h_univ : (Finset.univ : Finset (List.Vector B n × B)) = (Finset.univ : Finset (List.Vector B n)) ×ˢ (Finset.univ : Finset B) := rfl
      rw [h_univ]
      exact Finset.sum_product' Finset.univ Finset.univ (fun x' b => f (vectorAppendEquiv (x', b)))
    }
    rw [h_prod]
    have h_inner : ∀ x', ∑ b : B, f (vectorAppendEquiv (x', b)) = f (vectorAppendEquiv (x', B.O)) + f (vectorAppendEquiv (x', B.I)) := by {
      intro x'
      have h_univ : (Finset.univ : Finset B) = {B.O, B.I} := rfl
      rw [h_univ]
      have h_disj : B.O ≠ B.I := by decide
      rw [Finset.sum_insert (by simp [h_disj])]
      rw [Finset.sum_singleton]
    }
    have h_rw : (∑ x' : List.Vector B n, ∑ b : B, f (vectorAppendEquiv (x', b))) = ∑ x' : List.Vector B n, (f (vectorAppendEquiv (x', B.O)) + f (vectorAppendEquiv (x', B.I))) := by {
      apply Finset.sum_congr rfl
      intro x' _
      exact h_inner x'
    }
    rw [h_rw]
    exact Finset.sum_add_distrib
  }

lemma sum_appendBit {n : Nat} (f : List.Vector B (n + 1) → Nat) :
  ∑ x : List.Vector B (n + 1), f x = (∑ x' : List.Vector B n, f (appendBit x' B.O)) + (∑ x' : List.Vector B n, f (appendBit x' B.I)) := by {
    rw [sum_appendBit_aux, sum_appendBit_aux2]
    rfl
  }

def c_0 {n : Nat} (c : List.Vector B (n + 1) → Nat) : List.Vector B n → Nat :=
  fun x => c (appendBit x B.O)

def c_1 {n : Nat} (c : List.Vector B (n + 1) → Nat) : List.Vector B n → Nat :=
  fun x => c (appendBit x B.I)

def e_0 {n : Nat} (hn : 0 < n) (c : List.Vector B (n + 1) → Nat) : List.Vector B (n - 1) → Nat :=
  fun y => c (appendBit (appendBit_sub_add hn y B.O) B.I)

def e_1 {n : Nat} (hn : 0 < n) (c : List.Vector B (n + 1) → Nat) : List.Vector B (n - 1) → Nat :=
  fun y => c (appendBit (appendBit_sub_add hn y B.I) B.O)

lemma perfect_code_1_step_reduction {n : Nat} (hn : 0 < n) (c : List.Vector B (n + 1) → Nat)
    (hc : is_perfect_algebraic (n + 1) c) :
  ∀ y' : List.Vector B (n - 1),
    (∑ x' : List.Vector B n, A_mat n n x' y' * (c_0 c x')) + e_0 hn c y' = 1 ∧
    (∑ x' : List.Vector B n, A_mat n n x' y' * (c_1 c x')) + e_1 hn c y' = 1 := by {
  intro y'
  constructor
  · have hy0 := hc (appendBit_sub_add hn y' B.O)
    have h_sum : ∑ x : List.Vector B (n + 1), A_mat (n + 1) (n + 1) x (appendBit_sub_add hn y' B.O) * c x =
      (∑ x' : List.Vector B n, A_mat n n x' y' * (c_0 c x')) + e_0 hn c y' := by {
        have h_split := sum_appendBit (fun x => A_mat (n + 1) (n + 1) x (appendBit_sub_add hn y' B.O) * c x)
        rw [h_split]
        have h_sum_O : ∑ x' : List.Vector B n, A_mat (n + 1) (n + 1) (appendBit x' B.O) (appendBit_sub_add hn y' B.O) * c (appendBit x' B.O) =
          ∑ x' : List.Vector B n, A_mat n n x' y' * c_0 c x' := by {
          apply Finset.sum_congr rfl
          intro x' _
          rw [A_mat_n_plus_1_eq, A_mat_n_appendBit_eq hn x' B.O y' B.O, B_mat_n_plus_1_appendBit_eq hn x' B.O y' B.O]
          dsimp [c_0]
          simp
        }
        have h_sum_I : ∑ x' : List.Vector B n, A_mat (n + 1) (n + 1) (appendBit x' B.I) (appendBit_sub_add hn y' B.O) * c (appendBit x' B.I) =
          e_0 hn c y' := by {
          have h_eq2 : ∑ x' : List.Vector B n, A_mat (n + 1) (n + 1) (appendBit x' B.I) (appendBit_sub_add hn y' B.O) * c (appendBit x' B.I) =
            ∑ x' : List.Vector B n, (if x' = appendBit_sub_add hn y' B.O then 1 else 0) * c (appendBit x' B.I) := by {
            apply Finset.sum_congr rfl
            intro x' _
            rw [A_mat_n_plus_1_eq, A_mat_n_appendBit_eq hn x' B.I y' B.O, B_mat_n_plus_1_appendBit_eq hn x' B.I y' B.O]
            have h_neq : B.I ≠ B.O := by decide
            simp [h_neq]
          }
          rw [h_eq2]
          have h_sum_ite : ∑ x' : List.Vector B n, (if x' = appendBit_sub_add hn y' B.O then 1 else 0) * c (appendBit x' B.I) = c (appendBit (appendBit_sub_add hn y' B.O) B.I) := by {
            have h_mul : ∀ x', (if x' = appendBit_sub_add hn y' B.O then 1 else 0) * c (appendBit x' B.I) = if x' = appendBit_sub_add hn y' B.O then c (appendBit x' B.I) else 0 := by {
              intro x'
              split_ifs <;> simp
            }
            have h_eq3 : ∑ x' : List.Vector B n, (if x' = appendBit_sub_add hn y' B.O then 1 else 0) * c (appendBit x' B.I) = ∑ x' : List.Vector B n, if x' = appendBit_sub_add hn y' B.O then c (appendBit x' B.I) else 0 := by {
              apply Finset.sum_congr rfl
              intro x' _
              exact h_mul x'
            }
            rw [h_eq3]
            simp [Finset.sum_ite_eq']
          }
          rw [h_sum_ite]
          rfl
        }
        rw [h_sum_O, h_sum_I]
    }
    rw [← h_sum]
    exact hy0
  · have hy1 := hc (appendBit_sub_add hn y' B.I)
    have h_sum : ∑ x : List.Vector B (n + 1), A_mat (n + 1) (n + 1) x (appendBit_sub_add hn y' B.I) * c x =
      (∑ x' : List.Vector B n, A_mat n n x' y' * (c_1 c x')) + e_1 hn c y' := by {
        have h_split := sum_appendBit (fun x => A_mat (n + 1) (n + 1) x (appendBit_sub_add hn y' B.I) * c x)
        rw [h_split]
        have h_sum_I : ∑ x' : List.Vector B n, A_mat (n + 1) (n + 1) (appendBit x' B.I) (appendBit_sub_add hn y' B.I) * c (appendBit x' B.I) =
          ∑ x' : List.Vector B n, A_mat n n x' y' * c_1 c x' := by {
          apply Finset.sum_congr rfl
          intro x' _
          rw [A_mat_n_plus_1_eq, A_mat_n_appendBit_eq hn x' B.I y' B.I, B_mat_n_plus_1_appendBit_eq hn x' B.I y' B.I]
          dsimp [c_1]
          simp
        }
        have h_sum_O : ∑ x' : List.Vector B n, A_mat (n + 1) (n + 1) (appendBit x' B.O) (appendBit_sub_add hn y' B.I) * c (appendBit x' B.O) =
          e_1 hn c y' := by {
          have h_eq2 : ∑ x' : List.Vector B n, A_mat (n + 1) (n + 1) (appendBit x' B.O) (appendBit_sub_add hn y' B.I) * c (appendBit x' B.O) =
            ∑ x' : List.Vector B n, (if x' = appendBit_sub_add hn y' B.I then 1 else 0) * c (appendBit x' B.O) := by {
            apply Finset.sum_congr rfl
            intro x' _
            rw [A_mat_n_plus_1_eq, A_mat_n_appendBit_eq hn x' B.O y' B.I, B_mat_n_plus_1_appendBit_eq hn x' B.O y' B.I]
            have h_neq : B.O ≠ B.I := by decide
            simp [h_neq]
          }
          rw [h_eq2]
          have h_sum_ite : ∑ x' : List.Vector B n, (if x' = appendBit_sub_add hn y' B.I then 1 else 0) * c (appendBit x' B.O) = c (appendBit (appendBit_sub_add hn y' B.I) B.O) := by {
            have h_mul : ∀ x', (if x' = appendBit_sub_add hn y' B.I then 1 else 0) * c (appendBit x' B.O) = if x' = appendBit_sub_add hn y' B.I then c (appendBit x' B.O) else 0 := by {
              intro x'
              split_ifs <;> simp
            }
            have h_eq3 : ∑ x' : List.Vector B n, (if x' = appendBit_sub_add hn y' B.I then 1 else 0) * c (appendBit x' B.O) = ∑ x' : List.Vector B n, if x' = appendBit_sub_add hn y' B.I then c (appendBit x' B.O) else 0 := by {
              apply Finset.sum_congr rfl
              intro x' _
              exact h_mul x'
            }
            rw [h_eq3]
            simp [Finset.sum_ite_eq']
          }
          rw [h_sum_ite]
          rfl
        }
        rw [h_sum_I, h_sum_O, add_comm]
    }
    rw [← h_sum]
    exact hy1
}

def r_alg {n : Nat} (x : List.Vector B n) : Nat :=
  ∑ y : List.Vector B (n - 1), A_mat n n x y

lemma perfect_code_1_step_sum {n : Nat} (hn : 0 < n) (c : List.Vector B (n + 1) → Nat)
    (hc : is_perfect_algebraic (n + 1) c) :
  (∑ x' : List.Vector B n, r_alg x' * c_0 c x') + ∑ y' : List.Vector B (n - 1), e_0 hn c y' = 2 ^ (n - 1) ∧
  (∑ x' : List.Vector B n, r_alg x' * c_1 c x') + ∑ y' : List.Vector B (n - 1), e_1 hn c y' = 2 ^ (n - 1) := by {
  have h_red := perfect_code_1_step_reduction hn c hc
  have h_card_y : (Finset.univ : Finset (List.Vector B (n - 1))).card = 2 ^ (n - 1) := by simp
  constructor
  · have h_sum1 : ∑ y' : List.Vector B (n - 1), ((∑ x' : List.Vector B n, A_mat n n x' y' * c_0 c x') + e_0 hn c y') = ∑ y' : List.Vector B (n - 1), 1 := by {
      apply Finset.sum_congr rfl
      intro y' _
      exact (h_red y').1
    }
    rw [Finset.sum_const, h_card_y, smul_eq_mul, mul_one] at h_sum1
    rw [Finset.sum_add_distrib] at h_sum1
    have h_swap : ∑ y' : List.Vector B (n - 1), ∑ x' : List.Vector B n, A_mat n n x' y' * c_0 c x' = ∑ x' : List.Vector B n, r_alg x' * c_0 c x' := by {
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x' _
      have h_mul_sum : ∑ y' : List.Vector B (n - 1), A_mat n n x' y' * c_0 c x' = (∑ y' : List.Vector B (n - 1), A_mat n n x' y') * c_0 c x' := by {
        exact (Finset.sum_mul _ _ _).symm
      }
      rw [h_mul_sum]
      rfl
    }
    rw [h_swap] at h_sum1
    exact h_sum1
  · have h_sum2 : ∑ y' : List.Vector B (n - 1), ((∑ x' : List.Vector B n, A_mat n n x' y' * c_1 c x') + e_1 hn c y') = ∑ y' : List.Vector B (n - 1), 1 := by {
      apply Finset.sum_congr rfl
      intro y' _
      exact (h_red y').2
    }
    rw [Finset.sum_const, h_card_y, smul_eq_mul, mul_one] at h_sum2
    rw [Finset.sum_add_distrib] at h_sum2
    have h_swap : ∑ y' : List.Vector B (n - 1), ∑ x' : List.Vector B n, A_mat n n x' y' * c_1 c x' = ∑ x' : List.Vector B n, r_alg x' * c_1 c x' := by {
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro x' _
      have h_mul_sum : ∑ y' : List.Vector B (n - 1), A_mat n n x' y' * c_1 c x' = (∑ y' : List.Vector B (n - 1), A_mat n n x' y') * c_1 c x' := by {
        exact (Finset.sum_mul _ _ _).symm
      }
      rw [h_mul_sum]
      rfl
    }
    rw [h_swap] at h_sum2
    exact h_sum2
}

/-- The recursive unrolling of the perfect code equation forces the total cardinality
to match one of the n+1 combinatorial subset sums T(n, k, a). -/
lemma perfect_code_card_eq_sum_T {n : Nat} (c : List.Vector B n → Nat) (hc : is_perfect_algebraic n c) :
  ∃ a, (∑ x, c x) = ∑ k ∈ Finset.Iic n, T n k a := by sorry


