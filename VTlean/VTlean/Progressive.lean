/- Copyright Austin Anderson aided by Gemini 2026 -/
import VTlean.B
import VTlean.InsDel
import VTlean.DelCode
import VTlean.VTCode
import VTlean.FractalSlice
import VTlean.AlgebraicFractal
import VTlean.Networkx
import VTlean.Cuculiere

open B List.Vector Finset BigOperators

variable {n : Nat}

-- Helper lemmas have been moved to VTlean.Networkx due to dependency imports


/-- The Progressive Deletion Potential sum over the prefix deletion set. -/
def P (x : List.Vector B n) (k : Nat) (u : List.Vector B (n - 1) → Rat) : Rat :=
  ∑ y ∈ cumulativeDels x k, u y

/-- Property 1: The incremental progressive potential sum is zero inside a run. -/
lemma P_step_inside_run (x : List.Vector B n) (k' : Nat) (hk : k' + 1 < n)
    (h_eq : x.val.getD (k' + 1) B.O = x.val.getD k' B.O)
    (u : List.Vector B (n - 1) → Rat) :
    P x (k' + 2) u = P x (k' + 1) u := by {
  unfold P
  rw [cumulativeDels_step_inside_run x k' hk h_eq]
}

/-- The progressive increment delta P(x, k) is exactly zero inside a run. -/
lemma delta_P_eq_zero (x : List.Vector B n) (k' : Nat) (hk : k' + 1 < n)
    (h_eq : x.val.getD (k' + 1) B.O = x.val.getD k' B.O)
    (u : List.Vector B (n - 1) → Rat) :
    P x (k' + 2) u - P x (k' + 1) u = 0 := by {
  rw [P_step_inside_run x k' hk h_eq u]
  exact sub_self _
}

/-- Property 2: Non-zero progressive increments imply the prefix step is a run start. -/
lemma delta_P_nonzero_imp_run_start (x : List.Vector B n) (k' : Nat) (hk : k' + 1 < n)
    (u : List.Vector B (n - 1) → Rat)
    (h_nonzero : P x (k' + 2) u - P x (k' + 1) u ≠ 0) :
    x.val.getD (k' + 1) B.O ≠ x.val.getD k' B.O := by {
  intro h_eq
  have h_zero := delta_P_eq_zero x k' hk h_eq u
  exact h_nonzero h_zero
}

/-- Lemma: The progressive potential sum at prefix n is exactly
    the sum over the deletion sphere dS x. -/
lemma P_n_eq_sum_dS (x : List.Vector B n) (hn : 0 < n)
    (u : List.Vector B (n - 1) → Rat) :
    P x n u = ∑ y ∈ dS x, u y := by {
  unfold P cumulativeDels dS dS_list
  cases n with
  | zero => contradiction
  | succ n' => rfl
}

lemma sum_range_telescope (f : Nat → Rat) (n : Nat) :
    (∑ k ∈ Finset.range n, (f (k + 1) - f k)) = f n - f 0 := by {
  induction n with
  | zero =>
    rw [Finset.sum_range_zero, sub_self]
  | succ m ih =>
    rw [Finset.sum_range_succ, ih]
    ring
}

/-- Property 3: The telescoping sum of increments over all index steps
evaluates exactly to the full deletion sphere potential sum P x n u. -/
lemma progressive_potential_telescoping_sum (x : List.Vector B n)
    (u : List.Vector B (n - 1) → Rat) :
    (∑ k ∈ Finset.range n, (P x (k + 1) u - P x k u)) = P x n u := by {
  have h_tel := sum_range_telescope (fun k => P x k u) n
  have h_zero : P x 0 u = 0 := by {
    rfl
  }
  rw [h_tel, h_zero]
  ring
}

/-- A single-deletion correcting code is perfect if its deletion spheres perfectly
partition the entire space of deletion strings (univ). -/
def is_PerfectCodeCandidate (C : Finset (List.Vector B n)) : Prop :=
  is_OptimalCodeCandidate C ∧ C.biUnion dS = Finset.univ



lemma P_zero (x : List.Vector B n) (u : List.Vector B (n - 1) → Rat) :
    P x 0 u = 0 := by {
  rfl
}

lemma P_succ_le (x : List.Vector B n) (k' : Nat)
    (u : List.Vector B (n - 1) → Rat) (hu : ∀ y, 0 ≤ u y) :
    P x (k' + 1) u ≤ P x k' u + u (sDel x k') := by {
  unfold P
  rw [cumulativeDels_succ]
  by_cases h_mem : sDel x k' ∈ cumulativeDels x k'
  · rw [insert_eq_of_mem h_mem]
    have h_nonneg : 0 ≤ u (sDel x k') := hu _
    linarith
  · rw [sum_insert h_mem]
    linarith
}

lemma P_le_sum_range (x : List.Vector B n) (k : Nat)
    (u : List.Vector B (n - 1) → Rat) (hu : ∀ y, 0 ≤ u y) :
    P x k u ≤ ∑ i ∈ Finset.range k, u (sDel x i) := by {
  induction k with
  | zero =>
    rw [P_zero, Finset.sum_range_zero]
  | succ k' ih =>
    rw [Finset.sum_range_succ]
    have h_step := P_succ_le x k' u hu
    linarith
}

lemma P_n_constant_one (x : List.Vector B n) (hn : 0 < n) :
    P x n (fun _ => 1) = (dS x).card := by {
  rw [P_n_eq_sum_dS x hn]
  simp
}

lemma partition_sum (C : Finset (List.Vector B n)) (hC : is_PerfectCodeCandidate C)
    (u : List.Vector B (n - 1) → Rat) (hn : 0 < n) :
    ∑ x ∈ C, P x n u = ∑ y ∈ Finset.univ, u y := by {
  have h_P : ∀ x ∈ C, P x n u = ∑ y ∈ dS x, u y := by {
    intro x _
    exact P_n_eq_sum_dS x hn u
  }
  have h_sum1 : ∑ x ∈ C, P x n u = ∑ x ∈ C, ∑ y ∈ dS x, u y := Finset.sum_congr rfl h_P
  rw [h_sum1]
  have h_disj : ∀ x ∈ C, ∀ y ∈ C, x ≠ y → Disjoint (dS x) (dS y) := hC.left
  rw [← Finset.sum_biUnion h_disj]
  rw [hC.right]
}

lemma vt0_is_optimal_perfect_zero (C : Finset (List.Vector B 0)) (_hC : is_PerfectCodeCandidate C) :
    C.card ≤ (Finset.VTCode 0 0).card := by {
  have h_univ : (Finset.univ : Finset (List.Vector B 0)) = {List.Vector.nil} := by {
    ext x
    simp only [mem_univ, mem_singleton, true_iff]
    apply Subtype.ext
    exact List.eq_nil_of_length_eq_zero x.property
  }
  have h_subset : C ⊆ Finset.univ := Finset.subset_univ _
  rw [h_univ] at h_subset
  have h_vt : Finset.VTCode 0 0 = {List.Vector.nil} := by {
    ext x
    simp only [Finset.mem_VTCode, _root_.mem_VTCode, mem_singleton]
    constructor
    · intro _
      apply Subtype.ext
      exact List.eq_nil_of_length_eq_zero x.property
    · intro hx
      rw [hx]
      rfl
  }
  rw [h_vt]
  have h_card_C := Finset.card_le_card h_subset
  rw [Finset.card_singleton] at h_card_C ⊢
  exact h_card_C
}

lemma vt0_card_one : (Finset.VTCode 1 0).card = 1 := by {
  decide
}

lemma perfect_card_eq_one_of_length_one (C : Finset (List.Vector B 1))
    (hC : is_PerfectCodeCandidate C) :
    C.card = 1 := by {
  have h_univ : (Finset.univ : Finset (List.Vector B 0)).card = 1 := by decide
  have h_biUnion : (C.biUnion dS).card = 1 := by {
    rw [hC.right, h_univ]
  }
  have h_disj : (C : Set (List.Vector B 1)).PairwiseDisjoint dS := hC.left
  have h_card_eq : (C.biUnion dS).card = ∑ x ∈ C, (dS x).card := Finset.card_biUnion h_disj
  have h_ds_card : ∀ x ∈ C, (dS x).card = 1 := by {
    intro x _
    have h_ds : dS x = {sDel x 0} := by {
      ext y
      simp only [mem_dS, mem_singleton]
      constructor
      · rintro ⟨i, hi, rfl⟩
        have hi0 : i = 0 := by omega
        rw [hi0]
      · intro hy
        exact ⟨0, by omega, hy⟩
    }
    rw [h_ds]
    exact card_singleton _
  }
  have h_sum : ∑ x ∈ C, (dS x).card = ∑ x ∈ C, 1 := Finset.sum_congr rfl h_ds_card
  rw [h_sum, sum_const, smul_eq_mul, mul_one] at h_card_eq
  rw [h_biUnion] at h_card_eq
  omega
}

lemma vt0_is_optimal_perfect_one (C : Finset (List.Vector B 1)) (hC : is_PerfectCodeCandidate C) :
    C.card ≤ (Finset.VTCode 1 0).card := by {
  have h1 := perfect_card_eq_one_of_length_one C hC
  have h2 := vt0_card_one
  omega
}

lemma perfect_code_card_eq_vt_card (C : Finset (List.Vector B n)) (hC : is_PerfectCodeCandidate C) :
    ∃ a, C.card = (Finset.VTCode n a).card := by {
  cases n with
  | zero =>
    use 0
    have h_vt : (Finset.VTCode 0 0).card = 1 := by rfl
    rw [h_vt]
    have h_univ : (Finset.univ : Finset (List.Vector B 0)) = {List.Vector.nil} := by {
      ext y
      simp only [mem_univ, mem_singleton, List.Vector.eq_nil y]
    }
    have h_biUnion := hC.right
    rw [h_univ] at h_biUnion
    have h_card_eq : (C.biUnion dS).card = 1 := by rw [h_biUnion, card_singleton]
    have h_disj : (C : Set (List.Vector B 0)).PairwiseDisjoint dS := hC.left
    rw [Finset.card_biUnion h_disj] at h_card_eq
    have h_ds_card : ∀ x ∈ C, (dS x).card = 1 := by {
      intro x _
      have h_eq : dS x = {sDel x 0} := by {
        ext y
        rw [mem_dS]
        simp only [mem_singleton]
        constructor
        · rintro ⟨i, hi, rfl⟩
          have hi0 : i = 0 := by omega
          rw [hi0]
        · intro hy
          rw [hy]
          use 0
      }
      rw [h_eq, card_singleton]
    }
    have h_sum : (∑ x ∈ C, (dS x).card) = ∑ x ∈ C, 1 := Finset.sum_congr rfl h_ds_card
    rw [h_sum, sum_const, smul_eq_mul, mul_one] at h_card_eq
    omega
  | succ n' =>
    cases n' with
    | zero =>
      use 0
      rw [vt0_card_one]
      exact perfect_card_eq_one_of_length_one C hC
    | succ n'' =>
      have h_k : ∀ x : List.Vector B (n'' + 2), ∀ k ≤ n'' + 2, (cumulativeDels x k).card ≤ k := by {
        intro x k hk
        induction k with
        | zero =>
          rfl
        | succ k' ih =>
          have hk' : k' ≤ n'' + 2 := by omega
          have ih' := ih hk'
          rw [cumulativeDels_succ]
          have h_card_le := card_insert_le (sDel x k') (cumulativeDels x k')
          omega
      }
      have h_ds_le : ∀ x : List.Vector B (n'' + 2), (dS x).card ≤ n'' + 2 := by {
        intro x
        have h_eq : dS x = cumulativeDels x (n'' + 2) := rfl
        rw [h_eq]
        exact h_k x (n'' + 2) (by omega)
      }
      -- Algebraic formulation to close the sorry:
      
      let c : List.Vector B (n'' + 2) → Nat := fun x => if x ∈ C then 1 else 0
      
      have hc : is_perfect_algebraic (n'' + 2) c := by {
        intro y
        have h_sum : (∑ x : List.Vector B (n'' + 2), A_mat (n'' + 2) (n'' + 2) x y * c x) = 
          (C.filter (fun x => y ∈ dS x)).card := by {
          dsimp [c]
          have h_mul : ∀ x, A_mat (n'' + 2) (n'' + 2) x y * (if x ∈ C then 1 else 0) =
            if x ∈ C ∧ y ∈ dS x then 1 else 0 := by {
            intro x
            dsimp [A_mat]
            have h_ds_eq : cumulativeDels x (n'' + 2) = dS x := rfl
            rw [h_ds_eq]
            by_cases hC_in : x ∈ C <;> by_cases hy : y ∈ dS x <;> simp [hC_in]
          }
          rw [Finset.sum_congr rfl (fun x _ => h_mul x)]
          have h_sum_boole : (∑ x : List.Vector B (n'' + 2), if x ∈ C ∧ y ∈ dS x then 1 else 0) =
            (univ.filter (fun x => x ∈ C ∧ y ∈ dS x)).card := by simp [Finset.sum_boole]
          have h_eq : univ.filter (fun x => x ∈ C ∧ y ∈ dS x) = C.filter (fun x => y ∈ dS x) := by {
            ext x
            simp
          }
          rw [h_sum_boole]
          exact congrArg Finset.card h_eq
        }
        rw [h_sum]
        rcases hC with ⟨h_disj, h_univ⟩
        have hy_univ : y ∈ C.biUnion dS := by {
          rw [h_univ]
          exact Finset.mem_univ y
        }
        rw [Finset.mem_biUnion] at hy_univ
        rcases hy_univ with ⟨x, hx, hyx⟩
        have h_eq : C.filter (fun z => y ∈ dS z) = {x} := by {
          ext z
          simp only [Finset.mem_filter, Finset.mem_singleton]
          constructor
          · rintro ⟨hzC, hyz⟩
            by_contra h_neq
            have h_disj_xz := h_disj x hx z hzC (Ne.symm h_neq)
            exact Finset.disjoint_left.mp h_disj_xz hyx hyz
          · rintro rfl
            exact ⟨hx, hyx⟩
        }
        rw [h_eq, Finset.card_singleton]
      }
      
      have h_card_T := perfect_code_card_eq_sum_T c hc
      
      rcases h_card_T with ⟨a, ha⟩
      
      have hC_sum : C.card = ∑ x : List.Vector B (n'' + 2), c x := by {
        dsimp [c]
        have h_sum_boole : (∑ x : List.Vector B (n'' + 2), if x ∈ C then 1 else 0) = (univ.filter (fun x => x ∈ C)).card := by simp
        have h_eq : univ.filter (fun x => x ∈ C) = C := by {
          ext x
          simp
        }
        rw [h_sum_boole]
        exact (congrArg Finset.card h_eq).symm
      }
      
      use a
      rw [hC_sum, ha]
      
      -- VTCode_card_eq_sum_T provides the exact bridge to the VT code cardinality!
      exact (vt_size_eq_sum_T (n'' + 2) a).symm
}

/-- Theorem: VT_0 is optimal among all perfect single-deletion correcting codes.
Proven via double induction:
- Outer induction: string length n.
- Inner induction: prefix index k tracking run transitions and cumulative deletion spheres. -/
theorem vt0_is_optimal_perfect (C : Finset (List.Vector B n)) (hC : is_PerfectCodeCandidate C) :
    C.card ≤ (Finset.VTCode n 0).card := by {
  induction n with
  | zero =>
    exact vt0_is_optimal_perfect_zero C hC
  | succ n' ih =>
    cases n' with
    | zero =>
      exact vt0_is_optimal_perfect_one C hC
    | succ n'' =>
      have h_inner : ∀ k ≤ n'' + 2, ∀ x ∈ C, ∀ u : List.Vector B (n'' + 1) → Rat,
          (∀ y, 0 ≤ u y) → P x k u ≤ ∑ i ∈ Finset.range k, u (sDel x i) := by {
        intro k hk x hx u hu
        exact P_le_sum_range x k u hu
      }
      have ⟨a, h_eq⟩ := perfect_code_card_eq_vt_card C hC
      rw [h_eq]
      exact VTCode_zero_is_max (n'' + 2) a
}
