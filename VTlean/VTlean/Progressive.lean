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

/-- The unique codeword whose deletion sphere contains `y`, for a perfect code. -/
noncomputable def perfectParent (C : Finset (List.Vector B n))
    (hC : is_PerfectCodeCandidate C) (y : List.Vector B (n - 1)) : List.Vector B n := by {
  have hmem : y ∈ C.biUnion dS := by rw [hC.2]; simp
  exact Classical.choose (Finset.mem_biUnion.mp hmem)
}

lemma perfectParent_spec (C : Finset (List.Vector B n))
    (hC : is_PerfectCodeCandidate C) (y : List.Vector B (n - 1)) :
    perfectParent C hC y ∈ C ∧ y ∈ dS (perfectParent C hC y) := by {
  have hmem : y ∈ C.biUnion dS := by rw [hC.2]; simp
  exact Classical.choose_spec (Finset.mem_biUnion.mp hmem)
}

lemma perfectParent_eq_of_mem (C : Finset (List.Vector B n))
    (hC : is_PerfectCodeCandidate C) (x : List.Vector B n) (y : List.Vector B (n - 1))
    (hx : x ∈ C) (hy : y ∈ dS x) : perfectParent C hC y = x := by {
  have hp := perfectParent_spec C hC y
  by_contra hneq
  have hdisj := hC.1 _ hp.1 x hx hneq
  rw [Finset.disjoint_iff_inter_eq_empty] at hdisj
  have hinter : y ∈ dS (perfectParent C hC y) ∩ dS x :=
    Finset.mem_inter.mpr ⟨hp.2, hy⟩
  rw [hdisj] at hinter
  simp at hinter
}

/-- Pushforward identity for the unique-parent map: under uniform deletion
outputs, a parent `x` is sampled with probability proportional to its sphere
size. -/
lemma perfect_code_parent_pushforward (C : Finset (List.Vector B n))
    (hC : is_PerfectCodeCandidate C) (g : List.Vector B n → Rat) (hn : 0 < n) :
    ∑ y ∈ Finset.univ, g (perfectParent C hC y) =
      ∑ x ∈ C, (dS x).card * g x := by {
  let u : List.Vector B (n - 1) → Rat := fun y => g (perfectParent C hC y)
  have h_each : ∀ x ∈ C, P x n u = (dS x).card * g x := by {
    intro x hx
    rw [P_n_eq_sum_dS x hn]
    calc
      (∑ y ∈ dS x, u y) = ∑ y ∈ dS x, g x := by {
        apply Finset.sum_congr rfl
        intro y hy
        dsimp [u]
        rw [perfectParent_eq_of_mem C hC x y hx hy]
      }
      _ = (dS x).card * g x := by simp [Finset.sum_const, nsmul_eq_mul]
  }
  have h_left :
      (∑ x ∈ C, P x n u) = ∑ x ∈ C, (dS x).card * g x := by {
    apply Finset.sum_congr rfl
    intro x hx
    exact h_each x hx
  }
  calc
    (∑ y ∈ Finset.univ, g (perfectParent C hC y)) = ∑ x ∈ C, P x n u :=
      (partition_sum C hC u hn).symm
    _ = ∑ x ∈ C, (dS x).card * g x := h_left
}

/-- For a uniformly random deletion output, the expected reciprocal size of its
unique parent sphere is exactly `|C| / 2^(n-1)`.  Thus an upper bound on this
expectation is precisely a perfect-code cardinality bound. -/
lemma perfect_code_reciprocal_degree_identity (C : Finset (List.Vector B n))
    (hC : is_PerfectCodeCandidate C) (hn : 0 < n) :
    (C.card : Rat) =
      ∑ y ∈ Finset.univ,
        ((dS (perfectParent C hC y)).card : Rat)⁻¹ := by {
  let u : List.Vector B (n - 1) → Rat := fun y =>
    ((dS (perfectParent C hC y)).card : Rat)⁻¹
  have h_each : ∀ x ∈ C, P x n u = 1 := by {
    intro x hx
    rw [P_n_eq_sum_dS x hn]
    have hcard_pos : 0 < (dS x).card := by {
      rw [Finset.card_pos]
      refine ⟨sDel x 0, ?_⟩
      rw [mem_dS]
      exact ⟨0, by omega, rfl⟩
    }
    have hcard_ne : ((dS x).card : Rat) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hcard_pos)
    calc
      (∑ y ∈ dS x, u y) = ∑ y ∈ dS x, ((dS x).card : Rat)⁻¹ := by {
        apply Finset.sum_congr rfl
        intro y hy
        dsimp [u]
        rw [perfectParent_eq_of_mem C hC x y hx hy]
      }
      _ = 1 := by simp [Finset.sum_const, nsmul_eq_mul, hcard_ne]
  }
  have h_left : (∑ x ∈ C, P x n u) = (C.card : Rat) := by {
    calc
      (∑ x ∈ C, P x n u) = ∑ x ∈ C, (1 : Rat) := by {
        apply Finset.sum_congr rfl
        intro x hx
        exact h_each x hx
      }
      _ = (C.card : Rat) := by simp
  }
  have h_partition := partition_sum C hC u hn
  calc
    (C.card : Rat) = ∑ x ∈ C, P x n u := h_left.symm
    _ = ∑ y ∈ Finset.univ, u y := h_partition
    _ = ∑ y ∈ Finset.univ,
          ((dS (perfectParent C hC y)).card : Rat)⁻¹ := by rfl
}

/-- Specializing the perfect-partition identity to the indicator of the weight-`w`
layer gives an exact accounting identity for that layer.  Unlike the crude
bound `card (dS x) ≤ n`, this keeps the non-uniform edge sizes visible one
weight layer at a time. -/
lemma perfect_code_layer_budget (C : Finset (List.Vector B n))
    (hC : is_PerfectCodeCandidate C) (w : Nat) (hn : 0 < n) :
    ∑ x ∈ C, (dS_wt x w).card =
      (Finset.filter (fun y : List.Vector B (n - 1) => wt y = w) Finset.univ).card := by {
  let u : List.Vector B (n - 1) → Rat := fun y => if wt y = w then 1 else 0
  have h_left :
      (∑ x ∈ C, ((dS_wt x w).card : Rat)) = ∑ x ∈ C, P x n u := by {
    apply Finset.sum_congr rfl
    intro x hx
    rw [P_n_eq_sum_dS x hn]
    calc
      ((dS_wt x w).card : Rat) = ∑ y ∈ dS_wt x w, (1 : Rat) := by simp
      _ = ∑ y ∈ dS x, if wt y = w then 1 else 0 := by {
        unfold dS_wt
        rw [Finset.sum_filter]
      }
      _ = ∑ y ∈ dS x, u y := by simp [u]
  }
  have h_mid := partition_sum C hC u hn
  have h_right :
      (∑ y ∈ Finset.univ, u y) =
        ((Finset.filter (fun y : List.Vector B (n - 1) => wt y = w) Finset.univ).card : Rat) := by {
    unfold u
    rw [← Finset.sum_filter]
    simp
  }
  have h_rat :
      (∑ x ∈ C, ((dS_wt x w).card : Rat)) =
        ((Finset.filter (fun y : List.Vector B (n - 1) => wt y = w) Finset.univ).card : Rat) := by {
    calc
      _ = ∑ x ∈ C, P x n u := h_left
      _ = ∑ y ∈ Finset.univ, u y := h_mid
      _ = _ := h_right
  }
  exact_mod_cast h_rat
}

/-- In a perfect code, if every codeword contributes at least `r` descendants
to a fixed output-weight layer, then that layer has room for at least `r` per
codeword.  This is useful when run-count information supplies such a lower
bound on a (possibly filtered) family of codewords. -/
lemma perfect_code_layer_lower_bound (C : Finset (List.Vector B n))
    (hC : is_PerfectCodeCandidate C) (S : Finset (List.Vector B n)) (hS : S ⊆ C)
    (w r : Nat) (hn : 0 < n)
    (h_each : ∀ x ∈ S, r ≤ (dS_wt x w).card) :
    r * S.card ≤
      (Finset.filter (fun y : List.Vector B (n - 1) => wt y = w) Finset.univ).card := by {
  have hlow : r * S.card ≤ ∑ x ∈ S, (dS_wt x w).card := by {
    have hsum : (∑ x ∈ S, r) ≤ ∑ x ∈ S, (dS_wt x w).card := by {
      apply Finset.sum_le_sum
      intro x hx
      exact h_each x hx
    }
    rw [Finset.sum_const, nsmul_eq_mul] at hsum
    simpa [Nat.mul_comm] using hsum
  }
  have hsubset_sum :
      (∑ x ∈ S, (dS_wt x w).card) ≤ ∑ x ∈ C, (dS_wt x w).card :=
    Finset.sum_le_sum_of_subset_of_nonneg hS (by
      intro x hxC hxS
      exact Nat.zero_le _)
  calc
    r * S.card ≤ ∑ x ∈ S, (dS_wt x w).card := hlow
    _ ≤ ∑ x ∈ C, (dS_wt x w).card := hsubset_sum
    _ = (Finset.filter (fun y : List.Vector B (n - 1) => wt y = w) Finset.univ).card :=
      perfect_code_layer_budget C hC w hn
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

/-- Every perfect code has the size of some `VT_a(n)`, **conditional on** the open
`PerfectSizeBridge n` (only used for `n ≥ 2`; the cases `n = 0, 1` are proven outright). -/
lemma perfect_code_card_eq_vt_card (hBridge : PerfectSizeBridge n)
    (C : Finset (List.Vector B n)) (hC : is_PerfectCodeCandidate C) :
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
      
      have h_card_T := hBridge c hc
      
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

/-- Theorem (conditional): `VT_0(n)` is optimal among all perfect single-deletion
correcting codes, **assuming** the open hypothesis `PerfectSizeBridge n`.

Proof: `n = 0, 1` are handled directly. For `n ≥ 2`, the bridge gives `|C| = |VT_a(n)|`
for some `a`, and `VTCode_zero_is_max` (sorry-free, via the DFT) gives
`|VT_a(n)| ≤ |VT_0(n)|`. -/
theorem vt0_is_optimal_perfect (hBridge : PerfectSizeBridge n)
    (C : Finset (List.Vector B n)) (hC : is_PerfectCodeCandidate C) :
    C.card ≤ (Finset.VTCode n 0).card := by {
  match n, hBridge, C, hC with
  | 0, _, C, hC => exact vt0_is_optimal_perfect_zero C hC
  | 1, _, C, hC => exact vt0_is_optimal_perfect_one C hC
  | n'' + 2, hBridge, C, hC =>
    have ⟨a, h_eq⟩ := perfect_code_card_eq_vt_card hBridge C hC
    rw [h_eq]
    exact VTCode_zero_is_max (n'' + 2) a
}
