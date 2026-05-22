import re

with open("InfiniteTwos.lean", "r") as f:
    content = f.read()

# First, modify combinatorial_squeeze
squeeze_sig_old = """lemma combinatorial_squeeze (P : ℕ) (hP : P ≥ 4)
    (v : ℕ → ℕ)
    (f : Fin P → Fin P)
    (hv1 : ∀ k : Fin P, 1 ≤ v (k.val + 1))
    (hvP : ∀ k : Fin P, v (k.val + 1) ≤ P)
    (h_no2 : ∀ k : Fin P, v (k.val + 1) ≠ 2)
    (hf : ∀ k : Fin P, (f k).val = (k.val + 1 + P - v (k.val + 1)) % P)
    (hbij : Function.Bijective f)
    (h_recent : ∀ k : Fin P, v (f k).val = v (k.val + 1)) :
    False := by {"""

squeeze_sig_new = """lemma combinatorial_squeeze (P : ℕ) (hP : P ≥ 4)
    (v : ℕ → ℕ)
    (f : Fin P → Fin P)
    (hv1 : ∀ k : Fin P, 1 ≤ v (k.val + 1))
    (hvP : ∀ k : Fin P, v (k.val + 1) ≤ P)
    (h_no2 : ∀ k : Fin P, v (k.val + 1) ≠ 2)
    (h_no1 : ∃ k : Fin P, v (k.val + 1) ≠ 1)
    (hf : ∀ k : Fin P, (f k).val = (k.val + 1 + P - v (k.val + 1)) % P)
    (hbij : Function.Bijective f)
    (h_recent : ∀ k : Fin P, v (f k).val = v (k.val + 1)) :
    False := by {"""

squeeze_proof_old = """  -- If each distinct value X sums to P, then |S_X| * X = P, so the distinct values must form an exact cover of the cycle.
  -- But an exact cover with distinct moduli all >= 3 is impossible by Mirsky-Newman.
  sorry
}"""

squeeze_proof_new = """  let S := Finset.univ.image (fun k : Fin P => v (k.val + 1))
  let cover : ℕ → Finset (Fin P) := fun X => Finset.univ.filter (fun k : Fin P => v (k.val + 1) = X)
  
  have h_min : ∀ X ∈ S, X ≥ 3 := by {
    intro X hX
    have hX_in : ∃ k : Fin P, v (k.val + 1) = X := by {
      have h1 := Finset.mem_image.mp hX
      rcases h1 with ⟨k, hk_in, hk_eq⟩
      exact ⟨k, hk_eq⟩
    }
    rcases hX_in with ⟨k, hk⟩
    have hv := hv1 k
    have hn2 := h_no2 k
    by_cases hX1 : X = 1
    · rw [← hk] at hX1
      have h1_in : ∃ k : Fin P, v (k.val + 1) = 1 := ⟨k, hX1⟩
      have h_sum := vanEck_fiber_sum P hP v f hf hbij h_recent 1 h1_in
      rw [mul_one] at h_sum
      have h_all_1 : ∀ k : Fin P, v (k.val + 1) = 1 := by {
        intro x
        have h_card_univ : Finset.card (Finset.univ : Finset (Fin P)) = P := Fintype.card_fin P
        have h_subset : cover 1 ⊆ Finset.univ := Finset.filter_subset _ _
        have h_eq : cover 1 = Finset.univ := by {
          apply Finset.eq_of_subset_of_card_le h_subset
          rw [h_sum, h_card_univ]
        }
        have hx_in : x ∈ cover 1 := by {
          rw [h_eq]
          exact Finset.mem_univ x
        }
        have hx_filter := Finset.mem_filter.mp hx_in
        exact hx_filter.right
      }
      rcases h_no1 with ⟨k1, hk1⟩
      have hk1_1 := h_all_1 k1
      omega
    · omega
  }
  
  have h_partition : ∀ k : Fin P, ∃! X, X ∈ S ∧ k ∈ cover X := by {
    intro k
    use v (k.val + 1)
    constructor
    · constructor
      · apply Finset.mem_image.mpr
        exact ⟨k, Finset.mem_univ k, rfl⟩
      · apply Finset.mem_filter.mpr
        exact ⟨Finset.mem_univ k, rfl⟩
    · intro y hy
      rcases hy with ⟨hy1, hy2⟩
      have hy_filter := Finset.mem_filter.mp hy2
      exact hy_filter.right.symm
  }
  
  have h_ap : ∀ X ∈ S, ∃ start : Fin P, cover X = Finset.univ.filter (fun k => ∃ i : ℕ, k.val = (start.val + i * X) % P) := by {
    intro X hX
    -- The occurrences of X in the cycle form an exact arithmetic progression with step X
    -- because f(k) = k - X maps the fiber bijectively to itself.
    sorry
  }
  
  exact mirsky_newman_exact_cover P S h_min cover h_partition h_ap
}"""

# Replace combinatorial_squeeze
content = content.replace(squeeze_sig_old, squeeze_sig_new)
content = content.replace(squeeze_proof_old, squeeze_proof_new)

# Add open Classical at the top if not present
if "open Classical" not in content:
    content = content.replace("import Mathlib\n", "import Mathlib\nopen Classical\n")

# Now modify finite_cycle_gap_collapse
collapse_old = """      · have h_P_ge_4 : P ≥ 4 := by omega
        sorry"""

collapse_new = """      · have h_P_ge_4 : P ≥ 4 := by omega
        have h_no1 : ∃ k : Fin P, v_fn k ≠ 1 := by {
          by_contra hc
          push_neg at hc
          have h_sum : ∑ k : Fin P, v_fn k = P := by {
            have h1 : ∀ k : Fin P, v_fn k = 1 := hc
            have h2 : ∑ k : Fin P, v_fn k = ∑ k : Fin P, 1 := Finset.sum_congr rfl (fun x _ => h1 x)
            rw [h2]
            have h3 : ∑ k : Fin P, 1 = Finset.card (Finset.univ : Finset (Fin P)) * 1 := Finset.sum_const 1
            have h4 : Finset.card (Finset.univ : Finset (Fin P)) = P := Fintype.card_fin P
            omega
          }
          have h_sum2 : ∑ k : Fin P, v_fn k = C * P := hC
          omega
        }
        have h_no2_v_fn : ∀ k : Fin P, v_fn (k.val + 1) ≠ 2 := by {
          intro k
          -- v_fn k = vanEckNthTerm (n_2 + k + 1)
          -- But wait, v_fn (k.val + 1) doesn't typecheck directly since v_fn takes Fin P
          sorry
        }
        -- Need to call combinatorial_squeeze
        sorry"""

# Wait, v_fn takes Fin P, but combinatorial_squeeze takes v : ℕ → ℕ.
# We must define v_nat : ℕ → ℕ := fun k => vanEckNthTerm (n_2 + k).
# Let's fix that.
content = content.replace(collapse_old, collapse_new)

with open("InfiniteTwos.lean", "w") as f:
    f.write(content)
