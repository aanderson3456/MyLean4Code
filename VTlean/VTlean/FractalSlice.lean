/- Copyright Austin Anderson aided by Gemini 2026 -/
import VTlean.B
import VTlean.InsDel
import VTlean.DelCode
import VTlean.VTCode

open B List.Vector Finset

/-- The cumulative set of deletions of `x` restricted to the first `k` positions -/
def cumulativeDels {n : Nat} (x : List.Vector B n) (k : Nat) :
    Finset (List.Vector B (n - 1)) :=
  match k with
  | 0 => ∅
  | k' + 1 => List.toFinset (dS_le x k')

/-- B_k(x, y) holds if y is in the k-th deletion set but not in the cumulative (k-1)-th set -/
def isIncrementalDel {n : Nat} (x : List.Vector B n) (y : List.Vector B (n - 1)) (k : Nat) :
    Prop :=
  sDel x k = y ∧ y ∉ cumulativeDels x k

/-- The transition subset at index k -/
def TransitionSubset {n : Nat} (k : Nat) : Finset (List.Vector B n) :=
  Finset.univ.filter (fun x => x.val.getD k B.O ≠ x.val.getD (k - 1) B.O)

/-- Theorem 1: B_k(x, y) implies x belongs to the transition subset (for k >= 1) -/
theorem incremental_del_impl_transition {n : Nat} {k : Nat} (_hk : 0 < k ∧ k < n)
    (x : List.Vector B n) (y : List.Vector B (n - 1)) (h_del : isIncrementalDel x y k) :
    x ∈ TransitionSubset k := by
  sorry

/-- The closed-form insertion bijection f_k(y) -/
def sloaneInsertion {n : Nat} (y : List.Vector B (n - 1)) (k : Nat) (hk : k < n) :
    List.Vector B n :=
  ⟨y.val.take k ++ [B.flip (y.val.getD (k - 1) B.O)] ++ y.val.drop k, by {
    rw [List.length_append, List.length_append, List.length_take, List.length_drop, y.2,
        List.length_singleton]
    omega
  }⟩

/-- Theorem 2 (Part 1): Deleting the k-th position of f_k(y) always yields y -/
theorem sloane_insertion_is_del {n : Nat} (y : List.Vector B (n - 1)) (k : Nat) (hk : k < n) :
    sDel (sloaneInsertion y k hk) k = y := by
  apply Subtype.ext
  dsimp [sloaneInsertion, sDel]
  have h_take_len : (y.val.take k).length = k := by {
    have h_k : k ≤ n - 1 := by omega
    rw [List.length_take]
    have h_len : y.val.length = n - 1 := y.2
    rw [h_len]
    exact min_eq_left h_k
  }
  have h_append_ge :
      List.sDel (y.val.take k ++ ([B.flip (y.val.getD (k - 1) B.O)] ++ y.val.drop k)) k =
      y.val.take k ++ List.sDel ([B.flip (y.val.getD (k - 1) B.O)] ++ y.val.drop k)
        (k - (y.val.take k).length) := by {
    apply List.sDel_append_of_ge
    · rw [h_take_len]
    · intro h_nil
      contradiction
  }
  rw [List.append_assoc]
  rw [h_append_ge, h_take_len, Nat.sub_self]
  change y.val.take k ++ List.sDel (B.flip (y.val.getD (k - 1) B.O) :: y.val.drop k) 0 = y.val
  rw [List.sDel_zero]
  exact List.take_append_drop k y.val

/-- Theorem 2 (Part 2): The Sloane insertion is a bijection to the transition subset -/
def sloane_bijection_to_transition {n : Nat} (k : Nat) (_hk : 0 < k ∧ k < n) :
    Equiv (List.Vector B (n - 1)) { x : List.Vector B n // x ∈ TransitionSubset k } := by
  sorry

/-- Helper: For positive lengths, cumulativeDels of length n equals dS -/
lemma cumulativeDels_self {n : Nat} (hn : 0 < n) (x : List.Vector B n) :
    cumulativeDels x n = dS x := by
  cases n with
  | zero => contradiction
  | succ n' => rfl

/-- Theorem 3: Distinct VT0 codewords have disjoint deletion sets. -/
theorem vt0_dels_disjoint
  {n : Nat} (hn : 0 < n) (x1 x2 : List.Vector B n)
  (hx1 : x1 ∈ Finset.VTCode n 0) (hx2 : x2 ∈ Finset.VTCode n 0) (h_ne : x1 ≠ x2) :
  Disjoint (cumulativeDels x1 n) (cumulativeDels x2 n) := by
  rw [cumulativeDels_self hn, cumulativeDels_self hn]
  have h_delcode := DelCode_VTCode n 0
  unfold is_DelCode at h_delcode
  have h_inter := h_delcode x1 hx1 x2 hx2 h_ne
  rw [Finset.disjoint_iff_inter_eq_empty]
  exact h_inter
