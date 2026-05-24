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
  cuculiere_get (n + 1) c = cuculiere_get n c + if c < n + 1 then 0 else cuculiere_get n (c - (n + 1)) := by {
  unfold cuculiere_get
  have h_cuc_succ : cuculiere (n + 1) = List.zipWith (·+·) (cuculiere n ++ List.replicate (n + 1) 0) (List.replicate (n + 1) 0 ++ cuculiere n) := rfl
  rw [h_cuc_succ]
  generalize hl : cuculiere n = l
  have h_len : (l ++ List.replicate (n + 1) 0).length = (List.replicate (n + 1) 0 ++ l).length := by simp [Nat.add_comm]
  rw [getD_zipWith_add_of_length_eq _ _ h_len]
  rw [getD_append_replicate]
  rw [getD_replicate_append (n + 1) c l]
}

lemma vector_card_split (n : Nat) (P : List.Vector B (n + 1) → Prop) [DecidablePred P] :
  Finset.card (Finset.filter P univ) = 
  Finset.card (Finset.filter (fun v => P (List.Vector.push v B.O)) univ) + 
  Finset.card (Finset.filter (fun v => P (List.Vector.push v B.I)) univ) := by {
  sorry
}

/-- Lemma: The frequency of elements with a specific checksum `c` equals the `c`-th element of Cuculiere's triangle. -/
lemma moment_eq_cuculiere (n c : Nat) :
  Finset.card (Finset.filter (fun (x : List.Vector B n) => List.Vector.moment x = c) univ) = cuculiere_get n c := by {
  induction n generalizing c with
  | zero =>
    cases c with
    | zero => rfl
    | succ c =>
      have h : Finset.filter (fun (x : List.Vector B 0) => List.Vector.moment x = c + 1) univ = ∅ := by {
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
    have h1 : Finset.card (Finset.filter (fun (v : List.Vector B n) => List.Vector.moment (List.Vector.push v B.O) = c) univ) = 
              Finset.card (Finset.filter (fun (v : List.Vector B n) => List.Vector.moment v = c) univ) := by {
      congr 1
      ext v
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rw [List.Vector.moment_push_O]
    }
    
    have h2 : Finset.card (Finset.filter (fun (v : List.Vector B n) => List.Vector.moment (List.Vector.push v B.I) = c) univ) =
              if c < n + 1 then 0 else cuculiere_get n (c - (n + 1)) := by {
      split
      · have h_empty : Finset.filter (fun (v : List.Vector B n) => List.Vector.moment (List.Vector.push v B.I) = c) univ = ∅ := by {
          rw [Finset.filter_eq_empty_iff]
          intro v hv
          rw [List.Vector.moment_push_I]
          omega
        }
        rw [h_empty]
        rfl
      · have h_eq : Finset.card (Finset.filter (fun (v : List.Vector B n) => List.Vector.moment (List.Vector.push v B.I) = c) univ) = 
                    Finset.card (Finset.filter (fun (v : List.Vector B n) => List.Vector.moment v = c - (n + 1)) univ) := by {
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

/-- Formal theorem stating that the cardinality of the VT code exactly matches
    the subset summation over Cuculiere's triangle modulo n+1. -/
theorem card_VTCode_eq_cuculiere (n a : Nat) :
  Finset.card (Finset.VTCode n a) = cuculiere_mod_sum n a := by {
  -- The cardinality maps directly to subset summation over the moment partition
  sorry
}

-- Computations for verification:
#eval cuculiere 3
-- Expected: [1, 1, 1, 2, 1, 1, 1]

#eval cuculiere 4
-- Expected: [1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 1]
