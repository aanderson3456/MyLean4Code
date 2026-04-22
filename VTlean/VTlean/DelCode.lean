import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import VTlean.InsDel
import VTlean.B
import VTlean.NumOsNumIs
import Mathlib.Data.Fintype.EquivFin



variable {α : Type} [DecidableEq α]
variable {n : Nat} (C C' : Finset (List.Vector α n)) (c : List.Vector α n)
variable (X X' : List.Vector α n) (Y : List.Vector α (n - 1))

open Nat List List.Vector Finset B

def wt {n : Nat} (X : List.Vector B n) : Nat := List.num_Is X.val

def Icc_wt {n : Nat} (a b : Nat) (X : List.Vector B n) : Prop :=
  a ≤ wt X ∧ wt X ≤ b

noncomputable instance {n : Nat} (a b : Nat) : DecidablePred (@Icc_wt n a b) :=
  Classical.decPred _

def Iic_wt {n : Nat} (a : Nat) (X : List.Vector B n) : Prop :=
  wt X ≤ a

noncomputable instance {n : Nat} (a : Nat) : DecidablePred (@Iic_wt n a) :=
  Classical.decPred _

def Ici_wt {n : Nat} (a : Nat) (X : List.Vector B n) : Prop :=
  a ≤ wt X

noncomputable instance {n : Nat} (a : Nat) : DecidablePred (@Ici_wt n a) :=
  Classical.decPred _
def is_DelCode {n : Nat} (C : Finset (List.Vector α n)) : Prop :=
  ∀ X ∈ C, ∀ Y ∈ C, X ≠ Y → dS X ∩ dS Y = ∅

instance DecidablePred_is_DelCode [Fintype α] :
  DecidablePred (@is_DelCode α _ n) :=
by sorry
lemma DelCode_empty :
  is_DelCode (∅ : Finset (List.Vector α n)) :=
by sorry
lemma DelCode_singleton :
  is_DelCode ({X}) :=
by sorry
lemma DelCode_subset
  (H : is_DelCode C) (HCC : C' ⊆ C) :
  is_DelCode C' :=
by sorry
lemma DelCode_filter
  (H : is_DelCode C) (p : List.Vector α n → Prop) [DecidablePred p] :
  is_DelCode (filter p C) :=
by sorry
lemma DelCode_sdiff
  (H : is_DelCode C) (S : Finset (List.Vector α n)) :
  is_DelCode (C \ S) :=
by sorry
lemma DelCode_insert
  (HC : is_DelCode C) (Hx : ∀ c ∈ C, dS X ∩ dS c = ∅):
  is_DelCode (insert X C) :=
by sorry
lemma DelCode_of_insert
  (H : is_DelCode (insert X C)) :
  is_DelCode C :=
by sorry
lemma dS_inter_union_dS_iff (C : Finset (List.Vector α n)) :
  dS X ∩ union_dS C = ∅ ↔ ∀ c ∈ C, dS X ∩ dS c = ∅ :=
by sorry

lemma DelCode_insert_iff (Hx : X ∉ C) :
  is_DelCode (insert X C) ↔ is_DelCode C ∧ ∀ c ∈ C, dS X ∩ dS c = ∅ :=
by sorry

lemma DelCode_insert_iff' (Hx : X ∉ C) :
  is_DelCode (insert X C) ↔ is_DelCode C ∧ dS X ∩ union_dS C = ∅ :=
by sorry
lemma DelCode_erase (H : is_DelCode C) :
  is_DelCode (erase C X) :=
by sorry
def replaceCode :=
  insert X' (erase C X)

lemma DelCode_replaceCode
  (HC : is_DelCode C) (HX : X ∈ C) (HX' : dS X' ⊆ dS X) :
  is_DelCode (replaceCode C X X') :=
by sorry
lemma card_replaceCode
  (HC : is_DelCode C)
  (x : List.Vector α n) (Hx : x ∈ C)
  (y : List.Vector α n) (Hxy : dS y ⊆ dS x) :
  card (replaceCode C x y) = card C :=
by sorry
def flipCode (C : Finset (List.Vector B n)) : Finset (List.Vector B n) :=
  C.image B.Vector.flip

lemma DelCode_flipCode
  {C : Finset (List.Vector B n)} (HC : is_DelCode C) :
  is_DelCode (flipCode C) :=
by sorry
lemma exists_DC_sub_Icc_wt
  (a b : Nat) (Ha : a ≤ n) (Hb : b ≤ n)
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) (HCS : C ⊆ filter (Icc_wt a b) univ) :
  ∃ C' : Finset (List.Vector B n), is_DelCode C' ∧ C' ⊆ filter (Icc_wt (n - b) (n - a)) univ :=
by sorry
lemma exists_DC_card_filter_wt_le
  (S : Finset (List.Vector B n)) (HS : flipCode S = S)
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) (HCS : C ⊆ S)
  (a b : Nat) (Ha : a ≤ n) (Hb : b ≤ n) :
  ∃ C' : Finset (List.Vector B n), is_DelCode C' ∧ C' ⊆ S
  ∧ C'.card = C.card ∧ (filter (Icc_wt (n - b) (n - a)) C').card ≤ (filter (Icc_wt a b) C).card :=
by sorry
def sum_card_dS {n : Nat} (C : Finset (List.Vector α n)) : Nat :=
  C.sum (fun c => (dS c).card)

lemma sum_card_dS_empty :
  sum_card_dS (∅ : Finset (List.Vector α n)) = 0 :=
by sorry
lemma sum_card_dS_insert (H : X ∉ C) :
  sum_card_dS (insert X C) = (dS X).card + sum_card_dS C :=
by sorry
def is_DelCode' {n : Nat} (C : Finset (List.Vector α n)) : Prop :=
  (union_dS C).card = sum_card_dS C

instance DecidablePred_is_DelCode' :
  DecidablePred (@is_DelCode' α _ n) :=
fun C => by
  unfold is_DelCode'
  exact instDecidableEqNat _ _

lemma DelCode'_empty :
  is_DelCode' (∅ : Finset (List.Vector α n)) :=
by sorry
lemma card_union_dS_le :
  (union_dS C).card ≤ sum_card_dS C :=
by sorry
lemma dS_inter_union_dS_of_DelCode'_insert
  (HX : X ∉ C) (HCX : is_DelCode' (insert X C)) :
  dS X ∩ union_dS C = ∅ :=
by sorry
lemma DelCode'_of_DelCode'_insert
  (HX : X ∉ C) (HCX : is_DelCode' (insert X C)) :
  is_DelCode' C :=
by sorry
lemma card_dS_insert_of_card_dS
  (HC : is_DelCode' C) (HX : X ∉ C) (HCX : dS X ∩ union_dS C = ∅):
  is_DelCode' (insert X C) :=
by sorry
lemma DelCode'_insert_iff (HX : X ∉ C):
  is_DelCode' (insert X C) ↔ is_DelCode' C ∧ dS X ∩ union_dS C = ∅ :=
by sorry
lemma DelCode_of_DelCode' (HC : is_DelCode' C) :
  is_DelCode C :=
by sorry
lemma DelCode'_of_DelCode (HC : is_DelCode C) :
  is_DelCode' C :=
by sorry
lemma DelCode'_iff {n : Nat} (C : Finset (List.Vector α n)) :
  is_DelCode' C ↔ is_DelCode C :=
by sorry
lemma union_dS_inter_of_DelCode
  {C : Finset (List.Vector α n)} (HC : is_DelCode C)
  {C₁ C₂ : Finset (List.Vector α n)} (HC₁ : C₁ ⊆ C) (HC₂ : C₂ ⊆ C)
  (H : C₁ ∩ C₂ = ∅) :
  union_dS C₁ ∩ union_dS C₂ = ∅ :=
by sorry
namespace B

def dB {n : Nat} (X : List.Vector B n) : Finset (List.Vector B n) :=
  union_dS (IS X)

lemma mem_dB {n : Nat} (X Y : List.Vector B n) :
  Y ∈ dB X ↔ Y ∈ union_dS (IS X) :=
by sorry
lemma mem_dB_iff {n : Nat} (X Y : List.Vector B n) :
  Y ∈ dB X ↔ IS X ∩ IS Y ≠ ∅ :=
by sorry
lemma mem_dB_iff' {n : Nat} (X Y : List.Vector B n) :
  Y ∈ dB X ↔ dS X ∩ dS Y ≠ ∅ :=
by sorry
def union_dB {n : Nat} (C : Finset (List.Vector B n)) :=
  C.biUnion dB

lemma union_dB_empty {n : Nat} :
  union_dB (∅ : Finset (List.Vector B n)) = ∅ :=
by sorry
lemma mem_union_dB (C : Finset (List.Vector B n)) (X : List.Vector B n) :
  X ∈ union_dB C ↔ ∃ Y ∈ C, X ∈ dB Y :=
by sorry
lemma mem_union_dB_iff (C : Finset (List.Vector B n)) (X : List.Vector B n) :
  X ∈ union_dB C ↔ ∃ Y ∈ C, dS Y ∩ dS X ≠ ∅ :=
by sorry
lemma not_mem_dB_iff
  (C : Finset (List.Vector B n)) (X : List.Vector B n) :
  X ∉ union_dB C ↔ ∀ Y ∈ C, dS Y ∩ dS X = ∅ :=
by sorry
lemma subset_union_dB (C : Finset (List.Vector B n)) :
  C ⊆ union_dB C :=
by sorry
lemma union_dB_subset
  (C₁ C₂ : Finset (List.Vector B n)) (H : C₁ ⊆ C₂) :
  union_dB C₁ ⊆ union_dB C₂  :=
by sorry
lemma not_mem_of_not_mem_dB
  (C : Finset (List.Vector B n)) (X : List.Vector B n)
  (H : X ∉ union_dB C) :
  X ∉ C :=
by sorry
lemma DelCode_insert_iff_not_mem_dB
  (C : Finset (List.Vector B n)) (X : List.Vector B n) (HX : X ∉ C) :
  is_DelCode (insert X C) ↔ is_DelCode C ∧ X ∉ union_dB C :=
by sorry
lemma not_mem_union_dB
  {C : Finset (List.Vector B n)} (HC : is_DelCode C)
  {C₁ C₂ : Finset (List.Vector B n)}
  (HC₁ : C₁ ⊆ C) (HC₂ : C₂ ⊆ C) (H : C₁ ∩ C₂ = ∅)
  (c : List.Vector B n) (Hc : c ∈ C₁) :
  c ∉ union_dB C₂ :=
by sorry
lemma DelCode_union_iff
  {n : Nat} {C : Finset (List.Vector B n)} (HC : is_DelCode C)
  {S C' : Finset (List.Vector B n)} (HSC' : C' ⊆ S) (HC' : is_DelCode C') (H : C ∩ C' = ∅) :
  is_DelCode (C ∪ C') ↔ C' ⊆ S \ union_dB C :=
by sorry
lemma subset_union_dB_of_DelCode
  {S : Finset (List.Vector B n)} {C : Finset (List.Vector B n)}
  (HC : is_DelCode C) (HCS : C ⊆ S)
  {C₁ C₂ : Finset (List.Vector B n)}
  (HC₁ : C₁ ⊆ C) (HC₂ : C₂ ⊆ C) (H : C₁ ∩ C₂ = ∅) :
  C₁ ⊆ S \ union_dB C₂ :=
by sorry
lemma not_mem_union_dB_erase
  {C : Finset (List.Vector B n)} (HC : is_DelCode C)
  (c : List.Vector B n) (Hc : c ∈ C) :
  c ∉ union_dB (erase C c) :=
by sorry
def dS_wt (X : List.Vector B n) (w : Nat) : Finset (List.Vector B (n - 1)) :=
  filter (fun x => wt x = w) (dS X)

lemma mem_dS_wt (X : List.Vector B n) (w : Nat) (Y : List.Vector B (n - 1)) :
  Y ∈ dS_wt X w ↔ Y ∈ dS X ∧ wt Y = w :=
by sorry
lemma dS_wt_subset (X : List.Vector B n) (w : Nat) :
  dS_wt X w ⊆ dS X :=
by sorry
def union_dS_wt (C : Finset (List.Vector B n)) (w : Nat) : Finset (List.Vector B (n - 1)) :=
  filter (fun x => wt x = w) (union_dS C)

lemma mem_union_dS_wt (C : Finset (List.Vector B n)) (w : Nat) (X : List.Vector B (n - 1)) :
  X ∈ union_dS_wt C w ↔ X ∈ union_dS C ∧ wt X = w :=
by sorry
lemma union_dS_wt_empty (w : Nat) :
  union_dS_wt (∅ : Finset (List.Vector B n)) w = ∅ :=
by sorry
lemma  union_dS_wt_insert
  (C : Finset (List.Vector B n)) (w : Nat) (X : List.Vector B n) (HX : X ∉ C):
  union_dS_wt (insert X C) w = dS_wt X w ∪ union_dS_wt C w :=
by sorry
lemma union_dS_wt_subset
  (C : Finset (List.Vector B n)) (w : Nat):
  union_dS_wt C w ⊆ union_dS C :=
by sorry
lemma union_dS_wt_subset_of_subset
  (C₁ C₂ : Finset (List.Vector B n)) (H : C₁ ⊆ C₂) (w : Nat) :
  union_dS_wt C₁ w ⊆ union_dS_wt C₂ w :=
by sorry
lemma union_dS_wt_union
  (C₁ C₂ : Finset (List.Vector B n)) (w : Nat):
  union_dS_wt (C₁ ∪ C₂) w = union_dS_wt C₁ w ∪ union_dS_wt C₂ w :=
by sorry
def Cwr
  (C : Finset (List.Vector B n)) (w r : Nat) : Finset (List.Vector B n) :=
  filter (fun X => card (dS_wt X w) = r) C

lemma mem_Cwr (C : Finset (List.Vector B n)) (w r : Nat) (X : List.Vector B n) :
  X ∈ Cwr C w r ↔ X ∈ C ∧ card (dS_wt X w) = r :=
by sorry
lemma not_mem_Cwr
  (C : Finset (List.Vector B n)) (w r : Nat) (X : List.Vector B n) (Hx : X ∉ C) :
  X ∉ Cwr C w r :=
by sorry
lemma Cwr_empty (w r : Nat) :
  Cwr (∅ : Finset (List.Vector B n)) w r = ∅ :=
by sorry
lemma Cwr_subset (C : Finset (List.Vector B n)) (w r : Nat) :
  Cwr C w r ⊆ C :=
by sorry
lemma Cwr_subset_of_subset
  {C₁ C₂ : Finset (List.Vector B n)} (H : C₁ ⊆ C₂) (w r : Nat)  :
  Cwr C₁ w r ⊆ Cwr C₂ w r :=
by sorry
lemma DelCode_Cwr
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) (w r : Nat) :
  is_DelCode (Cwr C w r) :=
by sorry
lemma Cwr_insert_of_eq
  (C : Finset (List.Vector B n)) (w r : Nat) (X : List.Vector B n)
  (H : card (dS_wt X w) = r) :
  Cwr (insert X C) w r = insert X (Cwr C w r) :=
by sorry
lemma Cwr_insert_of_neq
  (C : Finset (List.Vector B n)) (w r : Nat) (X : List.Vector B n)
  (H : card (dS_wt X w) ≠ r)  :
  Cwr (insert X C) w r = Cwr C w r :=
by sorry
lemma Cwr_inter_of_ne (C : Finset (List.Vector B n)) (w r₁ r₂: ℕ) (Hr : r₁ ≠ r₂):
  Cwr C w r₁ ∩ Cwr C w r₂ = ∅  :=
by sorry
lemma card_union_dS_wt_Cwr_zero (C : Finset (List.Vector B n)) (w : Nat) :
  card (union_dS_wt (Cwr C w 0) w) = 0 :=
by sorry
lemma card_union_dS_wt_Cwr (C : Finset (List.Vector B n)) (HC : is_DelCode C) (w r : Nat) :
  card (union_dS_wt (Cwr C w r) w) = r * card (Cwr C w r) :=
by sorry
def mul_card_dS_wt (C : Finset (List.Vector B n)) (w r : Nat) :=
  r * (card (Cwr C w r))

lemma mul_card_dS_wt_empty (w r : Nat) :
  mul_card_dS_wt (∅ : Finset (List.Vector B n)) w r = 0 :=
by sorry
lemma mul_card_dS_wt_zero (C : Finset (List.Vector B n)) (w : Nat):
  mul_card_dS_wt C w 0 = 0 :=
by sorry
lemma mul_card_dS_wt_eq (C : Finset (List.Vector B n)) (HC : is_DelCode C) (w r : Nat) :
  mul_card_dS_wt C w r = card (union_dS_wt (Cwr C w r) w) :=
by sorry
def Cwr_le (C : Finset (List.Vector B n)) (w r : Nat) : Finset (List.Vector B n) :=
  filter (fun X => card (dS_wt X w) ≤ r) C

lemma mem_Cwr_le (C : Finset (List.Vector B n)) (w r : Nat) (X : List.Vector B n) :
  X ∈ Cwr_le C w r ↔ X ∈ C ∧ card (dS_wt X w) ≤ r :=
by sorry
lemma not_mem_Cwr_le
  (C : Finset (List.Vector B n)) (w r : Nat) (X : List.Vector B n) (HX : X ∉ C) :
  X ∉ Cwr_le C w r :=
by sorry
lemma Cwr_le_empty (w r : Nat) :
  Cwr_le (∅ : Finset (List.Vector B n)) w r = ∅ :=
by sorry
lemma Cwr_le_zero (C : Finset (List.Vector B n)) (w : Nat) :
  Cwr_le C w 0 = Cwr C w 0 :=
by sorry
lemma Cwr_le_subset (C : Finset (List.Vector B n)) (w r : Nat) :
  Cwr_le C w r ⊆ C :=
by sorry
lemma Cwr_subset_le (C : Finset (List.Vector B n)) (w r : Nat) :
  Cwr C w r ⊆ Cwr_le C w r :=
by sorry
lemma DelCode_Cwr_le
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) (w r : Nat) :
  is_DelCode (Cwr_le C w r) :=
by sorry
lemma Cwr_le_insert_of_le
  (C : Finset (List.Vector B n)) (w r : Nat) (X : List.Vector B n)
  (H : card (dS_wt X w) ≤ r) :
  Cwr_le (insert X C) w r = insert X (Cwr_le C w r) :=
by sorry
lemma Cwr_le_insert_of_gt
  (C : Finset (List.Vector B n)) (w r : Nat) (X : List.Vector B n)
  (H : r < card (dS_wt X w)) :
  Cwr_le (insert X C) w r = Cwr_le C w r :=
by sorry
lemma Cwr_le_succ (C : Finset (List.Vector B n)) (w r : Nat) :
  Cwr_le C w (r + 1) = Cwr_le C w r ∪ Cwr C w (r + 1) :=
by sorry
lemma Cwr_le_inter_eq (C : Finset (List.Vector B n)) (w r : Nat) :
  Cwr_le C w r ∩ Cwr C w (r + 1) = ∅ :=
by sorry
lemma card_Cwr_le_succ (C : Finset (List.Vector B n)) (w r : Nat) :
  card (Cwr_le C w (r + 1)) = card (Cwr_le C w r) + card (Cwr C w (r + 1)) :=
by sorry
lemma Cwr_le_length (C : Finset (List.Vector B n)) (w : Nat):
  Cwr_le C w (n - 1 + 1) = C :=
by sorry
lemma card_union_dS_wt_Cwr_le_zero (C : Finset (List.Vector B n)) (w : Nat) :
  card (union_dS_wt (Cwr_le C w 0) w) = 0 :=
by sorry
def mul_card_dS_wt_le : Finset (List.Vector B n) → ℕ → ℕ → ℕ
| C, w, 0       => mul_card_dS_wt C w 0
| C, w, k + 1 => mul_card_dS_wt C w (k + 1) + mul_card_dS_wt_le C w k

lemma mul_card_dS_wt_le_empty (w r : Nat) :
  mul_card_dS_wt_le (∅ : Finset (List.Vector B n)) w r = 0 :=
by sorry
lemma mul_card_dS_wt_le_zero (C : Finset (List.Vector B n)) (w : Nat):
  mul_card_dS_wt_le C w 0 = 0 :=
by sorry
lemma mul_card_dS_wt_le_insert_of_gt
  (C : Finset (List.Vector B n)) (w r : Nat)
  (x : List.Vector B n) (Hr : r < card (dS_wt x w)) :
  mul_card_dS_wt_le (insert x C) w r = mul_card_dS_wt_le C w r :=
by sorry
lemma mul_card_dS_wt_le_insert_of_le
  (C : Finset (List.Vector B n)) (w r : Nat)
  (x : List.Vector B n) (Hx : x ∉ C) (Hr : card (dS_wt x w) ≤ r) :
  mul_card_dS_wt_le (insert x C) w r
  = mul_card_dS_wt_le C w r + card (dS_wt x w) :=
by sorry
lemma mul_card_dS_wt_le_eq
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) (w r : Nat) :
  mul_card_dS_wt_le C w r = card (union_dS_wt (Cwr_le C w r) w) :=
by sorry
lemma mul_card_dS_wt_le_le
  (C : Finset (List.Vector B n)) (w r : Nat) :
  mul_card_dS_wt_le C w r ≤ mul_card_dS_wt_le C w (n - 1 + 1) :=
by sorry
lemma mul_card_dS_wt_le_length
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) (w r : Nat) :
  mul_card_dS_wt_le C w (n - 1 + 1) = card (union_dS_wt C w) :=
by sorry
lemma mul_card_dS_wt_le_card_univ
  {n : Nat} (C : Finset (List.Vector B n)) (HC : is_DelCode C) (w r : Nat) :
  mul_card_dS_wt_le C w r ≤ card (filter (fun x : List.Vector B (n - 1) => wt x = w) univ) :=
by sorry
lemma mul_card_dS_wt_le_card_univ'
  {n : Nat} (C : Finset (List.Vector B n)) (HC : is_DelCode C) (w : Nat) :
  mul_card_dS_wt_le C w n ≤ card (filter (fun x : List.Vector B (n - 1) => wt x = w) univ) :=
by sorry
def Cwr_ge (C : Finset (List.Vector B n)) (w r : Nat) : Finset (List.Vector B n) :=
  filter (fun X => r ≤ card (dS_wt X w)) C

lemma mem_Cwr_ge (C : Finset (List.Vector B n)) (w r : Nat) (X : List.Vector B n) :
  X ∈ Cwr_ge C w r ↔ X ∈ C ∧ r ≤ card (dS_wt X w) :=
by sorry
lemma Cwr_ge_empty (w r : Nat) :
  Cwr_ge (∅ : Finset (List.Vector B n)) w r = ∅ :=
by sorry
lemma Cwr_ge_insert_of_ge
  (C : Finset (List.Vector B n)) (w r : Nat) (X : List.Vector B n)
  (H : r ≤ card (dS_wt X w)) :
  Cwr_ge (insert X C) w r = insert X (Cwr_ge C w r) :=
by sorry
lemma Cwr_ge_insert_of_lt
  (C : Finset (List.Vector B n)) (w r : Nat) (X : List.Vector B n)
  (H : card (dS_wt X w) < r) :
  Cwr_ge (insert X C) w r = Cwr_ge C w r :=
by sorry
lemma Cwr_ge_subset
  (C : Finset (List.Vector B n)) (w r : Nat) :
  Cwr_ge C w r ⊆ C :=
by sorry
lemma Cwr_ge_subset_of_subset
  {C₁ C₂ : Finset (List.Vector B n)} (H : C₁ ⊆ C₂) (w r : Nat)  :
  Cwr_ge C₁ w r ⊆ Cwr_ge C₂ w r :=
by sorry
lemma Cwr_ge_zero (C : Finset (List.Vector B n)) (w : Nat) :
  Cwr_ge C w 0 = C :=
by sorry
lemma DelCode_Cwr_ge
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) (w r : Nat) :
  is_DelCode (Cwr_ge C w r) :=
by sorry
lemma Cwr_ge_eq
  (C : Finset (List.Vector B n)) (w r : Nat) :
  Cwr_ge C w r = Cwr C w r ∪ Cwr_ge C w (r + 1) :=
by sorry
lemma Cwr_subset_ge
  (C : Finset (List.Vector B n)) (w r : Nat) :
  Cwr C w r ⊆ Cwr_ge C w r :=
by sorry
lemma Cwr_le_union_ge (C : Finset (List.Vector B n)) (w r : Nat) :
  Cwr_le C w r ∪ Cwr_ge C w (r + 1) = C :=
by sorry
lemma Cwr_le_inter_ge (C : Finset (List.Vector B n)) (w r : Nat) :
  Cwr_le C w r ∩ Cwr_ge C w (r + 1) = ∅ :=
by sorry
lemma Cwr_ge_succ_eq_sdiff_le (C : Finset (List.Vector B n)) (w r : Nat) :
  Cwr_ge C w (r + 1) = C \ Cwr_le C w r :=
by sorry
lemma card_Cwr_le_add_ge (C : Finset (List.Vector B n)) (w r : Nat) :
  card (Cwr_le C w r) + card (Cwr_ge C w (r + 1)) = card C :=
by sorry
def mul_card_dS_wt_ge (C : Finset (List.Vector B n)) (w r : Nat) : Nat :=
  mul_card_dS_wt_le C w (n - 1 + 1) - mul_card_dS_wt_le C w (r - 1)

lemma mul_card_dS_wt_ge_empty (w r : Nat) :
  mul_card_dS_wt_ge (∅ : Finset (List.Vector B n)) w r = 0 :=
by sorry
lemma mul_card_dS_wt_ge_zero (C : Finset (List.Vector B n)) (w : Nat) :
  mul_card_dS_wt_ge C w 0 = mul_card_dS_wt_le C w (n - 1 + 1) :=
by sorry
lemma mul_card_dS_wt_ge_insert_of_lt
  (C : Finset (List.Vector B n)) (w r : Nat)
  (x : List.Vector B n) (Hr : card (dS_wt x w) < r) :
  mul_card_dS_wt_ge (insert x C) w r = mul_card_dS_wt_ge C w r :=
by sorry
lemma mul_card_dS_wt_ge_insert_of_ge
  (C : Finset (List.Vector B n)) (w r : Nat)
  (x : List.Vector B n) (Hx : x ∉ C) (Hr : r ≤ card (dS_wt x w)) :
  mul_card_dS_wt_ge (insert x C) w r
  = mul_card_dS_wt_ge C w r + card (dS_wt x w)  :=
by sorry
lemma card_dS_wt_ge_le (C : Finset (List.Vector B n)) (w r : Nat) :
  r * card (Cwr_ge C w r) ≤ mul_card_dS_wt_ge C w r :=
by sorry
lemma card_dS_wt_ge_le_univ
  (C : Finset (List.Vector B n)) (H : is_DelCode C) (w r : Nat) :
  card (Cwr_ge C w (r + 1))
  ≤ (card (filter (fun x : List.Vector B (n - 1) => wt x = w) univ)
    - mul_card_dS_wt_le C w r) / (r + 1) :=
by sorry
lemma card_Cwr_le_1
  (C : Finset (List.Vector B n)) (w : Nat):
  card (Cwr_le C w 1) = card (Cwr C w 0) + card (Cwr C w 1) :=
by sorry
lemma card_Cwr_le_2
  (C : Finset (List.Vector B n)) (w : Nat):
  card (Cwr_le C w 2) = card (Cwr C w 0) + card (Cwr C w 1) + card (Cwr C w 2):=
by sorry
lemma mul_card_dS_wt_le_1
  (C : Finset (List.Vector B n)) (w : Nat):
  mul_card_dS_wt_le C w 1 = card (Cwr C w 1) :=
by sorry
lemma mul_card_dS_wt_le_2
  (C : Finset (List.Vector B n)) (w : Nat):
  mul_card_dS_wt_le C w 2 = 2 * card (Cwr C w 2) + card (Cwr C w 1) :=
by sorry
lemma card_le_univ_add_1
  {n : Nat} (C : Finset (List.Vector B n)) (HC : is_DelCode C)
  (w : Nat) (HCw : Cwr C w 0 = ∅) :
  card C ≤ (card (filter (fun x : List.Vector B (n - 1) => wt x = w) univ) + card (Cwr C w 1)) / 2 :=
by sorry
lemma card_le_univ_add_2
  {n : Nat} (C : Finset (List.Vector B n)) (HC : is_DelCode C)
  (w : Nat) (HCw : Cwr C w 0 = ∅) :
  card C ≤ (card (filter (fun x : List.Vector B (n - 1) => wt x = w) univ) + 2 * card (Cwr C w 1) + card (Cwr C w 2)) / 3 :=
by sorry
end B

variable [Fintype α]
variable (S : Finset (List.Vector α n))

def DCs (n :  Nat) : Finset (Finset (List.Vector α n)) :=
  filter is_DelCode (powerset univ)

lemma mem_DCs :
  C ∈ @DCs α _ _ n ↔ is_DelCode C :=
by sorry
def DCs' (n : Nat) : Finset (Finset (List.Vector α n)) :=
  filter is_DelCode' (powerset univ)

lemma DCs'_eq :
  @DCs' α _ _ n = @DCs α _ _ n :=
by sorry
def DCs_sub (S : Finset (List.Vector α n)) : Finset (Finset (List.Vector α n)) :=
  filter is_DelCode (powerset S)

lemma mem_DCs_sub :
  C ∈ DCs_sub S ↔ C ⊆ S ∧ is_DelCode C :=
by sorry
lemma DCs_sub_empty :
  @DCs_sub α _ n _ ∅ = singleton ∅ :=
by sorry
lemma DCs_sub_univ :
  @DCs_sub α _ _ _ univ = DCs n :=
by sorry
lemma DCs_sub_subset
  {S₁ S₂ : Finset (List.Vector α n)} (HS : S₁ ⊆ S₂) :
  DCs_sub S₁ ⊆ DCs_sub S₂ :=
by sorry
def DCs_sub' (S : Finset (List.Vector α n)) : Finset (Finset (List.Vector α n)) :=
  filter is_DelCode' (powerset S)

lemma DCs_sub'_eq :
  DCs_sub' S = DCs_sub S :=
by sorry
def DCs_sub_len (S : Finset (List.Vector α n)) (k : Nat) : Finset (Finset (List.Vector α n)) :=
  filter is_DelCode (powersetCard k S)

lemma mem_DCs_sub_len (k : Nat) :
  C ∈ DCs_sub_len S k ↔ C ⊆ S ∧ card C = k ∧ is_DelCode C :=
by sorry
lemma mem_DCs_sub_len' (S : Finset (List.Vector α n)) (k : Nat) :
  C ∈ DCs_sub_len S k ↔ C ∈ DCs_sub S ∧ card C = k :=
by sorry
def DCs_sub_len' (S : Finset (List.Vector α n)) (k : Nat) : Finset (Finset (List.Vector α n)) :=
  filter is_DelCode' (powersetCard k S)

lemma DCs_sub_len'_eq (S : Finset (List.Vector α n)) (k : Nat) :
  DCs_sub_len' S k = DCs_sub_len S k :=
by sorry
namespace B

def DCs_sub_DC_len_succ
  (S : Finset (List.Vector B n)) (C : Finset (List.Vector B n)) : Finset (Finset (List.Vector B n)) :=
  image (fun x => insert x C) (S \ union_dB C)

lemma mem_DCs_sub_DC_len_succ
  (S : Finset (List.Vector B n)) (C : Finset (List.Vector B n)) (C' : Finset (List.Vector B n)) :
  C' ∈ DCs_sub_DC_len_succ S C ↔ ∃ c ∈ S \ union_dB C, insert c C = C' :=
by sorry
def DCs_sub_DCs_len_succ
  (S : Finset (List.Vector B n)) (Cs : Finset (Finset (List.Vector B n))) : Finset (Finset (List.Vector B n)) :=
  Cs.biUnion (fun C => DCs_sub_DC_len_succ S C)

lemma mem_DCs_sub_DCs_len_succ
  (S : Finset (List.Vector B n)) (Cs : Finset (Finset (List.Vector B n))) (C' : Finset (List.Vector B n)) :
  C' ∈ DCs_sub_DCs_len_succ S Cs ↔ ∃ C ∈ Cs, C' ∈ DCs_sub_DC_len_succ S C :=
by sorry
lemma mem_DCs_sub_DCs_len_succ'
  (S : Finset (List.Vector B n)) (Cs : Finset (Finset (List.Vector B n))) (C' : Finset (List.Vector B n)) :
  C' ∈ DCs_sub_DCs_len_succ S Cs ↔ ∃ C ∈ Cs, ∃ c ∈ S \ union_dB C, insert c C = C' :=
by sorry
lemma DCs_sub_DCs_len_succ_eq
  (S : Finset (List.Vector B n)) (k : Nat) :
  DCs_sub_DCs_len_succ S (DCs_sub_len S k) = DCs_sub_len S (k + 1) :=
by sorry
end B
