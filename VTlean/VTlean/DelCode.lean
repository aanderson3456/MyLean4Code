/- Copyright Manabu Hagiwara 2022, 2026 -/
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

noncomputable instance DecidablePred_is_DelCode [Fintype α] :
  DecidablePred (@is_DelCode α _ n) :=
  Classical.decPred _
lemma DelCode_empty :
  is_DelCode (∅ : Finset (List.Vector α n)) :=
by {
  intro x hx _ _ _
  exact False.elim (Finset.notMem_empty x hx)
}
lemma DelCode_singleton :
  is_DelCode ({X}) :=
by {
  intro x hx y hy hne
  rw [Finset.mem_singleton] at hx hy
  rw [hx, hy] at hne
  exact absurd rfl hne
}
lemma DelCode_subset
  (H : is_DelCode C) (HCC : C' ⊆ C) :
  is_DelCode C' :=
by {
  intro x hx y hy hne
  exact H x (HCC hx) y (HCC hy) hne
}
lemma DelCode_filter
  (H : is_DelCode C) (p : List.Vector α n → Prop) [DecidablePred p] :
  is_DelCode (filter p C) :=
  DelCode_subset C (filter p C) H (Finset.filter_subset p C)
lemma DelCode_sdiff
  (H : is_DelCode C) (S : Finset (List.Vector α n)) :
  is_DelCode (C \ S) :=
  DelCode_subset C (C \ S) H Finset.sdiff_subset
lemma DelCode_insert
  (HC : is_DelCode C) (Hx : ∀ c ∈ C, dS X ∩ dS c = ∅):
  is_DelCode (insert X C) :=
by {
  intro y hy z hz hne
  rw [Finset.mem_insert] at hy hz
  cases hy with
  | inl hyx =>
    cases hz with
    | inl hzx =>
      rw [hyx, hzx] at hne
      contradiction
    | inr hzC =>
      rw [hyx]
      exact Hx z hzC
  | inr hyC =>
    cases hz with
    | inl hzx =>
      rw [hzx, Finset.inter_comm]
      exact Hx y hyC
    | inr hzC =>
      exact HC y hyC z hzC hne
}
lemma DelCode_of_insert
  (H : is_DelCode (insert X C)) :
  is_DelCode C :=
  DelCode_subset (insert X C) C H (Finset.subset_insert X C)
lemma dS_inter_union_dS_iff (C : Finset (List.Vector α n)) :
  dS X ∩ union_dS C = ∅ ↔ ∀ c ∈ C, dS X ∩ dS c = ∅ :=
by {
  constructor
  · intro h c hc
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    rw [Finset.eq_empty_iff_forall_notMem] at h
    have hy_inter : y ∈ dS X ∩ union_dS C := by
      rw [Finset.mem_inter] at hy ⊢
      constructor
      · exact hy.left
      · rw [mem_union_dS]
        exact ⟨c, hc, hy.right⟩
    exact h y hy_inter
  · intro h
    apply Finset.eq_empty_iff_forall_notMem.mpr
    intro y hy
    rw [Finset.mem_inter] at hy
    rw [mem_union_dS] at hy
    rcases hy.right with ⟨c, hc, hyc⟩
    have h_empty := h c hc
    rw [Finset.eq_empty_iff_forall_notMem] at h_empty
    have hy_inter : y ∈ dS X ∩ dS c := by
      rw [Finset.mem_inter]
      exact ⟨hy.left, hyc⟩
    exact h_empty y hy_inter
}

lemma DelCode_insert_iff (Hx : X ∉ C) :
  is_DelCode (insert X C) ↔ is_DelCode C ∧ ∀ c ∈ C, dS X ∩ dS c = ∅ :=
by {
  constructor
  · intro hCx
    constructor
    · exact DelCode_of_insert _ X hCx
    · intro c hc
      apply hCx X (Finset.mem_insert_self X C) c (Finset.mem_insert_of_mem hc)
      rintro rfl
      contradiction
  · rintro ⟨h1, h2⟩
    exact DelCode_insert C X h1 h2
}

lemma DelCode_insert_iff' (Hx : X ∉ C) :
  is_DelCode (insert X C) ↔ is_DelCode C ∧ dS X ∩ union_dS C = ∅ :=
by {
  rw [DelCode_insert_iff C X Hx, dS_inter_union_dS_iff]
}
lemma DelCode_erase (H : is_DelCode C) :
  is_DelCode (erase C X) :=
  DelCode_subset C (erase C X) H (Finset.erase_subset X C)
def replaceCode :=
  insert X' (erase C X)

lemma DelCode_replaceCode
  (HC : is_DelCode C) (HX : X ∈ C) (HX' : dS X' ⊆ dS X) :
  is_DelCode (replaceCode C X X') :=
by {
  unfold replaceCode
  apply DelCode_insert _ _ (DelCode_erase C X HC)
  intro c hc
  rw [← Finset.subset_empty]
  apply Finset.Subset.trans
  · exact Finset.inter_subset_inter_right HX'
  · have hc_mem : c ∈ C := Finset.mem_of_mem_erase hc
    have hc_ne : X ≠ c := by
      intro heq
      rw [heq] at hc
      exact Finset.notMem_erase c C hc
    have h_inter := HC X HX c hc_mem hc_ne
    rw [h_inter]
}
lemma card_replaceCode
  (HC : is_DelCode C)
  (x : List.Vector α n) (Hx : x ∈ C)
  (y : List.Vector α n) (Hxy : dS y ⊆ dS x) :
  card (replaceCode C x y) = card C :=
by {
  unfold replaceCode
  rw [Finset.card_insert_of_notMem]
  · rw [Finset.card_erase_of_mem Hx]
    have h_card_pos : 0 < card C := by
      apply Finset.card_pos.mpr
      exact ⟨x, Hx⟩
    exact Nat.succ_pred_eq_of_pos h_card_pos
  · intro h
    rw [Finset.mem_erase] at h
    have h1 : dS x ∩ dS y = ∅ := HC x Hx y h.2 h.1.symm
    have h2 : dS y ⊆ dS x ∩ dS y := Finset.subset_inter Hxy (Finset.Subset.refl _)
    rw [h1] at h2
    have h3 : dS y = ∅ := Finset.subset_empty.mp h2
    have h4 : List.Vector.sDel y 0 ∈ dS y := by
      rw [List.Vector.mem_dS]
      use 0
      exact ⟨Nat.zero_le _, rfl⟩
    have h5 : dS y ≠ ∅ := Finset.ne_empty_of_mem h4
    contradiction
}
lemma DelCode_flipCode
  {C : Finset (List.Vector B n)} (HC : is_DelCode C) :
  is_DelCode (B.Finset.flipCode C) :=
by {
  intro x hx y hy hne
  rw [B.Finset.mem_flipCode] at hx hy
  rcases hx with ⟨x', hx', hxx'⟩
  rcases hy with ⟨y', hy', hyy'⟩
  rw [← hxx', ← hyy'] at hne
  have hne' : x' ≠ y' := by
    intro h
    rw [h] at hne
    contradiction
  have h_inter := HC x' hx' y' hy' hne'
  rw [dS_flip, dS_flip, ← B.Finset.flipCode_inter, h_inter, B.Finset.flipCode_empty]
}

lemma exists_DC_card_filter_wt_le
  (S : Finset (List.Vector B n)) (HS : B.Finset.flipCode S = S)
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) (HCS : C ⊆ S)
  (a b : Nat) (Ha : a ≤ n) (Hb : b ≤ n) :
  ∃ C' : Finset (List.Vector B n), is_DelCode C' ∧ C' ⊆ S
  ∧ C'.card = C.card ∧ (filter (Icc_wt (n - b) (n - a)) C').card ≤ (filter (Icc_wt a b) C).card :=
by {
  by_cases hle : (filter (Icc_wt (n - b) (n - a)) C).card ≤ (filter (Icc_wt a b) C).card
  · exact ⟨C, HC, HCS, rfl, hle⟩
  · use B.Finset.flipCode C
    rw [← HS]
    -- missing DelCode_flipCode, flipCode_subset, card_flipCode, filter_flipCode_swap
    sorry
}
def sum_card_dS {n : Nat} (C : Finset (List.Vector α n)) : Nat :=
  C.sum (fun c => (dS c).card)

lemma sum_card_dS_empty :
  sum_card_dS (∅ : Finset (List.Vector α n)) = 0 :=
by {
  unfold sum_card_dS
  exact Finset.sum_empty
}
lemma sum_card_dS_insert (H : X ∉ C) :
  sum_card_dS (insert X C) = (dS X).card + sum_card_dS C :=
by {
  unfold sum_card_dS
  exact Finset.sum_insert H
}
def is_DelCode' {n : Nat} (C : Finset (List.Vector α n)) : Prop :=
  (union_dS C).card = sum_card_dS C

instance DecidablePred_is_DelCode' :
  DecidablePred (@is_DelCode' α _ n) :=
fun C => by
  unfold is_DelCode'
  exact instDecidableEqNat _ _

lemma DelCode'_empty :
  is_DelCode' (∅ : Finset (List.Vector α n)) :=
by {
  unfold is_DelCode'
  rw [union_dS_empty, Finset.card_empty, sum_card_dS_empty]
}
lemma card_union_dS_le :
  (union_dS C).card ≤ sum_card_dS C :=
by {
  induction C using Finset.induction_on with
  | empty => exact Nat.le_refl _
  | insert x S hnin IH =>
    rw [sum_card_dS_insert S x hnin, union_dS_insert x S hnin]
    apply Nat.le_trans (Finset.card_union_le _ _)
    exact Nat.add_le_add_left IH _
}
lemma dS_inter_union_dS_of_DelCode'_insert
  (HX : X ∉ C) (HCX : is_DelCode' (insert X C)) :
  dS X ∩ union_dS C = ∅ :=
by {
  unfold is_DelCode' at HCX
  -- missing card_union_dS_insert, zero_of_sub_eq_of_le, card_dS_pos
  sorry
}
lemma DelCode'_of_DelCode'_insert
  (HX : X ∉ C) (HCX : is_DelCode' (insert X C)) :
  is_DelCode' C :=
by {
  unfold is_DelCode'
  -- missing card_union_dS_insert
  sorry
}
lemma card_dS_insert_of_card_dS
  (HC : is_DelCode' C) (HX : X ∉ C) (HCX : dS X ∩ union_dS C = ∅):
  is_DelCode' (insert X C) :=
by {
  unfold is_DelCode' at HC ⊢
  -- missing card_union_dS_insert
  sorry
}
lemma DelCode'_insert_iff (HX : X ∉ C) :
  is_DelCode' (insert X C) ↔ is_DelCode' C ∧ dS X ∩ union_dS C = ∅ :=
by {
  apply Iff.intro
  · intro h
    exact ⟨DelCode'_of_DelCode'_insert C X HX h, dS_inter_union_dS_of_DelCode'_insert C X HX h⟩
  · intro h
    exact card_dS_insert_of_card_dS C X h.left HX h.right
}
lemma DelCode_of_DelCode' (HC : is_DelCode' C) :
  is_DelCode C :=
by {
  induction C using Finset.induction_on with
  | empty => exact DelCode_empty
  | insert s S hs ihC =>
    rw [DelCode'_insert_iff S s hs] at HC
    rw [DelCode_insert_iff' S s hs]
    exact ⟨ihC HC.left, HC.right⟩
}
lemma DelCode'_of_DelCode (HC : is_DelCode C) :
  is_DelCode' C :=
by {
  induction C using Finset.induction_on with
  | empty => exact DelCode'_empty
  | insert s S hs ihC =>
    rw [DelCode_insert_iff' S s hs] at HC
    rw [DelCode'_insert_iff S s hs]
    exact ⟨ihC HC.left, HC.right⟩
}
lemma DelCode'_iff {n : Nat} (C : Finset (List.Vector α n)) :
  is_DelCode' C ↔ is_DelCode C :=
by {
  apply Iff.intro
  · exact DelCode_of_DelCode' C
  · exact DelCode'_of_DelCode C
}
lemma union_dS_inter_of_DelCode
  {C : Finset (List.Vector α n)} (HC : is_DelCode C)
  {C₁ C₂ : Finset (List.Vector α n)} (HC₁ : C₁ ⊆ C) (HC₂ : C₂ ⊆ C)
  (H : C₁ ∩ C₂ = ∅) :
  union_dS C₁ ∩ union_dS C₂ = ∅ :=
by {
  rw [← Finset.subset_empty]
  intro x hx
  rw [Finset.mem_inter] at hx
  have hx1 := hx.1
  have hx2 := hx.2
  rw [mem_union_dS] at hx1 hx2
  rcases hx1 with ⟨y1, hy1, hxy1⟩
  rcases hx2 with ⟨y2, hy2, hxy2⟩
  have h1 : dS y1 ∩ dS y2 = ∅ := by
    apply HC y1 (HC₁ hy1) y2 (HC₂ hy2)
    intro h_eq
    rw [h_eq] at hy1
    have h_mem_inter : y2 ∈ C₁ ∩ C₂ := by
      rw [Finset.mem_inter]
      exact ⟨hy1, hy2⟩
    rw [H] at h_mem_inter
    exact False.elim (Finset.notMem_empty _ h_mem_inter)
  have h2 : x ∈ dS y1 ∩ dS y2 := by
    rw [Finset.mem_inter]
    exact ⟨hxy1, hxy2⟩
  have h3 : dS y1 ∩ dS y2 ≠ ∅ := Finset.ne_empty_of_mem h2
  contradiction
}
namespace B

def dB {n : Nat} (X : List.Vector B n) : Finset (List.Vector B n) :=
  union_dS (IS X)

lemma mem_dB {n : Nat} (X Y : List.Vector B n) :
  Y ∈ dB X ↔ Y ∈ union_dS (IS X) :=
by sorry
lemma mem_dB_iff {n : Nat} (X Y : List.Vector B n) :
  Y ∈ dB X ↔ IS X ∩ IS Y ≠ ∅ :=
by {
  -- missing mem_dB, mem_IS_of_mem_dS, exists_mem_of_ne_empty, mem_dS_of_mem_IS
  sorry
}
lemma mem_dB_iff' {n : Nat} (X Y : List.Vector B n) :
  Y ∈ dB X ↔ dS X ∩ dS Y ≠ ∅ :=
by {
  rw [mem_dB_iff]
  -- missing IS_inter_ne_empty_iff
  sorry
}
def union_dB {n : Nat} (C : Finset (List.Vector B n)) :=
  C.biUnion dB

lemma union_dB_empty {n : Nat} :
  union_dB (∅ : Finset (List.Vector B n)) = ∅ :=
by {
  unfold union_dB
  exact Finset.biUnion_empty
}
lemma mem_union_dB (C : Finset (List.Vector B n)) (X : List.Vector B n) :
  X ∈ union_dB C ↔ ∃ Y ∈ C, X ∈ dB Y :=
by {
  unfold union_dB
  exact Finset.mem_biUnion
}
lemma mem_union_dB_iff (C : Finset (List.Vector B n)) (X : List.Vector B n) :
  X ∈ union_dB C ↔ ∃ Y ∈ C, dS Y ∩ dS X ≠ ∅ :=
by {
  apply Iff.intro
  · intro h
    rw [mem_union_dB] at h
    rcases h with ⟨Y, hY, hXY⟩
    rw [mem_dB_iff'] at hXY
    exact ⟨Y, hY, hXY⟩
  · intro h
    rcases h with ⟨Y, hY, hXY⟩
    rw [mem_union_dB]
    use Y
    exact ⟨hY, (mem_dB_iff' Y X).mpr hXY⟩
}
lemma not_mem_dB_iff
  (C : Finset (List.Vector B n)) (X : List.Vector B n) :
  X ∉ union_dB C ↔ ∀ Y ∈ C, dS Y ∩ dS X = ∅ :=
by {
  apply Iff.intro
  · intro h Y hY
    by_contra h_ne
    have h_mem : X ∈ union_dB C := by
      rw [mem_union_dB_iff]
      exact ⟨Y, hY, h_ne⟩
    contradiction
  · intro h h_mem
    rw [mem_union_dB_iff] at h_mem
    rcases h_mem with ⟨Y, hY, hXY⟩
    exact hXY (h Y hY)
}
lemma subset_union_dB (C : Finset (List.Vector B n)) :
  C ⊆ union_dB C :=
by {
  intro x hx
  rw [mem_union_dB_iff]
  use x
  exact ⟨hx, by {
    rw [Finset.inter_self]
    have h4 : List.Vector.sDel x 0 ∈ dS x := by
      rw [List.Vector.mem_dS]
      use 0
      exact ⟨Nat.zero_le _, rfl⟩
    exact Finset.ne_empty_of_mem h4
  }⟩
}
lemma union_dB_subset
  (C₁ C₂ : Finset (List.Vector B n)) (H : C₁ ⊆ C₂) :
  union_dB C₁ ⊆ union_dB C₂  :=
by {
  intro x hx
  rw [mem_union_dB_iff] at hx
  rcases hx with ⟨y, hy, hxy⟩
  rw [mem_union_dB_iff]
  exact ⟨y, H hy, hxy⟩
}
lemma not_mem_of_not_mem_dB
  (C : Finset (List.Vector B n)) (X : List.Vector B n)
  (H : X ∉ union_dB C) :
  X ∉ C :=
by {
  intro h
  have hX : X ∈ union_dB C := subset_union_dB C h
  contradiction
}
lemma DelCode_insert_iff_not_mem_dB
  (C : Finset (List.Vector B n)) (X : List.Vector B n) (HX : X ∉ C) :
  is_DelCode (insert X C) ↔ is_DelCode C ∧ X ∉ union_dB C :=
by {
  rw [DelCode_insert_iff C X HX, not_mem_dB_iff]
  apply Iff.intro
  · intro h
    refine ⟨h.1, fun Y hY => ?_⟩
    have h_eq := h.2 Y hY
    rw [Finset.inter_comm] at h_eq
    exact h_eq
  · intro h
    refine ⟨h.1, fun Y hY => ?_⟩
    have h_eq := h.2 Y hY
    rw [Finset.inter_comm] at h_eq
    exact h_eq
}
lemma not_mem_union_dB
  {C : Finset (List.Vector B n)} (HC : is_DelCode C)
  {C₁ C₂ : Finset (List.Vector B n)}
  (HC₁ : C₁ ⊆ C) (HC₂ : C₂ ⊆ C) (H : C₁ ∩ C₂ = ∅)
  (c : List.Vector B n) (Hc : c ∈ C₁) :
  c ∉ union_dB C₂ :=
by {
  rw [not_mem_dB_iff]
  intro y hy
  apply HC y (HC₂ hy) c (HC₁ Hc)
  intro h_eq
  have h_mem : c ∈ C₁ ∩ C₂ := by
    rw [Finset.mem_inter]
    exact ⟨Hc, by { rw [← h_eq]; exact hy }⟩
  rw [H] at h_mem
  exact Finset.notMem_empty _ h_mem
}
lemma DelCode_union_iff
  {n : Nat} {C : Finset (List.Vector B n)} (HC : is_DelCode C)
  {S C' : Finset (List.Vector B n)} (HSC' : C' ⊆ S) (HC' : is_DelCode C') (H : C ∩ C' = ∅) :
  is_DelCode (C ∪ C') ↔ C' ⊆ S \ union_dB C :=
by {
  apply Iff.intro
  · intro h x hx
    rw [Finset.mem_sdiff]
    exact ⟨HSC' hx, by {
      rw [not_mem_dB_iff]
      intro y hy
      apply h y (by { rw [Finset.mem_union]; exact Or.inl hy }) x (by { rw [Finset.mem_union]; exact Or.inr hx })
      intro h_eq
      have H' : C ∩ C' ≠ ∅ := by
        have h_mem : y ∈ C ∩ C' := by
          rw [Finset.mem_inter]
          exact ⟨hy, by { rw [h_eq]; exact hx }⟩
        exact Finset.ne_empty_of_mem h_mem
      contradiction
    }⟩
  · intro h x hx y hy hne
    rw [Finset.mem_union] at hx
    rcases hx with hx | hx
    · rw [Finset.mem_union] at hy
      rcases hy with hy | hy
      · exact HC x hx y hy hne
      · have H' : y ∈ S \ union_dB C := h hy
        rw [Finset.mem_sdiff] at H'
        rw [not_mem_dB_iff] at H'
        exact H'.2 x hx
    · rw [Finset.mem_union] at hy
      rcases hy with hy | hy
      · have H' : x ∈ S \ union_dB C := h hx
        rw [Finset.mem_sdiff] at H'
        rw [not_mem_dB_iff] at H'
        have h_eq := H'.2 y hy
        rw [Finset.inter_comm] at h_eq
        exact h_eq
      · exact HC' x hx y hy hne
}
lemma subset_union_dB_of_DelCode
  {S : Finset (List.Vector B n)} {C : Finset (List.Vector B n)}
  (HC : is_DelCode C) (HCS : C ⊆ S)
  {C₁ C₂ : Finset (List.Vector B n)}
  (HC₁ : C₁ ⊆ C) (HC₂ : C₂ ⊆ C) (H : C₁ ∩ C₂ = ∅) :
  C₁ ⊆ S \ union_dB C₂ :=
by {
  intro y hy
  rw [Finset.mem_sdiff]
  exact ⟨HCS (HC₁ hy), not_mem_union_dB HC HC₁ HC₂ H y hy⟩
}
lemma not_mem_union_dB_erase
  {C : Finset (List.Vector B n)} (HC : is_DelCode C)
  (c : List.Vector B n) (Hc : c ∈ C) :
  c ∉ union_dB (erase C c) :=
by {
  rw [not_mem_dB_iff]
  intro y hy
  apply HC y (Finset.erase_subset _ _ hy) c Hc
  rw [Finset.mem_erase] at hy
  exact hy.1
}
def dS_wt (X : List.Vector B n) (w : Nat) : Finset (List.Vector B (n - 1)) :=
  filter (fun x => wt x = w) (dS X)

lemma mem_dS_wt (X : List.Vector B n) (w : Nat) (Y : List.Vector B (n - 1)) :
  Y ∈ dS_wt X w ↔ Y ∈ dS X ∧ wt Y = w :=
by {
  unfold dS_wt
  rw [Finset.mem_filter]
}
lemma dS_wt_subset (X : List.Vector B n) (w : Nat) :
  dS_wt X w ⊆ dS X :=
by {
  intro x hx
  rw [mem_dS_wt] at hx
  exact hx.1
}
def union_dS_wt (C : Finset (List.Vector B n)) (w : Nat) : Finset (List.Vector B (n - 1)) :=
  filter (fun x => wt x = w) (union_dS C)

lemma mem_union_dS_wt (C : Finset (List.Vector B n)) (w : Nat) (X : List.Vector B (n - 1)) :
  X ∈ union_dS_wt C w ↔ X ∈ union_dS C ∧ wt X = w :=
by {
  unfold union_dS_wt
  rw [Finset.mem_filter]
}
lemma union_dS_wt_empty (w : Nat) :
  union_dS_wt (∅ : Finset (List.Vector B n)) w = ∅ :=
by {
  unfold union_dS_wt
  rw [union_dS_empty, Finset.filter_empty]
}
lemma  union_dS_wt_insert
  (C : Finset (List.Vector B n)) (w : Nat) (X : List.Vector B n) (HX : X ∉ C):
  union_dS_wt (insert X C) w = dS_wt X w ∪ union_dS_wt C w :=
by {
  unfold union_dS_wt dS_wt
  rw [List.Vector.union_dS_insert X C HX, Finset.filter_union]
}
lemma union_dS_wt_subset
  (C : Finset (List.Vector B n)) (w : Nat):
  union_dS_wt C w ⊆ union_dS C :=
by {
  intro x hx
  rw [mem_union_dS_wt] at hx
  exact hx.1
}
lemma union_dS_wt_subset_of_subset
  (C₁ C₂ : Finset (List.Vector B n)) (H : C₁ ⊆ C₂) (w : Nat) :
  union_dS_wt C₁ w ⊆ union_dS_wt C₂ w :=
by {
  intro x hx
  rw [mem_union_dS_wt] at hx ⊢
  exact ⟨union_dS_subset_of_subset _ _ H hx.1, hx.2⟩
}
lemma union_dS_wt_union
  (C₁ C₂ : Finset (List.Vector B n)) (w : Nat):
  union_dS_wt (C₁ ∪ C₂) w = union_dS_wt C₁ w ∪ union_dS_wt C₂ w :=
by {
  apply Finset.Subset.antisymm
  · intro x hx
    rw [mem_union_dS_wt, union_dS_union, Finset.mem_union] at hx
    rcases hx.1 with h_left | h_right
    · rw [Finset.mem_union, mem_union_dS_wt]
      exact Or.inl ⟨h_left, hx.2⟩
    · rw [Finset.mem_union, mem_union_dS_wt]
      exact Or.inr ⟨h_right, hx.2⟩
  · apply Finset.union_subset
    · exact union_dS_wt_subset_of_subset _ _ Finset.subset_union_left _
    · exact union_dS_wt_subset_of_subset _ _ Finset.subset_union_right _
}
def Cwr
  (C : Finset (List.Vector B n)) (w r : Nat) : Finset (List.Vector B n) :=
  filter (fun X => card (dS_wt X w) = r) C

lemma mem_Cwr (C : Finset (List.Vector B n)) (w r : Nat) (X : List.Vector B n) :
  X ∈ Cwr C w r ↔ X ∈ C ∧ card (dS_wt X w) = r :=
by {
  unfold Cwr
  rw [Finset.mem_filter]
}
lemma not_mem_Cwr
  (C : Finset (List.Vector B n)) (w r : Nat) (X : List.Vector B n) (Hx : X ∉ C) :
  X ∉ Cwr C w r :=
by {
  intro h
  rw [mem_Cwr] at h
  exact Hx h.1
}
lemma Cwr_empty (w r : Nat) :
  Cwr (∅ : Finset (List.Vector B n)) w r = ∅ :=
by {
  unfold Cwr
  exact Finset.filter_empty
}
lemma Cwr_subset (C : Finset (List.Vector B n)) (w r : Nat) :
  Cwr C w r ⊆ C :=
by {
  intro x hx
  rw [mem_Cwr] at hx
  exact hx.1
}
lemma Cwr_subset_of_subset
  {C₁ C₂ : Finset (List.Vector B n)} (H : C₁ ⊆ C₂) (w r : Nat)  :
  Cwr C₁ w r ⊆ Cwr C₂ w r :=
by {
  intro x hx
  rw [mem_Cwr] at hx ⊢
  exact ⟨H hx.1, hx.2⟩
}
lemma DelCode_Cwr
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) (w r : Nat) :
  is_DelCode (Cwr C w r) :=
by {
  exact DelCode_subset HC (Cwr_subset C w r)
}
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
noncomputable def DCs_sub (S : Finset (List.Vector α n)) : Finset (Finset (List.Vector α n)) :=
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
noncomputable def DCs_sub_len (S : Finset (List.Vector α n)) (k : Nat) : Finset (Finset (List.Vector α n)) :=
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
