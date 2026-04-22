import VTlean.DelCode

open Nat List.Vector Finset

variable {α : Type} [DecidableEq α] [Fintype α]
variable {n : Nat} (S S₁ S₂ C : Finset (List.Vector α n))

def is_optimal {n : Nat} (C : Finset (List.Vector α n)) (HC : is_DelCode C) : Prop :=
  ∀ C' : Finset (List.Vector α n), is_DelCode C' → Finset.card C' ≤ Finset.card C

def is_optimal' (C : Finset (List.Vector α n)) (HC : is_DelCode C) : Prop :=
  ∀ C' : Finset (List.Vector α n), is_DelCode' C' → Finset.card C' ≤ Finset.card C

instance Decidableis_optimal (HC : is_DelCode C) :
  Decidable (is_optimal C HC) := by unfold is_optimal; infer_instance
instance Decidableis_optimal' (HC : is_DelCode C) :
  Decidable (is_optimal' C HC) := by unfold is_optimal'; infer_instance
lemma optimal'_iff (HC : is_DelCode C) :
  is_optimal' C HC ↔ is_optimal C HC := by
  unfold is_optimal' is_optimal
  apply Iff.intro
  · intro h C' hC'; rw [← DelCode'_iff] at hC'; exact h C' hC'
  · intro h C' hC'; rw [DelCode'_iff] at hC'; exact h C' hC'
def is_optimal_sub (HC : is_DelCode C) : Prop :=
  ∀ C' ⊆ S, is_DelCode C' → Finset.card C' ≤ Finset.card C

def is_optimal_sub' (HC : is_DelCode C) : Prop :=
  ∀ C' ⊆ S, is_DelCode' C' → Finset.card C' ≤ Finset.card C

instance Decidableis_optimal_sub (HC : is_DelCode C) :
  Decidable (is_optimal_sub S C HC) := by unfold is_optimal_sub; infer_instance
instance Decidableis_optimal_sub' (HC : is_DelCode C) :
  Decidable (is_optimal_sub S C HC) := by unfold is_optimal_sub; infer_instance
lemma optimal_sub'_iff (HC : is_DelCode C) :
  is_optimal_sub' S C HC ↔ is_optimal_sub S C HC := by
  unfold is_optimal_sub' is_optimal_sub
  apply Iff.intro
  · intro h C' hS hC'; rw [← DelCode'_iff] at hC'; exact h C' hS hC'
  · intro h C' hS hC'; rw [DelCode'_iff] at hC'; exact h C' hS hC'
lemma is_optimal_sub_univ (HC : is_DelCode C) :
  is_optimal_sub univ C HC ↔ is_optimal C HC := by
  unfold is_optimal_sub is_optimal
  apply Iff.intro
  · intro h C' hC'; exact h C' (subset_univ C') hC'
  · intro h C' _ hC'; exact h C' hC'
lemma optimal_sub_of_supset
  (HS : S₁ ⊆ S₂) (HC : is_DelCode C) (HCS : is_optimal_sub S₂ C HC) :
  is_optimal_sub S₁ C HC := by
  intro C' hS hC'
  exact HCS _ (Finset.Subset.trans hS HS) hC'
lemma optimal_sub_of_ex
  (HC : is_DelCode C) (HCS : is_optimal_sub S₁ C HC)
  (Hex : ∀ C₂ ∈ DCs_sub S₂, ∃ C₁ ∈ DCs_sub S₁, Finset.card C₁ = Finset.card C₂) :
  is_optimal_sub S₂ C HC := by
  intro S' hSU hS'
  have h_mem : S' ∈ DCs_sub S₂ := by rw [mem_DCs_sub]; exact ⟨hSU, hS'⟩
  have Hex_S' := Hex S' h_mem
  rcases Hex_S' with ⟨C₁, HC₁, HC₁C₂⟩
  rw [← HC₁C₂]
  rw [mem_DCs_sub] at HC₁
  exact HCS C₁ HC₁.left HC₁.right
lemma exists_DelCode_erase
  (HC : C ∈ DCs_sub S)
  (X : List.Vector α n) (HX : ∃ X' ∈ S, X' ≠ X ∧ dS X' ⊆ dS X) :
  ∃ C' ∈ DCs_sub (erase S X), Finset.card C' = Finset.card C := by
  rw [mem_DCs_sub] at HC
  rcases HX with ⟨X', HX', HXX'_left, HXX'_right⟩
  cases Classical.em (X ∈ C) with
  | inl hXC =>
    use (replaceCode C X X')
    constructor
    · rw [mem_DCs_sub]
      constructor
      · rw [replaceCode, insert_subset_iff]
        constructor
        · rw [mem_erase]
          exact ⟨HXX'_left, HX'⟩
        · apply erase_subset_erase
          exact HC.left
      · exact DelCode_replaceCode _ _ _ HC.right hXC HXX'_right
    · exact card_replaceCode _ HC.right _ hXC X' HXX'_right
  | inr hnXC =>
    use C
    constructor
    · rw [mem_DCs_sub]
      constructor
      · intro z hzC
        rw [mem_erase]
        constructor
        · intro h
          rw [h] at hzC
          contradiction
        · exact HC.left hzC
      · exact HC.right
    · rfl
lemma exists_DelCode_sdiff
  (HC : C ∈ DCs_sub S)
  (X : Finset (List.Vector α n)) (HX : ∀ x ∈ X, ∃ x' ∈ S \ X, x' ≠ x ∧ dS x' ⊆ dS x) :
  ∃ C' ∈ DCs_sub (S \ X), Finset.card C' = Finset.card C := by
  revert S C
  induction X using Finset.induction with
  | empty =>
    intro S C HC HX
    use C
    constructor
    · rw [sdiff_empty]; exact HC
    · rfl
  | insert x X hx ihX =>
    intro S C HC HX
    have H_eq : S \ insert x X = (S.erase x) \ X := by ext a; simp [mem_sdiff, mem_insert, mem_erase]; tauto
    rw [H_eq]
    have Hex_erase : ∃ x' ∈ S, x' ≠ x ∧ dS x' ⊆ dS x := by
      rcases HX x (mem_insert_self x X) with ⟨x', hx', hxx'_ne, hxx'_sub⟩
      rw [mem_sdiff] at hx'
      exact ⟨x', hx'.left, hxx'_ne, hxx'_sub⟩
    rcases exists_DelCode_erase S C HC x Hex_erase with ⟨C', hC', hCC'⟩
    rw [← hCC']
    apply ihX (erase S x) C' hC'
    intro y hy
    rcases HX y (mem_insert_of_mem hy) with ⟨y', hy', hyy'_ne, hyy'_sub⟩
    use y'
    rw [H_eq] at hy'
    exact ⟨hy', hyy'_ne, hyy'_sub⟩
lemma exists_DelCode_sdiff'
  (HC : C ∈ DCs_sub S)
  (X : Finset (List.Vector α n)) (HX : ∀ x ∈ S ∩ X, ∃ x' ∈ S \ X, x' ≠ x ∧ dS x' ⊆ dS x) :
  ∃ C' ∈ DCs_sub (S \ X), Finset.card C' = Finset.card C := by
  have H_eq : S \ X = S \ (S ∩ X) := by
    ext a; simp only [mem_sdiff, mem_inter]; tauto
  rw [H_eq]
  apply exists_DelCode_sdiff S C HC
  intro x hx
  rcases HX x hx with ⟨x', hx'_mem, hx'_ne, hx'_sub⟩
  use x'
  rw [← H_eq]
  exact ⟨hx'_mem, hx'_ne, hx'_sub⟩
lemma optimal_sub_erase_iff
  (C : Finset (List.Vector α n)) (HC : is_DelCode C)
  (X : List.Vector α n) (HX : ∃ X' ∈ S, X' ≠ X ∧ dS X' ⊆ dS X) :
  is_optimal_sub (erase S X) C HC ↔ is_optimal_sub S C HC := by
  apply Iff.intro
  · intro h
    have Hex : ∀ C₂ ∈ DCs_sub S, ∃ C₁ ∈ DCs_sub (erase S X), Finset.card C₁ = Finset.card C₂ := by
      intro C₂ hC₂
      exact exists_DelCode_erase (HC := hC₂) (HX := HX)
    exact optimal_sub_of_ex (HCS := h) (Hex := Hex)
  · intro h
    exact optimal_sub_of_supset (HS := erase_subset X S) (HCS := h)
lemma optimal_sub_sdiff_iff
  (HC : is_DelCode C)
  (X : Finset (List.Vector α n)) (HX : ∀ x ∈ X, ∃ y ∈ S \ X, y ≠ x ∧ dS y ⊆ dS x) :
  is_optimal_sub (S \ X) C HC ↔ is_optimal_sub S C HC := by
  revert S
  induction X using Finset.induction with
  | empty =>
    intro S HX
    rw [sdiff_empty]
  | insert x X hx ihX =>
    intro S HX
    have H_eq : S \ insert x X = (S.erase x) \ X := by ext a; simp [mem_sdiff, mem_insert, mem_erase]; tauto
    rw [H_eq]
    have HX_erase : ∀ x' ∈ X, ∃ y ∈ S.erase x \ X, y ≠ x' ∧ dS y ⊆ dS x' := by
      intro x' hx'
      rcases HX x' (mem_insert_of_mem hx') with ⟨y, hy_mem, hy_ne, hy_sub⟩
      use y
      rw [H_eq] at hy_mem
      exact ⟨hy_mem, hy_ne, hy_sub⟩
    have ih := ihX (erase S x) HX_erase
    apply Iff.trans ih
    apply optimal_sub_erase_iff
    rcases HX x (mem_insert_self x X) with ⟨y, hy_mem, hy_ne, hy_sub⟩
    use y
    rw [mem_sdiff] at hy_mem
    exact ⟨hy_mem.left, hy_ne, hy_sub⟩
lemma optimal_sub_sdiff_iff'
  (HC : is_DelCode C)
  (X : Finset (List.Vector α n)) (HX : ∀ x ∈ S ∩ X, ∃ y ∈ S \ X, y ≠ x ∧ dS y ⊆ dS x) :
  is_optimal_sub (S \ X) C HC ↔ is_optimal_sub S C HC := by
  have H_eq : S \ X = S \ (S ∩ X) := by
    ext a; simp only [mem_sdiff, mem_inter]; tauto
  rw [H_eq]
  rw [optimal_sub_sdiff_iff S C HC]
  intro x hx
  rcases HX x hx with ⟨y, hy_mem, hy_ne, hy_sub⟩
  use y
  rw [← H_eq]
  exact ⟨hy_mem, hy_ne, hy_sub⟩
def is_card_DCs_sub_le (k : Nat) : Prop :=
  ∀ C' ⊆ S, is_DelCode C' → Finset.card C' ≤ k

instance Decidableis_card_DCs_sub_le  (k : Nat) :
  Decidable (is_card_DCs_sub_le S k) := by unfold is_card_DCs_sub_le; infer_instance
def is_card_DCs_sub_le' (k : Nat) : Prop :=
  ∀ C' ⊆ S, is_DelCode' C' → Finset.card C' ≤ k

instance Decidableis_card_DCs_sub_le'  (k : Nat) :
  Decidable (is_card_DCs_sub_le' S k) := by unfold is_card_DCs_sub_le'; infer_instance
lemma card_DCs_sub_le'_iff (k : Nat) :
  is_card_DCs_sub_le' S k ↔ is_card_DCs_sub_le S k := by
  unfold is_card_DCs_sub_le' is_card_DCs_sub_le
  apply Iff.intro
  · intro h C' hS hC'; rw [← DelCode'_iff] at hC'; exact h C' hS hC'
  · intro h C' hS hC'; rw [DelCode'_iff] at hC'; exact h C' hS hC'
lemma is_card_DCs_sub_le_DC (HC : is_DelCode C) :
  is_card_DCs_sub_le S (Finset.card C) ↔ is_optimal_sub S C HC := by
  rfl
lemma card_DCs_sub_le_of_supset
  {S₁ S₂ : Finset (List.Vector α n)} (HS : S₁ ⊆ S₂)
  (k : Nat) (HSk : is_card_DCs_sub_le S₂ k) :
  is_card_DCs_sub_le S₁ k := by
  intro C hCS hC
  exact HSk C (Finset.Subset.trans hCS HS) hC
lemma card_DCs_sub_le_of_ex
  {S₁ S₂ : Finset (List.Vector α n)}
  (k : Nat) (HSk : is_card_DCs_sub_le S₁ k)
  (Hex : ∀ C₂ ∈ DCs_sub S₂, ∃ C₁ ∈ DCs_sub S₁, Finset.card C₁ = Finset.card C₂) :
  is_card_DCs_sub_le S₂ k := by
  intro S' hSU hS'
  have h_mem : S' ∈ DCs_sub S₂ := by rw [mem_DCs_sub]; exact ⟨hSU, hS'⟩
  have Hex_S' := Hex S' h_mem
  rcases Hex_S' with ⟨C₁, HC₁, HC₁C₂⟩
  rw [← HC₁C₂]
  rw [mem_DCs_sub] at HC₁
  exact HSk C₁ HC₁.left HC₁.right
lemma card_DCs_sub_le_erase_iff
  {n : Nat} (S : Finset (List.Vector α n))
  (X : List.Vector α n) (Hx : ∃ X' ∈ S, X' ≠ X ∧ dS X' ⊆ dS X) (k : Nat) :
  is_card_DCs_sub_le (erase S X) k ↔ is_card_DCs_sub_le S k := by
  apply Iff.intro
  · intro h
    have Hex : ∀ C₂ ∈ DCs_sub S, ∃ C₁ ∈ DCs_sub (erase S X), Finset.card C₁ = Finset.card C₂ := by
      intro C₂ hC₂
      exact exists_DelCode_erase (HC := hC₂) (HX := Hx)
    exact card_DCs_sub_le_of_ex k h Hex
  · intro h
    exact card_DCs_sub_le_of_supset (erase_subset X S) k h
lemma card_DCs_sub_le_sdiff_iff
  (X : Finset (List.Vector α n)) (HX : ∀ x ∈ X, ∃ x' ∈ S \ X, x' ≠ x ∧ dS x' ⊆ dS x) (k : Nat) :
  is_card_DCs_sub_le (S \ X) k ↔ is_card_DCs_sub_le S k := by
  revert S
  induction X using Finset.induction with
  | empty =>
    intro S HX
    rw [sdiff_empty]
  | insert x X hx ihX =>
    intro S HX
    have H_eq : S \ insert x X = (S.erase x) \ X := by ext a; simp [mem_sdiff, mem_insert, mem_erase]; tauto
    rw [H_eq]
    have HX_erase : ∀ x' ∈ X, ∃ y ∈ S.erase x \ X, y ≠ x' ∧ dS y ⊆ dS x' := by
      intro x' hx'
      rcases HX x' (mem_insert_of_mem hx') with ⟨y, hy_mem, hy_ne, hy_sub⟩
      use y
      rw [H_eq] at hy_mem
      exact ⟨hy_mem, hy_ne, hy_sub⟩
    have ih := ihX (erase S x) HX_erase
    apply Iff.trans ih
    apply card_DCs_sub_le_erase_iff
    rcases HX x (mem_insert_self x X) with ⟨y, hy_mem, hy_ne, hy_sub⟩
    use y
    rw [mem_sdiff] at hy_mem
    exact ⟨hy_mem.left, hy_ne, hy_sub⟩
lemma card_DCs_sub_le_sdiff_iff'
  (X : Finset (List.Vector α n))
  (HX : ∀ x ∈ S ∩ X, ∃ x' ∈ S \ X, x' ≠ x ∧ dS x' ⊆ dS x) (k : Nat) :
  is_card_DCs_sub_le (S \ X) k ↔ is_card_DCs_sub_le S k := by
  have H_eq : S \ X = S \ (S ∩ X) := by
    ext a; simp only [mem_sdiff, mem_inter]; tauto
  rw [H_eq]
  rw [card_DCs_sub_le_sdiff_iff _ _ (HX := ?_)]
  · intro x hx
    rcases HX x hx with ⟨y, hy_mem, hy_ne, hy_sub⟩
    use y
    rw [← H_eq]
    exact ⟨hy_mem, hy_ne, hy_sub⟩
lemma card_DC_sub_le_of_succ_empty
  {n : Nat} (S : Finset (List.Vector α n)) (k : Nat) (Hk : DCs_sub_len S (k + 1) = ∅) :
  is_card_DCs_sub_le S k := by
  intro C hS hC
  cases Classical.em (Finset.card C ≤ k) with
  | inl hle =>
    exact hle
  | inr hnle =>
    rw [not_le] at hnle
    -- exists_subset_card_le is a Lean3 mathlib lemma not yet ported
    -- Finset.exists_subset_card_le : k ≤ card S → ∃ S' ⊆ S, card S' = k
    rcases Finset.exists_subset_card_le (s := C) (by omega : k + 1 ≤ Finset.card C) with ⟨C', hC'_sub, hC'_card⟩
    have h : C' ∈ DCs_sub_len S (k + 1) := by
      rw [mem_DCs_sub_len]
      constructor
      · exact Finset.Subset.trans hC'_sub hS
      · constructor
        · exact hC'_card
        · exact DelCode_subset _ _ hC hC'_sub
    have h_absurd : (DCs_sub_len S (k + 1)).Nonempty := ⟨C', h⟩
    rw [Hk] at h_absurd
    exact absurd h_absurd (by simp)
namespace B

lemma repO_mem_dS (X  : List.Vector B n) (HX : wt X ≤ 1) :
  List.Vector.replicate (n - 1) O ∈ dS X := by
  -- sDel_of_wt_le: when wt X ≤ 1, some sDel gives repeat O (n-1); not yet ported
  sorry
lemma repI_mem_dS (X  : List.Vector B n) (HX : n - 1 ≤ wt X) :
  List.Vector.replicate (n - 1) I ∈ dS X := by
  -- sDel_of_le_wt: when n-1 ≤ wt X, some sDel gives repeat I (n-1); not yet ported
  sorry
lemma card_Iic_wt_le
  {C : Finset (List.Vector B n)} (H : is_DelCode C):
  Finset.card (filter (Iic_wt 1) C) ≤ 1 := by
  cases Classical.em (Finset.card (filter (Iic_wt 1) C) ≤ 1) with
  | inl hle => exact hle
  | inr hnle =>
    rw [not_le] at hnle
    -- exists_distinct: Lean3 lemma ↔ Finset.one_lt_card in Lean4
    rw [Finset.one_lt_card] at hnle
    obtain ⟨X, hX, Y, hY, hXY⟩ := hnle
    have h : dS X ∩ dS Y ≠ ∅ := by
      apply Finset.Nonempty.ne_empty
      apply Finset.nonempty_of_mem (a := List.Vector.replicate (n - 1) O)
      rw [mem_inter]
      constructor
      · apply repO_mem_dS
        rw [mem_filter] at hX
        exact hX.right
      · apply repO_mem_dS
        rw [mem_filter] at hY
        exact hY.right
    have h_absurd := H X Y ?_ ?_ hXY
    · contradiction
    · rw [mem_filter] at hX; exact hX.left
    · rw [mem_filter] at hY; exact hY.left
lemma card_Ici_wt_le
  {C : Finset (List.Vector B n)} (HC : is_DelCode C):
  Finset.card (filter (Ici_wt (n - 1)) C) ≤ 1 := by
  cases Classical.em (Finset.card (filter (Ici_wt (n - 1)) C) ≤ 1) with
  | inl hle => exact hle
  | inr hnle =>
    rw [not_le] at hnle
    rw [Finset.one_lt_card] at hnle
    obtain ⟨X, hX, Y, hY, hXY⟩ := hnle
    have h : dS X ∩ dS Y ≠ ∅ := by
      apply Finset.Nonempty.ne_empty
      apply Finset.nonempty_of_mem (a := List.Vector.replicate (n - 1) I)
      rw [mem_inter]
      constructor
      · apply repI_mem_dS
        rw [mem_filter] at hX
        exact hX.right
      · apply repI_mem_dS
        rw [mem_filter] at hY
        exact hY.right
    have h_absurd := HC X Y ?_ ?_ hXY
    · contradiction
    · rw [mem_filter] at hX; exact hX.left
    · rw [mem_filter] at hY; exact hY.left
lemma card_le_filter_Icc
  {C : Finset (List.Vector B n)} (HC : is_DelCode C):
  Finset.card C ≤ Finset.card (filter (Icc_wt 2 (n - 2)) C) + 2 := by
  -- div_Iic_Icc_Ici is a Lean3 decomposition lemma not yet ported to Lean4
  sorry
lemma optimal_of_div_wt
  {n : Nat} {C : Finset (List.Vector B n)} (HC : is_DelCode C)
  (H : ∀ C' ⊆ filter (@Icc_wt n 2 (n - 2)) univ,
       is_DelCode C' → Finset.card C' + 2 ≤ Finset.card C) :
  is_optimal C HC := by
  intro C' hC'
  apply le_trans (card_le_filter_Icc hC')
  have hle := H (filter (Icc_wt 2 (n - 2)) C')
    (Finset.filter_subset_filter _ (subset_univ _))
    (DelCode_filter _ hC')
  omega
namespace List

open List

def mkIO (n k : Nat)  : List B :=
  List.replicate k I ++ List.replicate (n - k) O

lemma length_IO (n k : Nat) (Hnk : k ≤ n) :
  List.length (mkIO n k) = n :=
by {
  unfold mkIO
  rw [List.length_append, List.length_replicate, List.length_replicate]
  omega
}
lemma length_IO' (n k : Nat) :
  List.length (mkIO n k) = k + (n - k) :=
by {
  unfold mkIO
  rw [List.length_append, List.length_replicate, List.length_replicate]
}
lemma num_Os_IO (n k : Nat) :
  List.num_Is (mkIO n k) = k :=
by {
  unfold mkIO
  rw [List.num_Is_append, List.num_Is_replicate_I, List.num_Is_replicate_O]
  exact Nat.add_zero k
}
lemma num_Is_IO (n k : Nat) :
  List.num_Is (mkIO n k) = k :=
by {
  unfold mkIO
  rw [List.num_Is_append, List.num_Is_replicate_I, List.num_Is_replicate_O]
  exact Nat.add_zero k
}
def mkIOIO (n k : Nat) : List B :=
  List.replicate k I ++ O::I::List.replicate (n - k - 2) O

lemma length_IOIO (n k : Nat) (Hk : k + 2 ≤ n) :
    List.length (mkIOIO n k) = n :=
by sorry
lemma num_Os_IOIO (n k : Nat) :
  List.num_Os (mkIOIO n k) = n - k - 2 + 1 :=
by sorry
lemma num_Is_IOIO (n k : Nat) :
  List.num_Is (mkIOIO n k) = k + 1 :=
by sorry
lemma length_IOIO' (n k : Nat) (Hk : n ≤ k + 2) :
    List.length (mkIOIO n k) = k + 2 :=
by sorry
lemma sDel_IOIO_O (n k : Nat) :
  List.sDel (mkIOIO n k) k = mkIO (n - 1) (k + 1) :=
by sorry
lemma sDel_IOIO_I (n k : Nat) (Hk : k + 2 ≤ n) :
  List.sDel (mkIOIO n k) (k + 1) = mkIO (n - 1) k :=
by sorry
def mkOI (n k : Nat)  : List B :=
  List.replicate k O ++ List.replicate (n - k) I

lemma length_OI (n k : Nat) (Hnk : k ≤ n) :
  List.length (mkOI n k) = n :=
by sorry
lemma length_OI' (n k : Nat) :
  List.length (mkOI n k) = k + (n - k) :=
by sorry
lemma num_Os_OI (n k : Nat) :
  List.num_Os (mkOI n k) = k :=
by sorry
lemma num_Is_OI (n k : Nat) :
  List.num_Is (mkOI n k) = n - k :=
by sorry
def mkOIOI (n k : Nat) : List B :=
  List.replicate k O ++ I::O::List.replicate (n - k - 2) I

lemma length_OIOI (n k : Nat) (Hk : k + 2 ≤ n):
    List.length (mkOIOI n k) = n :=
by sorry
lemma length_OIOI' (n k : Nat) (Hk : n ≤ k + 2) :
    List.length (mkOIOI n k) = k + 2 :=
by sorry
lemma num_Os_OIOI (n k : Nat) :
  List.num_Os (mkOIOI n k) = k + 1 :=
by sorry
lemma num_Is_OIOI (n k : Nat) :
  List.num_Is (mkOIOI n k) = n - k - 2 + 1 :=
by sorry
lemma sDel_OIOI_I (n k : Nat) :
  List.sDel (mkOIOI n k) k = mkOI (n - 1) (k + 1) :=
by sorry
lemma sDel_OIOI_O (n k : Nat)  (Hk : k + 2 ≤ n) :
  List.sDel (mkOIOI n k) (k + 1) = mkOI (n - 1) k :=
by sorry
lemma OI_succ_ne_OIOI (n k : Nat) :
  mkOI n (k + 1) ≠ mkOIOI n k :=
by sorry
lemma OI_ne_OIOI (n k₁ k₂ : Nat) :
  mkOI n k₁ ≠ mkOIOI n k₂ :=
by sorry
lemma OI_ne_IOIO (n k₁ k₂ : Nat) (H : 3 ≤ n) :
  mkOI n k₁ ≠ mkIOIO n k₂ :=
by sorry
lemma IO_succ_ne_IOIO (n k : Nat) :
  mkIO n (k + 1) ≠ mkIOIO n k :=
by sorry
lemma IO_ne_IOIO (n k₁ k₂ : Nat) :
  mkIO n k₁ ≠ mkIOIO n k₂ :=
by sorry
lemma IO_ne_OIOI (n k₁ k₂ : Nat) (H : 3 ≤ n) :
  mkIO n k₁ ≠ mkOIOI n k₂ :=
by sorry
end List

namespace List.Vector

open List.Vector

def mkIO (n k : Nat) (Hk : k ≤ n) : List.Vector B n :=
  ⟨List.mkIO n k, List.length_IO n k Hk⟩

lemma wt_IO (n k : Nat) (Hk : k ≤ n) :
  wt (mkIO n k Hk) = k :=
by sorry
def mkIOIO (n k : Nat) (Hkn : k + 2 ≤ n) : List.Vector B n :=
  ⟨List.mkIOIO n k, List.length_IOIO n k Hkn⟩

lemma length_IOIO_le (n k : Nat) (Hnk : k + 2 ≤ n) :
  2 ≤ List.length (List.mkIOIO n k) :=
by sorry
lemma wt_IOIO (n k : Nat) (Hkn : k + 2 ≤ n) :
  wt (mkIOIO n k Hkn) = k + 1 :=
by sorry
lemma wt_IOIO_le
  (k : Nat) (Hnk : k + 2 ≤ n) (Hk : k < 1) :
  wt (mkIOIO n k Hnk) ≤ 1 :=
by sorry
lemma le_wt_IOIO
  (k : Nat) (Hnk : k + 2 ≤ n) (Hk : n - 3 < k) :
  n - 1 ≤ wt (mkIOIO n k Hnk) :=
by sorry
lemma sDel_IOIO_O (n k : Nat) (Hkn : k + 2 ≤ n) :
  List.Vector.sDel (List.Vector.mkIOIO n k Hkn) k
  = List.Vector.mkIO (n - 1) (k + 1) (Nat.le_sub_of_add_le Hkn) :=
by sorry
lemma sDel_IOIO_I (n k : Nat) (Hkn : k + 2 ≤ n) :
  List.Vector.sDel (List.Vector.mkIOIO n k Hkn) (k + 1)
  = List.Vector.mkIO (n - 1) k (le_of_succ_le (Nat.le_sub_of_add_le Hkn)) :=
by sorry
lemma dS_IO_subset (n k : Nat) (Hkn : k + 2 ≤ n) :
  dS (List.Vector.mkIO n (k + 1) (le_trans (le_succ _) Hkn)) ⊆ dS (List.Vector.mkIOIO n k Hkn) :=
by sorry
def mkOI (n k : Nat) (Hk : k ≤ n) : List.Vector B n :=
  ⟨List.mkOI n k, List.length_OI n k Hk⟩

lemma wt_OI (n k : Nat) (Hk : k ≤ n) :
  wt (mkOI n k Hk) = n - k :=
by sorry
def mkOIOI (n k : Nat) (Hkn : k + 2 ≤ n) : List.Vector B n :=
  ⟨List.mkOIOI n k, List.length_OIOI n k Hkn⟩

lemma length_OIOI_le (n k : Nat) (Hnk : k + 2 ≤ n) :
  2 ≤ List.length (List.mkOIOI n k) :=
by sorry
lemma wt_OIOI (n k : Nat) (Hkn : k + 2 ≤ n) :
  wt (mkOIOI n k Hkn) = n - k - 1 :=
by sorry
lemma le_wt_OIOI
  (k : Nat) (Hnk : k + 2 ≤ n) (Hk : k < 1) :
  n - 1 ≤ wt (mkOIOI n k Hnk) :=
by sorry
lemma wt_OIOI_le
  (k : Nat) (Hnk : k + 2 ≤ n) (Hk : n - 3 < k) :
  wt (mkOIOI n k Hnk) ≤ 1 :=
by sorry
lemma sDel_OIOI_I (n k : Nat) (Hkn : k + 2 ≤ n) :
  List.Vector.sDel (List.Vector.mkOIOI n k Hkn) k
  = List.Vector.mkOI (n - 1) (k + 1) (Nat.le_sub_of_add_le Hkn) :=
by sorry
lemma sDel_OIOI_O (n k : Nat) (Hkn : k + 2 ≤ n) :
  List.Vector.sDel (List.Vector.mkOIOI n k Hkn) (k + 1)
  = List.Vector.mkOI (n - 1) k (le_of_succ_le (Nat.le_sub_of_add_le Hkn)) :=
by sorry
lemma dS_OI_subset (n k : Nat) (Hkn : k + 2 ≤ n) :
  dS (List.Vector.mkOI n (k + 1) (le_trans (le_succ _) Hkn)) ⊆ dS (List.Vector.mkOIOI n k Hkn) :=
by sorry
lemma OI_ne_OIOI (n k₁ k₂ : Nat) (Hk₁ : k₁ ≤ n) (Hk₂ : k₂ + 2 ≤ n):
  List.Vector.mkOI n k₁ Hk₁ ≠ List.Vector.mkOIOI n k₂ Hk₂ :=
by sorry
lemma OI_ne_IOIO (n k₁ k₂ : Nat)
  (H : 3 ≤ n) (Hk₁ : k₁ ≤ n) (Hk₂ : k₂ + 2 ≤ n) :
  List.Vector.mkOI n k₁ Hk₁ ≠ List.Vector.mkIOIO n k₂ Hk₂ :=
by sorry
lemma IO_ne_IOIO (n k₁ k₂ : Nat) (Hk₁ : k₁ ≤ n) (Hk₂ : k₂ + 2 ≤ n):
  List.Vector.mkIO n k₁ Hk₁ ≠ List.Vector.mkIOIO n k₂ Hk₂ :=
by sorry
lemma IO_ne_OIOI (n k₁ k₂ : Nat)
  (H : 3 ≤ n) (Hk₁ : k₁ ≤ n) (Hk₂ : k₂ + 2 ≤ n) :
  List.Vector.mkIO n k₁ Hk₁ ≠ List.Vector.mkOIOI n k₂ Hk₂ :=
by sorry
lemma flip_OIOI (n k : Nat) (Hkn : k + 2 ≤ n) :
  B.Vector.flip (List.Vector.mkOIOI n k Hkn) = List.Vector.mkIOIO n k Hkn :=
by sorry
lemma flip_IOIO (n k : Nat) (Hkn : k + 2 ≤ n) :
  B.Vector.flip (List.Vector.mkIOIO n k Hkn) = List.Vector.mkOIOI n k Hkn :=
by sorry
end List.Vector

namespace Finset

open Finset

noncomputable def insert_repO (C : Finset (List.Vector B n)) :=
  insert (List.Vector.replicate n O ) (filter (Ici_wt 2) C)

lemma repO_not_mem (C : Finset (List.Vector B n)):
  List.Vector.replicate n O ∉ filter (Ici_wt 2) C :=
by sorry
lemma DelCode_insert_repO
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) :
  is_DelCode (insert_repO C) :=
by sorry
noncomputable def insert_repI (C : Finset (List.Vector B n)) :=
  insert (List.Vector.replicate n I ) (filter (Iic_wt (n - 2)) C)

lemma repI_not_mem (Hn : 2 ≤ n) (C : Finset (List.Vector B n)):
  List.Vector.replicate n I ∉ filter (Iic_wt (n - 2)) C :=
by sorry
lemma DelCode_insert_repI (Hn : 2 ≤ n)
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) :
  is_DelCode (insert_repI C) :=
by sorry
lemma DC_insert_repI_repO (Hn : 2 ≤ n)
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) :
  is_DelCode (insert_repI (insert_repO C)) :=
by sorry
lemma card_insert_repI_repO (Hn : 2 ≤ n)
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) :
  Finset.card (insert_repI (insert_repO C))
  = Finset.card (filter (Icc_wt 2 (n - 2)) C) + 2 :=
by sorry
lemma le_card_insert_repI_repO (Hn : 2 ≤ n)
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) :
  Finset.card C ≤ Finset.card (insert_repI (insert_repO C)) :=
by sorry
noncomputable def W22 (n : Nat) : Finset (List.Vector B n) :=
  filter (@Icc_wt n 2 (n - 2)) univ

lemma mem_W22 {n : Nat} (X : List.Vector B n) :
  X ∈ W22 n ↔ Icc_wt 2 (n - 2) X :=
by sorry
lemma not_mem_W22_of_le
  {n : Nat} (X : List.Vector B n) (H : wt X ≤ 1):
  X ∉ W22 n :=
by sorry
lemma not_mem_W22_of_ge
  {n : Nat} (Hn : 2 ≤ n) (X : List.Vector B n) (H : n - 1 ≤ wt X):
  X ∉ W22 n :=
by sorry
lemma W22_of_le_2 {n : Nat} (Hn : n ≤ 2) :
  W22 n = ∅ :=
by sorry
lemma flip_W22 {n : Nat} (Hn : 2 ≤ n) :
  Finset.image B.Vector.flip (W22 n) = W22 n :=
by sorry
lemma filter_Icc_wt
  (C : Finset (List.Vector B n)) (HC : C ⊆ W22 n) :
  filter (Icc_wt 2 (n - 2)) C = C :=
by sorry
lemma card_DCs_sub_W22_le (Hn : 2 ≤ n)
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) (HC' : is_optimal C HC) :
  is_card_DCs_sub_le (W22 n) (Finset.card C - 2) :=
by sorry
lemma IO_mem_W22 (Hn : 3 ≤ n) (k : Fin (n - 1)) (Hk : 1 ≤ k.1) (Hk' : k.1 ≤ n - 3) :
  List.Vector.mkIO n (k + 1)  (le_of_lt (succ_le_of_lt (Nat.add_lt_of_lt_sub k.2))) ∈ W22 n :=
by sorry
lemma IO_mem_W22' (Hn : 4 ≤ n) :
  List.Vector.mkIO n 2 (le_of_succ_le (le_of_succ_le Hn)) ∈ W22 n :=
by sorry
lemma OI_mem_W22 (Hn : 3 ≤ n) (k : Fin (n - 1)) (Hk : 1 ≤ k.1) (Hk' : k.1 ≤ n - 3) :
  List.Vector.mkOI n (k.1 + 1) (le_of_lt (succ_le_of_lt (Nat.add_lt_of_lt_sub k.2))) ∈ W22 n :=
by sorry
lemma optimal_of_W22
  {n : Nat} {C : Finset (List.Vector B n)} (HC : is_DelCode C)
  (H : ∀ C' ⊆ W22 n, is_DelCode C' → Finset.card C' + 2 ≤ Finset.card C) :
  is_optimal C HC :=
by sorry
lemma optimal_of_div_wt' (Hn : 4 ≤ n)
  {C : Finset (List.Vector B n)} (HC : is_DelCode C)
  (HC' : is_card_DCs_sub_le (W22 n) (Finset.card C - 2)) :
  is_optimal C HC :=
by sorry
lemma card_DCs_sub_le_of_optimal (Hn : 2 ≤ n)
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) (HC' : is_optimal C HC) :
  is_card_DCs_sub_le (W22 n) (Finset.card C - 2) :=
by sorry
lemma optimal_iff_W22 (Hn : 4 ≤ n)
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) :
  is_optimal C HC ↔ is_card_DCs_sub_le (W22 n) (Finset.card C - 2) :=
by sorry
def Repl_sub (n : Nat) (k : Fin (n - 1)) : Finset (List.Vector B n) :=
  { List.Vector.mkOIOI n k.1 (succ_le_of_lt (Nat.add_lt_of_lt_sub k.2)),
   List.Vector.mkIOIO n k.1 (succ_le_of_lt (Nat.add_lt_of_lt_sub k.2)) }

lemma flip_Repl_sub (n : Nat) (k : Fin (n - 1)) :
  Finset.image B.Vector.flip (Repl_sub n k) = Repl_sub n k :=
by sorry
def Repl (n : Nat) : Finset (List.Vector B n) :=
  Finset.biUnion (@univ (Fin (n - 1)) _) (Repl_sub n)

lemma mem_Repl (X : List.Vector B n) :
  X ∈ Repl n ↔ ∃ k : Fin (n - 1), X ∈ Repl_sub n k :=
by sorry
lemma mem_Repl'
  (X : List.Vector B n) (H : X ∈ Repl n) :
  ∃ k : Fin (n - 1),
  (X = List.Vector.mkOIOI n k.1 (succ_le_of_lt (Nat.add_lt_of_lt_sub k.2))
  ∨ X = List.Vector.mkIOIO n k.1 (succ_le_of_lt (Nat.add_lt_of_lt_sub k.2)) ) :=
by sorry
lemma mem_W22_inter_Repl (Hn : 2 ≤ n)
  (X : List.Vector B n) (H : X ∈ W22 n ∩ Repl n) :
  ∃ k : Fin (n - 1), (1 ≤ k.1) ∧ (k.1 ≤ n - 3) ∧
  (X = List.Vector.mkOIOI n k.1 (succ_le_of_lt (Nat.add_lt_of_lt_sub k.2))
  ∨ X = List.Vector.mkIOIO n k.1 (succ_le_of_lt (Nat.add_lt_of_lt_sub k.2)) ) :=
by sorry
lemma flip_Repl (n : Nat) :
  Finset.image B.Vector.flip (Repl n) = Repl n :=
by sorry
lemma OI_not_mem_replace (Hn : 3 ≤ n) (k : Fin (n - 1)) :
  List.Vector.mkOI n (k.1 + 1) (le_of_lt (succ_le_of_lt (Nat.add_lt_of_lt_sub k.2))) ∉ Repl n :=
by sorry
lemma IO_not_mem_replace (Hn : 3 ≤ n) (k : Fin (n - 1)) :
  List.Vector.mkIO n (k.1 + 1) (le_of_lt (succ_le_of_lt (Nat.add_lt_of_lt_sub k.2))) ∉ Repl n :=
by sorry
lemma OI_mem_sdiff_replace
  (Hn : 3 ≤ n) (k : Fin (n - 1)) (Hk : 1 ≤ k.1) (Hk' : k.1 ≤ n - 3) :
  List.Vector.mkOI n (k.1 + 1) (le_of_lt (succ_le_of_lt (Nat.add_lt_of_lt_sub k.2))) ∈ W22 n \ Repl n :=
by sorry
lemma IO_mem_sdiff_replace
  (Hn : 3 ≤ n) (k : Fin (n - 1)) (Hk : 1 ≤ k.1) (Hk' : k.1 ≤ n - 3) :
  List.Vector.mkIO n (k.1 + 1) (le_of_lt (succ_le_of_lt (Nat.add_lt_of_lt_sub k.2))) ∈ W22 n \ Repl n :=
by sorry
lemma exists_sdiff_Repl
  (Hn : 3 ≤ n) (X : List.Vector B n) (H : X ∈ W22 n ∩ Repl n) :
  ∃ X' ∈ W22 n \ Repl n, X' ≠ X ∧ dS X' ⊆ dS X :=
by sorry
lemma exists_sdiff_Repl'
  (X : List.Vector B n) (H : X ∈ W22 n ∩ Repl n) :
  ∃ X' ∈ W22 n \ Repl n, X' ≠ X ∧ dS X' ⊆ dS X :=
by sorry
lemma optimal_iff_sdiff_Repl (Hn : 3 ≤ n)
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) :
  is_optimal C HC ↔ is_optimal_sub (univ \ Repl n) C HC :=
by sorry
lemma Repl_of_le_one (Hn : n ≤ 1) : Repl n = ∅ :=
by sorry
lemma Repl_two : Repl 2 = {⟨[I, O], rfl⟩, ⟨[O, I], rfl⟩} := by sorry
lemma sdiff_Repl_two : univ \ Repl 2 = {⟨[I, I], rfl⟩, ⟨[O, O], rfl⟩} := by sorry

def II : List.Vector B 2 := ⟨[I, I], rfl⟩
lemma II_ne_IO : II ≠ ⟨[I, O], rfl⟩ := by sorry
lemma II_mem_sdiff : II ∈ univ \ Repl 2 := by sorry
lemma dS_II_subset_IO : dS II ⊆ dS ⟨[I, O], rfl⟩ := by sorry

def OO : List.Vector B 2 := ⟨[O, O], rfl⟩
lemma OO_ne_OI : OO ≠ ⟨[O, I], rfl⟩ := by sorry
lemma OO_mem_sdiff : OO ∈ univ \ Repl 2 := by sorry
lemma dS_OO_subset_OI : dS OO ⊆ dS ⟨[O, I], rfl⟩ := by sorry

lemma optimal_iff_sdiff_Repl'
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) :
  is_optimal C HC ↔ is_optimal_sub (univ \ Repl n) C HC :=
by sorry
lemma optimal_of_W22_sdiff_Repl
  {n : Nat} {C : Finset (List.Vector B n)} (HC : is_DelCode C)
  (H : ∀ C' ⊆ W22 n \ Repl n, is_DelCode C' → Finset.card C' + 2 ≤ Finset.card C) :
  is_optimal C HC :=
by sorry
lemma optimal_iff_W22_sdiff_Repl (Hn : 4 ≤ n)
  (C : Finset (List.Vector B n)) (HC : is_DelCode C) :
  is_optimal C HC ↔ is_card_DCs_sub_le (W22 n \ Repl n) (Finset.card C - 2) :=
by sorry
lemma flip_W22_sdiff_Repl (Hn : 2 ≤ n):
  Finset.image B.Vector.flip (W22 n \ Repl n) = W22 n \ Repl n :=
by sorry
end Finset

end B
