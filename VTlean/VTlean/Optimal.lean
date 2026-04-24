/- Copyright Manabu Hagiwara 2022, 2026 -/
import VTlean.DelCode

open Nat List.Vector Finset

variable {α : Type} [DecidableEq α] [Fintype α]
variable {n : Nat} (S S₁ S₂ C : Finset (List.Vector α n))

def is_optimal {n : Nat} (C : Finset (List.Vector α n)) (HC : is_DelCode C) : Prop :=
  ∀ C' : Finset (List.Vector α n), is_DelCode C' → Finset.card C' ≤ Finset.card C

def is_optimal' (C : Finset (List.Vector α n)) (HC : is_DelCode C) : Prop :=
  ∀ C' : Finset (List.Vector α n), is_DelCode' C' → Finset.card C' ≤ Finset.card C

noncomputable instance Decidableis_optimal (HC : is_DelCode C) :
  Decidable (is_optimal C HC) := by unfold is_optimal; infer_instance
noncomputable instance Decidableis_optimal' (HC : is_DelCode C) :
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

noncomputable instance Decidableis_optimal_sub (HC : is_DelCode C) :
  Decidable (is_optimal_sub S C HC) := by unfold is_optimal_sub; infer_instance
noncomputable instance Decidableis_optimal_sub' (HC : is_DelCode C) :
  Decidable (is_optimal_sub' S C HC) := by unfold is_optimal_sub'; infer_instance
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

noncomputable instance Decidableis_card_DCs_sub_le  (k : Nat) :
  Decidable (is_card_DCs_sub_le S k) := by unfold is_card_DCs_sub_le; infer_instance
def is_card_DCs_sub_le' (k : Nat) : Prop :=
  ∀ C' ⊆ S, is_DelCode' C' → Finset.card C' ≤ k

noncomputable instance Decidableis_card_DCs_sub_le'  (k : Nat) :
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
lemma exists_subset_card_le {α : Type} (s : Finset α) (k : Nat) (hk : k ≤ s.card) :
  ∃ s' ⊆ s, s'.card = k := Finset.exists_subset_card_eq hk

lemma card_DC_sub_le_of_succ_empty
  {n : Nat} (S : Finset (List.Vector α n)) (k : Nat) (Hk : DCs_sub_len S (k + 1) = ∅) :
  is_card_DCs_sub_le S k := by
  intro C hS hC
  cases Classical.em (Finset.card C ≤ k) with
  | inl hle =>
    exact hle
  | inr hnle =>
    rw [not_le] at hnle
    have hk : k + 1 ≤ Finset.card C := hnle
    rcases exists_subset_card_le C (k + 1) hk with ⟨C', hC'_sub, hC'_card⟩
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

lemma List.eq_replicate_O_of_num_Is_zero : ∀ (X : List B) (hx : List.num_Is X = 0), X = List.replicate X.length O
| [], _ => rfl
| O :: X', hx => by
  change O :: X' = O :: List.replicate X'.length O
  congr 1
  exact eq_replicate_O_of_num_Is_zero X' hx
| I :: X', hx => by
  change List.num_Is X' + 1 = 0 at hx
  contradiction

lemma list_sDel_of_wt_le : ∀ (X : List B) (hx : List.num_Is X ≤ 1),
  ∃ i, List.sDel X i = List.replicate (X.length - 1) O
| [], _ => ⟨0, rfl⟩
| O :: [], _ => ⟨0, rfl⟩
| O :: y :: Y', hx => by
  have hx' : List.num_Is (y :: Y') ≤ 1 := hx
  rcases list_sDel_of_wt_le (y :: Y') hx' with ⟨i, hi⟩
  use (i + 1)
  have H : y :: Y' ≠ [] := by intro h; contradiction
  rw [List.sDel_cons _ _ _ H]
  rw [hi]
  rfl
| I :: X', hx => by
  have hx' : List.num_Is X' = 0 := by
    change List.num_Is X' + 1 ≤ 1 at hx
    exact Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hx)
  use 0
  have H1 : List.sDel (I :: X') 0 = X' := List.sDel_zero _ _
  rw [H1]
  have H2 : X' = List.replicate X'.length O := List.eq_replicate_O_of_num_Is_zero X' hx'
  have H3 : (I :: X').length - 1 = X'.length := rfl
  rw [H3]
  exact H2

lemma vector_sDel_of_wt_le {n : Nat} (X : List.Vector B n) (HX : wt X ≤ 1) :
  ∃ i, List.Vector.sDel X i = List.Vector.replicate (n - 1) O := by
  have h : List.num_Is X.val ≤ 1 := HX
  rcases list_sDel_of_wt_le X.val h with ⟨i, hi⟩
  use i
  apply Subtype.ext
  change List.sDel X.val i = List.replicate (n - 1) O
  have Hn : X.val.length = n := X.property
  rw [Hn] at hi
  exact hi

lemma repO_mem_dS (X  : List.Vector B n) (HX : wt X ≤ 1) :
  List.Vector.replicate (n - 1) O ∈ List.Vector.dS X := by
  rcases vector_sDel_of_wt_le X HX with ⟨i, hi⟩
  rw [List.Vector.mem_dS]
  cases List.Vector.exists_sDel_le X i with
  | intro j hj =>
    use j
    constructor
    · exact hj.1
    · rw [← hj.2, hi]

lemma List.eq_replicate_I_of_num_Os_zero : ∀ (X : List B) (hx : List.num_Os X = 0), X = List.replicate X.length I
| [], _ => rfl
| I :: X', hx => by
  change I :: X' = I :: List.replicate X'.length I
  congr 1
  exact eq_replicate_I_of_num_Os_zero X' hx
| O :: X', hx => by
  change List.num_Os X' + 1 = 0 at hx
  contradiction

lemma list_sDel_of_le_wt : ∀ (X : List B) (hx : List.num_Os X ≤ 1),
  ∃ i, List.sDel X i = List.replicate (X.length - 1) I
| [], _ => ⟨0, rfl⟩
| I :: [], _ => ⟨0, rfl⟩
| I :: y :: Y', hx => by
  have hx' : List.num_Os (y :: Y') ≤ 1 := hx
  rcases list_sDel_of_le_wt (y :: Y') hx' with ⟨i, hi⟩
  use (i + 1)
  have H : y :: Y' ≠ [] := by intro h; contradiction
  rw [List.sDel_cons _ _ _ H]
  rw [hi]
  rfl
| O :: X', hx => by
  have hx' : List.num_Os X' = 0 := by
    change List.num_Os X' + 1 ≤ 1 at hx
    exact Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ hx)
  use 0
  have H1 : List.sDel (O :: X') 0 = X' := List.sDel_zero _ _
  rw [H1]
  have H2 : X' = List.replicate X'.length I := List.eq_replicate_I_of_num_Os_zero X' hx'
  have H3 : (O :: X').length - 1 = X'.length := rfl
  rw [H3]
  exact H2

lemma vector_sDel_of_le_wt {n : Nat} (X : List.Vector B n) (HX : n - 1 ≤ wt X) :
  ∃ i, List.Vector.sDel X i = List.Vector.replicate (n - 1) I := by
  have h1 := List.num_Os_add_num_Is_eq_length X.val
  have h2 : X.val.length = n := X.property
  rw [h2] at h1
  have h3 : List.num_Os X.val ≤ 1 := by
    cases n with
    | zero => 
      have hl : X.val.length = 0 := X.property
      have hnil : X.val = [] := List.eq_nil_of_length_eq_zero hl
      rw [hnil]
      exact Nat.zero_le 1
    | succ n' =>
      change n' ≤ wt X at HX
      have h4 : List.num_Os X.val + List.num_Is X.val = n' + 1 := h1
      apply Nat.le_of_add_le_add_right
      calc
        List.num_Os X.val + n' ≤ List.num_Os X.val + List.num_Is X.val := Nat.add_le_add_left HX _
        _ = n' + 1 := h4
        _ = 1 + n' := Nat.add_comm n' 1
  rcases list_sDel_of_le_wt X.val h3 with ⟨i, hi⟩
  use i
  apply Subtype.ext
  change List.sDel X.val i = List.replicate (n - 1) I
  have Hn : X.val.length = n := X.property
  rw [Hn] at hi
  exact hi

lemma repI_mem_dS (X  : List.Vector B n) (HX : n - 1 ≤ wt X) :
  List.Vector.replicate (n - 1) I ∈ List.Vector.dS X := by
  rcases vector_sDel_of_le_wt X HX with ⟨i, hi⟩
  rw [List.Vector.mem_dS]
  cases List.Vector.exists_sDel_le X i with
  | intro j hj =>
    use j
    constructor
    · exact hj.1
    · rw [← hj.2, hi]

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
      apply Finset.ne_empty_of_mem (a := List.Vector.replicate (n - 1) O)
      rw [mem_inter]
      constructor
      · apply repO_mem_dS
        rw [mem_filter] at hX
        exact hX.right
      · apply repO_mem_dS
        rw [mem_filter] at hY
        exact hY.right
    have h_absurd := H X ?_ Y ?_ hXY
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
      apply Finset.ne_empty_of_mem (a := List.Vector.replicate (n - 1) I)
      rw [mem_inter]
      constructor
      · apply repI_mem_dS
        rw [mem_filter] at hX
        exact hX.right
      · apply repI_mem_dS
        rw [mem_filter] at hY
        exact hY.right
    have h_absurd := HC X ?_ Y ?_ hXY
    · contradiction
    · rw [mem_filter] at hX; exact hX.left
    · rw [mem_filter] at hY; exact hY.left
lemma card_le_filter_Icc
  {C : Finset (List.Vector B n)} (HC : is_DelCode C):
  Finset.card C ≤ Finset.card (filter (Icc_wt 2 (n - 2)) C) + 2 := by
  have h_Iic : card (filter (Iic_wt 1) C) ≤ 1 := card_Iic_wt_le HC
  have h_Ici : card (filter (Ici_wt (n - 1)) C) ≤ 1 := card_Ici_wt_le HC
  have h_part1 : card (filter (Iic_wt 1) C) + card (filter (fun x => ¬ Iic_wt 1 x) C) = card C :=
    Finset.card_filter_add_card_filter_not (Iic_wt 1)
  have h_part2 : card (filter (Ici_wt (n - 1)) (filter (fun x => ¬ Iic_wt 1 x) C)) + card (filter (fun x => ¬ Ici_wt (n - 1) x) (filter (fun x => ¬ Iic_wt 1 x) C)) = card (filter (fun x => ¬ Iic_wt 1 x) C) :=
    Finset.card_filter_add_card_filter_not (Ici_wt (n - 1))
  have h_Ici_sub : filter (Ici_wt (n - 1)) (filter (fun x => ¬ Iic_wt 1 x) C) ⊆ filter (Ici_wt (n - 1)) C := by
    intro x hx
    rw [mem_filter] at hx ⊢
    exact ⟨(mem_filter.mp hx.1).1, hx.2⟩
  have h_Ici_card_le : card (filter (Ici_wt (n - 1)) (filter (fun x => ¬ Iic_wt 1 x) C)) ≤ 1 :=
    le_trans (Finset.card_le_card h_Ici_sub) h_Ici
  have h_eq_Icc : filter (fun x => ¬ Ici_wt (n - 1) x) (filter (fun x => ¬ Iic_wt 1 x) C) = filter (Icc_wt 2 (n - 2)) C := by
    apply Finset.ext
    intro x
    rw [mem_filter, mem_filter, mem_filter]
    apply Iff.intro
    · rintro ⟨⟨hC, hnIic⟩, hnIci⟩
      change ¬ wt x ≤ 1 at hnIic
      change ¬ n - 1 ≤ wt x at hnIci
      have h1 : 1 < wt x := Nat.lt_of_not_ge hnIic
      have h2 : wt x < n - 1 := Nat.lt_of_not_ge hnIci
      exact ⟨hC, ⟨Nat.succ_le_of_lt h1, Nat.le_sub_one_of_lt h2⟩⟩
    · rintro ⟨hC, h2, hn2⟩
      change 2 ≤ wt x at h2
      change wt x ≤ n - 2 at hn2
      constructor
      · constructor
        · exact hC
        · intro h
          change wt x ≤ 1 at h
          have h_absurd := Nat.lt_of_le_of_lt h h2
          exact Nat.lt_irrefl _ h_absurd
      · intro h
        change n - 1 ≤ wt x at h
        cases n with
        | zero => 
          have h0 : wt x = 0 := Nat.eq_zero_of_le_zero hn2
          rw [h0] at h h2
          exact Nat.not_lt_zero _ h2
        | succ n' =>
          cases n' with
          | zero =>
            change 1 - 1 ≤ wt x at h
            change wt x ≤ 1 - 2 at hn2
            have h0 : wt x = 0 := Nat.eq_zero_of_le_zero hn2
            rw [h0] at h2
            have hz : ¬ 2 ≤ 0 := by decide
            contradiction
          | succ n'' =>
            change n'' + 2 - 1 ≤ wt x at h
            change wt x ≤ n'' + 2 - 2 at hn2
            change n'' + 1 ≤ wt x at h
            change wt x ≤ n'' at hn2
            have h_absurd := Nat.lt_of_le_of_lt hn2 h
            exact Nat.lt_irrefl _ h_absurd
  rw [h_eq_Icc] at h_part2
  rw [← h_part1]
  rw [← h_part2]
  calc
    card (filter (Iic_wt 1) C) + (card (filter (Ici_wt (n - 1)) (filter (fun x => ¬Iic_wt 1 x) C)) + card (filter (Icc_wt 2 (n - 2)) C))
      ≤ 1 + (1 + card (filter (Icc_wt 2 (n - 2)) C)) := Nat.add_le_add h_Iic (Nat.add_le_add h_Ici_card_le (Nat.le_refl _))
    _ = card (filter (Icc_wt 2 (n - 2)) C) + 2 := by
      have H1 : 1 + (1 + card (filter (Icc_wt 2 (n - 2)) C)) = 1 + 1 + card (filter (Icc_wt 2 (n - 2)) C) := (Nat.add_assoc _ _ _).symm
      have H2 : 1 + 1 = 2 := rfl
      rw [H1, H2, Nat.add_comm]
lemma optimal_of_div_wt
  {n : Nat} {C : Finset (List.Vector B n)} (HC : is_DelCode C)
  (H : ∀ C' ⊆ filter (@Icc_wt n 2 (n - 2)) univ,
       is_DelCode C' → Finset.card C' + 2 ≤ Finset.card C) :
  is_optimal C HC := by
  intro C' hC'
  have hle := H (filter (Icc_wt 2 (n - 2)) C')
    (Finset.filter_subset_filter _ (subset_univ _))
    (DelCode_filter _ hC' _)
  exact le_trans (card_le_filter_Icc hC') hle
namespace List

open List

def mkIO (n k : Nat)  : List B :=
  List.replicate k I ++ List.replicate (n - k) O

lemma length_IO (n k : Nat) (Hnk : k ≤ n) :
  List.length (mkIO n k) = n :=
by {
  unfold mkIO
  rw [List.length_append, List.length_replicate, List.length_replicate]
  exact Nat.add_sub_cancel' Hnk
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
    List.length (mkIOIO n k) = n := by
  unfold mkIOIO
  rw [List.length_append, List.length_replicate, List.length_cons, List.length_cons, List.length_replicate]
  have h1 : n - k - 2 + 1 + 1 = n - k := by
    have H : n - k - 2 + 2 = n - k := Nat.sub_add_cancel (Nat.le_sub_of_add_le (Nat.add_comm 2 k ▸ Hk))
    exact H
  rw [h1]
  have h_k_le_n : k ≤ n := Nat.le_trans (Nat.le_add_right k 2) Hk
  exact Nat.add_sub_cancel' h_k_le_n
lemma num_Os_IOIO (n k : Nat) :
  List.num_Os (mkIOIO n k) = n - k - 2 + 1 := by
  unfold mkIOIO
  rw [List.num_Os_append, List.num_Os_replicate_I, Nat.zero_add]
  change List.num_Os (I :: List.replicate (n - k - 2) O) + 1 = _
  change List.num_Os (List.replicate (n - k - 2) O) + 1 = _
  rw [List.num_Os_replicate_O]
lemma num_Is_IOIO (n k : Nat) :
  List.num_Is (mkIOIO n k) = k + 1 := by
  unfold mkIOIO
  rw [List.num_Is_append, List.num_Is_replicate_I]
  change k + List.num_Is (I :: List.replicate (n - k - 2) O) = _
  change k + (List.num_Is (List.replicate (n - k - 2) O) + 1) = _
  rw [List.num_Is_replicate_O, Nat.zero_add]
lemma length_IOIO' (n k : Nat) (Hk : n ≤ k + 2) :
    List.length (mkIOIO n k) = k + 2 := by
  unfold mkIOIO
  rw [List.length_append, List.length_replicate, List.length_cons, List.length_cons, List.length_replicate]
  have h1 : n - k - 2 = 0 := by
    rw [Nat.sub_sub]
    exact Nat.sub_eq_zero_of_le Hk
  rw [h1]
lemma replicate_append_singleton {α : Type} (n : Nat) (a : α) :
  List.replicate n a ++ [a] = List.replicate (n + 1) a := by
  induction n with
  | zero => rfl
  | succ n' ih =>
    change a :: (List.replicate n' a ++ [a]) = a :: List.replicate (n' + 1) a
    rw [ih]

lemma sDel_IOIO_O (n k : Nat) :
  List.sDel (mkIOIO n k) k = mkIO (n - 1) (k + 1) := by
  unfold mkIOIO mkIO
  have h_len : List.length (List.replicate k I) = k := by rw [List.length_replicate]
  have h_ge : List.length (List.replicate k I) ≤ k := by rw [h_len]
  have h_ne : O :: I :: List.replicate (n - k - 2) O ≠ [] := by intro h; contradiction
  have H_rw := List.sDel_append_of_ge (List.replicate k I) (O :: I :: List.replicate (n - k - 2) O) k h_ge h_ne
  rw [H_rw]
  have h_sub : k - List.length (List.replicate k I) = 0 := by rw [h_len, Nat.sub_self]
  rw [h_sub]
  have h_sDel_0 : List.sDel (O :: I :: List.replicate (n - k - 2) O) 0 = I :: List.replicate (n - k - 2) O := by
    rw [List.sDel_zero]
  rw [h_sDel_0]
  have h_assoc : List.replicate k I ++ I :: List.replicate (n - k - 2) O = (List.replicate k I ++ [I]) ++ List.replicate (n - k - 2) O := by
    change List.replicate k I ++ ([I] ++ List.replicate (n - k - 2) O) = _
    rw [List.append_assoc]
  rw [h_assoc]
  rw [replicate_append_singleton]
  have h_n_1 : n - 1 - (k + 1) = n - k - 2 := by
    have H1 : 1 + (k + 1) = k + 2 := by rw [Nat.add_comm 1 (k + 1)]
    rw [Nat.sub_sub n 1 (k + 1)]
    rw [H1]
    exact (Nat.sub_sub n k 2).symm
  rw [h_n_1]

lemma sDel_IOIO_I (n k : Nat) (Hk : k + 2 ≤ n) :
  List.sDel (mkIOIO n k) (k + 1) = mkIO (n - 1) k := by
  unfold mkIOIO mkIO
  have h_len : List.length (List.replicate k I) = k := by rw [List.length_replicate]
  have h_ge : List.length (List.replicate k I) ≤ k + 1 := by rw [h_len]; exact Nat.le_succ _
  have h_ne : O :: I :: List.replicate (n - k - 2) O ≠ [] := by intro h; contradiction
  have H_rw := List.sDel_append_of_ge (List.replicate k I) (O :: I :: List.replicate (n - k - 2) O) (k + 1) h_ge h_ne
  rw [H_rw]
  have h_sub : k + 1 - List.length (List.replicate k I) = 1 := by rw [h_len, Nat.add_sub_cancel_left]
  rw [h_sub]
  have h_sDel_1 : List.sDel (O :: I :: List.replicate (n - k - 2) O) 1 = O :: List.replicate (n - k - 2) O := by
    change List.sDel (O :: (I :: List.replicate (n - k - 2) O)) (0 + 1) = _
    rw [List.sDel_cons]
    · rw [List.sDel_zero]
    · intro h; contradiction
  rw [h_sDel_1]
  have h_replicate_O : O :: List.replicate (n - k - 2) O = List.replicate (n - 1 - k) O := by
    have h_eq : n - k - 2 + 1 = n - 1 - k := by
      have H2 : 2 ≤ n - k := Nat.le_sub_of_add_le (Nat.add_comm 2 k ▸ Hk)
      have H3 : n - k - 2 + 1 = n - k - 1 := by
        have H4 : n - k = n - k - 2 + 2 := (Nat.sub_add_cancel H2).symm
        rw [H4]
        change n - k - 2 + 1 = n - k - 2 + 1 + 1 - 1
        rw [Nat.add_sub_cancel]
      rw [H3]
      exact Nat.sub_right_comm n k 1
    have h_rep_succ : O :: List.replicate (n - k - 2) O = List.replicate (n - k - 2 + 1) O := rfl
    rw [h_rep_succ, h_eq]
  rw [h_replicate_O]
def mkOI (n k : Nat)  : List B :=
  List.replicate k O ++ List.replicate (n - k) I

lemma length_OI (n k : Nat) (Hnk : k ≤ n) :
  List.length (mkOI n k) = n := by
  unfold mkOI
  rw [List.length_append, List.length_replicate, List.length_replicate]
  exact Nat.add_sub_cancel' Hnk
lemma length_OI' (n k : Nat) :
  List.length (mkOI n k) = k + (n - k) := by
  unfold mkOI
  rw [List.length_append, List.length_replicate, List.length_replicate]
lemma num_Os_OI (n k : Nat) :
  List.num_Os (mkOI n k) = k := by
  unfold mkOI
  rw [List.num_Os_append, List.num_Os_replicate_O, List.num_Os_replicate_I, Nat.add_zero]
lemma num_Is_OI (n k : Nat) :
  List.num_Is (mkOI n k) = n - k := by
  unfold mkOI
  rw [List.num_Is_append, List.num_Is_replicate_O, List.num_Is_replicate_I, Nat.zero_add]
def mkOIOI (n k : Nat) : List B :=
  List.replicate k O ++ I::O::List.replicate (n - k - 2) I

lemma length_OIOI (n k : Nat) (Hk : k + 2 ≤ n):
    List.length (mkOIOI n k) = n := by
  unfold mkOIOI
  rw [List.length_append, List.length_replicate, List.length_cons, List.length_cons, List.length_replicate]
  have h1 : n - k - 2 + 1 + 1 = n - k := by
    have H : n - k - 2 + 2 = n - k := Nat.sub_add_cancel (Nat.le_sub_of_add_le (Nat.add_comm 2 k ▸ Hk))
    exact H
  rw [h1]
  have h_k_le_n : k ≤ n := Nat.le_trans (Nat.le_add_right k 2) Hk
  exact Nat.add_sub_cancel' h_k_le_n
lemma length_OIOI' (n k : Nat) (Hk : n ≤ k + 2) :
    List.length (mkOIOI n k) = k + 2 := by
  unfold mkOIOI
  rw [List.length_append, List.length_replicate, List.length_cons, List.length_cons, List.length_replicate]
  have h1 : n - k - 2 = 0 := by
    rw [Nat.sub_sub]
    exact Nat.sub_eq_zero_of_le Hk
  rw [h1]
lemma num_Os_OIOI (n k : Nat) :
  List.num_Os (mkOIOI n k) = k + 1 := by
  unfold mkOIOI
  rw [List.num_Os_append, List.num_Os_replicate_O]
  change k + List.num_Os (O :: List.replicate (n - k - 2) I) = _
  change k + (List.num_Os (List.replicate (n - k - 2) I) + 1) = _
  rw [List.num_Os_replicate_I, Nat.zero_add]
lemma num_Is_OIOI (n k : Nat) :
  List.num_Is (mkOIOI n k) = n - k - 2 + 1 := by
  unfold mkOIOI
  rw [List.num_Is_append, List.num_Is_replicate_O, Nat.zero_add]
  change List.num_Is (O :: List.replicate (n - k - 2) I) + 1 = _
  change List.num_Is (List.replicate (n - k - 2) I) + 1 = _
  rw [List.num_Is_replicate_I]
lemma drop_replicate_append {α : Type} (k : Nat) (a : α) (L : List α) :
  List.drop k (List.replicate k a ++ L) = L := by
  induction k with
  | zero => rfl
  | succ k' ih => exact ih

lemma replicate_succ_append_eq_replicate_append_cons {α : Type} (k : Nat) (a : α) (L : List α) :
  List.replicate (k + 1) a ++ L = List.replicate k a ++ (a :: L) := by
  induction k with
  | zero => rfl
  | succ k' ih =>
    change a :: (List.replicate (k' + 1) a ++ L) = a :: (List.replicate k' a ++ (a :: L))
    rw [ih]

lemma sDel_OIOI_I (n k : Nat) :
  List.sDel (mkOIOI n k) k = mkOI (n - 1) (k + 1) := by
  unfold mkOIOI mkOI
  have h_len : List.length (List.replicate k O) = k := by rw [List.length_replicate]
  have h_ge : List.length (List.replicate k O) ≤ k := by rw [h_len]
  have h_ne : I :: O :: List.replicate (n - k - 2) I ≠ [] := by intro h; contradiction
  have H_rw := List.sDel_append_of_ge (List.replicate k O) (I :: O :: List.replicate (n - k - 2) I) k h_ge h_ne
  rw [H_rw]
  have h_sub : k - List.length (List.replicate k O) = 0 := by rw [h_len, Nat.sub_self]
  rw [h_sub]
  have h_sDel_0 : List.sDel (I :: O :: List.replicate (n - k - 2) I) 0 = O :: List.replicate (n - k - 2) I := by
    rw [List.sDel_zero]
  rw [h_sDel_0]
  have h_assoc : List.replicate k O ++ O :: List.replicate (n - k - 2) I = (List.replicate k O ++ [O]) ++ List.replicate (n - k - 2) I := by
    change List.replicate k O ++ ([O] ++ List.replicate (n - k - 2) I) = _
    rw [List.append_assoc]
  rw [h_assoc]
  rw [replicate_append_singleton]
  have h_n_1 : n - 1 - (k + 1) = n - k - 2 := by
    have H1 : 1 + (k + 1) = k + 2 := by rw [Nat.add_comm 1 (k + 1)]
    rw [Nat.sub_sub n 1 (k + 1)]
    rw [H1]
    exact (Nat.sub_sub n k 2).symm
  rw [h_n_1]
lemma sDel_OIOI_O (n k : Nat)  (Hk : k + 2 ≤ n) :
  List.sDel (mkOIOI n k) (k + 1) = mkOI (n - 1) k := by
  unfold mkOIOI mkOI
  have h_len : List.length (List.replicate k O) = k := by rw [List.length_replicate]
  have h_ge : List.length (List.replicate k O) ≤ k + 1 := by rw [h_len]; exact Nat.le_succ _
  have h_ne : I :: O :: List.replicate (n - k - 2) I ≠ [] := by intro h; contradiction
  have H_rw := List.sDel_append_of_ge (List.replicate k O) (I :: O :: List.replicate (n - k - 2) I) (k + 1) h_ge h_ne
  rw [H_rw]
  have h_sub : k + 1 - List.length (List.replicate k O) = 1 := by rw [h_len, Nat.add_sub_cancel_left]
  rw [h_sub]
  have h_sDel_1 : List.sDel (I :: O :: List.replicate (n - k - 2) I) 1 = I :: List.replicate (n - k - 2) I := by
    change List.sDel (I :: (O :: List.replicate (n - k - 2) I)) (0 + 1) = _
    rw [List.sDel_cons]
    · rw [List.sDel_zero]
    · intro h; contradiction
  rw [h_sDel_1]
  have h_replicate_O : I :: List.replicate (n - k - 2) I = List.replicate (n - 1 - k) I := by
    have h_eq : n - k - 2 + 1 = n - 1 - k := by
      have H2 : 2 ≤ n - k := Nat.le_sub_of_add_le (Nat.add_comm 2 k ▸ Hk)
      have H3 : n - k - 2 + 1 = n - k - 1 := by
        have H4 : n - k = n - k - 2 + 2 := (Nat.sub_add_cancel H2).symm
        rw [H4]
        change n - k - 2 + 1 = n - k - 2 + 1 + 1 - 1
        rw [Nat.add_sub_cancel]
      rw [H3]
      exact Nat.sub_right_comm n k 1
    have h_rep_succ : I :: List.replicate (n - k - 2) I = List.replicate (n - k - 2 + 1) I := rfl
    rw [h_rep_succ, h_eq]
  rw [h_replicate_O]
lemma OI_succ_ne_OIOI (n k : Nat) :
  mkOI n (k + 1) ≠ mkOIOI n k := by
  unfold mkOI mkOIOI
  intro h
  have h_drop : List.drop k (List.replicate (k + 1) O ++ List.replicate (n - (k + 1)) I) =
                List.drop k (List.replicate k O ++ I :: O :: List.replicate (n - k - 2) I) := by
    rw [h]
  rw [replicate_succ_append_eq_replicate_append_cons] at h_drop
  rw [drop_replicate_append] at h_drop
  rw [drop_replicate_append] at h_drop
  injection h_drop with h_head
  contradiction

lemma OI_ne_OIOI (n k₁ k₂ : Nat) :
  mkOI n k₁ ≠ mkOIOI n k₂ := by
  intro h
  by_cases hk : k₁ = k₂ + 1
  · subst hk
    exact OI_succ_ne_OIOI n k₂ h
  · have h_os : List.num_Os (mkOI n k₁) = List.num_Os (mkOIOI n k₂) := by rw [h]
    rw [num_Os_OI, num_Os_OIOI] at h_os
    contradiction
lemma drop_one_replicate_pos {α : Type} (k : Nat) (hk : 0 < k) (a : α) (L : List α) :
  List.drop 1 (List.replicate k a ++ L) = List.replicate (k - 1) a ++ L := by
  cases k with
  | zero => contradiction
  | succ k' =>
    change List.drop 1 (a :: (List.replicate k' a ++ L)) = _
    rw [List.drop]
    rfl

lemma head_replicate_pos {α : Type} (k : Nat) (hk : 0 < k) (a : α) (L : List α) :
  List.head? (List.replicate k a ++ L) = some a := by
  cases k with
  | zero => contradiction
  | succ k' => rfl

lemma head_replicate_pos_only {α : Type} (k : Nat) (hk : 0 < k) (a : α) :
  List.head? (List.replicate k a) = some a := by
  cases k with
  | zero => contradiction
  | succ k' => rfl



lemma OI_ne_IOIO (n k₁ k₂ : Nat) (H : 3 ≤ n) :
  mkOI n k₁ ≠ mkIOIO n k₂ := by
  intro h
  by_cases hk1 : k₁ = 0
  · subst hk1
    have h_drop : List.drop k₂ (mkOI n 0) = List.drop k₂ (mkIOIO n k₂) := by rw [h]
    unfold mkOI mkIOIO at h_drop
    change List.drop k₂ (List.replicate n I) = List.drop k₂ (List.replicate k₂ I ++ O :: I :: List.replicate (n - k₂ - 2) O) at h_drop
    rw [drop_replicate_append] at h_drop
    rw [List.drop_replicate] at h_drop
    have h_head := congrArg (@List.head? B) h_drop
    by_cases h_sub : n - k₂ = 0
    · rw [h_sub] at h_head
      change none = some O at h_head
      contradiction
    · have h_sub_pos : 0 < n - k₂ := Nat.pos_of_ne_zero h_sub
      rw [head_replicate_pos_only (n - k₂) h_sub_pos I] at h_head
      change some I = some O at h_head
      contradiction
  · have hk1_pos : 0 < k₁ := Nat.pos_of_ne_zero hk1
    by_cases hk2 : k₂ = 0
    · subst hk2
      have h_drop : List.drop 1 (mkOI n k₁) = List.drop 1 (mkIOIO n 0) := by rw [h]
      unfold mkOI mkIOIO at h_drop
      rw [drop_one_replicate_pos k₁ hk1_pos O (List.replicate (n - k₁) I)] at h_drop
      change List.replicate (k₁ - 1) O ++ List.replicate (n - k₁) I = I :: List.replicate (n - 2) O at h_drop
      by_cases hk1_eq_1 : k₁ - 1 = 0
      · have h_os : List.num_Os (List.replicate (k₁ - 1) O ++ List.replicate (n - k₁) I) =
                    List.num_Os (I :: List.replicate (n - 2) O) := by exact congrArg List.num_Os h_drop
        rw [hk1_eq_1] at h_os
        change List.num_Os (List.replicate (n - k₁) I) = List.num_Os (List.replicate (n - 2) O) at h_os
        rw [List.num_Os_replicate_I, List.num_Os_replicate_O] at h_os
        have h_n_2 : n - 2 = 0 := h_os.symm
        have h_n_le_2 : n ≤ 2 := Nat.le_of_sub_eq_zero h_n_2
        have h_contra : 3 ≤ 2 := Nat.le_trans H h_n_le_2
        contradiction
      · have hk1_sub_pos : 0 < k₁ - 1 := Nat.pos_of_ne_zero hk1_eq_1
        have h_head : List.head? (List.replicate (k₁ - 1) O ++ List.replicate (n - k₁) I) =
                      List.head? (I :: List.replicate (n - 2) O) := by exact congrArg List.head? h_drop
        rw [head_replicate_pos (k₁ - 1) hk1_sub_pos O (List.replicate (n - k₁) I)] at h_head
        change some O = some I at h_head
        contradiction
    · have hk2_pos : 0 < k₂ := Nat.pos_of_ne_zero hk2
      have h_head : List.head? (mkOI n k₁) = List.head? (mkIOIO n k₂) := by rw [h]
      unfold mkOI mkIOIO at h_head
      rw [head_replicate_pos k₁ hk1_pos O (List.replicate (n - k₁) I)] at h_head
      rw [head_replicate_pos k₂ hk2_pos I (O :: I :: List.replicate (n - k₂ - 2) O)] at h_head
      contradiction
lemma IO_succ_ne_IOIO (n k : Nat) :
  mkIO n (k + 1) ≠ mkIOIO n k := by
  unfold mkIO mkIOIO
  intro h
  have h_drop : List.drop k (List.replicate (k + 1) I ++ List.replicate (n - (k + 1)) O) =
                List.drop k (List.replicate k I ++ O :: I :: List.replicate (n - k - 2) O) := by
    rw [h]
  rw [replicate_succ_append_eq_replicate_append_cons] at h_drop
  rw [drop_replicate_append] at h_drop
  rw [drop_replicate_append] at h_drop
  injection h_drop with h_head
  contradiction

lemma IO_ne_IOIO (n k₁ k₂ : Nat) :
  mkIO n k₁ ≠ mkIOIO n k₂ := by
  intro h
  by_cases hk : k₁ = k₂ + 1
  · subst hk
    exact IO_succ_ne_IOIO n k₂ h
  · have h_is : List.num_Is (mkIO n k₁) = List.num_Is (mkIOIO n k₂) := by rw [h]
    rw [num_Is_IO, num_Is_IOIO] at h_is
    contradiction
lemma IO_ne_OIOI (n k₁ k₂ : Nat) (H : 3 ≤ n) :
  mkIO n k₁ ≠ mkOIOI n k₂ := by
  intro h
  by_cases hk1 : k₁ = 0
  · subst hk1
    have h_drop : List.drop k₂ (mkIO n 0) = List.drop k₂ (mkOIOI n k₂) := by rw [h]
    unfold mkIO mkOIOI at h_drop
    change List.drop k₂ (List.replicate n O) = List.drop k₂ (List.replicate k₂ O ++ I :: O :: List.replicate (n - k₂ - 2) I) at h_drop
    rw [drop_replicate_append] at h_drop
    rw [List.drop_replicate] at h_drop
    have h_head := congrArg (@List.head? B) h_drop
    by_cases h_sub : n - k₂ = 0
    · rw [h_sub] at h_head
      change none = some I at h_head
      contradiction
    · have h_sub_pos : 0 < n - k₂ := Nat.pos_of_ne_zero h_sub
      rw [head_replicate_pos_only (n - k₂) h_sub_pos O] at h_head
      change some O = some I at h_head
      contradiction
  · have hk1_pos : 0 < k₁ := Nat.pos_of_ne_zero hk1
    by_cases hk2 : k₂ = 0
    · subst hk2
      have h_drop : List.drop 1 (mkIO n k₁) = List.drop 1 (mkOIOI n 0) := by rw [h]
      unfold mkIO mkOIOI at h_drop
      rw [drop_one_replicate_pos k₁ hk1_pos I (List.replicate (n - k₁) O)] at h_drop
      change List.replicate (k₁ - 1) I ++ List.replicate (n - k₁) O = O :: List.replicate (n - 2) I at h_drop
      by_cases hk1_eq_1 : k₁ - 1 = 0
      · have h_is : List.num_Is (List.replicate (k₁ - 1) I ++ List.replicate (n - k₁) O) =
                    List.num_Is (O :: List.replicate (n - 2) I) := by exact congrArg List.num_Is h_drop
        rw [hk1_eq_1] at h_is
        change List.num_Is (List.replicate (n - k₁) O) = List.num_Is (List.replicate (n - 2) I) at h_is
        rw [List.num_Is_replicate_O, List.num_Is_replicate_I] at h_is
        have h_n_2 : n - 2 = 0 := h_is.symm
        have h_n_le_2 : n ≤ 2 := Nat.le_of_sub_eq_zero h_n_2
        have h_contra : 3 ≤ 2 := Nat.le_trans H h_n_le_2
        contradiction
      · have hk1_sub_pos : 0 < k₁ - 1 := Nat.pos_of_ne_zero hk1_eq_1
        have h_head : List.head? (List.replicate (k₁ - 1) I ++ List.replicate (n - k₁) O) =
                      List.head? (O :: List.replicate (n - 2) I) := by exact congrArg List.head? h_drop
        rw [head_replicate_pos (k₁ - 1) hk1_sub_pos I (List.replicate (n - k₁) O)] at h_head
        change some I = some O at h_head
        contradiction
    · have hk2_pos : 0 < k₂ := Nat.pos_of_ne_zero hk2
      have h_head : List.head? (mkIO n k₁) = List.head? (mkOIOI n k₂) := by rw [h]
      unfold mkIO mkOIOI at h_head
      rw [head_replicate_pos k₁ hk1_pos I (List.replicate (n - k₁) O)] at h_head
      rw [head_replicate_pos k₂ hk2_pos O (I :: O :: List.replicate (n - k₂ - 2) I)] at h_head
      contradiction
end List

namespace List.Vector

open List.Vector

def mkIO (n k : Nat) (Hk : k ≤ n) : List.Vector B n :=
  ⟨List.mkIO n k, List.length_IO n k Hk⟩

lemma wt_IO (n k : Nat) (Hk : k ≤ n) :
  wt (mkIO n k Hk) = k := by
  unfold wt mkIO
  exact List.num_Is_IO n k
def mkIOIO (n k : Nat) (Hkn : k + 2 ≤ n) : List.Vector B n :=
  ⟨List.mkIOIO n k, List.length_IOIO n k Hkn⟩

lemma length_IOIO_le (n k : Nat) (Hnk : k + 2 ≤ n) :
  2 ≤ List.length (List.mkIOIO n k) := by
  rw [List.length_IOIO n k Hnk]
  exact Nat.le_trans (Nat.le_add_left 2 k) Hnk
lemma wt_IOIO (n k : Nat) (Hkn : k + 2 ≤ n) :
  wt (mkIOIO n k Hkn) = k + 1 := by
  unfold wt mkIOIO
  exact List.num_Is_IOIO n k
lemma wt_IOIO_le
  (k : Nat) (Hnk : k + 2 ≤ n) (Hk : k < 1) :
  wt (mkIOIO n k Hnk) ≤ 1 := by
  rw [wt_IOIO n k Hnk]
  exact Hk
lemma le_wt_IOIO
  (k : Nat) (Hnk : k + 2 ≤ n) (Hk : n - 3 < k) :
  n - 1 ≤ wt (mkIOIO n k Hnk) := by
  rw [wt_IOIO n k Hnk]
  have hk_def : n - 3 + 1 ≤ k := Hk
  have hn3 : n - 3 + 1 = n - 2 := by
    have hn3_le : 3 ≤ n := by
      cases hn : n with
      | zero =>
        rw [hn] at Hnk Hk
        have h_k_zero : k = 0 := Nat.eq_zero_of_add_eq_zero_right (Nat.eq_zero_of_le_zero Hnk)
        rw [h_k_zero] at Hk
        contradiction
      | succ n' =>
        cases hn' : n' with
        | zero =>
          rw [hn, hn'] at Hnk Hk
          have h_k_zero : k = 0 := Nat.eq_zero_of_add_eq_zero_right (Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ Hnk))
          rw [h_k_zero] at Hk
          contradiction
        | succ n'' =>
          cases hn'' : n'' with
          | zero =>
            rw [hn, hn', hn''] at Hnk Hk
            have h_k_zero : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ Hnk))
            rw [h_k_zero] at Hk
            contradiction
          | succ n''' => exact Nat.le_add_left 3 n'''
    have H_sub : n = n - 3 + 3 := (Nat.sub_add_cancel hn3_le).symm
    nth_rw 2 [H_sub]
    change n - 3 + 1 = n - 3 + 1 + 2 - 2
    rw [Nat.add_sub_cancel]
  rw [hn3] at hk_def
  have hk1 : n - 2 ≤ k := hk_def
  have hk2 : k ≤ n - 2 := Nat.le_sub_of_add_le (Nat.add_comm 2 k ▸ Hnk)
  have heq : k = n - 2 := Nat.le_antisymm hk2 hk1
  have heq2 : k + 1 = n - 2 + 1 := by rw [heq]
  have hn2 : 2 ≤ n := Nat.le_trans (Nat.add_comm 2 k ▸ Nat.le_add_left 2 k) Hnk
  have H3 : n - 2 + 1 = n - 1 := by
    have H4 : n = n - 2 + 2 := (Nat.sub_add_cancel hn2).symm
    nth_rw 2 [H4]
    have H5 : n - 2 + 2 = n - 2 + 1 + 1 := by
      change n - 2 + 2 = n - 2 + (1 + 1)
      rw [← Nat.add_assoc]
    rw [H5, Nat.add_sub_cancel]
  rw [H3] at heq2
  exact Nat.le_of_eq heq2.symm
lemma sDel_IOIO_O (n k : Nat) (Hkn : k + 2 ≤ n) :
  List.Vector.sDel (List.Vector.mkIOIO n k Hkn) k
  = List.Vector.mkIO (n - 1) (k + 1) (Nat.le_sub_of_add_le Hkn) := by
  apply Subtype.ext
  exact List.sDel_IOIO_O n k

lemma sDel_IOIO_I (n k : Nat) (Hkn : k + 2 ≤ n) :
  List.Vector.sDel (List.Vector.mkIOIO n k Hkn) (k + 1)
  = List.Vector.mkIO (n - 1) k (le_of_succ_le (Nat.le_sub_of_add_le Hkn)) := by
  apply Subtype.ext
  exact List.sDel_IOIO_I n k Hkn
lemma dS_IO_subset (n k : Nat) (Hkn : k + 2 ≤ n) :
  dS (List.Vector.mkIO n (k + 1) (le_trans (le_succ _) Hkn)) ⊆ dS (List.Vector.mkIOIO n k Hkn) :=
by sorry
def mkOI (n k : Nat) (Hk : k ≤ n) : List.Vector B n :=
  ⟨List.mkOI n k, List.length_OI n k Hk⟩

lemma wt_OI (n k : Nat) (Hk : k ≤ n) :
  wt (mkOI n k Hk) = n - k := by
  unfold wt mkOI
  exact List.num_Is_OI n k
def mkOIOI (n k : Nat) (Hkn : k + 2 ≤ n) : List.Vector B n :=
  ⟨List.mkOIOI n k, List.length_OIOI n k Hkn⟩

lemma length_OIOI_le (n k : Nat) (Hnk : k + 2 ≤ n) :
  2 ≤ List.length (List.mkOIOI n k) := by
  rw [List.length_OIOI n k Hnk]
  exact Nat.le_trans (Nat.le_add_left 2 k) Hnk

lemma wt_OIOI (n k : Nat) (Hkn : k + 2 ≤ n) :
  wt (mkOIOI n k Hkn) = n - k - 1 := by
  have h1 : List.num_Is (List.mkOIOI n k) = n - k - 2 + 1 := List.num_Is_OIOI n k
  have h2 : n - k - 2 + 1 = n - k - 1 := by
    have h3 : 2 ≤ n - k := Nat.le_sub_of_add_le (Nat.add_comm 2 k ▸ Hkn)
    have h4 : n - k = n - k - 2 + 2 := (Nat.sub_add_cancel h3).symm
    nth_rw 2 [h4]
    change n - k - 2 + 1 = n - k - 2 + 1 + 1 - 1
    rw [Nat.add_sub_cancel]
  rw [h2] at h1
  exact h1

lemma le_wt_OIOI
  (k : Nat) (Hnk : k + 2 ≤ n) (Hk : k < 1) :
  n - 1 ≤ wt (mkOIOI n k Hnk) := by
  rw [wt_OIOI n k Hnk]
  have hk0 : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_lt_succ Hk)
  rw [hk0, Nat.sub_zero]

lemma wt_OIOI_le
  (k : Nat) (Hnk : k + 2 ≤ n) (Hk : n - 3 < k) :
  wt (mkOIOI n k Hnk) ≤ 1 := by
  rw [wt_OIOI n k Hnk]
  have hk_def : n - 3 + 1 ≤ k := Hk
  have hn3 : n - 3 + 1 = n - 2 := by
    have hn3_le : 3 ≤ n := by
      cases hn : n with
      | zero =>
        rw [hn] at Hnk Hk
        have h_k_zero : k = 0 := Nat.eq_zero_of_add_eq_zero_right (Nat.eq_zero_of_le_zero Hnk)
        rw [h_k_zero] at Hk
        contradiction
      | succ n' =>
        cases hn' : n' with
        | zero =>
          rw [hn, hn'] at Hnk Hk
          have h_k_zero : k = 0 := Nat.eq_zero_of_add_eq_zero_right (Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ Hnk))
          rw [h_k_zero] at Hk
          contradiction
        | succ n'' =>
          cases hn'' : n'' with
          | zero =>
            rw [hn, hn', hn''] at Hnk Hk
            have h_k_zero : k = 0 := Nat.eq_zero_of_le_zero (Nat.le_of_succ_le_succ (Nat.le_of_succ_le_succ Hnk))
            rw [h_k_zero] at Hk
            contradiction
          | succ n''' => exact Nat.le_add_left 3 n'''
    have H_sub : n = n - 3 + 3 := (Nat.sub_add_cancel hn3_le).symm
    nth_rw 2 [H_sub]
    change n - 3 + 1 = n - 3 + 1 + 2 - 2
    rw [Nat.add_sub_cancel]
  rw [hn3] at hk_def
  have hk1 : n - 2 ≤ k := hk_def
  have hk2 : k ≤ n - 2 := Nat.le_sub_of_add_le (Nat.add_comm 2 k ▸ Hnk)
  have heq : k = n - 2 := Nat.le_antisymm hk2 hk1
  rw [heq]
  have hn2 : 2 ≤ n := Nat.le_trans (Nat.add_comm 2 k ▸ Nat.le_add_left 2 k) Hnk
  have H3 : n - (n - 2) - 1 = 1 := by
    have H4 : n = n - 2 + 2 := (Nat.sub_add_cancel hn2).symm
    nth_rw 1 [H4]
    rw [Nat.add_sub_cancel_left]
  rw [H3]
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
