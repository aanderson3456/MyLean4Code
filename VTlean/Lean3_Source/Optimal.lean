import .DelCode 

open nat vector finset

variables {α : Type} [decidable_eq α] [fintype α]
variables {n : ℕ} (S S₁ S₂ C : finset (vector α n))

def is_optimal {n : ℕ} (C : finset (vector α n)) (HC : is_DelCode C) : Prop := 
  ∀ C' : finset (vector α n), is_DelCode C' → card C' ≤ card C 

def is_optimal' (C : finset (vector α n)) (HC : is_DelCode C) : Prop := 
  ∀ C' : finset (vector α n), is_DelCode' C' → card C' ≤ card C 

instance decidable_is_optimal (HC : is_DelCode C) : 
  decidable (is_optimal C HC) :=
by {unfold is_optimal, apply_instance}

instance decidable_is_optimal' (HC : is_DelCode C) : 
  decidable (is_optimal' C HC) :=
by {unfold is_optimal', apply_instance}

lemma optimal'_iff (HC : is_DelCode C) : 
  is_optimal' C HC ↔ is_optimal C HC :=
begin
unfold is_optimal', unfold is_optimal, apply iff.intro,
  {intros h C' hC', rw ← DelCode'_iff at hC', apply h C' hC'},
  {intros h C' hC', rw DelCode'_iff at hC', apply h C' hC'}
end

def is_optimal_sub (HC : is_DelCode C) : Prop :=
  ∀ C' ⊆ S, is_DelCode C' → card C' ≤ card C 

def is_optimal_sub' (HC : is_DelCode C) : Prop :=
  ∀ C' ⊆ S, is_DelCode' C' → card C' ≤ card C 

instance decidable_is_optimal_sub (HC : is_DelCode C) : 
  decidable (is_optimal_sub S C HC) :=
by {unfold is_optimal_sub, apply_instance}

instance decidable_is_optimal_sub' (HC : is_DelCode C) : 
  decidable (is_optimal_sub S C HC) :=
by {unfold is_optimal_sub, apply_instance}

lemma optimal_sub'_iff (HC : is_DelCode C) : 
  is_optimal_sub' S C HC ↔ is_optimal_sub S C HC :=
begin
unfold is_optimal_sub', unfold is_optimal_sub, apply iff.intro,
  {intros h C' hS hC', rw ← DelCode'_iff at hC', apply h C' hS hC'},
  {intros h C' hS hC', rw DelCode'_iff at hC', apply h C' hS hC'}
end

lemma is_optimal_sub_univ (HC : is_DelCode C) : 
  is_optimal_sub univ C HC ↔ is_optimal C HC :=
begin
unfold is_optimal_sub, unfold is_optimal,
apply iff.intro,
  {intros h C', apply h C' (subset_univ C')},
  {intros h C' hC', apply h}
end

lemma optimal_sub_of_supset
  (HS : S₁ ⊆ S₂) (HC : is_DelCode C) (HCS : is_optimal_sub S₂ C HC) :
  is_optimal_sub S₁ C HC :=
by {intros C' hS hC', apply HCS _ (subset.trans hS HS) hC'}

lemma optimal_sub_of_ex
  (HC : is_DelCode C) (HCS : is_optimal_sub S₁ C HC)
  (Hex : ∀ C₂ ∈ DCs_sub S₂, ∃ C₁ ∈ DCs_sub S₁, card C₁ = card C₂) :
  is_optimal_sub S₂ C HC :=
begin
intros S hSU hS, 
cases Hex S _ with C₁ HC₁, 
  {cases HC₁ with HC₁ HC₁C₂, rw ← HC₁C₂,
   rw mem_DCs_sub at HC₁, apply HCS C₁ HC₁.left HC₁.right},
  {rw mem_DCs_sub, apply and.intro hSU hS}
end

lemma exists_DelCode_erase
  (HC : C ∈ DCs_sub S) 
  (X : vector α n) (HX : ∃ X' ∈ S, X' ≠ X ∧ dS X' ⊆ dS X) :
  ∃ C' ∈ DCs_sub (erase S X), card C' = card C :=
begin
rw mem_DCs_sub at HC,  
cases HX with X' HX', cases HX' with HX' HXX', 
cases decidable.em (X ∈ C) with hXC hnXC,
  {apply exists.intro (replace C X X'), apply exists.intro,
    {rw mem_DCs_sub, apply and.intro,
      {unfold replace, rw insert_subset, apply and.intro,
        {rw mem_erase, apply and.intro,
          {apply HXX'.left},
          {apply HX'}},
        {apply erase_subset_erase, apply HC.left}},
      {apply DelCode_replace _ _ _ HC.right hXC HXX'.right}},
    {rw card_replace _ HC.right _ hXC X' HXX'.right}},
  {apply exists.intro C, apply exists.intro,
    {rw mem_DCs_sub, apply and.intro,
      {intros z hzC, rw mem_erase, apply and.intro,
        {assume h, rw h at hzC, contradiction},
        {apply HC.left hzC}},
    {apply HC.right}},
    {refl}}
end

lemma exists_DelCode_sdiff
  (HC : C ∈ DCs_sub S) 
  (X : finset (vector α n)) (HX : ∀ x ∈ X, ∃ x' ∈ S \ X, x' ≠ x ∧ dS x' ⊆ dS x) :
  ∃ C' ∈ DCs_sub (S \ X), card C' = card C :=
begin
revert S C, induction X using finset.induction with x X hx ihX,
  {intros S C HC HX, apply exists.intro C, apply exists.intro,
    {rw sdiff_empty, apply HC},
    {refl}},
  {intros S C HC HX, rw sdiff_insert', 
   cases exists_DelCode_erase S C HC x _ with C' hC',
    {cases hC' with hC' hCC', rw ← hCC', 
     rw ← sdiff_insert', rw sdiff_insert, apply ihX _ _ hC',
     intros y hy, cases HX y (mem_insert_of_mem hy) with y' hy', 
     cases hy' with hy' hyy', apply exists.intro y', apply exists.intro,
      {rw ← sdiff_insert, apply hy'},
      {apply hyy'}},
    {cases HX x (mem_insert_self x X) with x' hx', cases hx' with hx' hxx',
     apply exists.intro x', apply exists.intro,
      {rw mem_sdiff at hx', apply hx'.left},
      {apply hxx'}}}
end

lemma exists_DelCode_sdiff'
  (HC : C ∈ DCs_sub S) 
  (X : finset (vector α n)) (HX : ∀ x ∈ S ∩ X, ∃ x' ∈ S \ X, x' ≠ x ∧ dS x' ⊆ dS x) :
  ∃ C' ∈ DCs_sub (S \ X), card C' = card C :=
by {rw ← sdiff_inter, apply exists_DelCode_sdiff _ _ HC, rw sdiff_inter, apply HX}

lemma optimal_sub_erase_iff
  (C : finset (vector α n)) (HC : is_DelCode C) 
  (X : vector α n) (HX : ∃ X' ∈ S, X' ≠ X ∧ dS X' ⊆ dS X) :
  is_optimal_sub (erase S X) C HC ↔ is_optimal_sub S C HC :=
begin
apply iff.intro,
  {intro h, apply optimal_sub_of_ex,
    {apply h},
    {intros C₂ hC₂, apply exists_DelCode_erase _ _ hC₂ X HX}},
  {apply optimal_sub_of_supset, apply erase_subset},
end

lemma optimal_sub_sdiff_iff
  (HC : is_DelCode C) 
  (X : finset (vector α n)) (HX : ∀ x ∈ X, ∃ y ∈ S \ X, y ≠ x ∧ dS y ⊆ dS x) :
  is_optimal_sub (S \ X) C HC ↔ is_optimal_sub S C HC :=
begin
revert S, induction X using finset.induction with x X hx ihX,
  {intros S HX, rw sdiff_empty},
  {intros S HX, rw sdiff_insert, rw ihX,
    {rw optimal_sub_erase_iff,
     cases (HX x (mem_insert_self _ _)) with y hy, cases hy with hy hxy,
     apply exists.intro y, apply exists.intro _,
      {apply hxy},
      {rw mem_sdiff at hy, apply hy.left}},
    {intros x' hx', 
     cases (HX x' (mem_insert_of_mem hx')) with y hy, cases hy with hy hxy,
     apply exists.intro y, apply exists.intro _,
      {apply hxy},
      {rw sdiff_insert at hy, apply hy}}}
end

lemma optimal_sub_sdiff_iff'
  (HC : is_DelCode C) 
  (X : finset (vector α n)) (HX : ∀ x ∈ S ∩ X, ∃ y ∈ S \ X, y ≠ x ∧ dS y ⊆ dS x) :
  is_optimal_sub (S \ X) C HC ↔ is_optimal_sub S C HC :=
begin
rw ← sdiff_inter, rw optimal_sub_sdiff_iff,
intros x hx, cases HX x hx with y hy, cases hy with hy hxy,
apply exists.intro y, apply exists.intro, 
  {rw sdiff_inter, apply hy},
  {apply hxy}
end

def is_card_DCs_sub_le (k : ℕ) : Prop := 
  ∀ C' ⊆ S, is_DelCode C' → card C' ≤ k 

instance decidable_is_card_DCs_sub_le  (k : ℕ) : 
  decidable (is_card_DCs_sub_le S k) :=
by {unfold is_card_DCs_sub_le, apply_instance}

def is_card_DCs_sub_le' (k : ℕ) : Prop := 
  ∀ C' ⊆ S, is_DelCode' C' → card C' ≤ k 

instance decidable_is_card_DCs_sub_le'  (k : ℕ) : 
  decidable (is_card_DCs_sub_le' S k) :=
by {unfold is_card_DCs_sub_le', apply_instance}

lemma card_DCs_sub_le'_iff (k : ℕ) : 
  is_card_DCs_sub_le' S k ↔ is_card_DCs_sub_le S k :=
begin
unfold is_card_DCs_sub_le', 
unfold is_card_DCs_sub_le, apply iff.intro,
  {intros h C' hS hC', rw ← DelCode'_iff at hC', apply h C' hS hC'},
  {intros h C' hS hC', rw DelCode'_iff at hC', apply h C' hS hC'}
end

lemma is_card_DCs_sub_le_DC (HC : is_DelCode C) : 
  is_card_DCs_sub_le S (card C) ↔ is_optimal_sub S C HC :=
by trivial

lemma card_DCs_sub_le_of_supset
  {S₁ S₂ : finset (vector α n)} (HS : S₁ ⊆ S₂) 
  (k : ℕ) (HSk : is_card_DCs_sub_le S₂ k) :
  is_card_DCs_sub_le S₁ k :=
by {intros C hCS hC, apply HSk C (subset.trans hCS HS) hC}

lemma card_DCs_sub_le_of_ex
  {S₁ S₂ : finset (vector α n)} 
  (k : ℕ) (HSk : is_card_DCs_sub_le S₁ k)
  (Hex : ∀ C₂ ∈ DCs_sub S₂, ∃ C₁ ∈ DCs_sub S₁, card C₁ = card C₂) :
  is_card_DCs_sub_le S₂ k :=
begin
intros S hSU hS, 
cases Hex S _ with C₁ HC₁, 
  {cases HC₁ with HC₁ HC₁C₂, rw ← HC₁C₂,
   rw mem_DCs_sub at HC₁, apply HSk C₁ HC₁.left HC₁.right},
  {rw mem_DCs_sub, apply and.intro hSU hS}
end

lemma card_DCs_sub_le_erase_iff
  {n : ℕ} (S : finset (vector α n)) 
  (X : vector α n) (Hx : ∃ X' ∈ S, X' ≠ X ∧ dS X' ⊆ dS X) (k : ℕ) :
  is_card_DCs_sub_le (erase S X) k ↔ is_card_DCs_sub_le S k :=
begin
apply iff.intro,
  {intro h, apply card_DCs_sub_le_of_ex,
    {apply h},
    {intros C' hC', apply exists_DelCode_erase S C' hC' X Hx}},
  {apply card_DCs_sub_le_of_supset, apply erase_subset},
end

lemma card_DCs_sub_le_sdiff_iff
  (X : finset (vector α n)) (HX : ∀ x ∈ X, ∃ x' ∈ S \ X, x' ≠ x ∧ dS x' ⊆ dS x) (k : ℕ) :
  is_card_DCs_sub_le (S \ X) k ↔ is_card_DCs_sub_le S k :=
begin
revert S, induction X using finset.induction with x X hx ihX,
  {intros S HX, rw sdiff_empty},
  {intros S HX, rw sdiff_insert, rw ihX,
    {rw card_DCs_sub_le_erase_iff,
     cases (HX x (mem_insert_self _ _)) with y hy, cases hy with hy hxy,
     apply exists.intro y, apply exists.intro _,
      {apply hxy},
      {rw mem_sdiff at hy, apply hy.left}},
    {intros x' hx', 
     cases (HX x' (mem_insert_of_mem hx')) with y hy, cases hy with hy hxy,
     apply exists.intro y, apply exists.intro _,
      {apply hxy},
      {rw sdiff_insert at hy, apply hy}}}
end

lemma card_DCs_sub_le_sdiff_iff'
  (X : finset (vector α n)) 
  (HX : ∀ x ∈ S ∩ X, ∃ x' ∈ S \ X, x' ≠ x ∧ dS x' ⊆ dS x) (k : ℕ) :
  is_card_DCs_sub_le (S \ X) k ↔ is_card_DCs_sub_le S k :=
begin
rw ← sdiff_inter, rw card_DCs_sub_le_sdiff_iff,
intros x hx, cases HX x hx with x' hx', cases hx' with hx' hxx',
apply exists.intro x', apply exists.intro,
  {rw sdiff_inter, apply hx'},
  {apply hxx'}
end

lemma card_DC_sub_le_of_succ_empty
  {n : ℕ} (S : finset (vector α n)) (k : ℕ) (Hk : DCs_sub_len S (k + 1) = ∅) :
  is_card_DCs_sub_le S k :=
begin
intros C hS hC, cases decidable.em (card C ≤ k) with hle hnle,
  {apply hle},
  {rw not_le at hnle, rw lt_iff_add_one_le at hnle,
   cases exists_subset_card_le C (k + 1) hnle with C' hC',
   have h : C' ∈ DCs_sub_len S (k + 1),
    {rw mem_DCs_sub_len, apply and.intro,
      {apply subset.trans hC'.left hS},
      {apply and.intro,
        {apply hC'.right},
        {apply DelCode_subset _ _ hC hC'.left}}},
   apply absurd Hk, apply ne_empty_of_mem h}
end

namespace B

lemma repO_mem_dS (X  : vector B n) (HX : wt X ≤ 1) :
  repeat O (n - 1) ∈ dS X :=
begin
rw mem_dS, cases sDel_of_wt_le X HX with i hi,
apply exists.intro i, rw hi
end

lemma repI_mem_dS (X  : vector B n) (HX : n - 1 ≤ wt X) :
  repeat I (n - 1) ∈ dS X :=
begin
rw mem_dS, cases sDel_of_le_wt X HX with i hi,
apply exists.intro i, rw hi
end

lemma card_Iic_wt_le 
  {C : finset (vector B n)} (H : is_DelCode C):
  card (filter (Iic_wt 1) C) ≤ 1 :=
begin
cases decidable.em(card (filter (Iic_wt 1) C) ≤ 1) with hle hnle,
  {apply hle},
  {cases exists_distinct _ (lt_of_not_ge hnle) with X hX, 
   cases hX with Y hXY, cases hXY with hX hXY, cases hXY with hY hXY,
   have h : dS X ∩ dS Y ≠ ∅,
    {apply ne_empty_of_mem, rw mem_inter, apply and.intro,
      {apply repO_mem_dS, rw mem_filter at hX, apply hX.right},
      {apply repO_mem_dS, rw mem_filter at hY, apply hY.right}},
   apply absurd (H X Y _ _ hXY) h,
    {rw mem_filter at hX, apply hX.left},
    {rw mem_filter at hY, apply hY.left}}
end

lemma card_Ici_wt_le
  {C : finset (vector B n)} (HC : is_DelCode C):
  card (filter (Ici_wt (n - 1)) C) ≤ 1 :=
begin
cases decidable.em(card (filter (Ici_wt (n - 1)) C) ≤ 1) with hle hnle,
  {apply hle},
  {cases exists_distinct _ (lt_of_not_ge hnle) with X hX, 
   cases hX with Y hXY, cases hXY with hX hXY, cases hXY with hY hXY,
   have h : dS X ∩ dS Y ≠ ∅,
    {apply ne_empty_of_mem, rw mem_inter, apply and.intro,
      {apply repI_mem_dS, rw mem_filter at hX, apply hX.right},
      {apply repI_mem_dS, rw mem_filter at hY, apply hY.right}},
   apply absurd (HC X Y _ _ hXY) h,
    {rw mem_filter at hX, apply hX.left},
    {rw mem_filter at hY, apply hY.left}}
end

lemma card_le_filter_Icc
  {C : finset (vector B n)} (HC : is_DelCode C):
  card C ≤ card (filter (Icc_wt 2 (n - 2)) C) + 2 :=
begin
rw ← div_Iic_Icc_Ici 1 (n - 1) C,
apply le_trans,
  {apply card_union_le},
  {apply le_trans,
    {apply add_le_add_left (card_Ici_wt_le HC)},
    {apply succ_le_succ, apply le_trans,
      {apply card_union_le},
      {rw add_comm, apply add_le_add,
        {rw div_Iic_Icc_Ici 1 (n - 1), refl},
        {apply card_Iic_wt_le HC}}}}
end

lemma optimal_of_div_wt 
  {n : ℕ} {C : finset (vector B n)} (HC : is_DelCode C) 
  (H : ∀ C' ⊆ filter (@Icc_wt n 2 (n - 2)) univ, 
       is_DelCode C' → card C' + 2 ≤ card C) :
  is_optimal C HC :=
begin
intros C' hC', apply le_trans,
  {apply card_le_filter_Icc hC'},
  {apply le_trans _,
    {apply H (filter (Icc_wt 2 (n - 2)) C'),
      {apply filter_subset_filter, apply subset_univ},
      {apply DelCode_filter _ hC'}},
    {refl}}
end

namespace list 

open list 

def IO (n k : ℕ)  : list B :=
  repeat I k ++ repeat O (n - k)

lemma length_IO (n k : ℕ) (Hnk : k ≤ n) :
  length (IO n k) = n :=
begin
unfold IO, repeat {rw length_append}, repeat {rw length_repeat}, 
rw ← nat.add_sub_assoc Hnk, rw nat.add_sub_cancel_left
end

lemma length_IO' (n k : ℕ) :
  length (IO n k) = k + (n - k) :=
by {unfold IO, repeat {rw length_append}, repeat {rw length_repeat}}

lemma num_Os_IO (n k : ℕ) :
  num_Is (IO n k) = k :=
begin
unfold IO, rw num_Is_append, 
rw num_Is_repO, rw num_Is_repI, rw nat.add_zero
end

lemma num_Is_IO (n k : ℕ) :
  num_Is (IO n k) = k :=
begin
unfold IO, rw num_Is_append, 
rw num_Is_repI, rw num_Is_repO, rw nat.add_zero
end

lemma sDel_IO_of_lt (n k i : ℕ) (Hki : i + 1 ≤ k):
  sDel (IO n k) i = IO (n - 1) (k - 1) :=
begin
unfold IO, rw sDel_append_of_lt, 
  {rw list.sDel_repeat, 
   rw nat.sub_sub, rw add_comm, rw nat.sub_add_cancel,
   apply le_trans (le_add_left 1 i) Hki},
  {rw length_repeat, apply  Hki}
end

lemma sDel_IO_of_ge (n k i : ℕ) (Hkn : k + 1 ≤ n) (Hki : k ≤ i) :
  sDel (IO n k) i = IO (n - 1) k :=
begin
unfold IO, rw sDel_append_of_ge, 
  {rw list.sDel_repeat, repeat {rw nat.sub_sub}, rw add_comm},
  {rw length_repeat, apply Hki},
  {assume h, 
   have hl : length (list.repeat O (n - k)) = 0,
    {rw h, rw list.length},
   apply absurd hl, apply nat.ne_of_gt,
   rw length_repeat, apply lt_of_succ_le, 
   apply nat.le_sub_left_of_add_le Hkn}
end

def IOIO (n k : ℕ) : list B :=
  repeat I k ++ O::I::list.repeat O (n - k - 2)

lemma length_IOIO (n k : ℕ) (Hk : k + 2 ≤ n) :
    length (IOIO n k) = n :=
begin
unfold IOIO, rw length_append, unfold list.length, 
repeat {rw length_repeat},
calc 
k + (n - k - 2 + 1 + 1) = k + (n - k - 2 + 2) : rfl
... =  n - k - 2 + 2 + k : by rw add_comm 
... =  n - k - 2 + k + 2 : by rw add_right_comm
... =  n - k - 2 + (k + 2) : by rw add_assoc
... =  n - (k + 2) + (k + 2) : by rw nat.sub_sub
... =  n : by rw nat.sub_add_cancel Hk
end

lemma num_Os_IOIO (n k : ℕ) :
  num_Os (IOIO n k) = n - k - 2 + 1 :=
begin
unfold IOIO, rw num_Os_append, 
rw num_Os_repI, unfold num_Os, rw num_Os_repO, rw nat.zero_add
end

lemma num_Is_IOIO (n k : ℕ) :
  num_Is (IOIO n k) = k + 1 :=
begin
unfold IOIO, rw num_Is_append, 
rw num_Is_repI, unfold num_Is, rw num_Is_repO
end

lemma length_IOIO' (n k : ℕ) (Hk : n ≤ k + 2) :
    length (IOIO n k) = k + 2 :=
begin
unfold IOIO, rw @eq_zero_of_le_zero (n - k - 2),
  {rw length_append, unfold list.length, 
   repeat {rw length_repeat}},
  {rw nat.sub_sub, rw sub_eq_zero_of_le Hk}
end

lemma sDel_IOIO_O (n k : ℕ) :
  sDel (IOIO n k) k = IO (n - 1) (k + 1) :=
begin
unfold IOIO, rw sDel_append_of_ge, 
  {rw length_repeat, rw nat.sub_self, rw list.sDel_zero, 
   unfold IO, rw list.repeat_add, rw append_assoc, 
   repeat {rw nat.sub_sub}, rw add_comm 1, refl},
  {rw length_repeat},
  {apply cons_ne_nil}
end

lemma sDel_IOIO_I (n k : ℕ) (Hk : k + 2 ≤ n) :
  sDel (IOIO n k) (k + 1) = IO (n - 1) k :=
begin
unfold IOIO, rw sDel_append_of_ge, 
  {rw length_repeat, rw nat.add_sub_cancel_left, 
   rw list.sDel, rw list.sDel_zero, unfold IO, 
   have h : n - 1 - k = n - k - 2 + 1,
    {rw nat.sub_add_eq_add_sub,
      {rw succ_sub_succ, repeat {rw nat.sub_sub}, rw add_comm},
      {apply nat.le_sub_left_of_add_le Hk}},
   rw h, rw repeat_succ},
  {rw length_repeat, apply le_succ},
  {apply cons_ne_nil}
end

def OI (n k : ℕ)  : list B :=
  repeat O k ++ repeat I (n - k)

lemma length_OI (n k : ℕ) (Hnk : k ≤ n) :
  length (OI n k) = n :=
begin
unfold OI, repeat {rw length_append}, repeat {rw length_repeat}, 
rw ← nat.add_sub_assoc Hnk, rw nat.add_sub_cancel_left
end

lemma length_OI' (n k : ℕ) :
  length (OI n k) = k + (n - k) :=
by {unfold OI, repeat {rw length_append}, repeat {rw length_repeat}}


lemma num_Os_OI (n k : ℕ) :
  num_Os (OI n k) = k :=
begin
unfold OI, rw num_Os_append, 
rw num_Os_repO, rw num_Os_repI, rw nat.add_zero
end

lemma num_Is_OI (n k : ℕ) :
  num_Is (OI n k) = n - k :=
begin
unfold OI, rw num_Is_append, 
rw num_Is_repO, rw num_Is_repI, rw nat.zero_add
end

lemma sDel_OI_of_lt (n k i : ℕ) (Hki : i + 1 ≤ k):
  sDel (OI n k) i = OI (n - 1) (k - 1) :=
begin
unfold OI, rw sDel_append_of_lt, 
  {rw list.sDel_repeat, 
   rw nat.sub_sub, rw add_comm, rw nat.sub_add_cancel,
   apply le_trans (le_add_left 1 i) Hki},
  {rw length_repeat, apply  Hki}
end

lemma sDel_OI_of_ge (n k i : ℕ) (Hkn : k + 1 ≤ n) (Hki : k ≤ i) :
  sDel (OI n k) i = OI (n - 1) k :=
begin
unfold OI, rw sDel_append_of_ge, 
  {rw list.sDel_repeat, repeat {rw nat.sub_sub}, rw add_comm},
  {rw length_repeat, apply Hki},
  {assume h, 
   have hl : length (list.repeat I (n - k)) = 0,
    {rw h, rw list.length},
   apply absurd hl, apply nat.ne_of_gt,
   rw length_repeat, apply lt_of_succ_le, 
   apply nat.le_sub_left_of_add_le Hkn}
end

def OIOI (n k : ℕ) : list B :=
  repeat O k ++ I::O::list.repeat I (n - k - 2)

lemma length_OIOI (n k : ℕ) (Hk : k + 2 ≤ n):
    length (OIOI n k) = n :=
begin
unfold OIOI, rw length_append, unfold list.length, 
repeat {rw length_repeat},
calc 
k + (n - k - 2 + 1 + 1) = k + (n - k - 2 + 2) : rfl
... =  n - k - 2 + 2 + k : by rw add_comm 
... =  n - k - 2 + k + 2 : by rw add_right_comm
... =  n - k - 2 + (k + 2) : by rw add_assoc
... =  n - (k + 2) + (k + 2) : by rw nat.sub_sub
... =  n : by rw nat.sub_add_cancel Hk
end

lemma length_OIOI' (n k : ℕ) (Hk : n ≤ k + 2) :
    length (OIOI n k) = k + 2 :=
begin
unfold OIOI, rw @eq_zero_of_le_zero (n - k - 2),
  {rw length_append, unfold list.length, 
   repeat {rw length_repeat}},
  {rw nat.sub_sub, rw sub_eq_zero_of_le Hk}
end

lemma num_Os_OIOI (n k : ℕ) :
  num_Os (OIOI n k) = k + 1 :=
begin
unfold OIOI, rw num_Os_append, 
rw num_Os_repO, unfold num_Os, rw num_Os_repI
end

lemma num_Is_OIOI (n k : ℕ) :
  num_Is (OIOI n k) = n - k - 2 + 1 :=
begin
unfold OIOI, rw num_Is_append, 
rw num_Is_repO, unfold num_Is, rw num_Is_repI, rw nat.zero_add
end

lemma sDel_OIOI_I (n k : ℕ) :
  sDel (OIOI n k) k = OI (n - 1) (k + 1) :=
begin
unfold OIOI, rw sDel_append_of_ge, 
  {rw length_repeat, rw nat.sub_self, rw list.sDel_zero, 
   unfold OI, rw list.repeat_add, rw append_assoc, 
   repeat {rw nat.sub_sub}, rw add_comm 1, refl},
  {rw length_repeat},
  {apply cons_ne_nil}
end

lemma sDel_OIOI_O (n k : ℕ)  (Hk : k + 2 ≤ n) :
  sDel (OIOI n k) (k + 1) = OI (n - 1) k :=
begin
unfold OIOI, rw sDel_append_of_ge, 
  {rw length_repeat, rw nat.add_sub_cancel_left, 
   rw list.sDel, rw list.sDel_zero, unfold OI, 
   have h : n - 1 - k = n - k - 2 + 1,
    {rw nat.sub_add_eq_add_sub,
      {rw succ_sub_succ, repeat {rw nat.sub_sub}, rw add_comm},
      {apply nat.le_sub_left_of_add_le Hk}},
   rw h, rw repeat_succ},
  {rw length_repeat, apply le_succ},
  {apply cons_ne_nil}
end

lemma OI_succ_ne_OIOI (n k : ℕ) :
  OI n (k + 1) ≠ OIOI n k :=
begin
unfold OIOI, unfold OI, assume h, 
rw list.repeat_add at h, rw append_assoc at h, 
rw append_left_inj at h, 
have h' : O = I, from head_eq_of_cons_eq h,
apply absurd h' (B.O_ne_I)
end

lemma OI_ne_OIOI (n k₁ k₂ : ℕ) :
  OI n k₁ ≠ OIOI n k₂ :=
begin
assume h, 
have h' : num_Os (OI n k₁) = num_Os (OIOI n k₂), rw h,
rw num_Os_OI at h', rw num_Os_OIOI at h', rw h' at h, 
apply absurd h (OI_succ_ne_OIOI n k₂)
end

lemma OI_ne_IOIO (n k₁ k₂ : ℕ) (H : 3 ≤ n) :
  OI n k₁ ≠ IOIO n k₂ :=
begin
assume h, cases k₁,
  {have h' : num_Os (OI n 0) = num_Os (IOIO n k₂), rw h,
   rw num_Os_OI at h', rw num_Os_IOIO at h', 
   apply absurd h', apply nat.ne_of_lt, 
   apply lt_succ_of_le, apply nat.zero_le},
  {cases k₂, 
    {cases k₁,
      {have h' : num_Os (OI n 1) = num_Os (IOIO n 0), rw h,
       rw num_Os_OI at h', rw num_Os_IOIO at h', 
       apply absurd h', rw nat.sub_zero,
       apply nat.ne_of_lt, apply lt_succ_of_le, 
       apply nat.le_sub_left_of_add_le H},
      {unfold OI at h, unfold IOIO at h, unfold list.repeat at h, 
       rw nil_append at h, rw cons_append at h, rw cons_inj' at h,
       have h' : O = I, from head_eq_of_cons_eq h,
       apply absurd h' O_ne_I}},
    {unfold OI at h, unfold IOIO at h, 
     unfold list.repeat at h, rw cons_append at h, 
     have h' : O = I, from head_eq_of_cons_eq h,
     apply absurd h' O_ne_I}}
end

lemma IO_succ_ne_IOIO (n k : ℕ) :
  IO n (k + 1) ≠ IOIO n k :=
begin
unfold IOIO, unfold IO, assume h, 
rw list.repeat_add at h, rw append_assoc at h, 
rw append_left_inj at h, 
have h' : O = I, from (head_eq_of_cons_eq h).symm,
apply absurd h' (B.O_ne_I)
end

lemma IO_ne_IOIO (n k₁ k₂ : ℕ) :
  IO n k₁ ≠ IOIO n k₂ :=
begin
assume h, 
have h' : num_Is (IO n k₁) = num_Is (IOIO n k₂), rw h,
rw num_Is_IO at h', rw num_Is_IOIO at h', rw h' at h, 
apply absurd h (IO_succ_ne_IOIO n k₂)
end

lemma IO_ne_OIOI (n k₁ k₂ : ℕ) (H : 3 ≤ n) :
  IO n k₁ ≠ OIOI n k₂ :=
begin
assume h, cases k₁,
  {have h' : num_Is (IO n 0) = num_Is (OIOI n k₂), rw h,
   rw num_Is_IO at h', rw num_Is_OIOI at h', 
   apply absurd h', apply nat.ne_of_lt, 
   apply lt_succ_of_le, apply nat.zero_le},
  {cases k₂, 
    {cases k₁,
      {have h' : num_Is (IO n 1) = num_Is (OIOI n 0), rw h,
       rw num_Is_IO at h', rw num_Is_OIOI at h', 
       apply absurd h', rw nat.sub_zero,
       apply nat.ne_of_lt, apply lt_succ_of_le, 
       apply nat.le_sub_left_of_add_le H},
      {unfold IO at h, unfold OIOI at h, unfold list.repeat at h, 
       rw nil_append at h, rw cons_append at h, rw cons_inj' at h,
       have h' : I = O, from head_eq_of_cons_eq h,
       apply absurd h'.symm O_ne_I}},
    {unfold IO at h, unfold OIOI at h, 
     unfold list.repeat at h, rw cons_append at h, 
     have h' : I = O, from head_eq_of_cons_eq h,
     apply absurd h'.symm O_ne_I}}
end

lemma flip_OIOI (n k : ℕ) :
  flip (OIOI n k) = IOIO n k :=
begin
unfold OIOI, unfold IOIO,
rw flip_append, unfold flip, unfold B.flip, 
rw flip_repO, rw flip_repI
end

lemma flip_IOIO (n k : ℕ) :
  flip (IOIO n k) = OIOI n k :=
begin
unfold IOIO, unfold OIOI,
rw flip_append, unfold flip, unfold B.flip, 
rw flip_repI, rw flip_repO
end

end list 

namespace vector 

open vector 

def IO (n k : ℕ) (Hk : k ≤ n) : vector B n :=
  ⟨list.IO n k, list.length_IO n k Hk⟩ 

lemma wt_IO (n k : ℕ) (Hk : k ≤ n) :
  wt (IO n k Hk) = k :=
by {unfold wt, unfold IO, rw to_list_mk, apply list.num_Is_IO}

lemma sDel_IO_of_lt (n k i : ℕ) (Hkn : k ≤ n) (Hki : i + 1 ≤ k):
  sDel (IO n k Hkn) i 
  = IO (n - 1) (k - 1) (nat.sub_le_sub_right Hkn 1) :=
begin
unfold sDel, unfold IO, 
rw subtype.ext, rw ← to_list, rw to_list_mk, 
apply list.sDel_IO_of_lt _ _ _ Hki
end

lemma sDel_IO_succ_of_lt (n k i : ℕ) (Hkn : k + 1 ≤ n) (Hki : i ≤ k) :
  sDel (IO n (k + 1) Hkn) i 
  = IO (n - 1) k (nat.le_sub_right_of_add_le Hkn) :=
by apply sDel_IO_of_lt _ _ _ Hkn (succ_le_succ Hki)

lemma sDel_IO_of_ge (n k i : ℕ) (Hkn : k + 1 ≤ n) (Hki : k ≤ i) :
  sDel (IO n k (le_trans (le_succ k) Hkn)) i 
  = IO (n - 1) k (nat.le_sub_right_of_add_le Hkn) :=
begin
unfold sDel, unfold IO, 
rw subtype.ext, rw ← to_list, rw to_list_mk, 
apply list.sDel_IO_of_ge _ _ _ Hkn Hki
end

lemma sDel_IO_succ_of_ge (n k i : ℕ) (Hkn : k + 2 ≤ n) (Hki : k + 1 ≤ i) :
  sDel (IO n (k + 1) (le_trans (le_succ _ ) Hkn)) i 
  = IO (n - 1) (k + 1) (nat.le_sub_right_of_add_le Hkn)  :=
by apply sDel_IO_of_ge _ _ _ Hkn Hki

def IOIO (n k : ℕ) (Hkn : k + 2 ≤ n) : vector B n :=
  ⟨list.IOIO n k, list.length_IOIO n k Hkn⟩ 

lemma length_IOIO_le (n k : ℕ) (Hnk : k + 2 ≤ n) :
  2 ≤ length (vector.IOIO n k Hnk) :=
by {rw length, apply le_trans (le_add_left _ k) Hnk}

lemma wt_IOIO (n k : ℕ) (Hkn : k + 2 ≤ n) :
  wt (IOIO n k Hkn) = k + 1 :=
by {unfold wt, unfold IOIO, rw to_list_mk, apply list.num_Is_IOIO}

lemma wt_IOIO_le
  (k : ℕ) (Hnk : k + 2 ≤ n) (Hk : k < 1) :
  wt (vector.IOIO n k Hnk) ≤ 1 :=
begin
rw vector.wt_IOIO, apply le_trans,
  {apply add_le_add_right, apply (le_of_lt_succ Hk)},
  {rw zero_add}
end

lemma le_wt_IOIO
  (k : ℕ) (Hnk : k + 2 ≤ n) (Hk : n - 3 < k) :
  n - 1 ≤ wt (vector.IOIO n k Hnk) :=
begin
rw vector.wt_IOIO, 
apply nat.sub_le_right_of_le_add, 
apply le_of_lt_succ, rw ← nat.add_succ,
apply nat.lt_add_of_sub_lt_right Hk
end

lemma sDel_IOIO_O (n k : ℕ) (Hkn : k + 2 ≤ n) :
  sDel (IOIO n k Hkn) k 
  = IO (n - 1) (k + 1) (nat.le_sub_right_of_add_le Hkn) :=
begin
unfold sDel, unfold IOIO, unfold IO, 
rw subtype.ext, rw ← to_list, rw to_list_mk, 
apply list.sDel_IOIO_O
end

lemma sDel_IOIO_I (n k : ℕ) (Hkn : k + 2 ≤ n) :
  sDel (IOIO n k Hkn) (k + 1) 
  = IO (n - 1) k (le_of_succ_le (nat.le_sub_right_of_add_le Hkn)) :=
begin
unfold sDel, unfold IOIO, unfold IO, 
rw subtype.ext, rw ← to_list, rw to_list_mk, 
apply list.sDel_IOIO_I _ _ Hkn
end

lemma dS_IO_subset (n k : ℕ) (Hkn : k + 2 ≤ n) :
  dS (IO n (k + 1) (le_trans (le_succ _) Hkn)) ⊆ dS (IOIO n k Hkn) :=
begin
intros X hX, rw mem_dS at hX, cases hX with i hXi,
cases decidable.em(i ≤ k) with hlt hnlt,
  {rw sDel_IO_succ_of_lt _ _ _ _ at hXi,
    {rw mem_dS, apply exists.intro (k + 1), 
     rw sDel_IOIO_I n k Hkn, rw hXi},
    {apply hlt}},
  {rw sDel_IO_succ_of_ge _ _ _ _ at hXi,
    {rw mem_dS, apply exists.intro k, 
     rw sDel_IOIO_O n k Hkn, rw hXi},
    {rw not_le at hnlt, apply succ_le_of_lt hnlt}}
end

def OI (n k : ℕ) (Hk : k ≤ n) : vector B n :=
  ⟨list.OI n k, list.length_OI n k Hk⟩ 

lemma wt_OI (n k : ℕ) (Hk : k ≤ n) :
  wt (OI n k Hk) = n - k :=
by {unfold wt, unfold OI, rw to_list_mk, apply list.num_Is_OI}

lemma sDel_OI_of_lt (n k i : ℕ) (Hkn : k ≤ n) (Hki : i + 1 ≤ k):
  sDel (OI n k Hkn) i 
  = OI (n - 1) (k - 1) (nat.sub_le_sub_right Hkn 1) :=
begin
unfold sDel, unfold OI, 
rw subtype.ext, rw ← to_list, rw to_list_mk, 
apply list.sDel_OI_of_lt _ _ _ Hki
end

lemma sDel_OI_succ_of_lt (n k i : ℕ) (Hkn : k + 1 ≤ n) (Hki : i ≤ k) :
  sDel (OI n (k + 1) Hkn) i 
  = OI (n - 1) k (nat.le_sub_right_of_add_le Hkn) :=
by apply sDel_OI_of_lt _ _ _ Hkn (succ_le_succ Hki)

lemma sDel_OI_of_ge (n k i : ℕ) (Hkn : k + 1 ≤ n) (Hki : k ≤ i) :
  sDel (OI n k (le_trans (le_succ k) Hkn)) i 
  = OI (n - 1) k (nat.le_sub_right_of_add_le Hkn) :=
begin
unfold sDel, unfold OI, 
rw subtype.ext, rw ← to_list, rw to_list_mk, 
apply list.sDel_OI_of_ge _ _ _ Hkn Hki
end

lemma sDel_OI_succ_of_ge (n k i : ℕ) (Hkn : k + 2 ≤ n) (Hki : k + 1 ≤ i) :
  sDel (OI n (k + 1) (le_trans (le_succ _ ) Hkn)) i 
  = OI (n - 1) (k + 1) (nat.le_sub_right_of_add_le Hkn)  :=
by apply sDel_OI_of_ge _ _ _ Hkn Hki

def OIOI (n k : ℕ) (Hkn : k + 2 ≤ n) : vector B n :=
  ⟨list.OIOI n k, list.length_OIOI n k Hkn⟩ 

lemma length_OIOI_le (n k : ℕ) (Hnk : k + 2 ≤ n) :
  2 ≤ length (vector.OIOI n k Hnk) :=
by {rw length, apply le_trans (le_add_left _ k) Hnk}

lemma wt_OIOI (n k : ℕ) (Hkn : k + 2 ≤ n) :
  wt (OIOI n k Hkn) = n - k - 1 :=
begin
unfold wt, unfold OIOI, rw to_list_mk, 
rw list.num_Is_OIOI, rw ← nat.sub_add_comm,
  {rw nat.succ_sub_succ},
  {apply nat.le_sub_left_of_add_le Hkn}
end

lemma le_wt_OIOI
  (k : ℕ) (Hnk : k + 2 ≤ n) (Hk : k < 1) :
  n - 1 ≤ wt (vector.OIOI n k Hnk) :=
begin
rw vector.wt_OIOI, 
rw @eq_zero_of_le_zero k,
  {rw nat.sub_zero},
  {apply le_of_lt_succ Hk}
end

lemma wt_OIOI_le
  (k : ℕ) (Hnk : k + 2 ≤ n) (Hk : n - 3 < k) :
  wt (vector.OIOI n k Hnk) ≤ 1 :=
begin
rw vector.wt_OIOI, 
apply nat.sub_le_left_of_le_add, 
apply nat.sub_le_left_of_le_add, 
apply le_of_lt_succ, rw ← nat.add_succ,
apply nat.lt_add_of_sub_lt_right Hk
end

lemma sDel_OIOI_I (n k : ℕ) (Hkn : k + 2 ≤ n) :
  sDel (OIOI n k Hkn) k 
  = OI (n - 1) (k + 1) (nat.le_sub_right_of_add_le Hkn) :=
begin
unfold sDel, unfold OIOI, unfold OI, 
rw subtype.ext, rw ← to_list, rw to_list_mk, 
apply list.sDel_OIOI_I
end

lemma sDel_OIOI_O (n k : ℕ) (Hkn : k + 2 ≤ n) :
  sDel (OIOI n k Hkn) (k + 1) 
  = OI (n - 1) k (le_of_succ_le (nat.le_sub_right_of_add_le Hkn)) :=
begin
unfold sDel, unfold OIOI, unfold OI, 
rw subtype.ext, rw ← to_list, rw to_list_mk, 
apply list.sDel_OIOI_O _ _ Hkn
end

lemma dS_OI_subset (n k : ℕ) (Hkn : k + 2 ≤ n) :
  dS (OI n (k + 1) (le_trans (le_succ _) Hkn)) ⊆ dS (OIOI n k Hkn) :=
begin
intros X hX, rw mem_dS at hX, cases hX with i hXi,
cases decidable.em(i ≤ k) with hlt hnlt,
  {rw sDel_OI_succ_of_lt _ _ _ _ at hXi,
    {rw mem_dS, apply exists.intro (k + 1), 
     rw sDel_OIOI_O n k Hkn, rw hXi},
    {apply hlt}},
  {rw sDel_OI_succ_of_ge _ _ _ _ at hXi,
    {rw mem_dS, apply exists.intro k, 
     rw sDel_OIOI_I n k Hkn, rw hXi},
    {rw not_le at hnlt, apply succ_le_of_lt hnlt}}
end

lemma OI_ne_OIOI (n k₁ k₂ : ℕ) (Hk₁ : k₁ ≤ n) (Hk₂ : k₂ + 2 ≤ n):
  OI n k₁ Hk₁ ≠ OIOI n k₂ Hk₂ :=
begin
unfold OI, unfold OIOI, assume h, rw subtype.ext at h, 
repeat {rw ← to_list at h, rw to_list_mk at h}, 
apply list.OI_ne_OIOI _ _ _ h
end

lemma OI_ne_IOIO (n k₁ k₂ : ℕ) 
  (H : 3 ≤ n) (Hk₁ : k₁ ≤ n) (Hk₂ : k₂ + 2 ≤ n) :
  OI n k₁ Hk₁ ≠ IOIO n k₂ Hk₂ :=
begin
unfold OI, unfold IOIO, assume h, rw subtype.ext at h, 
repeat {rw ← to_list at h, rw to_list_mk at h}, 
apply list.OI_ne_IOIO _ _ _ H h
end

lemma IO_ne_IOIO (n k₁ k₂ : ℕ) (Hk₁ : k₁ ≤ n) (Hk₂ : k₂ + 2 ≤ n):
  IO n k₁ Hk₁ ≠ IOIO n k₂ Hk₂ :=
begin
unfold IO, unfold IOIO, assume h, rw subtype.ext at h, 
repeat {rw ← to_list at h, rw to_list_mk at h}, 
apply list.IO_ne_IOIO _ _ _ h
end

lemma IO_ne_OIOI (n k₁ k₂ : ℕ) 
  (H : 3 ≤ n) (Hk₁ : k₁ ≤ n) (Hk₂ : k₂ + 2 ≤ n) :
  IO n k₁ Hk₁ ≠ OIOI n k₂ Hk₂ :=
begin
unfold IO, unfold OIOI, assume h, rw subtype.ext at h, 
repeat {rw ← to_list at h, rw to_list_mk at h}, 
apply list.IO_ne_OIOI _ _ _ H h
end

lemma flip_OIOI (n k : ℕ) (Hkn : k + 2 ≤ n) :
  flip (OIOI n k Hkn) = IOIO n k Hkn :=
begin
unfold OIOI, unfold IOIO, rw subtype.ext,
repeat {rw ← to_list, rw to_list_mk},
apply list.flip_OIOI
end

lemma flip_IOIO (n k : ℕ) (Hkn : k + 2 ≤ n) :
  flip (IOIO n k Hkn) = OIOI n k Hkn :=
begin
unfold IOIO, unfold OIOI, rw subtype.ext,
repeat {rw ← to_list, rw to_list_mk},
apply list.flip_IOIO
end

end vector 

namespace finset

open finset B.finset

def insert_repO (C : finset (vector B n)) :=
  insert (repeat O n) (filter (Ici_wt 2) C) 

lemma repO_not_mem (C : finset (vector B n)):
  repeat O n ∉ filter (Ici_wt 2) C :=
begin
assume h, rw mem_filter at h, 
have hle : 2 ≤ wt (repeat O n), 
  {unfold Ici_wt at h, apply h.right},
apply absurd hle, apply not_le_of_gt, 
rw wt_repO, apply zero_lt_succ 
end

lemma DelCode_insert_repO
  (C : finset (vector B n)) (HC : is_DelCode C) :
  is_DelCode (insert_repO C) :=
begin
apply DelCode_insert,
  {apply DelCode_filter _ HC},
  {intros c hc, rw ← subset_empty, 
   intros x hx, rw mem_inter at hx, repeat {rw mem_dS at hx},
   cases hx.left with i hi, cases hx.right with j hj,
   have h1 : wt x = 0,
    {rw hi, rw sDel_repeat, rw wt_repO}, 
   have h2 : 1 ≤ wt x,
    {rw hj, apply le_trans _,
      {apply wt_le_sDel},
      {apply nat.le_sub_left_of_add_le,
       rw mem_filter at hc, apply hc.right}}, 
   apply absurd h1, apply nat.ne_of_gt (lt_of_succ_le h2)}
end

def insert_repI (C : finset (vector B n)) :=
  insert (repeat I n) (filter (Iic_wt (n - 2)) C) 

lemma repI_not_mem (Hn : 2 ≤ n) (C : finset (vector B n)):
  repeat I n ∉ filter (Iic_wt (n - 2)) C :=
begin
assume h, rw mem_filter at h, 
have hle : n - 2 < wt (repeat I n), 
  {rw wt_repI, apply nat.sub_lt,
    {apply lt_of_lt_of_le (zero_lt_two) Hn},
    {apply zero_lt_two}},
apply absurd hle, apply not_lt_of_ge, apply h.right
end

lemma DelCode_insert_repI (Hn : 2 ≤ n)
  (C : finset (vector B n)) (HC : is_DelCode C) :
  is_DelCode (insert_repI C) :=
begin
apply DelCode_insert,
  {apply DelCode_filter _ HC},
  {intros c hc, rw ← subset_empty, 
   intros x hx, rw mem_inter at hx, repeat {rw mem_dS at hx},
   cases hx.left with i hi, cases hx.right with j hj,
   have h1 : n - 1 = wt x,
    {rw hi, rw sDel_repeat, rw wt_repI}, 
   have h2 : wt x ≤ n - 2,
    {rw hj, apply le_trans,
      {apply wt_sDel_le},
      {rw mem_filter at hc, apply hc.right}}, 
   apply absurd h1, apply nat.ne_of_gt,
   apply lt_of_le_of_lt h2, 
   rw nat.sub_lt_right_iff_lt_add Hn,
   rw add_comm, rw ← nat.add_sub_assoc,
    {rw add_comm, rw succ_sub_succ, 
     rw nat.sub_zero, apply lt_succ_self},
    {apply le_trans (le_succ _) Hn}}
end

lemma DC_insert_repI_repO (Hn : 2 ≤ n) 
  (C : finset (vector B n)) (HC : is_DelCode C) :
  is_DelCode (insert_repI (insert_repO C)) :=
by {apply DelCode_insert_repI Hn, apply DelCode_insert_repO C HC}

lemma card_insert_repI_repO (Hn : 2 ≤ n) 
  (C : finset (vector B n)) (HC : is_DelCode C) :
  card (insert_repI (insert_repO C)) 
  = card (filter (Icc_wt 2 (n - 2)) C) + 2 :=
begin
unfold insert_repI, rw card_insert_of_not_mem, 
  {unfold insert_repO, rw filter_insert, rw if_pos,
    {rw card_insert_of_not_mem, 
      {repeat {rw succ_inj'}, rw filter_filter, congr},
      {rw filter_swap, apply repO_not_mem}},
    {unfold Iic_wt, rw wt_repO, apply nat.zero_le}},
  {apply repI_not_mem Hn}
end

lemma le_card_insert_repI_repO (Hn : 2 ≤ n) 
  (C : finset (vector B n)) (HC : is_DelCode C) :
  card C ≤ card (insert_repI (insert_repO C)) :=
begin
rw card_insert_repI_repO Hn C HC, 
apply card_le_filter_Icc HC,
end

def W22 (n : ℕ) : finset (vector B n) :=
  filter (@Icc_wt n 2 (n - 2)) univ

lemma mem_W22 {n : ℕ} (X : vector B n) : 
  X ∈ W22 n ↔ Icc_wt 2 (n - 2) X :=
begin
unfold W22, rw mem_filter, 
apply iff.intro,
  {intro h, apply h.right},
  {intro h, apply and.intro (mem_univ X) h}
end

lemma not_mem_W22_of_le 
  {n : ℕ} (X : vector B n) (H : wt X ≤ 1): 
  X ∉ W22 n :=
begin
assume h, rw mem_W22 at h,
apply absurd H, apply not_le_of_lt,
apply lt_of_succ_le, rw nat.succ_eq_add_one, 
apply  h.left
end

lemma not_mem_W22_of_ge 
  {n : ℕ} (Hn : 2 ≤ n) (X : vector B n) (H : n - 1 ≤ wt X): 
  X ∉ W22 n :=
begin
assume h, rw mem_W22 at h,
apply absurd h.right, apply not_le_of_lt,
apply lt_of_succ_le, rw nat.succ_eq_add_one,
rw ← nat.sub_add_comm Hn,
rw succ_sub_succ, apply H
end

lemma W22_of_le_2 {n : ℕ} (Hn : n ≤ 2) : 
  W22 n = ∅ :=
begin
rw ← subset_empty, 
intros x hx, unfold W22 at hx, 
rw mem_filter at hx, unfold Icc_wt at hx,
have h : wt x ≤ 0,
  {rw sub_eq_zero_of_le Hn at hx, apply hx.right.right},
apply absurd h, rw not_le, 
apply lt_of_succ_le, apply le_of_succ_le hx.right.left
end

lemma flip_W22 {n : ℕ} (Hn : 2 ≤ n) : 
  flip (W22 n) = W22 n :=
begin
unfold W22, rw flip_filter_swap _ _ _ Hn (nat.sub_le _ 2),
rw nat.sub_sub_self Hn, rw flip_univ 
end

lemma filter_Icc_wt
  (C : finset (vector B n)) (HC : C ⊆ W22 n) :
  filter (Icc_wt 2 (n - 2)) C = C :=
begin
apply subset.antisymm,
  {apply filter_subset},
  {intros c hc, unfold W22 at HC,
   have h : c ∈ filter (Icc_wt 2 (n - 2)) univ, from HC hc,
   rw mem_filter at h, rw mem_filter, apply and.intro hc h.right}
end

lemma card_DCs_sub_W22_le (Hn : 2 ≤ n) 
  (C : finset (vector B n)) (HC : is_DelCode C) (HC' : is_optimal C HC) :
  is_card_DCs_sub_le (W22 n) (card C - 2) :=
begin
intros C' hCS hC', 
have h : card C' + 2 ≤ card C,
  {apply le_trans _ ,
    {apply HC' (insert_repI (insert_repO C')), 
     apply DC_insert_repI_repO Hn C' hC'},
    {rw card_insert_repI_repO Hn C' hC',
     rw filter_Icc_wt _ hCS}},
apply nat.le_sub_right_of_add_le, apply h
end

lemma IO_mem_W22 (Hn : 3 ≤ n) (k : fin (n - 1)) (Hk : 1 ≤ k.1) (Hk' : k.1 ≤ n - 3) :
  vector.IO n (k + 1)  (le_of_lt (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2))) ∈ W22 n :=
begin
rw mem_W22, apply and.intro,
  {rw vector.wt_IO, apply succ_le_succ, apply Hk},
  {rw vector.wt_IO, apply nat.le_sub_left_of_add_le, 
   rw add_comm, rw add_assoc, 
   rw ← nat.le_sub_right_iff_add_le Hn, apply Hk'}
end

lemma IO_mem_W22' (Hn : 4 ≤ n) :
  vector.IO n 2 (le_of_succ_le (le_of_succ_le Hn)) ∈ W22 n :=
begin
rw mem_W22, apply and.intro,
  {rw vector.wt_IO},
  {rw vector.wt_IO, apply nat.le_sub_left_of_add_le Hn}
end

lemma OI_mem_W22 (Hn : 3 ≤ n) (k : fin (n - 1)) (Hk : 1 ≤ k.1) (Hk' : k.1 ≤ n - 3) :
  vector.OI n (k.1 + 1) (le_of_lt (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2))) ∈ W22 n :=
begin
rw mem_W22, apply and.intro,
  {rw vector.wt_OI, apply nat.le_sub_left_of_add_le, 
   rw add_assoc, rw ← nat.le_sub_right_iff_add_le Hn, apply Hk'},
  {rw vector.wt_OI, apply nat.sub_le_sub_left,
   apply succ_le_succ, apply Hk}
end

lemma optimal_of_W22
  {n : ℕ} {C : finset (vector B n)} (HC : is_DelCode C) 
  (H : ∀ C' ⊆ W22 n, is_DelCode C' → card C' + 2 ≤ card C) :
  is_optimal C HC :=
by apply optimal_of_div_wt HC H 

lemma optimal_of_div_wt' (Hn : 4 ≤ n) 
  {C : finset (vector B n)} (HC : is_DelCode C) 
  (HC' : is_card_DCs_sub_le (W22 n) (card C - 2)) :
  is_optimal C HC :=
begin
have Hn' : 2 ≤ n, from le_trans (le_trans (le_succ 2) (le_succ 3)) Hn,
intros C' hC', apply le_trans,
  {apply le_card_insert_repI_repO Hn' C' hC'},
  {rw card_insert_repI_repO Hn' C' hC', 
    {have h : 1 ≤ card C - 2,
      {apply lt_of_succ_le, apply le_trans _,
        {apply HC' (finset.singleton (vector.IO n 2 Hn')),
          {intros x hx, rw mem_singleton at hx, rw hx, 
           apply IO_mem_W22' Hn},
          {apply DelCode_singleton}},
        {rw card_singleton}},
     rw ← nat.le_sub_right_iff_add_le, 
      {apply HC', 
        {unfold W22, apply filter_subset_filter, apply subset_univ},
        {apply DelCode_filter _ hC'}},
      {apply le_of_lt, apply nat.lt_of_sub_pos h}}}
end

lemma card_DCs_sub_le_of_optimal (Hn : 2 ≤ n)
  (C : finset (vector B n)) (HC : is_DelCode C) (HC' : is_optimal C HC) :
  is_card_DCs_sub_le (W22 n) (card C - 2) :=
begin
intros C' hS hC', 
apply nat.le_sub_right_of_add_le, apply le_trans _,
  {apply HC' (insert_repI (insert_repO C')),
   apply DC_insert_repI_repO Hn C' hC'},
  {rw card_insert_repI_repO Hn C' hC',
   rw filter_Icc_wt _ hS}
end

lemma optimal_iff_W22 (Hn : 4 ≤ n)
  (C : finset (vector B n)) (HC : is_DelCode C) :
  is_optimal C HC ↔ is_card_DCs_sub_le (W22 n) (card C - 2) :=
begin
apply iff.intro,
  {apply card_DCs_sub_le_of_optimal 
    (le_trans (le_trans (le_succ 2) (le_succ 3)) Hn)},
  {apply optimal_of_div_wt' Hn}
end

def Repl_sub (n : ℕ) (k : fin (n - 1)) : finset (vector B n) :=
  {vector.OIOI n k.1 (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2)),
   vector.IOIO n k.1 (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2))}

lemma flip_Repl_sub (n : ℕ) (k : fin (n - 1)) : 
  flip (Repl_sub n k) = Repl_sub n k :=
begin
unfold Repl_sub, apply subset.antisymm,
  {intros x hx, rw mem_flip at hx, 
   cases hx with y hy, cases hy with hy hxy, 
   simp at hy, cases hy,
    {simp, right, rw ← hxy, rw hy, rw vector.flip_IOIO},
    {simp, left, rw ← hxy, rw hy, rw vector.flip_OIOI}},
  {intros x hx, rw mem_flip, simp at hx, cases hx,
    {apply exists.intro (vector.OIOI n (k.val) (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2))),
     apply exists.intro,
      {simp},
      {rw hx, rw vector.flip_OIOI}},
    {apply exists.intro (vector.IOIO n (k.val) (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2))),
     apply exists.intro,
      {simp},
      {rw hx, rw vector.flip_IOIO}}}
end

def Repl (n : ℕ) : finset (vector B n) :=
  fold (∪) ∅ (Repl_sub n) (@univ (fin (n - 1)) _)

lemma mem_Repl (X : vector B n) : 
  X ∈ Repl n ↔ ∃ k : fin (n - 1), X ∈ Repl_sub n k :=
begin
unfold Repl, rw mem_fold_union, apply iff.intro,
  {intro h, cases h with k hk, cases hk with hk hXk,
   apply exists.intro k, apply hXk},
  {intro h, cases h with k hk, 
   apply exists.intro k, apply exists.intro (mem_univ _), apply hk}
end

lemma mem_Repl' 
  (X : vector B n) (H : X ∈ Repl n) :
  ∃ k : fin (n - 1), 
  (X = vector.OIOI n k.1 (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2)) 
  ∨ X = vector.IOIO n k.1 (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2))) :=
begin
rw mem_Repl at H,  cases H with k Hk, 
unfold Repl_sub at Hk, simp at Hk, cases Hk, 
  {apply exists.intro, right, apply Hk},
  {apply exists.intro, left, apply Hk}
end

lemma mem_W22_inter_Repl (Hn : 2 ≤ n)
  (X : vector B n) (H : X ∈ W22 n ∩ Repl n) :
  ∃ k : fin (n - 1), (1 ≤ k.1) ∧ (k.1 ≤ n - 3) ∧ 
  (X = vector.OIOI n k.1 (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2)) 
  ∨ X = vector.IOIO n k.1 (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2))) :=
begin
rw mem_inter at H, rw mem_Repl at H, 
cases H.right with k hk, unfold Repl_sub at hk, simp at hk,
cases decidable.em(k.1 < 1) with hlt hnlt,
  {cases hk,
    {apply absurd H.left,
     apply not_mem_W22_of_le,
     rw hk, apply vector.wt_IOIO_le _ _ hlt},
    {apply absurd H.left,
     apply not_mem_W22_of_ge,
      {apply Hn},
      {rw hk, apply vector.le_wt_OIOI _ _ hlt}}},
  {cases decidable.em(n - 3 < k.1) with hlt' hnlt',
    {cases hk,
      {apply absurd H.left,
       apply not_mem_W22_of_ge,
        {apply Hn},
        {rw hk, apply vector.le_wt_IOIO _ _ hlt'}},
      {apply absurd H.left,
       apply not_mem_W22_of_le,
       rw hk, apply vector.wt_OIOI_le _ _ hlt'}},
    {apply exists.intro k, apply and.intro,
      {apply le_of_not_gt hnlt},
      {apply and.intro,
        {apply le_of_not_gt hnlt'},
        {rw or.comm, apply hk}}}}
end

lemma flip_Repl (n : ℕ) : 
  flip (Repl n) = Repl n :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_flip at hx,
   cases hx with y hy, cases hy with hy hxy, 
   rw mem_Repl at hy, cases hy with k hk,
   rw mem_Repl, apply exists.intro k, 
   rw ← hxy, rw flip_mem, rw flip_Repl_sub, apply hk},
  {intros x hx, rw mem_Repl at hx, 
   cases hx with k hk, rw mem_flip,
   apply exists.intro (vector.flip x), apply exists.intro,
    {rw mem_Repl, apply exists.intro k, 
     rw flip_mem, rw flip_Repl_sub, apply hk},
    {rw vector.flip_flip}}
end

lemma OI_not_mem_replace (Hn : 3 ≤ n) (k : fin (n - 1)) : 
  vector.OI n (k.1 + 1) (le_of_lt (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2))) ∉ Repl n := 
begin
assume h, rw mem_Repl at h, cases h with k hk, 
unfold Repl_sub at hk, simp at hk, cases hk,
  {apply vector.OI_ne_IOIO _ _ _ Hn, apply hk},
  {apply vector.OI_ne_OIOI, apply hk}
end

lemma IO_not_mem_replace (Hn : 3 ≤ n) (k : fin (n - 1)) : 
  vector.IO n (k.1 + 1) (le_of_lt (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2))) ∉ Repl n := 
begin
assume h, rw mem_Repl at h, cases h with k hk, 
unfold Repl_sub at hk, simp at hk, cases hk,
  {apply vector.IO_ne_IOIO, apply hk},
  {apply vector.IO_ne_OIOI _ _ _ Hn, apply hk}
end

lemma OI_mem_sdiff_replace
  (Hn : 3 ≤ n) (k : fin (n - 1)) (Hk : 1 ≤ k.1) (Hk' : k.1 ≤ n - 3) : 
  vector.OI n (k.1 + 1) (le_of_lt (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2))) ∈ W22 n \ Repl n := 
begin
rw mem_sdiff, apply and.intro,
  {apply OI_mem_W22 Hn _ Hk Hk'}, 
  {assume h, apply OI_not_mem_replace Hn _ h}
end

lemma IO_mem_sdiff_replace
  (Hn : 3 ≤ n) (k : fin (n - 1)) (Hk : 1 ≤ k.1) (Hk' : k.1 ≤ n - 3) : 
  vector.IO n (k.1 + 1) (le_of_lt (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2))) ∈ W22 n \ Repl n := 
begin
rw mem_sdiff, apply and.intro,
  {apply IO_mem_W22 Hn _ Hk Hk'}, 
  {assume h, apply IO_not_mem_replace Hn _ h}
end

lemma exists_sdiff_Repl
  (Hn : 3 ≤ n) (X : vector B n) (H : X ∈ W22 n ∩ Repl n) :
  ∃ X' ∈ W22 n \ Repl n, X' ≠ X ∧ dS X' ⊆ dS X :=
begin
cases mem_W22_inter_Repl  (le_of_succ_le Hn) X H with k hk, 
cases hk with hk1 hk, cases hk with hk2 hk, cases hk,
  {apply exists.intro (vector.OI n (k.val + 1) (le_of_lt (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2)))),
   apply exists.intro (OI_mem_sdiff_replace Hn _ hk1 hk2),
   apply and.intro,
    {rw hk, apply vector.OI_ne_OIOI},
    {rw hk, apply vector.dS_OI_subset}},
  {apply exists.intro (vector.IO n (k.val + 1) (le_of_lt (succ_le_of_lt (nat.add_lt_of_lt_sub_right k.2)))),
   apply exists.intro (IO_mem_sdiff_replace Hn _ hk1 hk2),
   apply and.intro,
    {rw hk, apply vector.IO_ne_IOIO},
    {rw hk, apply vector.dS_IO_subset}}
end

lemma exists_sdiff_Repl'
  (X : vector B n) (H : X ∈ W22 n ∩ Repl n) :
  ∃ X' ∈ W22 n \ Repl n, X' ≠ X ∧ dS X' ⊆ dS X :=
begin
cases decidable.em (3 ≤ n) with hle hnle,
  {apply exists_sdiff_Repl hle _ H},
  {rw not_le at hnle, rw lt_succ_iff at hnle,
   rw mem_inter at H, rw W22_of_le_2 hnle at H,
   apply false.elim H.left}
end

lemma optimal_iff_sdiff_Repl (Hn : 3 ≤ n)
  (C : finset (vector B n)) (HC : is_DelCode C) :
  is_optimal C HC ↔ is_optimal_sub (univ \ Repl n) C HC :=
begin
rw ← is_optimal_sub_univ,
rw iff.comm, rw optimal_sub_sdiff_iff,
intros x hx, cases mem_Repl' x hx with k hk, cases hk,
  {apply exists.intro, apply exists.intro,
    {rw mem_sdiff, apply and.intro,
      {apply mem_univ},
      {apply OI_not_mem_replace Hn k}},
    {apply and.intro,
      {rw hk, apply B.vector.OI_ne_OIOI},
      {rw hk, apply B.vector.dS_OI_subset}}},
  {apply exists.intro, apply exists.intro,
    {rw mem_sdiff, apply and.intro,
      {apply mem_univ},
      {apply IO_not_mem_replace Hn k}},
    {apply and.intro,
      {rw hk, apply B.vector.IO_ne_IOIO},
      {rw hk, apply B.vector.dS_IO_subset}}}
end

lemma Repl_of_le_one (Hn : n ≤ 1) : Repl n = ∅ := 
begin
rw ← subset_empty, intros x hx, cases mem_Repl' x hx with k hk, cases hk,
  {have h : 2 ≤ length x, 
    {rw hk, apply vector.length_OIOI_le},
   apply absurd Hn, apply not_le_of_gt (lt_of_succ_le h)},
  {have h : 2 ≤ length x, 
    {rw hk, apply vector.length_IOIO_le},
   apply absurd Hn, apply not_le_of_gt (lt_of_succ_le h)}
end

lemma Repl_two : Repl 2 = {⟨[I, O], rfl⟩, ⟨[O, I], rfl⟩} := rfl
lemma sdiff_Repl_two : univ \ Repl 2 = {⟨[I, I], rfl⟩, ⟨[O, O], rfl⟩} := rfl

def II : vector B 2 := ⟨[I, I], rfl⟩
lemma II_ne_IO : II ≠ ⟨[I, O], rfl⟩ := dec_trivial
lemma II_mem_sdiff : II ∈ univ \ Repl 2 := dec_trivial
lemma dS_II_subset_IO : dS II ⊆ dS ⟨[I, O], rfl⟩ := dec_trivial

def OO : vector B 2 := ⟨[O, O], rfl⟩
lemma OO_ne_OI : OO ≠ ⟨[O, I], rfl⟩ := dec_trivial
lemma OO_mem_sdiff : OO ∈ univ \ Repl 2 := dec_trivial
lemma dS_OO_subset_OI : dS OO ⊆ dS ⟨[O, I], rfl⟩ := dec_trivial

lemma optimal_iff_sdiff_Repl'
  (C : finset (vector B n)) (HC : is_DelCode C) :
  is_optimal C HC ↔ is_optimal_sub (univ \ Repl n) C HC :=
begin
rw ← is_optimal_sub_univ, cases n,
  {rw Repl_of_le_one, 
    {rw sdiff_empty},
    {apply nat.zero_le}},
  {cases n,
    {rw Repl_of_le_one, 
      {rw sdiff_empty},
      {refl}},
    {cases n,
      {rw iff.comm, rw optimal_sub_sdiff_iff, 
      intros x hx, rw Repl_two at hx, simp at hx, cases hx,
        {apply exists.intro OO, apply exists.intro OO_mem_sdiff,
         rw hx, apply and.intro OO_ne_OI dS_OO_subset_OI},
        {apply exists.intro II, apply exists.intro II_mem_sdiff,
         rw hx, apply and.intro II_ne_IO dS_II_subset_IO}},
      {rw is_optimal_sub_univ, rw optimal_iff_sdiff_Repl,
       repeat {apply succ_le_succ}, apply nat.zero_le}}}
end

lemma optimal_of_W22_sdiff_Repl
  {n : ℕ} {C : finset (vector B n)} (HC : is_DelCode C) 
  (H : ∀ C' ⊆ W22 n \ Repl n, is_DelCode C' → card C' + 2 ≤ card C) :
  is_optimal C HC :=
begin
apply optimal_of_W22, intros C' hC hC', 
cases exists_DelCode_sdiff' (W22 n) C' _ (Repl n) _ with C'' hC'',
  {cases hC'' with hC'' hCC'', rw mem_DCs_sub at hC'', rw ← hCC'', 
   apply H _ hC''.left hC''.right},
  {rw mem_DCs_sub, apply and.intro hC hC'},
  {intros x hx, apply exists_sdiff_Repl' x hx}
end

lemma optimal_iff_W22_sdiff_Repl (Hn : 4 ≤ n)
  (C : finset (vector B n)) (HC : is_DelCode C) :
  is_optimal C HC ↔ is_card_DCs_sub_le (W22 n \ Repl n) (card C - 2) :=
begin
rw optimal_iff_W22 Hn, rw ← card_DCs_sub_le_sdiff_iff',
intros x hx, apply exists_sdiff_Repl' x hx
end

lemma flip_W22_sdiff_Repl (Hn : 2 ≤ n):
  flip (W22 n \ Repl n) = W22 n \ Repl n :=
by {rw flip_sdiff, rw flip_W22 Hn, rw flip_Repl}

end finset

end B