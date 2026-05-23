/- Copyright Yuki Kondo c/o Manabu Hagiwara 2022, 2026 -/
import data.fintype .InsDel .B .NumOsNumIs

variables {α : Type} [decidable_eq α]
variables {n : ℕ} (C C' : finset (vector α n)) (c : vector α n)
variables (X X' : vector α n) (Y : vector α (n - 1))

open nat vector finset B.vector B.finset

def is_DelCode {n : ℕ} (C : finset (vector α n)) : Prop :=
  ∀ X Y ∈ C, X ≠ Y → dS X ∩ dS Y = ∅

instance decidable_pred_is_DelCode [fintype α] :
  decidable_pred (@is_DelCode α _inst_1 n) :=
by {intro s, rw is_DelCode, apply_instance}

lemma DelCode_empty :
  is_DelCode (∅ : finset (vector α n)) :=
begin
unfold is_DelCode, intros x y hxin hyin hne,
apply false.elim hxin
end

lemma DelCode_singleton :
  is_DelCode (finset.singleton X) :=
begin
unfold is_DelCode, intros x y hx hy hne,
rw mem_singleton at hx,
rw mem_singleton at hy,
rw hx at hne,  rw hy at hne,
apply absurd (eq.refl X) hne
end

lemma DelCode_subset
  (H : is_DelCode C) (HCC : C' ⊆ C) :
  is_DelCode C' :=
by {intros x y hx hy hne, apply H x y (HCC hx) (HCC hy) hne}

lemma DelCode_filter
  (H : is_DelCode C) (p : vector α n → Prop) [decidable_pred p] :
  is_DelCode (filter p C) :=
by {apply DelCode_subset _ _ H, apply filter_subset}

lemma DelCode_sdiff
  (H : is_DelCode C) (S : finset (vector α n)) :
  is_DelCode (C \ S) :=
by {apply DelCode_subset _ _ H, apply sdiff_subset_self}

lemma DelCode_insert
  (HC : is_DelCode C) (Hx : ∀ c ∈ C, dS X ∩ dS c = ∅):
  is_DelCode (insert X C) :=
begin
intros y z hy hz hne,
rw mem_insert at hy, rw mem_insert at hz,
cases hy with hyx hyC,
  {cases hz with hzx hzC,
    {rw hyx at hne, rw hzx at hne, contradiction},
    {rw hyx, apply Hx z hzC}},
  {cases hz with hzx hzC,
    {rw hzx, rw finset.inter_comm, apply Hx y hyC},
    {apply HC y z hyC hzC hne}}
end

lemma DelCode_of_insert
  (H : is_DelCode (insert X C)) :
  is_DelCode C :=
by {apply DelCode_subset _ _ H, apply subset_insert}

lemma DelCode_insert_iff (Hx : X ∉ C):
  is_DelCode (insert X C) ↔ is_DelCode C ∧ ∀ c ∈ C, dS X ∩ dS c = ∅:=
begin
apply iff.intro,
  {intros hCx, apply and.intro,
    {apply DelCode_of_insert _ X hCx},
    {intros c hc, apply hCx X c,
      {rw mem_insert, left, refl},
      {rw mem_insert, right, apply hc},
      {assume h, rw h at Hx, contradiction}}},
  {intro h, apply DelCode_insert _ _ h.left h.right}
end

lemma DelCode_insert_iff' (Hx : X ∉ C):
  is_DelCode (insert X C) ↔ is_DelCode C ∧ dS X ∩ union_dS C = ∅ :=
by {rw DelCode_insert_iff _ X Hx, rw forall_dS_inter_dS_iff}

lemma DelCode_erase (H : is_DelCode C) :
  is_DelCode (erase C X) :=
by {apply DelCode_subset _ _ H, apply erase_subset}

def replace :=
  insert X' (erase C X)

lemma DelCode_replace
  (HC : is_DelCode C) (HX : X ∈ C) (HX' : dS X' ⊆ dS X)  :
  is_DelCode (replace C X X') :=
begin
unfold replace, apply DelCode_insert,
  {apply DelCode_erase _ _ HC},
  {intros c hc, apply subset.antisymm,
    {apply subset.trans,
      {apply inter_subset_inter_right HX'},
      {rw HC X c HX _ _,
        {refl},
        {apply mem_of_mem_erase hc},
        {rw mem_erase at hc, apply hc.left.symm}}},
    {apply empty_subset}}
end

lemma card_replace
  (HC : is_DelCode C)
  (x : vector α n) (Hx : x ∈ C)
  (y : vector α n) (Hxy : dS y ⊆ dS x)  :
  card (replace C x y) = card C :=
begin
unfold replace, rw card_insert_of_not_mem,
  {rw card_erase_of_mem Hx,
   rw add_one, rw nat.succ_pred_eq_of_pos,
   rw gt, rw card_pos, apply ne_empty_of_mem Hx},
  {assume h, rw mem_erase at h,
   have h1 : dS x ∩ dS y = ∅,
    {apply HC x y Hx h.right h.left.symm},
   have h2 : dS x ∩ dS y ≠ ∅,
    {rw inter_of_right_subset Hxy, apply dS_ne},
   contradiction}
end

lemma DelCode_flip
  {C : finset (vector B n)} (HC : is_DelCode C) :
  is_DelCode (flip C) :=
begin
intros x y hx hy hne,
rw mem_flip at hx, cases hx with x' hx', cases hx' with hx' hxx',
rw mem_flip at hy, cases hy with y' hy', cases hy' with hy' hyy',
rw ← hxx' at hne, rw ← hyy' at hne,
rw ne_from_not_eq at hne, rw flip_eq_flip_iff at hne,
rw ← hxx', rw dS_flip, rw ← hyy', rw dS_flip,
rw ← flip_inter, rw HC x' y' hx' hy' hne, rw flip_empty
end

lemma exists_DC_sub_Icc_wt
  (a b : ℕ) (Ha : a ≤ n) (Hb : b ≤ n)
  (C : finset (vector B n)) (HC : is_DelCode C) (HCS : C ⊆ filter (Icc_wt a b) univ) :
  ∃ C' : finset (vector B n), is_DelCode C' ∧ C' ⊆ filter (Icc_wt (n - b) (n - a)) univ :=
begin
apply exists.intro (flip C), apply and.intro,
  {apply DelCode_flip HC},
  {intros x hx, rw mem_flip at hx,
   cases hx with y hy, cases hy with hy hxy,
   have h : y ∈ filter (Icc_wt a b) univ, from HCS hy,
   rw mem_filter at h, rw ← hxy, rw mem_filter, apply and.intro,
    {apply mem_univ},
    {unfold Icc_wt, apply and.intro,
      {rw wt_flip, rw nat.sub_le_sub_left_iff,
        {apply h.right.right},
        {apply le_trans h.right.right Hb}},
      {rw wt_flip, rw nat.sub_le_sub_left_iff,
        {apply h.right.left},
        {apply Ha}}}}
end

lemma exists_DC_card_filter_wt_le
  (S : finset (vector B n)) (HS : flip S = S)
  (C : finset (vector B n)) (HC : is_DelCode C) (HCS : C ⊆ S)
  (a b : ℕ) (Ha : a ≤ n) (Hb : b ≤ n) :
  ∃ C' : finset (vector B n), is_DelCode C' ∧ C' ⊆ S
  ∧ card C' = card C ∧ card (filter (Icc_wt (n - b) (n - a)) C') ≤ card (filter (Icc_wt a b) C') :=
begin
cases decidable.em(card (filter (Icc_wt (n - b) (n - a)) C) ≤ card (filter (Icc_wt a b) C)) with hle hnle,
  {apply exists.intro C, apply and.intro HC, apply and.intro HCS,
   apply and.intro (eq.refl _) hle},
  {apply exists.intro (flip C), rw ← HS,
   apply and.intro (DelCode_flip HC),
   apply and.intro (flip_subset _ _ HCS),
   apply and.intro (card_flip _),
   have h1 : card (filter (Icc_wt (n - b) (n - a)) (flip C)) = card (filter (Icc_wt a b) C),
    {rw filter_flip_swap _ _ _ (nat.sub_le_self _ _) (nat.sub_le_self _ _),
     rw nat.sub_sub_assoc (refl _) Ha, rw nat.sub_self, rw zero_add,
     rw nat.sub_sub_assoc (refl _) Hb, rw nat.sub_self, rw zero_add, rw card_flip},
   have h2 : card (filter (Icc_wt a b) (flip C)) = card (filter (Icc_wt (n - b) (n - a)) C),
    {rw filter_flip_swap _ _ _ Ha Hb, rw card_flip},
   rw h1, rw h2, apply le_of_lt (lt_of_not_ge hnle)}
end

def sum_card_dS {n : ℕ} (C : finset (vector α n)) : ℕ :=
  fold (+) 0 (λ c, card (dS c)) C

lemma sum_card_dS_empty :
  sum_card_dS (∅ : finset (vector α n)) = 0 :=
by {unfold sum_card_dS, rw fold_empty}

lemma sum_card_dS_insert (H : X ∉ C):
  sum_card_dS (insert X C) = card (dS X) + sum_card_dS C :=
by {unfold sum_card_dS, rw fold_insert H}

def is_DelCode' {n : ℕ} (C : finset (vector α n)) : Prop :=
  card (union_dS C) = sum_card_dS C

instance decidable_pred_is_DelCode' :
  decidable_pred (@is_DelCode' α _inst_1 n) :=
by {intro s, rw is_DelCode', apply_instance}

lemma DelCode'_empty :
  is_DelCode' (∅ : finset (vector α n)) :=
by {unfold is_DelCode', rw union_dS_empty, rw card_empty, rw sum_card_dS_empty}

lemma card_union_dS_le :
  card (union_dS C) ≤ sum_card_dS C :=
begin
induction C using finset.induction with s S hnin IH h,
  {refl},
  {rw sum_card_dS_insert S s hnin,
   rw union_dS_insert _ _ hnin,
   apply le_trans,
    {apply card_union_le},
    {apply nat.add_le_add_left IH}}
end

lemma dS_inter_union_dS_of_DelCode'_insert
  (HX : X ∉ C) (HCX : is_DelCode' (insert X C)) :
  dS X ∩ union_dS C = ∅ :=
begin
unfold is_DelCode' at HCX,
rw card_union_dS_insert _ _ HX at HCX,
rw sum_card_dS_insert C X HX at HCX,
rw ← card_eq_zero, apply zero_of_sub_eq_of_le _ _ HCX,
  {apply lt_of_lt_of_le (card_dS_pos X) (le_add_right _ _)},
  {apply add_le_add_left (card_union_dS_le C)}
end

lemma DelCode'_of_DelCode'_insert
  (HX : X ∉ C) (HCX : is_DelCode' (insert X C)) :
  is_DelCode' C :=
begin
have h : card (dS X) + card (union_dS C) - card (dS X ∩ union_dS C)
         = card (dS X) + sum_card_dS C,
  {unfold is_DelCode' at HCX,
   rw card_union_dS_insert _ _ HX at HCX,
   rw sum_card_dS_insert C X HX at HCX, apply HCX},
rw dS_inter_union_dS_of_DelCode'_insert C X HX HCX at h,
rw card_empty at h, rw nat.sub_zero at h,
apply eq_of_add_eq_add_left h
end

lemma card_dS_insert_of_card_dS
  (HC : is_DelCode' C) (HX : X ∉ C) (HCX : dS X ∩ union_dS C = ∅):
  is_DelCode' (insert X C) :=
begin
unfold is_DelCode' at HC, unfold is_DelCode',
rw card_union_dS_insert _ _ HX,
rw HC, rw HCX, rw card_empty, rw nat.sub_zero,
rw sum_card_dS_insert C X HX
end

lemma DelCode'_insert_iff (HX : X ∉ C):
  is_DelCode' (insert X C) ↔ is_DelCode' C ∧ dS X ∩ union_dS C = ∅ :=
begin
apply iff.intro,
  {intros h, apply and.intro,
    {apply DelCode'_of_DelCode'_insert C X HX h},
    {apply dS_inter_union_dS_of_DelCode'_insert C X HX h}},
  {intros h, apply card_dS_insert_of_card_dS _ _ h.left HX h.right}
end

lemma DelCode_of_DelCode' (HC : is_DelCode' C) :
  is_DelCode C :=
begin
induction C using finset.induction with s S hs ihC,
  {apply DelCode_empty},
  {rw DelCode'_insert_iff _ _ hs at HC,
   rw DelCode_insert_iff' _ s hs,
   apply and.intro (ihC HC.left) HC.right}
end

lemma DelCode'_of_DelCode (HC : is_DelCode C) :
  is_DelCode' C :=
begin
induction C using finset.induction with s S hs ihC,
  {apply DelCode'_empty},
  {rw DelCode_insert_iff' _ s hs at HC,
   rw DelCode'_insert_iff S s hs, apply and.intro (ihC HC.left) HC.right}
end

lemma DelCode'_iff {n : ℕ} (C : finset (vector α n)) :
  is_DelCode' C ↔ is_DelCode C :=
begin
apply iff.intro,
  {apply DelCode_of_DelCode'},
  {apply DelCode'_of_DelCode}
end

lemma union_dS_inter_of_DelCode
  {C : finset (vector α n)} (HC : is_DelCode C)
  {C₁ C₂ : finset (vector α n)} (HC₁ : C₁ ⊆ C) (HC₂ : C₂ ⊆ C)
  (H : C₁ ∩ C₂ = ∅) :
  union_dS C₁ ∩ union_dS C₂ = ∅ :=
begin
rw ← subset_empty,
intros x hx, rw mem_inter at hx,
repeat {rw mem_union_dS at hx}, cases hx with hx₁ hx₂,
cases hx₁ with y₁ hy₁, cases hy₁ with hy₁ hxy₁,
cases hx₂ with y₂ hy₂, cases hy₂ with hy₂ hxy₂,
have h1 : dS y₁ ∩ dS y₂ = ∅,
  {apply HC y₁ y₂ (HC₁ hy₁) (HC₂ hy₂),
   assume h, rw h at hy₁,
   have h' : y₂ ∈ C₁ ∩ C₂,
    {rw mem_inter, apply and.intro hy₁ hy₂},
   rw H at h', apply false.elim h'},
have h2 : dS y₁ ∩ dS y₂ ≠ ∅,
  {apply ne_empty_of_mem, rw mem_inter,
   apply and.intro hxy₁ hxy₂},
contradiction
end

namespace B

open B.vector vector

def dB {n : ℕ} (X : vector B n) : finset (vector B n) :=
  union_dS (IS X)

lemma mem_dB {n : ℕ} (X Y : vector B n) :
  Y ∈ dB X ↔ Y ∈ union_dS (IS X) :=
by trivial

lemma mem_dB_iff {n : ℕ} (X Y : vector B n) :
  Y ∈ dB X ↔ IS X ∩ IS Y ≠ ∅ :=
begin
apply iff.intro,
  {intro hY, rw mem_dB at hY,
   rw @mem_union_dS _ _ (n + 1) at hY,
   cases hY with Z hYZ, cases hYZ with hZ hYZ,
   have h : Z ∈ IS X ∩ IS Y,
    {rw mem_inter, apply and.intro hZ (mem_IS_of_mem_dS Z Y hYZ)},
   apply ne_empty_of_mem h},
  {intro h,
   cases exists_mem_of_ne_empty h with Z hZ,
   rw mem_inter at hZ, rw mem_dB, rw @mem_union_dS _ _ (n + 1),
   apply exists.intro Z, apply exists.intro,
    {apply hZ.left},
    {apply (mem_dS_of_mem_IS Y Z hZ.right)}}
end

lemma mem_dB_iff' {n : ℕ} (X Y : vector B n) :
  Y ∈ dB X ↔ dS X ∩ dS Y ≠ ∅ :=
by {rw mem_dB_iff, rw IS_inter_ne_empty_iff}

def union_dB (C : finset (vector B n)) :=
  fold (∪) ∅ dB C

def union_dB_empty :
  union_dB (∅ : finset (vector B n)) = ∅ :=
by {unfold union_dB, rw fold_empty}

lemma mem_union_dB (C : finset (vector B n)) (X : vector B n) :
  X ∈ union_dB C ↔ ∃ Y ∈ C, X ∈ dB Y :=
by {unfold union_dB, apply mem_fold_union}

lemma mem_union_dB_iff (C : finset (vector B n)) (X : vector B n) :
  X ∈ union_dB C ↔ ∃ Y ∈ C, dS Y ∩ dS X ≠ ∅ :=
begin
apply iff.intro,
  {intro h, rw mem_union_dB at h,
   cases h with y hy, cases hy with hy hxy, rw mem_dB_iff' at hxy,
   apply exists.intro y, apply exists.intro hy, apply hxy},
  {intro h, cases h with y hy, cases hy with hy hxy,
   rw mem_union_dB, apply exists.intro y, apply exists.intro hy,
  rw mem_dB_iff', apply hxy}
end

lemma not_mem_dB_iff
  (C : finset (vector B n)) (X : vector B n) :
  X ∉ union_dB C ↔ ∀ Y ∈ C, dS Y ∩ dS X = ∅ :=
begin
apply iff.intro,
  {intros h y hy, apply subset.antisymm,
    {intros z hz,
     have hzC : X ∈ union_dB C,
      {rw mem_union_dB_iff,
       apply exists.intro y, apply exists.intro hy,
       apply ne_empty_of_mem hz},
     contradiction},
    {apply empty_subset}},
  {intro h,
   assume h', rw mem_union_dB_iff at h',
   cases h' with y hy, cases hy with hy hxy,
   apply absurd (h y hy) hxy}
end

lemma subset_union_dB (C : finset (vector B n)) :
  C ⊆ union_dB C :=
begin
intros x hx, rw mem_union_dB_iff,
apply exists.intro x, apply exists.intro hx,
rw inter_self, apply dS_ne
end

lemma union_dB_subset
  (C₁ C₂ : finset (vector B n)) (H : C₁ ⊆ C₂) :
  union_dB C₁ ⊆ union_dB C₂  :=
begin
intros x hx, rw mem_union_dB_iff at hx,
cases hx with y hy, cases hy with hy hxy,
rw mem_union_dB_iff,
apply exists.intro y, apply exists.intro (H hy), apply hxy
end

lemma not_mem_of_not_mem_dB
  (C : finset (vector B n)) (X : vector B n)
  (H : X ∉ union_dB C) :
  X ∉ C :=
begin
assume h,
have hX : X ∈ union_dB C,
  from (subset_union_dB C) h,
contradiction
end

lemma DelCode_insert_iff_not_mem_dB
  (C : finset (vector B n)) (X : vector B n) (HX : X ∉ C) :
  is_DelCode (insert X C) ↔ is_DelCode C ∧ X ∉ union_dB C :=
begin
rw DelCode_insert_iff _ _ HX, rw not_mem_dB_iff, apply iff.intro,
  {intro h, apply and.intro h.left,
   intros Y hY, rw inter_comm, apply h.right Y hY},
  {intro h, apply and.intro h.left,
   intros Y hY, rw inter_comm, apply h.right Y hY}
end

lemma not_mem_union_dB
  {C : finset (vector B n)} (HC : is_DelCode C)
  {C₁ C₂ : finset (vector B n)}
  (HC₁ : C₁ ⊆ C) (HC₂ : C₂ ⊆ C) (H : C₁ ∩ C₂ = ∅)
  (c : vector B n) (Hc : c ∈ C₁) :
  c ∉ union_dB C₂ :=
begin
rw not_mem_dB_iff,
intros y hy, apply HC _ _ (HC₂ hy) (HC₁ Hc),
assume h,
have h' : c ∈ C₁ ∩ C₂,
  {rw mem_inter, apply and.intro Hc, rw ← h, apply hy},
rw H at h', apply false.elim h'
end

lemma DelCode_union_iff
  {n : ℕ} {C : finset (vector B n)} (HC : is_DelCode C)
  {S C' : finset (vector B n)} (HSC' : C' ⊆ S) (HC' : is_DelCode C') (H : C ∩ C' = ∅) :
  is_DelCode (C ∪ C') ↔ C' ⊆ S \ union_dB C :=
begin
apply iff.intro,
  {intros h x hx, rw mem_sdiff, apply and.intro,
    {apply HSC' hx},
    {rw not_mem_dB_iff, intros y hy, apply h,
      {rw mem_union, left, apply hy},
      {rw mem_union, right, apply hx},
      {assume h',
       have H' : C ∩ C' ≠ ∅,
        {apply ne_empty_of_mem, rw mem_inter, apply and.intro,
          {apply hy},
          {rw h', apply hx}},
       contradiction}}},
  {intros h x y hx hy hne,
   rw mem_union at hx, cases hx,
    {rw mem_union at hy, cases hy,
      {apply HC x y hx hy hne},
      {have H' : y ∈ S \ union_dB C, from h hy,
       rw mem_sdiff at H', rw not_mem_dB_iff at H',
       apply H'.right x hx}},
    {rw mem_union at hy, cases hy,
      {have H' : x ∈ S \ union_dB C, from h hx,
       rw mem_sdiff at H', rw not_mem_dB_iff at H',
       rw inter_comm, apply H'.right y hy},
      {apply HC' x y hx hy hne}}}
end

lemma subset_union_dB_of_DelCode
  {S : finset (vector B n)} {C : finset (vector B n)}
  (HC : is_DelCode C) (HCS : C ⊆ S)
  {C₁ C₂ : finset (vector B n)}
  (HC₁ : C₁ ⊆ C) (HC₂ : C₂ ⊆ C) (H : C₁ ∩ C₂ = ∅) :
  C₁ ⊆ S \ union_dB C₂ :=
begin
intros y hy, rw mem_sdiff, apply and.intro,
  {apply (subset.trans HC₁ HCS) hy},
  {apply not_mem_union_dB HC HC₁ HC₂ H _ hy}
end

lemma not_mem_union_dB_erase
  {C : finset (vector B n)} (HC : is_DelCode C)
  (c : vector B n) (Hc : c ∈ C) :
  c ∉ union_dB (erase C c) :=
begin
rw not_mem_dB_iff,
intros y hy, apply HC _ _ (erase_subset _ _ hy) Hc,
rw mem_erase at hy, apply hy.left
end

def dS_wt (X : vector B n) (w : ℕ) : finset (vector B (n - 1)) :=
  filter (λ x, wt x = w) (dS X)

lemma mem_dS_wt (X : vector B n) (w : ℕ) (Y : vector B (n - 1)) :
  Y ∈ dS_wt X w ↔ Y ∈ dS X ∧ wt Y = w :=
by {unfold dS_wt, rw mem_filter}

lemma dS_wt_subset (X : vector B n) (w : ℕ) :
  dS_wt X w ⊆ dS X :=
by {intros x hx, rw mem_dS_wt at hx, apply hx.left}

def union_dS_wt (C : finset (vector B n)) (w : ℕ) : finset (vector B (n - 1)) :=
  filter (λ x, wt x = w) (union_dS C)

lemma mem_union_dS_wt (C : finset (vector B n)) (w : ℕ) (X : vector B (n - 1)) :
  X ∈ union_dS_wt C w ↔ X ∈ union_dS C ∧ wt X = w :=
by {unfold union_dS_wt, rw mem_filter}

lemma union_dS_wt_empty (w : ℕ) :
  union_dS_wt (∅ : finset (vector B n)) w = ∅ :=
by {unfold union_dS_wt, rw union_dS_empty, apply filter_empty}

lemma  union_dS_wt_insert
  (C : finset (vector B n)) (w : ℕ) (X : vector B n) (HX : X ∉ C):
  union_dS_wt (insert X C) w = dS_wt X w ∪ union_dS_wt C w :=
begin
unfold union_dS_wt, rw union_dS_insert _ _ HX,
rw filter_union, unfold dS_wt
end

lemma union_dS_wt_subset
  (C : finset (vector B n)) (w : ℕ):
  union_dS_wt C w ⊆ union_dS C :=
by {intros x hx, rw mem_union_dS_wt at hx, apply hx.left}

lemma union_dS_wt_subset_of_subset
  (C₁ C₂ : finset (vector B n)) (H : C₁ ⊆ C₂) (w : ℕ) :
  union_dS_wt C₁ w ⊆ union_dS_wt C₂ w :=
begin
intros x hx, rw mem_union_dS_wt at hx, rw mem_union_dS_wt,
apply and.intro (union_dS_subset_of_subset _ _ H hx.left) hx.right
end

lemma union_dS_wt_union
  (C₁ C₂ : finset (vector B n)) (w : ℕ):
  union_dS_wt (C₁ ∪ C₂) w = union_dS_wt C₁ w ∪ union_dS_wt C₂ w :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_union_dS_wt at hx,
   rw union_dS_union at hx, rw mem_union at hx, cases hx.left,
    {rw mem_union, left, rw mem_union_dS_wt,
     apply and.intro h hx.right},
    {rw mem_union, right, rw mem_union_dS_wt,
     apply and.intro h hx.right}},
  {apply union_subset,
    {apply union_dS_wt_subset_of_subset, apply subset_union_left},
    {apply union_dS_wt_subset_of_subset, apply subset_union_right}}
end

def Cwr
  (C : finset (vector B n)) (w r : ℕ) : finset (vector B n) :=
  filter (λ X, card (dS_wt X w) = r) C

lemma mem_Cwr (C : finset (vector B n)) (w r : ℕ) (X : vector B n) :
  X ∈ Cwr C w r ↔ X ∈ C ∧ card (dS_wt X w) = r :=
by {unfold Cwr, rw mem_filter}

lemma not_mem_Cwr
  (C : finset (vector B n)) (w r : ℕ) (X : vector B n) (Hx : X ∉ C) :
  X ∉ Cwr C w r :=
by {unfold Cwr, apply not_mem_filter C _ X Hx}

lemma Cwr_empty (w r : ℕ) :
  Cwr (∅ : finset (vector B n)) w r = ∅ :=
by {unfold Cwr, rw filter_empty}

lemma Cwr_subset (C : finset (vector B n)) (w r : ℕ) :
  Cwr C w r ⊆ C :=
by {intros x hx, rw mem_Cwr at hx, apply hx.left}

lemma Cwr_subset_of_subset
  {C₁ C₂ : finset (vector B n)} (H : C₁ ⊆ C₂) (w r : ℕ)  :
  Cwr C₁ w r ⊆ Cwr C₂ w r :=
by {unfold Cwr, apply filter_subset_filter H}

lemma DelCode_Cwr
  (C : finset (vector B n)) (HC : is_DelCode C) (w r : ℕ) :
  is_DelCode (Cwr C w r) :=
by apply DelCode_subset _ _ HC (Cwr_subset _ _ _)

lemma Cwr_insert_of_eq
  (C : finset (vector B n)) (w r : ℕ) (X : vector B n)
  (H : card (dS_wt X w) = r) :
  Cwr (insert X C) w r = insert X (Cwr C w r) :=
by {unfold Cwr, rw filter_insert, rw if_pos H}

lemma Cwr_insert_of_neq
  (C : finset (vector B n)) (w r : ℕ) (X : vector B n)
  (H : card (dS_wt X w) ≠ r)  :
  Cwr (insert X C) w r = Cwr C w r :=
by {unfold Cwr, rw filter_insert, rw if_neg H}

lemma Cwr_inter_of_ne (C : finset (vector B n)) (w r₁ r₂: ℕ) (Hr : r₁ ≠ r₂):
  Cwr C w r₁ ∩ Cwr C w r₂ = ∅  :=
begin
unfold Cwr, rw ← filter_and,
apply subset.antisymm,
  {intros x hx, repeat {rw mem_filter at hx},
   have h : r₁ = r₂,
    {rw ← hx.right.left, rw ← hx.right.right},
   contradiction},
  {apply empty_subset}
end

lemma card_union_dS_wt_Cwr_zero (C : finset (vector B n)) (w : ℕ) :
  card (union_dS_wt (Cwr C w 0) w) = 0 :=
begin
induction C using finset.induction with s S hs ihS,
  {rw Cwr_empty, rw union_dS_wt_empty, rw card_empty},
  {cases decidable.em (card (dS_wt s w) = 0) with heq hneq,
    {rw Cwr_insert_of_eq S w 0 s heq,
     rw union_dS_wt_insert _ _ _ (not_mem_Cwr _ _ _ _ hs),
     apply eq_zero_of_le_zero, apply le_trans,
      {apply card_union_le},
      {rw heq, rw nat.zero_add, rw ihS}},
    {rw Cwr_insert_of_neq S w 0 s hneq, apply ihS}}
end

lemma card_union_dS_wt_Cwr (C : finset (vector B n)) (HC : is_DelCode C) (w r : ℕ) :
  card (union_dS_wt (Cwr C w r) w) = r * card (Cwr C w r) :=
begin
induction C using finset.induction with s S hs ihS,
  {rw Cwr_empty, rw union_dS_wt_empty, rw card_empty,
   rw card_empty, rw mul_zero},
  {rw DelCode_insert_iff' _ _ hs at HC,
   cases decidable.em (card (filter (λ y, wt y = w) (dS s)) = r) with heq hneq,
    {rw Cwr_insert_of_eq S w r s heq,
     rw union_dS_wt_insert _ _ _ (not_mem_Cwr _ _ _ _ hs),
     rw card_union_of_disjoint,
      {unfold dS_wt, rw heq, rw ihS HC.left,
       rw card_insert_of_not_mem (not_mem_Cwr _ _ _ _ hs),
       rw mul_succ, rw add_comm},
      {apply inter_eq_empty _ _ HC.right,
        {apply dS_wt_subset},
        {apply subset.trans,
          {apply union_dS_wt_subset},
          {apply union_dS_subset_of_subset _ _ (Cwr_subset _ _ _)}}}},
      {rw Cwr_insert_of_neq S w r s hneq, apply ihS HC.left}}
end

def mul_card_dS_wt (C : finset (vector B n)) (w r : ℕ) :=
  r * (card (Cwr C w r))

lemma mul_card_dS_wt_empty (w r : ℕ) :
  mul_card_dS_wt (∅ : finset (vector B n)) w r = 0 :=
by {unfold mul_card_dS_wt, rw Cwr_empty, rw card_empty, rw mul_zero}

lemma mul_card_dS_wt_zero (C : finset (vector B n)) (w : ℕ):
  mul_card_dS_wt C w 0 = 0 :=
by {unfold mul_card_dS_wt, rw zero_mul}

lemma mul_card_dS_wt_eq (C : finset (vector B n)) (HC : is_DelCode C) (w r : ℕ) :
  mul_card_dS_wt C w r = card (union_dS_wt (Cwr C w r) w) :=
by {unfold mul_card_dS_wt, rw ← card_union_dS_wt_Cwr _ HC}

def Cwr_le (C : finset (vector B n)) (w r : ℕ) : finset (vector B n) :=
  filter (λ X, card (dS_wt X w) ≤ r) C

lemma mem_Cwr_le (C : finset (vector B n)) (w r : ℕ) (X : vector B n) :
  X ∈ Cwr_le C w r ↔ X ∈ C ∧ card (dS_wt X w) ≤ r :=
by {unfold Cwr_le, rw mem_filter}

lemma not_mem_Cwr_le
  (C : finset (vector B n)) (w r : ℕ) (X : vector B n) (HX : X ∉ C) :
  X ∉ Cwr_le C w r :=
by {unfold Cwr_le, apply not_mem_filter C _ X HX}

lemma Cwr_le_empty (w r : ℕ) :
  Cwr_le (∅ : finset (vector B n)) w r = ∅ :=
by {unfold Cwr_le, rw filter_empty}

lemma Cwr_le_zero (C : finset (vector B n)) (w : ℕ) :
  Cwr_le C w 0 = Cwr C w 0 :=
by {unfold Cwr_le, unfold Cwr, congr, ext, rw le_zero_iff}

lemma Cwr_le_subset (C : finset (vector B n)) (w r : ℕ) :
  Cwr_le C w r ⊆ C :=
by {intros x hx, rw mem_Cwr_le at hx, apply hx.left}

lemma Cwr_subset_le (C : finset (vector B n)) (w r : ℕ) :
  Cwr C w r ⊆ Cwr_le C w r :=
begin
intros x hx, rw mem_Cwr at hx,
rw mem_Cwr_le, apply and.intro hx.left (le_of_eq hx.right)
end

lemma DelCode_Cwr_le
  (C : finset (vector B n)) (HC : is_DelCode C) (w r : ℕ) :
  is_DelCode (Cwr_le C w r) :=
by apply DelCode_subset _ _ HC (Cwr_le_subset _ _ _)

lemma Cwr_le_insert_of_le
  (C : finset (vector B n)) (w r : ℕ) (X : vector B n)
  (H : card (dS_wt X w) ≤ r) :
  Cwr_le (insert X C) w r = insert X (Cwr_le C w r) :=
by {unfold Cwr_le, rw filter_insert, rw if_pos H}

lemma Cwr_le_insert_of_gt
  (C : finset (vector B n)) (w r : ℕ) (X : vector B n)
  (H : r < card (dS_wt X w)) :
  Cwr_le (insert X C) w r = Cwr_le C w r :=
by {unfold Cwr_le, rw filter_insert, rw if_neg (not_le_of_gt H)}

lemma Cwr_le_succ (C : finset (vector B n)) (w r : ℕ) :
  Cwr_le C w (r + 1) = Cwr_le C w r ∪ Cwr C w (r + 1) :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_Cwr_le at hx,
   cases lt_or_eq_of_le hx.right,
    {rw mem_union, left, rw mem_Cwr_le,
     apply and.intro hx.left (le_of_lt_succ h)},
    {rw mem_union, right, rw mem_Cwr,
     apply and.intro hx.left h}},
  {intros x hx, rw mem_union at hx, cases hx,
    {rw mem_Cwr_le at hx, rw mem_Cwr_le,
     apply and.intro hx.left (le_succ_of_le hx.right)},
    {rw mem_Cwr at hx, rw mem_Cwr_le,
     apply and.intro hx.left (le_of_eq hx.right)}}
end

lemma Cwr_le_inter_eq (C : finset (vector B n)) (w r : ℕ) :
  Cwr_le C w r ∩ Cwr C w (r + 1) = ∅ :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_inter at hx,
   rw mem_Cwr_le at hx, rw mem_Cwr at hx,
   apply absurd hx.right.right,
   apply nat.ne_of_lt (lt_succ_of_le hx.left.right)},
  {apply empty_subset}
end

lemma card_Cwr_le_succ (C : finset (vector B n)) (w r : ℕ) :
  card (Cwr_le C w (r + 1)) = card (Cwr_le C w r) + card (Cwr C w (r + 1)) :=
by {rw Cwr_le_succ, rw card_union_of_disjoint, apply Cwr_le_inter_eq}

lemma Cwr_le_length (C : finset (vector B n)) (w : ℕ):
  Cwr_le C w (n - 1 + 1) = C :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_Cwr_le at hx, apply hx.left},
  {intros x hx, rw mem_Cwr_le, apply and.intro,
    {apply hx},
    {apply le_trans,
      {apply card_filter_le},
      {apply card_dS}}}
end

lemma card_union_dS_wt_Cwr_le_zero (C : finset (vector B n)) (w : ℕ) :
  card (union_dS_wt (Cwr_le C w 0) w) = 0 :=
by {rw Cwr_le_zero, rw card_union_dS_wt_Cwr_zero C w}

def mul_card_dS_wt_le : finset (vector B n) → ℕ → ℕ → ℕ
| C w 0       := mul_card_dS_wt C w 0
| C w (k + 1) := mul_card_dS_wt C w (k + 1) + mul_card_dS_wt_le C w k

lemma mul_card_dS_wt_le_empty (w r : ℕ) :
  mul_card_dS_wt_le (∅ : finset (vector B n)) w r = 0 :=
begin
induction r with r ihr,
  {unfold mul_card_dS_wt_le, rw mul_card_dS_wt_empty},
  {unfold mul_card_dS_wt_le, rw mul_card_dS_wt_empty, rw zero_add, rw ihr}
end

lemma mul_card_dS_wt_le_zero (C : finset (vector B n)) (w : ℕ):
  mul_card_dS_wt_le C w 0 = 0 :=
by {unfold mul_card_dS_wt_le, rw mul_card_dS_wt_zero}

lemma mul_card_dS_wt_le_insert_of_gt
  (C : finset (vector B n)) (w r : ℕ)
  (x : vector B n) (Hr : r < card (dS_wt x w)) :
  mul_card_dS_wt_le (insert x C) w r = mul_card_dS_wt_le C w r :=
begin
induction r with r ihr,
  {repeat {rw mul_card_dS_wt_le_zero}},
  {unfold mul_card_dS_wt_le, unfold mul_card_dS_wt,
   rw Cwr_insert_of_neq,
    {rw ihr (lt_of_le_of_lt (le_succ r) Hr)},
    {apply ne.symm (nat.ne_of_lt Hr)}}
end

lemma mul_card_dS_wt_le_insert_of_le
  (C : finset (vector B n)) (w r : ℕ)
  (x : vector B n) (Hx : x ∉ C) (Hr : card (dS_wt x w) ≤ r) :
  mul_card_dS_wt_le (insert x C) w r
  = mul_card_dS_wt_le C w r + card (dS_wt x w) :=
begin
induction r with r ihr,
  {repeat {rw mul_card_dS_wt_le_zero}, rw eq_zero_of_le_zero Hr},
  {unfold mul_card_dS_wt_le, unfold mul_card_dS_wt,
   cases eq_or_lt_of_le Hr with heq hlt,
    {rw Cwr_insert_of_eq C w (r + 1) x heq,
     rw card_insert_of_not_mem,
      {rw mul_succ, rw add_right_comm,
       rw mul_card_dS_wt_le_insert_of_gt,
        {rw heq},
        {rw heq, apply lt_succ_self}},
      {apply not_mem_Cwr C w (r + 1) x Hx}},
    {rw Cwr_insert_of_neq,
      {rw ihr (le_of_lt_succ hlt), rw add_assoc},
      {apply nat.ne_of_lt hlt}}}
end

lemma mul_card_dS_wt_le_eq
  (C : finset (vector B n)) (HC : is_DelCode C) (w r : ℕ) :
  mul_card_dS_wt_le C w r = card (union_dS_wt (Cwr_le C w r) w) :=
begin
induction r with r ihr,
  {rw mul_card_dS_wt_le_zero,
   rw card_union_dS_wt_Cwr_le_zero C},
  {unfold mul_card_dS_wt_le,
   rw mul_card_dS_wt_eq _ HC, rw ihr,
   rw Cwr_le_succ, rw union_dS_wt_union,
   rw card_union_of_disjoint,
    {rw add_comm},
    {rw ← subset_empty, apply subset.trans,
      {apply inter_subset_inter,
        {apply union_dS_wt_subset},
        {apply union_dS_wt_subset}},
      {rw union_dS_inter_of_DelCode HC,
        {refl},
        {apply Cwr_le_subset _ _ _},
        {apply Cwr_subset _ _ _},
        {apply Cwr_le_inter_eq}}}}
end

lemma mul_card_dS_wt_le_le
  (C : finset (vector B n)) (w r : ℕ) :
  mul_card_dS_wt_le C w r ≤ mul_card_dS_wt_le C w (n - 1 + 1) :=
begin
induction C using finset.induction with c C hc ihC,
  {rw mul_card_dS_wt_le_empty, apply nat.zero_le},
  {cases decidable.em (card (dS_wt c w) ≤ r) with hge hnge,
    {rw mul_card_dS_wt_le_insert_of_le _ _ _ _ hc hge,
     rw mul_card_dS_wt_le_insert_of_le _ _ _ _ hc,
      {apply add_le_add_right, apply ihC},
      {apply le_trans,
        {apply card_le_of_subset, apply dS_wt_subset},
        {apply card_dS}}},
    {rw mul_card_dS_wt_le_insert_of_gt _ _ _ _ (lt_of_not_ge hnge),
     rw mul_card_dS_wt_le_insert_of_le _ _ _ _ hc,
      {apply le_trans ihC (le_add_right (refl _))},
      {apply le_trans,
        {apply card_le_of_subset, apply dS_wt_subset},
        {apply card_dS}}}}
end

lemma mul_card_dS_wt_le_length
  (C : finset (vector B n)) (HC : is_DelCode C) (w r : ℕ) :
  mul_card_dS_wt_le C w (n - 1 + 1) = card (union_dS_wt C w) :=
by {rw mul_card_dS_wt_le_eq C HC, rw Cwr_le_length }

lemma mul_card_dS_wt_le_card_univ
  {n : ℕ} (C : finset (vector B n)) (HC : is_DelCode C) (w r : ℕ) :
  mul_card_dS_wt_le C w r ≤ card (filter (λ x : vector B (n - 1), wt x = w) univ) :=
begin
rw mul_card_dS_wt_le_eq C HC,
apply card_le_of_subset, unfold union_dS_wt,
apply filter_subset_filter, apply subset_univ
end

lemma mul_card_dS_wt_le_card_univ'
  {n : ℕ} (C : finset (vector B n)) (HC : is_DelCode C) (w : ℕ) :
  mul_card_dS_wt_le C w n ≤ card (filter (λ x : vector B (n - 1), wt x = w) univ) :=
by {apply mul_card_dS_wt_le_card_univ _ HC}

def Cwr_ge (C : finset (vector B n)) (w r : ℕ) : finset (vector B n) :=
  filter (λ X, r ≤ card (dS_wt X w)) C

lemma mem_Cwr_ge (C : finset (vector B n)) (w r : ℕ) (X : vector B n) :
  X ∈ Cwr_ge C w r ↔ X ∈ C ∧ r ≤ card (dS_wt X w) :=
by {unfold Cwr_ge, rw mem_filter}

lemma Cwr_ge_empty (w r : ℕ) :
  Cwr_ge (∅ : finset (vector B n)) w r = ∅ :=
by {unfold Cwr_ge, rw filter_empty}

lemma Cwr_ge_insert_of_ge
  (C : finset (vector B n)) (w r : ℕ) (X : vector B n)
  (H : r ≤ card (dS_wt X w)) :
  Cwr_ge (insert X C) w r = insert X (Cwr_ge C w r) :=
by {unfold Cwr_ge, rw filter_insert, rw if_pos H}

lemma Cwr_ge_insert_of_lt
  (C : finset (vector B n)) (w r : ℕ) (X : vector B n)
  (H : card (dS_wt X w) < r) :
  Cwr_ge (insert X C) w r = Cwr_ge C w r :=
by {unfold Cwr_ge, rw filter_insert, rw if_neg (not_le_of_gt H)}

lemma Cwr_ge_subset
  (C : finset (vector B n)) (w r : ℕ) :
  Cwr_ge C w r ⊆ C :=
by {unfold Cwr_ge, apply filter_subset}

lemma Cwr_ge_subset_of_subset
  {C₁ C₂ : finset (vector B n)} (H : C₁ ⊆ C₂) (w r : ℕ)  :
  Cwr_ge C₁ w r ⊆ Cwr_ge C₂ w r :=
by {unfold Cwr_ge, apply filter_subset_filter H}

lemma Cwr_ge_zero (C : finset (vector B n)) (w : ℕ) :
  Cwr_ge C w 0 = C :=
begin
apply subset.antisymm,
  {apply Cwr_ge_subset},
  {intros x hx, rw Cwr_ge,
   rw mem_filter, apply and.intro hx (nat.zero_le _)}
end

lemma DelCode_Cwr_ge
  (C : finset (vector B n)) (HC : is_DelCode C) (w r : ℕ) :
  is_DelCode (Cwr_ge C w r) :=
by {unfold Cwr_ge, apply DelCode_filter _ HC}

lemma Cwr_ge_eq
  (C : finset (vector B n)) (w r : ℕ) :
  Cwr_ge C w r = Cwr C w r ∪ Cwr_ge C w (r + 1) :=
begin
unfold Cwr_ge, unfold Cwr, rw ← filter_or,
congr, ext, apply iff.intro,
  {intro h, cases eq_or_lt_of_le h with heq hlt,
    {left, rw heq},
    {right, apply succ_le_of_lt hlt}},
  {intro h, cases h with heq hle,
    {rw heq},
    {apply le_of_succ_le hle}}
end

lemma Cwr_subset_ge
  (C : finset (vector B n)) (w r : ℕ) :
  Cwr C w r ⊆ Cwr_ge C w r :=
by {rw Cwr_ge_eq, apply subset_union_left}

lemma Cwr_le_union_ge (C : finset (vector B n)) (w r : ℕ) :
  Cwr_le C w r ∪ Cwr_ge C w (r + 1) = C :=
begin
apply subset.antisymm,
  {apply union_subset,
    {apply Cwr_le_subset},
    {apply Cwr_ge_subset}},
  {intros x hx,
   cases decidable.em(card (dS_wt x w) ≤ r) with hle hnle,
    {rw mem_union, left, rw mem_Cwr_le, apply and.intro hx hle},
    {rw mem_union, right, rw mem_Cwr_ge,
     apply and.intro hx, apply succ_le_of_lt (lt_of_not_ge hnle)}}
end

lemma Cwr_le_inter_ge (C : finset (vector B n)) (w r : ℕ) :
  Cwr_le C w r ∩ Cwr_ge C w (r + 1) = ∅ :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_inter at hx,
   rw mem_Cwr_le at hx,
   rw mem_Cwr_ge at hx,
   apply absurd hx.left.right,
   rw not_le, apply lt_of_succ_le hx.right.right},
  {apply empty_subset}
end

lemma Cwr_ge_succ_eq_sdiff_le (C : finset (vector B n)) (w r : ℕ) :
  Cwr_ge C w (r + 1) = C \ Cwr_le C w r :=
begin
rw ← Cwr_le_union_ge C, rw union_sdiff_distrib,
rw Cwr_le_union_ge C, rw sdiff_self, rw empty_union,
rw sdiff_of_disjoint, rw inter_comm, apply Cwr_le_inter_ge
end

lemma card_Cwr_le_add_ge (C : finset (vector B n)) (w r : ℕ) :
  card (Cwr_le C w r) + card (Cwr_ge C w (r + 1)) = card C :=
begin
rw ← card_union_of_disjoint,
  {rw Cwr_le_union_ge},
  {rw Cwr_le_inter_ge}
end

def mul_card_dS_wt_ge (C : finset (vector B n)) (w r : ℕ) : ℕ :=
  mul_card_dS_wt_le C w (n - 1 + 1) - mul_card_dS_wt_le C w (r - 1)

lemma mul_card_dS_wt_ge_empty (w r : ℕ) :
  mul_card_dS_wt_ge (∅ : finset (vector B n)) w r = 0 :=
by {unfold mul_card_dS_wt_ge, repeat {rw mul_card_dS_wt_le_empty}}

lemma mul_card_dS_wt_ge_zero (C : finset (vector B n)) (w : ℕ) :
  mul_card_dS_wt_ge C w 0 = mul_card_dS_wt_le C w (n - 1 + 1) :=
by {unfold mul_card_dS_wt_ge, rw mul_card_dS_wt_le_zero, rw nat.sub_zero}

lemma mul_card_dS_wt_ge_insert_of_lt
  (C : finset (vector B n)) (w r : ℕ)
  (x : vector B n) (Hr : card (dS_wt x w) < r) :
  mul_card_dS_wt_ge (insert x C) w r = mul_card_dS_wt_ge C w r :=
begin
cases decidable.em (x ∈ C) with hin hnin,
  {rw insert_eq_of_mem hin},
  {unfold mul_card_dS_wt_ge,
   rw mul_card_dS_wt_le_insert_of_le _ _ _ _ hnin,
    {rw mul_card_dS_wt_le_insert_of_le _ _ _ _ hnin,
      {rw nat.add_sub_add_right},
      {apply le_of_lt_succ, apply lt_of_lt_of_le Hr, cases r,
        {apply nat.zero_le},
        {rw succ_sub_one}}},
    {apply le_trans (card_le_of_subset (filter_subset _)) (vector.card_dS _)}}
end

lemma mul_card_dS_wt_ge_insert_of_ge
  (C : finset (vector B n)) (w r : ℕ)
  (x : vector B n) (Hx : x ∉ C) (Hr : r ≤ card (dS_wt x w)) :
  mul_card_dS_wt_ge (insert x C) w r
  = mul_card_dS_wt_ge C w r + card (dS_wt x w)  :=
begin
cases r,
  {repeat {rw mul_card_dS_wt_ge_zero},
   rw mul_card_dS_wt_le_insert_of_le _ _ _ _ Hx,
   apply le_trans (card_le_of_subset (filter_subset _)) (card_dS _)},
  {unfold mul_card_dS_wt_ge,
   rw mul_card_dS_wt_le_insert_of_le _ _ _ _ Hx,
    {rw succ_sub_one, rw mul_card_dS_wt_le_insert_of_gt _ _ r,
      {rw add_comm, rw nat.add_sub_assoc,
         {rw add_comm},
         {apply mul_card_dS_wt_le_le}},
      {apply lt_of_succ_le Hr}},
    {apply le_trans (card_le_of_subset (filter_subset _)) (card_dS _)}}
end

lemma card_dS_wt_ge_le (C : finset (vector B n)) (w r : ℕ) :
  r * card (Cwr_ge C w r) ≤ mul_card_dS_wt_ge C w r :=
begin
induction C using finset.induction with c C hc ihC,
  {rw Cwr_ge_empty, rw card_empty, rw mul_zero, apply nat.zero_le},
  {cases decidable.em(r ≤ card (dS_wt c w)) with hle hnle,
    {rw Cwr_ge_insert_of_ge _ _ _ _ hle,
     rw card_insert_of_not_mem,
      {rw mul_succ, rw mul_card_dS_wt_ge_insert_of_ge _ _ _ _ hc hle,
       apply add_le_add ihC hle},
      {unfold Cwr_ge, apply not_mem_filter _ _ _ hc}},
    {rw Cwr_ge_insert_of_lt _ _ _ _ (lt_of_not_ge hnle),
     rw mul_card_dS_wt_ge_insert_of_lt _ _ _ _ (lt_of_not_ge hnle),
     apply ihC}}
end

lemma card_dS_wt_ge_le_univ
  (C : finset (vector B n)) (H : is_DelCode C) (w r : ℕ) :
  card (Cwr_ge C w (r + 1))
  ≤ (card (filter (λ x : vector B (n - 1), wt x = w) univ)
    - mul_card_dS_wt_le C w r) / (r + 1) :=
begin
rw le_div_iff_mul_le' (zero_lt_succ r),
rw mul_comm, apply le_trans,
  {apply card_dS_wt_ge_le},
  {apply nat.le_sub_right_of_add_le,
   unfold mul_card_dS_wt_ge,
   rw succ_sub_one, rw nat.sub_add_cancel,
    {apply mul_card_dS_wt_le_card_univ _ H},
    {apply mul_card_dS_wt_le_le}}
end

lemma card_Cwr_le_1
  (C : finset (vector B n)) (w : ℕ):
  card (Cwr_le C w 1) = card (Cwr C w 0) + card (Cwr C w 1) :=
by {rw card_Cwr_le_succ, rw Cwr_le_zero}

lemma card_Cwr_le_2
  (C : finset (vector B n)) (w : ℕ):
  card (Cwr_le C w 2) = card (Cwr C w 0) + card (Cwr C w 1) + card (Cwr C w 2):=
by {repeat {rw card_Cwr_le_succ}, rw Cwr_le_zero}

lemma mul_card_dS_wt_le_1
  (C : finset (vector B n)) (w : ℕ):
  mul_card_dS_wt_le C w 1 = card (Cwr C w 1) :=
begin
unfold mul_card_dS_wt_le,
rw nat.zero_add, unfold mul_card_dS_wt,
rw one_mul, rw zero_mul, rw nat.add_zero
end

lemma mul_card_dS_wt_le_2
  (C : finset (vector B n)) (w : ℕ):
  mul_card_dS_wt_le C w 2 = 2 * card (Cwr C w 2) + card (Cwr C w 1) :=
by {rw mul_card_dS_wt_le, rw mul_card_dS_wt_le_1, rw mul_card_dS_wt}

lemma card_le_univ_add_1
  {n : ℕ} (C : finset (vector B n)) (HC : is_DelCode C)
  (w : ℕ) (HCw : Cwr C w 0 = ∅) :
  card C ≤ (card (filter (λ x : vector B (n - 1), wt x = w) univ) + card (Cwr C w 1)) / 2 :=
begin
rw le_div_iff_mul_le' (zero_lt_succ 1),
rw ← card_Cwr_le_add_ge C w 1,
rw card_Cwr_le_1, rw HCw, rw card_empty, rw nat.zero_add,
apply nat.le_add_of_sub_le_right,
rw add_mul, rw add_comm, rw mul_two (card (Cwr C w 1)),
rw ← add_assoc, rw nat.add_sub_cancel,
apply le_trans,
  {apply add_le_add_right,
   rw ← le_div_iff_mul_le' (zero_lt_succ 1),
   apply card_dS_wt_ge_le_univ C HC},
  {rw ← mul_card_dS_wt_le_1, rw nat.sub_add_cancel,
   apply mul_card_dS_wt_le_card_univ C HC}
end

lemma card_le_univ_add_2
  {n : ℕ} (C : finset (vector B n)) (HC : is_DelCode C)
  (w : ℕ) (HCw : Cwr C w 0 = ∅) :
  card C ≤ (card (filter (λ x : vector B (n - 1), wt x = w) univ) + 2 * card (Cwr C w 1) + card (Cwr C w 2)) / 3 :=
begin
rw le_div_iff_mul_le' (zero_lt_succ 2),
rw ← card_Cwr_le_add_ge C w 2,
rw add_mul, rw add_comm,
apply nat.le_add_of_sub_le_right,
rw mul_succ (card (Cwr_le C w 2)),
rw card_Cwr_le_2, rw HCw, rw card_empty, rw zero_add,
repeat {rw ← add_assoc}, rw nat.add_sub_cancel,
apply nat.le_add_of_sub_le_right,
rw add_right_comm, rw add_comm (card (Cwr C w 1)),
rw add_mul, rw mul_comm (card (Cwr C w 1)),
repeat {rw ← add_assoc}, rw nat.add_sub_cancel,
rw add_assoc, apply le_trans,
  {apply add_le_add_right,
   rw ← le_div_iff_mul_le' (zero_lt_succ 2),
   apply card_dS_wt_ge_le_univ C HC},
  {rw add_comm (card (Cwr C w 1)),
   rw mul_comm, rw ← mul_card_dS_wt_le_2, rw nat.sub_add_cancel,
   apply mul_card_dS_wt_le_card_univ C HC}
end

end B

variable [fintype α]
variable S : finset (vector α n)

def DCs (n :  ℕ) : finset (finset (vector α n)) :=
  filter is_DelCode (powerset univ)

lemma mem_DCs :
  C ∈ @DCs α _ _ n ↔ is_DelCode C :=
begin
unfold DCs, rw mem_filter, rw mem_powerset,
apply iff.intro,
    {intro h, apply h.right},
    {intro h, apply and.intro (subset_univ C) h}
end

def DCs' (n :  ℕ) : finset (finset (vector α n)) :=
  filter is_DelCode' (powerset univ)

lemma DCs'_eq :
  @DCs' α _ _ n = @DCs α _ _ n :=
by {unfold DCs, unfold DCs', congr, ext, rw DelCode'_iff}

def DCs_sub : finset (finset (vector α n)) :=
  filter is_DelCode (powerset S)

lemma mem_DCs_sub :
  C ∈ DCs_sub S ↔ C ⊆ S ∧ is_DelCode C :=
by {unfold DCs_sub, rw mem_filter, rw mem_powerset}

lemma DCs_sub_empty :
  @DCs_sub α _ n _ ∅ = finset.singleton ∅ :=
begin
ext, apply iff.intro,
  {intros h, rw mem_DCs_sub at h,
   rw mem_singleton, rw subset_empty at h, apply h.left},
  {intros h, rw mem_singleton at h,
   rw h, rw mem_DCs_sub, apply and.intro (subset.refl _) (DelCode_empty)}
end

lemma DCs_sub_univ :
  @DCs_sub α _ _ _ univ = DCs n :=
by trivial

lemma DCs_sub_subset
  {S₁ S₂ : finset (vector α n)} (HS : S₁ ⊆ S₂) :
  DCs_sub S₁ ⊆ DCs_sub S₂ :=
begin
intros S hS, rw mem_DCs_sub at hS, rw mem_DCs_sub,
apply and.intro (subset.trans hS.left HS) hS.right
end

def DCs_sub' : finset (finset (vector α n)) :=
  filter is_DelCode' (powerset S)

lemma DCs_sub'_eq :
  DCs_sub' S = DCs_sub S :=
by {unfold DCs_sub', unfold DCs_sub, congr, ext, rw DelCode'_iff}

def DCs_sub_len (S : finset (vector α n)) (k : ℕ) : finset (finset (vector α n)) :=
  filter is_DelCode (powerset_len k S)

lemma mem_DCs_sub_len (k : ℕ) :
  C ∈ DCs_sub_len S k ↔ C ⊆ S ∧ card C = k ∧ is_DelCode C :=
begin
unfold DCs_sub_len, rw mem_filter,
rw mem_powerset_len, apply and_assoc
end

lemma mem_DCs_sub_len' (S : finset (vector α n)) (k : ℕ) :
  C ∈ DCs_sub_len S k ↔ C ∈ DCs_sub S ∧ card C = k :=
by {rw mem_DCs_sub_len, rw mem_DCs_sub, rw and.right_comm, rw and_assoc}

def DCs_sub_len' (S : finset (vector α n)) (k : ℕ) : finset (finset (vector α n)) :=
  filter is_DelCode' (powerset_len k S)

lemma DCs_sub_len'_eq (S : finset (vector α n)) (k : ℕ) :
  DCs_sub_len' S k = DCs_sub_len S k :=
by {unfold DCs_sub_len', unfold DCs_sub_len, congr, ext, rw DelCode'_iff}

namespace B

def DCs_sub_DC_len_succ
  (S : finset (vector B n)) (C : finset (vector B n)) : finset (finset (vector B n)) :=
  image (λ x, insert x C) (S \ union_dB C)

lemma mem_DCs_sub_DC_len_succ
  (S : finset (vector B n)) (C : finset (vector B n)) (C' : finset (vector B n)) :
  C' ∈ DCs_sub_DC_len_succ S C ↔ ∃ c ∈ S \ union_dB C, insert c C = C' :=
by {unfold DCs_sub_DC_len_succ, rw mem_image}

def DCs_sub_DCs_len_succ
  (S : finset (vector B n)) (Cs : finset (finset (vector B n))) : finset (finset (vector B n)) :=
  fold (∪) ∅ (λ C, DCs_sub_DC_len_succ S C) Cs

lemma mem_DCs_sub_DCs_len_succ
  (S : finset (vector B n)) (Cs : finset (finset (vector B n))) (C' : finset (vector B n)) :
  C' ∈ DCs_sub_DCs_len_succ S Cs ↔ ∃ C ∈ Cs, C' ∈ DCs_sub_DC_len_succ S C :=
by {unfold DCs_sub_DCs_len_succ, apply mem_fold_union}

lemma mem_DCs_sub_DCs_len_succ'
  (S : finset (vector B n)) (Cs : finset (finset (vector B n))) (C' : finset (vector B n)) :
  C' ∈ DCs_sub_DCs_len_succ S Cs ↔ ∃ C ∈ Cs, ∃ c ∈ S \ union_dB C, insert c C = C' :=
begin
rw mem_DCs_sub_DCs_len_succ, apply iff.intro,
  {intro h, cases h with C hC, cases hC with hC hCC',
   rw mem_DCs_sub_DC_len_succ at hCC',
   apply exists.intro C, apply exists.intro hC, apply hCC'},
  {intro h, cases h with C hC, cases hC with hC hCC',
   rw ← mem_DCs_sub_DC_len_succ at hCC',
   apply exists.intro C, apply exists.intro hC, apply hCC'}
end

lemma DCs_sub_DCs_len_succ_eq
  (S : finset (vector B n)) (k : ℕ) :
  DCs_sub_DCs_len_succ S (DCs_sub_len S k) = DCs_sub_len S (k + 1) :=
begin
apply subset.antisymm,
  {intros C hC, rw mem_DCs_sub_DCs_len_succ' at hC,
   cases hC with C' hC', cases hC' with hC' hCC',
   cases hCC' with c hc, cases hc with hc hCC'c,
   rw mem_DCs_sub_len at hC', rw mem_sdiff at hc,
   rw ← hCC'c, rw mem_DCs_sub_len, apply and.intro,
    {rw insert_subset, apply and.intro hc.left hC'.left},
    {apply and.intro,
      {rw card_insert_of_not_mem,
        {rw hC'.right.left},
        {apply not_mem_of_not_mem_dB C' c hc.right}},
      {rw DelCode_insert_iff_not_mem_dB,
        {apply and.intro hC'.right.right hc.right},
        {apply not_mem_of_not_mem_dB C' c hc.right}}}},
  {intros C hC, rw mem_DCs_sub_len at hC,
   cases exists_mem_of_card C _ with c hc,
    {rw mem_DCs_sub_DCs_len_succ',
     apply exists.intro (erase C c), apply exists.intro,
      {rw mem_DCs_sub_len, apply and.intro,
        {apply subset.trans (erase_subset _ _) hC.left},
        {apply and.intro,
          {rw card_erase_of_mem hc, rw hC.right.left, rw pred_succ},
          {apply DelCode_erase _ _ hC.right.right}}},
      {apply exists.intro c, apply exists.intro,
        {rw mem_sdiff, apply and.intro,
          {apply hC.left hc},
          {apply not_mem_union_dB_erase hC.right.right _ hc}},
        {rw insert_erase hc}}},
    {rw hC.right.left, apply succ_ne_zero}}
end

end B
