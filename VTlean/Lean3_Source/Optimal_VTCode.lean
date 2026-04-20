import .Optimal .VTCode

open nat finset B B.finset

namespace length1

lemma optimal_VTCode_1_0 :
  is_optimal (VTCode 1 0) (DelCode_VTCode 1 0) := dec_trivial

end length1

namespace length2

lemma optimal_VTCode_2_0 :
  is_optimal (VTCode 2 0) (DelCode_VTCode 2 0) := dec_trivial

end length2


namespace length3

lemma optimal_VTCode_3_0 :
  is_optimal (VTCode 3 0) (DelCode_VTCode 3 0) := dec_trivial

end length3

namespace length4

def W2 : finset (vector B 4) :=
{⟨[I, I, O, O], rfl⟩, ⟨[I, O, O, I], rfl⟩, ⟨[O, I, I, O], rfl⟩, ⟨[O, O, I, I], rfl⟩}

lemma W2_eq : W2 = W22 4 \ Repl 4 := rfl

lemma DCs_sub_W2_len3' : DCs_sub_len' W2 3 = ∅ := rfl

lemma DCs_sub_W2_len3 : DCs_sub_len W2 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_W2_len3'}

lemma card_le_of_sub_W2
  (C : finset (vector B 4)) (HS : C ⊆ W2) (HC : is_DelCode C) : 
  card C ≤ 2 :=
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_W2_len3 _ HS HC

lemma optimal_of_card
  (C : finset (vector B 4)) (HC : is_DelCode C) (H : card C = 4) :
  is_optimal C HC :=
begin
rw optimal_iff_W22_sdiff_Repl (refl _) _ HC,
rw H, rw ← W2_eq, apply card_le_of_sub_W2
end

lemma card_VTCode_4_0 : card (VTCode 4 0) = 4 := rfl

lemma optimal_VTCode_4_0 : 
  is_optimal (VTCode 4 0) (DelCode_VTCode 4 0) := 
by {apply optimal_of_card, rw card_VTCode_4_0}

end length4

namespace length5

def W23 : finset (vector B 5) :=
{⟨[I, I, I, O, O], rfl⟩, ⟨[I, I, O, O, I], rfl⟩, ⟨[I, I, O, O, O], rfl⟩, ⟨[I, O, I, I, O], rfl⟩, ⟨[I, O, I, O, I], rfl⟩, ⟨[I, O, O, I, I], rfl⟩, ⟨[I, O, O, I, O], rfl⟩, ⟨[I, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O], rfl⟩, ⟨[O, I, I, O, I], rfl⟩, 
 ⟨[O, I, I, O, O], rfl⟩, ⟨[O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, I], rfl⟩, ⟨[O, O, I, I, I], rfl⟩, ⟨[O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, I], rfl⟩}

lemma W23_eq : W23 = W22 5 \ Repl 5 := rfl

lemma DCs_sub_W23_len5' : DCs_sub_len' W23 5 = ∅ := rfl

lemma DCs_sub_W23_len5 : DCs_sub_len W23 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_W23_len5'}

lemma card_le_of_sub_W23
  (C : finset (vector B 5)) (HS : C ⊆ W23) (HC : is_DelCode C) : 
  card C ≤ 4 :=
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_W23_len5 _ HS HC

lemma optimal_of_card
  (C : finset (vector B 5)) (HC : is_DelCode C) (H : card C = 6) :
  is_optimal C HC :=
begin
rw optimal_iff_W22_sdiff_Repl (le_succ _) _ HC,
rw H, rw ← W23_eq, apply card_le_of_sub_W23
end

lemma card_VTCode_5_0 : card (VTCode 5 0) = 6 := rfl

lemma optimal_VTCode_5_0 : 
  is_optimal (VTCode 5 0) (DelCode_VTCode 5 0) := 
by {apply optimal_of_card, rw card_VTCode_5_0}

end length5


namespace length6

def W24 : finset (vector B 6) :=
{⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, I, I, O, O, O], rfl⟩, ⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, I], rfl⟩, ⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, I], rfl⟩, ⟨[I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, 
 ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, ⟨[I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩, 
 ⟨[I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩, ⟨[O, I, I, I, O, I], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, 
 ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩, ⟨[O, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O], rfl⟩, 
 ⟨[O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩, ⟨[O, O, O, I, I, O], rfl⟩, ⟨[O, O, O, O, I, I], rfl⟩}

lemma W24_eq : W24 = W22 6 \ Repl 6 := rfl

lemma div_wt_of_sub_W24
  (C : finset (vector B 6)) (HC : C ⊆ W24) :
  filter (λ x, wt x = 2) C ∪ filter (Icc_wt 3 4) C = C :=
begin
apply subset.antisymm,
  {apply union_subset,
    {apply filter_subset},
    {apply filter_subset}},
  {intros x hx, repeat {rw mem_union}, 
   have h : x ∈ W24, from HC hx,
   rw W24_eq at h, rw mem_sdiff at h, 
   rw mem_W22 at h, unfold Icc_wt at h, simp at h,
   cases lt_or_eq_of_le h.left.left with hlt2 heq2,
    {right, rw mem_filter, apply and.intro hx,
     apply and.intro (succ_le_of_lt hlt2) h.left.right},
    {left, rw mem_filter, apply and.intro hx heq2.symm}}
end

lemma card_div_wt_of_sub_W24
  (C : finset (vector B 6)) (HC : C ⊆ W24) :
  card (filter (λ x, wt x = 2) C) + card (filter (Icc_wt 3 4) C) = card C :=
begin
rw ← card_union_of_disjoint, 
  {congr, apply div_wt_of_sub_W24 C HC},
  {rw filter_wt_eq_inter_Icc_of_lt _ _ _ _ (refl _)}
end

def W2 : finset (vector B 6) :=
{⟨[I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O], rfl⟩, 
 ⟨[O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O], rfl⟩, ⟨[O, O, O, O, I, I], rfl⟩}

lemma W2_eq : W2 = filter (λ x, wt x = 2) W24 := rfl

lemma DCs_sub_W2_len5' : DCs_sub_len' W2 5 = ∅ := rfl

lemma DCs_sub_W2_len5 : DCs_sub_len W2 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_W2_len5'}

lemma card_le_of_sub_W2
  (C : finset (vector B 6)) (HS : C ⊆ W2) (HC : is_DelCode C) : 
  card C ≤ 4 :=
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_W2_len5 _ HS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 6)) (HS : C ⊆ W24) (HC : is_DelCode C) : 
  card (filter (λ x, wt x = 2) C) ≤ 4 :=
begin
apply card_le_of_sub_W2,
  {rw W2_eq, apply filter_subset_filter HS},
  {apply DelCode_filter _ HC}
end

namespace card4

def DCs_sub_W2_len4 : finset (finset (vector B 6)) :=
{{⟨[I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I], rfl⟩}}

lemma DCs_sub_W2_len4_eq' : DCs_sub_W2_len4 = DCs_sub_len' W2 4 := rfl

lemma DCs_sub_W2_len4_eq : DCs_sub_W2_len4 = DCs_sub_len W2 4 := 
by {rw ← DCs_sub_len'_eq, apply DCs_sub_W2_len4_eq'}

def DC : finset (vector B 6) := 
{⟨[I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I], rfl⟩}

def sdiff_dB : finset (vector B 6) :=
{⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, I], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩, 
 ⟨[O, I, I, I, O, I], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}
 
lemma sdiff_dB_eq : sdiff_dB = W24 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_len5' : DCs_sub_len' sdiff_dB 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_len5 : DCs_sub_len sdiff_dB 5 = ∅ :=
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_len5'}

lemma card_le_of_sub_sdiff_dB
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB) (HC : is_DelCode C) :
  card C ≤ 4 :=
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_len5 _ HCS HC

lemma filter_wt34_subset
  (C : finset (vector B 6)) (HCS : C ⊆ W24) (HC : is_DelCode C) : 
  filter (Icc_wt 3 4) C ⊆ W24 \ union_dB (filter (λ x, wt x = 2) C) :=
begin
intros x hx, rw mem_sdiff, apply and.intro,
  {rw mem_filter at hx, apply HCS hx.left},
  {apply not_mem_union_dB HC _ _ _ x hx,
    {apply @filter_subset _ (Icc_wt 3 4)},
    {apply filter_subset},
    {rw inter_comm, 
     apply filter_wt_eq_inter_Icc_of_lt _ _ _ _ (refl _)}}
end

lemma card_filter_wt34_le_of_sup_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ W24) (HC : is_DelCode C)
  (H : filter (λ x, wt x = 2) C = DC): 
  card (filter (Icc_wt 3 4) C) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB,
  {rw sdiff_dB_eq, rw ← H, apply filter_wt34_subset _ HCS HC},
  {apply DelCode_filter _ HC}
end 

lemma card_filter_wt34_le 
  (C : finset (vector B 6)) (HCS : C ⊆ W24) (HC : is_DelCode C)
  (H : card (filter (λ x, wt x = 2) C) = 4): 
  card (filter (Icc_wt 3 4) C) ≤ 4 :=
begin
have h : filter (λ x, wt x = 2) C ∈ DCs_sub_W2_len4,
  {rw  DCs_sub_W2_len4_eq, rw mem_DCs_sub_len, apply and.intro,
    {rw W2_eq, apply filter_subset_filter, apply HCS},
    {apply and.intro H (DelCode_filter _ HC _)}},
rw DCs_sub_W2_len4 at h, cases h,
  {apply card_filter_wt34_le_of_sup_DC _ HCS HC, rw DC, apply h},
  {apply false.elim h}
end

end card4

def W34 : finset (vector B 6) :=
{⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, I, I, O, O, O], rfl⟩, ⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, I], rfl⟩, ⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, I], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, 
 ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩, ⟨[O, I, I, I, O, I], rfl⟩, 
 ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩, 
 ⟨[O, O, O, I, I, I], rfl⟩}

lemma W34_eq : W34 = filter (Icc_wt 3 4) W24 := rfl

namespace W34

lemma Cwr_W34_3_0 : Cwr W34 3 0 = ∅ := rfl

lemma Cwr_3_0_of_sub_W34 
  (C : finset (vector B 6)) (HC : C ⊆ W34) : 
  Cwr C 3 0 = ∅ :=
begin
unfold Cwr, rw ← subset_empty, 
apply subset.trans,
  {apply Cwr_subset_of_subset HC},
  {rw Cwr_W34_3_0, refl}
end

def Cwr_W34_3_1 : finset (vector B 6) :=
{⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, O, O], rfl⟩, ⟨[I, I, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}

lemma Cwr_W34_3_1_eq : Cwr_W34_3_1  = Cwr W34 3 1 := rfl

def Cwr_W34_3_ge2 : finset (vector B 6) :=
{⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, I], rfl⟩, ⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, I, O, O, I], rfl⟩, 
 ⟨[I, O, O, I, I, I], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, ⟨[O, I, I, I, O, I], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, 
 ⟨[O, O, I, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}

lemma Cwr_W34_3_ge2_eq : Cwr_W34_3_ge2 = Cwr_ge W34 3 2 := rfl

lemma card_wt3_univ :
  card (filter (λ x : vector B 5, wt x = 3) univ) = 10 := rfl

lemma Cwr_union_ge 
  (C : finset (vector B 6)) (H : C ⊆ W34) : 
  Cwr C 3 1 ∪ Cwr_ge C 3 2 = C :=
begin
have h : Cwr_le C 3 1 ∪ Cwr_ge C 3 2 = C, 
  {rw Cwr_le_union_ge C 3 1},
rw Cwr_le_succ at h, 
rw Cwr_le_zero at h, rw Cwr_3_0_of_sub_W34 _ H at h, 
rw empty_union at h, apply h
end

lemma card_Cwr_add_ge 
  (C : finset (vector B 6)) (H : C ⊆ W34) : 
  card (Cwr C 3 1) + card (Cwr_ge C 3 2) = card C :=
begin
have h : card (Cwr_le C 3 1) + card (Cwr_ge C 3 2) = card C, 
  {rw card_Cwr_le_add_ge C 3 1},
rw card_Cwr_le_succ at h, 
rw Cwr_le_zero at h, rw Cwr_3_0_of_sub_W34 _ H at h, 
rw card_empty at h, rw nat.zero_add at h, apply h
end

lemma Cwr_3_ge2_subset 
  (C : finset (vector B 6)) (HCS : C ⊆ W34) (HC : is_DelCode C) : 
  Cwr_ge C 3 2 ⊆ Cwr_W34_3_ge2 \ union_dB (Cwr C 3 1) :=
begin
intros x hx, rw mem_sdiff, apply and.intro,
  {rw Cwr_W34_3_ge2_eq, 
   apply (Cwr_ge_subset_of_subset HCS _ _) hx},
  {apply not_mem_union_dB HC, 
    {apply Cwr_ge_subset _ 3 2},
    {apply Cwr_subset},
    {rw inter_comm, rw ← subset_empty, apply subset.trans, 
      {apply inter_subset_inter_right, apply Cwr_subset_le},
      {rw Cwr_le_inter_ge, refl}},
    {apply hx}}
end

lemma Cwr_3_ge2_mem 
  (C : finset (vector B 6)) (HCS : C ⊆ W34) (HC : is_DelCode C) : 
  Cwr_ge C 3 2 ∈ DCs_sub (Cwr_W34_3_ge2 \ union_dB (Cwr C 3 1)) :=
begin
rw mem_DCs_sub, apply and.intro,
  {apply Cwr_3_ge2_subset _ HCS HC},
  {apply DelCode_Cwr_ge _ HC},
end

lemma DCs_sub_Cwr_W34_3_1_len4' : DCs_sub_len' Cwr_W34_3_1 4 = ∅ := rfl

lemma DCs_sub_Cwr_W34_3_1_len4 : DCs_sub_len Cwr_W34_3_1 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_Cwr_W34_3_1_len4'}

lemma card_le_of_sub_Cwr_W34_3_1 
  (C : finset (vector B 6)) (HCS : C ⊆ Cwr_W34_3_1) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_Cwr_W34_3_1_len4 _ HCS HC

lemma card_Cwr_3_1_le
  (C : finset (vector B 6)) (HCS : C ⊆ W34) (HC : is_DelCode C) : 
  card (Cwr C 3 1) ≤ 3 := 
begin
apply card_le_of_sub_Cwr_W34_3_1,
  {rw Cwr_W34_3_1_eq, apply Cwr_subset_of_subset HCS},
  {apply DelCode_Cwr _ HC}
end

namespace card3

def DCs : finset (finset (vector B 6)) :=
{{⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}}

lemma DCs_eq' : DCs = DCs_sub_len' Cwr_W34_3_1 3 := dec_trivial

lemma DCs_eq : DCs = DCs_sub_len Cwr_W34_3_1 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs_eq'}

def DCs_list : list (finset (vector B 6)) :=
[{⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}]

lemma DCs_list_to_finset : DCs_list.to_finset = DCs := dec_trivial

lemma mem_DCs_list (s : finset (vector B 6)) : 
  s ∈ DCs_list ↔ s ∈ DCs :=
by {rw ← DCs_list_to_finset, rw ← list.mem_to_finset}

namespace DC1 

def DC : finset (vector B 6) :=
{⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC1

namespace DC2 

def DC : finset (vector B 6) :=
{⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[O, I, I, I, O, I], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC2

namespace DC3 

def DC : finset (vector B 6) :=
{⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC3

namespace DC4 

def DC : finset (vector B 6) :=
{⟨[I, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC4

namespace DC5 

def DC : finset (vector B 6) :=
{⟨[I, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC5

namespace DC6 

def DC : finset (vector B 6) :=
{⟨[I, I, I, O, O, O], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, I], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC6

namespace DC7 

def DC : finset (vector B 6) :=
{⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC7

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : card (Cwr C 3 1) = 3) : 
  card (Cwr_ge C 3 2) ≤ 2 :=
begin
have h : Cwr C 3 1 ∈ DCs,
  {rw DCs_eq, rw mem_DCs_sub_len, apply and.intro,
    {rw Cwr_W34_3_1_eq, apply Cwr_subset_of_subset HCS},
    {apply and.intro H (DelCode_Cwr _ HC _ _)}},
rw ← mem_DCs_list at h, rw DCs_list at h, cases h,
  {apply DC1.card_Cwr_ge_le _ HCS HC, rw DC1.DC, rw h},
  {cases h,
    {apply DC2.card_Cwr_ge_le _ HCS HC, rw DC2.DC, rw h},
    {cases h,
      {apply DC3.card_Cwr_ge_le _ HCS HC, rw DC3.DC, rw h},
      {cases h,
        {apply DC4.card_Cwr_ge_le _ HCS HC, rw DC4.DC, rw h},
        {cases h,
          {apply DC5.card_Cwr_ge_le _ HCS HC, rw DC5.DC, rw h},
          {cases h,
            {apply DC6.card_Cwr_ge_le _ HCS HC, rw DC6.DC, rw h},
            {cases h,
              {apply DC7.card_Cwr_ge_le _ HCS HC, rw DC7.DC, rw h},
              {apply false.elim h}}}}}}}
end

end card3

namespace card2

def DCs : finset (finset (vector B 6)) :=
{{⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[O, I, I, I, I, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}}

lemma DCs_eq' : DCs = DCs_sub_len' Cwr_W34_3_1 2 := dec_trivial

lemma DCs_eq : DCs = DCs_sub_len Cwr_W34_3_1 2 := 
by {rw ← DCs_sub_len'_eq, rw DCs_eq'}

def DCs_list : list (finset (vector B 6)) :=
[{⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}, 
 {⟨[O, I, I, I, I, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}]

lemma DCs_list_to_finset : DCs_list.to_finset = DCs := dec_trivial

lemma mem_DCs_list (s : finset (vector B 6)) : 
  s ∈ DCs_list ↔ s ∈ DCs :=
by {rw ← DCs_list_to_finset, rw ← list.mem_to_finset}

namespace DC1 

def DC : finset (vector B 6) :=
{⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[O, I, I, I, O, I], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩, 
 ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC1

namespace DC2 

def DC : finset (vector B 6) :=
{⟨[I, I, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[O, I, I, I, O, I], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩, 
 ⟨[O, O, I, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC2

namespace DC3 

def DC : finset (vector B 6) :=
{⟨[I, I, I, I, O, O], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, I], rfl⟩, ⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, 
 ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC3

namespace DC4 

def DC : finset (vector B 6) :=
{⟨[I, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, I], rfl⟩, ⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, ⟨[O, I, I, I, O, I], rfl⟩, 
 ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC4

namespace DC5 

def DC : finset (vector B 6) :=
{⟨[I, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[O, I, I, I, O, I], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, 
 ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC5

namespace DC6 

def DC : finset (vector B 6) :=
{⟨[I, I, I, O, O, O], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, I], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, 
 ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC6

namespace DC7 

def DC : finset (vector B 6) :=
{⟨[I, I, I, O, O, O], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, I], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, 
 ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC7

namespace DC8 

def DC : finset (vector B 6) :=
{⟨[I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, I], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, 
 ⟨[O, I, I, I, O, I], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC8

namespace DC9 

def DC : finset (vector B 6) :=
{⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC9

namespace DC10 

def DC : finset (vector B 6) :=
{⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, 
 ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC10

namespace DC11 

def DC : finset (vector B 6) :=
{⟨[I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[O, I, I, I, O, I], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, 
 ⟨[O, I, I, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC11

namespace DC12 

def DC : finset (vector B 6) :=
{⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, I, I, I, I, O], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC12

namespace DC13 

def DC : finset (vector B 6) :=
{⟨[I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O], rfl⟩, 
 ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC13

namespace DC14 

def DC : finset (vector B 6) :=
{⟨[O, I, I, I, I, O], rfl⟩, ⟨[O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 6) :=
{⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, I], rfl⟩, ⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, 
 ⟨[I, O, O, I, O, I], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W34_3_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 6)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : Cwr C 3 1 = DC) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw Cwr_W34_3_ge2_eq, rw ← H, 
   apply Cwr_3_ge2_subset C HCS HC},
  {apply DelCode_Cwr_ge C HC}
end

end DC14

lemma card_Cwr_ge_le (C : finset (vector B 6)) 
  (HCS : C ⊆ W34) (HC : is_DelCode C) (H : card (Cwr C 3 1) = 2) : 
  card (Cwr_ge C 3 2) ≤ 3 :=
begin
have h : Cwr C 3 1 ∈ DCs,
  {rw DCs_eq, rw mem_DCs_sub_len, apply and.intro,
    {rw Cwr_W34_3_1_eq, apply Cwr_subset_of_subset HCS},
    {apply and.intro H (DelCode_Cwr _ HC _ _)}},
rw ← mem_DCs_list at h, rw DCs_list at h, cases h,
  {apply DC1.card_Cwr_ge_le _ HCS HC, rw DC1.DC, rw h},
  {cases h,
    {apply DC2.card_Cwr_ge_le _ HCS HC, rw DC2.DC, rw h},
    {cases h,
      {apply DC3.card_Cwr_ge_le _ HCS HC, rw DC3.DC, rw h},
      {cases h,
        {apply DC4.card_Cwr_ge_le _ HCS HC, rw DC4.DC, rw h},
        {cases h,
          {apply DC5.card_Cwr_ge_le _ HCS HC, rw DC5.DC, rw h},
          {cases h,
            {apply DC6.card_Cwr_ge_le _ HCS HC, rw DC6.DC, rw h},
            {cases h,
              {apply DC7.card_Cwr_ge_le _ HCS HC, rw DC7.DC, rw h},
              {cases h,
                {apply DC8.card_Cwr_ge_le _ HCS HC, rw DC8.DC, rw h},
                {cases h,
                  {apply DC9.card_Cwr_ge_le _ HCS HC, rw DC9.DC, rw h},
                  {cases h,
                    {apply DC10.card_Cwr_ge_le _ HCS HC, rw DC10.DC, rw h},
                    {cases h,
                      {apply DC11.card_Cwr_ge_le _ HCS HC, rw DC11.DC, rw h},
                      {cases h,
                        {apply DC12.card_Cwr_ge_le _ HCS HC, rw DC12.DC, rw h},
                        {cases h,
                         {apply DC13.card_Cwr_ge_le _ HCS HC, rw DC13.DC, rw h},
                         {cases h,
                          {apply DC14.card_Cwr_ge_le _ HCS HC, rw DC14.DC, rw h},
                          {apply false.elim h}}}}}}}}}}}}}}
end

end card2

def DCs_sub_Cwr_W34_3_ge2_len4 : finset (finset (vector B 6)) :=
{{⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}, 
 {⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, I, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, I, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, I, O, O, I], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[O, I, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩}, 
 {⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, O, I, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}, 
 {⟨[I, I, O, I, I, O], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, ⟨[O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, I, I, O], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, I, O, I], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, I, O, I], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, I], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, I], rfl⟩, ⟨[I, O, I, O, I, O], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, I, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, I], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[O, I, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[O, I, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[O, I, I, I, O, I], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, I, O, I, I], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, O, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, I], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩, ⟨[O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩}, 
 {⟨[I, O, I, O, I, O], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, I, I], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩}, 
 {⟨[I, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O], rfl⟩, ⟨[O, I, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, I], rfl⟩}}

lemma DCs_sub_Cwr_W34_3_ge2_len4_eq' : 
  DCs_sub_Cwr_W34_3_ge2_len4 = DCs_sub_len' Cwr_W34_3_ge2 4 := dec_trivial

lemma DCs_sub_Cwr_W34_3_ge2_len4_eq : 
  DCs_sub_Cwr_W34_3_ge2_len4 = DCs_sub_len Cwr_W34_3_ge2 4 := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_Cwr_W34_3_ge2_len4_eq'}

lemma DCs_sub_Cwr_W34_3_ge2_len4_succ : 
  DCs_sub_DCs_len_succ Cwr_W34_3_ge2 DCs_sub_Cwr_W34_3_ge2_len4 = ∅ := rfl

lemma DCs_sub_Cwr_W34_3_ge2_len5 : DCs_sub_len Cwr_W34_3_ge2 5 = ∅ := 
begin
rw ← DCs_sub_DCs_len_succ_eq, rw ← DCs_sub_Cwr_W34_3_ge2_len4_eq, 
apply DCs_sub_Cwr_W34_3_ge2_len4_succ
end

lemma card_le_of_sub_Cwr_W34_3_ge2 
  (C : finset (vector B 6)) (HCS : C ⊆ Cwr_W34_3_ge2) (HC : is_DelCode C) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_Cwr_W34_3_ge2_len5 _ HCS HC

lemma card_Cwr_3_2_le
  (C : finset (vector B 6)) (HCS : C ⊆ W34) (HC : is_DelCode C) : 
  card (Cwr_ge C 3 2) ≤ 4 := 
begin
apply card_le_of_sub_Cwr_W34_3_ge2,
  {rw Cwr_W34_3_ge2_eq, apply Cwr_ge_subset_of_subset HCS},
  {apply DelCode_Cwr_ge _ HC}
end

lemma card_le_of_sub_W34 
  (C : finset (vector B 6)) (HCS : C ⊆ W34) (HC : is_DelCode C) : 
  card C ≤ 5 :=
begin
rw ← W34.card_Cwr_add_ge _ HCS, 
have h : card (Cwr C 3 1) ≤ 3,
  {apply W34.card_Cwr_3_1_le _ HCS HC},
cases eq_or_lt_of_le h with heq3 hlt3,
  {rw heq3, rw add_comm, repeat {apply succ_le_succ},
   apply card3.card_Cwr_ge_le _ HCS HC heq3},
  {rw lt_succ_iff at hlt3, 
   cases eq_or_lt_of_le hlt3 with heq2 hlt2,
    {rw heq2, rw add_comm, repeat {apply succ_le_succ},
     apply card2.card_Cwr_ge_le _ HCS HC heq2},
    {rw lt_succ_iff at hlt2, apply le_trans,
      {apply add_le_add hlt2 (card_Cwr_3_2_le _ HCS HC)},
      {refl}}}
end

end W34

lemma card_le_of_sub_W24 
  (C : finset (vector B 6)) (HCS : C ⊆ W24) (HC : is_DelCode C) : 
  card C ≤ 8 :=
begin
rw ← card_div_wt_of_sub_W24 _ HCS,
have h : card (filter (λ x, wt x = 2) C) ≤ 4,
  {apply card_filter_wt2_le _ HCS HC},
cases eq_or_lt_of_le h with heq4 hlt4,
  {rw heq4, rw add_comm, repeat {apply succ_le_succ},
   apply card4.card_filter_wt34_le _ HCS HC heq4},
  {rw lt_succ_iff at hlt4, apply le_trans,
    {apply add_le_add,
      {apply hlt4},
      {apply W34.card_le_of_sub_W34, 
        {rw W34_eq, apply filter_subset_filter HCS},
        {apply DelCode_filter _ HC}}},
    {refl}} 
end

lemma optimal_of_card
  (C : finset (vector B 6)) (HC : is_DelCode C) (H : card C = 10) :
  is_optimal C HC :=
begin
rw optimal_iff_W22_sdiff_Repl (le_trans (le_succ _) (le_succ _)) _ HC,
rw H, rw ← W24_eq, apply card_le_of_sub_W24
end

lemma card_VTCode_6_0 : card (VTCode 6 0) = 10 := rfl

lemma optimal_VTCode_6_0 : 
  is_optimal (VTCode 6 0) (DelCode_VTCode 6 0) := 
by {apply optimal_of_card, rw card_VTCode_6_0}

end length6

namespace length7

def W25 : finset (vector B 7) :=
{⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, I, O, O, I], rfl⟩, ⟨[I, I, I, I, O, O, O], rfl⟩, ⟨[I, I, I, O, I, I, O], rfl⟩, ⟨[I, I, I, O, I, O, I], rfl⟩, ⟨[I, I, I, O, O, I, I], rfl⟩, ⟨[I, I, I, O, O, I, O], rfl⟩, ⟨[I, I, I, O, O, O, I], rfl⟩, ⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, I, O, I, I, I, O], rfl⟩, 
 ⟨[I, I, O, I, I, O, I], rfl⟩, ⟨[I, I, O, I, I, O, O], rfl⟩, ⟨[I, I, O, I, O, I, I], rfl⟩, ⟨[I, I, O, I, O, I, O], rfl⟩, ⟨[I, I, O, I, O, O, I], rfl⟩, ⟨[I, I, O, O, I, I, I], rfl⟩, ⟨[I, I, O, O, I, I, O], rfl⟩, ⟨[I, I, O, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, I], rfl⟩, 
 ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[I, O, I, I, I, I, O], rfl⟩, ⟨[I, O, I, I, I, O, I], rfl⟩, ⟨[I, O, I, I, I, O, O], rfl⟩, ⟨[I, O, I, I, O, I, I], rfl⟩, ⟨[I, O, I, I, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, 
 ⟨[I, O, I, O, I, I, I], rfl⟩, ⟨[I, O, I, O, I, I, O], rfl⟩, ⟨[I, O, I, O, I, O, I], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, I, O, O, I, I], rfl⟩, ⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, I, I], rfl⟩, ⟨[I, O, O, I, I, I, O], rfl⟩, ⟨[I, O, O, I, I, O, I], rfl⟩, 
 ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, I, I], rfl⟩, ⟨[I, O, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, I], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, 
 ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, I, I, O], rfl⟩, ⟨[O, I, I, I, I, O, I], rfl⟩, ⟨[O, I, I, I, I, O, O], rfl⟩, ⟨[O, I, I, I, O, I, I], rfl⟩, ⟨[O, I, I, I, O, I, O], rfl⟩, ⟨[O, I, I, I, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, I, I, O, I, I, I], rfl⟩, 
 ⟨[O, I, I, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, I, I, I, O], rfl⟩, ⟨[O, I, O, I, I, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, 
 ⟨[O, I, O, I, O, I, I], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, I, O, O, I], rfl⟩, ⟨[O, I, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩, 
 ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩, ⟨[O, O, I, I, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, 
 ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, I, O], rfl⟩, 
 ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma W25_eq : W25 = W22 7 \ Repl 7 := rfl

lemma flip_W25 : flip W25 = W25 := 
begin
rw W25_eq, rw flip_W22_sdiff_Repl, 
repeat {apply succ_le_succ}, apply nat.zero_le
end

lemma div_wt_of_sub_W25
  (C : finset (vector B 7)) (HCS : C ⊆ W25) : 
  filter (Icc_wt 2 3) C ∪ filter (Icc_wt 4 5) C = C := 
begin
apply subset.antisymm,
  {apply union_subset,
    {apply filter_subset},
    {apply filter_subset}},
  {intros x hx, 
   have h : x ∈ W25, from HCS hx,
   rw W25_eq at h, rw mem_sdiff at h, 
   rw mem_W22 at h, unfold Icc_wt at h,
   cases decidable.em (4 ≤ wt x) with hle hnle,
    {rw mem_union, right, rw mem_filter, 
     apply and.intro hx (and.intro hle h.left.right)},
    {rw not_le at hnle, rw lt_succ_iff at hnle,
     rw mem_union, left, rw mem_filter, 
     apply and.intro hx (and.intro h.left.left hnle)}}
end

lemma filter_wt_inter_of_sub_W25
  (C : finset (vector B 7)) (HCS : C ⊆ W25) : 
  filter (Icc_wt 2 3) C ∩ filter (Icc_wt 4 5) C = ∅ := 
begin
rw ← subset_empty, 
intros x hx, rw mem_inter at hx, repeat {rw mem_filter at hx}, 
apply absurd hx.left.right.right,
rw not_le, apply lt_of_succ_le hx.right.right.left
end

lemma card_div_wt_of_sub_W25
  (C : finset (vector B 7)) (HCS : C ⊆ W25) : 
  card (filter (Icc_wt 2 3) C) + card (filter (Icc_wt 4 5) C) = card C := 
begin
rw ← div_wt_of_sub_W25 C HCS,
rw card_union_of_disjoint, 
  {rw div_wt_of_sub_W25 C HCS},
  {rw filter_wt_inter_of_sub_W25 _ HCS}
end

lemma exists_DC_card_filter_wt_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W25) (HC : is_DelCode C) :
  ∃ C' : finset (vector B 7), is_DelCode C' ∧ C' ⊆ W25 
  ∧ card C' = card C ∧ card (filter (Icc_wt 4 5) C') ≤ card (filter (Icc_wt 2 3) C') :=
begin
cases exists_DC_card_filter_wt_le _ flip_W25 _ HC HCS 2 3 _ _ with C' hC',
  {apply exists.intro C', simp at hC', apply hC'},
  {repeat {apply succ_le_succ}, apply nat.zero_le},
  {repeat {apply succ_le_succ}, apply nat.zero_le}
end

def W23 : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, 
 ⟨[I, O, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, I], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, 
 ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, I, O, O, I], rfl⟩, ⟨[O, I, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, 
 ⟨[O, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, 
 ⟨[O, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩, 
 ⟨[O, O, O, O, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma W23_eq : W23 = filter (Icc_wt 2 3) W25 := rfl

namespace W23

lemma Cwr_W23_2_0 : Cwr W23 2 0 = ∅ := rfl

lemma Cwr_2_0_of_sub_W23 
  (C : finset (vector B 7)) (HC : C ⊆ W23) : 
  Cwr C 2 0 = ∅ :=
begin
unfold Cwr, rw ← subset_empty, 
apply subset.trans,
  {apply Cwr_subset_of_subset HC},
  {rw Cwr_W23_2_0, refl}
end

def Cwr_W23_2_1 : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma Cwr_W23_2_1_eq : Cwr_W23_2_1  = Cwr W23 2 1 := rfl

def Cwr_W23_2_2  : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, 
 ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, 
 ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma Cwr_W23_2_2_eq : Cwr_W23_2_2 = Cwr W23 2 2 := rfl

def Cwr_W23_2_ge2 : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, I], rfl⟩, 
 ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, 
 ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, I, O, O, I], rfl⟩, ⟨[O, I, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, 
 ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, 
 ⟨[O, O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma Cwr_W23_2_ge2_eq : Cwr_W23_2_ge2 = Cwr_ge W23 2 2 := rfl

def Cwr_W23_2_ge3 : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[I, O, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, I], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, I, O, O, I], rfl⟩, ⟨[O, I, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, 
 ⟨[O, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, I, O], rfl⟩}

lemma Cwr_W23_2_ge3_eq : Cwr_W23_2_ge3 = Cwr_ge W23 2 3 := rfl

lemma card_wt2_univ :
  card (filter (λ x : vector B 6, wt x = 2) univ) = 15 := rfl

lemma card_Cwr_2_1_ge_of_card (C : finset (vector B 7)) 
  (HC : is_DelCode C) (HCS : C ⊆ W23) (H : 8 ≤ card C) : 
  1 ≤ card (Cwr C 2 1) :=
begin
have h : 8 ≤ (15 + card (Cwr C 2 1)) / 2, 
  {apply le_trans H,
   apply le_trans,
    {apply card_le_univ_add_1 C HC,
     apply Cwr_2_0_of_sub_W23 _ HCS},
    {rw card_wt2_univ}},
rw le_div_iff_mul_le' (zero_lt_succ 1) at h,
rw mul_two at h, rw add_comm 15 at h, 
repeat {rw succ_le_succ_iff at h}, apply h
end

lemma card_Cwr_2_2_ge_of_card (C : finset (vector B 7)) 
  (HC : is_DelCode C) (HCS : C ⊆ W23) (H : 8 ≤ card C)
  (k : ℕ) (Hk : card (Cwr C 2 1) = k) : 
  9 - 2 * k  ≤ card (Cwr C 2 2) :=
begin
have h : 8 ≤ (15 + 2 * k + card (Cwr C 2 2)) / 3, 
  {apply le_trans H,
   apply le_trans,
    {apply card_le_univ_add_2 C HC,
     apply Cwr_2_0_of_sub_W23 _ HCS},
    {rw card_wt2_univ, rw Hk}},
rw le_div_iff_mul_le' (zero_lt_succ 2) at h,
rw mul_succ at h, rw mul_two at h, 
rw add_comm 15 at h, rw add_right_comm _ 15 at h, 
repeat {rw succ_le_succ_iff at h}, 
apply nat.sub_le_left_of_le_add h
end

lemma Cwr_union_ge 
  (C : finset (vector B 7)) (H : C ⊆ W23) : 
  Cwr C 2 1 ∪ Cwr_ge C 2 2 = C :=
begin
have h : Cwr_le C 2 1 ∪ Cwr_ge C 2 2 = C, 
  {rw Cwr_le_union_ge C 2 1},
rw Cwr_le_succ at h, 
rw Cwr_le_zero at h, rw Cwr_2_0_of_sub_W23 _ H at h, 
rw empty_union at h, apply h
end

lemma card_Cwr_add_ge 
  (C : finset (vector B 7)) (H : C ⊆ W23) : 
  card (Cwr C 2 1) + card (Cwr_ge C 2 2) = card C :=
begin
have h : card (Cwr_le C 2 1) + card (Cwr_ge C 2 2) = card C, 
  {rw card_Cwr_le_add_ge C 2 1},
rw card_Cwr_le_succ at h, 
rw Cwr_le_zero at h, rw Cwr_2_0_of_sub_W23 _ H at h, 
rw card_empty at h, rw nat.zero_add at h, apply h
end

lemma Cwr_ge_2_2_subset 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  : 
  Cwr_ge C 2 2 ⊆ Cwr_W23_2_ge2 \ union_dB (Cwr C 2 1) :=
begin
intros x hx, rw mem_sdiff, apply and.intro,
  {rw Cwr_W23_2_ge2_eq, 
   apply (Cwr_ge_subset_of_subset HCS _ _) hx},
  {apply not_mem_union_dB HC, 
    {apply Cwr_ge_subset _ 2 2},
    {apply Cwr_subset},
    {rw inter_comm, rw ← subset_empty,
     apply subset.trans, 
      {apply inter_subset_inter_right, 
       apply Cwr_subset_le},
      {rw Cwr_le_inter_ge, refl}},
    {apply hx}}
end

lemma Cwr_ge_2_2_mem 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C): 
  Cwr_ge C 2 2 ∈ DCs_sub (Cwr_W23_2_ge2 \ union_dB (Cwr C 2 1)) :=
begin
rw mem_DCs_sub, apply and.intro,
  {apply Cwr_ge_2_2_subset _ HCS HC},
  {apply DelCode_Cwr_ge _ HC},
end

lemma Cwr_union_union_ge 
  (C : finset (vector B 7)) (H : C ⊆ W23) : 
  Cwr C 2 1 ∪ Cwr C 2 2 ∪ Cwr_ge C 2 3 = C :=
begin
have h : Cwr_le C 2 2 ∪ Cwr_ge C 2 3 = C, 
  {rw Cwr_le_union_ge C 2 2},
repeat {rw Cwr_le_succ at h}, 
rw Cwr_le_zero at h, rw Cwr_2_0_of_sub_W23 _ H at h, 
rw empty_union at h, apply h
end

lemma card_Cwr_add_add_ge 
  (C : finset (vector B 7)) (H : C ⊆ W23) : 
  card (Cwr C 2 1) + card (Cwr C 2 2) + card (Cwr_ge C 2 3) = card C :=
begin
have h : card (Cwr_le C 2 2) + card (Cwr_ge C 2 3) = card C, 
  {rw card_Cwr_le_add_ge C 2 2},
repeat {rw card_Cwr_le_succ at h}, 
rw Cwr_le_zero at h, rw Cwr_2_0_of_sub_W23 _ H at h, 
rw card_empty at h, rw nat.zero_add at h, apply h
end

lemma Cwr_2_2_subset 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  : 
  Cwr C 2 2 ⊆ Cwr_W23_2_2 \ union_dB (Cwr C 2 1) :=
begin
intros x hx, rw mem_sdiff, apply and.intro,
  {rw Cwr_W23_2_2_eq, 
   apply (Cwr_subset_of_subset HCS _ _) hx},
  {apply not_mem_union_dB HC, 
    {apply Cwr_subset _ 2 2},
    {apply Cwr_subset},
    {rw inter_comm, rw Cwr_inter_of_ne,
     apply nat.ne_of_lt, apply lt_succ_self},
    {apply hx}}
end

lemma Cwr_2_2_mem 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  : 
  Cwr C 2 2 ∈ DCs_sub (Cwr_W23_2_2 \ union_dB (Cwr C 2 1)) :=
begin
rw mem_DCs_sub, apply and.intro,
  {apply Cwr_2_2_subset _ HCS HC },
  {apply DelCode_Cwr _ HC}
end

lemma Cwr_ge_2_3_subset 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  : 
  Cwr_ge C 2 3 ⊆ Cwr_W23_2_ge3 \ union_dB (Cwr C 2 1 ∪ Cwr C 2 2) :=
begin
have h : Cwr C 2 1 ∪ Cwr C 2 2 = Cwr_le C 2 2,
  {repeat {rw Cwr_le_succ}, 
   rw Cwr_le_zero, rw Cwr_2_0_of_sub_W23 _ HCS, rw empty_union},
rw h, intros x hx, rw mem_sdiff, apply and.intro,
  {rw Cwr_W23_2_ge3_eq, 
   apply (Cwr_ge_subset_of_subset HCS _ _) hx},
  {apply not_mem_union_dB HC, 
    {apply Cwr_ge_subset _ 2 3},
    {apply Cwr_le_subset},
    {rw inter_comm, rw Cwr_le_inter_ge},
    {apply hx}}
end

lemma Cwr_ge_2_3_mem 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  : 
  Cwr_ge C 2 3 ∈ DCs_sub (Cwr_W23_2_ge3 \ union_dB (Cwr C 2 1 ∪ Cwr C 2 2)) :=
begin
rw mem_DCs_sub, apply and.intro,
  {apply Cwr_ge_2_3_subset _ HCS HC },
  {apply DelCode_Cwr_ge _ HC}
end

lemma DCs_sub_Cwr_W23_2_1_len5' : DCs_sub_len' Cwr_W23_2_1 5 = ∅ := rfl

lemma DCs_sub_Cwr_W23_2_1_len5 : DCs_sub_len Cwr_W23_2_1 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_Cwr_W23_2_1_len5'}

lemma card_DC_sub_Cwr_W23_2_1_le 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ Cwr_W23_2_1) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_Cwr_W23_2_1_len5 _ HCS HC

lemma card_Cwr_2_1_le
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  : 
  card (Cwr C 2 1) ≤ 4 := 
begin
apply card_DC_sub_Cwr_W23_2_1_le,
  {apply DelCode_Cwr _ HC},
  {rw Cwr_W23_2_1_eq, apply Cwr_subset_of_subset HCS}
end

namespace card4

lemma card_Cwr_ge_ge
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : card (Cwr C 2 1) = 4) : 
  4 ≤ card (Cwr_ge C 2 2) :=
begin
rw ← card_Cwr_add_ge _ HCS at H1,
rw H2 at H1, rw add_comm at H1, 
repeat {rw succ_le_succ_iff at H1}, apply H1
end

def DCs : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}}

lemma DCs_eq' : DCs = DCs_sub_len' Cwr_W23_2_1 4 := dec_trivial

lemma DCs_eq : DCs = DCs_sub_len Cwr_W23_2_1 4 := 
by {rw ← DCs_sub_len'_eq, rw DCs_eq'}

namespace DC1 

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma card_DC : card DC = 4 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, I, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, I, O, O, I], rfl⟩, ⟨[O, I, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, 
 ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_ge2 \ union_dB DC := rfl 

def DCs_sub_sdiff_dB_DC : finset (finset (vector B 7)) :=
{{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}, 
 {⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}, 
 {⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩}, 
 {⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}}

lemma DCs_sub_sdiff_dB_DC_eq' : 
   DCs_sub_sdiff_dB_DC = DCs_sub_len' sdiff_dB_DC 4 := dec_trivial

lemma DCs_sub_sdiff_dB_DC_eq : 
  DCs_sub_sdiff_dB_DC = DCs_sub_len sdiff_dB_DC 4 := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_eq'}

lemma DCs_sub_sdiff_dB_DC_succ : 
  DCs_sub_DCs_len_succ sdiff_dB_DC DCs_sub_sdiff_dB_DC = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
begin
rw ← DCs_sub_DCs_len_succ_eq, rw ← DCs_sub_sdiff_dB_DC_eq, 
apply DCs_sub_sdiff_dB_DC_succ
end

lemma card_le_of_sub_sdiff_dB_DC (C : finset (vector B 7)) 
  (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_ge_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr_ge C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge2_eq, rw ← H, 
   apply Cwr_ge_2_2_subset C HCS HC}
end

lemma card_Cwr_ge_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC): 
  card (Cwr_ge C 2 2) = 4 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_2_le _ HCS HC H2},
  {apply card_Cwr_ge_ge _ HCS HC H1, rw H2, rw card_DC}
end

lemma DC_union_1 : 
  DC ∪ {⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} 
  = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} := dec_trivial
lemma DC_union_2 : 
  DC ∪ {⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} 
  = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} := dec_trivial
lemma DC_union_3 : 
  DC ∪ {⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩} 
  = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩} := dec_trivial
lemma DC_union_4 : 
  DC ∪ {⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} 
  = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} := dec_trivial
lemma DC_union_5 : 
  DC ∪ {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} 
  = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} := dec_trivial

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}}

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  C ∈ DCs_sup_DC_len8 :=
begin
rw ← Cwr_union_ge C HCS, rw H2, 
have h : Cwr_ge C 2 2 ∈ DCs_sub_sdiff_dB_DC,
  {rw DCs_sub_sdiff_dB_DC_eq, rw mem_DCs_sub_len', apply and.intro,
    {rw sdiff_dB_DC_eq, rw ← H2, apply Cwr_ge_2_2_mem C HCS HC},
    {apply card_Cwr_ge_2_2 _ HCS HC H1 H2}},
rw DCs_sup_DC_len8, cases h,
  {rw h, left, rw DC_union_5},
  {cases h,
    {rw h, right, left, rw DC_union_4},
    {cases h,
      {rw h, right, right, left, rw DC_union_3},
      {cases h,
        {rw h, right, right, right, left, rw DC_union_2},
        {cases h,
          {rw h, right, right, right, right, left, rw DC_union_1},
          {apply false.elim h}}}}}
end

end DC1 

namespace DC2 

def DC : finset (vector B 7) :=
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 4 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, I], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, I, O, O, I], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, 
 ⟨[O, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_ge2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_ge_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr_ge C 2 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge2_eq, rw ← H, 
   apply Cwr_ge_2_2_subset C HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card C ≤ 7 :=
begin
rw ← card_Cwr_add_ge _ HCS, rw H, rw card_DC, 
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_le _ HCS HC H
end

end DC2

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
  DC1.DCs_sup_DC_len8

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : card (Cwr C 2 1) = 4) : 
  C ∈ DCs_sup_DC_len8 :=
begin
have h : Cwr C 2 1 ∈ DCs,
  {rw DCs_eq, rw mem_DCs_sub_len, apply and.intro,
    {rw Cwr_W23_2_1_eq, apply Cwr_subset_of_subset HCS},
    {apply and.intro H2 (DelCode_Cwr _ HC _ _)}},
rw DCs at h, cases h,
  {apply absurd H1, apply not_le_of_gt, apply lt_succ_of_le, 
   apply DC2.card_le_of_sup_DC _ HCS HC , rw DC2.DC, apply h},
  {cases h, 
    {unfold DCs_sup_DC_len8, 
     apply DC1.mem_DCs_sup_DC_len8 _ HCS HC  H1, 
     unfold DC1.DC, apply h},
    {apply false.elim h}}
end

end card4

namespace card3

lemma card_Cwr_2_2_ge 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : card (Cwr C 2 1) = 3) : 
  3 ≤ card (Cwr C 2 2) :=
by {apply le_trans _ (card_Cwr_2_2_ge_of_card C HC HCS H1 _ H2), refl}

def DCs : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}}

lemma DCs_eq' : DCs = DCs_sub_len' Cwr_W23_2_1 3 := dec_trivial

lemma DCs_eq : DCs = DCs_sub_len Cwr_W23_2_1 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs_eq' }

def DCs_list : list (finset (vector B 7)) :=
[{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}]

lemma DCs_list_to_finset : DCs_list.to_finset = DCs := dec_trivial

lemma mem_DCs_list (s : finset (vector B 7)) : 
  s ∈ DCs_list ↔ s ∈ DCs :=
by {rw ← DCs_list_to_finset, rw ← list.mem_to_finset}

namespace DC1 

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 3 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 3 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩} 

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, I, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : Cwr C 2 2 ∈ DCs',
    {rw DCs'_eq, rw sdiff_dB_DC_eq, 
     rw mem_DCs_sub_len', apply and.intro,
      {rw ← H, apply Cwr_2_2_mem _ HCS HC },
      {apply card_Cwr_2_2 _ HCS HC  h1 H}},
  rw DCs' at h2, cases h2,
    {apply DC5.card_le_of_sup_DC' _ HCS HC H, rw DC5.DC', rw h2},
    {cases h2,
      {apply DC4.card_le_of_sup_DC' _ HCS HC H, rw DC4.DC', rw h2},
      {cases h2,
        {apply DC3.card_le_of_sup_DC' _ HCS HC H, rw DC3.DC', rw h2},
        {cases h2,
          {apply DC2.card_le_of_sup_DC' _ HCS HC H, rw DC2.DC', rw h2},
          {cases h2,
            {apply DC1.card_le_of_sup_DC' _ HCS HC H, rw DC1.DC', rw h2},
            {apply false.elim h2}}}}}}
end

end DC1 

namespace DC2

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 3 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩}, 
 {⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 3 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

def DCs'_list : list (finset (vector B 7)) :=
[{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩}, 
 {⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}]

lemma DCs'_list_to_finset : 
  DCs'_list.to_finset = DCs' := dec_trivial

lemma mem_DCs'_list (s : finset (vector B 7)) : 
  s ∈ DCs'_list ↔ s ∈ DCs' :=
by {rw ← DCs'_list_to_finset, rw ← list.mem_to_finset}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC' 3 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC' 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC')  : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_Cwr_ge_2_3
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) = 2 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_3_le _ HCS HC  H2 H3},
  {rw ← card_Cwr_add_add_ge _ HCS at H1,
   rw H2 at H1, rw card_DC at H1, rw H3 at H1, rw card_DC' at H1,
   rw add_comm at H1, rw ← add_assoc at H1, 
   repeat {rw succ_le_succ_iff at H1}, apply H1}
end

def DCs_sub_sdiff_dB_DC_len2 : finset (finset (vector B 7)) :=
{{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}} 

lemma DCs_sub_sdiff_dB_DC_len2_eq' : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len' sdiff_dB_DC' 2 := rfl

lemma DCs_sub_sdiff_dB_DC_len2_eq : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len sdiff_dB_DC' 2:= 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2_eq'}

lemma DC_union_DC'_union : 
  DC ∪ DC' ∪ {⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩} := dec_trivial

def DCs_sup_DC'_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}}

lemma mem_DCs_sup_DC'_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  C ∈ DCs_sup_DC'_len8 := 
begin
rw ← Cwr_union_union_ge C HCS,
have h : Cwr_ge C 2 3 ∈ DCs_sub_sdiff_dB_DC_len2,
  {rw DCs_sub_sdiff_dB_DC_len2_eq, rw sdiff_dB_DC_eq,
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, rw ← H3, apply Cwr_ge_2_3_mem _ HCS HC },
    {apply card_Cwr_ge_2_3 _ HCS HC  H1 H2 H3}},
cases h,
  {rw H2, rw H3, rw h, rw DC_union_DC'_union, 
   rw DCs_sup_DC'_len8, left, refl},
  {apply false.elim h}
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

lemma sdiff_dB_DC_eq : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC_eq at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 6 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

namespace DC6

def DC' : finset (vector B 7) :=
{⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC6

namespace DC7

def DC' : finset (vector B 7) :=
{⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC7

namespace DC8

def DC' : finset (vector B 7) :=
{⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC8

namespace DC9

def DC' : finset (vector B 7) :=
{⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC9

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
  DC1.DCs_sup_DC'_len8

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  C ∈ DCs_sup_DC_len8 :=
begin
have h : Cwr C 2 2 ∈ DCs',
  {rw DCs'_eq, rw sdiff_dB_DC_eq, 
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, apply Cwr_2_2_mem _ HCS HC },
    {apply card_Cwr_2_2 _ HCS HC  H1 H2}},
rw ← mem_DCs'_list at h,
rw DCs'_list at h, cases h,
  {unfold DCs_sup_DC_len8, 
   apply DC1.mem_DCs_sup_DC'_len8 _ HCS HC H1 H2, rw DC1.DC', rw h},
  {cases h,
    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
     apply DC2.card_le_of_sup_DC' _ HCS HC H2, rw DC2.DC', rw h},
    {cases h,
      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
       apply DC3.card_le_of_sup_DC' _ HCS HC H2, rw DC3.DC', rw h},
      {cases h,
        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
         apply le_succ_of_le, apply DC4.card_le_of_sup_DC' _ HCS HC H2,
         rw DC4.DC', rw h},
        {cases h,
          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
           apply DC5.card_le_of_sup_DC' _ HCS HC H2, rw DC5.DC', rw h},
          {cases h,
            {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
             apply DC6.card_le_of_sup_DC' _ HCS HC H2, rw DC6.DC', rw h},
              {cases h,
              {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
               apply DC7.card_le_of_sup_DC' _ HCS HC H2, rw DC7.DC', rw h},
              {cases h,
                {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                 apply DC8.card_le_of_sup_DC' _ HCS HC H2, rw DC8.DC', rw h},
                {cases h,
                  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                   apply DC9.card_le_of_sup_DC' _ HCS HC H2, rw DC9.DC', rw h},
                  {apply false.elim h}}}}}}}}}
end

end DC2

namespace DC3

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, 
 ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 3 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 3 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

def DCs'_list : list (finset (vector B 7)) :=
[{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}]

lemma DCs'_list_to_finset : 
  DCs'_list.to_finset = DCs' := dec_trivial

lemma mem_DCs'_list (s : finset (vector B 7)) : 
  s ∈ DCs'_list ↔ s ∈ DCs' :=
by {rw ← DCs'_list_to_finset, rw ← list.mem_to_finset}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

lemma sdiff_dB_DC_eq : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC_eq at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 6 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

namespace DC6

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC6

namespace DC7

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC7

namespace DC8

def DC' : finset (vector B 7) :=
{⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

lemma sdiff_dB_DC_eq : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC_eq at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 6 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC8

namespace DC9

def DC' : finset (vector B 7) :=
{⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC9

namespace DC10

def DC' : finset (vector B 7) :=
{⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC10

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC): 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : Cwr C 2 2 ∈ DCs',
    {rw DCs'_eq, rw sdiff_dB_DC_eq, 
     rw mem_DCs_sub_len', apply and.intro,
      {rw ← H, apply Cwr_2_2_mem _ HCS HC },
      {apply card_Cwr_2_2 _ HCS HC  h1 H}},
  rw ← mem_DCs'_list at h2,
  rw DCs'_list at h2, cases h2,
    {apply DC1.card_le_of_sup_DC' _ HCS HC H, rw DC1.DC', rw h2},
    {cases h2,
      {apply le_succ_of_le, apply DC2.card_le_of_sup_DC' _ HCS HC H _,
       rw DC2.DC', rw h2},
      {cases h2,
        {apply DC3.card_le_of_sup_DC' _ HCS HC H _, rw DC3.DC', rw h2},
        {cases h2,
          {apply DC4.card_le_of_sup_DC' _ HCS HC H, rw DC4.DC', rw h2},
          {cases h2,
            {apply DC5.card_le_of_sup_DC' _ HCS HC H _, rw DC5.DC', rw h2},
            {cases h2,
              {apply DC6.card_le_of_sup_DC' _ HCS HC H, rw DC6.DC', rw h2},
              {cases h2,
                {apply DC7.card_le_of_sup_DC' _ HCS HC H, rw DC7.DC', rw h2},
                {cases h2,
                  {apply le_succ_of_le, apply DC8.card_le_of_sup_DC' _ HCS HC H,
                   rw DC8.DC', rw h2},
                  {cases h2,
                    {apply DC9.card_le_of_sup_DC' _ HCS HC H, rw DC9.DC', rw h2},
                    {cases h2,
                      {apply DC10.card_le_of_sup_DC' _ HCS HC H, rw DC10.DC', rw h2},
                      {apply false.elim h2}}}}}}}}}}}
end

end DC3 

namespace DC4

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

def DCs'_card4 : finset (finset (vector B 7)) :=
{{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}}

lemma DCs'_card4_eq' : DCs'_card4 = DCs_sub_len' sdiff_dB_DC 4 := dec_trivial

lemma DCs'_card4_eq : DCs'_card4 = DCs_sub_len sdiff_dB_DC 4 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_card4_eq'}

namespace card4

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 4 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) = 1 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_3_le _ HCS HC  H2 H3},
  {rw ← card_Cwr_add_add_ge _ HCS at H1,
   rw H2 at H1, rw card_DC at H1, rw H3 at H1, rw card_DC' at H1,
   rw add_comm at H1, repeat {rw succ_le_succ_iff at H1}, apply H1}
end

def DCs_sub_sdiff_dB_DC_len1 : finset (finset (vector B 7)) :=
{{⟨[O, O, I, O, I, O, I], rfl⟩}}

lemma DCs_sub_sdiff_dB_DC_len1_eq' : 
  DCs_sub_sdiff_dB_DC_len1 = DCs_sub_len' sdiff_dB_DC' 1 := rfl

lemma DCs_sub_sdiff_dB_DC_len1_eq : 
  DCs_sub_sdiff_dB_DC_len1 = DCs_sub_len sdiff_dB_DC' 1 := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len1_eq'}

lemma DC_union_DC'_union : 
  DC ∪ DC' ∪ {⟨[O, O, I, O, I, O, I], rfl⟩} = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩} := dec_trivial

def DCs_sup_DC'_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}}

lemma mem_DCs_sup_DC'_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  C ∈ DCs_sup_DC'_len8 := 
begin
rw ← Cwr_union_union_ge C HCS,
have h : Cwr_ge C 2 3 ∈ DCs_sub_sdiff_dB_DC_len1,
  {rw DCs_sub_sdiff_dB_DC_len1_eq, rw sdiff_dB_DC_eq,
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, rw ← H3, apply Cwr_ge_2_3_mem _ HCS HC },
    {apply card_Cwr_2_2 _ HCS HC  H1 H2 H3}},
cases h,
  {rw H2, rw H3, rw h, rw DC_union_DC'_union, rw DCs_sup_DC'_len8, left, refl},
  {apply false.elim h}
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 4 := rfl

lemma sdiff_dB_DC_eq : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC_eq at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 4 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) = 1 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_3_le _ HCS HC  H2 H3},
  {rw ← card_Cwr_add_add_ge _ HCS at H1,
   rw H2 at H1, rw card_DC at H1, rw H3 at H1, rw card_DC' at H1,
   rw add_comm at H1, repeat {rw succ_le_succ_iff at H1}, apply H1}
end

def DCs_sub_sdiff_dB_DC_len1 : finset (finset (vector B 7)) :=
{{⟨[O, I, O, I, O, I, O], rfl⟩}}

lemma DCs_sub_sdiff_dB_DC_len1_eq' : 
  DCs_sub_sdiff_dB_DC_len1 = DCs_sub_len' sdiff_dB_DC' 1 := rfl

lemma DCs_sub_sdiff_dB_DC_len1_eq : 
  DCs_sub_sdiff_dB_DC_len1 = DCs_sub_len sdiff_dB_DC' 1 := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len1_eq'}

lemma DC_union_DC'_union : 
  DC ∪ DC' ∪ {⟨[O, I, O, I, O, I, O], rfl⟩} = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩} := dec_trivial

def DCs_sup_DC'_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}}

lemma mem_DCs_sup_DC'_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  C ∈ DCs_sup_DC'_len8 := 
begin
rw ← Cwr_union_union_ge C HCS,
have h : Cwr_ge C 2 3 ∈ DCs_sub_sdiff_dB_DC_len1,
  {rw DCs_sub_sdiff_dB_DC_len1_eq, rw sdiff_dB_DC_eq,
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, rw ← H3, apply Cwr_ge_2_3_mem _ HCS HC },
    {apply card_Cwr_2_2 _ HCS HC  H1 H2 H3}},
cases h,
  {rw H2, rw H3, rw h, rw DC_union_DC'_union, rw DCs_sup_DC'_len8, left, refl},
  {apply false.elim h}
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 4 := rfl

lemma sdiff_dB_DC_eq : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC_eq at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 4 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) = 1 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_3_le _ HCS HC  H2 H3},
  {rw ← card_Cwr_add_add_ge _ HCS at H1,
   rw H2 at H1, rw card_DC at H1, rw H3 at H1, rw card_DC' at H1,
   rw add_comm at H1, repeat {rw succ_le_succ_iff at H1}, apply H1}
end

def DCs_sub_sdiff_dB_DC_len1 : finset (finset (vector B 7)) :=
{{⟨[I, O, I, O, I, O, O], rfl⟩}}

lemma DCs_sub_sdiff_dB_DC_len1_eq' : 
  DCs_sub_sdiff_dB_DC_len1 = DCs_sub_len' sdiff_dB_DC' 1 := rfl

lemma DCs_sub_sdiff_dB_DC_len1_eq : 
  DCs_sub_sdiff_dB_DC_len1 = DCs_sub_len sdiff_dB_DC' 1 := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len1_eq'}

lemma DC_union_DC'_union : 
  DC ∪ DC' ∪ {⟨[I, O, I, O, I, O, O], rfl⟩} = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩} := dec_trivial

def DCs_sup_DC'_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}}

lemma mem_DCs_sup_DC'_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  C ∈ DCs_sup_DC'_len8 := 
begin
rw ← Cwr_union_union_ge C HCS,
have h : Cwr_ge C 2 3 ∈ DCs_sub_sdiff_dB_DC_len1,
  {rw DCs_sub_sdiff_dB_DC_len1_eq, rw sdiff_dB_DC_eq,
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, rw ← H3, apply Cwr_ge_2_3_mem _ HCS HC },
    {apply card_Cwr_2_2 _ HCS HC  H1 H2 H3}},
cases h,
  {rw H2, rw H3, rw h, rw DC_union_DC'_union, rw DCs_sup_DC'_len8, left, refl},
  {apply false.elim h}
end

end DC5

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
  DC1.DCs_sup_DC'_len8 ∪ DC3.DCs_sup_DC'_len8 ∪ DC5.DCs_sup_DC'_len8

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : card (Cwr C 2 2) = 4) : 
  C ∈ DCs_sup_DC_len8 :=
begin
have h : Cwr C 2 2 ∈ DCs'_card4,
  {rw DCs'_card4_eq, rw sdiff_dB_DC_eq, 
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, apply Cwr_2_2_mem _ HCS HC },
    {apply H3}},
rw DCs'_card4 at h, 
unfold DCs_sup_DC_len8, repeat {rw mem_union}, cases h,
  {right, apply DC5.mem_DCs_sup_DC'_len8 _ HCS HC  H1 H2, rw DC5.DC', rw h},
  {cases h,
    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
     apply DC4.card_le_of_sup_DC' _ HCS HC H2, rw DC4.DC', rw h},
    {cases h,
      {left, right, apply DC3.mem_DCs_sup_DC'_len8 _ HCS HC  H1 H2, rw DC3.DC', rw h},
      {cases h,
        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
         apply DC2.card_le_of_sup_DC' _ HCS HC H2, rw DC2.DC', rw h},
        {cases h,
          {left, left, apply DC1.mem_DCs_sup_DC'_len8 _ HCS HC  H1 H2, rw DC1.DC', rw h},
          {apply false.elim h}}}}}
end

end card4

def DCs'_card3 : finset (finset (vector B 7)) :=
{{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩},
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}}

lemma DCs'_card3_eq' : DCs'_card3 = DCs_sub_len' sdiff_dB_DC 3 := dec_trivial

lemma DCs'_card3_eq : DCs'_card3 = DCs_sub_len sdiff_dB_DC 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_card3_eq'}

def DCs'_card3_list : list (finset (vector B 7)) :=
[{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩},
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}]

lemma DCs'_card3_list_to_finset : 
  DCs'_card3_list.to_finset = DCs'_card3 := dec_trivial

lemma mem_DCs'_card3_list (s : finset (vector B 7)) : 
  s ∈ DCs'_card3_list ↔ s ∈ DCs'_card3 :=
by {rw ← DCs'_card3_list_to_finset, rw ← list.mem_to_finset}

namespace card3

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

namespace DC6

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

lemma sdiff_dB_DC_eq : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC_eq at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 6 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC6

namespace DC7

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC7

namespace DC8

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC8

namespace DC9

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC9

namespace DC10

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

lemma sdiff_dB_DC_eq : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC_eq at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 6 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC10

namespace DC11

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC' 3 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC' 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC')  : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_Cwr_ge_2_3
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) = 2 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_3_le _ HCS HC  H2 H3},
  {rw ← card_Cwr_add_add_ge _ HCS at H1,
   rw H2 at H1, rw card_DC at H1, rw H3 at H1, rw card_DC' at H1,
   rw add_comm at H1, rw ← add_assoc at H1, 
   repeat {rw succ_le_succ_iff at H1}, apply H1}
end

def DCs_sub_sdiff_dB_DC_len2 : finset (finset (vector B 7)) :=
{{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}}

lemma DCs_sub_sdiff_dB_DC_len2_eq' : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len' sdiff_dB_DC' 2 := rfl

lemma DCs_sub_sdiff_dB_DC_len2_eq : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len sdiff_dB_DC' 2:= 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2_eq'}

lemma DC_union_DC'_union : 
  DC ∪ DC' ∪ {⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩} := dec_trivial

def DCs_sup_DC'_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}}

lemma mem_DCs_sup_DC'_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  C ∈ DCs_sup_DC'_len8 := 
begin
rw ← Cwr_union_union_ge C HCS,
have h : Cwr_ge C 2 3 ∈ DCs_sub_sdiff_dB_DC_len2,
  {rw DCs_sub_sdiff_dB_DC_len2_eq, rw sdiff_dB_DC_eq,
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, rw ← H3, apply Cwr_ge_2_3_mem _ HCS HC },
    {apply card_Cwr_ge_2_3 _ HCS HC  H1 H2 H3}},
cases h,
  {rw H2, rw H3, rw h, rw DC_union_DC'_union, rw DCs_sup_DC'_len8, left, refl},
  {apply false.elim h}
end

end DC11

namespace DC12

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC12

namespace DC13

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC13

namespace DC14

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC14

namespace DC15

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC15

namespace DC16

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

lemma sdiff_dB_DC_eq : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC_eq at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 6 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC16

namespace DC17

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC17

namespace DC18

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC18

namespace DC19

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

lemma sdiff_dB_DC_eq : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC_eq at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 6 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC19

namespace DC20

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC20

namespace DC21

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC21

namespace DC22

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC' 3 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC' 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC')  : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_Cwr_ge_2_3
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) = 2 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_3_le _ HCS HC  H2 H3},
  {rw ← card_Cwr_add_add_ge _ HCS at H1,
   rw H2 at H1, rw card_DC at H1, rw H3 at H1, rw card_DC' at H1,
   rw add_comm at H1, rw ← add_assoc at H1, 
   repeat {rw succ_le_succ_iff at H1}, apply H1}
end

def DCs_sub_sdiff_dB_DC_len2 : finset (finset (vector B 7)) :=
{{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}}

lemma DCs_sub_sdiff_dB_DC_len2_eq' : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len' sdiff_dB_DC' 2 := rfl

lemma DCs_sub_sdiff_dB_DC_len2_eq : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len sdiff_dB_DC' 2:= 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2_eq'}

lemma DC_union_DC'_union : 
  DC ∪ DC' ∪ {⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩} := dec_trivial

def DCs_sup_DC'_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}}

lemma mem_DCs_sup_DC'_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  C ∈ DCs_sup_DC'_len8 := 
begin
rw ← Cwr_union_union_ge C HCS,
have h : Cwr_ge C 2 3 ∈ DCs_sub_sdiff_dB_DC_len2,
  {rw DCs_sub_sdiff_dB_DC_len2_eq, rw sdiff_dB_DC_eq,
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, rw ← H3, apply Cwr_ge_2_3_mem _ HCS HC },
    {apply card_Cwr_ge_2_3 _ HCS HC  H1 H2 H3}},
cases h,
  {rw H2, rw H3, rw h, rw DC_union_DC'_union, rw DCs_sup_DC'_len8, left, refl},
  {apply false.elim h}
end

end DC22

namespace DC23

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC23

namespace DC24

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC24

namespace DC25

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, I, O, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC25

namespace DC26

def DC' : finset (vector B 7) :=
{⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC26

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
  DC11.DCs_sup_DC'_len8 ∪ DC22.DCs_sup_DC'_len8

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : card (Cwr C 2 2) = 3) : 
  C ∈ DCs_sup_DC_len8 :=
begin
have h : Cwr C 2 2 ∈ DCs'_card3,
  {rw DCs'_card3_eq, rw sdiff_dB_DC_eq, 
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, apply Cwr_2_2_mem _ HCS HC },
    {apply H3}},
rw ← mem_DCs'_card3_list at h, rw DCs'_card3_list at h, cases h,
  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
   apply DC1.card_le_of_sup_DC' _ HCS HC H2, rw DC1.DC', rw h},
  {cases h,
    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
     apply DC2.card_le_of_sup_DC' _ HCS HC H2, rw DC2.DC', rw h},
    {cases h,
      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
       apply DC3.card_le_of_sup_DC' _ HCS HC H2, rw DC3.DC', rw h},
      {cases h,
        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
         apply DC4.card_le_of_sup_DC' _ HCS HC H2, rw DC4.DC', rw h},
        {cases h, 
          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
           apply DC5.card_le_of_sup_DC' _ HCS HC H2, rw DC5.DC', rw h},
          {cases h, 
            {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
             apply le_succ_of_le, apply DC6.card_le_of_sup_DC' _ HCS HC H2, 
             rw DC6.DC', rw h},
            {cases h, 
              {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
               apply DC7.card_le_of_sup_DC' _ HCS HC H2, rw DC7.DC', rw h},
              {cases h,
                {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                 apply DC8.card_le_of_sup_DC' _ HCS HC H2, rw DC8.DC', rw h},
                {cases h,
                  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                   apply DC9.card_le_of_sup_DC' _ HCS HC H2, rw DC9.DC', rw h},
                  {cases h,
                    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                     apply le_succ_of_le, apply DC10.card_le_of_sup_DC' _ HCS HC H2, 
                     rw DC10.DC', rw h},
                    {cases h,
                      {unfold DCs_sup_DC_len8, rw mem_union, left,
                       apply DC11.mem_DCs_sup_DC'_len8 _ HCS HC H1 H2, rw DC11.DC', rw h},
                      {cases h,
                        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                         apply DC12.card_le_of_sup_DC' _ HCS HC H2, rw DC12.DC', rw h},
                        {cases h,
                          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                           apply DC13.card_le_of_sup_DC' _ HCS HC H2, rw DC13.DC', rw h},
                          {cases h,
                            {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                             apply DC14.card_le_of_sup_DC' _ HCS HC H2, rw DC14.DC', rw h},
                            {cases h,
                              {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                               apply DC15.card_le_of_sup_DC' _ HCS HC H2, rw DC15.DC', rw h},
                              {cases h,
                                {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                 apply le_succ_of_le, apply DC16.card_le_of_sup_DC' _ HCS HC H2, 
                                 rw DC16.DC', rw h},
                                {cases h,
                                  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                   apply DC17.card_le_of_sup_DC' _ HCS HC H2, rw DC17.DC', rw h},
                                  {cases h,
                                    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                     apply DC18.card_le_of_sup_DC' _ HCS HC H2, rw DC18.DC', rw h},
                                    {cases h,
                                      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                       apply le_succ_of_le, apply DC19.card_le_of_sup_DC' _ HCS HC H2, 
                                       rw DC19.DC', rw h},
                                      {cases h,
                                        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                         apply DC20.card_le_of_sup_DC' _ HCS HC H2, rw DC20.DC', rw h},
                                        {cases h,
                                          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                           apply DC21.card_le_of_sup_DC' _ HCS HC H2, rw DC21.DC', rw h},
                                          {cases h,
                                            {unfold DCs_sup_DC_len8, rw mem_union, right,
                                             apply DC22.mem_DCs_sup_DC'_len8 _ HCS HC  H1 H2, rw DC22.DC', rw h},
                                            {cases h,
                                              {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                               apply DC23.card_le_of_sup_DC' _ HCS HC H2, rw DC23.DC', rw h},
                                              {cases h,
                                                {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                                 apply DC24.card_le_of_sup_DC' _ HCS HC H2, rw DC24.DC', rw h},
                                                {cases h,
                                                  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                                   apply DC25.card_le_of_sup_DC' _ HCS HC H2, rw DC25.DC', rw h},
                                                  {cases h,
                                                    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                                     apply DC26.card_le_of_sup_DC' _ HCS HC H2, rw DC26.DC', rw h},
                                                    {apply false.elim h}}}}}}}}}}}}}}}}}}}}}}}}}}
end

end card3

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
  card4.DCs_sup_DC_len8 ∪ card3.DCs_sup_DC_len8

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  C ∈ DCs_sup_DC_len8 :=
begin
unfold DCs_sup_DC_len8, rw mem_union, 
cases eq_or_lt_of_le (card_Cwr_2_2_le _ HCS HC  H2) with heq hlt,
  {left, apply card4.mem_DCs_sup_DC_len8 _ HCS HC  H1 H2 heq},
  {right, apply card3.mem_DCs_sup_DC_len8 _ HCS HC  H1 H2,
   apply le_antisymm,
    {apply le_of_lt_succ hlt},
    {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}}
end

end DC4

namespace DC5 

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 3 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 3 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

def DCs'_list : list (finset (vector B 7)) :=
[{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}]

lemma DCs'_list_to_finset : 
  DCs'_list.to_finset = DCs' := dec_trivial

lemma mem_DCs'_list (s : finset (vector B 7)) : 
  s ∈ DCs'_list ↔ s ∈ DCs' :=
by {rw ← DCs'_list_to_finset, rw ← list.mem_to_finset}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

lemma sdiff_dB_DC_eq : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC_eq at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 6 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

namespace DC6

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC6

namespace DC7

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC7

namespace DC8

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC8

namespace DC9

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC9

namespace DC10

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC' 3 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC' 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC')  : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_Cwr_ge_2_3
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) = 2 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_3_le _ HCS HC  H2 H3},
  {rw ← card_Cwr_add_add_ge _ HCS at H1,
   rw H2 at H1, rw card_DC at H1, rw H3 at H1, rw card_DC' at H1,
   rw add_comm at H1, rw ← add_assoc at H1, 
   repeat {rw succ_le_succ_iff at H1}, apply H1}
end

def DCs_sub_sdiff_dB_DC_len2 : finset (finset (vector B 7)) :=
{{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}}

lemma DCs_sub_sdiff_dB_DC_len2_eq' : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len' sdiff_dB_DC' 2 := rfl

lemma DCs_sub_sdiff_dB_DC_len2_eq : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len sdiff_dB_DC' 2:= 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2_eq'}

lemma DC_union_DC'_union : 
  DC ∪ DC' ∪ {⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩} := dec_trivial

def DCs_sup_DC'_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}}

lemma mem_DCs_sup_DC'_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  C ∈ DCs_sup_DC'_len8 := 
begin
rw ← Cwr_union_union_ge C HCS,
have h : Cwr_ge C 2 3 ∈ DCs_sub_sdiff_dB_DC_len2,
  {rw DCs_sub_sdiff_dB_DC_len2_eq, rw sdiff_dB_DC_eq,
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, rw ← H3, apply Cwr_ge_2_3_mem _ HCS HC },
    {apply card_Cwr_ge_2_3 _ HCS HC  H1 H2 H3}},
cases h,
  {rw H2, rw H3, rw h, rw DC_union_DC'_union, rw DCs_sup_DC'_len8, left, refl},
  {apply false.elim h}
end

end DC10

namespace DC11

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC11

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
  DC10.DCs_sup_DC'_len8

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  C ∈ DCs_sup_DC_len8 :=
begin
have h : Cwr C 2 2 ∈ DCs',
  {rw DCs'_eq, rw sdiff_dB_DC_eq, 
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, apply Cwr_2_2_mem _ HCS HC },
    {apply card_Cwr_2_2 _ HCS HC  H1 H2}},
rw ← mem_DCs'_list at h,
rw DCs'_list at h, cases h,
  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
   apply DC1.card_le_of_sup_DC' _ HCS HC H2, rw DC1.DC', rw h},
  {cases h,
    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
     apply DC2.card_le_of_sup_DC' _ HCS HC H2, rw DC2.DC', rw h},
    {cases h,
      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
       apply le_succ_of_le, apply DC3.card_le_of_sup_DC' _ HCS HC H2,
       rw DC3.DC', rw h},
      {cases h,
        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
         apply DC4.card_le_of_sup_DC' _ HCS HC H2, rw DC4.DC', rw h},
        {cases h,
          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
           apply DC5.card_le_of_sup_DC' _ HCS HC H2, rw DC5.DC', rw h},
          {cases h,
            {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
             apply DC6.card_le_of_sup_DC' _ HCS HC H2, rw DC6.DC', rw h},
              {cases h,
              {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
               apply DC7.card_le_of_sup_DC' _ HCS HC H2, rw DC7.DC', rw h},
              {cases h,
                {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                 apply DC8.card_le_of_sup_DC' _ HCS HC H2, rw DC8.DC', rw h},
                {cases h,
                  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                   apply DC9.card_le_of_sup_DC' _ HCS HC H2, rw DC9.DC', rw h},
                  {cases h,
                    {unfold DCs_sup_DC_len8, 
                     apply DC10.mem_DCs_sup_DC'_len8 _ HCS HC  H1 H2, rw DC10.DC', rw h},
                    {cases h,
                      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                       apply DC11.card_le_of_sup_DC' _ HCS HC H2, rw DC11.DC', rw h},
                      {apply false.elim h}}}}}}}}}}}
end

end DC5

namespace DC6

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 3 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 3 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

def DCs'_list : list (finset (vector B 7)) :=
[{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}]

lemma DCs'_list_to_finset : 
  DCs'_list.to_finset = DCs' := dec_trivial

lemma mem_DCs'_list (s : finset (vector B 7)) : 
  s ∈ DCs'_list ↔ s ∈ DCs' :=
by {rw ← DCs'_list_to_finset, rw ← list.mem_to_finset}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

namespace DC6

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC6

namespace DC7

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC7

namespace DC8

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC' 3 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC' 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC')  : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_Cwr_ge_2_3
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) = 2 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_3_le _ HCS HC  H2 H3},
  {rw ← card_Cwr_add_add_ge _ HCS at H1,
   rw H2 at H1, rw card_DC at H1, rw H3 at H1, rw card_DC' at H1,
   rw add_comm at H1, rw ← add_assoc at H1, 
   repeat {rw succ_le_succ_iff at H1}, apply H1}
end

def DCs_sub_sdiff_dB_DC_len2 : finset (finset (vector B 7)) :=
{{⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}}

lemma DCs_sub_sdiff_dB_DC_len2_eq' : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len' sdiff_dB_DC' 2 := rfl

lemma DCs_sub_sdiff_dB_DC_len2_eq : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len sdiff_dB_DC' 2:= 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2_eq'}

lemma DC_union_DC'_union : 
  DC ∪ DC' ∪ {⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩} := dec_trivial

def DCs_sup_DC'_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}}

lemma mem_DCs_sup_DC'_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  C ∈ DCs_sup_DC'_len8 := 
begin
rw ← Cwr_union_union_ge C HCS,
have h : Cwr_ge C 2 3 ∈ DCs_sub_sdiff_dB_DC_len2,
  {rw DCs_sub_sdiff_dB_DC_len2_eq, rw sdiff_dB_DC_eq,
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, rw ← H3, apply Cwr_ge_2_3_mem _ HCS HC },
    {apply card_Cwr_ge_2_3 _ HCS HC  H1 H2 H3}},
cases h,
  {rw H2, rw H3, rw h, rw DC_union_DC'_union, rw DCs_sup_DC'_len8, left, refl},
  {apply false.elim h}
end

end DC8

namespace DC9

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC9

namespace DC10

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC10

namespace DC11

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC11

namespace DC12

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC12

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
  DC8.DCs_sup_DC'_len8

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  C ∈ DCs_sup_DC_len8 :=
begin
have h : Cwr C 2 2 ∈ DCs',
  {rw DCs'_eq, rw sdiff_dB_DC_eq, 
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, apply Cwr_2_2_mem _ HCS HC },
    {apply card_Cwr_2_2 _ HCS HC  H1 H2}},
rw ← mem_DCs'_list at h,
rw DCs'_list at h, cases h,
  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
   apply DC1.card_le_of_sup_DC' _ HCS HC H2, rw DC1.DC', rw h},
  {cases h,
    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
     apply DC2.card_le_of_sup_DC' _ HCS HC H2, rw DC2.DC', rw h},
    {cases h,
      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
       apply DC3.card_le_of_sup_DC' _ HCS HC H2, rw DC3.DC', rw h},
      {cases h,
        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
         apply DC4.card_le_of_sup_DC' _ HCS HC H2, rw DC4.DC', rw h},
        {cases h,
          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
           apply DC5.card_le_of_sup_DC' _ HCS HC H2, rw DC5.DC', rw h},
          {cases h,
            {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
             apply DC6.card_le_of_sup_DC' _ HCS HC H2, rw DC6.DC', rw h},
              {cases h,
              {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
               apply DC7.card_le_of_sup_DC' _ HCS HC H2, rw DC7.DC', rw h},
              {cases h,
                {unfold DCs_sup_DC_len8, 
                 apply DC8.mem_DCs_sup_DC'_len8 _ HCS HC  H1 H2, rw DC8.DC', rw h},
                {cases h,
                  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                   apply DC9.card_le_of_sup_DC' _ HCS HC H2, rw DC9.DC', rw h},
                  {cases h,
                    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                     apply DC10.card_le_of_sup_DC' _ HCS HC H2, rw DC10.DC', rw h},
                    {cases h,
                      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                       apply DC11.card_le_of_sup_DC' _ HCS HC H2, rw DC11.DC', rw h},
                      {cases h,
                        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                         apply DC12.card_le_of_sup_DC' _ HCS HC H2, rw DC12.DC', rw h},
                        {apply false.elim h}}}}}}}}}}}}
end

end DC6

namespace DC7

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩} 

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 3 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 3 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : Cwr C 2 2 ∈ DCs',
    {rw DCs'_eq, rw sdiff_dB_DC_eq, 
     rw mem_DCs_sub_len', apply and.intro,
      {rw ← H, apply Cwr_2_2_mem _ HCS HC },
      {apply card_Cwr_2_2 _ HCS HC  h1 H}},
  rw DCs' at h2, cases h2,
    {apply DC4.card_le_of_sup_DC' _ HCS HC H, rw DC4.DC', rw h2},
    {cases h2,
      {apply DC3.card_le_of_sup_DC' _ HCS HC H, rw DC3.DC', rw h2},
      {cases h2,
        {apply DC2.card_le_of_sup_DC' _ HCS HC H, rw DC2.DC', rw h2},
        {cases h2,
          {apply DC1.card_le_of_sup_DC' _ HCS HC H, rw DC1.DC', rw h2},
          {apply false.elim h2}}}}}
end

end DC7

namespace DC8 

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 3 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 3 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

def DCs'_list : list (finset (vector B 7)) :=
[{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}]

lemma DCs'_list_to_finset : 
  DCs'_list.to_finset = DCs' := dec_trivial

lemma mem_DCs'_list (s : finset (vector B 7)) : 
  s ∈ DCs'_list ↔ s ∈ DCs' :=
by {rw ← DCs'_list_to_finset, rw ← list.mem_to_finset}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

namespace DC6

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC6

namespace DC7

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC7

namespace DC8

def DC' : finset (vector B 7) :=
{⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC8

namespace DC9

def DC' : finset (vector B 7) :=
{⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC9

namespace DC10

def DC' : finset (vector B 7) :=
{⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC' 3 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC' 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC')  : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_Cwr_ge_2_3
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) = 2 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_3_le _ HCS HC  H2 H3},
  {rw ← card_Cwr_add_add_ge _ HCS at H1,
   rw H2 at H1, rw card_DC at H1, rw H3 at H1, rw card_DC' at H1,
   rw add_comm at H1, rw ← add_assoc at H1, 
   repeat {rw succ_le_succ_iff at H1}, apply H1}
end

def DCs_sub_sdiff_dB_DC_len2 : finset (finset (vector B 7)) :=
{{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩}}

lemma DCs_sub_sdiff_dB_DC_len2_eq' : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len' sdiff_dB_DC' 2 := rfl

lemma DCs_sub_sdiff_dB_DC_len2_eq : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len sdiff_dB_DC' 2:= 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2_eq'}

lemma DC_union_DC'_union : 
  DC ∪ DC' ∪ {⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩} = {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩} := dec_trivial

def DCs_sup_DC'_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}}

lemma mem_DCs_sup_DC'_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  C ∈ DCs_sup_DC'_len8 := 
begin
rw ← Cwr_union_union_ge C HCS,
have h : Cwr_ge C 2 3 ∈ DCs_sub_sdiff_dB_DC_len2,
  {rw DCs_sub_sdiff_dB_DC_len2_eq, rw sdiff_dB_DC_eq,
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, rw ← H3, apply Cwr_ge_2_3_mem _ HCS HC },
    {apply card_Cwr_ge_2_3 _ HCS HC  H1 H2 H3}},
cases h,
  {rw H2, rw H3, rw h, rw DC_union_DC'_union, rw DCs_sup_DC'_len8, left, refl},
  {apply false.elim h}
end

end DC10

namespace DC11

def DC' : finset (vector B 7) :=
{⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC11

namespace DC12

def DC' : finset (vector B 7) :=
{⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, I, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC12

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
  DC10.DCs_sup_DC'_len8

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  C ∈ DCs_sup_DC_len8 :=
begin
have h : Cwr C 2 2 ∈ DCs',
  {rw DCs'_eq, rw sdiff_dB_DC_eq, 
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, apply Cwr_2_2_mem _ HCS HC },
    {apply card_Cwr_2_2 _ HCS HC  H1 H2}},
rw ← mem_DCs'_list at h,
rw DCs'_list at h, cases h,
  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
   apply DC1.card_le_of_sup_DC' _ HCS HC H2, rw DC1.DC', rw h},
  {cases h,
    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
     apply DC2.card_le_of_sup_DC' _ HCS HC H2, rw DC2.DC', rw h},
    {cases h,
      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
       apply DC3.card_le_of_sup_DC' _ HCS HC H2, rw DC3.DC', rw h},
      {cases h,
        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
         apply DC4.card_le_of_sup_DC' _ HCS HC H2, rw DC4.DC', rw h},
        {cases h,
          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
           apply DC5.card_le_of_sup_DC' _ HCS HC H2, rw DC5.DC', rw h},
          {cases h,
            {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
             apply DC6.card_le_of_sup_DC' _ HCS HC H2, rw DC6.DC', rw h},
              {cases h,
              {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
               apply DC7.card_le_of_sup_DC' _ HCS HC H2, rw DC7.DC', rw h},
              {cases h,
                {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                 apply DC8.card_le_of_sup_DC' _ HCS HC H2, rw DC8.DC', rw h},
                {cases h,
                  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                   apply DC9.card_le_of_sup_DC' _ HCS HC H2, rw DC9.DC', rw h},
                  {cases h,
                    {unfold DCs_sup_DC_len8, 
                     apply DC10.mem_DCs_sup_DC'_len8 _ HCS HC  H1 H2, rw DC10.DC', rw h},
                    {cases h,
                      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                       apply DC11.card_le_of_sup_DC' _ HCS HC H2, rw DC11.DC', rw h},
                      {cases h,
                        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                         apply DC12.card_le_of_sup_DC' _ HCS HC H2, rw DC12.DC', rw h},
                        {apply false.elim h}}}}}}}}}}}}
end

end DC8

namespace DC9 

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : 3 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC  h1, rw H, rw card_DC},
   apply absurd h2, apply not_le_of_gt, apply lt_succ_of_le,
   apply card_Cwr_2_2_le _ HCS HC H}
end

end DC9

namespace DC10 

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 3 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 3 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

def DCs'_list : list (finset (vector B 7)) :=
[{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}]

lemma DCs'_list_to_finset : 
  DCs'_list.to_finset = DCs' := dec_trivial

lemma mem_DCs'_list (s : finset (vector B 7)) : 
  s ∈ DCs'_list ↔ s ∈ DCs' :=
by {rw ← DCs'_list_to_finset, rw ← list.mem_to_finset}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

namespace DC6

def DC' : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

lemma sdiff_dB_DC_eq : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC_eq at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 6 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC6

namespace DC7

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC' 3 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC' 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC')  : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_Cwr_ge_2_3
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) = 2 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_3_le _ HCS HC  H2 H3},
  {rw ← card_Cwr_add_add_ge _ HCS at H1,
   rw H2 at H1, rw card_DC at H1, rw H3 at H1, rw card_DC' at H1,
   rw add_comm at H1, rw ← add_assoc at H1, 
   repeat {rw succ_le_succ_iff at H1}, apply H1}
end

def DCs_sub_sdiff_dB_DC_len2 : finset (finset (vector B 7)) :=
{{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}}

lemma DCs_sub_sdiff_dB_DC_len2_eq' : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len' sdiff_dB_DC' 2 := rfl

lemma DCs_sub_sdiff_dB_DC_len2_eq : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len sdiff_dB_DC' 2:= 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2_eq'}

lemma DC_union_DC'_union : 
  DC ∪ DC' ∪ {⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩} = {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩} := dec_trivial

def DCs_sup_DC'_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}}

lemma mem_DCs_sup_DC'_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  C ∈ DCs_sup_DC'_len8 := 
begin
rw ← Cwr_union_union_ge C HCS,
have h : Cwr_ge C 2 3 ∈ DCs_sub_sdiff_dB_DC_len2,
  {rw DCs_sub_sdiff_dB_DC_len2_eq, rw sdiff_dB_DC_eq,
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, rw ← H3, apply Cwr_ge_2_3_mem _ HCS HC },
    {apply card_Cwr_ge_2_3 _ HCS HC  H1 H2 H3}},
cases h,
  {rw H2, rw H3, rw h, rw DC_union_DC'_union, rw DCs_sup_DC'_len8, left, refl},
  {apply false.elim h}
end

end DC7

namespace DC8

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC8

namespace DC9

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC9

namespace DC10

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC10

namespace DC11

def DC' : finset (vector B 7) :=
{⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC11

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
  DC7.DCs_sup_DC'_len8

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  C ∈ DCs_sup_DC_len8 :=
begin
have h : Cwr C 2 2 ∈ DCs',
  {rw DCs'_eq, rw sdiff_dB_DC_eq, 
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, apply Cwr_2_2_mem _ HCS HC },
    {apply card_Cwr_2_2 _ HCS HC  H1 H2}},
rw ← mem_DCs'_list at h,
rw DCs'_list at h, cases h,
  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
   apply DC1.card_le_of_sup_DC' _ HCS HC H2, rw DC1.DC', rw h},
  {cases h,
    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
     apply DC2.card_le_of_sup_DC' _ HCS HC H2, rw DC2.DC', rw h},
    {cases h,
      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
       apply DC3.card_le_of_sup_DC' _ HCS HC H2, rw DC3.DC', rw h},
      {cases h,
        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
         apply DC4.card_le_of_sup_DC' _ HCS HC H2, rw DC4.DC', rw h},
        {cases h,
          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
           apply DC5.card_le_of_sup_DC' _ HCS HC H2, rw DC5.DC', rw h},
          {cases h,
            {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
             apply le_succ_of_le, apply DC6.card_le_of_sup_DC' _ HCS HC H2,
             rw DC6.DC', rw h},
              {cases h,
              {unfold DCs_sup_DC_len8, 
               apply DC7.mem_DCs_sup_DC'_len8 _ HCS HC  H1 H2, rw DC7.DC', rw h},
              {cases h,
                {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                 apply DC8.card_le_of_sup_DC' _ HCS HC H2, rw DC8.DC', rw h},
                {cases h,
                  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                   apply DC9.card_le_of_sup_DC' _ HCS HC H2, rw DC9.DC', rw h},
                  {cases h,
                    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                     apply DC10.card_le_of_sup_DC' _ HCS HC H2, rw DC10.DC', rw h},
                    {cases h,
                      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                       apply DC11.card_le_of_sup_DC' _ HCS HC H2, rw DC11.DC', rw h},
                      {apply false.elim h}}}}}}}}}}}
end

end DC10 

namespace DC11 

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : 3 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC  h1, rw H, rw card_DC},
   apply absurd h2, apply not_le_of_gt, apply lt_succ_of_le,
   apply card_Cwr_2_2_le _ HCS HC H}
end

end DC11

namespace DC12

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : 3 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC  h1, rw H, rw card_DC},
   apply absurd h2, apply not_le_of_gt, apply lt_succ_of_le,
   apply card_Cwr_2_2_le _ HCS HC H}
end

end DC12

namespace DC13

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 3 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 3 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : Cwr C 2 2 ∈ DCs',
    {rw DCs'_eq, rw sdiff_dB_DC_eq, 
     rw mem_DCs_sub_len', apply and.intro,
      {rw ← H, apply Cwr_2_2_mem _ HCS HC },
      {apply card_Cwr_2_2 _ HCS HC  h1 H}},
  rw DCs' at h2, cases h2,
    {apply DC4.card_le_of_sup_DC' _ HCS HC H, rw DC4.DC', rw h2},
    {cases h2,
      {apply DC3.card_le_of_sup_DC' _ HCS HC H, rw DC3.DC', rw h2},
      {cases h2,
        {apply DC2.card_le_of_sup_DC' _ HCS HC H, rw DC2.DC', rw h2},
        {cases h2,
          {apply DC1.card_le_of_sup_DC' _ HCS HC H, rw DC1.DC', rw h2},
          {apply false.elim h2}}}}}
end

end DC13

namespace DC14

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 3 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 3 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

def DCs'_list : list (finset (vector B 7)) :=
[{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}]

lemma DCs'_list_to_finset : 
  DCs'_list.to_finset = DCs' := dec_trivial

lemma mem_DCs'_list (s : finset (vector B 7)) : 
  s ∈ DCs'_list ↔ s ∈ DCs' :=
by {rw ← DCs'_list_to_finset, rw ← list.mem_to_finset}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, O, I], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

lemma sdiff_dB_DC_eq : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC_eq at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 6 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

namespace DC6

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, O, I], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC6

namespace DC7

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC7

namespace DC8

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC8

namespace DC9

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC' 3 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC' 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC')  : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_Cwr_ge_2_3
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) = 2 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_3_le _ HCS HC  H2 H3},
  {rw ← card_Cwr_add_add_ge _ HCS at H1,
   rw H2 at H1, rw card_DC at H1, rw H3 at H1, rw card_DC' at H1,
   rw add_comm at H1, rw ← add_assoc at H1, 
   repeat {rw succ_le_succ_iff at H1}, apply H1}
end

def DCs_sub_sdiff_dB_DC_len2 : finset (finset (vector B 7)) :=
{{⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩}}

lemma DCs_sub_sdiff_dB_DC_len2_eq' : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len' sdiff_dB_DC' 2 := rfl

lemma DCs_sub_sdiff_dB_DC_len2_eq : 
  DCs_sub_sdiff_dB_DC_len2 = DCs_sub_len sdiff_dB_DC' 2:= 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2_eq'}

lemma DC_union_DC'_union : 
  DC ∪ DC' ∪ {⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩} = {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩} := dec_trivial

def DCs_sup_DC'_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}}

lemma mem_DCs_sup_DC'_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  C ∈ DCs_sup_DC'_len8 := 
begin
rw ← Cwr_union_union_ge C HCS,
have h : Cwr_ge C 2 3 ∈ DCs_sub_sdiff_dB_DC_len2,
  {rw DCs_sub_sdiff_dB_DC_len2_eq, rw sdiff_dB_DC_eq,
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, rw ← H3, apply Cwr_ge_2_3_mem _ HCS HC },
    {apply card_Cwr_ge_2_3 _ HCS HC  H1 H2 H3}},
cases h,
  {rw H2, rw H3, rw h, rw DC_union_DC'_union, rw DCs_sup_DC'_len8, left, refl},
  {apply false.elim h}
end

end DC9

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
  DC9.DCs_sup_DC'_len8

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  C ∈ DCs_sup_DC_len8 :=
begin
have h : Cwr C 2 2 ∈ DCs',
  {rw DCs'_eq, rw sdiff_dB_DC_eq, 
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, apply Cwr_2_2_mem _ HCS HC },
    {apply card_Cwr_2_2 _ HCS HC  H1 H2}},
rw ← mem_DCs'_list at h,
rw DCs'_list at h, cases h,
  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
   apply DC1.card_le_of_sup_DC' _ HCS HC H2, rw DC1.DC', rw h},
  {cases h,
    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
     apply DC2.card_le_of_sup_DC' _ HCS HC H2, rw DC2.DC', rw h},
    {cases h,
      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
       apply DC3.card_le_of_sup_DC' _ HCS HC H2, rw DC3.DC', rw h},
      {cases h,
        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
         apply le_succ_of_le, apply DC4.card_le_of_sup_DC' _ HCS HC H2, 
         rw DC4.DC', rw h},
        {cases h,
          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
           apply DC5.card_le_of_sup_DC' _ HCS HC H2, rw DC5.DC', rw h},
          {cases h,
            {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
             apply DC6.card_le_of_sup_DC' _ HCS HC H2, rw DC6.DC', rw h},
              {cases h,
              {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
               apply DC7.card_le_of_sup_DC' _ HCS HC H2, rw DC7.DC', rw h},
              {cases h,
                {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                 apply DC8.card_le_of_sup_DC' _ HCS HC H2, rw DC8.DC', rw h},
                {cases h,
                  {unfold DCs_sup_DC_len8, 
                   apply DC9.mem_DCs_sup_DC'_len8 _ HCS HC  H1 H2, rw DC9.DC', rw h},
                  {apply false.elim h}}}}}}}}}
end

end DC14

namespace DC15

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 3 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 3 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, I, O, O, I], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : Cwr C 2 2 ∈ DCs',
    {rw DCs'_eq, rw sdiff_dB_DC_eq, 
     rw mem_DCs_sub_len', apply and.intro,
      {rw ← H, apply Cwr_2_2_mem _ HCS HC },
      {apply card_Cwr_2_2 _ HCS HC  h1 H}},
  rw DCs' at h2, cases h2,
    {apply DC5.card_le_of_sup_DC' _ HCS HC H, rw DC5.DC', rw h2},
    {cases h2,
      {apply DC4.card_le_of_sup_DC' _ HCS HC H, rw DC4.DC', rw h2},
      {cases h2,
        {apply DC3.card_le_of_sup_DC' _ HCS HC H, rw DC3.DC', rw h2},
        {cases h2,
          {apply DC2.card_le_of_sup_DC' _ HCS HC H, rw DC2.DC', rw h2},
          {cases h2,
            {apply DC1.card_le_of_sup_DC' _ HCS HC H, rw DC1.DC', rw h2},
            {apply false.elim h2}}}}}}
end

end DC15

namespace DC16

def DC : finset (vector B 7) :=
{⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 3 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 3 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 3 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, I, O, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 3 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC') : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : Cwr C 2 2 ∈ DCs',
    {rw DCs'_eq, rw sdiff_dB_DC_eq, 
     rw mem_DCs_sub_len', apply and.intro,
      {rw ← H, apply Cwr_2_2_mem _ HCS HC },
      {apply card_Cwr_2_2 _ HCS HC  h1 H}},
  rw DCs' at h2, cases h2,
    {apply DC4.card_le_of_sup_DC' _ HCS HC H, rw DC4.DC', rw h2},
    {cases h2,
      {apply DC3.card_le_of_sup_DC' _ HCS HC H, rw DC3.DC', rw h2},
      {cases h2,
        {apply DC2.card_le_of_sup_DC' _ HCS HC H, rw DC2.DC', rw h2},
        {cases h2,
          {apply DC1.card_le_of_sup_DC' _ HCS HC H, rw DC1.DC', rw h2},
          {apply false.elim h2}}}}}
end

end DC16

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
  DC2.DCs_sup_DC_len8 ∪ DC4.DCs_sup_DC_len8 ∪ DC5.DCs_sup_DC_len8 
  ∪ DC6.DCs_sup_DC_len8 ∪ DC8.DCs_sup_DC_len8 ∪ DC10.DCs_sup_DC_len8 ∪ DC14.DCs_sup_DC_len8

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : card (Cwr C 2 1) = 3) : 
  C ∈ DCs_sup_DC_len8 :=
begin
have h : Cwr C 2 1 ∈ DCs,
  {rw DCs_eq, rw mem_DCs_sub_len, apply and.intro,
    {rw Cwr_W23_2_1_eq, apply Cwr_subset_of_subset HCS},
    {apply and.intro H2 (DelCode_Cwr _ HC 2 1)}},
rw ← mem_DCs_list at h, rw DCs_list at h, 
unfold DCs_sup_DC_len8, repeat {rw mem_union}, cases h,
  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
   apply DC1.card_le_of_sup_DC _ HCS HC , rw DC1.DC, rw h},
  {cases h,
    {left, left, left, left, left, left, apply DC2.mem_DCs_sup_DC_len8 _ HCS HC H1, rw DC2.DC, rw h},
    {cases h,
      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
       apply DC3.card_le_of_sup_DC _ HCS HC, rw DC3.DC, rw h},
      {cases h,
        {left, left, left, left, left, right, apply DC4.mem_DCs_sup_DC_len8 _ HCS HC H1, rw DC4.DC, rw h},
        {cases h, 
          {left, left, left, left, right, apply DC5.mem_DCs_sup_DC_len8 _ HCS HC H1, rw DC5.DC, rw h},
          {cases h, 
            {left, left, left, right, apply DC6.mem_DCs_sup_DC_len8 _ HCS HC H1, rw DC6.DC, rw h},
            {cases h, 
              {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
               apply DC7.card_le_of_sup_DC _ HCS HC, rw DC7.DC, rw h},
              {cases h,
                {left, left, right, apply DC8.mem_DCs_sup_DC_len8 _ HCS HC H1, rw DC8.DC, rw h},
                {cases h,
                  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                   apply DC9.card_le_of_sup_DC _ HCS HC, rw DC9.DC, rw h},
                  {cases h,
                    {left, right, apply DC10.mem_DCs_sup_DC_len8 _ HCS HC H1, rw DC10.DC, rw h},
                    {cases h,
                      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                       apply DC11.card_le_of_sup_DC _ HCS HC, rw DC11.DC, rw h},
                      {cases h,
                        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                         apply DC12.card_le_of_sup_DC _ HCS HC, rw DC12.DC, rw h},
                        {cases h,
                          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                           apply DC13.card_le_of_sup_DC _ HCS HC, rw DC13.DC, rw h},
                          {cases h,
                            {right, apply DC14.mem_DCs_sup_DC_len8 _ HCS HC  H1, rw DC14.DC, rw h},
                            {cases h,
                              {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                               apply DC15.card_le_of_sup_DC _ HCS HC, rw DC15.DC, rw h},
                              {cases h,
                                {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                 apply DC16.card_le_of_sup_DC _ HCS HC, rw DC16.DC, rw h},
                                {apply false.elim h}}}}}}}}}}}}}}}}
end

end card3

namespace card2

lemma card_Cwr_2_2_ge 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : card (Cwr C 2 1) = 2) : 
  5 ≤ card (Cwr C 2 2) :=
by {apply le_trans _ (card_Cwr_2_2_ge_of_card C HC HCS H1 _ H2), refl}

def DCs : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩},
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}}

lemma DCs_eq' : DCs = DCs_sub_len' Cwr_W23_2_1 2 := dec_trivial

lemma DCs_eq : DCs = DCs_sub_len Cwr_W23_2_1 2 := 
by {rw ← DCs_sub_len'_eq, rw DCs_eq'}

def DCs_list : list (finset (vector B 7)) :=
[{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩},
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}]

lemma DCs_list_to_finset : DCs_list.to_finset = DCs := dec_trivial

lemma mem_DCs_list (s : finset (vector B 7)) : 
  s ∈ DCs_list ↔ s ∈ DCs :=
by {rw ← DCs_list_to_finset, rw ← list.mem_to_finset}

namespace DC1

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, 
 ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC1

namespace DC2

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, 
 ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 5 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 5 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

lemma DCs'_succ : DCs_sub_DCs_len_succ sdiff_dB_DC DCs' = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len6 : DCs_sub_len sdiff_dB_DC 6 = ∅ := 
by {rw ← DCs_sub_DCs_len_succ_eq, rw ← DCs'_eq, apply DCs'_succ}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 5 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len6 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 5 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 5 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : Cwr C 2 2 ∈ DCs',
    {rw DCs'_eq, rw sdiff_dB_DC_eq, 
     rw mem_DCs_sub_len', apply and.intro,
      {rw ← H, apply Cwr_2_2_mem _ HCS HC },
      {apply card_Cwr_2_2 _ HCS HC  h1 H}},
  rw DCs' at h2, cases h2,
    {apply DC5.card_le_of_sup_DC' _ HCS HC H, rw DC5.DC', rw h2},
    {cases h2,
      {apply DC4.card_le_of_sup_DC' _ HCS HC H, rw DC4.DC', rw h2},
      {cases h2,
        {apply DC3.card_le_of_sup_DC' _ HCS HC H, rw DC3.DC', rw h2},
        {cases h2,
          {apply DC2.card_le_of_sup_DC' _ HCS HC H, rw DC2.DC', rw h2},
          {cases h2,
            {apply DC1.card_le_of_sup_DC' _ HCS HC H, rw DC1.DC', rw h2},
            {apply false.elim h2}}}}}}
end

end DC2

namespace DC3

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, 
 ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 5 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 5 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

lemma DCs'_succ : DCs_sub_DCs_len_succ sdiff_dB_DC DCs' = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len6 : DCs_sub_len sdiff_dB_DC 6 = ∅ := 
begin
rw ← DCs_sub_DCs_len_succ_eq, rw ← DCs'_eq, 
apply DCs'_succ
end

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 5 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len6 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 5 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 5 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs'_list : list (finset (vector B 7)) :=
[{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}]

lemma DCs'_list_to_finset : 
  DCs'_list.to_finset = DCs' := dec_trivial

lemma mem_DCs'_list (s : finset (vector B 7)) : 
  s ∈ DCs'_list ↔ s ∈ DCs' :=
by {rw ← DCs'_list_to_finset, rw ← list.mem_to_finset}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

namespace DC6

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC6

namespace DC7

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC7

namespace DC8

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC8

namespace DC9

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC9

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : Cwr C 2 2 ∈ DCs',
    {rw DCs'_eq, rw sdiff_dB_DC_eq, 
     rw mem_DCs_sub_len', apply and.intro,
      {rw ← H, apply Cwr_2_2_mem _ HCS HC },
      {apply card_Cwr_2_2 _ HCS HC  h1 H}},
  rw ← mem_DCs'_list at h2, 
  rw DCs'_list at h2, cases h2,
    {apply DC1.card_le_of_sup_DC' _ HCS HC H, rw DC1.DC', rw h2},
    {cases h2,
      {apply DC2.card_le_of_sup_DC' _ HCS HC H, rw DC2.DC', rw h2},
      {cases h2,
        {apply DC3.card_le_of_sup_DC' _ HCS HC H, rw DC3.DC', rw h2},
        {cases h2,
          {apply DC4.card_le_of_sup_DC' _ HCS HC H, rw DC4.DC', rw h2},
          {cases h2,
            {apply DC5.card_le_of_sup_DC' _ HCS HC H, rw DC5.DC', rw h2},
            {cases h2,
              {apply DC6.card_le_of_sup_DC' _ HCS HC H, rw DC6.DC', rw h2},
              {cases h2,
                {apply DC7.card_le_of_sup_DC' _ HCS HC H, rw DC7.DC', rw h2},
                {cases h2,
                  {apply DC8.card_le_of_sup_DC' _ HCS HC H, rw DC8.DC', rw h2},
                  {cases h2,
                    {apply DC9.card_le_of_sup_DC' _ HCS HC H, rw DC9.DC', rw h2},
                    {apply false.elim h2}}}}}}}}}}
end

end DC3

namespace DC4

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, 
 ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 5 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 5 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

lemma DCs'_succ : DCs_sub_DCs_len_succ sdiff_dB_DC DCs' = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len6 : DCs_sub_len sdiff_dB_DC 6 = ∅ := 
begin
rw ← DCs_sub_DCs_len_succ_eq, rw ← DCs'_eq, 
apply DCs'_succ
end

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 5 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len6 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 5 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 5 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs'_list : list (finset (vector B 7)) :=
[{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}]

lemma DCs'_list_to_finset : 
  DCs'_list.to_finset = DCs' := dec_trivial

lemma mem_DCs'_list (s : finset (vector B 7)) : 
  s ∈ DCs'_list ↔ s ∈ DCs' :=
by {rw ← DCs'_list_to_finset, rw ← list.mem_to_finset}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

namespace DC6

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC6

namespace DC7

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[O, O, I, O, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC')  : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_Cwr_ge_2_3
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) = 1 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_3_le _ HCS HC  H2 H3},
  {rw ← card_Cwr_add_add_ge _ HCS at H1,
   rw H2 at H1, rw card_DC at H1, rw H3 at H1, rw card_DC' at H1,
   rw add_comm at H1, rw ← add_assoc at H1, 
   repeat {rw succ_le_succ_iff at H1}, apply H1}
end

def DCs_sub_sdiff_dB_DC_len1 : finset (finset (vector B 7)) :=
{{⟨[O, O, I, O, I, O, I], rfl⟩}}

lemma DCs_sub_sdiff_dB_DC_len1_eq' : 
  DCs_sub_sdiff_dB_DC_len1 = DCs_sub_len' sdiff_dB_DC' 1 := rfl

lemma DCs_sub_sdiff_dB_DC_len1_eq : 
  DCs_sub_sdiff_dB_DC_len1 = DCs_sub_len sdiff_dB_DC' 1 := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len1_eq'}

lemma DC_union_DC'_union : 
  DC ∪ DC' ∪ {⟨[O, O, I, O, I, O, I], rfl⟩} = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩} := dec_trivial

def DCs_sup_DC'_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}}

lemma mem_DCs_sup_DC'_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  C ∈ DCs_sup_DC'_len8 := 
begin
rw ← Cwr_union_union_ge C HCS,
have h : Cwr_ge C 2 3 ∈ DCs_sub_sdiff_dB_DC_len1,
  {rw DCs_sub_sdiff_dB_DC_len1_eq, rw sdiff_dB_DC_eq,
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, rw ← H3, apply Cwr_ge_2_3_mem _ HCS HC },
    {apply card_Cwr_ge_2_3 _ HCS HC  H1 H2 H3}},
cases h,
  {rw H2, rw H3, rw h, rw DC_union_DC'_union, rw DCs_sup_DC'_len8, left, refl},
  {apply false.elim h}
end

end DC7

namespace DC8

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC8

namespace DC9

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC9

namespace DC10

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC10

namespace DC11

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC11

namespace DC12

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC12

namespace DC13

def DC' : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC13

namespace DC14

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC14

namespace DC15

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC15

namespace DC16

def DC' : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

def sdiff_dB_DC' : finset (vector B 7) :=
{⟨[I, O, I, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC' = Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') := rfl

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC' 2 = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC' 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC')  : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr_ge C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_ge3_eq, 
   rw ← H1, rw ← H2, apply Cwr_ge_2_3_subset _ HCS HC}
end

lemma card_Cwr_ge_2_3
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) = 1 :=
begin
apply le_antisymm,
  {apply card_Cwr_ge_2_3_le _ HCS HC  H2 H3},
  {rw ← card_Cwr_add_add_ge _ HCS at H1,
   rw H2 at H1, rw card_DC at H1, rw H3 at H1, rw card_DC' at H1,
   rw add_comm at H1, rw ← add_assoc at H1, 
   repeat {rw succ_le_succ_iff at H1}, apply H1}
end

def DCs_sub_sdiff_dB_DC_len1 : finset (finset (vector B 7)) :=
{{⟨[I, O, I, O, I, O, O], rfl⟩}}

lemma DCs_sub_sdiff_dB_DC_len1_eq' : 
  DCs_sub_sdiff_dB_DC_len1 = DCs_sub_len' sdiff_dB_DC' 1 := rfl

lemma DCs_sub_sdiff_dB_DC_len1_eq : 
  DCs_sub_sdiff_dB_DC_len1 = DCs_sub_len sdiff_dB_DC' 1 := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len1_eq'}

lemma DC_union_DC'_union : 
  DC ∪ DC' ∪ {⟨[I, O, I, O, I, O, O], rfl⟩} = {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩} := dec_trivial

def DCs_sup_DC'_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}}

lemma mem_DCs_sup_DC'_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) (H3 : Cwr C 2 2 = DC') : 
  C ∈ DCs_sup_DC'_len8 := 
begin
rw ← Cwr_union_union_ge C HCS,
have h : Cwr_ge C 2 3 ∈ DCs_sub_sdiff_dB_DC_len1,
  {rw DCs_sub_sdiff_dB_DC_len1_eq, rw sdiff_dB_DC_eq,
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, rw ← H3, apply Cwr_ge_2_3_mem _ HCS HC },
    {apply card_Cwr_ge_2_3 _ HCS HC  H1 H2 H3}},
cases h,
  {rw H2, rw H3, rw h, rw DC_union_DC'_union, rw DCs_sup_DC'_len8, left, refl},
  {apply false.elim h}
end

end DC16

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
  DC7.DCs_sup_DC'_len8 ∪ DC16.DCs_sup_DC'_len8 

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  C ∈ DCs_sup_DC_len8 :=
begin
have h : Cwr C 2 2 ∈ DCs',
  {rw DCs'_eq, rw sdiff_dB_DC_eq, 
   rw mem_DCs_sub_len', apply and.intro,
    {rw ← H2, apply Cwr_2_2_mem _ HCS HC },
    {apply card_Cwr_2_2 _ HCS HC  H1 H2}},
rw ← mem_DCs'_list at h,
rw DCs'_list at h, cases h,
  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
   apply DC1.card_le_of_sup_DC' _ HCS HC H2, rw DC1.DC', rw h},
  {cases h,
    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
     apply DC2.card_le_of_sup_DC' _ HCS HC H2, rw DC2.DC', rw h},
    {cases h,
      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
       apply DC3.card_le_of_sup_DC' _ HCS HC H2, rw DC3.DC', rw h},
      {cases h,
        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
         apply DC4.card_le_of_sup_DC' _ HCS HC H2, rw DC4.DC', rw h},
        {cases h,
          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
           apply DC5.card_le_of_sup_DC' _ HCS HC H2, rw DC5.DC', rw h},
          {cases h,
            {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
             apply DC6.card_le_of_sup_DC' _ HCS HC H2, rw DC6.DC', rw h},
              {cases h,
              {unfold DCs_sup_DC_len8, rw mem_union, left,
               apply DC7.mem_DCs_sup_DC'_len8 _ HCS HC  H1 H2, rw DC7.DC', rw h},
              {cases h,
                {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                 apply DC8.card_le_of_sup_DC' _ HCS HC H2, rw DC8.DC', rw h},
                {cases h,
                  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                   apply DC9.card_le_of_sup_DC' _ HCS HC H2, rw DC9.DC', rw h},
                  {cases h,
                    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                     apply DC10.card_le_of_sup_DC' _ HCS HC H2, rw DC10.DC', rw h},
                    {cases h,
                      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                       apply DC11.card_le_of_sup_DC' _ HCS HC H2, rw DC11.DC', rw h},
                      {cases h,
                        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                         apply DC12.card_le_of_sup_DC' _ HCS HC H2, rw DC12.DC', rw h},
                        {cases h,
                          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                           apply DC13.card_le_of_sup_DC' _ HCS HC H2, rw DC13.DC', rw h},
                          {cases h,
                            {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                             apply DC14.card_le_of_sup_DC' _ HCS HC H2, rw DC14.DC', rw h},
                            {cases h,
                              {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                               apply DC15.card_le_of_sup_DC' _ HCS HC H2, rw DC15.DC', rw h},
                              {cases h,
                                {unfold DCs_sup_DC_len8, rw mem_union, right,
                                 apply DC16.mem_DCs_sup_DC'_len8 _ HCS HC  H1 H2, rw DC16.DC', rw h},
                                {apply false.elim h}}}}}}}}}}}}}}}}
end

end DC4

namespace DC5

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, 
 ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC5

namespace DC6

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, 
 ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC6

namespace DC7

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, 
 ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC7

namespace DC8

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, 
 ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC8

namespace DC9

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, 
 ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC9

namespace DC10

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, 
 ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC10

namespace DC11

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, 
 ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC11

namespace DC12

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, 
 ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC12

namespace DC13

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, 
 ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC13

namespace DC14

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, 
 ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC14

namespace DC15

def DC : finset (vector B 7) :=
{⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, 
 ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC15

namespace DC16

def DC : finset (vector B 7) :=
{⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, 
 ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 5 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 5 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

lemma DCs'_succ : DCs_sub_DCs_len_succ sdiff_dB_DC DCs' = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len6 : DCs_sub_len sdiff_dB_DC 6 = ∅ := 
begin
rw ← DCs_sub_DCs_len_succ_eq, rw ← DCs'_eq,
apply DCs'_succ
end

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 5 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len6 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 5 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 5 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

def DCs'_list : list (finset (vector B 7)) :=
[{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}]

lemma DCs'_list_to_finset : 
  DCs'_list.to_finset = DCs' := dec_trivial

lemma mem_DCs'_list (s : finset (vector B 7)) : 
  s ∈ DCs'_list ↔ s ∈ DCs' :=
by {rw ← DCs'_list_to_finset, rw ← list.mem_to_finset}

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

namespace DC6

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC6

namespace DC7

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC7

namespace DC8

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC8

namespace DC9

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC9

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : Cwr C 2 2 ∈ DCs',
    {rw DCs'_eq, rw sdiff_dB_DC_eq, 
     rw mem_DCs_sub_len', apply and.intro,
      {rw ← H, apply Cwr_2_2_mem _ HCS HC },
      {apply card_Cwr_2_2 _ HCS HC  h1 H}},
  rw ← mem_DCs'_list at h2, 
  rw DCs'_list at h2, cases h2,
    {apply DC1.card_le_of_sup_DC' _ HCS HC H, rw DC1.DC', rw h2},
    {cases h2,
      {apply DC2.card_le_of_sup_DC' _ HCS HC H, rw DC2.DC', rw h2},
      {cases h2,
        {apply DC3.card_le_of_sup_DC' _ HCS HC H, rw DC3.DC', rw h2},
        {cases h2,
          {apply DC4.card_le_of_sup_DC' _ HCS HC H, rw DC4.DC', rw h2},
          {cases h2,
            {apply DC5.card_le_of_sup_DC' _ HCS HC H, rw DC5.DC', rw h2},
            {cases h2,
              {apply DC6.card_le_of_sup_DC' _ HCS HC H, rw DC6.DC', rw h2},
              {cases h2,
                {apply DC7.card_le_of_sup_DC' _ HCS HC H, rw DC7.DC', rw h2},
                {cases h2,
                  {apply DC8.card_le_of_sup_DC' _ HCS HC H, rw DC8.DC', rw h2},
                  {cases h2,
                    {apply DC9.card_le_of_sup_DC' _ HCS HC H, rw DC9.DC', rw h2},
                    {apply false.elim h2}}}}}}}}}}
end

end DC16

namespace DC17

def DC : finset (vector B 7) :=
{⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, 
 ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC17

namespace DC18

def DC : finset (vector B 7) :=
{⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, 
 ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

def DCs' : finset (finset (vector B 7)) :=
{{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}}

lemma DCs'_eq' : DCs' = DCs_sub_len' sdiff_dB_DC 5 := dec_trivial

lemma DCs'_eq : DCs' = DCs_sub_len sdiff_dB_DC 5 := 
by {rw ← DCs_sub_len'_eq, rw DCs'_eq'}

lemma DCs'_succ : DCs_sub_DCs_len_succ sdiff_dB_DC DCs' = ∅ := rfl

lemma DCs_sub_sdiff_dB_DC_len6 : DCs_sub_len sdiff_dB_DC 6 = ∅ := 
begin
rw ← DCs_sub_DCs_len_succ_eq, rw ← DCs'_eq, 
apply DCs'_succ
end

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 5 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len6 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 5 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_Cwr_2_2 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : 8 ≤ card C) (H2 : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) = 5 :=
begin
apply le_antisymm,
  {apply card_Cwr_2_2_le _ HCS HC  H2},
  {apply card_Cwr_2_2_ge _ HCS HC  H1, rw H2, rw card_DC}
end

namespace DC1

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC1

namespace DC2

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC2

namespace DC3

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC3

namespace DC4

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC4

namespace DC5

def DC' : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC' : card DC' = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_ge3 \ union_dB (DC ∪ DC') = ∅ := rfl

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_ge3 \ union_dB (DC ∪ DC')) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_Cwr_ge_2_3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card (Cwr_ge C 2 3) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw Cwr_W23_2_ge3_eq, rw ← H1, rw ← H2, 
apply Cwr_ge_2_3_subset _ HCS HC
end

lemma card_le_of_sup_DC'
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  
  (H1 : Cwr C 2 1 = DC) (H2 : Cwr C 2 2 = DC') : 
  card C ≤ 7 := 
begin
rw ← card_Cwr_add_add_ge _ HCS, 
rw H1, rw card_DC, rw H2, rw card_DC',
rw add_comm, repeat {apply succ_le_succ},
apply card_Cwr_ge_2_3_le _ HCS HC  H1 H2
end

end DC5

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : Cwr C 2 2 ∈ DCs',
    {rw DCs'_eq, rw sdiff_dB_DC_eq, 
     rw mem_DCs_sub_len', apply and.intro,
      {rw ← H, apply Cwr_2_2_mem _ HCS HC },
      {apply card_Cwr_2_2 _ HCS HC  h1 H}},
  rw DCs' at h2, cases h2,
    {apply DC5.card_le_of_sup_DC' _ HCS HC H, rw DC5.DC', rw h2},
    {cases h2,
      {apply DC4.card_le_of_sup_DC' _ HCS HC H, rw DC4.DC', rw h2},
      {cases h2,
        {apply DC3.card_le_of_sup_DC' _ HCS HC H, rw DC3.DC', rw h2},
        {cases h2,
          {apply DC2.card_le_of_sup_DC' _ HCS HC H, rw DC2.DC', rw h2},
          {cases h2,
            {apply DC1.card_le_of_sup_DC' _ HCS HC H, rw DC1.DC', rw h2},
            {apply false.elim h2}}}}}}
end

end DC18

namespace DC19

def DC : finset (vector B 7) :=
{⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, 
 ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC19

namespace DC20

def DC : finset (vector B 7) :=
{⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 2 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, 
 ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len5' : DCs_sub_len' sdiff_dB_DC 5 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len5 : DCs_sub_len sdiff_dB_DC 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len5'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len5 _ HCS HC

lemma card_Cwr_2_2_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC) : 
  card (Cwr C 2 2) ≤ 4 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_Cwr C HC},
  {rw sdiff_dB_DC_eq, rw Cwr_W23_2_2_eq, rw ← H, 
   apply Cwr_2_2_subset _ HCS HC}
end

lemma card_le_of_sup_DC (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : Cwr C 2 1 = DC)   : 
  card C ≤ 7 := 
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h : 5 ≤ card (Cwr C 2 2),
    {apply card_Cwr_2_2_ge _ HCS HC ,
      {apply succ_le_of_lt (lt_of_not_ge hnle)},
      {rw H, rw card_DC}},
   apply absurd h, rw not_le, 
   apply lt_succ_of_le (card_Cwr_2_2_le _ HCS HC  H)}
end

end DC20

def DCs_sup_DC_len8 : finset (finset (vector B 7)) :=
  DC4.DCs_sup_DC_len8 

lemma mem_DCs_sup_DC_len8
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : card (Cwr C 2 1) = 2) : 
  C ∈ DCs_sup_DC_len8 :=
begin
have h : Cwr C 2 1 ∈ DCs,
  {rw DCs_eq, rw mem_DCs_sub_len, apply and.intro,
    {rw Cwr_W23_2_1_eq, apply Cwr_subset_of_subset HCS},
    {apply and.intro H2 (DelCode_Cwr _ HC 2 1)}},
rw ← mem_DCs_list at h, rw DCs_list at h, cases h,
  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
   apply DC1.card_le_of_sup_DC _ HCS HC , rw DC1.DC, rw h},
  {cases h,
    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
     apply DC2.card_le_of_sup_DC _ HCS HC , rw DC2.DC, rw h},
    {cases h,
      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
       apply DC3.card_le_of_sup_DC _ HCS HC , rw DC3.DC, rw h},
      {cases h,
        {unfold DCs_sup_DC_len8, 
         apply DC4.mem_DCs_sup_DC_len8 _ HCS HC  H1, rw DC4.DC, rw h},
        {cases h, 
          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
           apply DC5.card_le_of_sup_DC _ HCS HC , rw DC5.DC, rw h},
          {cases h, 
            {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
             apply DC6.card_le_of_sup_DC _ HCS HC , rw DC6.DC, rw h},
            {cases h, 
              {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
               apply DC7.card_le_of_sup_DC _ HCS HC , rw DC7.DC, rw h},
              {cases h,
                {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                 apply DC8.card_le_of_sup_DC _ HCS HC , rw DC8.DC, rw h},
                {cases h,
                  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                   apply DC9.card_le_of_sup_DC _ HCS HC , rw DC9.DC, rw h},
                  {cases h,
                    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                     apply DC10.card_le_of_sup_DC _ HCS HC , rw DC10.DC, rw h},
                    {cases h,
                      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                       apply DC11.card_le_of_sup_DC _ HCS HC , rw DC11.DC, rw h},
                      {cases h,
                        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                         apply DC12.card_le_of_sup_DC _ HCS HC , rw DC12.DC, rw h},
                        {cases h,
                          {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                           apply DC13.card_le_of_sup_DC _ HCS HC , rw DC13.DC, rw h},
                          {cases h,
                            {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                             apply DC14.card_le_of_sup_DC _ HCS HC , rw DC14.DC, rw h},
                            {cases h,
                              {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                               apply DC15.card_le_of_sup_DC _ HCS HC , rw DC15.DC, rw h},
                              {cases h,
                                {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                 apply DC16.card_le_of_sup_DC _ HCS HC , rw DC16.DC, rw h},
                                {cases h,
                                  {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                   apply DC17.card_le_of_sup_DC _ HCS HC , rw DC17.DC, rw h},
                                  {cases h,
                                    {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                     apply DC18.card_le_of_sup_DC _ HCS HC , rw DC18.DC, rw h},
                                    {cases h,
                                      {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                       apply DC19.card_le_of_sup_DC _ HCS HC , rw DC19.DC, rw h},
                                      {cases h,
                                        {apply absurd H1, apply not_le_of_gt, apply nat.lt_succ_of_le,
                                         apply DC20.card_le_of_sup_DC _ HCS HC , rw DC20.DC, rw h},
                                        {apply false.elim h}}}}}}}}}}}}}}}}}}}}
end

end card2

namespace card1

lemma card_Cwr_2_2_ge 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C) 
  (H1 : 8 ≤ card C) (H2 : card (Cwr C 2 1) = 1) : 
  7 ≤ card (Cwr C 2 2) :=
by {apply le_trans _ (card_Cwr_2_2_ge_of_card C HC HCS H1 _ H2), refl}

lemma div_wt_of_sub_Cwr_W23_2_2
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2) : 
  filter (λ x, wt x = 2) C ∪ filter (λ x, wt x = 3) C = C := 
begin
apply subset.antisymm,
  {apply union_subset,
    {apply filter_subset},
    {apply filter_subset}},
  {intros x hx, 
   have h : x ∈ W23,
    {rw Cwr_W23_2_2_eq at HCS, rw Cwr at HCS, 
     apply filter_subset _ (HCS hx)},
   rw W23_eq at h, rw mem_filter at h,  unfold Icc_wt at h,
   cases eq_or_lt_of_le h.right.right with heq hgt, 
    {rw mem_union, right, rw mem_filter, apply and.intro hx heq},
    {rw mem_union, left, rw mem_filter, 
     apply and.intro hx (le_antisymm (le_of_lt_succ hgt) h.right.left)}}
end

lemma card_div_wt_of_sub_Cwr_W23_2_2
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2) : 
  card (filter (λ x, wt x = 2) C) + card (filter (λ x, wt x = 3) C) = card C := 
begin
rw ← div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw card_union_of_disjoint, 
  {rw div_wt_of_sub_Cwr_W23_2_2 C HCS},
  {rw filter_wt_eq_inter_of_ne, 
   apply nat.ne_of_lt, apply lt_succ_self}
end

lemma filter_wt3_subset
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2) (HC : is_DelCode C) : 
  filter (λ x, wt x = 3) C ⊆ Cwr_W23_2_2 \ union_dB (filter (λ x, wt x = 2) C) :=
begin
apply subset_union_dB_of_DelCode HC,
    {apply HCS},
    {apply filter_subset},
    {apply filter_subset},
    {apply filter_wt_eq_inter_of_ne, 
     apply nat.ne_of_gt, apply lt_succ_self}
end

lemma filter_wt2_subset
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2) (HC : is_DelCode C) : 
  filter (λ x, wt x = 2) C ⊆ Cwr_W23_2_2 \ union_dB (filter (λ x, wt x = 3) C) :=
begin
apply subset_union_dB_of_DelCode HC,
    {apply HCS},
    {apply filter_subset},
    {apply filter_subset},
    {apply filter_wt_eq_inter_of_ne, 
     apply nat.ne_of_lt, apply lt_succ_self}
end

namespace Cwr_W23_2_2_wt2

def Cwr_W23_2_2_wt2  : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma Cwr_W23_2_2_wt2_eq : Cwr_W23_2_2_wt2 = filter (λ x, wt x = 2) Cwr_W23_2_2 := rfl

lemma DCs_Cwr_W23_2_2_wt2_len5' : DCs_sub_len' Cwr_W23_2_2_wt2 5 = ∅ := rfl

lemma DCs_Cwr_W23_2_2_wt2_len5 : DCs_sub_len Cwr_W23_2_2_wt2 5 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_Cwr_W23_2_2_wt2_len5'}

lemma card_le_of_sub_Cwr_W23_2_2_wt2 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2_wt2) (HC : is_DelCode C) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_Cwr_W23_2_2_wt2_len5 _ HCS HC

lemma card_filter_wt2_le
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2) (HC : is_DelCode C) : 
  card (filter (λ x, wt x = 2) C) ≤ 4 := 
begin
apply card_le_of_sub_Cwr_W23_2_2_wt2,
  {rw Cwr_W23_2_2_wt2_eq, apply filter_subset_filter HCS},
  {apply DelCode_filter _ HC}
end

namespace card4

def DCs_Cwr_W23_2_2_wt2_len4  : finset (finset (vector B 7)) :=
{{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}}

lemma DCs_Cwr_W23_2_2_wt2_len4_eq' : DCs_Cwr_W23_2_2_wt2_len4 = DCs_sub_len' Cwr_W23_2_2_wt2 4 := rfl

lemma DCs_Cwr_W23_2_2_wt2_len4_eq : DCs_Cwr_W23_2_2_wt2_len4 = DCs_sub_len Cwr_W23_2_2_wt2 4 := 
by {rw ← DCs_sub_len'_eq, apply DCs_Cwr_W23_2_2_wt2_len4_eq'}

namespace DC1

def DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 4 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC1

namespace DC2

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 4 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC2

namespace DC3

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 4 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt3_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card C ≤ 4 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC3

namespace DC4

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma card_DC : card DC = 4 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt3_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card C ≤ 4 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC4

lemma card_le_of_card4 (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_2) (HC : is_DelCode C) 
  (H : card (filter (λ x, wt x = 2) C) = 4) : 
  card C ≤ 5 := 
begin
have h : filter (λ x, wt x = 2) C ∈ DCs_Cwr_W23_2_2_wt2_len4,
  {rw DCs_Cwr_W23_2_2_wt2_len4_eq, rw Cwr_W23_2_2_wt2_eq, 
   rw mem_DCs_sub_len, apply and.intro,
    {apply filter_subset_filter HCS},
    {apply and.intro H (DelCode_filter _ HC _)}},
rw DCs_Cwr_W23_2_2_wt2_len4 at h, cases h,
  {apply le_trans (DC4.card_le_of_sup_DC _ HCS HC  _) (le_succ _), rw DC4.DC, rw h},
  {cases h,
    {apply le_trans (DC3.card_le_of_sup_DC _ HCS HC  _) (le_succ _), rw DC3.DC, rw h},
    {cases h,
      {apply DC2.card_le_of_sup_DC  _ HCS HC , rw DC2.DC, rw h},
      {cases h,
        {apply DC1.card_le_of_sup_DC  _ HCS HC , rw DC1.DC, rw h},
        {apply false.elim h}}}}
end

end card4

namespace card3

def DCs_Cwr_W23_2_2_wt2_len3  : finset (finset (vector B 7)) :=
{{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}, 
 {⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}, 
 {⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}}

lemma DCs_Cwr_W23_2_2_wt2_len3_eq' : DCs_Cwr_W23_2_2_wt2_len3 = DCs_sub_len' Cwr_W23_2_2_wt2 3 := dec_trivial

lemma DCs_Cwr_W23_2_2_wt2_len3_eq : DCs_Cwr_W23_2_2_wt2_len3 = DCs_sub_len Cwr_W23_2_2_wt2 3 := 
by {rw ← DCs_sub_len'_eq, apply DCs_Cwr_W23_2_2_wt2_len3_eq'}

def DCs_Cwr_W23_2_2_wt2_len3_list : list (finset (vector B 7)) :=
[{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}, 
 {⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}, 
 {⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}, 
 {⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}, 
 {⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}]

lemma DCs_Cwr_W23_2_2_wt2_len3_list_to_finset : 
  DCs_Cwr_W23_2_2_wt2_len3_list.to_finset = DCs_Cwr_W23_2_2_wt2_len3 := dec_trivial

lemma mem_DCs_Cwr_W23_2_2_wt2_len3_list (s : finset (vector B 7)) : 
  s ∈ DCs_Cwr_W23_2_2_wt2_len3_list ↔ s ∈ DCs_Cwr_W23_2_2_wt2_len3 :=
by {rw ← DCs_Cwr_W23_2_2_wt2_len3_list_to_finset, rw ← list.mem_to_finset}

namespace DC1

def DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 4 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC1

namespace DC2

def DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC2

namespace DC3

def DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC3

namespace DC4

def DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC4

namespace DC5

def DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC5

namespace DC6

def DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC6

namespace DC7

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC7

namespace DC8

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC8

namespace DC9

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC9

namespace DC10

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC10

namespace DC11

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 4 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC11

namespace DC12

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC12

namespace DC13

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC13

namespace DC14

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 4 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC14

namespace DC15

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC15

namespace DC16

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len4' : DCs_sub_len' sdiff_dB_DC 4 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len4 : DCs_sub_len sdiff_dB_DC 4 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len4'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 3 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len4 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 3 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC16

namespace DC17

def DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC17

namespace DC18

def DC : finset (vector B 7) :=
{⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, I, O, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 4 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC18

namespace DC19

def DC : finset (vector B 7) :=
{⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC19

namespace DC20

def DC : finset (vector B 7) :=
{⟨[O, I, I, O, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC20

namespace DC21

def DC : finset (vector B 7) :=
{⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 4 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC21

namespace DC22

def DC : finset (vector B 7) :=
{⟨[O, O, I, I, O, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 3 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt3_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)  : 
  card (filter (λ x, wt x = 3) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt3_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C) (H : filter (λ x, wt x = 2) C = DC)   : 
  card C ≤ 4 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, rw add_comm, repeat {apply succ_le_succ},
apply card_filter_wt3_le _ HCS HC H
end

end DC22

lemma card_le_of_card3 (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_2) (HC : is_DelCode C) 
  (H : card (filter (λ x, wt x = 2) C) = 3) : 
  card C ≤ 6 := 
begin
have h : filter (λ x, wt x = 2) C ∈ DCs_Cwr_W23_2_2_wt2_len3,
  {rw DCs_Cwr_W23_2_2_wt2_len3_eq, rw Cwr_W23_2_2_wt2_eq, 
   rw mem_DCs_sub_len, apply and.intro,
    {apply filter_subset_filter HCS},
    {apply and.intro H (DelCode_filter _ HC _)}},
rw ← mem_DCs_Cwr_W23_2_2_wt2_len3_list at h, 
rw DCs_Cwr_W23_2_2_wt2_len3_list at h, cases h,
  {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
   apply DC1.card_le_of_sup_DC  _ HCS HC  _, rw DC1.DC, rw h},
  {cases h,
    {apply DC2.card_le_of_sup_DC  _ HCS HC , rw DC2.DC, rw h},
    {cases h,
      {apply le_trans (DC3.card_le_of_sup_DC  _ HCS HC  _) (le_succ _), 
       rw DC3.DC, rw h},
      {cases h,
        {apply DC4.card_le_of_sup_DC  _ HCS HC , rw DC4.DC, rw h},
        {cases h, 
          {apply DC5.card_le_of_sup_DC  _ HCS HC , rw DC5.DC, rw h},
          {cases h, 
            {apply DC6.card_le_of_sup_DC  _ HCS HC , rw DC6.DC, rw h},
            {cases h, 
              {apply DC7.card_le_of_sup_DC  _ HCS HC , rw DC7.DC, rw h},
              {cases h,
                {apply le_trans (DC8.card_le_of_sup_DC  _ HCS HC  _) (le_succ _), 
                 rw DC8.DC, rw h},
                {cases h,
                  {apply le_trans (DC9.card_le_of_sup_DC  _ HCS HC  _) (le_succ _), 
                   rw DC9.DC, rw h},
                  {cases h,
                    {apply le_trans (DC10.card_le_of_sup_DC  _ HCS HC  _) (le_succ _), 
                     rw DC10.DC, rw h},
                    {cases h,
                      {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
                       apply DC11.card_le_of_sup_DC  _ HCS HC , rw DC11.DC, rw h},
                      {cases h,
                        {apply DC12.card_le_of_sup_DC  _ HCS HC , rw DC12.DC, rw h},
                        {cases h,
                          {apply le_trans (DC13.card_le_of_sup_DC  _ HCS HC  _) (le_succ _),
                           rw DC13.DC, rw h},
                          {cases h,
                            {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
                             apply DC14.card_le_of_sup_DC  _ HCS HC , rw DC14.DC, rw h},
                            {cases h,
                              {apply DC15.card_le_of_sup_DC  _ HCS HC , rw DC15.DC, rw h},
                              {cases h,
                                {apply DC16.card_le_of_sup_DC  _ HCS HC , rw DC16.DC, rw h},
                                {cases h,
                                  {apply le_trans (DC17.card_le_of_sup_DC  _ HCS HC  _) (le_succ _),
                                   rw DC17.DC, rw h},
                                  {cases h,
                                    {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
                                     apply DC18.card_le_of_sup_DC  _ HCS HC , rw DC18.DC, rw h},
                                    {cases h,
                                      {apply le_trans (DC19.card_le_of_sup_DC  _ HCS HC  _) (le_succ _),
                                       rw DC19.DC, rw h},
                                      {cases h,
                                        {apply le_trans (DC20.card_le_of_sup_DC  _ HCS HC  _) (le_succ _),
                                         rw DC20.DC, rw h},
                                        {cases h,
                                          {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
                                           apply DC21.card_le_of_sup_DC  _ HCS HC , rw DC21.DC, rw h},
                                          {cases h,
                                            {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
                                             apply DC22.card_le_of_sup_DC  _ HCS HC , rw DC22.DC, rw h},
                                            {apply false.elim h}}}}}}}}}}}}}}}}}}}}}}
end

end card3

end Cwr_W23_2_2_wt2

namespace Cwr_W23_2_2_wt3

def Cwr_W23_2_2_wt3  : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, 
 ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma Cwr_W23_2_2_wt3_eq : Cwr_W23_2_2_wt3 = filter (λ x, wt x = 3) Cwr_W23_2_2 := rfl

def DCs_Cwr_W23_2_2_wt3_len5 : finset (finset (vector B 7)) := 
{{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}}

lemma DCs_Cwr_W23_2_2_wt3_len5_eq' : DCs_Cwr_W23_2_2_wt3_len5 = DCs_sub_len' Cwr_W23_2_2_wt3 5 := dec_trivial

lemma DCs_Cwr_W23_2_2_wt3_len5_eq : DCs_Cwr_W23_2_2_wt3_len5 = DCs_sub_len Cwr_W23_2_2_wt3 5 := 
by {rw ← DCs_sub_len'_eq, rw DCs_Cwr_W23_2_2_wt3_len5_eq'}

lemma DCs_Cwr_W23_2_2_wt3_len5_succ : 
  DCs_sub_DCs_len_succ Cwr_W23_2_2_wt3 DCs_Cwr_W23_2_2_wt3_len5 = ∅ := rfl

lemma DCs_Cwr_W23_2_2_wt3_len6 : DCs_sub_len Cwr_W23_2_2_wt3 6 = ∅ := 
begin
rw ← DCs_sub_DCs_len_succ_eq, rw ← DCs_Cwr_W23_2_2_wt3_len5_eq,
apply DCs_Cwr_W23_2_2_wt3_len5_succ
end

lemma card_DC_sub_Cwr_W23_2_2_wt3_le 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ Cwr_W23_2_2_wt3) : 
  card C ≤ 5 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_Cwr_W23_2_2_wt3_len6 _ HCS HC

lemma card_filter_wt3_le
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2) (HC : is_DelCode C) : 
  card (filter (λ x, wt x = 3) C) ≤ 5 := 
begin
apply card_DC_sub_Cwr_W23_2_2_wt3_le,
  {apply DelCode_filter _ HC},
  {rw Cwr_W23_2_2_wt3_eq, apply filter_subset_filter HCS}
end

def DCs_Cwr_W23_2_2_wt3_len5_list : list (finset (vector B 7)) :=
[{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}]

lemma DCs_Cwr_W23_2_2_wt3_len5_list_to_finset : 
  DCs_Cwr_W23_2_2_wt3_len5_list.to_finset = DCs_Cwr_W23_2_2_wt3_len5 := dec_trivial

lemma mem_DCs_Cwr_W23_2_2_wt3_len5_list (s : finset (vector B 7)) : 
  s ∈ DCs_Cwr_W23_2_2_wt3_len5_list ↔ s ∈ DCs_Cwr_W23_2_2_wt3_len5 :=
by {rw ← DCs_Cwr_W23_2_2_wt3_len5_list_to_finset, rw ← list.mem_to_finset}

namespace DC1

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, I, O, O, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le _ HCS HC H
end

end DC1

namespace DC2

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC2

namespace DC3

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC3

namespace DC4

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC4

namespace DC5

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC5

namespace DC6

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC6

namespace DC7

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC7

namespace DC8

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC8

namespace DC9

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC9

namespace DC10

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, O, O, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC10

namespace DC11

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC11

namespace DC12

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC12

namespace DC13

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC13

namespace DC14

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC14

namespace DC15

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC15

namespace DC16

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, O, I, O, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC16

namespace DC17

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC17

namespace DC18

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC18

namespace DC19

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, I, O, O, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC19

namespace DC20

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC20

namespace DC21

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, O, O, O, I, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC21

namespace DC22

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC22

namespace DC23

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC23

namespace DC24

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC24

namespace DC25

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC25

namespace DC26

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC26

namespace DC27

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC27

namespace DC28

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, O, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end
end DC28

namespace DC29

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC29

namespace DC30

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

lemma sdiff_dB_DC : Cwr_W23_2_2 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw ← H, apply filter_wt2_subset _ HCS HC
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card C ≤ 5 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC30

namespace DC31

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC31

namespace DC32

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC32

namespace DC33

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC33

namespace DC34

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, I], rfl⟩, ⟨[O, O, O, I, I, O, I], rfl⟩}

lemma card_DC : card DC = 5 := rfl

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = Cwr_W23_2_2 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC 
  (C : finset (vector B 7)) (HC : is_DelCode C) (HCS : C ⊆ sdiff_dB_DC) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC) : 
  card (filter (λ x, wt x = 2) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {apply DelCode_filter C HC},
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt2_subset _ HCS HC}
end

lemma card_le_of_sup_DC 
  (C : finset (vector B 7)) (HCS : C ⊆ Cwr_W23_2_2)
  (HC : is_DelCode C)  (H : filter (λ x, wt x = 3) C = DC)  : 
  card C ≤ 6 := 
begin
rw ← card_div_wt_of_sub_Cwr_W23_2_2 C HCS,
rw H, rw card_DC, repeat {apply succ_le_succ},
apply card_filter_wt2_le  _ HCS HC  H
end

end DC34

lemma card_le_of_filter_wt3 (C : finset (vector B 7)) 
  (HCS : C ⊆ Cwr_W23_2_2) (HC : is_DelCode C) 
  (H : card (filter (λ x, wt x = 3) C) = 5) : 
  card C ≤ 6 := 
begin
have h : filter (λ x, wt x = 3) C ∈ DCs_Cwr_W23_2_2_wt3_len5,
  {rw DCs_Cwr_W23_2_2_wt3_len5_eq, rw Cwr_W23_2_2_wt3_eq, 
   rw mem_DCs_sub_len, apply and.intro,
    {apply filter_subset_filter HCS},
    {apply and.intro H (DelCode_filter _ HC _)}},
rw ← mem_DCs_Cwr_W23_2_2_wt3_len5_list at h, 
rw DCs_Cwr_W23_2_2_wt3_len5_list at h, cases h,
  {apply DC1.card_le_of_sup_DC  _ HCS HC  _, rw DC1.DC, rw h},
  {cases h,
    {apply DC2.card_le_of_sup_DC  _ HCS HC , rw DC2.DC, rw h},
    {cases h,
      {apply le_trans (DC3.card_le_of_sup_DC  _ HCS HC  _) (le_succ _), 
       rw DC3.DC, rw h},
      {cases h,
        {apply le_trans (DC4.card_le_of_sup_DC  _ HCS HC  _) (le_succ _), 
         rw DC4.DC, rw h},
        {cases h, 
          {apply DC5.card_le_of_sup_DC  _ HCS HC , rw DC5.DC, rw h},
          {cases h, 
            {apply le_trans (DC6.card_le_of_sup_DC  _ HCS HC  _) (le_succ _), 
             rw DC6.DC, rw h},
            {cases h, 
              {apply le_trans (DC7.card_le_of_sup_DC  _ HCS HC  _) (le_succ _), 
               rw DC7.DC, rw h},
              {cases h,
                {apply le_trans (DC8.card_le_of_sup_DC  _ HCS HC  _) (le_succ _), 
                 rw DC8.DC, rw h},
                {cases h,
                  {apply DC9.card_le_of_sup_DC  _ HCS HC , rw DC9.DC, rw h},
                  {cases h,
                    {apply DC10.card_le_of_sup_DC  _ HCS HC , rw DC10.DC, rw h},
                    {cases h,
                      {apply DC11.card_le_of_sup_DC  _ HCS HC , rw DC11.DC, rw h},
                      {cases h,
                        {apply le_trans (DC12.card_le_of_sup_DC  _ HCS HC  _) (le_succ _),
                         rw DC12.DC, rw h},
                        {cases h,
                          {apply le_trans (DC13.card_le_of_sup_DC  _ HCS HC  _) (le_succ _),
                           rw DC13.DC, rw h},
                          {cases h,
                            {apply le_trans (DC14.card_le_of_sup_DC  _ HCS HC  _) (le_succ _),
                             rw DC14.DC, rw h},
                            {cases h,
                              {apply DC15.card_le_of_sup_DC  _ HCS HC , rw DC15.DC, rw h},
                              {cases h,
                                {apply DC16.card_le_of_sup_DC  _ HCS HC , rw DC16.DC, rw h},
                                {cases h,
                                  {apply DC17.card_le_of_sup_DC  _ HCS HC , rw DC17.DC, rw h},
                                  {cases h,
                                    {apply le_trans (DC18.card_le_of_sup_DC  _ HCS HC  _) (le_succ _),
                                     rw DC18.DC, rw h},
                                    {cases h,
                                      {apply DC19.card_le_of_sup_DC  _ HCS HC , rw DC19.DC, rw h},
                                      {cases h,
                                        {apply DC20.card_le_of_sup_DC  _ HCS HC , rw DC20.DC, rw h},
                                        {cases h,
                                          {apply DC21.card_le_of_sup_DC  _ HCS HC , rw DC21.DC, rw h},
                                          {cases h,
                                            {apply DC22.card_le_of_sup_DC  _ HCS HC , rw DC22.DC, rw h},
                                            {cases h,
                                              {apply le_trans (DC23.card_le_of_sup_DC  _ HCS HC  _) (le_succ _),
                                               rw DC23.DC, rw h},
                                              {cases h,
                                                {apply DC24.card_le_of_sup_DC  _ HCS HC , rw DC24.DC, rw h},
                                                {cases h,
                                                  {apply DC25.card_le_of_sup_DC  _ HCS HC , rw DC25.DC, rw h},
                                                  {cases h,
                                                    {apply le_trans (DC26.card_le_of_sup_DC  _ HCS HC  _) (le_succ _),
                                                     rw DC26.DC, rw h},
                                                    {cases h,
                                                      {apply le_trans (DC27.card_le_of_sup_DC  _ HCS HC  _) (le_succ _),
                                                       rw DC27.DC, rw h},
                                                      {cases h,
                                                        {apply DC28.card_le_of_sup_DC  _ HCS HC , rw DC28.DC, rw h},
                                                        {cases h,
                                                          {apply le_trans (DC29.card_le_of_sup_DC  _ HCS HC  _) (le_succ _),
                                                           rw DC29.DC, rw h},
                                                          {cases h,
                                                            {apply le_trans (DC30.card_le_of_sup_DC  _ HCS HC  _) (le_succ _),
                                                             rw DC30.DC, rw h},
                                                            {cases h,
                                                              {apply DC31.card_le_of_sup_DC  _ HCS HC , rw DC31.DC, rw h},
                                                              {cases h,
                                                                {apply DC32.card_le_of_sup_DC  _ HCS HC , rw DC32.DC, rw h},
                                                                {cases h,
                                                                  {apply DC33.card_le_of_sup_DC  _ HCS HC , rw DC33.DC, rw h},
                                                                  {cases h,
                                                                    {apply DC34.card_le_of_sup_DC  _ HCS HC , rw DC34.DC, rw h},
                                                                    {apply false.elim h}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}}
end

end Cwr_W23_2_2_wt3

lemma card_Cwr_2_2_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W23) (HC : is_DelCode C)  : 
  card (Cwr C 2 2) ≤ 6 :=
begin
have h : Cwr C 2 2 ⊆ Cwr_W23_2_2,
  {rw Cwr_W23_2_2_eq, apply filter_subset_filter HCS},
have h1 : card (filter (λ (x : vector B 7), wt x = 2) (Cwr C 2 2)) ≤ 4,
  {apply Cwr_W23_2_2_wt2.card_filter_wt2_le _ h (DelCode_Cwr _ HC _ _ )},
have h2 : card (filter (λ (x : vector B 7), wt x = 3) (Cwr C 2 2)) ≤ 5,
  {apply Cwr_W23_2_2_wt3.card_filter_wt3_le _ h (DelCode_Cwr _ HC _ _)},
cases eq_or_lt_of_le h1 with heq4 hlt4,
  {apply le_trans _ (le_succ _),
   apply Cwr_W23_2_2_wt2.card4.card_le_of_card4 _ h (DelCode_Cwr _ HC _ _) heq4},
  {rw lt_succ_iff at hlt4,  
   cases eq_or_lt_of_le hlt4 with heq3 hlt3,
    {apply Cwr_W23_2_2_wt2.card3.card_le_of_card3 _ h (DelCode_Cwr _ HC _ _) heq3},
    {cases eq_or_lt_of_le h2 with heq5 hlt5,
      {apply Cwr_W23_2_2_wt3.card_le_of_filter_wt3 _ h (DelCode_Cwr _ HC _ _) heq5},
      {rw lt_succ_iff at hlt3,  rw lt_succ_iff at hlt5,
       rw ← card_div_wt_of_sub_Cwr_W23_2_2 _ h,
       apply le_trans (add_le_add hlt3 hlt5) (refl _)}}}
end

lemma card_DCs_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : card (Cwr C 2 1) = 1) : 
  card C ≤ 7 :=
begin
cases decidable.em(card C ≤ 7) with hle hnle,
  {apply hle},
  {have h1 : 8 ≤ card C, from succ_le_of_lt (lt_of_not_ge hnle),
   have h2 : card (Cwr C 2 2) ≤ 6, from card_Cwr_2_2_le _ HCS HC ,
   have h2' : 7 ≤ card (Cwr C 2 2), from card_Cwr_2_2_ge _ HCS HC  h1 H,
   apply absurd h2, apply not_le_of_gt, apply lt_of_succ_le h2'}
end

end card1

def DCs_sub_W23_len8 :finset (finset (vector B 7)) :=
  card4.DCs_sup_DC_len8 ∪ card3.DCs_sup_DC_len8 ∪ card2.DCs_sup_DC_len8

lemma mem_DCs_sub_W23_len8 (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : 8 ≤ card C) : 
  C ∈ DCs_sub_W23_len8 :=
begin
have h1 : card (Cwr C 2 1) ≤ 4,
  {apply card_Cwr_2_1_le _ HCS HC },
have h2 : 1 ≤ card (Cwr C 2 1),
  {apply card_Cwr_2_1_ge_of_card _ HC HCS H},
rw DCs_sub_W23_len8, repeat {rw mem_union},
cases eq_or_lt_of_le h1 with heq4 hlt4,
  {left, left, apply card4.mem_DCs_sup_DC_len8 _ HCS HC H heq4},
  {rw lt_succ_iff at hlt4,  
   cases eq_or_lt_of_le hlt4 with heq3 hlt3,
    {left, right, apply card3.mem_DCs_sup_DC_len8 _ HCS HC H heq3},
    {rw lt_succ_iff at hlt3,  
     cases eq_or_lt_of_le hlt3 with heq2 hlt2,
      {right, apply card2.mem_DCs_sup_DC_len8 _ HCS HC H heq2},
      {rw lt_succ_iff at hlt2, 
       apply absurd H, apply not_le_of_gt, apply lt_succ_of_le,
       apply card1.card_DCs_le _ HCS HC  (le_antisymm hlt2 h2)}}}
end

end W23

def DCs_sub_W23_len8 : finset (finset (vector B 7)) :=
{{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}}

lemma DCs_sub_W23_len8_eq : DCs_sub_W23_len8 = W23.DCs_sub_W23_len8 := dec_trivial

def DCs_sub_W23_len8_list : list (finset (vector B 7)) :=
[{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}, 
 {⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}]

lemma DCs_sub_W23_len8_list_to_finset : 
  DCs_sub_W23_len8_list.to_finset = DCs_sub_W23_len8 := dec_trivial

lemma mem_DCs_sub_W23_len8_list (s : finset (vector B 7)) : 
  s ∈ DCs_sub_W23_len8_list ↔ s ∈ DCs_sub_W23_len8 :=
by {rw ← DCs_sub_W23_len8_list_to_finset, rw ← list.mem_to_finset}

lemma card_DCs_sub_W23_len8 
  (C : finset (vector B 7)) (H : C ∈ DCs_sub_W23_len8) : card C = 8 := 
begin
rw ← mem_DCs_sub_W23_len8_list at H, 
rw DCs_sub_W23_len8_list at H, cases H,
  {rw H, refl},
  {cases H,
    {rw H, refl},
    {cases H,
      {rw H, refl},
      {cases H,
        {rw H, refl},
        {cases H,
          {rw H, refl},
          {cases H,
            {rw H, refl},
            {cases H,
              {rw H, refl},
              {cases H,
                {rw H, refl},
                {cases H,
                  {rw H, refl},
                  {cases H,
                    {rw H, refl},
                    {cases H,
                      {rw H, refl},
                      {cases H,
                        {rw H, refl},
                        {cases H,
                          {rw H, refl},
                          {cases H,
                            {rw H, refl},
                            {cases H,
                              {rw H, refl},
                              {cases H,
                                {rw H, refl},
                                {cases H,
                                  {rw H, refl},
                                  {cases H,
                                    {rw H, refl},
                                    {apply false.elim H}}}}}}}}}}}}}}}}}}
end

lemma card_of_sub_W23_of_ge (C : finset (vector B 7)) 
  (HCS : C ⊆ W23) (HC : is_DelCode C) (H : 8 ≤ card C) : 
  card C = 8 :=
begin
apply card_DCs_sub_W23_len8, rw DCs_sub_W23_len8_eq,
apply W23.mem_DCs_sub_W23_len8 _ HCS HC H
end

lemma filter_wt_mem_DCs_sub_W23_len8 
  (C : finset (vector B 7)) (HCS : C ⊆ W25) (HC : is_DelCode C) 
  (H : 8 ≤ card (filter (Icc_wt 2 3) C)) : 
  filter (Icc_wt 2 3) C ∈ DCs_sub_W23_len8 :=
begin
rw DCs_sub_W23_len8_eq,
apply W23.mem_DCs_sub_W23_len8,
  {rw W23_eq, apply filter_subset_filter HCS},
  {apply DelCode_filter _ HC},
  {apply H}
end

lemma card_filter_wt_of_ge
  (C : finset (vector B 7)) (HCS : C ⊆ W25) (HC : is_DelCode C) 
  (H : 8 ≤ card (filter (Icc_wt 2 3) C)) : 
  card (filter (Icc_wt 2 3) C) = 8 :=
begin
rw card_of_sub_W23_of_ge,
  {rw W23_eq, apply filter_subset_filter HCS},
  {apply DelCode_filter _ HC},
  {apply H}
end

lemma div_filter_wt45 (C : finset (vector B 7)) : 
  filter (λ x, wt x = 4) C ∪ filter (λ x, wt x = 5) C = filter (Icc_wt 4 5) C := 
begin
rw ← filter_or, congr, ext, apply iff.intro,
  {intro h, cases h,
    {unfold Icc_wt, rw h, apply and.intro (le_refl _) (le_succ _)},
    {unfold Icc_wt, rw h, apply and.intro (le_succ _) (le_refl _)}},
  {intro h, unfold Icc_wt at h, 
   cases eq_or_lt_of_le h.right with heq5 hlt5,
    {right, apply heq5},
    {left, apply le_antisymm (le_of_lt_succ hlt5) h.left}} 
end

lemma card_div_filter_wt45 (C : finset (vector B 7)) : 
  card (filter (λ x, wt x = 4) C) + card (filter (λ x, wt x = 5) C) = card (filter (Icc_wt 4 5) C) := 
begin
rw ← div_filter_wt45,
rw card_union_of_disjoint, 
rw filter_wt_eq_inter_of_ne, 
apply nat.ne_of_lt, apply lt_succ_self
end

def W4 : finset (vector B 7) :=
{⟨[I, I, I, I, O, O, O], rfl⟩, ⟨[I, I, I, O, O, I, O], rfl⟩, ⟨[I, I, I, O, O, O, I], rfl⟩, ⟨[I, I, O, I, I, O, O], rfl⟩, ⟨[I, I, O, I, O, I, O], rfl⟩, ⟨[I, I, O, I, O, O, I], rfl⟩, ⟨[I, I, O, O, I, I, O], rfl⟩, ⟨[I, I, O, O, I, O, I], rfl⟩, ⟨[I, I, O, O, O, I, I], rfl⟩, ⟨[I, O, I, I, I, O, O], rfl⟩, 
 ⟨[I, O, I, I, O, I, O], rfl⟩, ⟨[I, O, I, I, O, O, I], rfl⟩, ⟨[I, O, I, O, I, I, O], rfl⟩, ⟨[I, O, I, O, I, O, I], rfl⟩, ⟨[I, O, I, O, O, I, I], rfl⟩, ⟨[I, O, O, I, I, I, O], rfl⟩, ⟨[I, O, O, I, I, O, I], rfl⟩, ⟨[I, O, O, I, O, I, I], rfl⟩, ⟨[I, O, O, O, I, I, I], rfl⟩, ⟨[O, I, I, I, I, O, O], rfl⟩, 
 ⟨[O, I, I, I, O, I, O], rfl⟩, ⟨[O, I, I, I, O, O, I], rfl⟩, ⟨[O, I, I, O, I, I, O], rfl⟩, ⟨[O, I, I, O, I, O, I], rfl⟩, ⟨[O, I, I, O, O, I, I], rfl⟩, ⟨[O, I, O, I, I, I, O], rfl⟩, ⟨[O, I, O, I, I, O, I], rfl⟩, ⟨[O, I, O, I, O, I, I], rfl⟩, ⟨[O, I, O, O, I, I, I], rfl⟩, ⟨[O, O, I, I, I, I, O], rfl⟩, 
 ⟨[O, O, I, I, I, O, I], rfl⟩, ⟨[O, O, I, I, O, I, I], rfl⟩, ⟨[O, O, O, I, I, I, I], rfl⟩}

lemma W4_eq : W4 = filter (λ x, wt x = 4) W25 := rfl

lemma filter_wt4_subset_sdiff
  (C : finset (vector B 7)) (HCS : C ⊆ W25) (HC : is_DelCode C) : 
  filter (λ x, wt x = 4) C ⊆ W4 \ union_dB (filter (Icc_wt 2 3) C) :=
begin
intros x hx, rw mem_sdiff, apply and.intro,
  {rw W4_eq, rw mem_filter, rw mem_filter at hx, 
   apply and.intro (HCS hx.left) hx.right},
  {apply not_mem_union_dB HC _ _ _ x hx,
    {apply @filter_subset},
    {apply @filter_subset},
    {rw filter_wt_eq_inter_Icc_of_gt, refl}}
end

namespace W4

namespace DC1

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma sdiff_dB_DC : W4 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ W4 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt4_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W25) (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC): 
  card (filter (λ x, wt x = 4) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw W4_eq, rw ← H, apply filter_wt4_subset_sdiff _ HCS HC 
end

end DC1

namespace DC2

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, I, I, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = W4 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt4_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W25)
  (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC) : 
  card (filter (λ x, wt x = 4) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt4_subset_sdiff _ HCS HC },
  {apply DelCode_filter C HC}
end

end DC2

namespace DC3

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, O, I, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[O, I, I, O, I, I, O], rfl⟩, ⟨[O, I, O, I, I, O, I], rfl⟩, ⟨[O, I, O, I, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = W4 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt4_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W25)
  (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC) : 
  card (filter (λ x, wt x = 4) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt4_subset_sdiff _ HCS HC },
  {apply DelCode_filter C HC}
end

end DC3

namespace DC4

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma sdiff_dB_DC : W4 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ W4 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt4_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W25) (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC): 
  card (filter (λ x, wt x = 4) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw W4_eq, rw ← H, apply filter_wt4_subset_sdiff _ HCS HC 
end

end DC4

namespace DC5

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma sdiff_dB_DC : W4 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ W4 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt4_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W25) (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC): 
  card (filter (λ x, wt x = 4) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw W4_eq, rw ← H, apply filter_wt4_subset_sdiff _ HCS HC 
end

end DC5

namespace DC6

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, O, I, I, I], rfl⟩, ⟨[O, O, O, I, I, I, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = W4 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt4_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W25)
  (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC) : 
  card (filter (λ x, wt x = 4) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt4_subset_sdiff _ HCS HC },
  {apply DelCode_filter C HC}
end

end DC6

namespace DC7

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, I, I], rfl⟩, ⟨[O, O, I, I, O, I, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = W4 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt4_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W25)
  (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC) : 
  card (filter (λ x, wt x = 4) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt4_subset_sdiff _ HCS HC },
  {apply DelCode_filter C HC}
end

end DC7

namespace DC8

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, O, O, I, O, I, I], rfl⟩, ⟨[O, I, I, I, I, O, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = W4 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_filter_wt4_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W25)
  (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC) : 
  card (filter (λ x, wt x = 4) C) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt4_subset_sdiff _ HCS HC },
  {apply DelCode_filter C HC}
end

end DC8

namespace DC9

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma sdiff_dB_DC : W4 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ W4 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt4_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W25) (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC): 
  card (filter (λ x, wt x = 4) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw W4_eq, rw ← H, apply filter_wt4_subset_sdiff _ HCS HC 
end

end DC9

namespace DC10

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, O, I, O], rfl⟩, ⟨[I, O, O, I, I, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, I, O, O], rfl⟩, ⟨[O, I, O, O, O, I, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩}

lemma sdiff_dB_DC : W4 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ W4 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt4_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W25) (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC): 
  card (filter (λ x, wt x = 4) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw W4_eq, rw ← H, apply filter_wt4_subset_sdiff _ HCS HC 
end

end DC10

namespace DC11

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, I, O, O, O, I], rfl⟩, ⟨[I, O, O, O, I, O, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, I, I, I, O], rfl⟩, ⟨[O, O, O, O, O, I, I], rfl⟩}

lemma sdiff_dB_DC : W4 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ W4 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt4_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W25) (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC): 
  card (filter (λ x, wt x = 4) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw W4_eq, rw ← H, apply filter_wt4_subset_sdiff _ HCS HC 
end

end DC11

namespace DC12

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, I, I, O, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, I, O, O, I], rfl⟩, ⟨[O, O, I, I, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = W4 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_filter_wt4_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W25)
  (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC) : 
  card (filter (λ x, wt x = 4) C) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt4_subset_sdiff _ HCS HC },
  {apply DelCode_filter C HC}
end

end DC12

namespace DC13

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, I, I, O, O], rfl⟩, ⟨[I, I, O, I, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = W4 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt4_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W25)
  (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC) : 
  card (filter (λ x, wt x = 4) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt4_subset_sdiff _ HCS HC },
  {apply DelCode_filter C HC}
end

end DC13

namespace DC14

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, I, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, I, O, I, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, O, I, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, I, I, O, O], rfl⟩, ⟨[O, O, I, I, O, I, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = W4 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_filter_wt4_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W25)
  (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC) : 
  card (filter (λ x, wt x = 4) C) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt4_subset_sdiff _ HCS HC },
  {apply DelCode_filter C HC}
end

end DC14

namespace DC15

def DC : finset (vector B 7) :=
{⟨[I, I, I, O, O, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, O, O, O, I], rfl⟩, ⟨[O, I, O, O, I, O, O], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, O, I, I, O, O], rfl⟩, ⟨[I, I, O, I, O, I, O], rfl⟩, ⟨[I, O, I, I, O, I, O], rfl⟩, ⟨[O, I, I, O, I, I, O], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = W4 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len3' : DCs_sub_len' sdiff_dB_DC 3 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len3 : DCs_sub_len sdiff_dB_DC 3 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len3'}

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 2 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len3 _ HCS HC

lemma card_filter_wt4_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W25)
  (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC) : 
  card (filter (λ x, wt x = 4) C) ≤ 2 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt4_subset_sdiff _ HCS HC },
  {apply DelCode_filter C HC}
end

end DC15

namespace DC16

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, I, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, O, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, O, I], rfl⟩, ⟨[O, O, I, I, O, O, I], rfl⟩, ⟨[O, O, I, O, I, I, O], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma sdiff_dB_DC : W4 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ W4 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt4_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W25) (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC): 
  card (filter (λ x, wt x = 4) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw W4_eq, rw ← H, apply filter_wt4_subset_sdiff _ HCS HC 
end

end DC16

namespace DC17

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, I, O], rfl⟩, ⟨[O, I, I, O, O, I, O], rfl⟩, ⟨[O, I, O, O, O, O, I], rfl⟩, ⟨[O, O, I, I, I, O, O], rfl⟩, ⟨[O, O, I, O, I, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

def sdiff_dB_DC : finset (vector B 7) :=
{⟨[I, I, I, I, O, O, O], rfl⟩, ⟨[I, I, I, O, O, O, I], rfl⟩}

lemma sdiff_dB_DC_eq : sdiff_dB_DC = W4 \ union_dB DC := rfl 

lemma DCs_sub_sdiff_dB_DC_len2' : DCs_sub_len' sdiff_dB_DC 2 = ∅ := dec_trivial

lemma DCs_sub_sdiff_dB_DC_len2 : DCs_sub_len sdiff_dB_DC 2 = ∅ := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_sdiff_dB_DC_len2'}

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ sdiff_dB_DC) (HC : is_DelCode C) : 
  card C ≤ 1 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_sdiff_dB_DC_len2 _ HCS HC

lemma card_filter_wt4_le 
  (C : finset (vector B 7)) (HCS : C ⊆ W25)
  (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC) : 
  card (filter (λ x, wt x = 4) C) ≤ 1 :=
begin
apply card_le_of_sub_sdiff_dB_DC,
  {rw sdiff_dB_DC_eq, rw ← H,
   apply filter_wt4_subset_sdiff _ HCS HC },
  {apply DelCode_filter C HC}
end

end DC17

namespace DC18

def DC : finset (vector B 7) :=
{⟨[I, I, O, O, O, O, O], rfl⟩, ⟨[I, O, I, O, I, O, O], rfl⟩, ⟨[I, O, O, O, I, O, I], rfl⟩, ⟨[O, I, I, I, O, O, O], rfl⟩, ⟨[O, I, O, O, I, I, O], rfl⟩, ⟨[O, O, I, I, O, I, O], rfl⟩, ⟨[O, O, I, O, O, O, I], rfl⟩, ⟨[O, O, O, O, I, I, I], rfl⟩}

lemma sdiff_dB_DC : W4 \ union_dB DC = ∅ := rfl 

lemma card_le_of_sub_sdiff_dB_DC
  (C : finset (vector B 7)) (HCS : C ⊆ W4 \ union_dB DC) : 
  card C ≤ 0 := 
begin
rw sdiff_dB_DC at HCS, 
rw subset_empty at HCS, rw HCS, rw card_empty
end

lemma card_filter_wt4_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W25) (HC : is_DelCode C) (H : filter (Icc_wt 2 3) C = DC): 
  card (filter (λ x, wt x = 4) C) ≤ 0 := 
begin
apply card_le_of_sub_sdiff_dB_DC,
rw W4_eq, rw ← H, apply filter_wt4_subset_sdiff _ HCS HC 
end

end DC18

lemma card_filter_wt4_le (C : finset (vector B 7)) 
  (HCS : C ⊆ W25) (HC : is_DelCode C) 
  (H : 8 ≤ card (filter (Icc_wt 2 3) C)) : 
  card (filter (λ x, wt x = 4) C) ≤ 2 := 
begin
have h : filter (Icc_wt 2 3) C ∈ DCs_sub_W23_len8,
  {apply filter_wt_mem_DCs_sub_W23_len8 _ HCS HC H},
rw ← mem_DCs_sub_W23_len8_list at h, 
rw DCs_sub_W23_len8_list at h, cases h,
  {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
   apply DC1.card_filter_wt4_le _ HCS HC _, rw DC1.DC, rw h},
  {cases h,
    {apply le_of_succ_le, apply succ_le_succ,
     apply DC2.card_filter_wt4_le _ HCS HC , rw DC2.DC, rw h},
    {cases h,
      {apply le_of_succ_le, apply succ_le_succ,
       apply DC3.card_filter_wt4_le _ HCS HC, rw DC3.DC, rw h},
      {cases h,
        {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
         apply DC4.card_filter_wt4_le _ HCS HC , rw DC4.DC, rw h},
        {cases h, 
          {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
           apply DC5.card_filter_wt4_le _ HCS HC , rw DC5.DC, rw h},
          {cases h, 
            {apply le_of_succ_le, apply succ_le_succ,
             apply DC6.card_filter_wt4_le _ HCS HC , rw DC6.DC, rw h},
            {cases h, 
              {apply le_of_succ_le, apply succ_le_succ,
               apply DC7.card_filter_wt4_le _ HCS HC , rw DC7.DC, rw h},
              {cases h,
                {apply DC8.card_filter_wt4_le _ HCS HC, rw DC8.DC, rw h},
                {cases h,
                  {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
                   apply DC9.card_filter_wt4_le _ HCS HC, rw DC9.DC, rw h},
                  {cases h,
                    {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
                     apply DC10.card_filter_wt4_le _ HCS HC, rw DC10.DC, rw h},
                    {cases h,
                      {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
                       apply DC11.card_filter_wt4_le _ HCS HC , rw DC11.DC, rw h},
                      {cases h,
                        {apply DC12.card_filter_wt4_le _ HCS HC , rw DC12.DC, rw h},
                        {cases h,
                          {apply le_of_succ_le, apply succ_le_succ,
                           apply DC13.card_filter_wt4_le _ HCS HC, rw DC13.DC, rw h},
                          {cases h,
                            {apply DC14.card_filter_wt4_le _ HCS HC , rw DC14.DC, rw h},
                            {cases h,
                              {apply DC15.card_filter_wt4_le _ HCS HC , rw DC15.DC, rw h},
                              {cases h,
                                {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
                                 apply DC16.card_filter_wt4_le _ HCS HC , rw DC16.DC, rw h},
                                {cases h,
                                  {apply le_of_succ_le, apply succ_le_succ,
                                   apply DC17.card_filter_wt4_le _ HCS HC, rw DC17.DC, rw h},
                                  {cases h,
                                    {apply le_of_succ_le, apply le_of_succ_le, repeat {apply succ_le_succ},
                                     apply DC18.card_filter_wt4_le _ HCS HC , rw DC18.DC, rw h},
                                    {apply false.elim h}}}}}}}}}}}}}}}}}}
end

end W4

def W5 : finset (vector B 7) :=
{⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, I, O, O, I], rfl⟩, ⟨[I, I, I, O, I, I, O], rfl⟩, ⟨[I, I, I, O, I, O, I], rfl⟩, ⟨[I, I, I, O, O, I, I], rfl⟩, ⟨[I, I, O, I, I, I, O], rfl⟩, ⟨[I, I, O, I, I, O, I], rfl⟩, ⟨[I, I, O, I, O, I, I], rfl⟩, ⟨[I, I, O, O, I, I, I], rfl⟩, ⟨[I, O, I, I, I, I, O], rfl⟩, 
 ⟨[I, O, I, I, I, O, I], rfl⟩, ⟨[I, O, I, I, O, I, I], rfl⟩, ⟨[I, O, I, O, I, I, I], rfl⟩, ⟨[I, O, O, I, I, I, I], rfl⟩, ⟨[O, I, I, I, I, I, O], rfl⟩, ⟨[O, I, I, I, I, O, I], rfl⟩, ⟨[O, I, I, I, O, I, I], rfl⟩, ⟨[O, I, I, O, I, I, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}

lemma W5_eq : W5 = filter (λ x, wt x = 5) W25 := rfl

def DCs_sub_W5_len4 : finset (finset (vector B 7)) := 
{{⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, I, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, I, O, I], rfl⟩, ⟨[I, O, I, O, I, I, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, I, O, I], rfl⟩, ⟨[I, O, O, I, I, I, I], rfl⟩, ⟨[O, I, I, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, O, I, I], rfl⟩, ⟨[I, I, O, I, I, O, I], rfl⟩, ⟨[I, O, O, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, O, I, I], rfl⟩, ⟨[I, I, O, I, I, O, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, O, I, I], rfl⟩, ⟨[I, O, I, I, I, O, I], rfl⟩, ⟨[O, I, I, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, O, I, I], rfl⟩, ⟨[I, O, I, I, I, O, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, O, I, I], rfl⟩, ⟨[I, O, I, O, I, I, I], rfl⟩, ⟨[O, I, I, I, I, O, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, O, I, I], rfl⟩, ⟨[I, O, I, O, I, I, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, O, I, I], rfl⟩, ⟨[I, O, O, I, I, I, I], rfl⟩, ⟨[O, I, I, I, I, O, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, I, O, O, I, I], rfl⟩, ⟨[I, O, O, I, I, I, I], rfl⟩, ⟨[O, I, I, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, I, I, O, I], rfl⟩, ⟨[I, O, O, I, I, I, I], rfl⟩, ⟨[O, I, I, I, O, I, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, I, I, O, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩},
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, I, O, I, I], rfl⟩, ⟨[I, O, O, I, I, I, I], rfl⟩, ⟨[O, I, I, I, I, O, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, O, I, I, I], rfl⟩, ⟨[I, O, I, I, I, O, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, O, I, I, I], rfl⟩, ⟨[I, O, I, I, O, I, I], rfl⟩, ⟨[O, I, I, I, I, O, I], rfl⟩}, 
 {⟨[I, I, I, I, I, O, O], rfl⟩, ⟨[I, I, O, O, I, I, I], rfl⟩, ⟨[I, O, I, I, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O, I], rfl⟩, ⟨[I, I, I, O, I, I, O], rfl⟩, ⟨[I, I, O, O, I, I, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O, I], rfl⟩, ⟨[I, I, I, O, I, I, O], rfl⟩, ⟨[I, O, I, O, I, I, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O, I], rfl⟩, ⟨[I, I, I, O, I, I, O], rfl⟩, ⟨[I, O, O, I, I, I, I], rfl⟩, ⟨[O, I, I, O, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, I, I, O], rfl⟩, ⟨[I, O, I, I, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, I, I, O], rfl⟩, ⟨[I, O, O, I, I, I, I], rfl⟩, ⟨[O, I, I, I, O, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, O, I, I], rfl⟩, ⟨[I, O, I, I, I, I, O], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, I, O, I, I], rfl⟩, ⟨[I, O, O, I, I, I, I], rfl⟩, ⟨[O, I, I, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, O, I, I, I], rfl⟩, ⟨[I, O, I, I, I, I, O], rfl⟩, ⟨[O, I, I, I, O, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, O, I, I, I], rfl⟩, ⟨[I, O, I, I, I, I, O], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, O, I, I, I], rfl⟩, ⟨[I, O, I, I, O, I, I], rfl⟩, ⟨[O, I, I, I, I, I, O], rfl⟩}, 
 {⟨[I, I, I, I, O, O, I], rfl⟩, ⟨[I, I, O, O, I, I, I], rfl⟩, ⟨[I, O, I, I, O, I, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, I, I, O], rfl⟩, ⟨[I, I, O, O, I, I, I], rfl⟩, ⟨[I, O, I, I, I, O, I], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, I, O, I], rfl⟩, ⟨[I, I, O, O, I, I, I], rfl⟩, ⟨[I, O, I, I, I, I, O], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, I, I], rfl⟩, ⟨[I, I, O, I, I, I, O], rfl⟩, ⟨[I, O, O, I, I, I, I], rfl⟩, ⟨[O, I, I, I, I, O, I], rfl⟩}, 
 {⟨[I, I, I, O, O, I, I], rfl⟩, ⟨[I, I, O, I, I, O, I], rfl⟩, ⟨[I, O, I, I, I, I, O], rfl⟩, ⟨[O, O, I, I, I, I, I], rfl⟩}, 
 {⟨[I, I, I, O, O, I, I], rfl⟩, ⟨[I, I, O, I, I, O, I], rfl⟩, ⟨[I, O, O, I, I, I, I], rfl⟩, ⟨[O, I, I, I, I, I, O], rfl⟩}}

lemma DCs_sub_W5_len4_eq' : 
  DCs_sub_W5_len4 = DCs_sub_len' W5 4 := dec_trivial

lemma DCs_sub_W5_len4_eq : 
  DCs_sub_W5_len4 = DCs_sub_len W5 4 := 
by {rw ← DCs_sub_len'_eq, rw DCs_sub_W5_len4_eq'}

lemma DCs_sub_W5_len4_succ : 
  DCs_sub_DCs_len_succ W5 DCs_sub_W5_len4 = ∅ := rfl

lemma DCs_sub_W5_len5 : DCs_sub_len W5 5 = ∅ := 
begin
rw ← DCs_sub_DCs_len_succ_eq, rw ← DCs_sub_W5_len4_eq,
apply DCs_sub_W5_len4_succ
end

lemma card_le_of_sub_W5
  (C : finset (vector B 7)) (HCS : C ⊆ W5) (HC : is_DelCode C) : 
  card C ≤ 4 := 
by apply card_DC_sub_le_of_succ_empty _ _ DCs_sub_W5_len5 _ HCS HC

lemma card_filter_wt5_le
  (C : finset (vector B 7)) (HCS : C ⊆ W25) (HC : is_DelCode C) : 
  card (filter (λ x, wt x = 5) C) ≤ 4 := 
begin
apply card_le_of_sub_W5,
  {rw W5_eq, apply filter_subset_filter HCS},
  {apply DelCode_filter _ HC}
end

lemma card_le_of_sub_W25 
  (C : finset (vector B 7)) (HCS : C ⊆ W25) (HC : is_DelCode C) : 
  card C ≤ 14 :=
begin
cases exists_DC_card_filter_wt_le _ HCS HC with C' hC', 
rw ← hC'.right.right.left,
rw ← card_div_wt_of_sub_W25 _ hC'.right.left,
cases decidable.em (8 ≤ card (filter (Icc_wt 2 3) C')) with hle hnle,
  {rw card_filter_wt_of_ge _ hC'.right.left hC'.left hle,
   rw add_comm, repeat {apply succ_le_succ},
   rw ← card_div_filter_wt45 C', apply le_trans,
    {apply add_le_add,
      {apply W4.card_filter_wt4_le _ hC'.right.left hC'.left hle},
      {apply card_filter_wt5_le _ hC'.right.left hC'.left}},
    {refl}},
  {rw not_le at hnle, rw lt_succ_iff at hnle,
   apply le_trans,
    {apply add_le_add hnle (le_trans hC'.right.right.right hnle)},
    {refl}}
end

lemma optimal_of_card
  (C : finset (vector B 7)) (HC : is_DelCode C) (H : card C = 16) :
  is_optimal C HC :=
begin
rw optimal_iff_W22_sdiff_Repl _ _ HC,
  {rw H, rw ← W25_eq, apply card_le_of_sub_W25},
  {apply le_succ_of_le, apply le_succ_of_le, apply le_succ_of_le, refl}
end

lemma card_VTCode_7_0 : card (VTCode 7 0) = 16 := rfl

lemma optimal_VTCode_7_0 : 
  is_optimal (VTCode 7 0) (DelCode_VTCode 7 0) := 
by {apply optimal_of_card, rw card_VTCode_7_0}

end length7

