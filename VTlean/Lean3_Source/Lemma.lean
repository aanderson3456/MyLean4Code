import data.list.basic data.vector data.finset

namespace nat 

open nat 

lemma ne_of_lt {a b : ℕ} (H : a < b): a ≠ b := 
by {assume h, apply le_lt_antisymm (le_of_eq h.symm) H}

lemma ne_of_gt {a b : ℕ} (H : b < a): a ≠ b := 
by {assume h, apply le_lt_antisymm (le_of_eq h) H}

lemma sub_sub_eq_add_sub {b c : ℕ} (H : c ≤ b) (a : ℕ) :
  a - (b - c) = a + c - b :=
begin
revert a c, induction b with b ihb,
  {intros a c H, rw eq_zero_of_le_zero H, simp},
  {intros a c H, cases c,
    {rw nat.sub_zero, rw nat_add_zero},
    {repeat {rw succ_sub_succ}, 
     apply ihb _ (le_of_succ_le_succ H)}}
end 

lemma add_eq_self_iff {n m : ℕ} : 
  n + m = n ↔ m = 0 :=
begin
cases m,
  {apply iff.intro,
    {intros, refl},
    {intros, rw add_zero}},
  {apply iff.intro,
    {intro h, apply absurd h, apply ne_of_gt, 
     apply lt_add_of_pos_right, apply zero_lt_succ},
    {intro h, apply absurd h, apply ne_of_gt, 
     apply zero_lt_succ}}
end

lemma add_left_eq_add_iff {a b c : ℕ} : 
  a + b = a + c ↔ b = c :=
begin
apply iff.intro,
  {revert b c, induction a with a iha,
    {intros b c h, repeat {rw zero_add at h}, apply h},
    {intros b c h, repeat {rw succ_add at h}, apply iha (succ_inj h)}},
  {intro h, rw h}
end

lemma add_right_eq_add_iff {a b c : ℕ} : 
  b + a = c + a ↔ b = c :=
begin
apply iff.intro,
  {revert b c, induction a with a iha,
    {intros b c h, repeat {rw zero_add at h}, apply h},
    {intros b c h, repeat {rw succ_add at h}, apply iha (succ_inj h)}},
  {intro h, rw h}
end

lemma sub_eq_self_iff {n m : ℕ} : 
  n - m = n ↔ n = 0 ∨ m = 0 :=
begin
cases n,
  {apply iff.intro,
    {intros, left, refl},
    {intros, rw nat.zero_sub}},
  {cases m,
    {apply iff.intro,
      {intros, right, refl},
      {intros, rw nat.sub_zero}},
    {apply iff.intro,
      {intro h, apply absurd h,
       apply ne_of_lt, apply nat.sub_lt_self,
        {apply zero_lt_succ},
        {apply zero_lt_succ}},
      {intro h, cases h, 
        {apply absurd h, apply ne_of_gt, apply zero_lt_succ},
        {apply absurd h, apply ne_of_gt, apply zero_lt_succ}}}}
end

lemma zero_of_sub_eq_of_le {n m k: ℕ} 
(Hn : 0 < n) (Hnm : n ≤ m) (Hnkm : n - k = m): 
  k = 0 :=
begin
cases k,
  {refl},
  {cases n,
    {apply absurd Hn, rw not_lt},
    {apply absurd Hnm, rw not_le,
     rw ← Hnkm, rw succ_sub_succ, apply lt_of_le_of_lt,
      {apply nat.sub_le_self},
      {apply lt_succ_self}}}
end

lemma eq_of_sub_eq_le {n m k: ℕ} (Hnm : n ≤ m) (Hnkm : n - k = m): 
  n = m :=
begin
cases k,
  {rw nat.sub_zero at Hnkm, apply Hnkm},
  {cases n,
    {rw nat.zero_sub at Hnkm, apply Hnkm},
    {apply absurd Hnm, rw not_le,
     rw ← Hnkm, rw succ_sub_succ, apply lt_of_le_of_lt,
      {apply nat.sub_le_self},
      {apply lt_succ_self}}}
end

lemma le_and_sub_eq_iff {n m k: ℕ} (Hn : 0 < n): 
  n ≤ m ∧ n - k = m ↔ k = 0 ∧ n = m :=
begin
apply iff.intro,
  {intro h, apply and.intro,
    {cases k,
      {refl},
      {apply absurd h.right,
       apply ne_of_lt, apply lt_of_lt_of_le,
        {apply nat.sub_lt_self Hn (zero_lt_succ k)},
        {apply h.left}}},
    {apply le_antisymm,
      {apply h.left},
      {rw ← h.right, apply nat.sub_le_self}}},
  {intro h, apply and.intro,
    {rw h.right},
    {rw h.left, rw nat.sub_zero, apply h.right}}
end

lemma add_right_div_le_of_le (a b₁ b₂ c : ℕ) (H : b₁ ≤ b₂): 
  (a + b₁) / c ≤ (a + b₂) / c :=
by {apply nat.div_le_div_right, apply add_le_add_left H}

end nat 

namespace list

open list

variables {α : Type} 

lemma eq_singleton (X : list α) (H : list.length X = 1):
  ∃ b : α, X = [b] :=
begin
cases X with x X', 
  {contradiction},
  {cases X' with x' X'',
    {apply exists.intro x, refl},
    {apply absurd H, unfold list.length,
     apply nat.ne_of_gt, apply nat.lt_succ_of_le, 
     apply nat.succ_le_succ, apply nat.zero_le}}
end

lemma eq_of_append_eq (X Y₁ Y₂ : list α) (HY : X ++ Y₁ = X ++ Y₂): 
  Y₁ = Y₂ :=
begin
induction X with x X' ihX,
  {repeat {rw nil_append at HY}, apply HY},
  {repeat {rw cons_append at HY}, apply ihX (tail_eq_of_cons_eq HY)}
end 

lemma append_eq_iff (X Y₁ Y₂ : list α) : 
  X ++ Y₁ = X ++ Y₂ ↔ Y₁ = Y₂ :=
begin
apply iff.intro,
  {apply eq_of_append_eq},
  {intro h, rw h}
end 

variables (r : α → α → Prop) [decidable_eq α]

def lex' : list α → list α → Prop
| [] _              := true
| (x :: X) []       := false
| (x :: X) (y :: Y) := (x = y ∧ lex' X Y) ∨ (x ≠ y ∧ r x y)

instance decidable_lex' [decidable_rel r] (X Y : list α): 
  decidable (lex' r X Y) :=
begin
revert Y, induction X with x X' IHX,
  {intro Y, unfold lex', apply_instance},
  {intro Y, cases Y with y Y',
    {unfold lex', apply_instance},
    {unfold lex',
     apply @or.decidable _ _ _ _,
      {apply @and.decidable _ _ _ _,
        {apply_instance},
        {apply IHX Y'}},
      {apply_instance}}}
end

instance decidable_rel_lex' [decidable_rel r] : 
  decidable_rel (lex' r) :=
by {intros X Y,  apply_instance}

lemma lex'_trans
  (r : α → α → Prop) [is_trans α r] [is_antisymm α r] 
  (X Y Z : list α) (H1 : lex' r X Y) (H2 : lex' r Y Z) : 
  lex' r X Z :=
begin
revert Y Z, induction X with x X' ihX,
  {intros Y Z h1 h2, trivial},
  {intros Y Z h1 h2, cases Y with y Y', 
    {apply false.elim h1},
    {cases Z with z Z',
      {apply false.elim h2},
      {cases h1,
        {cases h2, 
          {unfold lex', left, apply and.intro,
            {apply (eq.trans h1.left h2.left)},
            {apply ihX _ _ h1.right h2.right}},
          {unfold lex', right, apply and.intro,
            {rw h1.left, apply h2.left},
            {rw h1.left, apply h2.right}}},
        {cases h2, 
          {unfold lex', right, apply and.intro,
            {rw ← h2.left, apply h1.left},
            {rw ← h2.left, apply h1.right}},
          {unfold lex', right, apply and.intro,
            {assume h, 
             have h1' : x = y,
              {rw ← h at h2, apply antisymm h1.right h2.right},
             apply absurd h1' h1.left},
            {apply trans h1.right h2.right}}}}}}
end

instance is_trans_lex'
  (r : α → α → Prop) [is_trans α r] [is_antisymm α r] : 
  is_trans (list α) (lex' r) :=
by {apply is_trans.mk, apply lex'_trans}

lemma lex'_antisymm
  (r : α → α → Prop) [is_antisymm α r] 
  (X Y : list α) (H1 : lex' r X Y) (H2 : lex' r Y X) :
  X = Y :=
begin
revert Y, induction X with x X' ihX,
  {intros Y h1 h2, cases Y with y Y',
    {refl},
    {apply false.elim h2}},
  {intros Y h1 h2, cases Y with y Y',
    {apply false.elim h1},
    {cases h1,
      {cases h2,
        {rw h1.left, rw ihX _ h1.right h2.right},
        {apply absurd h1.left.symm h2.left}},
      {cases h2,
        {apply absurd h2.left.symm h1.left},
        {apply absurd (antisymm h1.right h2.right) h1.left}}}}
end

instance is_antisymm_lex'
  (r : α → α → Prop) [is_antisymm α r] : 
  is_antisymm (list α) (lex' r) :=
by {apply is_antisymm.mk, apply lex'_antisymm}

lemma lex'_total
  (r : α → α → Prop) [is_total α r] (X Y : list α) : 
  lex' r X Y ∨ lex' r Y X :=
begin
revert Y, induction X with x X' ihX,
  {intro Y, left, trivial},
  {intro Y, cases Y with y Y',
    {right, trivial},
    {cases decidable.em (x = y) with heq hneq, 
      {cases ihX Y' with hle hnle, 
        {left, unfold lex', left, apply and.intro heq hle},
        {right, unfold lex', left, apply and.intro heq.symm hnle}},
      {cases (is_total.total r x y) with hle hnle, 
        {left, unfold lex', right, apply and.intro hneq hle},
        {right, unfold lex', right, apply and.intro (ne.symm hneq) hnle}}}}
end

instance is_total_lex'
  (r : α → α → Prop) [is_total α r] : 
  is_total (list α) (lex' r) :=
by {apply is_total.mk, apply lex'_total}

end list


namespace vector

open vector 

variables {α : Type} 

lemma eq_singleton (X : vector α 1): ∃ x : α, X = ⟨[x], rfl⟩ :=
begin
cases X with X H_lenX, 
cases list.eq_singleton X H_lenX with x H_x,
apply exists.intro x, 
rw subtype.ext, rw ← to_list, rw to_list_mk, rw H_x
end

def vector.repr [has_repr α] {n : ℕ} (x : vector α n) : string :=
"⟨" ++ list.repr (to_list x) ++ ", rfl⟩"

instance [has_repr α] {n : ℕ} : 
  has_repr (vector α n) :=
⟨vector.repr⟩

end vector

namespace finset 

open finset

variables {α : Type} [decidable_eq α]
variables {β : Type} [decidable_eq β]

lemma insert_swap (s : finset α) (a b : α) : 
  insert a (insert b s) = insert b (insert a s) :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_insert at hx, cases hx,
    {rw mem_insert, right, rw mem_insert, left, apply hx},
    {rw mem_insert at hx, cases hx,
      {rw mem_insert, left, apply hx},
      {rw mem_insert, right, rw mem_insert, right, apply hx}}},
  {intros x hx, rw mem_insert at hx, cases hx,
    {rw mem_insert, right, rw mem_insert, left, apply hx},
    {rw mem_insert at hx, cases hx,
      {rw mem_insert, left, apply hx},
      {rw mem_insert, right, rw mem_insert, right, apply hx}}},
end 

lemma union_subset_union 
  {s₁ s₂ t₁ t₂ : finset α} (Hs : s₁ ⊆ s₂) (Ht : t₁ ⊆ t₂): 
  s₁ ∪ t₁ ⊆ s₂ ∪ t₂  :=
begin 
intros x hx, rw mem_union at hx, cases hx,
  {rw mem_union, left, apply Hs hx},
  {rw mem_union, right, apply Ht hx}
end

lemma union_right_of_subset
  {s t : finset α} (H : s ⊆ t) : 
  s ∪ t = t :=
begin 
apply subset.antisymm,
  {apply union_subset H (refl _)},
  {apply subset_union_right}
end

lemma union_left_of_subset
  {s t : finset α} (H : t ⊆ s) : 
  s ∪ t = s :=
begin 
apply subset.antisymm,
  {apply union_subset (refl _) H},
  {apply subset_union_left}
end

lemma inter_eq_empty {s₁ s₂ t₁ t₂ : finset α} 
  (Hs : s₁ ⊆ s₂) (Ht : t₁ ⊆ t₂) (Hst : s₂ ∩ t₂ = ∅): 
  s₁ ∩ t₁ = ∅ :=
begin 
apply subset.antisymm,
  {apply subset.trans,
    {apply inter_subset_inter Hs Ht},
    {rw Hst, refl}},
  {apply empty_subset}
end

lemma inter_eq_empty_left 
  {s t₁ t₂ : finset α} (Ht : t₁ ⊆ t₂) (Hst : s ∩ t₂ = ∅): 
  s ∩ t₁ = ∅ :=
by apply inter_eq_empty (subset.refl s) Ht Hst

lemma inter_eq_empty_right
  {s₁ s₂ t : finset α} (Hs : s₁ ⊆ s₂) (Hst : s₂ ∩ t = ∅): 
  s₁ ∩ t = ∅ :=
by apply inter_eq_empty Hs (subset.refl t) Hst

lemma subset_erase_iff (s t : finset α) (a : α): 
  s ⊆ erase t a ↔ s ⊆ t ∧ a ∉ s  :=
begin 
apply iff.intro,
  {intro h, apply and.intro,
    {intros x hx, 
     have h1 : x ∈ erase t a, from h hx,
     rw mem_erase at h1, apply h1.right},
    {assume hain, 
     have h1 : a ∈ erase t a, from h hain,
     rw mem_erase at h1, cases h1, contradiction}},
  {intros h x hsin, rw mem_erase, apply and.intro,
    {assume hxa, 
     have h1 : a ∈ s, 
      {rw ← hxa, apply hsin},
     apply absurd h1 h.right},
    {apply h.left hsin}}
end

lemma subset_erase_iff_insert (s t : finset α) (a : α): 
  erase s a ⊆ t ↔ s ⊆ insert a t :=
begin 
apply iff.intro,
  {intros h x hx, 
   cases decidable.em (x = a) with heq hneq,
    {rw mem_insert, left, apply heq},
    {rw mem_insert, right, apply h, 
     rw mem_erase, apply and.intro hneq hx}},
  {intros h x hx, rw mem_erase at hx,
   have h' : x ∈ insert a t, from h hx.right,
   rw mem_insert at h', cases h',
    {apply absurd h' hx.left},
    {apply h'}}
end

lemma subset_of_subset_insert (s t : finset α) (a : α) 
  (Hst : s ⊆ insert a t) (Ha : a ∉ s) : 
  s ⊆ t :=
begin 
intros x hx, 
have h : x ∈ insert a t, from Hst hx,
rw mem_insert at h, cases h,
  {rw h at hx, contradiction},
  {apply h}
end

lemma not_mem_filter
  (C : finset α) (p : α → Prop) [decidable_pred p] 
  (x : α) (Hx : x ∉ C) :
  x ∉ filter p C :=
by {assume h, rw mem_filter at h, apply absurd h.left Hx}

lemma filter_swap
  (C : finset α) (p : α → Prop) (q : α → Prop) [decidable_pred p] [decidable_pred q] :
  filter q (filter p C) = filter p (filter q C) :=
begin
rw finset.ext, intros s, apply iff.intro,
  {intro sin, rw mem_filter, rw mem_filter, 
   rw mem_filter at sin, rw mem_filter at sin, 
   apply and.intro,
    {apply and.intro sin.left.left sin.right},
    {apply sin.left.right}},
  {intro sin, rw mem_filter, rw mem_filter, 
   rw mem_filter at sin, rw mem_filter at sin, 
   apply and.intro,
    {apply and.intro sin.left.left sin.right},
    {apply sin.left.right}}
end

lemma filter_and_swap
  (C : finset α) (p : α → Prop) (q : α → Prop) [decidable_pred p] [decidable_pred q] :
  filter (λ x, p x ∧ q x) C = filter (λ x, q x ∧ p x) C :=
by {rw ← filter_filter, rw ← filter_filter, rw filter_swap}

lemma filter_subset_filter_of_pred
  (C : finset α) (p : α → Prop) (q : α → Prop) [decidable_pred p] [decidable_pred q] 
  (H : ∀ x ∈ C, p x → q x) :
  filter p C ⊆ filter q C :=
begin
intros s sin, rw mem_filter at sin, 
rw mem_filter, apply and.intro sin.left (H s sin.left sin.right)
end

lemma card_eq_filter_add_filter
  (C : finset α) (p : α → Prop) [decidable_pred p] :
  card C = card (filter p C) + card (filter (λ x, ¬ p x) C) :=
begin
rw ← card_union_add_card_inter,
rw filter_not, rw union_sdiff_of_subset,
  {rw inter_sdiff_self, rw card_empty, rw nat_add_zero},
  {apply filter_subset}
end

lemma card_filter
  (C : finset α) (p : α → Prop) [decidable_pred p] :
  card (filter p C) = card C - card (filter (λ x, ¬ p x) C) :=
by {rw card_eq_filter_add_filter C p, rw nat.add_sub_cancel}

lemma card_filter_not
  (C : finset α) (p : α → Prop) [decidable_pred p] :
  card (filter (λ x, ¬ p x) C) = card C - card (filter p C) :=
by {rw card_eq_filter_add_filter C p, rw nat.add_sub_cancel_left}

lemma card_filter_le
  (C : finset α) (p : α → Prop) [decidable_pred p] :
  card (filter p C) ≤  card C :=
by {apply card_le_of_subset, apply filter_subset}

lemma card_union_of_disjoint
  (C₁ C₂ : finset α) (H : C₁ ∩ C₂ = ∅ ):
  card (C₁ ∪ C₂) = card C₁ + card C₂ :=
by {rw ← card_union_add_card_inter, rw H, rw card_empty, rw nat.add_zero}

lemma filter_inter_filter (p : α → Prop) [decidable_pred p] 
  {s t : finset α} : filter p s ∩ filter p t = filter p (s ∩ t) :=
begin 
apply subset.antisymm,
  {intros x hx, rw mem_inter at hx, repeat {rw mem_filter at hx},
   rw mem_filter, apply and.intro,
    {rw mem_inter, apply and.intro hx.left.left hx.right.left},
    {apply hx.left.right}},
  {intros x hx, rw mem_filter at hx,
   rw mem_inter, apply and.intro,
    {rw mem_filter, apply and.intro,
      {apply (inter_subset_left s t) hx.left},
      {apply hx.right}},
    {rw mem_filter, apply and.intro,
      {apply (inter_subset_right s t) hx.left},
      {apply hx.right}}}
end

lemma filter_inter_disjoint 
  {s t : finset α} (H : s ∩ t = ∅)
  (p q: α → Prop) [decidable_pred p] [decidable_pred q] :
  filter p s ∩ filter q t = ∅ :=
begin 
apply subset.antisymm,
  {intros x hx, rw mem_inter at hx, repeat {rw mem_filter at hx},
   have h : x ∈ s ∩ t,  
    {rw mem_inter, apply and.intro hx.left.left hx.right.left},
   rw H at h, apply h},
  {apply empty_subset}
end

lemma sdiff_empty (s : finset α) : s \ ∅  = s :=
begin
apply subset.antisymm, 
  {intros x hx, rw mem_sdiff at hx, apply hx.left},
  {intros x hx, rw mem_sdiff, apply and.intro,
    {apply hx},
    {assume h, apply false.elim h}}
end

lemma sdiff_subset_self (s t : finset α) : s \ t ⊆ s :=
by {intros x hx, rw mem_sdiff at hx, apply hx.left}

lemma inter_of_left_subset {s t : finset α} (Hst : s ⊆ t) : s ∩ t = s :=
begin
apply subset.antisymm,
  {apply inter_subset_left},
  {rw ← inter_self s, apply inter_subset_inter,
    {rw inter_self, refl},
    {apply Hst}}
end

lemma inter_of_right_subset {s t : finset α} (Hts : t ⊆ s) : s ∩ t = t :=
by {rw inter_comm, apply inter_of_left_subset Hts}

lemma empty_sdiff (s : finset α) :
  ∅ \ s = ∅ :=
begin
apply subset.antisymm,
  {apply sdiff_subset_self},
  {apply empty_subset}
end

lemma sdiff_self (s : finset α) :
  s \ s = ∅ :=
begin
apply subset.antisymm,
  {intros x hx,
   rw mem_sdiff at hx, cases hx, contradiction},
  {apply empty_subset}
end

lemma union_sdiff_distrib (s₁ s₂ t : finset α) :
  (s₁ ∪ s₂) \ t  = (s₁ \ t) ∪ (s₂ \ t) :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_sdiff at hx, rw mem_union at hx,
   cases hx.left,
    {rw mem_union, left, rw mem_sdiff, apply and.intro h hx.right},
    {rw mem_union, right, rw mem_sdiff, apply and.intro h hx.right}},
  {intros x hx, rw mem_union at hx, cases hx, 
    {rw mem_sdiff at hx, rw mem_sdiff, apply and.intro,
      {rw mem_union, left, apply hx.left},
      {apply hx.right}},
    {rw mem_sdiff at hx, rw mem_sdiff, apply and.intro,
      {rw mem_union, right, apply hx.left},
      {apply hx.right}}}
end

lemma inter_sdiff_distrib (s₁ s₂ t : finset α) :
  (s₁ ∩ s₂) \ t = (s₁ \ t) ∩ (s₂ \ t) :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_sdiff at hx, rw mem_inter at hx,
   rw mem_inter, apply and.intro,
    {rw mem_sdiff, apply and.intro hx.left.left hx.right},
    {rw mem_sdiff, apply and.intro hx.left.right hx.right}},
  {intros x hx, rw mem_inter at hx, repeat {rw mem_sdiff at hx}, 
   rw mem_sdiff, apply and.intro,
      {rw mem_inter, apply and.intro hx.left.left hx.right.left},
      {apply hx.left.right}}
end

lemma sdiff_inter (s t : finset α) : 
  s \ (s ∩ t) = s \ t :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_sdiff at hx, 
   rw mem_sdiff, apply and.intro, 
    {apply hx.left},
    {assume h, 
     have hx' : x ∈ s ∩ t, 
      {rw mem_inter, apply and.intro hx.left h},  
     apply absurd hx' hx.right}},
  {apply sdiff_subset_sdiff (refl s) (inter_subset_right _ _)}
end 

lemma sdiff_sdiff (s t₁ t₂  : finset α) : 
  s \ t₁ \ t₂ = s \ (t₁ ∪ t₂) :=
begin
apply subset.antisymm,
  {intros x hx, repeat {rw mem_sdiff at hx},
   rw mem_sdiff, apply and.intro,
    {apply hx.left.left},
    {assume h, rw mem_union at h, cases h,
      {apply absurd h hx.left.right},
      {apply absurd h hx.right}}},
  {intros x hx, rw mem_sdiff at hx,
   rw mem_sdiff, apply and.intro,
    {rw mem_sdiff, apply and.intro,
      {apply hx.left},
      {assume h, 
       have hx' : x ∈ t₁ ∪ t₂, 
        {rw mem_union, apply or.inl h},
       apply absurd hx' hx.right}},
    {assume h, 
       have hx' : x ∈ t₁ ∪ t₂, 
        {rw mem_union, apply or.inr h},
       apply absurd hx' hx.right}}
end

lemma inter_union_sdiff (s t : finset α) : 
  (s ∩ t) ∪ (s \ t) = s :=
begin
apply subset.antisymm,
  {apply union_subset, 
    {apply inter_subset_left},
    {apply sdiff_subset_self}},
  {intros x hx, cases decidable.em(x ∈ t) with hxt hnxt,
    {rw mem_union, left, rw mem_inter, apply and.intro hx hxt},
    {rw mem_union, right, rw mem_sdiff, apply and.intro hx hnxt}}
end 

lemma inter_inter_sdiff (s t : finset α) : 
  (s ∩ t) ∩ (s \ t) = ∅ :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_inter at hx, cases hx with hx1 hx2, 
   rw mem_inter at hx1, rw mem_sdiff at hx2, apply absurd hx1.right hx2.right},
  {apply empty_subset}
end 

lemma sdiff_of_disjoint
  (s t : finset α) (H : s ∩ t = ∅) :
  s \ t = s :=
begin
rw ← inter_union_sdiff s t, 
rw H, rw empty_union, rw sdiff_sdiff, rw union_self
end

lemma subset_sdiff_of_disjoint
  (s₁ s₂ t : finset α) (Hs : s₁ ⊆ s₂) (Hst : s₁ ∩ t = ∅) :
  s₁ ⊆ s₂ \ t :=
begin
intros x hx, rw mem_sdiff, apply and.intro,
  {apply Hs hx},
  {assume h, 
   have Hst' : s₁ ∩ t ≠ ∅,
    {apply ne_empty_of_mem, rw mem_inter, apply and.intro hx h},
   contradiction}
end

lemma card_inter_add_sdiff (s t : finset α) : 
  card (s ∩ t) + card (s \ t)  = card s :=
by {rw ← card_union_add_card_inter, rw inter_union_sdiff, rw inter_inter_sdiff, refl}

lemma card_sdiff' (s t : finset α) : 
  card (s \ t) = card s - card (s ∩ t) :=
by {rw ←  card_inter_add_sdiff s t, rw add_comm, rw nat.add_sub_cancel}

lemma insert_sdiff_of_mem (s t : finset α) (a : α) (H : a ∈ t): 
  insert a s \ t = s \ t :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_sdiff at hx, rw mem_insert at hx,
   cases hx.left with hxa hxs,
    {rw hxa at hx, apply absurd H hx.right},
    {rw mem_sdiff, apply and.intro hxs hx.right}},
  {apply sdiff_subset_sdiff (subset_insert a s) (refl t)}
end 

lemma insert_sdiff_of_not_mem (s t : finset α) (a : α) (H : a ∉ t): 
  insert a s \ t = insert a (s \ t) :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_sdiff at hx, rw mem_insert at hx,
   cases hx.left with hxa hxs,
    {rw mem_insert, left, apply hxa},
    {rw mem_insert, right, rw mem_sdiff, apply and.intro hxs hx.right}},
  {intros x hx, rw mem_insert at hx, cases hx with hxa hxs,
    {rw mem_sdiff, apply and.intro,
      {rw mem_insert, left, apply hxa},
      {rw hxa, apply H}},
    {rw mem_sdiff at hxs, rw mem_sdiff, apply and.intro,
      {rw mem_insert, right, apply hxs.left},
      {apply hxs.right}}}
end 

lemma sdiff_insert (s t : finset α) (a : α) : 
  s \ insert a t = erase s a \ t :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_sdiff at hx, rw mem_insert at hx,
   rw mem_sdiff, apply and.intro,
    {rw mem_erase, apply and.intro,
      {assume h, apply absurd (or.inl h) hx.right},
      {apply hx.left}},
    {assume h, apply absurd (or.inr h) hx.right}},
  {intros x hx, rw mem_sdiff at hx, rw mem_erase at hx,
   rw mem_sdiff, apply and.intro,
    {apply hx.left.right},
    {assume h, rw mem_insert at h, cases h,
      {apply absurd h hx.left.left},
      {apply absurd h hx.right}}}
end 

lemma sdiff_insert' (s t : finset α) (a : α) : 
  s \ insert a t = erase (s \ t) a :=
begin
rw sdiff_insert, ext,
rw mem_sdiff, rw mem_erase,
rw mem_erase, rw mem_sdiff, rw and.assoc
end 

lemma disjoint_of_insert_disjoint {s t : finset α} {a : α} (H : insert a s ∩ t = ∅): 
  s ∩ t = ∅ :=
begin
apply subset.antisymm,
  {apply subset.trans,
    {apply inter_subset_inter_right (subset_insert a s)},
    {rw H, refl}},
  {apply empty_subset}
end 

lemma not_mem_of_insert_disjoint {s t : finset α} {a : α} (Hs : a ∉ s) (H : insert a s ∩ t = ∅): 
  a ∉ s ∪ t :=
begin
assume h, rw mem_union at h, cases h,
  {contradiction},
  {apply absurd H, apply ne_empty_of_mem, 
   rw mem_inter, apply and.intro (mem_insert_self a s) h}
end 

lemma exists_mem_of_card (s : finset α) (Hs : card s ≠ 0) : 
  ∃ x : α, x ∈ s :=
begin
have h : s ≠ ∅,
  {assume h, rw ← card_eq_zero at h, contradiction},
apply exists_mem_of_ne_empty h
end 

lemma exists_distinct (s : finset α) (Hs : 1 < card s) : 
  ∃ x y ∈ s, x ≠ y :=
begin
have h1 : 0 < card s, 
  {apply nat.lt_of_succ_lt Hs},
rw card_pos at h1, cases exists_mem_of_ne_empty h1 with x hx, 
have h2 : 0 < card (erase s x), 
  {rw card_erase_of_mem hx, rw nat.lt_pred_iff, apply Hs},
rw card_pos at h2, cases exists_mem_of_ne_empty h2 with y hy, 
apply exists.intro x, apply exists.intro y,
apply exists.intro hx, apply exists.intro (mem_of_mem_erase hy),
rw mem_erase at hy, apply hy.left.symm
end 

lemma exists_subset_card_le
  (S : finset α) (k : ℕ) (Hk : k ≤ card S) : 
  ∃ S' : finset α, S' ⊆ S ∧ card S' = k :=
begin
revert k, induction S using finset.induction with s S hs ih,
  {intros k Hk, apply exists.intro ∅, 
   apply and.intro (empty_subset _), 
   rw card_empty at Hk, rw nat.eq_zero_of_le_zero Hk, rw card_empty},
  {intros k Hk, cases k,
    {apply exists.intro ∅, 
     apply and.intro (empty_subset _), rw card_empty},
    {cases ih k _ with S' hS',
      {apply exists.intro (insert s S'), apply and.intro,
        {apply insert_subset_insert, apply hS'.left},
        {rw card_insert_of_not_mem, 
          {rw hS'.right},
          {assume h, apply absurd (hS'.left h) hs}}},
      {rw card_insert_of_not_mem hs at Hk, 
       apply nat.le_of_succ_le_succ Hk}}}
end

lemma mem_fold_union (S : finset α) (op : α → finset β) (x : β) :
  x ∈ fold (∪) ∅ op S ↔ ∃ y ∈ S, x ∈ op y :=
begin
induction S using finset.induction with s S hs ih,
  {apply iff.intro,
    {intro h, rw fold_empty at h, apply false.elim h},
    {intro h, cases h with y hy, cases hy with hy hxy, apply false.elim hy}},
  {apply iff.intro,
    {intro h, rw fold_insert hs at h, rw mem_union at h, cases h with hs hS,
      {apply exists.intro s, apply exists.intro (mem_insert_self s S), apply hs},
      {rw ih at hS, cases hS with y hy, cases hy with hy hxy,
       apply exists.intro y, apply exists.intro (mem_insert_of_mem hy), apply hxy}},
    {intro hx, cases hx with y hxy, cases hxy with hy hxy, rw mem_insert at hy,
     rw fold_insert hs, rw mem_union, cases hy,
      {left, rw ← hy, apply hxy},
      {right, rw ih, apply exists.intro y, apply exists.intro hy, apply hxy}}}
end

end finset 