/- Copyright Manabu Hagiwara 2022, 2026 -/
import data.fintype data.list.basic
import .Lemma

inductive B : Type
| O : B
| I : B

export B (O I)

namespace B

def repr : B → string
| O := "O"
| I := "I"

instance : has_repr B :=
⟨B.repr⟩

lemma O_ne_I (H : O = I) : false := 
by contradiction

instance dec_eq_B : decidable_eq B
| O O := is_true rfl
| O I := is_false O_ne_I
| I O := is_false (ne.symm O_ne_I)
| I I := is_true rfl

instance : inhabited B := 
inhabited.mk O

open fintype 

instance fin_B : fintype B := 
begin
have h : ∀ x : B, x ∈ [O,I], 
    {intro x, cases x, 
        {left, refl},
        {right, left, refl}},
apply fintype.of_list _ h
end

@[simp] lemma card_B : card B = 2 := rfl

def to_nat  : B → ℕ 
| O := 0
| I := 1

def flip : B → B 
| O := I
| I := O

lemma eq_of_flip_eq (x y : B) (H : flip x = flip y) :
  x = y :=
begin
cases x,
  {cases y,
    {refl},
    {unfold flip at H, contradiction}},
  {cases y,
    {unfold flip at H, contradiction},
    {refl}}
end

lemma flip_eq_flip_iff (x y : B) :
  flip x = flip y ↔ x = y :=
begin
apply iff.intro,
  {apply eq_of_flip_eq},
  {intro h, rw h}
end

lemma flip_flip (x : B) :
  flip (flip x) = x :=
begin
cases x,
    {trivial},
    {trivial}
end

lemma flip_eq_iff (x y : B) :
  flip x = y ↔ x = flip y :=
begin
apply iff.intro,
  {intro h, rw ← h, rw flip_flip},
  {intro h, rw h, rw flip_flip}
end

lemma flip_ne_self (x : B) : x ≠ flip x := 
by {cases x, repeat {unfold flip, trivial}}

lemma flip_of_ne {x x' : B} (Hne : x ≠ x') : flip x = x' := 
begin
cases x,
  {cases x',
    {contradiction},
    {refl}},
  {cases x',
    {refl},
    {contradiction}},
end

namespace list 

open list

variables (X Y : list B) (i : ℕ)

def to_nat  : list B → ℕ 
| [] := 0
| (x::X) := 2 * to_nat X + B.to_nat x

lemma to_nat_cons (x : B) (X : list B) : 
    to_nat X ≤ to_nat (x::X) :=
begin
unfold to_nat, apply le_trans,
  {apply nat.le_mul_of_pos_left, apply zero_lt_two},
  {apply nat.le_add_right}
end

lemma head_eq_of_to_nat_cons
    (x y : B) (X Y: list B) 
    (H :to_nat (x::X) = to_nat (y::Y)) :
    x = y :=
begin
cases x,
  {cases y,
    {refl},
    {apply absurd H, unfold to_nat, unfold B.to_nat,
     apply nat.two_mul_ne_two_mul_add_one}},
  {cases y,
    {apply absurd H, unfold to_nat, unfold B.to_nat,
     rw eq_comm, apply nat.two_mul_ne_two_mul_add_one},
    {refl}}
end

lemma tail_eq_of_to_nat_cons (x y : B) (X Y: list B) 
    (H :to_nat (x::X) = to_nat (y::Y)) :
     to_nat X = to_nat Y :=
begin
have h : x = y, from head_eq_of_to_nat_cons x y X Y H,
unfold to_nat at H, rw h at H, rw ← nat.mul_left_inj (zero_lt_two),
apply nat.add_right_cancel H
end

lemma head_zero_of_to_nat_zero (x : B) (X : list B)  
    (H : to_nat (x::X) = 0) :
    x = O :=
begin
cases x,
  {refl},
  {apply absurd H,
   unfold to_nat, unfold B.to_nat, apply ne_of_gt,
   apply nat.zero_lt_succ}
end

lemma tail_zero_of_to_nat_zero (x : B) (X : list B)  
    (H : to_nat (x::X) = 0) :
    to_nat X = 0 :=
begin
have h : x = O, from head_zero_of_to_nat_zero x X H,
unfold to_nat at H, rw h at H, unfold B.to_nat at H, rw add_zero at H, 
cases nat.eq_zero_of_mul_eq_zero H with h2 hX,
  {contradiction},
  {apply hX}
end

lemma to_nat_repeat_zero (n : ℕ) : 
    to_nat (repeat O n) = 0 :=
begin
induction n with k IHk,
  {unfold repeat, unfold to_nat},
  {unfold repeat, unfold to_nat, unfold B.to_nat, rw add_zero, rw IHk, rw mul_zero}
end

lemma eq_repeat_zero 
  (X : list B) (HX : to_nat X = 0) : 
  X = repeat O (length X) :=
begin
induction X with x X' IHX,
  {refl},
  {rw head_zero_of_to_nat_zero x X' HX,
   unfold length, rw repeat_succ, 
   congr, apply IHX (tail_zero_of_to_nat_zero x X' HX)}  
end

lemma to_nat_zero_iff (X : list B) : 
  to_nat X = 0 ↔ X = repeat O (length X) :=
begin
apply iff.intro,
  {intro h, apply eq_repeat_zero X h},
  {intro h, rw h, apply to_nat_repeat_zero}
end

lemma vector.to_nat_zero_iff (X : list B) (n : ℕ) (H : length X = n): 
  to_nat X = 0 ↔ X = repeat O n :=
by {rw to_nat_zero_iff, rw H}

lemma  eq_of_to_nat 
  (X Y : list B) (H1 : length X = length Y) (H2 : to_nat X = to_nat Y) :
  X = Y :=
begin
revert X, induction Y with y Y' IHY,
  {intros X H1 H2, rw ← length_eq_zero, apply H1},
  {intros X H1 H2, cases X with x X', 
    {apply absurd H1, apply ne_of_lt, apply nat.zero_lt_succ},
    {rw head_eq_of_to_nat_cons x y X' Y' H2, 
     congr, apply IHY, 
      {apply nat.succ_inj H1},
      {apply tail_eq_of_to_nat_cons x y X' Y' H2}}}
end

def flip : list B → list B 
| []     := []
| (x::X) := (B.flip x)::(flip X)

lemma flip_nil :
  flip ([] : list B) = [] :=
by trivial

lemma eq_of_flip_eq (H : flip X = flip Y):
  X = Y :=
begin
revert X, induction Y with y Y' IHY,
  {intros X H, cases X with x X',
    {refl},
    {unfold flip at H, apply absurd H, apply cons_ne_nil}},
  {intros X H, cases X with x X',
    {unfold flip at H, apply absurd H, apply ne.symm (cons_ne_nil _ _ )},
    {unfold flip at H, congr,
      {apply eq_of_flip_eq, apply head_eq_of_cons_eq H},
      {apply IHY, apply tail_eq_of_cons_eq H}}}
end

lemma flip_eq_flip_iff :
  flip X = flip Y ↔ X = Y :=
begin
apply iff.intro,
  {apply eq_of_flip_eq},
  {intro h, rw h}
end

lemma flip_flip :
  flip (flip X) = X :=
begin
induction X with x X' IHX,
    {trivial},
    {unfold flip, rw B.flip_flip, rw IHX}
end

lemma flip_eq_iff :
  flip X = Y ↔ X = flip Y :=
begin
apply iff.intro,
  {intro h, rw ← h, rw flip_flip},
  {intro h, rw h, rw flip_flip}
end

lemma length_flip :
  length (flip X) = length X :=
begin
induction X with x X' IHX,
  {unfold flip},
  {unfold flip, unfold list.length, rw IHX}
end

lemma flip_append :
  flip (X ++ Y) = flip X ++ flip Y :=
begin
induction X with x X' IHX,
  {rw nil_append, rw flip_nil, rw nil_append},
  {rw cons_append, unfold flip, rw cons_append, 
   rw cons_inj', apply IHX}
end

lemma flip_repO (k : ℕ) :
  flip (repeat O k) = repeat I k :=
begin
induction k with k IHk,
  {unfold repeat, rw flip_nil},
  {repeat {rw repeat_succ}, unfold flip, 
   unfold B.flip, rw IHk}
end

lemma flip_repI (k : ℕ) :
  flip (repeat I k) = repeat O k :=
begin
induction k with k IHk,
  {unfold repeat, rw flip_nil},
  {repeat {rw repeat_succ}, unfold flip, 
   unfold B.flip, rw IHk}
end

end list 

namespace vector

open vector 

variables {n : ℕ} (X Y : vector B n) (i : ℕ)

instance dec_eq_Bn : decidable_eq (vector B n) :=
by apply_instance

instance fin_Bnn : fintype (vector B n) := 
vector.fintype

@[simp] lemma card_vectorB (n : ℕ) : 
    card (vector B n) = 2 ^ n :=
by {rw card_vector, rw card_B}

def to_nat (X : vector B n) : ℕ :=
    list.to_nat X.1

lemma to_nat_repeat_zero (n : ℕ) : 
    to_nat (repeat O n) = 0 :=
by {unfold to_nat, apply list.to_nat_repeat_zero}

lemma eq_repeat_zero (X : vector B n) (H : to_nat X = 0) : 
  X = repeat O n :=
begin
rw subtype.ext, unfold vector.repeat, 
repeat {rw ← to_list}, rw to_list_mk,
rw list.eq_repeat_zero (to_list X),
  {rw to_list_length},
  {apply H}
end

lemma to_nat_zero_iff
    {n : ℕ} (X : vector B n) : 
    to_nat X = 0 ↔ X = repeat O n :=
begin
apply iff.intro,
    {apply eq_repeat_zero X},
    {intro h, rw h, apply to_nat_repeat_zero}
end

lemma  eq_of_to_nat {n : ℕ} (X Y : vector B n)
    (H : to_nat X = to_nat Y) :
     X = Y :=
begin
rw subtype.ext, apply list.eq_of_to_nat,
  {repeat {rw ← to_list}, repeat {rw to_list_length}},
  {apply H}
end

def le {n : ℕ} (X Y : vector B n) : Prop :=
  to_nat X ≤ to_nat Y

instance {n : ℕ} : decidable_rel (@le n) :=
by {intros X Y, unfold le, apply_instance}

instance {n : ℕ} : is_trans (vector B n) (le) :=
by {apply is_trans.mk, intros a b c h1 h2, apply le_trans h1 h2}

instance {n : ℕ} : is_antisymm (vector B n) (le) :=
begin
apply is_antisymm.mk, intros a b h1 h2,
apply eq_of_to_nat, apply le_antisymm h1 h2
end

instance {n : ℕ} : is_total (vector B n) (le) :=
by {apply is_total.mk, intros a b, apply le_total}

lemma length_flip_vec :
  list.length (list.flip (to_list X)) = n :=
by {rw list.length_flip, rw vector.to_list_length}

def flip : vector B n :=
  ⟨list.flip (to_list X), length_flip_vec X⟩ 

lemma flip_eq_flip_iff :
  flip X = flip Y ↔ X = Y :=
by {unfold flip, repeat {rw subtype.ext}, apply list.flip_eq_flip_iff}

lemma injective_flip :
  function.injective (@flip n) :=
by {unfold function.injective, intros x y, apply (iff.elim_left (flip_eq_flip_iff x y))}

lemma flip_flip :
  flip (flip X) = X :=
by {unfold flip, rw subtype.ext, apply list.flip_flip}

lemma flip_eq_iff :
  flip X = Y ↔ X = flip Y :=
begin
apply iff.intro,
  {intro h, rw ← h, rw flip_flip},
  {intro h, rw h, rw flip_flip}
end

lemma flip_repO (k : ℕ) :
  flip (repeat O k) = repeat I k :=
begin
unfold flip, rw subtype.ext, 
repeat {rw ← to_list, rw to_list_mk}, 
apply list.flip_repO 
end

lemma flip_repI (k : ℕ) :
  flip (repeat I k) = repeat O k :=
begin
unfold flip, rw subtype.ext, 
repeat {rw ← to_list, rw to_list_mk}, 
apply list.flip_repI
end

end vector

namespace finset 

variable {n : ℕ}

open finset B.vector 

def le {n : ℕ} (s₁ s₂ : finset (vector B n)) : Prop :=
  list.lex' (vector.le) (sort vector.le s₁) (sort vector.le s₂)

instance {n : ℕ} : decidable_rel (@le n) :=
by {intros X Y, unfold le, apply_instance}

instance {n : ℕ} : is_trans (finset (vector B n)) (le) :=
by {apply is_trans.mk, unfold le, intros X Y Z, apply list.lex'_trans}

instance {n : ℕ} : is_antisymm (finset (vector B n)) (le) :=
begin
apply is_antisymm.mk, unfold le, intros X Y h1 h2, 
have h : sort vector.le X = sort vector.le Y, 
  {apply list.lex'_antisymm _ _ _ h1 h2},
apply subset.antisymm,
  {intros x hx, rw ← mem_sort vector.le at hx, rw h at hx, 
   rw ← mem_sort vector.le, apply hx},
  {intros x hx, rw ← mem_sort vector.le at hx, rw ← h at hx, 
   rw ← mem_sort vector.le, apply hx}
end

instance {n : ℕ} : is_total (finset (vector B n)) (le) :=
by {apply is_total.mk, unfold le, intros X Y, apply list.lex'_total}

def flip (C : finset (vector B n)) := 
  image vector.flip C

lemma mem_flip (C : finset (vector B n)) (x : vector B n):
  x ∈ flip C ↔ ∃ y ∈ C, vector.flip y = x :=
by {unfold flip, rw mem_image}

lemma flip_mem (C : finset (vector B n)) (x : vector B n):
  vector.flip x ∈ C ↔ x ∈ flip C :=
begin
apply iff.intro,
  {intros h, rw mem_flip, 
   apply exists.intro (vector.flip x), apply exists.intro h,
   rw vector.flip_flip},
  {intros h, rw mem_flip at h,
   cases h with y hy, cases hy with hy hxy, 
   rw ← hxy, rw vector.flip_flip, apply hy}
end

lemma flip_empty :
  flip (∅ : finset (vector B n)) = ∅ :=
by {unfold flip, rw image_empty}

lemma flip_univ :
  flip (univ : finset (vector B n)) = univ :=
begin
apply subset.antisymm,
  {apply subset_univ},
  {intros x hx, rw mem_flip, 
   apply exists.intro (vector.flip x), apply exists.intro,
    {apply mem_univ},
    {rw vector.flip_flip}}
end

lemma flip_flip (C : finset (vector B n)) :
  flip (flip C) = C :=
begin
apply subset.antisymm,
  {intros X hX, rw mem_flip at hX, 
   cases hX with Y hX, cases hX with hY hYX, 
   rw mem_flip at hY, 
   cases hY with Z hZ, cases hZ with hZ hZY,
   rw ← hYX, rw ← hZY, rw vector.flip_flip, apply hZ},
  {intros X hX, rw mem_flip, 
   apply exists.intro (vector.flip X), apply exists.intro,
    {rw mem_flip, apply exists.intro X, apply exists.intro hX, refl},
    {rw vector.flip_flip}}
end

lemma flip_subset (C C' : finset (vector B n)) (H : C ⊆ C'):
  flip C ⊆ flip C' :=
begin
intros X HX, rw mem_flip at HX, cases HX with Y HX, cases HX with HYin HYX,
rw mem_flip, apply exists.intro Y, apply exists.intro (H HYin), apply HYX
end

lemma flip_union (C C' : finset (vector B n)):
  flip (C ∪ C') = flip C ∪ flip C' :=
begin
apply subset.antisymm,
  {intros X hX, rw mem_flip at hX, 
   cases hX with Y hX, cases hX with hY hX, 
   rw mem_union at hY, cases hY,
    {rw mem_union, left, rw mem_flip, 
     apply exists.intro Y, apply exists.intro hY, apply hX},
    {rw mem_union, right, rw mem_flip, 
     apply exists.intro Y, apply exists.intro hY, apply hX}},
  {intros X hX, rw mem_union at hX, cases hX,
    {rw mem_flip at hX, cases hX with Y hX, cases hX with hY hX, 
     rw mem_flip, apply exists.intro Y, apply exists.intro,
      {rw mem_union, left, apply hY},
      {apply hX}},
    {rw mem_flip at hX, cases hX with Y hX, cases hX with hY hX, 
     rw mem_flip, apply exists.intro Y, apply exists.intro,
      {rw mem_union, right, apply hY},
      {apply hX}}}
end

lemma flip_inter (C C' : finset (vector B n)):
  flip (C ∩ C') = flip C ∩ flip C' :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_flip at hx, 
   cases hx with y hx, cases hx with hy hyx, 
   rw mem_inter at hy, rw mem_inter, apply and.intro,
    {rw mem_flip, apply exists.intro y, apply exists.intro hy.left, apply hyx},
    {rw mem_flip, apply exists.intro y, apply exists.intro hy.right, apply hyx}},
  {intros x hx, rw mem_inter at hx, cases hx with hxl hxr,
   rw mem_flip at hxl, cases hxl with y₁ hxl, cases hxl with hyl hyxl,
   rw mem_flip at hxr, cases hxr with y₂ hxr, cases hxr with hyr hyxr,
   rw mem_flip, apply exists.intro y₁, apply exists.intro,
    {have h : y₁ = y₂, 
      {rw ← vector.flip_eq_flip_iff, rw hyxl, rw hyxr},
     rw mem_inter, apply and.intro,
      {apply hyl},
      {rw h, apply hyr}},
    {apply hyxl}}
end

lemma flip_insert (C : finset (vector B n)) (X : vector B n):
  flip (insert X C) = insert (vector.flip X) (flip C) :=
begin
apply subset.antisymm,
  {intros Y hY, rw mem_flip at hY, 
   cases hY with Z hZ, cases hZ with hZ hZY, 
   rw mem_insert at hZ, rw mem_insert, cases hZ, 
    {left, rw ← hZ, rw hZY},
    {right, rw mem_flip, 
     apply exists.intro Z, apply exists.intro hZ, apply hZY}},
  {intros Y hY, rw mem_insert at hY, rw mem_flip, cases hY, 
      {apply exists.intro X, apply exists.intro,
        {apply mem_insert_self},
        {rw hY}},
      {rw mem_flip at hY, cases hY with Z hZ, cases hZ with hZ hZY,
       apply exists.intro Z, apply exists.intro,
        {apply mem_insert_of_mem hZ},
        {rw hZY}}}
end

lemma flip_erase (C : finset (vector B n)) (X : vector B n):
  flip (erase C X) = erase (flip C) (vector.flip X) :=
begin
apply subset.antisymm,
  {intros X hX, rw mem_flip at hX, 
   cases hX with Y hX, cases hX with hY hX, rw mem_erase at hY,
   rw mem_erase, apply and.intro,
    {assume h, rw ← hX at h, rw vector.flip_eq_flip_iff at h, 
     apply absurd h hY.left},
    {rw mem_flip, apply exists.intro Y, apply exists.intro hY.right, apply hX}},
  {intros X hX, rw mem_erase at hX,
   cases hX with hXne hXmem, rw mem_flip at hXmem, 
   cases hXmem with y hy, cases hy with hy hyX, 
   rw mem_flip,  apply exists.intro y, apply exists.intro,
      {rw mem_erase, apply and.intro,
        {assume h, rw ← hyX at hXne, 
         rw ← vector.flip_eq_flip_iff at h, contradiction},
        {apply hy}},
      {apply hyX}}
end

lemma flip_sdiff (C₁ C₂ : finset (vector B n)) :
  flip (C₁ \ C₂) = flip C₁ \ flip C₂ :=
begin
apply subset.antisymm,
  {intros X hX, rw mem_flip at hX, 
   cases hX with Y hX, cases hX with hY hYX, rw mem_sdiff at hY,
   rw mem_sdiff, apply and.intro,
    {rw mem_flip, apply exists.intro Y, 
     apply exists.intro hY.left, apply hYX},
    {assume h, rw ← hYX at h, rw flip_mem at h,
     rw flip_flip at h, apply absurd h hY.right}},
  {intros X hX, rw mem_sdiff at hX,
   rw mem_flip at hX, cases hX.left with Y hX, cases hX with hY hYX, 
   rw mem_flip, apply exists.intro Y, apply exists.intro,
    {rw mem_sdiff, apply and.intro hY, assume h, 
     have h' : X ∈ flip C₂,
      {rw mem_flip, apply exists.intro Y, apply exists.intro h hYX},
     apply absurd h' hX.right},
    {apply hYX}}
end

lemma card_flip {n : ℕ} (C : finset (vector B n)) :
  card (flip C) = card C :=
by {unfold flip, rw card_image_of_injective, apply B.vector.injective_flip} 

end finset

end B
