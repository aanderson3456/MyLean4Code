import data.vector .Lemma .B

variables {α : Type} [decidable_eq α]

namespace list 

open list nat

variables (x y : α) (X Y : list α) (i j : ℕ) (a b : α) 

def sDel : list α → ℕ → list α 
| []           _       := []
| (x::[])      _       := []
| (x::x'::X')  0       := x'::X'
| (x::x'::X')  (i + 1) := x :: sDel (x'::X') i 

lemma sDel_nil : 
  sDel ([] : list α) i = [] := 
by trivial

lemma sDel_singleton : sDel [x] i = [] := 
by trivial

lemma sDel_zero : sDel (x::X) 0 = X := 
begin
cases X with x' X',
  {trivial},
  {trivial}
end

lemma sDel_cons (H : X ≠ []) :
   sDel (x::X) (i + 1) = x :: (sDel X i) := 
begin 
cases X with x'  X', 
  {contradiction},
  {trivial}
end

lemma length_sDel :
  length (sDel X i) = length X - 1 := 
begin
revert i, induction X with x X' IHX,
  {intro n, trivial},
  {intro n, cases X' with x' X'',
    {trivial},
    {cases n, 
      {unfold sDel, unfold length, rw nat.add_sub_cancel},
      {unfold sDel, rw length, rw IHX, unfold length, 
       rw nat.add_sub_cancel, rw nat.add_sub_cancel}}}
end

lemma sDel_of_ovrlen (H : length X - 1 ≤ i):
  sDel X i = sDel X (length X - 1) := 
begin
revert i, induction X with x X' IHX,
  {intros i H, repeat {rw sDel_nil}},
  {intros i H, cases X' with x' X'',
    {repeat {rw sDel_singleton}},
    {cases i,
      {unfold length at H, rw nat.add_sub_cancel at H,
       apply false.elim (not_succ_le_zero _ H)},
      {rw length, unfold sDel, rw IHX,
        {unfold length, rw nat.add_sub_cancel,
         rw nat.add_sub_cancel, unfold sDel},
        {apply le_of_succ_le_succ H}}}}
end

lemma exists_sDel_le :  
  ∃ j : ℕ, j ≤ length X - 1 ∧ sDel X i = sDel X j :=
begin
cases decidable.em(i ≤ length X - 1) with hle hnle,
  {apply exists.intro i, apply and.intro (hle) (eq.refl _)},
  {apply exists.intro (length X - 1), apply and.intro,
    {refl},
    {rw sDel_of_ovrlen,
     apply le_of_lt (lt_of_not_ge hnle)}}
end 

lemma sDel_append_of_lt (H : i + 1 ≤ length X) :
  sDel (X ++ Y) i = sDel X i ++ Y :=
begin
revert i, induction X with x X' IHX,
  {intros i H, apply false.elim (not_lt_zero i H)},
  {intros i H, cases X' with x' X'',
    {have hi : i = 0, 
      {apply eq_zero_of_le_zero, apply le_of_lt_succ H}, 
     rw hi, rw cons_append, repeat {rw sDel_zero}},
    {cases i,
      {rw cons_append, repeat {rw sDel_zero}},
      {repeat {rw cons_append}, unfold sDel, congr,
       rw ← cons_append, apply IHX i (lt_of_succ_lt_succ H)}}}
end

lemma sDel_append_of_ge (H : length X ≤ i) (HY : Y ≠ []):
  sDel (X ++ Y) i = X ++ sDel Y (i - length X) :=
begin
revert i, induction X with x X' IHX,
  {intros i H, rw nil_append, 
   rw nil_append, rw list.length, rw nat.sub_zero},
  {intros i H, cases X' with x' X'',
    {cases i, 
      {apply absurd H, apply not_le_of_gt, apply zero_lt_succ},
      {cases Y with y Y',
        {contradiction},
        {repeat {rw cons_append, rw nil_append}, unfold sDel, 
         repeat {rw list.length}, rw succ_sub_succ, rw nat.sub_zero}}},
    {cases i, 
      {apply absurd H, apply not_le_of_gt, apply zero_lt_succ},
      {cases Y with y Y',
        {contradiction},
        {repeat {rw cons_append}, unfold sDel, congr,  
         repeat {rw ← cons_append}, rw IHX i (lt_of_succ_lt_succ H),
         repeat {rw list.length}, rw succ_sub_succ}}}}
end

lemma sDel_repeat (k : ℕ) :  
  sDel (repeat a k) i = repeat a (k - 1) :=
begin
revert i, induction k with k IHn,
  {intro i, trivial},
  {intro i, unfold list.repeat, cases k, 
    {trivial},
    {rw nat.succ_sub_one, unfold list.repeat, cases i,
      {unfold sDel},
      {unfold sDel, congr, rw ← repeat_succ, apply IHn}}}
end 

lemma exists_sDel_sDel 
  (X : list α) (i j : ℕ) :
  ∃ i' j' : ℕ, sDel (sDel X i) j' = sDel (sDel X j) i' :=
begin
revert i j, induction X with x X' ihX,
  {intros i j, apply exists.intro 0, apply exists.intro 0, refl},
  {intros i j, cases X' with x' X'', 
    {apply exists.intro 0, apply exists.intro 0, refl},
    {cases X'' with x'' X''',
      {apply exists.intro 0, apply exists.intro 0, 
       have h1 : sDel (sDel [x, x'] i) 0 = [],
        {apply eq_nil_of_length_eq_zero, repeat {rw length_sDel}, refl},
       have h2 : sDel (sDel [x, x'] j) 0 = [],
        {apply eq_nil_of_length_eq_zero, repeat {rw length_sDel}, refl},
       rw h1, rw h2},
      {cases i, 
        {cases j,
          {apply exists.intro 0, apply exists.intro 0, refl},
          {apply exists.intro 0, apply exists.intro j, 
           rw sDel_zero, unfold sDel, rw sDel_zero}},
        {cases j,
          {apply exists.intro i, apply exists.intro 0,
           unfold sDel, rw sDel_zero},
          {cases ihX i j with i' hi', cases hi' with j' hij',
           apply exists.intro (i' + 1), apply exists.intro (j' + 1),
           unfold sDel, rw sDel_cons,
            {rw sDel_cons,
              {rw hij'},
              {cases j,
                {rw sDel, apply cons_ne_nil},
                {rw sDel, apply cons_ne_nil}}},
            {cases i,
              {rw sDel, apply cons_ne_nil},
              {rw sDel, apply cons_ne_nil}}}}}}}
end

def sIns : list α → ℕ → α → list α
| []       _       b := [b]
| (x :: X) 0       b := b :: x :: X
| (x :: X) (i + 1) b := x :: sIns X i b 

lemma sIns_nil :
 sIns ([] : list α) i b = [b] :=
by trivial

lemma sIns_zero : sIns X 0 b = b :: X := 
begin
cases X with x X, 
  {trivial}, 
  {trivial} 
end

lemma sIns_cons :
 sIns (x :: X) (i + 1) b = x :: sIns X i b := 
by trivial

lemma length_sIns :
  length (sIns X i b) = length X + 1 := 
begin
revert i, induction X with x X' IHX, 
  {intro i, refl},
  {intro i, cases i,
    {refl},
    {unfold sIns, unfold length, rw IHX i}}
end

lemma sIns_ne_nil :
  sIns X i b ≠ [] := 
begin
assume h,
have hl : length (sIns X i b) = 0, 
  {rw h, unfold length},
rw length_sIns at hl, apply absurd hl, 
apply nat.ne_of_gt (zero_lt_succ _)
end

lemma sIns_of_ovrlen (H : length X ≤ i):
  sIns X i b = X ++ [b] := 
begin
revert i, induction X with x X' IHX,
  {intros i H, trivial},
  {intros i H, cases i,
    {apply absurd H, simp},
    {unfold sIns, rw cons_append, congr, 
     apply IHX _ (le_of_succ_le_succ H)}}
end

lemma exists_sIns_le :  
  ∃ j : ℕ, j ≤ length X ∧ sIns X i b = sIns X j b :=
begin
cases decidable.em(i ≤ length X) with hlt hnlt,
  {apply exists.intro i, apply and.intro hlt (eq.refl _)},
  {apply exists.intro (length X), apply and.intro,
    {refl},
    {rw sIns_of_ovrlen, 
      {rw sIns_of_ovrlen, refl},
      {apply le_of_lt (lt_of_not_ge hnlt)}}}
end 

lemma exists_sIns_sIns_eq :
  ∃ i' j' : ℕ, sIns (sIns X i a) j' b = sIns (sIns X j b) i' a :=
begin
revert i j, induction X with x X' ihX,
  {intros i j, apply exists.intro 0, apply exists.intro 1, refl},
  {intros i j, cases i, 
    {cases j,
      {apply exists.intro 0, apply exists.intro 1, refl},
      {apply exists.intro 0, apply exists.intro (j + 2), refl}},
    {cases j,
      {apply exists.intro (i + 2), apply exists.intro 0, refl},
      {cases ihX i j with i' hi', cases hi' with j' hij',
       apply exists.intro (i' + 1), apply exists.intro (j' + 1), 
       unfold sIns, rw hij'}}}
end

lemma sIns_sDel_id (H : 1 ≤ length X)  :
  ∃ (b : α), sIns (sDel X i) i b = X :=
begin
revert i, induction X with x X' IHX,
  {intros i, apply false.elim (not_succ_le_zero _ H)},
  {intros i, cases X' with x' X'',
    {apply exists.intro x, rw sDel_singleton, unfold sIns},
    {cases i,
      {apply exists.intro x, unfold sDel, unfold sIns},
      {cases IHX (le_add_left 1 (length X'')) i with a ha,
       apply exists.intro a, unfold sDel, unfold sIns, rw ha}}}
end

lemma sDel_sIns_id (b : α) :
  sDel (sIns X i b) i = X :=
begin
revert i, induction X with x X' IHX,
  {intros i, trivial},
  {intros i, cases i,
    {trivial},
    {unfold sIns,
     rw sDel_cons,
      {rw IHX},
      {apply sIns_ne_nil}}}
end

lemma sIns_of_sDel (HX : 1 ≤ length X) (HXY : Y = sDel X i) :
  ∃ b : α, X = sIns Y i b :=
by {cases sIns_sDel_id _ _ HX with a, rw HXY, apply exists.intro a, rw h}

lemma sDel_of_sIns (HXY : Y = sIns X i b) :
  X = sDel Y i :=
by {rw HXY, rw sDel_sIns_id}

lemma exists_sIns_eq_of_sDel [inhabited α]
  (HXY : length X = length Y) (Hij : sDel X i = sDel Y j) :
  ∃ i' j' : ℕ, ∃ a b : α, sIns X i' a = sIns Y j' b :=
begin
cases decidable.em(1 ≤ length X) with hle hnle,
  {cases sIns_sDel_id _ i hle with a ha, 
   cases sIns_sDel_id _ j (le_trans hle (le_of_eq HXY)) with b hb,
   cases exists_sIns_sIns_eq (sDel X i) i j a b with i' hi', 
   cases hi' with j' hij', 
   apply exists.intro j', apply exists.intro i', 
   apply exists.intro b, apply exists.intro a,
   rw ← ha, rw hij', rw ← hb, rw Hij},
  {apply exists.intro 0, apply exists.intro 0, 
   apply exists.intro (default α), apply exists.intro (default α),
   rw @eq_nil_of_length_eq_zero α X _,
    {rw @eq_nil_of_length_eq_zero α Y,
     rw ← HXY, apply eq_zero_of_le_zero, apply le_of_lt_succ, apply lt_of_not_ge hnle},
    {apply eq_zero_of_le_zero, apply le_of_lt_succ, apply lt_of_not_ge hnle}}
end

lemma exists_sDel_eq_of_sIns
  (HXYij : sIns X i a = sIns Y j b) :
  ∃ i' j' : ℕ, sDel X i' = sDel Y j' :=
begin
rw ← sDel_sIns_id X i a, rw ← sDel_sIns_id Y j b, rw ← HXYij, 
cases exists_sDel_sDel (sIns X i a) i j with i' hi', cases hi' with j' hij', 
apply exists.intro j', apply exists.intro i', rw hij'
end

end  list 

namespace vector 

open vector nat

variables {n : ℕ} (x : α) (X : vector α n) (Y : vector α (n - 1)) (i j : ℕ) (a b : α) 

lemma list.length_sDel :
  list.length (list.sDel (to_list X) i) = n - 1 := 
by {rw list.length_sDel, rw to_list_length}

def sDel {n : ℕ} (X : vector α n) (i : ℕ) : vector α (n - 1) := 
  ⟨list.sDel (to_list X) i, list.length_sDel X i⟩ 

lemma sDel_nil : 
  sDel (@vector.nil α) i = vector.nil := 
by trivial

lemma sDel_zero :
  sDel (x::X) 0 = X := 
begin
unfold sDel, rw subtype.ext, 
repeat {rw ← to_list}, rw to_list_mk, 
rw to_list_cons, rw list.sDel_zero
end

lemma sDel_cons (X : vector α (n + 1)) :
   sDel (x::X) (i + 1) = x :: (sDel X i) := 
begin 
unfold sDel, rw subtype.ext,
rw ← to_list, rw to_list_mk, rw to_list_cons, 
rw ← to_list, rw to_list_cons, rw list.sDel_cons,
  {congr},
  {assume h, 
   have h1 : list.length (to_list X) = 0,
    {rw h, refl},
   apply absurd h1, apply nat.ne_of_gt,
   rw to_list_length, apply lt_succ_of_le, apply nat.zero_le}
end

lemma length_sDel :
  length (sDel X i) = n - 1 := 
by trivial

lemma sDel_of_ovrlen (H : n - 1 ≤ i) : 
  sDel X i = sDel X (n - 1) :=
begin
unfold sDel, rw subtype.ext, 
repeat {rw ← to_list, rw to_list_mk},
rw list.sDel_of_ovrlen,
  {rw to_list_length},
  {rw to_list_length, apply H}
end 

lemma exists_sDel_le :  
  ∃ j : ℕ, j ≤ n - 1 ∧ sDel X i = sDel X j :=
begin
cases list.exists_sDel_le (to_list X) i with j hj,
  {apply exists.intro j, apply and.intro,
    {rw to_list_length at hj, apply hj.left},
    {unfold sDel, rw subtype.ext, apply hj.right}}
end 

lemma sDel_repeat :  
  sDel (repeat a n) i = repeat a (n - 1) :=
by {rw subtype.ext, unfold sDel, apply list.sDel_repeat}

lemma list.length_sIns :
  list.length (list.sIns (to_list X) i b) = n + 1 := 
by {rw list.length_sIns, rw to_list_length}

def sIns {n : ℕ} (X : vector α n) (i : ℕ) (b : α) : vector α (n + 1) := 
  ⟨list.sIns (to_list X) i b,  list.length_sIns X i b⟩

lemma sIns_nil : 
  sIns nil i b = ⟨[b], rfl⟩  := 
by trivial

lemma sIns_zero :
  sIns X 0 b = b::X := 
begin
unfold sIns, rw subtype.ext,
repeat{rw ← to_list}, rw to_list_mk, 
rw to_list_cons, rw list.sIns_zero
end

lemma sIns_cons {n : ℕ} (x : α) (X : vector α n) (i : ℕ) (b : α) :
   sIns (x::X) (i + 1) b = x :: (sIns X i b) := 
begin 
unfold sIns, rw subtype.ext, 
rw ← to_list, rw to_list_mk, 
rw to_list_cons, rw ← to_list, rw list.sIns_cons,
rw to_list_cons, rw to_list_mk
end

lemma length_sIns (b : α) : 
  length (sIns X i b) = n + 1 := 
by trivial

lemma sIns_of_ovrlen (H : n ≤ i) : 
  sIns X i b = sIns X n b :=
begin
unfold sIns, rw subtype.ext, 
repeat {rw ← to_list, rw to_list_mk},
rw list.sIns_of_ovrlen,
  {rw list.sIns_of_ovrlen, rw to_list_length},
  {rw to_list_length, apply H}
end 

lemma exists_sIns_le : 
  ∃ j : ℕ, j ≤ n ∧ sIns X i b = sIns X j b :=
begin
cases list.exists_sIns_le (to_list X) i b with j hj,
  {apply exists.intro j, apply and.intro,
    {rw to_list_length at hj, apply hj.left},
    {unfold sIns, rw subtype.ext, apply hj.right}}
end 

lemma sIns_sDel_id {n : ℕ} (X : vector α (n + 1)) (i : ℕ) :
  ∃ (b : α), sIns (sDel X i) i b = X :=
begin
unfold sIns, unfold sDel, 
have h : ∃ (b : α), list.sIns (list.sDel (to_list X) i) i b = to_list X,
  {apply list.sIns_sDel_id, rw to_list_length, 
   apply succ_le_succ, apply nat.zero_le},
cases h with b hX, apply exists.intro b, rw subtype.ext, apply hX
end

lemma sDel_sIns_id :
  sDel (sIns X i b) i = X :=
by {unfold sDel, unfold sIns, rw subtype.ext, apply list.sDel_sIns_id}

lemma sIns_of_sDel 
  (X : vector α (n + 1)) (Y : vector α n) (HXY : Y = sDel X i) :
  ∃ b : α, X = sIns Y i b :=
begin
cases list.sIns_of_sDel (to_list X) (to_list Y) i _ _ with b hb,
  {apply exists.intro b, unfold sIns, rw subtype.ext, apply hb},
  {rw to_list_length, apply succ_le_succ (nat.zero_le n)},
  {rw subtype.ext at HXY, apply HXY}
end

lemma sDel_of_sIns 
  (X : vector α n) (Y : vector α (n + 1)) (HXY : Y = sIns X i b) :
  X = sDel Y i :=
begin
rw subtype.ext, apply list.sDel_of_sIns (to_list X) (to_list Y) i b,
rw subtype.ext at HXY, apply HXY
end

lemma exists_sIns_eq_of_sDel [inhabited α]
  (X Y : vector α n) (HXYij : sDel X i = sDel Y j) :
  ∃ i' j' : ℕ, ∃ a b : α, sIns X i' a = sIns Y j' b :=
begin
cases @list.exists_sIns_eq_of_sDel _ _ _ _ i j _inst_2 _ _ with i' hi',
  {cases hi' with j' hij', cases hij' with a hija, cases hija with b hijab, 
   apply exists.intro i', apply exists.intro j',
   apply exists.intro a, apply exists.intro b,
   unfold sIns, rw subtype.ext, apply hijab},
  {repeat {rw to_list_length}},
  {rw subtype.ext at HXYij, apply HXYij}
end

lemma exists_sDel_eq_of_sIns
  (X Y : vector α n) (HXYij : sIns X i a = sIns Y j b) :
  ∃ i' j' : ℕ, sDel X i' = sDel Y j' :=
begin
cases list.exists_sDel_eq_of_sIns _ _ i j a b _ with i' hi',
  {cases hi' with j' hij', 
   apply exists.intro i', apply exists.intro j',
   unfold sDel, rw subtype.ext, apply hij'},
  {rw subtype.ext at HXYij, apply HXYij}
end

def list.dS_le {n : ℕ} (X : vector α n) :  ℕ → list (vector α (n - 1))
| 0       := [sDel X 0]
| (k + 1) := (sDel X (k + 1)) :: list.dS_le k

lemma list.mem_dS_le (k : ℕ) :
  Y ∈ list.dS_le X k ↔ ∃ i : ℕ, i ≤ k ∧ Y = vector.sDel X i :=
begin
induction k with k ihk,
  {apply iff.intro,
    {intros hy, unfold list.dS_le at hy, cases hy,
      {apply exists.intro 0, apply and.intro (le_refl 0) hy},
      {apply false.elim hy}},
    {intros hy, cases hy with i hyi, cases hyi with hi hyx,
     rw eq_zero_of_le_zero hi at hyx,
     unfold list.dS_le, rw hyx, rw list.mem_cons_eq, left, refl}},
  {apply iff.intro,
    {intros hy, unfold list.dS_le  at hy, 
     rw list.mem_cons_eq at hy, cases hy,
      {apply exists.intro (k + 1), 
       apply and.intro (le_refl (k + 1)) hy},
      {rw ihk at hy, cases hy with i hyi, 
       apply exists.intro i, 
       apply and.intro (le_trans hyi.left (nat.le_succ k)) hyi.right}},
    {intros hy, cases hy with i hyi, 
     cases decidable.em (i = k + 1) with heq hneq,
      {unfold list.dS_le , rw list.mem_cons_eq, 
       left, rw hyi.right, rw heq},
      {unfold list.dS_le, rw list.mem_cons_eq, 
       right, rw ihk, apply exists.intro i, 
       apply and.intro (le_of_lt_succ (lt_of_le_of_ne hyi.left hneq)) hyi.right}}}
end

def list.dS {n : ℕ} (X : vector α n) : list (vector α (n - 1)) :=
  list.dS_le X (n - 1)

lemma list.mem_dS :
  Y ∈ list.dS X ↔ ∃ i : ℕ, i ≤ n - 1 ∧ Y = sDel X i :=
by {unfold list.dS, rw list.mem_dS_le} 

lemma list.mem_dS' :
  Y ∈ list.dS X ↔ ∃ i : ℕ, Y = sDel X i :=
begin
rw list.mem_dS, cases n,
  {have hx : X = vector.nil, from vector.eq_nil X,
   have hy : Y = vector.nil, from vector.eq_nil Y,
   apply iff.intro,
    {intros hxi, apply exists.intro 0, rw hy, rw hx, rw vector.sDel_nil},
    {intros hxi, apply exists.intro 0, apply and.intro,
      {apply le_refl},
      {rw hy, rw hx, rw vector.sDel_nil}}},
  {apply iff.intro,
    {intros h, cases h with i hi, 
 apply exists.intro i, apply hi.right},
    {intros h, cases h with i hi,
     cases decidable.em (i < succ n) with hlt hnlt,
      {apply exists.intro i, apply and.intro (le_of_lt_succ hlt) hi},
      {apply exists.intro n, apply and.intro,
        {refl},
        {rw vector.sDel_of_ovrlen at hi,
          {apply hi},
          {rw succ_sub_one, rw not_lt at hnlt,
           apply le_trans (le_succ n) hnlt}}}}}
end

lemma length_dS_le (X : vector α n) (k : ℕ) :
  list.length (list.dS_le X k) ≤ k + 1 :=
begin
revert n X, induction k with k ihk,
  {intros n X, trivial},
  {intros n X, unfold list.dS_le, 
   unfold list.length, apply succ_le_succ, apply ihk}
end

lemma length_dS (X : vector α n) (k : ℕ) :
  list.length (list.dS X) ≤ n - 1 + 1 :=
by {apply length_dS_le}

open finset 

def dS_le (x : vector α n) (k : ℕ) : finset (vector α (n - 1)) :=
  list.to_finset (list.dS_le x k)

lemma card_dS_le (x : vector α n) (k : ℕ) :
  card (dS_le x k) ≤ k + 1 :=
begin
revert n x, induction k with k ihk,
  {intros n x, trivial},
  {intros n x, unfold dS_le, unfold list.dS_le,
   rw list.to_finset_cons, apply le_trans,
    {apply card_insert_le},
    {apply nat.succ_le_succ, rw ← dS_le, apply ihk}}
end

def dS {n : ℕ} (X : vector α n) : finset (vector α (n - 1)) :=
  list.to_finset (list.dS X)

lemma mem_dS :
  Y ∈ dS X ↔ ∃ i : ℕ, Y = vector.sDel X i :=
by {unfold dS, rw list.mem_to_finset, rw list.mem_dS'} 

lemma sDel_zero_mem_dS :
  sDel X 0 ∈ dS X :=
by {rw mem_dS, apply exists.intro 0, refl}

lemma dS_ne :
  dS X ≠ ∅ :=
by apply ne_empty_of_mem (sDel_zero_mem_dS X)

lemma card_dS_pos :
  0 < card (dS X) :=
by {rw card_pos, apply dS_ne}

lemma dS_eq (x : vector α n) : 
  dS x = dS_le x (n - 1) :=
by trivial

lemma card_dS (x : vector α n) :
  card (dS x) ≤ n - 1 + 1 :=
begin
rw dS_eq, apply le_trans, 
  {apply card_dS_le},
  {refl}
end

def union_dS {n : ℕ} (C : finset (vector α n)) : finset (vector α (n - 1)) :=
  fold (∪) ∅ dS C

lemma union_dS_empty :
  union_dS (∅ : finset (vector α n)) = ∅ :=
by {unfold union_dS, apply fold_empty}

lemma union_dS_insert (C : finset (vector α n)) (Hx : X ∉ C):
  union_dS (insert X C) = dS X ∪ union_dS C :=
by {unfold union_dS, apply fold_insert Hx}

lemma mem_union_dS (C : finset (vector α n)) :
  Y ∈ union_dS C ↔ ∃ X ∈ C, Y ∈ dS X :=
by {unfold union_dS, apply mem_fold_union}

lemma card_union_dS_insert (C : finset (vector α n)) (H : X ∉ C):
  card (union_dS (insert X C)) = card (dS X) + card (union_dS C) - card (dS X ∩ union_dS C) :=
begin
rw union_dS_insert _ C H,
rw ← card_union_add_card_inter, rw nat.add_sub_cancel
end

lemma dS_subset_union_dS 
  (C : finset (vector α n)) (c : vector α n) (Hc : c ∈ C) :
  dS c ⊆ union_dS C :=
begin
intros x hx, rw mem_union_dS, 
apply exists.intro c, apply exists.intro Hc, apply hx
end

lemma union_dS_subset_of_subset
  (C₁ C₂ : finset (vector α n)) (H : C₁ ⊆ C₂) :
  union_dS C₁ ⊆ union_dS C₂  :=
begin
intros x hx, rw mem_union_dS at hx, 
cases hx with y hy, cases hy with hy hxy, 
rw mem_union_dS, 
apply exists.intro y, apply exists.intro (H hy), apply hxy
end

lemma union_dS_union
  (C₁ C₂ : finset (vector B n)) :
  union_dS (C₁ ∪ C₂) = union_dS C₁ ∪ union_dS C₂ :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_union_dS at hx, 
   cases hx with y hy, cases hy with hy hxy,
   rw mem_union at hy, cases hy,
    {rw mem_union, left, rw mem_union_dS, 
     apply exists.intro y, apply exists.intro hy, apply hxy},
    {rw mem_union, right, rw mem_union_dS, 
     apply exists.intro y, apply exists.intro hy, apply hxy}},
  {apply union_subset,
    {apply union_dS_subset_of_subset, apply subset_union_left},
    {apply union_dS_subset_of_subset, apply subset_union_right}}
end

lemma dS_inter_union_dS
  (C : finset (vector α n)) (HX : ∀ c ∈ C, dS X ∩ dS c = ∅) :
  dS X ∩ union_dS C = ∅ :=
begin
apply subset.antisymm,
  {intros z hz, rw mem_inter at hz, cases hz with hzx hzC,
   rw mem_union_dS at hzC, cases hzC with y hy, cases hy with hy hzy,  
   have h : z ∈ dS X ∩ dS y, 
    {rw mem_inter, apply and.intro hzx hzy},
   rw HX y hy at h, apply h},
  {apply empty_subset}
end

lemma forall_dS_inter_dS
  (C : finset (vector α n)) (HX : dS X ∩ union_dS C = ∅)  :
  ∀ c ∈ C, dS X ∩ dS c = ∅ :=
begin
intros c hc, apply subset.antisymm,
  {apply subset.trans,
    {apply inter_subset_inter_left, 
     apply dS_subset_union_dS _ _ hc},
    {rw HX, refl}},
  {apply empty_subset}
end

lemma forall_dS_inter_dS_iff (C : finset (vector α n)):
  (∀ c ∈ C, dS X ∩ dS c = ∅) ↔ dS X ∩ union_dS C = ∅ :=
begin
apply iff.intro,
  {apply dS_inter_union_dS},
  {apply forall_dS_inter_dS}
end

end vector 

namespace B

namespace list 

open list 

lemma sDel_flip (X : list B) (i : ℕ) :
  sDel (flip X) i = flip (sDel X i) :=
begin
revert i, induction X with x X' IHX,
  {intro i, unfold B.list.flip, rw list.sDel_nil, unfold B.list.flip},
  {intro i, cases X' with x' X'',
    {unfold B.list.flip, repeat {rw list.sDel_singleton}, unfold B.list.flip},
    {rw B.list.flip, cases i,
      {repeat {rw list.sDel_zero}},
      {rw list.sDel_cons,
        {unfold list.sDel, rw IHX, unfold B.list.flip},
        {unfold B.list.flip, apply list.cons_ne_nil}}}}
end

end list 

namespace vector 

open vector nat finset B.finset

variables {n : ℕ} (X : vector B n) (i : ℕ)

lemma sDel_flip (X : vector B n) (i : ℕ) :
  sDel (flip X) i = flip (sDel X i) :=
begin
unfold vector.sDel, unfold B.vector.flip, 
rw subtype.ext, apply list.sDel_flip
end

lemma dS_flip (x : vector B n) :
  dS (flip x) = B.finset.flip (dS x) :=
begin
apply subset.antisymm,
  {intros y hy, rw vector.mem_dS at hy, cases hy with i hyi, 
   rw sDel_flip at hyi, rw mem_flip, 
   apply exists.intro (sDel x i), apply exists.intro,
    {rw vector.mem_dS, apply exists.intro i, refl},
    {rw hyi}},
  {intros y hy, rw mem_flip at hy, 
   cases hy with z hz, cases hz with hz hzy, 
   rw vector.mem_dS at hz, cases hz with i hz, 
   rw vector.mem_dS, apply exists.intro i, 
   rw ← hzy, rw hz, rw sDel_flip}
end

def list.IS_le : vector B n → ℕ → list (vector B (n + 1))
| X 0       := [sIns X 0 O, sIns X 0 I]
| X (i + 1) := (sIns X (i + 1) O) :: (sIns X (i + 1) I) ::list.IS_le X i

lemma list.mem_IS_le (x : vector B n) (k : ℕ) (y : vector B (n + 1)) :
  y ∈ list.IS_le x k ↔ ∃ i : ℕ, ∃ b : B, i ≤ k ∧ y = vector.sIns x i b :=
begin
induction k with k ihk,
  {apply iff.intro,
    {intros hy, unfold list.IS_le at hy, cases hy,
      {apply exists.intro 0, apply exists.intro O,
       apply and.intro (le_refl 0) hy},
      {cases hy,
        {apply exists.intro 0, apply exists.intro I,
         apply and.intro (le_refl 0) hy},
        {apply false.elim hy}}},
    {intros hy, cases hy with i hyi, cases hyi with b hyib, 
     cases hyib with hi hyb, rw eq_zero_of_le_zero hi at hyb, cases b,
      {unfold list.IS_le, left, apply hyb},
      {unfold list.IS_le, right, left, apply hyb}}},
  {apply iff.intro,
    {intros hy, unfold list.IS_le at hy, 
     rw list.mem_cons_eq at hy, cases hy,
      {apply exists.intro (k + 1), apply exists.intro O,
       apply and.intro (le_refl (k + 1)) hy},
      {cases hy,
        {apply exists.intro (k + 1), apply exists.intro I,
         apply and.intro (le_refl (k + 1)) hy},
        {unfold has_mem.mem at ihk, rw ihk at hy, cases hy with i hyi, cases hyi with b hyib,  
         apply exists.intro i, apply exists.intro b, 
         apply and.intro (le_trans hyib.left (le_succ k)) hyib.right}}},
    {intros hy, cases hy with i hyi, cases hyi with b hyib, 
     cases decidable.em (i = k + 1) with heq hneq,
      {unfold list.IS_le, rw list.mem_cons_eq, 
       cases b,
        {left, rw hyib.right, rw heq},
        {right, rw list.mem_cons_eq, left, rw hyib.right, rw heq}},
      {unfold list.IS_le, rw list.mem_cons_eq, 
       right, rw list.mem_cons_eq, right, rw ihk, 
       apply exists.intro i, apply exists.intro b, 
       apply and.intro (le_of_lt_succ (lt_of_le_of_ne hyib.left hneq)) hyib.right}}}
end

def list.IS {n : ℕ} (X : vector B n) : list (vector B (n + 1)) :=
  list.IS_le X n

lemma list.mem_IS (x : vector B n) (y : vector B (n + 1)) :
  y ∈ list.IS x ↔ ∃ i : ℕ, ∃ b : B, i ≤ n ∧ y = sIns x i b :=
by {unfold list.IS, rw list.mem_IS_le} 

lemma list.mem_IS' (x : vector B n) (y : vector B (n + 1)) :
  y ∈ list.IS x ↔ ∃ i : ℕ, ∃ b : B, y = sIns x i b:=
begin
rw list.mem_IS, cases n,
  {apply iff.intro,
    {intros hy, cases hy with i hyi, cases hyi with b hyib, 
     apply exists.intro i, apply exists.intro b, apply hyib.right},
    {intros hy, cases hy with i hyi, cases hyi with b hyib, 
     rw vector.sIns_of_ovrlen x i b (nat.zero_le i)at hyib,
     apply exists.intro 0, apply exists.intro b, 
     apply and.intro (le_refl 0) hyib}},
  {apply iff.intro,
    {intros h, cases h with i hi, cases hi with b hib, 
     apply exists.intro i, apply exists.intro b, apply hib.right},
    {intros h, cases h with i hi, cases hi with b hib, 
     cases decidable.em (i < succ n) with hlt hnlt,
      {apply exists.intro i, apply exists.intro b,
       apply and.intro (le_of_lt hlt) hib},
      {apply exists.intro (succ n), apply exists.intro b,
       apply and.intro,
        {refl},
        {rw vector.sIns_of_ovrlen at hib,
          {apply hib},
          {rw not_lt at hnlt, apply hnlt}}}}}
end

open finset 

def IS_le (X : vector B n) (i : ℕ) : finset (vector B (n + 1)) :=
  list.to_finset (list.IS_le X i)

def IS {n : ℕ} (X : vector B n) : finset (vector B (n + 1)) :=
  list.to_finset (list.IS X)

lemma mem_IS (x : vector B n) (y : vector B (n + 1)) :
  y ∈ IS x ↔ ∃ i : ℕ, ∃ b : B, y = sIns x i b :=
by {unfold IS, rw list.mem_to_finset, rw list.mem_IS'} 

lemma IS_eq (x : vector B n) : 
  IS x = IS_le x n :=
by trivial

lemma sIns_zero_mem_IS (X : vector B n) :
  sIns X 0 O ∈ IS X :=
by {rw mem_IS, apply exists.intro 0, apply exists.intro O, refl}

lemma IS_ne (X : vector B n) :
  IS X ≠ ∅ :=
by apply ne_empty_of_mem (sIns_zero_mem_IS X)

lemma card_IS_ne (X : vector B n) :
  card (IS X) ≠ 0 :=
by apply card_ne_zero_of_mem (sIns_zero_mem_IS X)

lemma card_IS_pos (X : vector B n) :
  0 < card (IS X) :=
by {apply lt_of_le_of_ne (nat.zero_le (card (IS X))) (card_IS_ne X).symm }

lemma mem_IS_of_mem_dS 
  (X : vector B (n + 1)) (Y : vector B n) (HXY : Y ∈ dS X) :
  X ∈ IS Y :=
begin
rw @mem_dS B _ (n + 1) _ at HXY, cases HXY with i Hi,
rw mem_IS, apply exists.intro i, apply sIns_of_sDel _ _ _ Hi
end

lemma mem_dS_of_mem_IS 
  (X : vector B n) (Y : vector B (n + 1)) (HXY : Y ∈ IS X) :
  X ∈ dS Y :=
begin
rw mem_IS at HXY, cases HXY with i Hi, cases Hi with a Hia,
rw @mem_dS B _ (n + 1) _, apply exists.intro i, 
apply sDel_of_sIns _ _ _ _ Hia
end

lemma dS_inter_empty_of_IS_inter 
  {X Y : vector B n} (HXY : IS X ∩ IS Y = ∅) : 
  dS X ∩ dS Y = ∅ :=
begin
apply subset.antisymm,
  {intros z hz,
   rw mem_inter at hz, 
   rw mem_dS at hz, cases hz.left with i hi,
   rw mem_dS at hz, cases hz.right with j hj, 
   have h1 : ∃ i' j' : ℕ, ∃ a b : B, sIns X i' a = sIns Y j' b, 
    {apply exists_sIns_eq_of_sDel _ _ _ _ (eq.trans hi.symm hj)},
   cases h1 with i' hi', cases hi' with j' hij',   
   cases hij' with a hija, cases hija with b hijab,   
   have h2 : sIns X i' a ∈ IS(X) ∩ IS(Y),
      {rw mem_inter, apply and.intro,
        {rw mem_IS, apply exists.intro i', apply exists.intro a, refl},
        {rw hijab, rw mem_IS, apply exists.intro j', apply exists.intro b, refl}},
   apply absurd HXY, apply ne_empty_of_mem h2},
  {apply empty_subset}
end

lemma IS_inter_empty_of_dS_inter
  {X Y : vector B n} (HXY : dS X ∩ dS Y = ∅) : 
  IS X ∩ IS Y = ∅ :=
begin
apply subset.antisymm,
  {intros z hz,
   rw mem_inter at hz, 
   rw mem_IS at hz, cases hz.left with i hi, cases hi with a hia,
   rw mem_IS at hz, cases hz.right with j hj, cases hj with b hjb,
   have h1 : ∃ i' j' : ℕ, sDel X i' = sDel Y j', 
    {apply exists_sDel_eq_of_sIns _ _ _ _ _ _ (eq.trans hia.symm hjb)},
   cases h1 with i' hi', cases hi' with j' hij',   
   have h2 : sDel X i' ∈ dS(X) ∩ dS(Y),
      {rw mem_inter, apply and.intro,
        {rw mem_dS, apply exists.intro i', refl},
        {rw hij', rw mem_dS, apply exists.intro j', refl}},
   apply absurd HXY, apply ne_empty_of_mem h2},
  {apply empty_subset}
end

lemma IS_inter_empty_iff (X Y : vector B n) :
  IS X ∩ IS Y = ∅ ↔ dS X ∩ dS Y = ∅ :=
begin
apply iff.intro,
  {apply dS_inter_empty_of_IS_inter},
  {apply IS_inter_empty_of_dS_inter}
end

lemma IS_inter_ne_empty_iff (X Y : vector B n) :
  IS X ∩ IS Y ≠ ∅ ↔ dS X ∩ dS Y ≠ ∅ :=
begin
apply iff.intro,
  {intro h, assume h', rw ← IS_inter_empty_iff at h', contradiction},
  {intro h, assume h', rw IS_inter_empty_iff at h', contradiction}
end

end vector 

end B