import .B .InsDel

namespace list

open list nat

variables (x y : B) (X Y : list B) (i j : ℕ) (b : B) 

def num_Os : list B → ℕ
| []     := 0
| (O::X) := num_Os X + 1 
| (I::X) := num_Os X

def num_Is : list B → ℕ
| []     := 0
| (O::X) := num_Is X  
| (I::X) := num_Is X + 1

lemma num_Os_cons
    (x : B) (X : list B) :
    num_Os (x::X) = num_Os [x] + num_Os X :=
begin
cases x,
    {unfold num_Os, rw add_comm},
    {unfold num_Os, rw zero_add}
end

lemma num_Os_le_cons
    (x : B) (X : list B) :
    num_Os X ≤ num_Os (x::X) :=
begin
cases x,
    {unfold num_Os, apply le_succ},
    {trivial}
end

lemma num_Os_cons_le
    (x : B) (X : list B) :
    num_Os (x::X) ≤ num_Os X + 1 :=
begin
cases x,
    {trivial},
    {unfold num_Os, apply le_succ}
end

lemma num_Os_le_length 
    (X : list B) :
    num_Os X ≤ length X :=
begin
induction X with x X' IHX,
    {trivial},
    {cases x,
        {unfold num_Os, apply succ_le_succ IHX},
        {unfold num_Os, apply le_succ_of_le IHX}}
end

lemma num_Os_sDel_le
    (X : list B) (i : ℕ) :
    num_Os (sDel X i) ≤ num_Os X :=
begin
revert i, induction X with x X' IHX,
    {intro i, trivial},
    {intro i, cases X' with x' X'',
        {rw sDel_singleton, apply nat.zero_le},
        {cases i,
            {rw sDel_zero, apply num_Os_le_cons},
            {unfold sDel, cases x,
                {unfold num_Os, apply succ_le_succ, apply IHX},
                {unfold num_Os, apply IHX}}}}
end

lemma num_Os_sDel_le_length
    (X : list B) (i : ℕ) :
    num_Os (sDel X i) ≤ length X - 1 :=
begin
apply le_trans,
    {apply num_Os_le_length},
    {rw length_sDel}
end

lemma num_Os_sIns_zero
    (X : list B) (i : ℕ) :
    num_Os (sIns X i O) = num_Os X + 1 := 
begin
revert X, induction i with k IHi,
    {intro X, cases X with x X',
        {trivial},
        {trivial}},
    {intro X, cases X with x X',
        {trivial},
        {rw sIns, cases x,
            {unfold num_Os, rw (IHi X')},
            {unfold num_Os, rw (IHi X')}}}
end

lemma num_Os_sIns_one
    (X : list B) (i : ℕ) :
    num_Os (sIns X i I) = num_Os X := 
begin
revert X, induction i with k IHi,
    {intro X, cases X with x X',
        {trivial},
        {trivial}},
    {intro X, cases X with x X',
        {trivial},
        {rw sIns, cases x,
            {unfold num_Os, rw (IHi X')},
            {unfold num_Os, rw (IHi X')}}}
end

lemma num_Os_le_sIns 
    (X : list B) (i : ℕ) (a : B) :
    num_Os X ≤ num_Os (sIns X i a) :=
begin
cases a,
    {rw num_Os_sIns_zero, apply le_succ},
    {rw num_Os_sIns_one}
end

lemma num_Os_append (X Y : list B) :
    num_Os (X ++ Y) = num_Os X + num_Os Y :=
begin
induction X with x X' ihX,
    {rw nil_append, unfold num_Os, rw nat.zero_add},
    {rw cons_append, cases x,
        {unfold num_Os, rw ihX, rw add_right_comm},
        {unfold num_Os, rw ihX}}
end

lemma num_Os_repO (n : ℕ) :
    num_Os (repeat O n) = n :=
begin
induction n with n ihn, 
    {refl},
    {unfold repeat, unfold num_Os, rw ihn}
end

lemma num_Os_repI (n : ℕ) :
    num_Os (repeat I n) = 0 :=
begin
induction n with n ihn, 
    {refl},
    {unfold repeat, unfold num_Os, rw ihn}
end

lemma num_Is_cons :
    num_Is (x::X) = num_Is [x] + num_Is X :=
begin
cases x,
    {unfold num_Is, rw zero_add},
    {unfold num_Is, rw add_comm}
end

lemma num_Is_le_cons :
    num_Is X ≤ num_Is (x::X) :=
begin
cases x,
    {trivial},
    {unfold num_Is, apply le_succ}
end

lemma num_Is_cons_le :
    num_Is (x::X) ≤ num_Is X + 1 :=
begin
cases x,
    {unfold num_Is, apply le_succ},
    {trivial}
end

lemma num_Is_le_length 
    (X : list B):
    num_Is X ≤ length X :=
begin
induction X with x X' IHX,
    {trivial},
    {cases x,
        {unfold num_Is, apply le_succ_of_le IHX},
        {unfold num_Is, apply succ_le_succ IHX}}
end

lemma num_Is_sDel_le :
    num_Is (sDel X i) ≤ num_Is X :=
begin
revert X, induction i with k IHi,
    {intro X, cases X with x X',
        {trivial},
        {rw sDel_zero, apply num_Is_le_cons}},
    {intro X, cases X with x X',
        {trivial},
        {cases X' with x' X'',
            {rw sDel_singleton, apply nat.zero_le},
            {unfold sDel, cases x,
                {unfold num_Is, apply IHi},
                {unfold num_Is, apply succ_le_succ, apply IHi}}}}
end

lemma num_Is_sDel_le_length :
    num_Is (sDel X i) ≤ length X - 1 :=
begin
apply le_trans,
    {apply num_Is_le_length},
    {rw length_sDel}  
end

lemma num_Is_le_sDel :
    num_Is X - 1 ≤ num_Is (sDel X i) :=
begin
revert i, induction X with x X' IHX,
    {intro i, trivial},
    {intro i, cases X' with x' X'',
        {cases x,
            {trivial},
            {trivial}},
        {cases i,
            {cases x,
                {unfold num_Is, rw sDel_zero, apply nat.sub_le},
                {unfold num_Is, rw sDel_zero, rw nat.add_sub_cancel}},
            {unfold sDel, cases x,
                {unfold num_Is, apply IHX},
                {unfold num_Is, rw nat.add_sub_cancel,
                 cases num_Is (x' :: X''),
                    {apply nat.zero_le},
                    {apply succ_le_succ, apply IHX}}}}}
end

lemma num_Is_sIns_zero :
    num_Is (sIns X i O) = num_Is X := 
begin
revert X, induction i with k IHi,
    {intro X, cases X with x X',
        {trivial},
        {trivial}},
    {intro X, cases X with x X',
        {trivial},
        {rw sIns, cases x,
            {unfold num_Is, rw (IHi X')},
            {unfold num_Is, rw (IHi X')}}}
end

lemma num_Is_sIns_one :
    num_Is (sIns X i I) = num_Is X + 1 := 
begin
revert X, induction i with k IHi,
    {intro X, cases X with x X',
        {trivial},
        {trivial}},
    {intro X, cases X with x X',
        {trivial},
        {rw sIns, cases x,
            {unfold num_Is, rw (IHi X')},
            {unfold num_Is, rw (IHi X')}}}
end

lemma num_Is_le_sIns :
    num_Is X ≤ num_Is (sIns X i b) :=
begin
cases b,
    {rw num_Is_sIns_zero},
    {rw num_Is_sIns_one, apply le_succ}
end

lemma num_Is_append :
    num_Is (X ++ Y) = num_Is X + num_Is Y :=
begin
induction X with x X' ihX,
    {rw nil_append, unfold num_Is, rw nat.zero_add},
    {rw cons_append, cases x,
        {unfold num_Is, rw ihX},
        {unfold num_Is, rw ihX, rw add_right_comm}}
end

lemma num_Is_repO (n : ℕ) :
    num_Is (repeat O n) = 0 :=
begin
induction n with n ihn, 
    {refl},
    {unfold repeat, unfold num_Is, rw ihn}
end

lemma num_Is_repI (n : ℕ) :
    num_Is (repeat I n) = n :=
begin
induction n with n ihn, 
    {refl},
    {unfold repeat, unfold num_Is, rw ihn}
end

lemma eq_rep0_of_num_Is (H : num_Is X = 0) :  
  X = repeat O (length X) :=
begin
induction X with x X' IHX,
  {trivial},
  {unfold list.length, unfold list.repeat, cases x,
    {congr, unfold num_Is at H, apply IHX H},
    {contradiction}}
end 

lemma sDel_of_num_Is_0 (H : num_Is X = 0) :  
  sDel X i = repeat O (length X - 1) :=
by {rw eq_rep0_of_num_Is X H, rw list.sDel_repeat, rw length_repeat}

lemma sDel_of_num_Is_1 (H : num_Is X = 1) :  
  ∃ i : ℕ, sDel X i = repeat O (length X - 1) :=
begin
induction X with x X' IHX,
  {apply exists.intro 0, rw list.sDel_nil, refl},
  {cases X' with x' X'', 
    {apply exists.intro 0, refl},
    {cases x,
      {unfold num_Is at H, cases IHX H with i IHXi, 
       apply exists.intro (i + 1), unfold list.sDel, rw IHXi, 
       unfold list.length, repeat{rw nat.succ_sub_one}, refl},
      {apply exists.intro 0, unfold list.sDel, unfold num_Is at H,
       rw eq_rep0_of_num_Is _ (nat.succ_inj H), simp}}}
end 

lemma sDel_of_num_Is_le (H : num_Is X ≤ 1) :  
  ∃ i : ℕ, sDel X i = repeat O (length X - 1) :=
begin
cases eq_or_lt_of_le H, 
  {apply sDel_of_num_Is_1 _ h},
  {apply exists.intro 0, apply sDel_of_num_Is_0,
   apply nat.eq_zero_of_le_zero, apply nat.le_of_lt_succ h}
end 

lemma eq_rep1_of_num_Is (H : num_Is X = (length X)) :  
  X = repeat I (length X) :=
begin
induction X with x X' IHX,
  {trivial},
  {unfold list.length, unfold list.repeat, cases x,
    {unfold num_Is at H, apply absurd H, apply nat.ne_of_lt,
     apply nat.lt_succ_of_le, apply num_Is_le_length},
    {congr, unfold num_Is at H, apply IHX (nat.succ_inj H)}}
end 

lemma sDel_of_num_Is_n (H : num_Is X = length X) :  
  sDel X i = repeat I (length X - 1) :=
by {rw eq_rep1_of_num_Is X H, rw list.sDel_repeat, rw length_repeat}

lemma sDel_of_num_Is_n_sub (X : list B) (H : num_Is X = (length X) - 1) :  
  ∃ i : ℕ, sDel X i = repeat I (length X - 1) :=
begin
induction X with x X' IHX,
  {apply exists.intro 0, trivial},
  {cases X' with x' X'', 
    {apply exists.intro 0, trivial},
    {cases x,
      {apply exists.intro 0, unfold list.sDel, unfold num_Is at H,
       rw eq_rep1_of_num_Is _ H, simp},
      {cases IHX (nat.succ_inj H) with i IHXi, 
        {apply exists.intro (i + 1),
         unfold list.sDel, rw IHXi, unfold list.length, 
         repeat{rw nat.succ_sub_one}, unfold list.repeat}}}}
end 

lemma sDel_of_le_num_Is (X : list B) (H : length X - 1 ≤ num_Is X) :  
  ∃ i : ℕ, sDel X i = repeat I (length X - 1) :=
begin
cases eq_or_lt_of_le H,
  {apply sDel_of_num_Is_n_sub X h.symm},
  {apply exists.intro 0,
   have h : num_Is X = length X, 
    {apply le_antisymm, 
      {apply num_Is_le_length},
      {apply nat.le_of_pred_lt, apply h}},
   apply sDel_of_num_Is_n X 0 h}
end 

lemma num_Os_add_num_Is (X : list B) :  
  num_Os X + num_Is X = length X :=
begin
induction X with x X' ihX,
  {trivial},
  {cases x,
    {unfold num_Os, unfold num_Is, unfold length,
     rw add_right_comm, rw succ_inj', apply ihX},
    {unfold num_Os, unfold num_Is, unfold length,
     rw ← add_assoc, rw succ_inj', apply ihX}}
end 

lemma num_Os_eq_len_sub (X : list B) :  
  num_Os X = length X - num_Is X :=
by {rw ← num_Os_add_num_Is, rw nat.add_sub_cancel}

lemma num_Is_eq_len_sub (X : list B) :  
  num_Is X = length X - num_Os X :=
by {rw ← num_Os_add_num_Is, rw add_comm, rw nat.add_sub_cancel}

lemma num_Is_flip_eq_num_Os (X : list B) :  
  num_Is (B.list.flip X) = num_Os X :=
begin
induction X with x X' IHX,
  {trivial},
  {cases x,
    {unfold B.list.flip, unfold B.flip, 
     unfold num_Is, unfold num_Os, rw IHX},
    {unfold B.list.flip, unfold B.flip, 
     unfold num_Is, unfold num_Os, rw IHX}}
end 

lemma num_Is_flip (X : list B) :  
    num_Is (B.list.flip X) = length X - num_Is X :=
by {rw num_Is_flip_eq_num_Os, rw num_Os_eq_len_sub} 


def num_LOs : list B → ℕ → ℕ 
| []     _       := 0
| (x::X) 0       := 0
| (O::X) (n + 1) := num_LOs X n + 1
| (I::X) (n + 1) := num_LOs X n

lemma num_LOs_zero :
    num_LOs X 0 = 0 :=
begin
cases X with x X',
    {trivial},
    {cases x,
        {trivial},
        {trivial}}
end

lemma num_LOs_le :
    num_LOs X i ≤ i :=
begin
revert X, induction i with k IHi,
    {intro X, rw num_LOs_zero},
    {intro X, cases X with x X',
        {apply nat.zero_le},
        {cases x,
            {unfold num_LOs, apply succ_le_succ (IHi X')},
            {unfold num_LOs, apply le_succ_of_le (IHi X')}}}
end

lemma num_LOs_le_num_Os :
    num_LOs X i ≤ num_Os X :=
begin
revert X, induction i with k IHi,
    {intro X, rw num_LOs_zero, apply nat.zero_le},
    {intro X, cases X with x X',
        {apply nat.zero_le},
        {cases x,
            {unfold num_LOs, unfold num_Os, apply succ_le_succ (IHi X')},
            {unfold num_LOs, unfold num_Os, apply IHi X'}}}
end

lemma num_LOs_of_ovrlen (H : length X ≤ i) :
    num_LOs X i = num_Os X :=
begin
revert i, induction X with x X' IHX,
    {intros i H, trivial},
    {intros i H, cases i,
        {apply false.elim (not_succ_le_zero (length X') H)},
        {cases x,
            {unfold num_LOs, unfold num_Os, rw IHX _ (le_of_succ_le_succ H)},
            {unfold num_LOs, unfold num_Os, rw IHX _ (le_of_succ_le_succ H)}}}
end

lemma num_LOs_le_length (H : i + 1 ≤ length X ):
    num_LOs X i ≤ length X - 1 :=
begin
revert i, induction X with x X' ihX,
    {intros i H, trivial},
    {intros i H, cases i,
        {rw num_LOs_zero, apply nat.zero_le},
        {cases x,
            {unfold num_LOs, unfold length, rw nat.add_sub_cancel,
             apply le_trans,
                {apply add_le_add_right (ihX i (le_of_succ_le_succ H))},
                {rw nat.sub_add_cancel, apply le_trans,
                    {apply le_add_left 1 i},
                    {apply le_of_succ_le_succ H}}},
            {unfold num_LOs, unfold length, rw nat.add_sub_cancel,
             apply le_trans,
                {apply ihX i (le_of_succ_le_succ H)},
                {apply nat.sub_le}}}}
end

lemma num_LOs_le_sDel (H : i + 1 ≤ length X) :
    num_LOs X i ≤ num_Os (sDel X i) :=
begin
revert X, induction i with k IHi,
    {intros X H, rw num_LOs_zero, apply nat.zero_le},
    {intros X H, cases X with x X',
        {apply nat.zero_le},
        {cases X' with x' X'',
            {apply absurd H, unfold length, 
             apply not_le_of_gt (succ_lt_succ (zero_lt_succ k))},
            {cases x,
                {unfold num_LOs, unfold sDel, unfold num_Os,
                 apply succ_le_succ (IHi _ (le_of_succ_le_succ H))},
                {unfold num_LOs, unfold sDel, unfold num_Os,
                 apply IHi _ (le_of_succ_le_succ H)}}}}
end

lemma num_LOs_sIns (H : i + 1 ≤ length X) :
    num_LOs (sIns X i b) i = num_LOs X i :=
begin
revert X, induction i with k IHi,
    {intros X H, repeat {rw num_LOs_zero}},
    {intros X H, cases X with x X',
        {apply absurd H, apply not_le_of_gt (zero_lt_succ _)},
        {unfold sIns, cases x,
            {unfold num_LOs, rw IHi _ (le_of_succ_le_succ H)},
            {unfold num_LOs, rw IHi _ (le_of_succ_le_succ H)}}}
end

lemma num_LOs_sIns_one (H : length X ≤ i):
    num_LOs (sIns X i I) i = num_Os X :=
begin
revert X, induction i with k IHi,
    {intros X H, 
     have h : X = [], 
      from eq_nil_of_length_eq_zero (eq_zero_of_le_zero H),
     rw h, trivial},
    {intros X H, cases X with x X',
        {trivial},
        {unfold sIns, cases x,
            {unfold num_Os, unfold num_LOs, 
             rw IHi _ (le_of_succ_le_succ H)},
            {unfold num_Os, unfold num_LOs, 
             rw IHi _ (le_of_succ_le_succ H)}}}
end

lemma head_of_num_LOs
    (H : num_LOs (x::X) (succ i) = 0) :
    x = I :=
begin
cases x,
    {apply absurd H, apply nat.ne_of_gt, 
     unfold num_LOs, apply lt_succ_of_le (nat.zero_le (num_LOs X i))},
    {refl}
end

lemma sIns_one_of_num_LOs
    (H : num_LOs X i = num_LOs X j) :
    sIns X i I = sIns X j I :=
begin
revert i j, induction X with x X' IHX,
    {intros i j H, trivial},
    {intros i j H, cases i,
        {cases j,
            {refl},
            {rw num_LOs_zero at H, 
             have h : x = I, from head_of_num_LOs _ _ _ H.symm,
             rw h, unfold sIns, rw cons_inj', 
             rw h at H, unfold num_LOs at H, rw ← IHX 0 j,
                {rw sIns_zero},
                {rw num_LOs_zero, apply H}}},
        {cases j,
            {rw num_LOs_zero at H, 
             have h : x = I, from head_of_num_LOs _ _ _ H,
             rw h, unfold sIns, rw cons_inj', 
             rw h at H, unfold num_LOs at H, rw IHX i 0,
                {rw sIns_zero},
                {rw num_LOs_zero, apply H}},
            {unfold sIns, rw cons_inj', 
             apply IHX, cases x,
                {unfold num_LOs at H, apply succ_inj H},
                {unfold num_LOs at H, apply H}}}}
end

def num_RIs : list B → ℕ → ℕ 
| []     _       := 0
| (x::X) 0       := num_Is (x :: X)
| (x::X) (n + 1) := num_RIs X n

lemma num_RIs_zero :
    num_RIs X 0 = num_Is X :=
begin
cases X with x X',
    {trivial},
    {trivial}
end

lemma num_RIs_le_cons
    (x : B) (X : list B) (i : ℕ) :
    num_RIs X i ≤ num_RIs (x::X) i :=
begin
revert x i, induction X with x' X' IHX,
    {intros x i, unfold num_RIs, apply nat.zero_le},
    {intros x i, cases i,
        {unfold num_RIs, apply num_Is_le_cons},
        {unfold num_RIs, apply IHX}}
end

lemma num_RIs_succ_le
    (X : list B) (i : ℕ) :
    num_RIs X (succ i) ≤ num_RIs X i :=
begin
revert i, induction X with x' X' IHX,
    {intro i, trivial},
    {intro i, cases i,
        {unfold num_RIs, rw num_RIs_zero, apply num_Is_le_cons},
        {unfold num_RIs, apply IHX}}
end

lemma num_RIs_le :
    num_RIs X i ≤ length X - i :=
begin
revert i, induction X with x X' ihX,
    {intro i, unfold num_RIs, apply nat.zero_le},
    {intro i, cases i,
        {rw num_RIs_zero, apply num_Is_le_length},
        {unfold num_RIs, unfold length, rw nat.succ_sub_succ, apply ihX}}
end

lemma num_RIs_le_num_Is :
    num_RIs X i ≤ num_Is X :=
begin
revert i, induction X with x X' ihX,
    {intro i, unfold num_RIs, apply nat.zero_le},
    {intro i, cases i,
        {rw num_RIs_zero},
        {unfold num_RIs, apply le_trans (ihX i) (num_Is_le_cons _ _)}}
end

lemma num_RIs_of_ovrlen (H : length X ≤ i) :
    num_RIs X i = 0 :=
begin
revert i, induction X with x X' IHX,
    {intros i H, trivial},
    {intros i H, cases i,
        {apply false.elim (not_succ_le_zero (length X') H)},
        {cases x,
            {unfold num_RIs, rw IHX _ (le_of_succ_le_succ H)},
            {unfold num_RIs, rw IHX _ (le_of_succ_le_succ H)}}}
end

lemma num_RIs_sIns_zero :
    num_RIs (sIns X i O) i = num_RIs X i :=
begin
revert i, induction X with x X ihX,
    {intro i, rw sIns_nil, cases i,
        {trivial},
        {trivial}},
    {intro i, cases i,
        {trivial},
        {unfold sIns, unfold num_RIs, apply ihX}}   
end

lemma num_RIs_sIns (H : length X + 1 ≤ i) :
    num_RIs (sIns X i b) i = num_RIs X i :=
begin
revert i, induction X with x X' IHX,
    {intros i H, unfold sIns, cases i,
        {apply false.elim (not_succ_le_zero _ H)},
        {trivial}},
    {intros i H, cases i,
        {apply false.elim (not_succ_le_zero _ H)},
        {unfold num_RIs, rw sIns, rw num_RIs, 
         apply IHX _ (le_of_succ_le_succ H)}}
end

lemma head_of_num_RIs
    (H : num_RIs (x::X) (succ i) = num_Is (x::X)) :
    x = O :=
begin
cases x,
    {refl},
    {apply absurd H, apply nat.ne_of_lt, apply lt_succ_of_le,
     rw num_RIs, apply num_RIs_le_num_Is}
end

lemma sIns_zero_of_num_RIs
    (H : num_RIs X i = num_RIs X j) :
    sIns X i O = sIns X j O :=
begin
revert i j, induction X with x X' IHX,
    {intros i j H, trivial},
    {intros i j H, cases i,
        {cases j,
            {refl},
            {rw num_RIs_zero at H, 
             have h : x = O, from head_of_num_RIs _ _ _ H.symm,
             rw h, unfold sIns, rw cons_inj', 
             rw h at H, unfold num_RIs at H, rw ← IHX 0 j,
                {rw sIns_zero},
                {rw num_RIs_zero, apply H}}},
        {cases j,
            {rw num_RIs_zero at H, 
             have h : x = O, from head_of_num_RIs _ _ _ H,
             rw h, unfold sIns, rw cons_inj', 
             rw h at H, unfold num_RIs at H, rw IHX i 0,
                {rw sIns_zero},
                {rw num_RIs_zero, apply H}},
            {unfold sIns, rw cons_inj', 
             apply IHX, unfold num_RIs at H, apply H}}}  
end

lemma num_Is_sDel_lt_sub_mod
    (X : list B) (i : ℕ) :
    num_Is (sDel X i) < num_RIs X i + i + 1 :=
begin
revert i, induction X with x X' IHX,
    {intro i, apply zero_lt_succ},
    {intro i, cases X' with x' X'',
        {rw sDel_singleton, apply zero_lt_succ},
        {cases i,
            {unfold sDel, unfold num_RIs, 
             rw lt_succ_iff, rw add_zero, apply num_Is_le_cons},
            {unfold sDel, unfold num_RIs, 
             apply lt_of_le_of_lt 
              (num_Is_cons_le x (sDel (x'::X'') i))
              (succ_lt_succ (IHX i))}}}
end

end list

open nat vector 

variables {n : ℕ} (X Y : vector B n) (i j : ℕ) (b : B)

def wt {n : ℕ} (X : vector B n) : ℕ :=
    list.num_Is (to_list X)

lemma ne_of_wt_lt (H : wt X < wt Y):  
    X ≠ Y :=
by {assume h, rw h at H, apply lt_le_antisymm H, refl}

lemma ne_of_wt_gt (H : wt Y < wt X):  
    X ≠ Y :=
by {assume h, rw h at H, apply lt_le_antisymm H, refl}

lemma wt_repO :  
  wt (repeat O n) = 0 :=
by {unfold vector.repeat, unfold wt, apply list.num_Is_repO}

lemma wt_repI :  
  wt (repeat I n) = n :=
by {unfold vector.repeat, unfold wt, apply list.num_Is_repI}

lemma  wt_le_length : wt X ≤ n :=
begin
unfold wt, apply le_trans,
    {apply list.num_Is_le_length},
    {rw to_list_length}
end

lemma  wt_sDel_le : 
    wt (sDel X i) ≤ wt X :=
begin
unfold vector.sDel, unfold wt,
rw to_list_mk, apply list.num_Is_sDel_le
end

lemma  wt_le_sDel : 
    wt X - 1 ≤ wt (sDel X i) :=
begin
unfold vector.sDel, unfold wt,
rw to_list_mk, apply list.num_Is_le_sDel
end

lemma sDel_of_wt_le (Hx : wt X ≤ 1) :  
  ∃ i : ℕ, sDel X i = repeat O (n - 1) :=
begin
cases list.sDel_of_num_Is_le (to_list X) _ with i hi,
  {rw to_list_length at hi,
   apply exists.intro i, 
   rw subtype.ext, unfold vector.sDel, 
   repeat {rw ← to_list}, rw to_list_mk, apply hi},
  {apply Hx}
end 

lemma sDel_of_le_wt (HX : n - 1 ≤ wt X) :  
  ∃ i : ℕ, sDel X i = repeat I (n - 1) :=
begin
cases list.sDel_of_le_num_Is (to_list X) _ with i hi,
  {rw to_list_length at hi,
   apply exists.intro i, 
   rw subtype.ext, unfold vector.sDel, 
   repeat {rw ← to_list}, rw to_list_mk, apply hi},
  {rw to_list_length, apply HX}
end 

def num_LOs : ℕ :=
  list.num_LOs (to_list X) i 

lemma num_LOs_zero :
    num_LOs X 0 = 0 :=
by {unfold num_LOs, apply list.num_LOs_zero} 

lemma num_LOs_le :
    num_LOs X i ≤ i :=
by {unfold num_LOs, apply list.num_LOs_le} 

lemma num_LOs_le_length (H : i + 1 ≤ n):
    num_LOs X i ≤ n - 1 :=
begin
unfold num_LOs, apply le_trans,
    {apply list.num_LOs_le_length,
     rw to_list_length, apply H},
    {rw to_list_length}
end

lemma num_LOs_sIns (H : i + 1 ≤ n) :
    num_LOs (sIns X i b) i = num_LOs X i :=
begin
unfold num_LOs, apply list.num_LOs_sIns,
rw to_list_length, apply H
end

lemma sIns_one_of_num_LOs
    {n : ℕ} (X : vector B n) (i j : ℕ)
    (H : num_LOs X i = num_LOs X j) :
    sIns X i I = sIns X j I :=
begin
unfold vector.sIns, rw subtype.ext,
repeat {rw ← to_list}, repeat {rw to_list_mk}, 
apply list.sIns_one_of_num_LOs,
unfold num_LOs at H, apply H 
end

def num_RIs : ℕ :=
  list.num_RIs (to_list X) i 

lemma num_RIs_zero :
    num_RIs X 0 = wt X :=
by {unfold num_RIs, apply list.num_RIs_zero} 

lemma num_RIs_le :
    num_RIs X i ≤ n - i :=
begin
unfold num_RIs, apply le_trans,
    {apply list.num_RIs_le},
    {rw to_list_length}
end

lemma num_RIs_le_wt :
    num_RIs X i ≤ wt X :=
by {unfold num_RIs, unfold wt, apply list.num_RIs_le_num_Is}

lemma num_RIs_of_ovrlen (H : n ≤ i) :
    num_RIs X i = 0 :=
begin
unfold num_RIs, apply list.num_RIs_of_ovrlen, 
rw to_list_length, apply H
end

lemma num_RIs_sIns_zero :
    num_RIs (sIns X i O) i = num_RIs X i :=
by {unfold num_RIs, apply list.num_RIs_sIns_zero}

lemma num_RIs_sIns (H : n + 1 ≤ i) :
    num_RIs (sIns X i b) i = num_RIs X i :=
begin
unfold num_RIs, apply list.num_RIs_sIns, 
rw to_list_length, apply H
end

lemma sIns_zero_of_num_RIs
    {n : ℕ} (X : vector B n) (i j : ℕ)
    (H : num_RIs X i = num_RIs X j) :
    sIns X i O = sIns X j O :=
begin
unfold vector.sIns, rw subtype.ext,
repeat {rw ← to_list}, repeat {rw to_list_mk}, 
apply list.sIns_zero_of_num_RIs,
unfold num_RIs at H, apply H 
end

lemma num_Is_sDel_lt_sub_mod :
    wt (sDel X i) < num_RIs X i + i + 1 :=
by {unfold num_RIs, apply list.num_Is_sDel_lt_sub_mod}

lemma wt_flip {n : ℕ} (X : vector B n) :  
    wt (B.vector.flip X) = n - wt X :=
begin
unfold wt, unfold B.vector.flip, 
rw to_list_mk, rw list.num_Is_flip, rw to_list_length
end

def Iic_wt (a : ℕ) (X : vector B n) :=  wt X ≤ a

instance decidable_pred_Iic_wt (a : ℕ) : 
  decidable_pred (@Iic_wt n a) :=
by {intro s, unfold Iic_wt, apply_instance}

def Icc_wt (a b : ℕ) (X : vector B n) := a ≤ wt X ∧ wt X ≤ b

instance decidable_pred_Icc_wt (a b : ℕ) : 
  decidable_pred (@Icc_wt n a b) :=
by {intro s, unfold Icc_wt, apply_instance}

lemma Icc_wt_self (a : ℕ) (X : vector B n) : 
  Icc_wt a a X ↔ wt X = a :=
by {unfold Icc_wt, rw le_antisymm_iff, rw and_comm}

def Ici_wt (a : ℕ) (X : vector B n) := a ≤ wt X 

instance decidable_pred_Ici_wt (a : ℕ) : 
  decidable_pred (@Ici_wt n a) :=
by {intro s, unfold Ici_wt, apply_instance}

open finset B.finset

lemma not_mem_filter_Icc_wt_of_lt 
  (C : finset (vector B n)) (a b : ℕ) (X : vector B n) (H : wt X < a):
  X ∉ filter (Icc_wt a b) C :=
begin
assume h, rw mem_filter at h,
apply absurd h.right.left, apply not_le_of_lt H
end

lemma not_mem_filter_Icc_wt_of_gt 
  (C : finset (vector B n)) (a b : ℕ) (X : vector B n) (H : b < wt X):
  X ∉ filter (Icc_wt a b) C :=
begin
assume h, rw mem_filter at h,
apply absurd h.right.right, apply not_le_of_lt H
end

lemma div_Iic_Icc_Ici (a b : ℕ) (C : finset (vector B n)) :
  filter (Iic_wt a) C ∪ filter (Icc_wt (a + 1) (b - 1)) C ∪ filter (Ici_wt b) C = C :=
begin
apply subset.antisymm,
  {apply union_subset,
    {apply union_subset,
      {apply filter_subset},
      {apply filter_subset}},
    {apply filter_subset}},
  {intros x hx, cases decidable.em (wt x ≤ a) with hle hnle,
    {repeat {rw mem_union}, left, left, 
     rw mem_filter, apply and.intro hx hle},
    {cases decidable.em (wt x ≤  b - 1) with hle' hnle',
      {repeat {rw mem_union}, left, right, 
       rw mem_filter, apply and.intro hx,
       apply and.intro (succ_le_of_lt (lt_of_not_ge hnle)) hle'},
      {repeat {rw mem_union}, right, 
       rw mem_filter, apply and.intro hx,
       apply nat.le_of_pred_lt (lt_of_not_ge hnle')}}}
end

lemma filter_wt_eq_inter_of_ne
  (C : finset (vector B n)) (a b : ℕ) (H : a ≠ b) :
  filter (λ x, wt x = a) C ∩ (filter (λ x, wt x = b) C) = ∅ :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_inter at hx, repeat {rw mem_filter at hx},
   have h : a = b,
    {rw ← hx.left.right, rw ← hx.right.right},
   contradiction},
  {apply empty_subset}
end

lemma filter_wt_eq_inter_Icc_of_lt
  (C : finset (vector B n)) (a b c : ℕ) (H : a + 1 ≤ b) :
  filter (λ x, wt x = a) C ∩ filter (Icc_wt b c) C = ∅ :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_inter at hx, repeat {rw mem_filter at hx},
   have h : b ≤ a,
    {rw ← hx.left.right, apply hx.right.right.left},
   apply absurd h, apply not_le_of_gt, 
   apply lt_of_succ_le H},
  {apply empty_subset}
end

lemma filter_wt_eq_inter_Icc_of_gt
  (C : finset (vector B n)) (a b c : ℕ) (H : c + 1 ≤ a) :
  filter (λ x, wt x = a) C ∩ filter (Icc_wt b c) C = ∅ :=
begin
apply subset.antisymm,
  {intros x hx, rw mem_inter at hx, repeat {rw mem_filter at hx},
   have h : a ≤ c,
    {rw ← hx.left.right, apply hx.right.right.right},
   apply absurd h, apply not_le_of_gt, 
   apply lt_of_succ_le H},
  {apply empty_subset}
end

lemma flip_filter_subset_swap (C : finset (vector B n)) (a b : ℕ) : 
  flip (filter (Icc_wt a b) C) ⊆ filter (Icc_wt (n - b) (n - a)) (flip C) := 
begin
intros x hx, rw mem_flip at hx, 
cases hx with y hx, cases hx with hy hxy, rw mem_filter at hy,
have h1 : n - b ≤ wt x,
  {rw ← hxy, rw wt_flip, apply nat.sub_le_sub_left, apply hy.right.right},
have h2 : wt x ≤ n - a,
  {rw ← hxy, rw wt_flip, apply nat.sub_le_sub_left, apply hy.right.left},
rw mem_filter, apply and.intro,
  {rw mem_flip, apply exists.intro y, apply exists.intro hy.left, apply hxy},
  {apply and.intro h1 h2}
end

lemma filter_flip_subset_swap (C : finset (vector B n)) (a b : ℕ) : 
  filter (Icc_wt a b) (flip C) ⊆ flip (filter (Icc_wt (n - b) (n - a)) C) := 
begin
intros x hx, rw mem_filter at hx, rw mem_flip at hx,
cases hx.left with y hx, cases hx with hy hxy, rw mem_flip,
apply exists.intro y, apply exists.intro,
    {rw mem_filter, apply and.intro hy,
     unfold Icc_wt, rw B.vector.flip_eq_iff at hxy, 
     rw hxy, apply and.intro,
        {rw wt_flip, apply nat.sub_le_sub_left,
         apply hx.right.right},
        {rw wt_flip, apply nat.sub_le_sub_left,
         apply hx.right.left}},
    {apply hxy}
end

lemma flip_filter_swap (C : finset (vector B n)) (a b : ℕ) (Ha : a ≤ n) (Hb : b ≤ n): 
  flip (filter (Icc_wt a b) C) = filter (Icc_wt (n - b) (n - a)) (flip C) := 
begin
apply subset.antisymm,
  {apply flip_filter_subset_swap},
  {apply subset.trans,
    {apply filter_flip_subset_swap},
    {rw sub_sub_assoc (refl _) Ha,
     rw nat.sub_self, rw zero_add,
     rw sub_sub_assoc (refl _) Hb,
     rw nat.sub_self, rw zero_add, refl}}
end

lemma filter_flip_swap (C : finset (vector B n)) (a b : ℕ) (Ha : a ≤ n) (Hb : b ≤ n): 
  filter (Icc_wt a b) (flip C) = flip (filter (Icc_wt (n - b) (n - a)) C)  := 
begin
rw flip_filter_swap _ _ _ (nat.sub_le_self _ _) (nat.sub_le_self _ _),
rw nat.sub_sub_assoc (refl _) Ha, rw nat.sub_self, rw zero_add,
rw nat.sub_sub_assoc (refl _) Hb, rw nat.sub_self, rw zero_add
end
