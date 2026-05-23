/- Copyright Yuki Kondo c/o Manabu Hagiwara 2022, 2026 -/
import .NumOsNumIs .DelCode .Optimal

open nat 

namespace list 

open list 

variables (x : B) (X Y : list B) (i : ℕ) (b : B)

def moment: list B → ℕ
| []     := 0 
| (x::X) := moment X + num_Is (x::X)

prefix `ρ` : 25 := moment

namespace hidden 

def moment_sub : list B → ℕ → ℕ 
| []     _ := 0 
| (O::X) n := moment_sub X (n + 1)
| (I::X) n := moment_sub X (n + 1) + n

lemma moment_sub_succ
  (X : list B) (n : ℕ) :
  moment_sub X (n + 1) = moment_sub X n + num_Is X :=
begin
revert n, induction X with x X' IHX,
  {intro n, trivial},
  {intro n, cases x,
    {unfold moment_sub, unfold num_Is, rw IHX},
    {unfold moment_sub, unfold num_Is, rw IHX, simp}}
end

def moment :=  moment_sub X 1

lemma moment_nil :
  moment [] = 0 :=
by trivial

lemma moment_singleton :
  moment [x] = num_Is [x] :=
begin
cases x,
  {trivial},
  {trivial}
end

lemma moment_cons :
  moment (x::X) = moment X + num_Is (x::X) :=
begin
revert x, cases X with x' X',
  {intro x, rw moment_singleton,
   rw moment_nil, rw nat.zero_add},
  {intro x, unfold moment, cases x,
    {unfold moment_sub, unfold num_Is, apply moment_sub_succ},
    {unfold moment_sub, unfold num_Is, 
     rw ← add_assoc, rw moment_sub_succ}}
end

lemma moment_iff_moment :
  moment X = list.moment X :=
begin
induction X with x X' IHX,
  {trivial},
  {rw moment_cons, rw list.moment, rw IHX}
end

end hidden 

lemma moment_nil : (ρ []) = 0 := 
by trivial

lemma moment_zero : (ρ [O]) = 0 := 
by trivial

lemma moment_one : (ρ [I]) = 1 := 
by trivial

lemma moment_cons :
  (ρ x::X) = (ρ X) + num_Is (x::X) := 
by trivial

lemma moment_le_cons :
  (ρ X) ≤  (ρ x::X) := 
by {unfold moment, simp}

lemma moment_sDel_le : 
  (ρ sDel X i) ≤ (ρ X) := 
begin
revert i, induction X with x X' IHX,
  {intro i, trivial},
  {intro i, cases X' with x' X'',
    {apply nat.zero_le},
    {cases i,
      {unfold sDel, apply moment_le_cons},
      {unfold sDel, rw moment, rw moment, 
       apply add_le_add (IHX i), cases x,
        {unfold num_Is, apply num_Is_sDel_le},
        {unfold num_Is, apply succ_le_succ, apply num_Is_sDel_le}}}}
end

lemma moment_le_sIns :
  (ρ X) ≤ (ρ sIns X i b) := 
begin
revert i, induction X with x X' IHX,
  {intro i, unfold moment, apply nat.zero_le},
  {intro i, cases i,
    {unfold sIns, apply moment_le_cons},
    {unfold sIns, unfold moment, 
     apply add_le_add (IHX i), cases x,
      {unfold num_Is, apply num_Is_le_sIns},
      {unfold num_Is, apply nat.succ_le_succ, 
       apply num_Is_le_sIns}}}
end

lemma moment_sIns_zero :
  (ρ sIns X i O) = (ρ X) + num_RIs X i := 
begin
revert i, induction X with x X' IHX,
  {intro i, unfold sIns, rw moment_zero, 
   rw moment_nil, rw num_RIs},
  {intro i, cases i,
    {unfold sIns, unfold moment, 
     unfold num_Is, unfold num_RIs},
    {unfold sIns, unfold moment, unfold num_RIs, 
     rw num_Is_cons, rw num_Is_cons x X', rw IHX,
     rw num_Is_sIns_zero, simp}}
end

lemma moment_sIns_one :
  (ρ sIns X i I) = (ρ X) + num_LOs X i + num_Is X + 1 := 
begin
revert i, induction X with x X' IHX,
  {intro i, unfold sIns, rw moment_one,
   unfold moment, cases i,
    {unfold num_LOs, unfold num_Is},
    {unfold num_LOs, unfold num_Is}},
  {intro i, cases i,
    {unfold sIns, rw moment, unfold num_Is, 
     rw num_LOs_zero, simp},
    {unfold sIns, unfold moment, rw IHX, cases x,
      {unfold num_Is, rw num_Is_sIns_one, rw num_LOs, simp},
      {unfold num_Is, rw num_Is_sIns_one,
       rw num_LOs, rw ← add_assoc, simp}}}
end

lemma moment_sub_sDel_of_sDel_O 
  (H : sIns (sDel X i) i O = X) :
  (ρ X) - (ρ sDel X i) = num_RIs (sDel X i) i :=
begin
rw ← H, rw sDel_sIns_id, rw moment_sIns_zero,
rw add_comm, rw nat.add_sub_cancel
end

lemma moment_sub_sDel_of_sDel_I 
  (H : sIns (sDel X i) i I = X) :
  (ρ X) - (ρ sDel X i) = num_LOs (sDel X i) i + num_Is (sDel X i) + 1 :=
begin
rw ← H, rw sDel_sIns_id, rw moment_sIns_one,
repeat {rw add_assoc}, rw add_comm, rw nat.add_sub_cancel
end

lemma moment_sub_sDel_le :
  (ρ X) - (ρ sDel X i) ≤ length X :=
begin
cases X with x X',
  {trivial},
  {cases sIns_sDel_id (x::X') i _ with b hb,
    {cases b,
      {rw moment_sub_sDel_of_sDel_O _ _ hb,
       apply le_trans (num_RIs_le_num_Is _ _),
       apply le_trans (num_Is_le_length _),
       rw length_sDel, apply nat.sub_le},
      {rw moment_sub_sDel_of_sDel_I _ _ hb,
       unfold length, apply succ_le_succ,
       apply le_trans,
        {apply add_le_add_right, apply num_LOs_le_num_Os},
        {rw num_Os_add_num_Is, rw length_sDel, 
         unfold length, rw nat.add_sub_cancel}}},
    {unfold length, apply succ_le_succ (nat.zero_le _)}}
end

lemma sIns_fig_of_pos_of_moment
    (H1 : 1 ≤ length X)
    (H2 : (ρ X) - (ρ sDel X i) ≤ num_Is (sDel X i)) :
    sIns (sDel X i) i O = X :=
begin
cases sIns_sDel_id _ _ H1 with b hb, cases b,
  {rw hb},
  {apply absurd H2, rw not_le,
   rw moment_sub_sDel_of_sDel_I _ _ hb,
   rw lt_succ_iff, apply nat.le_add_left}
end

lemma sIns_fig_of_neg_of_moment
    (H1 : 1 ≤ length X)
    (H2 : ¬ (ρ X) - (ρ sDel X i) ≤ num_Is (sDel X i)) :
    sIns (sDel X i) i I = X:=
begin
cases sIns_sDel_id _ _ H1 with b hb, cases b,
  {have h : (ρ X) - (ρ sDel X i) ≤ num_Is (sDel X i),
    {rw moment_sub_sDel_of_sDel_O _ _ hb,
     apply num_RIs_le_num_Is},
   contradiction},
  {rw hb}
end

end list 

namespace vector

variables {n : ℕ} (X : vector B n) (i : ℕ) (b : B)

def moment : ℕ :=
  list.moment (to_list X)

prefix `ρ` : 25 := moment

lemma moment_nil : 
  (ρ vector.nil) = 0 := 
by {unfold moment, apply list.moment_nil}

lemma moment_sDel_le : 
  (ρ sDel X i) ≤ (ρ X) := 
by {unfold moment, apply list.moment_sDel_le}

lemma moment_le_sIns :
  (ρ X) ≤ (ρ sIns X i b) := 
by {unfold moment, apply list.moment_le_sIns}

lemma moment_sIns_zero :
  (ρ sIns X i O) = (ρ X) + num_RIs X i := 
by {unfold moment, apply list.moment_sIns_zero}

lemma moment_sIns_one :
  (ρ sIns X i I) = (ρ X) + num_LOs X i + wt X + 1 := 
by {unfold moment, apply list.moment_sIns_one}

lemma moment_sub_sDel_of_sDel_O 
  (X : vector B (n + 1))
  (H : sIns (sDel X i) i O = X) :
  (ρ X) - (ρ sDel X i) = num_RIs (sDel X i) i :=
begin
unfold moment, apply list.moment_sub_sDel_of_sDel_O,
unfold sIns at H, rw subtype.ext at H,
rw ← to_list at H, rw to_list_mk at H, apply H  
end

lemma moment_sub_sDel_of_sDel_I 
  (X : vector B (n + 1))
  (H : sIns (sDel X i) i I = X) :
  (ρ X) - (ρ sDel X i) = num_LOs (sDel X i) i + wt (sDel X i) + 1 :=
begin
unfold moment, apply list.moment_sub_sDel_of_sDel_I,
unfold sIns at H, rw subtype.ext at H,
rw ← to_list at H, rw to_list_mk at H, apply H  
end

lemma moment_sub_sDel_le :
  (ρ X) - (ρ sDel X i) ≤ n :=
begin
unfold moment, apply le_trans,
  {apply list.moment_sub_sDel_le},
  {rw to_list_length}
end

lemma sIns_fig_of_pos_of_moment
    (X : vector B (n + 1))
    (H : (ρ X) - (ρ sDel X i) ≤ wt (sDel X i)) :
    sIns (sDel X i) i O = X :=
begin
unfold sIns, unfold sDel, rw subtype.ext,
repeat {rw ← to_list}, repeat {rw to_list_mk}, 
apply list.sIns_fig_of_pos_of_moment,
  {rw to_list_length, apply succ_le_succ (nat.zero_le _)},
  {apply H}
end

lemma sIns_fig_of_neg_of_moment
    (X : vector B (n + 1))
    (H : ¬ (ρ X) - (ρ sDel X i) ≤ wt (sDel X i)) :
    sIns (sDel X i) i I = X :=
begin
unfold sIns, unfold sDel, rw subtype.ext,
repeat {rw ← to_list}, repeat {rw to_list_mk}, 
apply list.sIns_fig_of_neg_of_moment,
  {rw to_list_length, apply succ_le_succ (nat.zero_le _)},
  {apply H}
end

end vector


variables {n : ℕ} (a : ℕ) (X : vector B n)

namespace set 

def VTCode (n a : ℕ) : set (vector B n) :=
  {X | (ρ X) % (n + 1) =  a % (n + 1)}

def mem_VTCode :
  X ∈ VTCode n a ↔ (ρ X) % (n + 1) = a % (n + 1) :=
by trivial

instance decidable_pred_VTCode (n a : ℕ) : 
  decidable_pred (VTCode n a) :=
by {intro x, unfold VTCode, apply_instance}


namespace decoding_alg

namespace list 

open list

def sub_mod (m a : ℕ) (X : list B) : ℕ :=
if (ρ X) < a then (a - (ρ X)) % m 
             else (m - ((ρ X) - a) % m) % m

lemma sub_mod_zero (m : ℕ) (X : list B) :
    sub_mod m 0 X = (m - (ρ X) % m) % m :=
begin
unfold sub_mod, rw if_neg, 
  {rw nat.sub_zero},
  {apply not_lt_of_ge (nat.zero_le _)}
end 

lemma sub_mod_mod_self (m : ℕ) (X : list B) :
  sub_mod m m X = sub_mod m 0 X :=
begin
rw sub_mod, rw sub_mod_zero,
cases decidable.em ((ρ X) < m) with hlt hnlt,
  {rw if_pos hlt, rw mod_eq_of_lt hlt},
  {rw if_neg hnlt, rw mod_eq_sub_mod (le_of_not_gt hnlt)}
end 

lemma sub_mod_nil (m : ℕ) :
    sub_mod m a [] = a % m :=
begin
cases a, 
  {rw sub_mod_zero, rw list.moment_nil, rw zero_mod, 
   rw nat.sub_zero, rw mod_self},
  {unfold sub_mod, rw list.moment_nil, 
   rw if_pos (zero_lt_succ _), rw nat.sub_zero}
end 

lemma sub_mod_add (m : ℕ) (X : list B) :
  sub_mod m (a + m) X = sub_mod m a X :=
begin
induction a using nat.case_strong_induction_on with a IHa,
  {rw zero_add, rw sub_mod_mod_self},
  {unfold sub_mod, cases decidable.em ((ρ X) < a + 1) with hlt hnlt,
    {rw if_pos hlt, rw if_pos,
      {rw nat.add_comm (a + 1), rw nat.add_sub_assoc, 
        {rw add_mod_left},
        {apply le_of_lt hlt}},
      {apply lt_of_lt_of_le hlt (le_add_right _ _)}},
    {rw if_neg hnlt, rw not_lt at hnlt, 
     cases decidable.em ((ρ X) < succ a + m) with hlt' hnlt',
      {rw if_pos hlt', rw @mod_eq_of_lt ((ρ X) - (a + 1)),
        {rw sub_sub_eq_add_sub hnlt, rw add_comm},
        {rw nat.sub_lt_left_iff_lt_add hnlt, apply hlt'}},
      {rw if_neg hnlt', rw not_lt at hnlt', 
       rw ← nat.sub_sub, rw ← mod_eq_sub_mod,
       rw ge, rw nat.le_sub_left_iff_add_le hnlt, apply hnlt'}}}
end 

lemma sub_mod_sub (m : ℕ) (X : list B) (H : m  ≤ a) :
  sub_mod m (a - m) X = sub_mod m a X :=
by {rw ← sub_mod_add _ _ _, rw nat.sub_add_cancel H}

lemma sub_mod_mod (m : ℕ) (X : list B) :
  sub_mod m (a % m) X = sub_mod m a X :=
begin
cases m,
  {rw mod_zero},
  {induction a using nat.case_strong_induction_on with a IHa,
    {rw zero_mod},
    {cases decidable.em (succ a ≤ m + 1) with hle hnle,
      {cases decidable.em (succ a = m + 1) with heq hneq,
        {rw heq, rw mod_self, rw sub_mod_mod_self},
        {rw mod_def, rw if_neg,
         assume h, apply absurd h.right,
         rw not_le, apply lt_of_le_of_ne hle hneq}},
      {rw mod_eq_sub_mod (le_of_not_ge hnle), rw IHa,
        {rw sub_mod_sub _ _ _ (le_of_not_ge hnle)},
        {rw succ_sub_succ, apply nat.sub_le}}}}
end 

lemma sub_mod_sDel
  {n a : ℕ} {X : list B} (HX : length X = n) 
  (H : (ρ X) % (n + 1) = a % (n + 1)) (i : ℕ) : 
  sub_mod (n + 1) a (sDel X i) = (ρ X) - (ρ sDel X i) :=
begin
cases X with x X',
  {rw sDel_nil, rw sub_mod_nil, rw ← H, 
   rw moment_nil, rw zero_mod},
  {rw ← sub_mod_mod, rw ← H, rw sub_mod_mod, unfold sub_mod, 
   cases decidable.em ((ρ (sDel (x :: X') i)) = (list.moment (x :: X'))) with heq hneq,
    {rw if_neg,
      {rw heq, rw nat.sub_self, rw zero_mod, 
       rw nat.sub_zero, rw mod_self},
      {apply not_lt_of_ge, rw heq, apply le_refl}},
    {rw if_pos (lt_of_le_of_ne (list.moment_sDel_le _ _) hneq),
     rw mod_eq_of_lt, apply lt_of_le_of_lt,
      {apply list.moment_sub_sDel_le},
      {rw HX, apply lt_succ_of_le (le_refl _)}}}
end

lemma sub_mod_sDel_of_pos
    {n a : ℕ} {X : list B} (HX : 1 ≤ length X) 
    (HXn : length X = n) (HXa : (ρ X) % (n + 1) = a % (n + 1)) 
    (i : ℕ) (H : sub_mod (n + 1) a (sDel X i) ≤ num_Is (sDel X i)) :
    sub_mod (n + 1) a (sDel X i) = num_RIs (sDel X i) i :=
begin
rw sub_mod_sDel HXn HXa,
apply moment_sub_sDel_of_sDel_O, 
rw sIns_fig_of_pos_of_moment _ _ HX,
rw ← sub_mod_sDel HXn HXa, apply H
end

lemma sub_mod_sDel_of_neg
    {n a : ℕ} {X : list B} (HX : 1 ≤ length X) 
    (HXn : length X = n) (HXa : (ρ X) % (n + 1) = a % (n + 1)) 
    (i : ℕ) (H : ¬ sub_mod (n + 1) a (sDel X i) ≤ num_Is (sDel X i)) :
    sub_mod (n + 1) a (sDel X i) = num_LOs (sDel X i) i + num_Is (sDel X i) + 1 :=
begin
rw sub_mod_sDel HXn HXa,
apply moment_sub_sDel_of_sDel_I, 
rw sIns_fig_of_neg_of_moment _ _ HX,
rw ← sub_mod_sDel HXn HXa, apply H
end

lemma sIns_fig_of_pos
    {n a : ℕ} {X : list B} (HX : 1 ≤ length X) 
    (HXn : length X = n) (HXa : (ρ X) % (n + 1) = a % (n + 1)) 
    (i : ℕ) (H : sub_mod (n + 1) a (sDel X i) ≤ num_Is (sDel X i))   :
  sIns (sDel X i) i O = X :=
begin
cases sIns_sDel_id _ i HX with b hb, cases b,
  {apply hb},
  {apply absurd H, apply not_le_of_gt,
   rw sub_mod_sDel HXn HXa,
   rw moment_sub_sDel_of_sDel_I _ _ hb,
   apply lt_succ_of_le, apply nat.le_add_left}
end

lemma sIns_fig_of_neg
    {n a : ℕ} {X : list B} (HX : 1 ≤ length X) 
    (HXn : length X = n) (HXa : (ρ X) % (n + 1) = a % (n + 1)) 
    (i : ℕ) (H : ¬ sub_mod (n + 1) a (sDel X i) ≤ num_Is (sDel X i))   :
  sIns (sDel X i) i I = X :=
begin
cases sIns_sDel_id _ i HX with b hb, cases b,
  {have h : sub_mod (n + 1) a (sDel X i) ≤ num_Is (sDel X i),
    {rw sub_mod_sDel HXn HXa,
     rw moment_sub_sDel_of_sDel_O _ _ hb,
     apply num_RIs_le_num_Is},
   contradiction},
  {apply hb},
end

def min_num_LOs : list B → ℕ → ℕ 
|[]     _       := 0
|(x::X) 0       := 0
|(O::X) (n + 1) := min_num_LOs X n + 1
|(I::X) (n + 1) := min_num_LOs X (n + 1) + 1

lemma min_num_LOs_zero (X : list B) :
  min_num_LOs X 0 = 0 :=
begin
cases X with x X',
  {trivial},
  {cases x,
    {trivial},
    {trivial}}
end

lemma min_num_LOs_of_num_Os (X : list B) (i : ℕ) 
  (H : num_Os X + 1 ≤ i) :
  min_num_LOs X i = length X :=
begin
revert i, induction X with x X' IHX,
  {intros i H, trivial},
  {intros i H, cases i,
    {apply false.elim (not_succ_le_zero (num_Os (x::X')) H)},
    {cases x,
      {unfold min_num_LOs, unfold length, rw IHX,
       apply le_of_succ_le_succ H},
      {unfold min_num_LOs, unfold length, rw IHX, apply H}}}
end

lemma num_LOs_min_num_LOs (X : list B) (i : ℕ)  
  (H : i ≤ num_Os X) :
  num_LOs X (min_num_LOs X i) = i :=
begin
revert i, induction X with x X' IHX,
  {intros i H, cases i,
    {trivial}, 
    {apply false.elim (not_succ_le_zero i H)}},
  {intros i H, cases i,
    {rw min_num_LOs_zero, rw list.num_LOs_zero},
    {cases x,
      {unfold min_num_LOs, unfold list.num_LOs, rw IHX,
       unfold num_Os at H, apply le_of_succ_le_succ H},
      {unfold min_num_LOs, unfold list.num_LOs, rw IHX, 
       unfold num_Os at H, apply H}}}
end

def max_num_RIs : list B → ℕ → ℕ 
| []     _ := 0
| (x::X) n := if num_Is X + 1 ≤ n 
              then max_num_RIs X n else max_num_RIs X n + 1

lemma max_num_RIs_zero (X : list B) :
  max_num_RIs X 0 = length X :=
begin
induction X with x X' IHX,
  {trivial},
  {unfold max_num_RIs, 
   cases decidable.em (num_Is X' + 1 ≤ 0) with h_le h_nle,
    {apply false.elim (not_succ_le_zero (num_Is X') h_le)},
    {rw if_neg h_nle, unfold length, rw IHX}}
end

lemma max_num_RIs_of_num_Is (X : list B) (i : ℕ) 
  (H : num_Is X + 1 ≤ i) :
  max_num_RIs X i = 0 :=
begin
revert i, induction X with x X' IHX,
  {intros i H, trivial},
  {intros i H, cases i,
    {apply false.elim (not_succ_le_zero (num_Is (x::X')) H)},
    {unfold max_num_RIs, 
     have h : num_Is X' + 1 ≤ succ i, 
      {apply le_trans (add_le_add_right (num_Is_le_cons x X') 1) H},
     rw if_pos h, rw IHX (succ i) h}}
end

lemma num_RIs_max_num_RIs (X : list B) (i : ℕ) 
  (H : i ≤ num_Is X) :
  num_RIs X (max_num_RIs X i) = i :=
begin
revert i, induction X with x X' IHX,
  {intros i H, cases i,
    {trivial},
    {apply false.elim (not_succ_le_zero i H)}},
  {intros i H, unfold max_num_RIs, 
    cases decidable.em (num_Is X' + 1 ≤ i) with hle hnle,
    {rw if_pos hle, 
     have h : max_num_RIs X' i = 0, 
      {apply max_num_RIs_of_num_Is _ _ hle},
     rw h, unfold list.num_RIs, 
     apply le_antisymm (le_trans (num_Is_cons_le x X') hle) H},
    {rw if_neg hnle, unfold list.num_RIs, 
     rw IHX _  (le_of_lt_succ (lt_of_not_ge hnle))}}
end

def decoding_alg (n a : ℕ) (X : list B) :=
if length X = n then X 
    else if sub_mod (n + 1) a X  ≤ num_Is X
        then sIns X (max_num_RIs X (sub_mod (n + 1) a X)) O
        else sIns X (min_num_LOs X ((sub_mod (n + 1) a X) - num_Is X - 1)) I

lemma length_decoding_alg 
  (n a : ℕ) (X : list B) (H : length X = n - 1) :
  length (decoding_alg n a X) = n :=
begin 
unfold decoding_alg, 
cases decidable.em (n ≤ 0) with hle_len hnle_len,
    {have h : length X = n,
      {rw H, rw eq_zero_of_le_zero hle_len}, 
     rw if_pos h, rw h},
    {have h : length X ≠ n,
      {rw H, apply nat.ne_of_lt, apply nat.sub_lt_self,
        {apply lt_of_not_ge hnle_len},
        {apply zero_lt_one}},
     rw if_neg h, 
     cases decidable.em(sub_mod (n + 1) a X ≤ num_Is X) with hle hnle,
        {rw if_pos hle, rw list.length_sIns, rw H, 
         rw nat.sub_add_cancel, apply nat.succ_le_of_lt, 
         apply lt_of_not_ge hnle_len},
        {rw if_neg hnle, rw list.length_sIns, rw H,
         rw nat.sub_add_cancel, apply nat.succ_le_of_lt, 
         apply lt_of_not_ge hnle_len}}
end

lemma sDelErr_correctable_of_pos
    {n a : ℕ} {X : list B} (HX : 1 ≤ length X) 
    (HXn : length X = n) (HXa : (ρ X) % (n + 1) = a % (n + 1)) 
    (i : ℕ) (Hr : sub_mod (n + 1) a (sDel X i) ≤ num_Is (sDel X i)) :
    decoding_alg n a (sDel X i) = X := 
begin
unfold decoding_alg, rw if_neg, 
  {rw if_pos Hr,
   rw ← sIns_fig_of_pos HX HXn HXa _ Hr,
   rw sDel_sIns_id,
   apply list.sIns_zero_of_num_RIs,
   rw num_RIs_max_num_RIs _ _ Hr,
   apply sub_mod_sDel_of_pos HX HXn HXa _ Hr},
  {apply nat.ne_of_lt, rw length_sDel,
   rw ← HXn, apply nat.sub_lt_self,
    {apply lt_of_lt_of_le (zero_lt_one) HX},
    {apply zero_lt_one}}
end

lemma sDelErr_correctable_of_neg
    {n a : ℕ} {X : list B} (HX : 1 ≤ length X) 
    (HXn : length X = n) (HXa : (ρ X) % (n + 1) = a % (n + 1)) 
    (i : ℕ) (Hr : ¬ sub_mod (n + 1) a (sDel X i) ≤ num_Is (sDel X i)) :
    decoding_alg n a (sDel X i) = X := 
begin
unfold decoding_alg, rw if_neg, 
  {rw if_neg Hr,
   rw ← sIns_fig_of_neg HX HXn HXa _ Hr,
   rw sDel_sIns_id,
   apply list.sIns_one_of_num_LOs,
   rw num_LOs_min_num_LOs,
    {rw sub_mod_sDel_of_neg HX HXn HXa _ Hr, 
     rw add_right_comm, rw nat.add_sub_cancel, 
     rw nat.add_sub_cancel},
    {rw sub_mod_sDel_of_neg HX HXn HXa _ Hr, 
     rw add_right_comm, rw nat.add_sub_cancel, 
     rw nat.add_sub_cancel, apply num_LOs_le_num_Os}},
  {apply nat.ne_of_lt, rw length_sDel,
   rw ← HXn, apply nat.sub_lt_self,
    {apply lt_of_lt_of_le (zero_lt_one) HX},
    {apply zero_lt_one}}
end

lemma sDelErr_correctable
  {n a : ℕ} {X : list B} 
  (HXn : length X = n) (HXa : (ρ X) % (n + 1) = a % (n + 1)) (i : ℕ) :
  decoding_alg n a (sDel X i) = X := 
begin
cases n,
  {unfold decoding_alg, rw if_pos, 
    {rw eq_nil_of_length_eq_zero HXn, rw sDel_nil},
    {rw eq_nil_of_length_eq_zero HXn, 
     rw sDel_nil, unfold length}},
  {cases decidable.em(sub_mod (n + 2) a (sDel X i) ≤ num_Is (sDel X i)) with hle hnle,
    {apply sDelErr_correctable_of_pos _ HXn HXa _ hle,
     rw HXn, apply succ_le_succ (nat.zero_le _)},
    {apply sDelErr_correctable_of_neg _ HXn HXa _ hnle,
     rw HXn, apply succ_le_succ (nat.zero_le _)}},
end

end list 

namespace vector

open vector

def sub_mod (m a : ℕ) (X : vector B n) : ℕ :=
  list.sub_mod m a (to_list X)

lemma sub_mod_zero (m : ℕ) :
    sub_mod m 0 X = (m - (ρ X) % m) % m :=
by {unfold sub_mod, apply list.sub_mod_zero}

lemma sub_mod_mod_self (m : ℕ) :
  sub_mod m m X = sub_mod m 0 X :=
by {unfold sub_mod, apply list.sub_mod_mod_self}

lemma sub_mod_nil (m : ℕ) :
    sub_mod m a vector.nil = a % m :=
by {unfold sub_mod, apply list.sub_mod_nil}

lemma sub_mod_add (m : ℕ) :
  sub_mod m (a + m) X = sub_mod m a X :=
by {unfold sub_mod, apply list.sub_mod_add}

lemma sub_mod_sub (m : ℕ) (H : m ≤ a) :
  sub_mod m (a - m) X = sub_mod m a X :=
by {unfold sub_mod, apply list.sub_mod_sub _ _ _ H}

lemma sub_mod_mod (m : ℕ) :
  sub_mod m (a % m) X = sub_mod m a X :=
by {unfold sub_mod, apply list.sub_mod_mod}

lemma sub_mod_sDel
  {n a : ℕ} {X : vector B n} (H : X ∈ VTCode n a) (i : ℕ) : 
  sub_mod (n + 1) a (sDel X i) = (ρ X) - (ρ sDel X i) :=
begin
unfold sub_mod, apply list.sub_mod_sDel,
  {rw to_list_length},
  {rw mem_VTCode at H, apply H}
end

lemma sub_mod_sDel_of_pos
  {n a : ℕ} {X : vector B (n + 1)} (HX : X ∈ VTCode (n + 1) a) 
  (i : ℕ) (H : sub_mod (n + 2) a (sDel X i) ≤ wt (sDel X i)) : 
  sub_mod (n + 2) a (sDel X i) = num_RIs (sDel X i) i :=
begin
unfold sub_mod, apply list.sub_mod_sDel_of_pos,
  {rw to_list_length, apply succ_le_succ (nat.zero_le _)},
  {rw to_list_length},
  {rw mem_VTCode at HX, apply HX},
  {apply H}
end

lemma sub_mod_sDel_of_neg
  {n a : ℕ} {X : vector B (n + 1)} (HX : X ∈ VTCode (n + 1) a) 
  (i : ℕ) (H : ¬ sub_mod (n + 2) a (sDel X i) ≤ wt (sDel X i)) : 
  sub_mod (n + 2) a (sDel X i) = num_LOs (sDel X i) i + wt (sDel X i) + 1 :=
begin
unfold sub_mod, apply list.sub_mod_sDel_of_neg,
  {rw to_list_length, apply succ_le_succ (nat.zero_le _)},
  {rw to_list_length},
  {rw mem_VTCode at HX, apply HX},
  {apply H}
end

lemma sIns_fig_of_pos
  {n a : ℕ} {c : vector B (n + 1)} (Hc : c ∈ VTCode (n + 1) a) 
  (i : ℕ) (H : sub_mod (n + 2) a (sDel c i) ≤ wt (sDel c i))  :
  sIns (sDel c i) i O = c :=
begin
unfold sIns, unfold sDel, rw subtype.ext,
repeat {rw ← to_list}, repeat {rw to_list_mk}, 
apply @list.sIns_fig_of_pos (n + 1) a (to_list c),
  {rw to_list_length, apply succ_le_succ (nat.zero_le _)},
  {rw to_list_length},
  {rw @mem_VTCode (n + 1) at Hc, apply Hc},
  {apply H}
end

lemma sIns_fig_of_neg
  {n a : ℕ} {c : vector B (n + 1)} (Hc : c ∈ VTCode (n + 1) a) 
  (i : ℕ) (H : ¬ sub_mod (n + 2) a (sDel c i) ≤ wt (sDel c i))  :
  sIns (sDel c i) i I = c :=
begin
unfold sIns, unfold sDel, rw subtype.ext,
repeat {rw ← to_list}, repeat {rw to_list_mk}, 
apply @list.sIns_fig_of_neg (n + 1) a (to_list c),
  {rw to_list_length, apply succ_le_succ (nat.zero_le _)},
  {rw to_list_length},
  {rw @mem_VTCode (n + 1) at Hc, apply Hc},
  {apply H}
end

def min_num_LOs (i : ℕ) : ℕ := 
  list.min_num_LOs (to_list X) i 

lemma min_num_LOs_zero :
  min_num_LOs X 0 = 0 :=
by {unfold min_num_LOs, apply list.min_num_LOs_zero}

lemma num_LOs_min_num_LOs (i : ℕ) (H : i ≤ n - wt X) :
  num_LOs X (min_num_LOs X i) = i :=
begin
unfold min_num_LOs, apply list.num_LOs_min_num_LOs,
rw list.num_Os_eq_len_sub,
rw to_list_length, apply H
end

def max_num_RIs (i : ℕ) : ℕ := 
  list.max_num_RIs (to_list X) i 

lemma max_num_RIs_zero :
  max_num_RIs X 0 = n :=
begin
unfold max_num_RIs, apply eq.trans,
  {apply list.max_num_RIs_zero},
  {rw to_list_length}
end

lemma max_num_RIs_of_num_Is (i : ℕ) (H : wt X + 1 ≤ i) :
  max_num_RIs X i = 0 :=
by {unfold max_num_RIs, apply list.max_num_RIs_of_num_Is _ _ H}


lemma num_RIs_max_num_RIs (i : ℕ) (H : i ≤ wt X) :
  num_RIs X (max_num_RIs X i) = i :=
by {unfold max_num_RIs, apply list.num_RIs_max_num_RIs _ _ H}

def decoding_alg (n a : ℕ) (X : vector B (n - 1)) : vector B n :=
  ⟨list.decoding_alg n a (to_list X), list.length_decoding_alg n a (to_list X) X.2⟩ 

lemma decoding_alg_to_list (n a : ℕ) (X : vector B (n - 1)) : 
  to_list (decoding_alg n a X) = list.decoding_alg n a (to_list X) := rfl

lemma sDelErr_correctable_of_nil
    {a : ℕ} {X : vector B 0} (H : X ∈ VTCode 0 a) (i : ℕ) :
    decoding_alg 0 a (sDel X i) = X := 
begin
rw subtype.ext, repeat {rw ← to_list}, 
rw decoding_alg_to_list, unfold list.decoding_alg, rw if_pos, 
    {rw vector.eq_nil X, rw sDel_nil},
    {rw to_list_length}
end

lemma sDelErr_correctable_of_pos
    {n a : ℕ} {X : vector B (n + 1)} (HX : X ∈ VTCode (n + 1) a) 
    (i : ℕ) (Hr : sub_mod (n + 2) a (sDel X i) ≤ wt (sDel X i)) :
    decoding_alg (n + 1) a (sDel X i) = X := 
begin
rw subtype.ext, repeat {rw ← to_list}, 
rw decoding_alg_to_list,
apply list.sDelErr_correctable_of_pos,
  {rw to_list_length, apply succ_le_succ (nat.zero_le _)},
  {rw to_list_length},
  {rw mem_VTCode at HX, apply HX},
  {apply Hr}
end

lemma sDelErr_correctable_of_neg
    {n a : ℕ} {X : vector B (n + 1)} (HX : X ∈ VTCode (n + 1) a) 
    (i : ℕ) (Hr : ¬ sub_mod (n + 2) a (sDel X i) ≤ wt (sDel X i)) :
    decoding_alg (n + 1) a (sDel X i) = X := 
begin
rw subtype.ext, repeat {rw ← to_list}, 
rw decoding_alg_to_list,
apply list.sDelErr_correctable_of_neg,
  {rw to_list_length, apply succ_le_succ (nat.zero_le _)},
  {rw to_list_length},
  {rw mem_VTCode at HX, apply HX},
  {apply Hr}
end

theorem sDelErr_correctable
  {n a : ℕ} {c : vector B n} 
  (Hc : c ∈ VTCode n a) (i : ℕ) :
  decoding_alg n a (sDel c i) = c :=
begin
cases n,
  {apply sDelErr_correctable_of_nil Hc},
  {cases decidable.em (sub_mod (n + 2) a (sDel c i) ≤ wt (sDel c i)) with hle hnle,
    {apply sDelErr_correctable_of_pos Hc _ hle},
    {apply sDelErr_correctable_of_neg Hc _ hnle}}
end

end vector

end decoding_alg

end set 

namespace finset

open finset vector

def VTCode (n a : ℕ) : finset (vector B n) :=
  filter (set.VTCode n a) univ

lemma mem_VTCode (n a : ℕ) (x : vector B n) :
  x ∈ finset.VTCode n a ↔ x ∈ set.VTCode n a :=
begin
unfold finset.VTCode, rw mem_filter, apply iff.intro,
  {intros h, apply h.right},
  {intros h, apply and.intro (mem_univ _) h}
end

theorem DelCode_VTCode (n a : ℕ) :
  is_DelCode (VTCode n a) :=
begin
intros X Y Xin Yin hneq,
rw mem_VTCode at Xin, rw mem_VTCode at Yin, 
apply subset.antisymm,
  {intros w hw, rw mem_inter at hw, 
   repeat {rw mem_dS at hw},
   have h1 : ∃ i : ℕ, w = sDel X i, from hw.left,
   cases h1 with i h1_i,
   have h2 : ∃ j : ℕ, w = sDel Y j, from hw.right,
   cases h2 with j h2_j,
   have heq : X = Y,
    {rw ← set.decoding_alg.vector.sDelErr_correctable Xin, 
     rw ← set.decoding_alg.vector.sDelErr_correctable Yin,
     rw ← h1_i, rw ← h2_j},
   apply absurd heq hneq},
  {apply set.empty_subset}
end

end finset
