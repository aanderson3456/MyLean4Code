import VTlean.B
import VTlean.InsDel
import VTlean.NumOsNumIs

open B Finset

def run_count_O (l : List B) : Nat :=
  match l with
  | [] => 0
  | [B.O] => 1
  | [B.I] => 0
  | B.O :: B.O :: xs => run_count_O (B.O :: xs)
  | B.O :: B.I :: xs => run_count_O (B.I :: xs) + 1
  | B.I :: xs => run_count_O xs

def run_count_I (l : List B) : Nat :=
  match l with
  | [] => 0
  | [B.I] => 1
  | [B.O] => 0
  | B.I :: B.I :: xs => run_count_I (B.I :: xs)
  | B.I :: B.O :: xs => run_count_I (B.O :: xs) + 1
  | B.O :: xs => run_count_I xs

def list_dels_same_wt (l : List B) : Finset (List B) :=
  match l with
  | [] => ∅
  | B.O :: xs => insert xs ( (list_dels_same_wt xs).image (fun ys => B.O :: ys) )
  | B.I :: xs => (list_dels_same_wt xs).image (fun ys => B.I :: ys)

def list_dels_dec_wt (l : List B) : Finset (List B) :=
  match l with
  | [] => ∅
  | B.I :: xs => insert xs ( (list_dels_dec_wt xs).image (fun ys => B.I :: ys) )
  | B.O :: xs => (list_dels_dec_wt xs).image (fun ys => B.O :: ys)

lemma mem_image_cons_O_iff (xs : List B) :
  xs ∈ (list_dels_same_wt xs).image (fun ys => B.O :: ys) ↔ ∃ ys, xs = B.O :: ys := by {
  constructor
  · rintro h
    simp only [mem_image] at h
    rcases h with ⟨ys, _, rfl⟩
    exact ⟨ys, rfl⟩
  · rintro ⟨ys, rfl⟩
    simp only [mem_image]
    use ys
    refine ⟨?_, rfl⟩
    dsimp [list_dels_same_wt]
    exact mem_insert_self ys _
}

lemma mem_image_cons_I_iff (xs : List B) :
  xs ∈ (list_dels_dec_wt xs).image (fun ys => B.I :: ys) ↔ ∃ ys, xs = B.I :: ys := by {
  constructor
  · rintro h
    simp only [mem_image] at h
    rcases h with ⟨ys, _, rfl⟩
    exact ⟨ys, rfl⟩
  · rintro ⟨ys, rfl⟩
    simp only [mem_image]
    use ys
    refine ⟨?_, rfl⟩
    dsimp [list_dels_dec_wt]
    exact mem_insert_self ys _
}

lemma cons_inj_O : Function.Injective (fun (ys : List B) => B.O :: ys) := by {
  intro a b h
  cases h
  rfl
}

lemma cons_inj_I : Function.Injective (fun (ys : List B) => B.I :: ys) := by {
  intro a b h
  cases h
  rfl
}

lemma card_list_dels_same_wt (l : List B) :
  (list_dels_same_wt l).card = run_count_O l := by {
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | I =>
      dsimp [list_dels_same_wt]
      cases xs with
      | nil => rfl
      | cons y ys =>
        dsimp [run_count_O]
        rw [card_image_of_injective _ cons_inj_I]
        exact ih
    | O =>
      dsimp [list_dels_same_wt]
      by_cases h_mem : xs ∈ (list_dels_same_wt xs).image (fun ys => B.O :: ys)
      · rw [Finset.card_insert_of_mem h_mem]
        rw [Finset.card_image_of_injective _ cons_inj_O]
        rw [mem_image_cons_O_iff] at h_mem
        rcases h_mem with ⟨ys, rfl⟩
        dsimp [run_count_O]
        exact ih
      · rw [Finset.card_insert_of_notMem h_mem]
        rw [Finset.card_image_of_injective _ cons_inj_O]
        rw [mem_image_cons_O_iff] at h_mem
        cases xs with
        | nil =>
          dsimp [run_count_O]
          rfl
        | cons y ys =>
          cases y with
          | O =>
            have h_exists : ∃ zs, B.O :: ys = B.O :: zs := ⟨ys, rfl⟩
            contradiction
          | I =>
            dsimp [run_count_O]
            omega
}

lemma card_list_dels_dec_wt (l : List B) :
  (list_dels_dec_wt l).card = run_count_I l := by {
  induction l with
  | nil => rfl
  | cons x xs ih =>
    cases x with
    | O =>
      dsimp [list_dels_dec_wt]
      cases xs with
      | nil => rfl
      | cons y ys =>
        dsimp [run_count_I]
        rw [card_image_of_injective _ cons_inj_O]
        exact ih
    | I =>
      dsimp [list_dels_dec_wt]
      by_cases h_mem : xs ∈ (list_dels_dec_wt xs).image (fun ys => B.I :: ys)
      · rw [Finset.card_insert_of_mem h_mem]
        rw [Finset.card_image_of_injective _ cons_inj_I]
        rw [mem_image_cons_I_iff] at h_mem
        rcases h_mem with ⟨ys, rfl⟩
        dsimp [run_count_I]
        exact ih
      · rw [Finset.card_insert_of_notMem h_mem]
        rw [Finset.card_image_of_injective _ cons_inj_I]
        rw [mem_image_cons_I_iff] at h_mem
        cases xs with
        | nil =>
          dsimp [run_count_I]
          rfl
        | cons y ys =>
          cases y with
          | I =>
            have h_exists : ∃ zs, B.I :: ys = B.I :: zs := ⟨ys, rfl⟩
            contradiction
          | O =>
            dsimp [run_count_I]
            omega
}

lemma mem_list_dels_same_wt (l : List B) (ys : List B) :
  ys ∈ list_dels_same_wt l ↔ ∃ i, i < l.length ∧ ys = _root_.List.sDel l i ∧ List.num_Is ys = List.num_Is l := by {
  induction l generalizing ys with
  | nil =>
    simp [list_dels_same_wt]
  | cons x xs ih =>
    cases x with
    | I =>
      dsimp [list_dels_same_wt, run_count_O]
      simp only [mem_image]
      constructor
      · rintro ⟨zs, hzs, rfl⟩
        have h_xs_ne : xs ≠ [] := by {
          intro h_empty
          subst h_empty
          dsimp [list_dels_same_wt] at hzs
          simp at hzs
        }
        rw [ih zs] at hzs
        rcases hzs with ⟨i, hi, rfl, h_wt⟩
        use i + 1
        refine ⟨by omega, ?_, ?_⟩
        · rw [_root_.List.sDel_cons (H := h_xs_ne)]
        · dsimp [List.num_Is]
          omega
      · rintro ⟨j, hj, heq, h_wt⟩
        cases j with
        | zero =>
          rw [_root_.List.sDel_zero] at heq
          subst heq
          dsimp [List.num_Is] at h_wt
          omega
        | succ i =>
          have h_xs_ne : xs ≠ [] := by { intro h; subst h; simp at hj }
          rw [_root_.List.sDel_cons (H := h_xs_ne)] at heq
          have h_wt' : List.num_Is (_root_.List.sDel xs i) = List.num_Is xs := by {
            rw [heq] at h_wt
            dsimp [List.num_Is] at h_wt
            omega
          }
          use _root_.List.sDel xs i
          refine ⟨?_, heq.symm⟩
          rw [ih]
          refine ⟨i, by omega, rfl, h_wt'⟩
    | O =>
      dsimp [list_dels_same_wt]
      simp only [mem_insert, mem_image]
      constructor
      · rintro (rfl | ⟨zs, hzs, rfl⟩)
        · use 0
          refine ⟨by omega, ?_, ?_⟩
          · rw [_root_.List.sDel_zero]
          · rfl
        · have h_xs_ne : xs ≠ [] := by {
            intro h_empty
            subst h_empty
            dsimp [list_dels_same_wt] at hzs
            simp at hzs
          }
          rw [ih zs] at hzs
          rcases hzs with ⟨i, hi, rfl, h_wt⟩
          use i + 1
          refine ⟨by omega, ?_, ?_⟩
          · rw [_root_.List.sDel_cons (H := h_xs_ne)]
          · dsimp [List.num_Is]
            omega
      · rintro ⟨j, hj, heq, h_wt⟩
        cases j with
        | zero =>
          rw [_root_.List.sDel_zero] at heq
          left; exact heq
        | succ i =>
          have h_xs_ne : xs ≠ [] := by { intro h; subst h; simp at hj }
          rw [_root_.List.sDel_cons (H := h_xs_ne)] at heq
          right
          have h_wt' : List.num_Is (_root_.List.sDel xs i) = List.num_Is xs := by {
            rw [heq] at h_wt
            dsimp [List.num_Is] at h_wt
            omega
          }
          use _root_.List.sDel xs i
          refine ⟨?_, heq.symm⟩
          rw [ih]
          refine ⟨i, by omega, rfl, h_wt'⟩
}

lemma mem_list_dels_dec_wt (l : List B) (ys : List B) :
  ys ∈ list_dels_dec_wt l ↔ ∃ i, i < l.length ∧ ys = _root_.List.sDel l i ∧ List.num_Is ys + 1 = List.num_Is l := by {
  induction l generalizing ys with
  | nil =>
    simp [list_dels_dec_wt]
  | cons x xs ih =>
    cases x with
    | O =>
      dsimp [list_dels_dec_wt]
      simp only [mem_image]
      constructor
      · rintro ⟨zs, hzs, rfl⟩
        have h_xs_ne : xs ≠ [] := by {
          intro h_empty
          subst h_empty
          dsimp [list_dels_dec_wt] at hzs
          simp at hzs
        }
        rw [ih zs] at hzs
        rcases hzs with ⟨i, hi, rfl, h_wt⟩
        use i + 1
        refine ⟨by omega, ?_, ?_⟩
        · rw [_root_.List.sDel_cons (H := h_xs_ne)]
        · dsimp [List.num_Is]
          omega
      · rintro ⟨j, hj, heq, h_wt⟩
        cases j with
        | zero =>
          rw [_root_.List.sDel_zero] at heq
          subst heq
          dsimp [List.num_Is] at h_wt
          omega
        | succ i =>
          have h_xs_ne : xs ≠ [] := by { intro h; subst h; simp at hj }
          rw [_root_.List.sDel_cons (H := h_xs_ne)] at heq
          have h_wt' : List.num_Is (_root_.List.sDel xs i) + 1 = List.num_Is xs := by {
            rw [heq] at h_wt
            dsimp [List.num_Is] at h_wt
            omega
          }
          use _root_.List.sDel xs i
          refine ⟨?_, heq.symm⟩
          rw [ih]
          refine ⟨i, by omega, rfl, h_wt'⟩
    | I =>
      dsimp [list_dels_dec_wt]
      simp only [mem_insert, mem_image]
      constructor
      · rintro (rfl | ⟨zs, hzs, rfl⟩)
        · use 0
          refine ⟨by omega, ?_, ?_⟩
          · rw [_root_.List.sDel_zero]
          · rfl
        · have h_xs_ne : xs ≠ [] := by {
            intro h_empty
            subst h_empty
            dsimp [list_dels_dec_wt] at hzs
            simp at hzs
          }
          rw [ih zs] at hzs
          rcases hzs with ⟨i, hi, rfl, h_wt⟩
          use i + 1
          refine ⟨by omega, ?_, ?_⟩
          · rw [_root_.List.sDel_cons (H := h_xs_ne)]
          · dsimp [List.num_Is]
            omega
      · rintro ⟨j, hj, heq, h_wt⟩
        cases j with
        | zero =>
          rw [_root_.List.sDel_zero] at heq
          left; exact heq
        | succ i =>
          have h_xs_ne : xs ≠ [] := by { intro h; subst h; simp at hj }
          rw [_root_.List.sDel_cons (H := h_xs_ne)] at heq
          right
          have h_wt' : List.num_Is (_root_.List.sDel xs i) + 1 = List.num_Is xs := by {
            rw [heq] at h_wt
            dsimp [List.num_Is] at h_wt
            omega
          }
          use _root_.List.sDel xs i
          refine ⟨?_, heq.symm⟩
          rw [ih]
          refine ⟨i, by omega, rfl, h_wt'⟩
}

lemma num_Is_sDel_eq_iff (X : List B) (i : Nat) (hi : i < X.length) :
  List.num_Is (_root_.List.sDel X i) = List.num_Is X ↔ X.getD i B.O = B.O := by {
  revert i
  induction X with
  | nil =>
    intro i hi
    simp at hi
  | cons x xs ih =>
    intro i hi
    cases i with
    | zero =>
      rw [_root_.List.sDel_zero]
      cases x with
      | O =>
        simp [List.num_Is, List.getD]
      | I =>
        simp [List.num_Is, List.getD]
    | succ k =>
      have h_xs_ne : xs ≠ [] := by { intro h; subst h; simp at hi }
      rw [_root_.List.sDel_cons (H := h_xs_ne)]
      have hi_xs : k < xs.length := by {
        simp only [List.length_cons] at hi
        omega
      }
      cases x with
      | O =>
        dsimp [List.num_Is, List.getD]
        exact ih k hi_xs
      | I =>
        dsimp [List.num_Is, List.getD]
        have h_eq : (List.num_Is (_root_.List.sDel xs k) + 1 = List.num_Is xs + 1) ↔ (List.num_Is (_root_.List.sDel xs k) = List.num_Is xs) := by omega
        rw [h_eq]
        exact ih k hi_xs
}

lemma wt_sDel_eq_wt_iff_deleted_O {n : Nat} (x : List.Vector B n) (i : Nat) (hi : i < n) :
  Vector.wt (List.Vector.sDel x i) = Vector.wt x ↔ x.val.getD i B.O = B.O := by {
  have h_len : x.val.length = n := x.property
  have hi_list : i < x.val.length := h_len.symm ▸ hi
  exact num_Is_sDel_eq_iff x.val i hi_list
}

lemma card_dels_same_wt {n : Nat} (x : List.Vector B (n + 1)) :
  (univ.filter (fun y => y ∈ List.Vector.dS x ∧ Vector.wt y = Vector.wt x)).card = run_count_O x.val := by {
  rw [← card_list_dels_same_wt x.val]
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    rw [Finset.mem_filter] at hy
    rcases hy with ⟨_, hy_ds, hy_wt⟩
    rw [mem_list_dels_same_wt]
    rw [List.Vector.mem_dS] at hy_ds
    rcases hy_ds with ⟨i, hi, rfl⟩
    use i
    have h_len : x.val.length = n + 1 := x.property
    refine ⟨by omega, rfl, hy_wt⟩
  · intro y1 hy1 y2 hy2 heq
    exact Subtype.ext heq
  · intro ys hys
    rw [mem_list_dels_same_wt] at hys
    rcases hys with ⟨i, hi, rfl, h_wt⟩
    have h_len : (_root_.List.sDel x.val i).length = n := by {
      rw [List.length_sDel, x.property]
      rfl
    }
    use ⟨_root_.List.sDel x.val i, h_len⟩
    refine ⟨?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, h_wt⟩
    rw [List.Vector.mem_dS]
    use i
    have h_len2 : x.val.length = n + 1 := x.property
    refine ⟨by omega, rfl⟩
}

lemma card_dels_dec_wt {n : Nat} (x : List.Vector B (n + 1)) :
  (univ.filter (fun y => y ∈ List.Vector.dS x ∧ Vector.wt y + 1 = Vector.wt x)).card = run_count_I x.val := by {
  rw [← card_list_dels_dec_wt x.val]
  apply Finset.card_bij (fun y _ => y.val)
  · intro y hy
    rw [Finset.mem_filter] at hy
    rcases hy with ⟨_, hy_ds, hy_wt⟩
    rw [mem_list_dels_dec_wt]
    rw [List.Vector.mem_dS] at hy_ds
    rcases hy_ds with ⟨i, hi, rfl⟩
    use i
    have h_len : x.val.length = n + 1 := x.property
    refine ⟨by omega, rfl, hy_wt⟩
  · intro y1 hy1 y2 hy2 heq
    exact Subtype.ext heq
  · intro ys hys
    rw [mem_list_dels_dec_wt] at hys
    rcases hys with ⟨i, hi, rfl, h_wt⟩
    have h_len : (_root_.List.sDel x.val i).length = n := by {
      rw [List.length_sDel, x.property]
      rfl
    }
    use ⟨_root_.List.sDel x.val i, h_len⟩
    refine ⟨?_, rfl⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_, h_wt⟩
    rw [List.Vector.mem_dS]
    use i
    have h_len2 : x.val.length = n + 1 := x.property
    refine ⟨by omega, rfl⟩
}
