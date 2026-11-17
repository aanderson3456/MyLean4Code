/-
Copyright (c) 2026 Austin Anderson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Austin Anderson, aided by Gemini
-/
import Mathlib.ModelTheory.Basic
import Mathlib.ModelTheory.Semantics
import Mathlib.ModelTheory.Syntax
import Mathlib.ModelTheory.Satisfiability
import VanEck

open FirstOrder Language
open scoped FirstOrder

/-- The type of functions in our custom first-order language for Van Eck arithmetic. -/
inductive VanEckFunc : ℕ → Type
  | zero : VanEckFunc 0
  | one : VanEckFunc 0
  | succ : VanEckFunc 1
  | add : VanEckFunc 2
  | mul : VanEckFunc 2
  | vanEck : VanEckFunc 1
  deriving DecidableEq

/-- The type of relations in our custom first-order language. -/
inductive VanEckRel : ℕ → Type
  | lt : VanEckRel 2
  deriving DecidableEq

/-- The first-order language of Van Eck arithmetic. -/
def L_VanEck : Language where
  Functions := VanEckFunc
  Relations := VanEckRel

section Terms

variable {β : Type*}

def termZero : L_VanEck.Term β := Term.func .zero ![]
def termOne : L_VanEck.Term β := Term.func .one ![]
def termSucc (t : L_VanEck.Term β) : L_VanEck.Term β := Term.func .succ ![t]
def termAdd (t₁ t₂ : L_VanEck.Term β) : L_VanEck.Term β := Term.func .add ![t₁, t₂]
def termMul (t₁ t₂ : L_VanEck.Term β) : L_VanEck.Term β := Term.func .mul ![t₁, t₂]
def termVanEck (t : L_VanEck.Term β) : L_VanEck.Term β := Term.func .vanEck ![t]

end Terms

section Variables

def var0_1 : L_VanEck.Term (Empty ⊕ Fin 1) := Term.var (Sum.inr 0)

def var0_2 : L_VanEck.Term (Empty ⊕ Fin 2) := Term.var (Sum.inr 0)
def var1_2 : L_VanEck.Term (Empty ⊕ Fin 2) := Term.var (Sum.inr 1)

def var0_3 : L_VanEck.Term (Empty ⊕ Fin 3) := Term.var (Sum.inr 0)
def var1_3 : L_VanEck.Term (Empty ⊕ Fin 3) := Term.var (Sum.inr 1)
def var2_3 : L_VanEck.Term (Empty ⊕ Fin 3) := Term.var (Sum.inr 2)

end Variables

section Axioms

/-- Robinson Axiom 1: ∀ x, succ x ≠ 0 -/
def ax1 : L_VanEck.Sentence :=
  (∼ (termSucc var0_1 =' termZero)).all

/-- Robinson Axiom 2: ∀ x y, succ x = succ y → x = y -/
def ax2 : L_VanEck.Sentence :=
  ((termSucc var0_2 =' termSucc var1_2) ⟹ (var0_2 =' var1_2)).all.all

/-- Robinson Axiom 3: ∀ x, x + 0 = x -/
def ax3 : L_VanEck.Sentence :=
  (termAdd var0_1 termZero =' var0_1).all

/-- Robinson Axiom 4: ∀ x y, x + succ y = succ (x + y) -/
def ax4 : L_VanEck.Sentence :=
  (termAdd var0_2 (termSucc var1_2) =' termSucc (termAdd var0_2 var1_2)).all.all

/-- Robinson Axiom 5: ∀ x, x * 0 = 0 -/
def ax5 : L_VanEck.Sentence :=
  (termMul var0_1 termZero =' termZero).all

/-- Robinson Axiom 6: ∀ x y, x * succ y = x * y + x -/
def ax6 : L_VanEck.Sentence :=
  (termMul var0_2 (termSucc var1_2) =' termAdd (termMul var0_2 var1_2) var0_2).all.all

/-- Robinson Axiom 7: ∀ x y, x < y ↔ ∃ z, x + succ z = y -/
def ax7 : L_VanEck.Sentence :=
  let body : L_VanEck.BoundedFormula Empty 2 :=
    BoundedFormula.rel .lt ![var0_2, var1_2] ⇔
    BoundedFormula.ex (termAdd var0_3 (termSucc var2_3) =' var1_3)
  body.all.all

/-- Van Eck Axiom 1: vanEck(0) = 0 -/
def vE_ax1 : L_VanEck.Sentence :=
  termVanEck termZero =' termZero

/-- Van Eck Axiom 2: ∀ n, (∀ k, k < n → vanEck(k) ≠ vanEck(n)) → vanEck(n + 1) = 0 -/
def vE_ax2 : L_VanEck.Sentence :=
  let premise : L_VanEck.BoundedFormula Empty 2 :=
    BoundedFormula.rel .lt ![var1_2, var0_2] ⟹ ∼ (termVanEck var1_2 =' termVanEck var0_2)
  (premise.all ⟹ (termVanEck (termSucc var0_1) =' termZero)).all

/-- Van Eck Axiom 3: ∀ n k, k < n ∧ vanEck(k) = vanEck(n) ∧
    (∀ j, k < j ∧ j < n → vanEck(j) ≠ vanEck(n)) → vanEck(n + 1) + k = n -/
def vE_ax3 : L_VanEck.Sentence :=
  let cond_j : L_VanEck.BoundedFormula Empty 3 :=
    (BoundedFormula.rel .lt ![var1_3, var2_3] ⊓ BoundedFormula.rel .lt ![var2_3, var0_3]) ⟹
    ∼ (termVanEck var2_3 =' termVanEck var0_3)
  let premise : L_VanEck.BoundedFormula Empty 2 :=
    BoundedFormula.rel .lt ![var1_2, var0_2] ⊓ (termVanEck var1_2 =' termVanEck var0_2) ⊓ cond_j.all
  (premise ⟹ (termAdd (termVanEck (termSucc var0_2)) var1_2 =' var0_2)).all.all

/-- The first-order theory of Van Eck arithmetic over Robinson's Q. -/
def T_VanEck : L_VanEck.Theory :=
  { ax1, ax2, ax3, ax4, ax5, ax6, ax7, vE_ax1, vE_ax2, vE_ax3 }

end Axioms

/-- The standard model structure on the natural numbers. -/
instance natStructure : L_VanEck.Structure ℕ where
  funMap {_} f v := match f with
    | .zero => 0
    | .one => 1
    | .succ => v 0 + 1
    | .add => v 0 + v 1
    | .mul => v 0 * v 1
    | .vanEck => vanEckNthTerm (v 0)
  RelMap {_} r v := match r with
    | .lt => v 0 < v 1

section StandardModel

lemma nat_vE_zero_of_new (n : ℕ) (h : ∀ k < n, vanEckNthTerm k ≠ vanEckNthTerm n) :
    vanEckNthTerm (n + 1) = 0 := by {
  cases n with
  | zero => rfl
  | succ m => exact (vanEck_mth_term_eq_zero_iff_prev_term_new m).mpr h
}

lemma nat_vE_gap_of_last (n k : ℕ) (h_lt : k < n) (h_eq : vanEckNthTerm k = vanEckNthTerm n)
    (h_between : ∀ j, k < j ∧ j < n → vanEckNthTerm j ≠ vanEckNthTerm n) :
    vanEckNthTerm (n + 1) + k = n := by {
  have h_len1 : (vanEck n).length - 1 = n := by {
    have hl := vanEckLength n
    omega
  }
  have h_match : listNth (vanEck n) ((vanEck n).length - 1) = listNth (vanEck n) k := by {
    rw [h_len1]
    have hd_n : listNth (vanEck n) n = vanEckNthTerm n := rfl
    have hd_k : listNth (vanEck n) k = vanEckNthTerm k :=
      VanEck_deterministic n k (Nat.le_of_lt h_lt)
    rw [hd_n, hd_k, h_eq]
  }
  have h_fail : ∀ d, 1 ≤ d → d ≤ n - k - 1 →
      listNth (vanEck n) ((vanEck n).length - 1) ≠ listNth (vanEck n) (k + d) := by {
    intro d hd1 hd_le
    rw [h_len1]
    have hd_n : listNth (vanEck n) n = vanEckNthTerm n := rfl
    have hd_kd : listNth (vanEck n) (k + d) = vanEckNthTerm (k + d) :=
      VanEck_deterministic n (k + d) (by { omega })
    rw [hd_n, hd_kd]
    exact fun hc => h_between (k + d) ⟨by { omega }, by { omega }⟩ hc.symm
  }
  have h_ms := matchSearch_eq_dist (vanEck n) k (n - k - 1) h_match h_fail
  have h_sub : k + (n - k - 1) + 1 = n := by { omega }
  have h_len2 : (vanEck n).length - 1 - k = n - k := by { omega }
  rw [h_sub, h_len2] at h_ms
  have h_gap := vanEck_is_gap (n + 1) (by { omega })
  have h_sub_n : n + 1 - 1 = n := rfl
  rw [h_sub_n, h_ms] at h_gap
  omega
}

lemma nat_models_ax7 : ℕ ⊨ ax7 := by {
  intro x y
  rw [BoundedFormula.realize_iff, BoundedFormula.realize_ex]
  change x < y ↔ ∃ z : ℕ, x + (z + 1) = y
  constructor
  · intro h
    refine ⟨y - x - 1, ?_⟩
    omega
  · rintro ⟨z, hz⟩
    omega
}

lemma nat_models_vE_ax3 : ℕ ⊨ vE_ax3 := by {
  intro n k h_prem
  rw [BoundedFormula.realize_inf, BoundedFormula.realize_inf] at h_prem
  rcases h_prem with ⟨⟨h_lt, h_eq⟩, h_between⟩
  apply nat_vE_gap_of_last n k h_lt h_eq
  intro j hj
  have h_j := h_between j
  rw [BoundedFormula.realize_imp, BoundedFormula.realize_inf] at h_j
  exact h_j hj
}

/-- The standard natural numbers `ℕ` model all 10 axioms of `T_VanEck`. -/
instance nat_models_T_VanEck : ℕ ⊨ T_VanEck := by {
  rw [Theory.model_iff]
  intro φ hφ
  rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · intro x
    change x + 1 ≠ 0
    omega
  · intro x y h
    change x + 1 = y + 1 at h
    change x = y
    omega
  · intro x
    change x + 0 = x
    omega
  · intro x y
    change x + (y + 1) = (x + y) + 1
    omega
  · intro x
    change x * 0 = 0
    exact Nat.mul_zero x
  · intro x y
    change x * (y + 1) = x * y + x
    exact Nat.mul_succ x y
  · exact nat_models_ax7
  · rfl
  · intro n h_new
    exact nat_vE_zero_of_new n h_new
  · exact nat_models_vE_ax3
}

end StandardModel

section NonstandardOptionModel

/-- Successor on `Option ℕ = ℕ ∪ {∞}`, where `none` is the reflexive point `∞`. -/
def optSucc : Option ℕ → Option ℕ
  | some n => some (n + 1)
  | none => none

/-- Addition on `Option ℕ = ℕ ∪ {∞}` with absorbing `∞`. -/
def optAdd : Option ℕ → Option ℕ → Option ℕ
  | some a, some b => some (a + b)
  | _, _ => none

/-- Multiplication on `Option ℕ = ℕ ∪ {∞}` preserving `x * 0 = 0` and `0 * x = 0`. -/
def optMul : Option ℕ → Option ℕ → Option ℕ
  | _, some 0 => some 0
  | some 0, _ => some 0
  | some (a + 1), some (b + 1) => some ((a + 1) * (b + 1))
  | _, _ => none

/-- Van Eck evaluation on `Option ℕ`, extending `vanEckNthTerm` by `vanEck(∞) = 0`. -/
def optVanEck : Option ℕ → Option ℕ
  | some n => some (vanEckNthTerm n)
  | none => some 0

/-- Order relation on `Option ℕ` induced by Robinson's `ax7` (`x < y ↔ ∃ z, x + succ z = y`). -/
def optLt : Option ℕ → Option ℕ → Prop
  | some a, some b => a < b
  | some _, none => True
  | none, some _ => False
  | none, none => True

/-- Robinson's 1-point compactification nonstandard structure on `Option ℕ = ℕ ∪ {∞}`. -/
instance optionNatStructure : L_VanEck.Structure (Option ℕ) where
  funMap {_} f v := match f with
    | .zero => some 0
    | .one => some 1
    | .succ => optSucc (v 0)
    | .add => optAdd (v 0) (v 1)
    | .mul => optMul (v 0) (v 1)
    | .vanEck => optVanEck (v 0)
  RelMap {_} r v := match r with
    | .lt => optLt (v 0) (v 1)

lemma opt_models_ax1_to_ax4 (φ : L_VanEck.Sentence)
    (hφ : φ = ax1 ∨ φ = ax2 ∨ φ = ax3 ∨ φ = ax4) : (Option ℕ) ⊨ φ := by {
  rcases hφ with rfl | rfl | rfl | rfl
  · intro x
    change optSucc x ≠ some 0
    cases x with
    | none => decide
    | some n => simp [optSucc]
  · intro x y h
    change optSucc x = optSucc y at h
    change x = y
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some m => cases h
    | some n =>
      cases y with
      | none => cases h
      | some m =>
        simp only [optSucc, Option.some.injEq] at h
        rw [Nat.succ.inj h]
  · intro x
    change optAdd x (some 0) = x
    cases x with
    | none => rfl
    | some n => simp [optAdd]
  · intro x y
    change optAdd x (optSucc y) = optSucc (optAdd x y)
    cases x with
    | none => cases y <;> rfl
    | some n =>
      cases y with
      | none => rfl
      | some m => simp [optAdd, optSucc, Nat.add_assoc]
}

lemma opt_models_ax5_ax6 (φ : L_VanEck.Sentence)
    (hφ : φ = ax5 ∨ φ = ax6) : (Option ℕ) ⊨ φ := by {
  rcases hφ with rfl | rfl
  · intro x
    change optMul x (some 0) = some 0
    cases x <;> rfl
  · intro x y
    change optMul x (optSucc y) = optAdd (optMul x y) x
    cases x with
    | none =>
      cases y with
      | none => rfl
      | some b => cases b <;> rfl
    | some a =>
      cases a with
      | zero =>
        cases y with
        | none => rfl
        | some b => cases b <;> rfl
      | succ a' =>
        cases y with
        | none => rfl
        | some b =>
          cases b with
          | zero => simp [optMul, optSucc, optAdd]
          | succ b' => simp [optMul, optSucc, optAdd, Nat.mul_succ]
}

lemma opt_models_ax7 : (Option ℕ) ⊨ ax7 := by {
  intro x y
  rw [BoundedFormula.realize_iff, BoundedFormula.realize_ex]
  change optLt x y ↔ ∃ z : Option ℕ, optAdd x (optSucc z) = y
  cases x with
  | none =>
    cases y with
    | none =>
      constructor
      · intro _
        exact ⟨none, rfl⟩
      · intro _
        trivial
    | some b =>
      constructor
      · intro h
        exact False.elim h
      · rintro ⟨z, hz⟩
        cases hz
  | some a =>
    cases y with
    | none =>
      constructor
      · intro _
        exact ⟨none, rfl⟩
      · intro _
        trivial
    | some b =>
      constructor
      · intro h
        change a < b at h
        refine ⟨some (b - a - 1), ?_⟩
        simp only [optSucc, optAdd, Option.some.injEq]
        omega
      · rintro ⟨z, hz⟩
        cases z with
        | none => cases hz
        | some c =>
          simp only [optSucc, optAdd, Option.some.injEq] at hz
          change a < b
          omega
}

lemma opt_models_vE_ax2 : (Option ℕ) ⊨ vE_ax2 := by {
  intro n h_new
  change (∀ k : Option ℕ, optLt k n → optVanEck k ≠ optVanEck n) at h_new
  change optVanEck (optSucc n) = some 0
  cases n with
  | none => rfl
  | some m =>
    simp only [optSucc, optVanEck, Option.some.injEq]
    apply nat_vE_zero_of_new m
    intro k hk
    have hk_opt := h_new (some k) hk
    intro heq
    exact hk_opt (congrArg some heq)
}

lemma opt_models_vE_ax3 : (Option ℕ) ⊨ vE_ax3 := by {
  intro n k h_prem
  rw [BoundedFormula.realize_inf, BoundedFormula.realize_inf] at h_prem
  rcases h_prem with ⟨⟨h_lt, h_eq⟩, h_between⟩
  change optLt k n at h_lt
  change optVanEck k = optVanEck n at h_eq
  change optAdd (optVanEck (optSucc n)) k = n
  cases n with
  | none =>
    cases k with
    | none => rfl
    | some i =>
      exfalso
      have h_inf := h_between none
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_inf] at h_inf
      exact h_inf ⟨trivial, trivial⟩ rfl
  | some m =>
    cases k with
    | none => exact False.elim h_lt
    | some i =>
      simp only [optSucc, optVanEck, optAdd, Option.some.injEq]
      apply nat_vE_gap_of_last m i h_lt (Option.some.inj h_eq)
      intro j hj
      have hj_opt := h_between (some j)
      rw [BoundedFormula.realize_imp, BoundedFormula.realize_inf] at hj_opt
      intro heq
      exact hj_opt hj (congrArg some heq)
}

/-- The nonstandard model `Option ℕ = ℕ ∪ {∞}` satisfies all 10 axioms of `T_VanEck`. -/
instance optionNat_models_T_VanEck : (Option ℕ) ⊨ T_VanEck := by {
  rw [Theory.model_iff]
  intro φ hφ
  rcases hφ with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact opt_models_ax1_to_ax4 ax1 (Or.inl rfl)
  · exact opt_models_ax1_to_ax4 ax2 (Or.inr (Or.inl rfl))
  · exact opt_models_ax1_to_ax4 ax3 (Or.inr (Or.inr (Or.inl rfl)))
  · exact opt_models_ax1_to_ax4 ax4 (Or.inr (Or.inr (Or.inr rfl)))
  · exact opt_models_ax5_ax6 ax5 (Or.inl rfl)
  · exact opt_models_ax5_ax6 ax6 (Or.inr rfl)
  · exact opt_models_ax7
  · rfl
  · exact opt_models_vE_ax2
  · exact opt_models_vE_ax3
}

end NonstandardOptionModel

/-- A sentence is independent (undecidable) from a theory if the theory models neither the sentence
    nor its negation. -/
def Undecidable (T : L_VanEck.Theory) (φ : L_VanEck.Sentence) : Prop :=
  ¬(Theory.ModelsBoundedFormula T φ) ∧ ¬(Theory.ModelsBoundedFormula T φ.not)

/-- The InfiniteTwos conjecture represented as a first-order sentence:
    ∀ N, ∃ m, N < m ∧ vanEck(m) = 2 -/
def InfiniteTwosSentence : L_VanEck.Sentence :=
  let body : L_VanEck.BoundedFormula Empty 2 :=
    BoundedFormula.rel .lt ![var0_2, var1_2] ⊓ (termVanEck var1_2 =' termSucc termOne)
  body.ex.all

/-- The InfiniteEvens conjecture represented as a first-order sentence:
    ∀ N, ∃ m, N < m ∧ vanEck(m) ≠ 0 ∧ ∃ k, (1 + 1) * k = vanEck(m) -/
def InfiniteEvensSentence : L_VanEck.Sentence :=
  let evenWitness : L_VanEck.BoundedFormula Empty 3 :=
    termMul (termSucc termOne) var2_3 =' termVanEck var1_3
  let body : L_VanEck.BoundedFormula Empty 2 :=
    BoundedFormula.rel .lt ![var0_2, var1_2] ⊓
    (∼ (termVanEck var1_2 =' termZero)) ⊓
    evenWitness.ex
  body.ex.all

lemma optionNat_not_models_InfiniteTwos : ¬ ((Option ℕ) ⊨ InfiniteTwosSentence) := by {
  intro h
  have h_inf := h none
  rw [BoundedFormula.realize_ex] at h_inf
  rcases h_inf with ⟨m, hm⟩
  rw [BoundedFormula.realize_inf] at hm
  rcases hm with ⟨hm_lt, hm_eq⟩
  change optLt none m at hm_lt
  change optVanEck m = optSucc (some 1) at hm_eq
  cases m with
  | none => cases hm_eq
  | some k => exact hm_lt
}

/-- Unconditional unprovability of `InfiniteTwosSentence` in `T_VanEck`, witnessed by
    Robinson's 1-point nonstandard model `Option ℕ = ℕ ∪ {∞}`. -/
theorem InfiniteTwos_not_provable_in_T_VanEck :
    ¬ (Theory.ModelsBoundedFormula T_VanEck InfiniteTwosSentence) := by {
  intro h_prov
  have h_real : (Option ℕ) ⊨ InfiniteTwosSentence :=
    Theory.ModelsBoundedFormula.realize_sentence h_prov (Option ℕ)
  exact optionNat_not_models_InfiniteTwos h_real
}

lemma optionNat_not_models_InfiniteEvens : ¬ ((Option ℕ) ⊨ InfiniteEvensSentence) := by {
  intro h
  have h_inf := h none
  rw [BoundedFormula.realize_ex] at h_inf
  rcases h_inf with ⟨m, hm⟩
  rw [BoundedFormula.realize_inf, BoundedFormula.realize_inf] at hm
  rcases hm with ⟨⟨hm_lt, hm_nz⟩, _⟩
  change optLt none m at hm_lt
  change optVanEck m ≠ some 0 at hm_nz
  cases m with
  | none => exact hm_nz rfl
  | some k => exact hm_lt
}

/-- Unconditional unprovability of `InfiniteEvensSentence` in `T_VanEck`, witnessed by
    `Option ℕ = ℕ ∪ {∞}`. -/
theorem InfiniteEvens_not_provable_in_T_VanEck :
    ¬ (Theory.ModelsBoundedFormula T_VanEck InfiniteEvensSentence) := by {
  intro h_prov
  have h_real : (Option ℕ) ⊨ InfiniteEvensSentence :=
    Theory.ModelsBoundedFormula.realize_sentence h_prov (Option ℕ)
  exact optionNat_not_models_InfiniteEvens h_real
}

/-- If `InfiniteTwos` holds in standard `ℕ`, then `T_VanEck` cannot refute `InfiniteTwosSentence`. -/
theorem InfiniteTwos_not_refutable_of_standard
    (h_std : ∀ N, ∃ m > N, vanEckNthTerm m = 2) :
    ¬ (Theory.ModelsBoundedFormula T_VanEck InfiniteTwosSentence.not) := by {
  intro h_ref
  have h_not : ℕ ⊨ InfiniteTwosSentence.not :=
    Theory.ModelsBoundedFormula.realize_sentence h_ref ℕ
  have h_pos : ℕ ⊨ InfiniteTwosSentence := by {
    intro N
    rcases h_std N with ⟨m, hm_gt, hm_eq⟩
    rw [BoundedFormula.realize_ex]
    refine ⟨m, ?_⟩
    rw [BoundedFormula.realize_inf]
    exact ⟨hm_gt, hm_eq⟩
  }
  exact (Sentence.realize_not ℕ).mp h_not h_pos
}

/-- Complete model-theoretic bridge: if `InfiniteTwos` holds in `ℕ`, then `InfiniteTwosSentence`
    is formally undecidable in `T_VanEck` (`ℕ` models `φ`, `Option ℕ` models `¬φ`). -/
theorem InfiniteTwos_undecidable_of_standard
    (h_std : ∀ N, ∃ m > N, vanEckNthTerm m = 2) :
    Undecidable T_VanEck InfiniteTwosSentence := by {
  exact ⟨InfiniteTwos_not_provable_in_T_VanEck, InfiniteTwos_not_refutable_of_standard h_std⟩
}

/-- The conjecture that InfiniteTwos is undecidable in Van Eck arithmetic (`T_VanEck`).
    The unprovability half is discharged unconditionally via `Option ℕ`; the non-refutability
    half reduces directly to standard `InfiniteTwos` over `ℕ`. -/
theorem InfiniteTwos_undecidable : Undecidable T_VanEck InfiniteTwosSentence := by {
  apply InfiniteTwos_undecidable_of_standard
  sorry
}
