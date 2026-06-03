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

/-- The complete first-order theory of Van Eck arithmetic. -/
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

/-- The conjecture that InfiniteTwos is undecidable in Van Eck arithmetic. -/
theorem InfiniteTwos_undecidable : Undecidable T_VanEck InfiniteTwosSentence := by {
  sorry
}
