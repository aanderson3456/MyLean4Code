import Mathlib.Data.Real.Basic

#check 2 + 2

def f (x : ℕ) :=
  x + 3

#check f


--conjunction from MathinLean
lemma prac1 (p q : Prop) : p → (p ∨ q) := by {
  intro hp
  left
  exact hp
}

lemma lemmaLogic3 (p q : Prop) : (p → q) ↔ (¬ p ∨ q) := by {
  constructor
  intro hpq
  rcases p with ht --?????

}
