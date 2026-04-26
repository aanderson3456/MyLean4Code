import Snakey.Pentominoes.Shapes
import Snakey.Pentominoes.Game

inductive Parity
  | even
  | odd

def parity : Nat → Parity
  | 0 => Parity.even
  | 1 => Parity.odd
  | n + 2 => parity n

lemma parity_succ_even (n : Nat) : parity n = Parity.even → parity (n + 1) = Parity.odd := by sorry
lemma parity_succ_odd (n : Nat) : parity n = Parity.odd → parity (n + 1) = Parity.even := by sorry

def is_brickwork_pair (p1 p2 : Point) : Prop :=
  p1.y = p2.y ∧ p1.x + 1 = p2.x ∧
  match parity p1.y, parity p1.x with
  | Parity.even, Parity.even => True
  | Parity.odd, Parity.odd => True
  | _, _ => False

theorem boxy_is_paving_loser (x y : Nat) :
  ∃ p1 ∈ translate_shape Tetromino_O (x, y),
  ∃ p2 ∈ translate_shape Tetromino_O (x, y),
  is_brickwork_pair p1 p2 :=
by {
  dsimp [translate_shape, Tetromino_O, translate_point, List.map]
  have hx : parity x = Parity.even ∨ parity x = Parity.odd := by sorry
  have hy : parity y = Parity.even ∨ parity y = Parity.odd := by sorry
  
  cases hx with
  | inl hxe =>
    cases hy with
    | inl hye =>
      exists (x, y)
      constructor
      · exact Or.inl rfl
      · exists (x + 1, y)
        constructor
        · exact Or.inr (Or.inl rfl)
        · dsimp [is_brickwork_pair]
          constructor
          · rfl
          · constructor
            · rfl
            · rw [hxe, hye]
              exact trivial
    | inr hyo =>
      exists (x, y + 1)
      constructor
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exists (x + 1, y + 1)
        constructor
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · dsimp [is_brickwork_pair]
          constructor
          · rfl
          · constructor
            · rfl
            · have h1 := parity_succ_odd y hyo
              have h2 := parity_succ_even x hxe
              rw [h1, h2]
              exact trivial
  | inr hxo =>
    cases hy with
    | inl hye =>
      exists (x, y + 1)
      constructor
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exists (x + 1, y + 1)
        constructor
        · exact Or.inr (Or.inr (Or.inr (Or.inl rfl)))
        · dsimp [is_brickwork_pair]
          constructor
          · rfl
          · constructor
            · rfl
            · have h1 := parity_succ_even y hye
              have h2 := parity_succ_odd x hxo
              rw [h1, h2]
              exact trivial
    | inr hyo =>
      exists (x, y)
      constructor
      · exact Or.inl rfl
      · exists (x + 1, y)
        constructor
        · exact Or.inr (Or.inl rfl)
        · dsimp [is_brickwork_pair]
          constructor
          · rfl
          · constructor
            · rfl
            · rw [hxo, hyo]
              exact trivial
}
