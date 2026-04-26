import Snakey.Pentominoes.Game
import Snakey.Pentominoes.Shapes

inductive Parity | even | odd deriving DecidableEq

def parity : Nat → Parity
  | 0 => Parity.even
  | 1 => Parity.odd
  | n + 2 => parity n

def flip_parity : Parity → Parity
  | Parity.even => Parity.odd
  | Parity.odd => Parity.even

def parity_succ (n : Nat) : parity (n + 1) = flip_parity (parity n) :=
  match n with
  | 0 => rfl
  | 1 => rfl
  | n + 2 => parity_succ n

lemma parity_succ_even (n : Nat) (h : parity n = Parity.even) : parity (n + 1) = Parity.odd := by
  rw [parity_succ n, h]
  rfl

lemma parity_succ_odd (n : Nat) (h : parity n = Parity.odd) : parity (n + 1) = Parity.even := by
  rw [parity_succ n, h]
  rfl

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
  have hx : parity x = Parity.even ∨ parity x = Parity.odd := by { cases parity x <;> simp }
  have hy : parity y = Parity.even ∨ parity y = Parity.odd := by { cases parity y <;> simp }
  
  cases hx with
  | inl hxe =>
    cases hy with
    | inl hye =>
      exists (x, y)
      dsimp [translate_shape, Tetromino_O, translate_point, List.map, Point.x, Point.y]
      constructor
      · exact List.Mem.head _
      · exists (x + 1, y)
        constructor
        · exact List.Mem.tail _ (List.Mem.head _)
        · dsimp [is_brickwork_pair, Point.x, Point.y]
          simp [hxe, hye]
    | inr hyo =>
      exists (x, y + 1)
      dsimp [translate_shape, Tetromino_O, translate_point, List.map, Point.x, Point.y]
      constructor
      · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      · exists (x + 1, y + 1)
        constructor
        · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        · dsimp [is_brickwork_pair, Point.x, Point.y]
          have h1 := parity_succ_odd y hyo
          simp [h1, hxe]
  | inr hxo =>
    cases hy with
    | inl hye =>
      exists (x, y + 1)
      dsimp [translate_shape, Tetromino_O, translate_point, List.map, Point.x, Point.y]
      constructor
      · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _))
      · exists (x + 1, y + 1)
        constructor
        · exact List.Mem.tail _ (List.Mem.tail _ (List.Mem.tail _ (List.Mem.head _)))
        · dsimp [is_brickwork_pair, Point.x, Point.y]
          have h1 := parity_succ_even y hye
          simp [h1, hxo]
    | inr hyo =>
      exists (x, y)
      dsimp [translate_shape, Tetromino_O, translate_point, List.map, Point.x, Point.y]
      constructor
      · exact List.Mem.head _
      · exists (x + 1, y)
        constructor
        · exact List.Mem.tail _ (List.Mem.head _)
        · dsimp [is_brickwork_pair, Point.x, Point.y]
          simp [hxo, hyo]
}
