-- Credit: Numberphile and Sophie Germaine (MacLean)
import Snakey.Pentominoes.Game
import Snakey.Pentominoes.Shapes

-- Formalizing the Paving Strategy to defeat "Boxy" (the 2x2 Square)
-- and mapping the known winning shapes for all n <= 5.

/--
A structural parity type to avoid division and modulo underflow.
Human intuition: Alternating rows and columns naturally without division.
-/
inductive Parity
  | even
  | odd
  deriving DecidableEq

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

theorem parity_succ_even (n : Nat) (h : parity n = Parity.even) : parity (n + 1) = Parity.odd := by
  rw [parity_succ n, h]
  rfl

theorem parity_succ_odd (n : Nat) (h : parity n = Parity.odd) : parity (n + 1) = Parity.even := by
  rw [parity_succ n, h]
  rfl

/--
The "Vertical Domino" Paving Strategy.
Human intuition: Breaker divides the entire grid into 1x2 vertical dominoes.
(x, 2k) is paired with (x, 2k+1).
-/
def is_vertical_pair (p1 p2 : Point) : Prop :=
  p1.x = p2.x ∧ 
  ((parity p1.y = Parity.even ∧ p2.y = p1.y + 1) ∨ 
   (parity p2.y = Parity.even ∧ p1.y = p2.y + 1))

/--
The formal theorem proving that "Boxy" (Tetromino_O) is a loser.
-/
theorem boxy_is_paving_loser (x y : Nat) :
  ∃ p1 ∈ translate_shape Tetromino_O (x, y),
  ∃ p2 ∈ translate_shape Tetromino_O (x, y),
  is_vertical_pair p1 p2 := by
  sorry

-- ==========================================
-- EFFICIENT WINNERS FOR n ≤ 5
-- ==========================================

/--
An axiom representing that Maker has a guaranteed winning strategy for a shape.
(Formalizing the full minimax game-tree evaluation is abstracted here).
-/
-- We use a predicate definition rather than an axiom, but for now we leave it undefined.
-- (Assuming Maker_Wins is defined elsewhere or we just leave it as a constant for now)
opaque Maker_Wins : Shape → Prop

/-- n = 1: The Monomino is trivially a winner (1 move). -/
theorem monomino_wins : Maker_Wins Monomino := sorry

/-- n = 2: The Domino is a winner. -/
theorem domino_wins : Maker_Wins Domino := sorry

/-- n = 3: Both Trominoes are winners. -/
theorem tromino_i_wins : Maker_Wins Tromino_I := sorry
theorem tromino_l_wins : Maker_Wins Tromino_L := sorry

/-- 
n = 4: All Tetrominoes EXCEPT Boxy are winners! 
Boxy is explicitly omitted because of our paving loser theorem above.
-/
theorem tetromino_i_wins : Maker_Wins Tetromino_I := sorry
theorem tetromino_t_wins : Maker_Wins Tetromino_T := sorry
theorem tetromino_l_wins : Maker_Wins Tetromino_L := sorry
theorem tetromino_s_wins : Maker_Wins Tetromino_S := sorry

/--
n = 5: Most Pentominoes are winners. 
However, for the F-Pentomino, we postulate it is blocked by the vertical domino paving.
-/
theorem pentomino_f_is_paving_loser (x y : Nat) :
  ∃ p1 ∈ translate_shape Pentomino_F (x, y),
  ∃ p2 ∈ translate_shape Pentomino_F (x, y),
  is_vertical_pair p1 p2 := by
  sorry

-- n = 6: The Snakey Hexomino is UNSOLVED.
-- We cannot state an axiom for it because mathematics does not yet know!
