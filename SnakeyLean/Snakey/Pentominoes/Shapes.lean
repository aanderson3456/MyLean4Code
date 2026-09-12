import Snakey.Pentominoes.Basic

-- Formalizing Polyomino shapes sequentially from size 1 up to size 6.
-- We also introduce graph-theoretic definitions for "Grid Snakes"
-- manually mapped via native boolean folds.

/--
A computable version of adjacency.
Human intuition: A mechanical way to check if two squares touch, 
returning a simple True/False boolean instead of a logical Proposition.
-/
def adjacent_bool (p q : Point) : Bool :=
  (p.x == q.x && (p.y + 1 == q.y || q.y + 1 == p.y)) ||
  (p.y == q.y && (p.x + 1 == q.x || q.x + 1 == p.x))

/--
The graph degree of a block inside a shape.
Human intuition: We count exactly how many neighboring blocks touch this specific block.
We use a computable fold to tally up the `adjacent_bool` matches directly.
-/
def degree (p : Point) (s : Shape) : Nat :=
  s.foldl (fun acc q => if adjacent_bool p q then acc + 1 else acc) 0

/--
A shape is a "Grid Snake" (a simple path graph) if:
1. It is exactly one contiguous piece (connected).
2. Exactly two of its blocks are "ends" (degree 1).
3. All other blocks are "body segments" (degree 2).
Human intuition: A snake is a sequence of blocks that never branches 
and never loops back to touch itself. We formulate the body check 
using `+ 2` to avoid Nat subtraction underflows.
-/
def is_grid_snake (s : Shape) : Prop :=
  is_connected s ∧
  (s.filter (fun p => degree p s == 1)).length = 2 ∧
  (s.filter (fun p => degree p s == 2)).length + 2 = s.length


-- ==========================================
-- 1. MONOMINO (Size 1)
-- ==========================================

/--
The single, trivial 1-square shape.
Human intuition: A single dot on the grid.
-/
def Monomino : Shape := [(0, 0)]


-- ==========================================
-- 2. DOMINO (Size 2)
-- ==========================================

/--
The unique 2-square shape.
Human intuition: Two squares placed side-by-side. 
Note: The vertical domino is just a rotated version of this one.
-/
def Domino : Shape := [(0, 0), (1, 0)]


-- ==========================================
-- 3. TROMINOES / "Triminos" (Size 3)
-- ==========================================

/--
The straight Tromino.
Human intuition: Three squares in a straight line.
This trivially satisfies the `is_grid_snake` property.
-/
def Tromino_I : Shape := [(0, 0), (1, 0), (2, 0)]

/--
The L-shaped Tromino.
Human intuition: Three squares forming a right angle.
This is also a valid grid snake!
-/
def Tromino_L : Shape := [(0, 0), (1, 0), (0, 1)]


-- ==========================================
-- 4. TETROMINOES / "Quadrominos" (Size 4)
-- ==========================================

/-- The O-Tetromino (Square block). -/
def Tetromino_O : Shape := [(0, 0), (1, 0), (0, 1), (1, 1)]

/-- The I-Tetromino (Straight line). -/
def Tetromino_I : Shape := [(0, 0), (1, 0), (2, 0), (3, 0)]

/-- The T-Tetromino. -/
def Tetromino_T : Shape := [(0, 0), (1, 0), (2, 0), (1, 1)]

/-- The L-Tetromino. -/
def Tetromino_L : Shape := [(0, 0), (1, 0), (2, 0), (0, 1)]

/-- The S-Tetromino (or Z-Tetromino). -/
def Tetromino_S : Shape := [(0, 0), (1, 0), (1, 1), (2, 1)]


-- ==========================================
-- 5. PENTOMINOES (Size 5)
-- ==========================================

/--
We define one representative Pentomino for the sequence.
The F-Pentomino is famously asymmetric.
Human intuition: A shape composed of 5 blocks, often used in tiling puzzles.
-/
def Pentomino_F : Shape := [(1, 0), (2, 0), (0, 1), (1, 1), (1, 2)]


-- ==========================================
-- 6. THE SNAKEY HEXOMINO (Size 6)
-- ==========================================

/--
The famous "Snakey" Hexomino!
Human intuition: A 6-block shape formed by joining an I-Tetromino and a Domino,
creating a zigzag that resembles a snake. It is mathematically the ONLY 
Hexomino whose winning strategy status in Harary's Tic-Tac-Toe remains UNSOLVED.
-/
def Snakey_Hexomino : Shape :=
  [(0, 0), (1, 0), (1, 1), (1, 2), (1, 3), (2, 3)]

/--
A quick structural validation that our defined Snakey Hexomino
has exactly 6 blocks.
-/
theorem snakey_is_six_blocks : Snakey_Hexomino.length = 6 :=
by {
  rfl
}
