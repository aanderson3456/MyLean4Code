import Snakey.Pentominoes.Basic

-- Formalizing Harary's Tic-Tac-Toe (Polyomino Achievement Game)
-- We strictly adhere to our native `Nat` structural proofs.

/--
The two players in Harary's Tic-Tac-Toe.
Human intuition: 'Maker' (Player 1) tries to build a target polyomino.
'Breaker' (Player 2) tries to block Maker from completing it.
-/
inductive Player
  | Maker
  | Breaker
  deriving DecidableEq, Repr

/--
The board is a mapping from every coordinate to either a Player or nothing.
Human intuition: An infinite piece of grid paper where players take turns
coloring in squares with their respective colors.
-/
def Board := Point → Option Player

/--
Translates a single point by adding the coordinates of an offset point.
Human intuition: Shifting a square right and up across our grid without rotating it.
-/
def translate_point (p : Point) (offset : Point) : Point :=
  (offset.x + p.x, offset.y + p.y)

/--
Translates an entire shape by a given offset.
Human intuition: Moving the entire polyomino rigidly across the board.
We use `List.map` to structurally apply the translation natively.
-/
def translate_shape (s : Shape) (offset : Point) : Shape :=
  s.map (fun p => translate_point p offset)

/--
A player has achieved a specific exact shape if all points in the shape
are claimed by that player on the board.
Human intuition: Checking if every square of the target shape is colored
with the player's color.
-/
def achieves_shape (b : Board) (player : Player) (s : Shape) : Prop :=
  ∀ p, p ∈ (s : List Point) → b p = some player

/--
A player achieves an orientation of a polyomino if there exists some
translation offset such that all points in the translated shape are claimed.
Human intuition: You can place the polyomino anywhere on the board,
so we just need to find at least one valid shifting offset where Maker wins.
-/
def achieves_orientation (b : Board) (player : Player) (s : Shape) : Prop :=
  ∃ offset : Point, achieves_shape b player (translate_shape s offset)

/--
Because Harary's Tic-Tac-Toe allows rotation and reflection, a full Polyomino
is represented as a list of valid Shape orientations.
Human intuition: A polyomino puzzle piece can be spun around or flipped over.
We represent this natively as a finite list of up to 8 distinct shapes.
-/
abbrev Polyomino := List Shape

/--
A player achieves a Polyomino if they achieve ANY of its valid orientations.
Human intuition: Winning the game means building the target shape in ANY
valid rotation or reflection anywhere on the board.
-/
def achieves_polyomino (b : Board) (player : Player) (poly : Polyomino) : Prop :=
  ∃ s, s ∈ (poly : List Shape) ∧ achieves_orientation b player s

/--
A completely empty board.
Human intuition: A fresh sheet of grid paper before the game starts.
-/
def empty_board : Board :=
  fun _ => none

/--
A modular sub-lemma proving that an empty board contains no achieved shapes
for any shape with at least one block.
Human intuition: If no one has played, no one can have built a shape.
-/
theorem empty_board_no_achievement (player : Player) (p : Point) (rest : Shape) :
    ¬ achieves_shape empty_board player (p :: rest) :=
by {
  intro h
  -- The hypothesis h says that every point in (p :: rest) is colored by `player`
  -- We specialize it to our first point `p`.
  have h_p : empty_board p = some player := h p (List.Mem.head rest)
  -- But empty_board is unconditionally `none`, so this is a contradiction.
  contradiction
}
