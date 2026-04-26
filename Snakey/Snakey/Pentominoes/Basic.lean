-- A formal definition of the 2D Coordinate Grid and the Pentomino shapes.
-- We restrict our formalizations strictly to structural Natural number proofs
-- avoiding `omega` and any automated solvers, forcing manual boundary tracking.

/--
A point on a 2D coordinate grid. 
Human intuition: Imagine the standard Cartesian coordinate system,
but restricted to the non-negative quadrant. By using `Nat`, we
avoid all negative underflow errors naturally and ensure all points
lie within a well-defined topological limit.
-/
def Point := Nat × Nat

/--
The 'x' coordinate of our point.
Human intuition: The horizontal distance from the origin. 
This is an explicit accessor to make our subsequent structural proofs
more readable and grounded in geometric intuition.
-/
def Point.x (p : Point) : Nat := p.1

/--
The 'y' coordinate of our point.
Human intuition: The vertical distance from the origin.
Like `Point.x`, this gives a concrete geometric grounding to our
abstract tuple.
-/
def Point.y (p : Point) : Nat := p.2

/--
Two points are contiguous (adjacent) if they share an edge.
Human intuition: On a physical grid paper, two squares are adjacent
if they touch along a flat side. This means they are identical in one
coordinate and differ by exactly 1 unit in the other coordinate.
To avoid subtraction underflow (since we are working with Nat),
we phrase this natively using addition.
-/
def adjacent (p1 p2 : Point) : Prop :=
  (p1.x = p2.x ∧ (p1.y + 1 = p2.y ∨ p2.y + 1 = p1.y)) ∨
  (p1.y = p2.y ∧ (p1.x + 1 = p2.x ∨ p2.x + 1 = p1.x))

/--
A simple, clean modular sub-lemma proving that adjacency is symmetric.
Human intuition: If a physical square A touches square B, 
then square B must touch square A. This spatial relationship is 
fundamentally bi-directional and independent of the order of observation.
We prove this natively using strict structural matching.
-/
theorem adjacent_symm (p1 p2 : Point) : adjacent p1 p2 → adjacent p2 p1 :=
by {
  intro h
  cases h with
  | inl h_y =>
    apply Or.inl
    constructor
    · exact h_y.left.symm
    · cases h_y.right with
      | inl h_y1 => exact Or.inr h_y1
      | inr h_y2 => exact Or.inl h_y2
  | inr h_x =>
    apply Or.inr
    constructor
    · exact h_x.left.symm
    · cases h_x.right with
      | inl h_x1 => exact Or.inr h_x1
      | inr h_x2 => exact Or.inl h_x2
}

/--
A Shape is intuitively a collection of points on our grid.
Human intuition: We use a List to represent this collection. 
This allows us to construct and reason about shapes structurally
by inducting over the list sequentially, mapping perfectly to
finite math bounds without unbounded topological limits.
-/
abbrev Shape := List Point

/--
To be a valid Pentomino, a shape must have exactly 5 blocks.
Human intuition: The prefix "penta-" means five. A pentomino 
is specifically a geometric shape composed of 5 square blocks.
-/
def is_five_blocks (s : Shape) : Prop :=
  s.length = 5

/--
Checks if a point is adjacent to at least one point in a given shape.
Human intuition: If we have an existing shape, and we want to add 
a new square to it, that new square must touch at least one of the 
existing squares to keep the shape as a single contiguous piece.
-/
def adjacent_to_shape (p : Point) (s : Shape) : Prop :=
  ∃ q, q ∈ (s : List Point) ∧ adjacent p q

/--
A shape is connected if every block touches at least one other block
in a contiguous chain. We define this structurally:
An empty shape is trivially connected. A shape with one block is connected.
For larger shapes, the first block must be adjacent to the rest of the shape,
and the rest of the shape must itself be connected.
Human intuition: Imagine building the pentomino one block at a time.
Each new block you place must snap onto the existing connected piece.
Note that this definition implicitly assumes the list is ordered such
that we can deconstruct it sequentially. For our finite subsets,
defining it this way avoids complex topological graph traversals.
-/
def is_connected : Shape → Prop
  | [] => True
  | [_] => True
  | (p :: rest) => adjacent_to_shape p rest ∧ is_connected rest

/--
A formal definition combining our length and connectedness constraints.
Human intuition: A shape is a valid Pentomino if and only if it 
is exactly 5 blocks large, and all 5 blocks are connected into
a single, unified piece.
-/
def is_pentomino (s : Shape) : Prop :=
  is_five_blocks s ∧ is_connected s
