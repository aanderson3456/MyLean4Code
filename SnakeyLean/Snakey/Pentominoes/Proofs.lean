import Snakey.Pentominoes.Shapes

-- Formal structural proofs verifying that specific polyomino shapes
-- satisfy our graph-theoretic definition of a "Grid Snake".
-- We completely avoid the `omega` tactic and verify paths structurally!

/--
A sub-lemma explicitly verifying that the Domino shape is fully connected.
Human intuition: The two blocks of a domino are indeed touching edge-to-edge.
-/
theorem domino_is_connected : is_connected Domino :=
by {
  -- Domino is structurally [(0, 0), (1, 0)]
  dsimp [Domino, is_connected, adjacent_to_shape]
  constructor
  · -- We prove the first block touches the second block.
    exists (1, 0)
    constructor
    · exact List.Mem.head _
    · dsimp [adjacent]
      apply Or.inr
      constructor
      · rfl
      · apply Or.inl
        rfl
  · -- The remaining 1-block shape is trivially connected.
    exact trivial
}

/--
A complete formal proof that the Domino is a "Grid Snake".
Human intuition: A domino is just a line of 2 blocks, which is the 
simplest possible snake graph (two heads, zero body segments).
-/
theorem domino_is_grid_snake : is_grid_snake Domino :=
by {
  dsimp [is_grid_snake, Domino]
  constructor
  · -- Prove connectedness using our modular sub-lemma.
    exact domino_is_connected
  · -- Prove the degree constraints structurally using our boolean mappings!
    -- This evaluates directly without underflow issues or `omega` limits.
    constructor
    · rfl
    · rfl
}


/--
A sub-lemma explicitly verifying that the straight Tromino is fully connected.
Human intuition: The three blocks are placed in a sequence, touching
edge-to-edge consecutively.
-/
theorem tromino_i_is_connected : is_connected Tromino_I :=
by {
  -- Tromino_I is structurally [(0, 0), (1, 0), (2, 0)]
  dsimp [Tromino_I, is_connected, adjacent_to_shape]
  constructor
  · -- Prove (0,0) touches (1,0)
    exists (1, 0)
    constructor
    · exact List.Mem.head _
    · dsimp [adjacent]
      apply Or.inr
      constructor
      · rfl
      · apply Or.inl
        rfl
  · constructor
    · -- Prove (1,0) touches (2,0)
      exists (2, 0)
      constructor
      · exact List.Mem.head _
      · dsimp [adjacent]
        apply Or.inr
        constructor
        · rfl
        · apply Or.inl
          rfl
    · -- The remaining 1-block shape is trivially connected.
      exact trivial
}

/--
A complete formal proof that the straight Tromino is a "Grid Snake".
Human intuition: A 3-block straight line has exactly 2 ends and 1 body segment.
Our structural equations map this directly to the underlying path graph.
-/
theorem tromino_i_is_grid_snake : is_grid_snake Tromino_I :=
by {
  dsimp [is_grid_snake, Tromino_I]
  constructor
  · -- Prove connectedness using our modular sub-lemma.
    exact tromino_i_is_connected
  · -- Prove the 2 head blocks and 1 body block constraints using rfl!
    constructor
    · rfl
    · rfl
}
