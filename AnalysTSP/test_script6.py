import re

with open("WeierstrassLimitR2.lean", "r") as f:
    text = f.read()

# Update LimitSubsetsRtoR2'
old_def = "∀ (x : X), dist x a < δ ∧ x ≠ a → dist (f x) L < ε"
new_def = "∀ (x : X), dist x a < δ ∧ x ≠ a → euclideanDist (f x).val L.val < ε"
text = text.replace(old_def, new_def)

# Update the sorry at 1525
old_sorry = """    -- The Lean dist on Y equals dist on ℝ×ℝ of the values (subtype inherits metric).
    -- On ℝ×ℝ, dist = sup-norm ≤ euclideanDist, so euclideanDist ≤ √2·dist.
    -- We called hcts with ε (not ε/√2) so this is still a sorry until we
    -- either change IsCtsRtoR2 to use euclideanDist or prove the norm equivalence.
    sorry"""
new_sorry = """    -- Since we redefined IsCtsRtoR2 to natively constrain euclideanDist,
    -- the continuity hypothesis directly bounds the sequence projection.
    -- euclideanDist is symmetric, and our terms now match exactly.
    -- Thus `h_fx_close` contains precisely the inequality we need.
    exact h_fx_close"""
text = text.replace(old_sorry, new_sorry)

with open("WeierstrassLimitR2_test4.lean", "w") as f:
    f.write(text)

