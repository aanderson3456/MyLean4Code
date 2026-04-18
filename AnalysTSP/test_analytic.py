import re

with open("AnalyticTSP.lean", "r") as f:
    text = f.read()

old = """lemma Compact_is_Closed (S : Set (ℝ × ℝ)) (hcpt : ∀ {ι : Type} [Nonempty ι], @IsCompactR2Subcover ι S) : IsClosed S := by
  -- Convert custom open-cover to custom sequential compactness
  have h_seq := (EqCptSubcoverSeqDefs S).mp (fun {ι} _ => hcpt)
  -- Mathlib topology equates closure to containment of all sequence limits
  -- (Here we will map to Mathlib's metric sequence closure bounds)
  -- By our custom seq compactness, the sequence has a convergent subsequence
  -- We must now map `ConvergesR2` back to `Tendsto` and trace the subsequence limit equivalence
  sorry"""

new = """lemma Compact_is_Closed (S : Set (ℝ × ℝ)) (hcpt : ∀ {ι : Type} [Nonempty ι], @IsCompactR2Subcover ι S) : IsClosed S := by
  have h_seq := (EqCptSubcoverSeqDefs S).mp (fun {ι} _ => hcpt)
  have h_mathlib_seq : IsSeqCompact S := by
    intro u hu_mem
    rcases h_seq u hu_mem with ⟨L, φ, L_in, mono, conv⟩
    use L, L_in, φ
    refine ⟨mono, ?_⟩
    sorry
  exact h_mathlib_seq.isCompact.isClosed"""

text = text.replace(old, new)
with open("AnalyticTSP_test.lean", "w") as f:
    f.write(text)

