import Mathlib
import AnalysTSP.WeierstrassLimitR2

open Filter Topology Set ManualEuclideanR2

lemma Compact_is_Closed (S : Set (ℝ × ℝ)) (hcpt : ∀ {ι : Type} [Nonempty ι], @IsCompactR2Subcover ι S) : IsClosed S := by
  have h_seq := (EqCptSubcoverSeqDefs S).mp (fun {ι} _ => hcpt)
  have h_mathlib_seq : IsSeqCompact S := by
    intro u hu_mem
    rcases h_seq u hu_mem with ⟨L, φ, L_in, mono, conv⟩
    use L, L_in, φ
    refine ⟨mono, ?_⟩
    sorry
  exact h_mathlib_seq.isCompact.isClosed
