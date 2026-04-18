import Mathlib
import AnalysTSP.WeierstrassLimitR2

open Filter Topology Set ManualEuclideanR2

lemma Compact_is_Closed (S : Set (ℝ × ℝ)) (hcpt : ∀ {ι : Type} [Nonempty ι], @IsCompactR2Subcover ι S) : IsClosed S := by
  have hseq : IsCompactR2Seq S := (EqCptSubcoverSeqDefs S).mp (fun {ι} _ => hcpt)
  rw [isClosed_iff_sequence_bounds] -- wait, let's use isClosed_iff_tendsto
  sorry
