import Mathlib
import AnalysTSP.WeierstrassLimitR2

open ManualEuclideanR2

-- We define IsOpenR2 with euclideanDist. Mathlib uses Prod.pseudoMetricSpace using sup-norm.
lemma is_open_r2_iff (S : Set (ℝ × ℝ)) : IsOpenR2 S ↔ IsOpen S := by
  sorry

