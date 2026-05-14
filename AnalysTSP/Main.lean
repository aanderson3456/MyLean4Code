/-
Copyright (c) 2026 Austin Anderson and Tony Ou. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Austin Anderson, Tony Ou
Assisted by Gemini (AI assistant)
-/

import Mathlib
import AnalysTSP
import WeierstrassLimitR2
import AnalyticTSP
import HausdorffVariation

open AnalyticTSP
open ManualEuclideanR2

/-!
# Analyst's Traveling Salesman Problem (TSP) Failure

The ultimate goal is to show there exists no rectifiable path
covering ℚ×ℚ ∩ [0,1]×[0,1] in the plane, as an example
of a bounded countable set for which no solution to the
analyst's travelling salesman problem exists. We build
countability of the set from elementary principles and use a
compactness argument.
-/

/--
There exists no rectifiable path covering ℚ×ℚ ∩ [0,1]×[0,1] in the plane,
as an example of a bounded countable set for which no solution to the
analyst's travelling salesman problem exists.
-/
theorem Main_ATSP_Failure :
  ¬ ∃ (S : Set (ℝ × ℝ)) (L : ℝ), IsPathInR2 S ∧ CtsRectifiable S L ∧ UnitRationalSquare ⊆ S := by {
  exact ATSP_Rational_Failure
}
