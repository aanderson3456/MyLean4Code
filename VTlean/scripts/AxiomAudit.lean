import VTlean.Progressive
-- Expected: none of these depend on `sorryAx`.
-- `vt0_is_optimal_perfect` / `perfect_code_card_eq_vt_card` are conditional on
-- the explicit hypothesis `PerfectSizeBridge n` (see AlgebraicFractal.lean).
#print axioms vt0_is_optimal_perfect
#print axioms VTCode_zero_is_max
#print axioms vt_size_eq_sum_T
#print axioms perfect_code_card_eq_vt_card
#check @vt0_is_optimal_perfect
