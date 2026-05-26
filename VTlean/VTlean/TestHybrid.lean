import VTlean.CuculiereCombinatorial
import VTlean.Cuculiere

theorem absolute_optimality (n a : Nat) :
  (Finset.VTCode n a).card ≤ (Finset.VTCode n 0).card := by {
  exact VTCode_zero_is_max n a
}
