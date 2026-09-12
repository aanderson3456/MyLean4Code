import Mathlib
import ComplexAnalysis.Sarason.Chapter2

lemma test_abs_linarith (c d Q : ℝ) (hc : |Q - c| < |c - d| / 2) (hd : |Q - d| < |c - d| / 2) : False := by {
  have h1 : -( |c - d| / 2 ) < Q - c := (abs_lt.mp hc).1
  have h2 : Q - c < |c - d| / 2 := (abs_lt.mp hc).2
  have h3 : -( |c - d| / 2 ) < Q - d := (abs_lt.mp hd).1
  have h4 : Q - d < |c - d| / 2 := (abs_lt.mp hd).2
  have h5 : d - c < |c - d| := by linarith
  have h6 : c - d < |c - d| := by linarith
  rcases le_total 0 (c - d) with h | h
  · have : |c - d| = c - d := abs_of_nonneg h
    linarith
  · have : |c - d| = -(c - d) := abs_of_nonpos h
    linarith
}
