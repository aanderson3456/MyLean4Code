import ComplexAnalysis.Sarason.Chapter2

lemma test_deriv_add_const (f : ℝ → ℂ) (c : ℂ) (t : ℝ) :
  deriv (fun t => c + f t) t = deriv f t := by {
  exact deriv_const_add c
}
