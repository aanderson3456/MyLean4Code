import sys

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

cr_lemma = """
lemma cr_of_delBar_zero (ux uy vx vy : ℝ) (h : delBar_eps ux uy vx vy = 0) :
  ux = vy ∧ uy = -vx := by {
  unfold delBar_eps at h
  have h1 : (1 / 2 : ℂ) ≠ 0 := by simp
  have h2 : ((ux - vy : ℝ) : ℂ) + I * (vx + uy : ℝ) = 0 := by {
    have h3 : (1 / 2 : ℂ) * (((ux - vy : ℝ) : ℂ) + I * (vx + uy : ℝ)) = 0 := h
    exact mul_eq_zero.mp h3 |>.resolve_left h1
  }
  have h_re : (((ux - vy : ℝ) : ℂ) + I * (vx + uy : ℝ)).re = 0 := by {
    rw [h2]
    exact rfl
  }
  have h_im : (((ux - vy : ℝ) : ℂ) + I * (vx + uy : ℝ)).im = 0 := by {
    rw [h2]
    exact rfl
  }
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.I_re, Complex.I_im, Complex.ofReal_im] at h_re
  simp only [Complex.add_im, Complex.ofReal_im, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re] at h_im
  have h_re2 : ux - vy = 0 := by linarith
  have h_im2 : vx + uy = 0 := by linarith
  exact ⟨sub_eq_zero.mp h_re2, by linarith⟩
}
"""

target = "lemma deriv_eps_eq_del"
content = content.replace(target, cr_lemma + "\n" + target)

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
