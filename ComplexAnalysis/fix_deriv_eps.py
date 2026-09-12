import re

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

restore_block = """lemma deriv_eps_eq_del (ux uy vx vy : ℝ) (h_cr : ux = vy ∧ uy = -vx) :
  (ux : ℂ) + I * vx = del_eps ux uy vx vy := by {
  unfold del_eps
  apply Complex.ext
  · simp [Complex.mul_re, Complex.add_re, Complex.I_re, Complex.I_im, Complex.sub_re]
    linarith
  · simp [Complex.mul_im, Complex.add_im, Complex.I_re, Complex.I_im, Complex.sub_im]
    linarith
}

"""

content = content.replace("lemma conformal_implies_delBar_zero_of_fderiv", restore_block + "lemma conformal_implies_delBar_zero_of_fderiv")

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
