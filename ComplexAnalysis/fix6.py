import re

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

old_proof = """      have h_re_eq : (deriv_eps f z h_diff_at).re = ux (z.re, z.im) := by {
        sorry
      }
      have h_im_eq : (deriv_eps f z h_diff_at).im = vx (z.re, z.im) := by {
        sorry
      }
      apply Complex.ext
      · exact h_re_eq
      · exact h_im_eq"""

new_proof = """      have h_re_eq : (deriv_eps f z h_diff_at).re = ux (z.re, z.im) := by {
        sorry
      }
      have h_im_eq : (deriv_eps f z h_diff_at).im = vx (z.re, z.im) := by {
        sorry
      }
      apply Complex.ext
      · simp [h_re_eq]
      · simp [h_im_eq]"""

content = content.replace(old_proof, new_proof)

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
