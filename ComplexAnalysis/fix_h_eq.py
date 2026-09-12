import re

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

old_proof = """      have h_re_eq : (deriv_eps f z h_diff_at).re = ux (z.re, z.im) := by {
        have h_uniq := partial_deriv_unique_x (fun z => (f z).re) (deriv_eps f z h_diff_at).re (ux (z.re, z.im)) z h1 hu_x_z
        exact h_uniq
      }
      have h_im_eq : (deriv_eps f z h_diff_at).im = vx (z.re, z.im) := by {
        have h_uniq := partial_deriv_unique_x (fun z => (f z).im) (deriv_eps f z h_diff_at).im (vx (z.re, z.im)) z h3 hv_x_z
        exact h_uniq
      }"""

new_proof = """      have h_re_eq : (deriv_eps f z h_diff_at).re = ux (z.re, z.im) := by {
        have h_f_re : (fun z => (f z).re) = (fun z => u (z.re, z.im)) := by {
          funext w
          rw [hf w]
          simp
        }
        rw [h_f_re] at h1
        have h_uniq := partial_deriv_unique_x (fun z => u (z.re, z.im)) (deriv_eps f z h_diff_at).re (ux (z.re, z.im)) z h1 hu_x_z
        exact h_uniq
      }
      have h_im_eq : (deriv_eps f z h_diff_at).im = vx (z.re, z.im) := by {
        have h_f_im : (fun z => (f z).im) = (fun z => v (z.re, z.im)) := by {
          funext w
          rw [hf w]
          simp
        }
        rw [h_f_im] at h3
        have h_uniq := partial_deriv_unique_x (fun z => v (z.re, z.im)) (deriv_eps f z h_diff_at).im (vx (z.re, z.im)) z h3 hv_x_z
        exact h_uniq
      }"""

content = content.replace(old_proof, new_proof)

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
