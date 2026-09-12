import re

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

old_proof = """      have h_deriv := deriv_eps_eq f z h_diff_at"""

new_proof = """      have h_deriv : HasDerivAt_eps f (deriv_eps f z h_diff_at) z := Classical.choose_spec h_diff_at"""

content = content.replace(old_proof, new_proof)

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
