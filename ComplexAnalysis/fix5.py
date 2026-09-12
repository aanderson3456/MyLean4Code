import re

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

old_proof = """  have h_chain := chain_rule_R2 h_diff (fun t => ((γ.extend t).re, (γ.extend t).im)) t₀ (by {
    exact (congrArg (fun w => (w.re, w.im)) h_eq).trans (by simp)
  }) ((pathDeriv γ t₀).re, (pathDeriv γ t₀).im) hγ_diff_R2"""

new_proof = """  have h_chain := chain_rule_R2 h_diff (fun t => ((γ.extend t).re, (γ.extend t).im)) t₀ (by {
    exact congrArg (fun w => (w.re, w.im)) h_eq
  }) ((pathDeriv γ t₀).re, (pathDeriv γ t₀).im) hγ_diff_R2"""

content = content.replace(old_proof, new_proof)

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
