import re

with open('Lean3_Source/Optimal.lean', 'r') as f:
    text3 = f.read()

# Extract lemmas and their proofs from Lean 3
proofs3 = {}
for match in re.finditer(r'(lemma|def|instance|theorem)\s+([^\s\(\{:]+).*?:=\s*(.*?)\n(?:lemma|def|instance|theorem|namespace|end)', text3, re.DOTALL):
    name = match.group(2)
    proof = match.group(3).strip()
    proofs3[name] = proof

# The final block doesn't have a trailing keyword always
last_match = re.search(r'(lemma|def|instance|theorem)\s+([^\s\(\{:]+).*?:=\s*(.*?)\nend', text3, re.DOTALL)
if last_match:
    proofs3[last_match.group(2)] = last_match.group(3).strip()

print(f"Extracted {len(proofs3)} proofs from Lean 3.")
for k, v in list(proofs3.items())[:5]:
    print(k, v[:30].replace('\n', '\\n'))
