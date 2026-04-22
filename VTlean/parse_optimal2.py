import re

with open('Lean3_Source/Optimal.lean', 'r') as f:
    text3 = f.read()

proofs3 = {}
for match in re.finditer(r'(?:lemma|def|instance|theorem)\s+([^\s\(\{:]+).*?:=\s*(.*?)(?=\n(?:lemma|def|instance|theorem|namespace|end|--)|$)', text3, re.DOTALL):
    name = match.group(1)
    proof = match.group(2).strip()
    proofs3[name] = proof

with open('VTlean/Optimal.lean', 'r') as f:
    text4 = f.read()

# Instead of blindly matching, let's see which Lean 4 definitions are sorry.
sorry_defs = []
for match in re.finditer(r'(?:lemma|def|instance|theorem)\s+([^\s\(\{:]+).*?:=\s*by sorry', text4, re.DOTALL):
    sorry_defs.append(match.group(1))

print(f"Lean 4 sorry defs: {len(sorry_defs)}")
for name in sorry_defs[:5]:
    lean3_name = name
    if name == 'Decidableis_optimal': lean3_name = 'decidable_is_optimal'
    if name == 'Decidableis_optimal' + "'": lean3_name = 'decidable_is_optimal' + "'"
    if name == 'Decidableis_optimal_sub': lean3_name = 'decidable_is_optimal_sub'
    if name == 'Decidableis_optimal_sub' + "'": lean3_name = 'decidable_is_optimal_sub' + "'"
    
    proof = proofs3.get(name, proofs3.get(lean3_name, 'NOT FOUND'))
    print(f"--- {name} ---")
    print(proof)
