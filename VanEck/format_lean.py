import re

with open("LimSup.lean", "r") as f:
    lines = f.readlines()

new_lines = []
in_proof = False
for i, line in enumerate(lines):
    if ":= by" in line:
        line = line.replace(":= by", ":= by {")
        in_proof = True
    elif in_proof and line.strip() == "" and i+1 < len(lines) and (lines[i+1].startswith("lemma ") or lines[i+1].startswith("theorem ") or lines[i+1].startswith("/-- ") or lines[i+1].startswith("def ")):
        new_lines.append("}\n")
        in_proof = False
    new_lines.append(line)

if in_proof:
    new_lines.append("}\n")

with open("LimSup.lean", "w") as f:
    f.writelines(new_lines)
