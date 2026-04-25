with open("LimSup.lean", "r") as f:
    lines = f.readlines()

new_lines = []
in_proof = False
for i, line in enumerate(lines):
    stripped = line.rstrip()
    
    if in_proof:
        # Check if we should end the proof
        if line.startswith("lemma ") or line.startswith("theorem ") or line.startswith("/-- ") or line.startswith("def ") or line.startswith("@"):
            new_lines.append("}\n\n")
            in_proof = False
            
    if (line.startswith("lemma ") or line.startswith("theorem ")) and stripped.endswith(":= by"):
        new_lines.append(stripped + " {\n")
        in_proof = True
    elif in_proof and stripped.endswith(":= by"):
        # Could be an inner := by, we leave it alone.
        new_lines.append(line)
    elif not line.startswith("lemma ") and not line.startswith("theorem ") and ":= by" in stripped and in_proof == False:
        # Check if it's a multi-line lemma/theorem declaration that ends in := by
        if stripped.endswith(":= by"):
            # Check backwards to see if it's part of a lemma/theorem
            is_lemma = False
            for j in range(i-1, max(-1, i-5), -1):
                if lines[j].startswith("lemma ") or lines[j].startswith("theorem "):
                    is_lemma = True
                    break
                if lines[j].strip() == "":
                    break
            if is_lemma:
                new_lines.append(stripped + " {\n")
                in_proof = True
            else:
                new_lines.append(line)
        else:
            new_lines.append(line)
    else:
        new_lines.append(line)

if in_proof:
    new_lines.append("}\n")

# Cleanup empty lines before }
for i in range(len(new_lines) - 1, 0, -1):
    if new_lines[i] == "}\n" and new_lines[i-1].strip() == "":
        new_lines[i-1] = ""

with open("LimSup.lean", "w") as f:
    f.writelines([line for line in new_lines if line is not None])
