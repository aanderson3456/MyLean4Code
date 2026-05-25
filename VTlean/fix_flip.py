with open("VTlean/NumOsNumIs.lean", "r") as f:
    lines = f.readlines()

new_lines = []
skip = False
for line in lines:
    if "lemma num_Is_flip_eq_num_Os" in line and not skip:
        # First occurrence: skip until the next lemma (num_Os_eq_len_sub)
        skip = True
    if skip and "lemma num_Os_eq_len_sub" in line:
        skip = False
    
    if not skip:
        new_lines.append(line)

with open("VTlean/NumOsNumIs.lean", "w") as f:
    f.writelines(new_lines)
