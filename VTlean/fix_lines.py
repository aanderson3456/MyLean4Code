import re

def wrap_line(line, max_len=100):
    if len(line) <= max_len:
        return line
    
    indent = len(line) - len(line.lstrip())
    # If the line contains an assignment, try breaking after :=
    if ' := ' in line:
        parts = line.split(' := ', 1)
        if len(parts[0]) + 4 <= max_len:
            return parts[0] + ' :=\n' + ' ' * (indent + 2) + parts[1]
            
    # Try breaking at logical operators or large spaces
    for sep in [' = ', ' ∪ ', ' ↔ ']:
        if sep in line:
            parts = line.split(sep, 1)
            if len(parts[0]) + len(sep) <= max_len:
                return parts[0] + sep.rstrip() + '\n' + ' ' * (indent + 2) + parts[1].lstrip()
                
    # Break at ')' or ']' if it follows a long sequence
    if '(' in line and len(line) > max_len:
        # custom break
        pass

    return line

with open('VTlean/Cuculiere.lean', 'r') as f:
    lines = f.readlines()

new_lines = []
for i, line in enumerate(lines):
    # Remove unused simp arg
    if "simp only [f0, f1, List.Vector.push, Finset.mem_univ, Finset.mem_image, true_and, true_iff]" in line:
        line = line.replace(", true_iff", "")
    
    # Remove empty lines around comments
    if "max_{k>=0} T(n,k) = A025591(n). -/" in line:
        new_lines.append(line)
        # Skip next line if it's empty
        if i + 1 < len(lines) and lines[i+1].strip() == "":
            lines[i+1] = "\nskip\n" # hack to skip
        continue
    if line == "\nskip\n":
        continue

    # Attempt to wrap
    if len(line) > 100 and not line.strip().startswith('--'):
        # Manual breaks for known long lines
        if 'Finset.card (Finset.filter P (univ.image f0))' in line and 'Finset.card (Finset.filter (fun v => P (f0 v)) univ)' in line:
            line = line.replace(' = Finset.card', ' =\n    Finset.card')
        elif 'Finset.card (Finset.filter P (univ.image f1))' in line and 'Finset.card (Finset.filter (fun v => P (f1 v)) univ)' in line:
            line = line.replace(' = Finset.card', ' =\n    Finset.card')
        elif 'have h_l : l = l.dropLast ++ [l.getLast h_not_empty]' in line:
            line = line.replace(':= (List', ':=\n      (List')
        elif 'Finset.card (Finset.filter' in line and 'cuculiere_get n' in line:
            line = line.replace(' = cuculiere', ' =\n    cuculiere')
        elif 'Finset.filter (fun (x : List.Vector B 0)' in line:
            line = line.replace(' = ∅', ' =\n        ∅')
        elif 'Finset.card (Finset.filter' in line and ' = Finset.card' in line:
            line = line.replace(' = Finset.card', ' =\n              Finset.card')
        elif 'simp only [f0, f1, List.Vector.push, Finset.mem_univ, Finset.mem_image, true_and]' in line:
            line = line.replace('] at', ']\n      at')
        elif 'simp only [f0, f1, List.Vector.push, Finset.mem_univ, Finset.mem_union' in line:
            line = line.replace('Finset.mem_union,', 'Finset.mem_union,\n      ')
        elif 'Finset.filter P univ = (Finset.filter P (univ.image f0))' in line:
            line = line.replace(' ∪ ', ' ∪\n    ')
        elif 'Disjoint (Finset.filter P (univ.image f0))' in line:
            line = line.replace(' (Finset.filter P (univ.image f1))', '\n    (Finset.filter P (univ.image f1))')
        elif 'vector_card_split (n : Nat) (P : List.Vector B (n + 1) → Prop) [DecidablePred P] :' in line:
            line = line.replace(' [DecidablePred P]', '\n    [DecidablePred P]')
        elif 'Finset.card (Finset.filter (fun v => P (List.Vector.push v B.O)) univ)' in line:
            line = line.replace(' +', ' +\n ')
        else:
            line = wrap_line(line)
            
    new_lines.append(line)

with open('VTlean/Cuculiere.lean', 'w') as f:
    f.writelines(new_lines)
