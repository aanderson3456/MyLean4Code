import re

with open('VTlean/CuculiereCombinatorial.lean', 'r') as f:
    lines = f.readlines()

new_lines = []
in_by_block = False
base_indent = 0

i = 0
while i < len(lines):
    line = lines[i]
    if not in_by_block:
        match = re.search(r':=\s*by\s*$', line)
        if match:
            new_lines.append(line.rstrip() + ' {\n')
            in_by_block = True
            base_indent = -1
        else:
            new_lines.append(line)
    else:
        # Check if the line is empty or whitespace
        if line.strip() == '':
            new_lines.append(line)
        else:
            indent = len(line) - len(line.lstrip())
            if base_indent == -1:
                base_indent = indent
            
            if indent < base_indent:
                # End of block
                new_lines.append('}\n\n' if not new_lines[-1].strip() else '}\n')
                in_by_block = False
                
                # Re-process the current line
                continue
            else:
                new_lines.append(line)
    i += 1

if in_by_block:
    new_lines.append('}\n')

with open('VTlean/CuculiereCombinatorial.lean', 'w') as f:
    f.writelines(new_lines)
