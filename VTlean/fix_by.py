import re

def main():
    with open('VTlean/CuculiereCombinatorial.lean', 'r') as f:
        content = f.read()

    # We need to replace all `:= by\n` with `:= by {\n` and insert `}` at the end of the block.
    # Finding the end of the block is tricky. Let's just do it manually with regex for each lemma.
    lines = content.split('\n')
    out_lines = []
    
    in_by = False
    by_indent = 0
    
    i = 0
    while i < len(lines):
        line = lines[i]
        
        # Check if the line ends with `:= by`
        if re.search(r':=\s*by\s*$', line):
            out_lines.append(re.sub(r':=\s*by\s*$', ':= by {', line))
            in_by = True
            
            # Find the indentation of the next non-empty line
            j = i + 1
            while j < len(lines) and not lines[j].strip():
                out_lines.append(lines[j])
                j += 1
                
            if j < len(lines):
                by_indent = len(lines[j]) - len(lines[j].lstrip())
            i = j - 1
        elif in_by:
            if not line.strip():
                out_lines.append(line)
            else:
                curr_indent = len(line) - len(line.lstrip())
                # If we encounter a line with indent 0 (like another lemma), the by block ended
                if curr_indent == 0:
                    # Before adding this line, close the by block
                    # But wait, what if there's trailing empty lines? We should insert `}` before them.
                    
                    # Pop empty lines
                    empty_buffer = []
                    while out_lines and not out_lines[-1].strip():
                        empty_buffer.append(out_lines.pop())
                    
                    out_lines.append('}')
                    
                    for emp in reversed(empty_buffer):
                        out_lines.append(emp)
                        
                    in_by = False
                    
                    if re.search(r':=\s*by\s*$', line):
                        out_lines.append(re.sub(r':=\s*by\s*$', ':= by {', line))
                        in_by = True
                    else:
                        out_lines.append(line)
                else:
                    out_lines.append(line)
        else:
            out_lines.append(line)
            
        i += 1
        
    if in_by:
        # Pop empty lines
        empty_buffer = []
        while out_lines and not out_lines[-1].strip():
            empty_buffer.append(out_lines.pop())
        
        out_lines.append('}')
        
        for emp in reversed(empty_buffer):
            out_lines.append(emp)
            
    with open('VTlean/CuculiereCombinatorial.lean', 'w') as f:
        f.write('\n'.join(out_lines))

if __name__ == '__main__':
    main()
