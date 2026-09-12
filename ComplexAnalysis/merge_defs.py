import re

with open('old_defs.tex', 'r') as f:
    old_content = f.read()

with open('definitions.tex', 'r') as f:
    new_content = f.read()

# Extract items from old_defs
old_items = {}
for match in re.finditer(r'\\item \\textbf\{\\texttt\{([^}]+)\}\}(.*?)\n', old_content):
    name = match.group(1)
    desc = match.group(2)
    old_items[name] = desc

# Replace in new_content
def replacer(match):
    name = match.group(1)
    if name in old_items:
        return f'\\item \\textbf{{\\texttt{{{name}}}}}{old_items[name]}\n'
    return match.group(0)

merged_content = re.sub(r'\\item \\textbf\{\\texttt\{([^}]+)\}\}\s*\n', replacer, new_content)

with open('definitions.tex', 'w') as f:
    f.write(merged_content)
