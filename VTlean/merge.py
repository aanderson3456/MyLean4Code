import re

with open('VTlean/VTCode.lean', 'r') as f:
    existing = f.read()

with open('VTlean/VTCode_ported.lean', 'r') as f:
    ported = f.read()

# Fix case of namespaces
ported = ported.replace('namespace list', 'namespace List')
ported = ported.replace('end list', 'end List')
ported = ported.replace('namespace vector', 'namespace Vector')
ported = ported.replace('end vector', 'end Vector')
ported = ported.replace('namespace set', 'namespace Set')
ported = ported.replace('end set', 'end Set')
ported = ported.replace('namespace finset', 'namespace Finset')
ported = ported.replace('end finset', 'end Finset')

# Extract List lemmas from ported (lines 56 to 107)
lines = ported.split('\n')
list_lemmas = '\n'.join(lines[55:107])
vector_lemmas = '\n'.join(lines[115:169])
rest = '\n'.join(lines[176:]) # Skip `def VTCode` and `mem_VTCode` which are already in existing

# Merge
new_content = existing.replace('end List', list_lemmas + '\n\nend List')
new_content = new_content.replace('end Vector', vector_lemmas + '\n\nend Vector')
new_content += '\n\n' + rest

with open('VTlean/VTCode.lean', 'w') as f:
    f.write(new_content)
