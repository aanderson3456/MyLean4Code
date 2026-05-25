import re

with open('scratch_numos.lean', 'r') as f:
    scratch_content = f.read()

with open('VTlean/NumOsNumIs.lean', 'r') as f:
    numos_content = f.read()

# Find the end of `end List` in scratch
end_list_scratch = scratch_content.rfind('end List') + len('end List\n')
scratch_part = scratch_content[:end_list_scratch]

# Find the start of `namespace Vector` in NumOsNumIs
ns_vector = numos_content.find('namespace Vector')
vector_part = numos_content[ns_vector:]

with open('VTlean/NumOsNumIs.lean', 'w') as f:
    f.write(scratch_part + '\n' + vector_part)

