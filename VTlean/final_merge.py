import re

with open('scratch_finset.lean', 'r') as f:
    finset_content = f.read()

with open('VTlean/NumOsNumIs.lean', 'r') as f:
    numos_content = f.read()

# Add import Mathlib.Data.Finset.Basic to NumOsNumIs.lean if not there
if 'import Mathlib.Data.Finset.Basic' not in numos_content:
    numos_content = numos_content.replace('import VTlean.InsDel', 'import VTlean.InsDel\nimport Mathlib.Data.Finset.Basic')

# Extract missing vector lemmas from scratch_finset.lean
# They start from "lemma ne_of_wt_lt" and end before "lemma not_mem_filter_Icc_wt_of_lt"
start_idx = finset_content.find("lemma ne_of_wt_lt")
end_idx = finset_content.find("lemma not_mem_filter_Icc_wt_of_lt")
missing_vector_lemmas = finset_content[start_idx:end_idx]

# Extract finset lemmas
finset_lemmas = finset_content[end_idx:]

# Insert missing vector lemmas into NumOsNumIs.lean
insert_idx = numos_content.find('lemma wt_sDel_le')
numos_content = numos_content[:insert_idx] + missing_vector_lemmas + numos_content[insert_idx:]

# Insert finset lemmas into NumOsNumIs.lean
end_vector_idx = numos_content.find('end Vector')
# we need to add "open Finset B.Finset" before finset_lemmas
finset_section = "\nopen Finset B.Finset\n\n" + finset_lemmas
numos_content = numos_content[:end_vector_idx] + finset_section + "\nend Vector\n"

with open('VTlean/NumOsNumIs.lean', 'w') as f:
    f.write(numos_content)

