import re

with open("VTlean/NumOsNumIs.lean", "r") as f:
    content = f.read()

# Extract the header
header_match = re.search(r'(/-.*?Copyright.*?namespace List\nvariable \(X : List B\)\n\n)', content, re.DOTALL)
header = header_match.group(1) if header_match else ""

# Extract the footer
footer = "end List\n\nnamespace Vector\nvariable {n : Nat}\n"

# Find all blocks (def or lemma)
blocks = {}
block_regex = re.compile(r'((?:def|lemma)\s+([a-zA-Z0-9_]+)[\s\S]*?(?=\n(?:def|lemma|end List|namespace Vector)|$))')
for match in block_regex.finditer(content):
    block_text = match.group(1).strip()
    name = match.group(2)
    blocks[name] = block_text

# Rename some blocks that were renamed in Lean 4
renames = {
    "num_Os_add_num_Is_eq_length": "num_Os_add_num_Is",
    "num_Os_replicate_O": "num_Os_repO",
    "num_Os_replicate_I": "num_Os_repI",
    "num_Is_replicate_O": "num_Is_repO",
    "num_Is_replicate_I": "num_Is_repI"
}

for old_name, new_name in renames.items():
    if old_name in blocks:
        block = blocks[old_name]
        block = block.replace(old_name, new_name)
        blocks[new_name] = block
        del blocks[old_name]

# Define the order for List lemmas
list_order = [
    "num_Os",
    "num_Is",
    "num_Os_cons",
    "num_Os_le_cons",
    "num_Os_cons_le",
    "num_Os_le_length",
    "num_Os_sDel_le",
    "num_Os_sDel_le_length",
    "num_Os_sIns_zero",
    "num_Os_sIns_one",
    "num_Os_le_sIns",
    "num_Os_append",
    "num_Os_repO",
    "num_Os_repI",
    "num_Is_cons",
    "num_Is_le_cons",
    "num_Is_cons_le",
    "num_Is_le_length",
    "num_Is_sDel_le",
    "num_Is_sDel_le_length",
    "num_Is_le_sDel",
    "num_Is_sIns_zero",
    "num_Is_sIns_one",
    "num_Is_le_sIns",
    "num_Is_append",
    "num_Is_repO",
    "num_Is_repI",
    "num_Os_add_num_Is",
    "num_Is_flip",
    "num_LOs",
    "num_LOs_zero",
    "num_LOs_le",
    "num_RIs",
    "num_RIs_zero"
]

# Define the order for Vector lemmas
vector_order = [
    "wt",
    "num_Os", # Vector.num_Os
    "ne_of_wt_lt",
    "ne_of_wt_gt",
    "wt_repO",
    "wt_repI",
    "wt_le_length",
    "wt_sDel_le",
    "wt_le_sDel"
]

# Write to a new file
with open("VTlean/NumOsNumIs.lean", "w") as f:
    f.write(header)
    for name in list_order:
        if name in blocks:
            f.write(blocks[name] + "\n\n")
    
    f.write("end List\n\nnamespace Vector\nvariable {n : Nat}\n\n")
    
    # We rename Vector.num_Is to Vector.wt
    if "num_Is" in blocks:
        block = blocks["num_Is"]
        block = block.replace("num_Is", "wt")
        blocks["wt"] = block
        
    for name in vector_order:
        if name in blocks:
            f.write(blocks[name] + "\n\n")
            
    f.write("end Vector\n")

print("Reordered successfully!")
