import re
import os

files = ["DelCode.lean", "Optimal.lean", "Optimal_VTCode.lean"]

for file_name in files:
    with open(f"VTlean/{file_name}", "r") as f:
        text = f.read()

    text = text.replace("vector ", "Vector ")
    text = text.replace("finset.", "Finset.")
    text = text.replace("finset ", "Finset ")
    text = text.replace("list ", "List ")
    text = text.replace("list.", "List.")
    text = text.replace("decidable_pred ", "DecidablePred ")
    text = text.replace("decidable ", "Decidable ")
    text = text.replace("Decidablepred", "DecidablePred")
    text = text.replace("decidable.em", "Classical.em")
    text = text.replace("apply_instance", "inferInstance")
    text = text.replace("rfl", "rfl")
    # Fix the missing commas in struct instantiations
    text = re.sub(r'by · intro s, rw is_DelCode, inferInstance', r'by intro s; rw [is_DelCode]; exact inferInstance', text)
    text = re.sub(r'intro ([a-zA-Z0-9_\.]+) ([a-zA-Z0-9_\.]+)', r'intro \1 \2', text)
    text = text.replace("by {", "by\n  ")
    text = text.replace("}", "")

    with open(f"VTlean/{file_name}", "w") as f:
        f.write(text)

print("Syntax fix complete.")
