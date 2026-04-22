import re
import os

files = ["DelCode.lean", "Optimal.lean", "Optimal_VTCode.lean"]

def process_file(file_name):
    with open(f"Lean3_Source/{file_name}", "r") as f:
        text = f.read()

    # Basic imports
    text = text.replace("import data.fintype .InsDel .B .NumOsNumIs", "import Mathlib.Data.Fintype.Basic\nimport VTlean.InsDel\nimport VTlean.B\nimport VTlean.NumOsNumIs")
    text = text.replace("import .DelCode", "import VTlean.DelCode")
    text = text.replace("import .Optimal .VTCode", "import VTlean.Optimal\nimport VTlean.VTCode")

    # Namespaces
    text = text.replace("namespace nat", "namespace Nat")
    text = text.replace("open nat", "open Nat")
    text = text.replace("namespace list", "namespace List")
    text = text.replace("open list", "open List")
    text = text.replace("namespace vector", "namespace Vector")
    text = text.replace("open vector", "open Vector")
    text = text.replace("namespace finset", "namespace Finset")
    text = text.replace("open finset", "open Finset")
    text = text.replace("variables", "variable")
    text = text.replace("vector ", "Vector ")
    text = text.replace("finset.", "Finset.")
    text = text.replace("finset ", "Finset ")
    text = text.replace("list ", "List ")
    text = text.replace("list.", "List.")
    text = text.replace("decidable_pred ", "DecidablePred ")
    text = text.replace("decidable_eq", "DecidableEq")
    text = text.replace("decidable ", "Decidable ")
    text = text.replace("Decidablepred", "DecidablePred")
    text = text.replace("decidable.em", "Classical.em")
    text = text.replace("apply_instance", "inferInstance")
    text = text.replace("fintype ", "Fintype ")
    
    # Types
    text = text.replace(" : ℕ", " : Nat")
    text = text.replace(" : list ", " : List ")
    text = text.replace(" : vector ", " : Vector ")
    text = text.replace(" : finset ", " : Finset ")
    text = text.replace(" : Prop", " : Prop")

    # dec_trivial
    text = text.replace(":= dec_trivial", ":= by decide")

    # Tactic conventions
    text = re.sub(r'begin\s*', 'by\n  ', text)
    text = re.sub(r'\nend\s*\n', '\n\n', text)
    text = re.sub(r'([ \t]*)\{', r'\1· ', text)
    # Restore actual `{` for sets and configs
    text = text.replace("· ⟨", "{⟨")
    # Actually it's easier to just do targeted regex for tactic blocks
    # Let's revert the `{` replace and do it better
    pass

def process_file_better(file_name):
    with open(f"Lean3_Source/{file_name}", "r") as f:
        text = f.read()

    # Basic imports
    text = text.replace("import data.fintype .InsDel .B .NumOsNumIs", "import Mathlib.Data.Fintype.Basic\nimport VTlean.InsDel\nimport VTlean.B\nimport VTlean.NumOsNumIs")
    text = text.replace("import .DelCode", "import VTlean.DelCode")
    text = text.replace("import .Optimal .VTCode", "import VTlean.Optimal\nimport VTlean.VTCode")

    # Namespaces
    text = text.replace("namespace nat", "namespace Nat")
    text = text.replace("open nat", "open Nat")
    text = text.replace("namespace list", "namespace List")
    text = text.replace("open list", "open List")
    text = text.replace("namespace vector", "namespace Vector")
    text = text.replace("open vector", "open Vector")
    text = text.replace("namespace finset", "namespace Finset")
    text = text.replace("open finset", "open Finset")
    text = text.replace("variables", "variable")
    text = text.replace("vector ", "Vector ")
    text = text.replace("finset.", "Finset.")
    text = text.replace("finset ", "Finset ")
    text = text.replace("list ", "List ")
    text = text.replace("list.", "List.")
    text = text.replace("decidable_pred ", "DecidablePred ")
    text = text.replace("decidable_eq", "DecidableEq")
    text = text.replace("decidable ", "Decidable ")
    text = text.replace("Decidablepred", "DecidablePred")
    text = text.replace("decidable.em", "Classical.em")
    text = text.replace("apply_instance", "inferInstance")
    text = text.replace("fintype ", "Fintype ")
    
    # Types
    text = text.replace(" : ℕ", " : Nat")
    text = text.replace(" : list ", " : List ")
    text = text.replace(" : vector ", " : Vector ")
    text = text.replace(" : finset ", " : Finset ")
    text = text.replace(" : Prop", " : Prop")

    # dec_trivial
    text = text.replace(":= dec_trivial", ":= by decide")

    # Tactic conventions
    text = re.sub(r'begin\s*', 'by\n  ', text)
    text = re.sub(r'\nend\s*\n', '\n\n', text)
    
    # Safely replace '{ tactic }' blocks
    # Lean 3 style: `  {intro x, refl},`
    text = re.sub(r'^([ \t]*)\{([^\{\}]+)\},?$', r'\1· \2', text, flags=re.MULTILINE)
    text = re.sub(r'^([ \t]*)\{([^\{\}]+)\}$', r'\1· \2', text, flags=re.MULTILINE)
    text = re.sub(r'by \{([^\}]+)\}', r'by \1', text)

    # Common tactics
    text = re.sub(r'rw ([a-zA-Z0-9_\.]+)', r'rw [\1]', text)
    text = re.sub(r'rw ← ([a-zA-Z0-9_\.]+)', r'rw [← \1]', text)

    with open(f"VTlean/{file_name}", "w") as f:
        f.write(text)

for file in files:
    process_file_better(file)

print("Translation complete.")
