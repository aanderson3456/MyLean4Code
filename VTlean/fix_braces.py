import re
import os

files = ["DelCode.lean", "Optimal.lean", "Optimal_VTCode.lean"]

for file_name in files:
    with open(f"VTlean/{file_name}", "r") as f:
        text = f.read()

    # Re-translating cleanly from base Lean3_Source is safer since it's just Python string replace!
    pass

def re_process(file_name):
    with open(f"Lean3_Source/{file_name}", "r") as f:
        text = f.read()

    # 1. Imports
    text = text.replace("import data.fintype .InsDel .B .NumOsNumIs", "import Mathlib.Data.Fintype.Basic\nimport VTlean.InsDel\nimport VTlean.B\nimport VTlean.NumOsNumIs")
    text = text.replace("import .DelCode", "import VTlean.DelCode")
    text = text.replace("import .Optimal .VTCode", "import VTlean.Optimal\nimport VTlean.VTCode")

    # 2. Namespace & open
    text = text.replace("namespace nat", "namespace Nat")
    text = text.replace("open nat", "open Nat")
    text = text.replace("namespace list", "namespace List")
    text = text.replace("open list", "open List")
    text = text.replace("namespace vector", "namespace Vector")
    text = text.replace("open vector", "open Vector")
    text = text.replace("namespace finset", "namespace Finset")
    text = text.replace("open finset", "open Finset")
    text = text.replace("B.finset", "")
    text = text.replace("B.Vector", "B")

    # 3. Keywords & Types
    text = text.replace("variables", "variable")
    text = text.replace(" : ℕ", " : Nat")
    text = text.replace(" : list ", " : List ")
    text = text.replace(" : vector ", " : Vector ")
    text = text.replace(" : finset ", " : Finset ")
    text = text.replace(" : Prop", " : Prop")
    text = text.replace("decidable_", "Decidable")
    text = text.replace("Decidableeq", "DecidableEq")
    text = text.replace("Decidablepred", "DecidablePred")
    text = text.replace("decidable.em", "Classical.em")
    text = text.replace("apply_instance", "inferInstance")
    text = text.replace("fintype ", "Fintype ")
    text = text.replace("vector ", "Vector ")
    text = text.replace("finset.", "Finset.")
    text = text.replace("finset ", "Finset ")
    text = text.replace("list ", "List ")
    text = text.replace("list.", "List.")

    text = text.replace(":= dec_trivial", ":= by decide")

    # 4. Tactics
    text = re.sub(r'begin\s*', 'by\n  ', text)
    text = re.sub(r'\nend\s*\n', '\n\n', text)
    
    # 5. `  {tactic}` to `  · tactic` without removing `}` bounds
    # Match lines that *start* with whitespace, then `{`, then non-brace content, then `}`, optionally `,`
    text = re.sub(r'^([ \t]*)\{([^\{\}]+)\},?$', r'\1· \2', text, flags=re.MULTILINE)
    
    # 6. `by {tactic}` to `by tactic`
    text = re.sub(r'by \{([^\}]+)\}', r'by \1', text)

    # 7. Common rw
    text = re.sub(r'rw ([a-zA-Z0-9_\.]+)', r'rw [\1]', text)
    text = re.sub(r'rw ← ([a-zA-Z0-9_\.]+)', r'rw [← \1]', text)

    with open(f"VTlean/{file_name}", "w") as f:
        f.write(text)

for file_name in files:
    re_process(file_name)

print("Redone.")
