import re

with open("Lean3_Source/Lemma.lean", "r") as f:
    text = f.read()

# basic syntax conversions
text = text.replace("import data.list.basic data.vector data.finset", "import Mathlib.Data.List.Basic\nimport Mathlib.Data.Vector.Basic\nimport Mathlib.Data.Finset.Basic")
text = text.replace("namespace nat", "namespace Nat")
text = text.replace("open nat", "open Nat")
text = text.replace("namespace list", "namespace List")
text = text.replace("open list", "open List")
text = text.replace("namespace vector", "namespace Vector")
text = text.replace("open vector", "open Vector")
text = text.replace("namespace finset", "namespace Finset")
text = text.replace("open finset", "open Finset")

# Tactic conversions
text = re.sub(r'begin\s*', 'by\n  ', text)
text = re.sub(r'\nend\s*\n', '\n\n', text)
text = text.replace("  {", "  · ")
text = text.replace("    {", "    · ")
text = text.replace("      {", "      · ")
text = text.replace("        {", "        · ")
text = text.replace("}", "")

# rename types
text = text.replace(" : ℕ", " : Nat")
text = text.replace(" : list ", " : List ")
text = text.replace(" : vector ", " : Vector ")
text = text.replace(" : finset ", " : Finset ")
text = text.replace(" : Prop", " : Prop")

# common tactics
text = re.sub(r'rw ([a-zA-Z0-9_\.]+)', r'rw [\1]', text)
text = re.sub(r'rw ← ([a-zA-Z0-9_\.]+)', r'rw [← \1]', text)

with open("VTlean/Lemma.lean", "w") as f:
    f.write(text)
