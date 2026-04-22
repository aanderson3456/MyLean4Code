import re

with open("Lean3_Source/InsDel.lean", "r") as f:
    text = f.read()

# basic syntax conversions
text = text.replace("import data.vector .Lemma .B", "import Mathlib.Data.Vector.Basic\nimport Mathlib.Data.Finset.Basic\nimport Mathlib.Data.Fintype.Basic\nimport VTlean.Lemma\nimport VTlean.B\nimport Mathlib.Data.Fintype.EquivFin\n\nopen scoped Classical\n")
text = text.replace("namespace nat", "namespace Nat")
text = text.replace("open nat", "open Nat")
text = text.replace("namespace list", "namespace List")
text = text.replace("open list", "open List")
text = text.replace("namespace vector", "namespace Vector")
text = text.replace("open vector", "open Vector")
text = text.replace("namespace finset", "namespace Finset")
text = text.replace("open finset", "open Finset")
text = text.replace("variables", "variable")
text = text.replace("vector", "Vector")
text = text.replace("list", "List")

# Case matching conventions
text = text.replace("list.length", "List.length")
text = text.replace("list.repeat", "List.repeat")
text = text.replace("vector.nil", "Vector.nil")

# rename types
text = text.replace(" : ℕ", " : Nat")
text = text.replace(" : Prop", " : Prop")
text = text.replace("decidable_eq", "DecidableEq")

text = re.sub(r'begin\s*', 'by {\n  ', text)
text = re.sub(r'\nend\s*', '\n}', text)
text = text.replace("  {", "  · ")
text = text.replace("    {", "    · ")
text = text.replace("      {", "      · ")
text = text.replace("        {", "        · ")

# common tactics
text = re.sub(r'rw ([a-zA-Z0-9_\.]+)', r'rw [\1]', text)
text = re.sub(r'rw ← ([a-zA-Z0-9_\.]+)', r'rw [← \1]', text)

with open("/Users/austinanderson/.gemini/antigravity/brain/3e0fd088-92bf-4860-b67c-c10a8eedf3f8/scratch/InsDel_translated.lean", "w") as f:
    f.write(text)
