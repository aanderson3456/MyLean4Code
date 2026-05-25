with open("VTlean/NumOsNumIs.lean", "r") as f:
    content = f.read()

with open("list_lemmas.lean", "r") as f:
    lemmas = f.read()

# Insert lemmas before num_Os_add_num_Is
idx = content.find("lemma num_Os_add_num_Is")
if idx != -1:
    content = content[:idx] + lemmas + "\n" + content[idx:]
else:
    print("Could not find num_Os_add_num_Is")

# Rename num_Is_flip to num_Is_flip_eq_num_Os
content = content.replace("lemma num_Is_flip (X : List B) : num_Is (B.List.flip X) = num_Os X := by", "lemma num_Is_flip_eq_num_Os (X : List B) : num_Is (B.List.flip X) = num_Os X := by")

# Insert the missing flip lemmas after num_Is_flip_eq_num_Os
flip_lemmas = """
lemma num_Os_eq_len_sub (X : List B) : num_Os X = X.length - num_Is X := by
  sorry

lemma num_Is_eq_len_sub (X : List B) : num_Is X = X.length - num_Os X := by
  sorry

lemma num_Is_flip (X : List B) : num_Is (B.List.flip X) = X.length - num_Is X := by
  sorry
"""
idx = content.find("def num_LOs")
if idx != -1:
    content = content[:idx] + flip_lemmas + "\n" + content[idx:]
else:
    print("Could not find def num_LOs")

with open("VTlean/NumOsNumIs.lean", "w") as f:
    f.write(content)

