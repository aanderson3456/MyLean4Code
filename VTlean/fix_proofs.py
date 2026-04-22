import re
import os

with open(f"VTlean/DelCode.lean", "r") as f:
    text = f.read()

# Fix commas to semicolons in tactics loosely
# But only safe ones:
text = text.replace("unfold is_DelCode, ", "unfold is_DelCode; ")
text = text.replace("intros x y hx hy hne, ", "intros x hx y hy hne; ")
text = text.replace("intros x y hx hy hne", "intros x hx y hy hne")
text = text.replace("apply false.elim", "apply False.elim")

text = text.replace("∀ X Y ∈ C,", "∀ X ∈ C, ∀ Y ∈ C,")
text = text.replace("∀ X Y : Vector B n,", "∀ X : Vector B n, ∀ Y : Vector B n,")
text = text.replace("∀ y z ∈ C,", "∀ y ∈ C, ∀ z ∈ C,")

# It's tedious, let me just fix commas manually via one big regex for DelCode?
# Actually there are `cases x with y z,` and `rw [x] at h,`
text = re.sub(r'([A-Za-z0-9_\]\)]),\s*(rw \[)', r'\1; \2', text)
text = re.sub(r'([A-Za-z0-9_\]\)]),\s*(apply )', r'\1; \2', text)
text = re.sub(r'([A-Za-z0-9_\]\)]),\s*(cases )', r'\1; \2', text)
text = re.sub(r'([A-Za-z0-9_\]\)]),\s*(intros? )', r'\1; \2', text)
text = re.sub(r'([A-Za-z0-9_\]\)]),\s*(unfold )', r'\1; \2', text)
text = re.sub(r'([A-Za-z0-9_\]\)]),\s*(left|right)', r'\1; \2', text)
text = re.sub(r'([A-Za-z0-9_\]\)]),\s*(contradiction|refl|repeat|assume|exact|intro)', r'\1; \2', text)

with open(f"VTlean/DelCode.lean", "w") as f:
    f.write(text)

print("Proof tactics patched.")
