import re

with open('scratch_numos.lean', 'r') as f:
    content = f.read()

content = content.replace("change B.I :: sIns X' 0 B.I = B.I :: sIns X' j' B.I", "change B.I :: B.I :: X' = B.I :: sIns X' j' B.I")
content = content.replace("change B.I :: sIns X' i' B.I = B.I :: sIns X' 0 B.I", "change B.I :: sIns X' i' B.I = B.I :: B.I :: X'")
content = content.replace("have h2 : (x::X').length - (i'+1) = X'.length - i' := rfl", "have h2 : (x::X').length - (i'+1) = X'.length - i' := by omega")
content = content.replace("change B.O :: sIns X' 0 B.O = B.O :: sIns X' j' B.O", "change B.O :: B.O :: X' = B.O :: sIns X' j' B.O")
content = content.replace("change B.O :: sIns X' i' B.O = B.O :: sIns X' 0 B.O", "change B.O :: sIns X' i' B.O = B.O :: B.O :: X'")

# Also remove any trailing syntax errors like extra parentheses at the end of the file.
content = re.sub(r'\(.*$', '', content, flags=re.DOTALL)

with open('scratch_numos.lean', 'w') as f:
    f.write(content)
