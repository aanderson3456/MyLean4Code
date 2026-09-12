with open("definitions.tex", "r") as f:
    text = f.read()

text = text.replace("\\DeclareUnicodeCharacter{2080}{$_0$}\n", "")
text = text.replace("\\begin{document}", "\\lstset{literate={₀}{{$_0$}}1}\n\\begin{document}")

with open("definitions.tex", "w") as f:
    f.write(text)
