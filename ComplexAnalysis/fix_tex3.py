with open("definitions.tex", "r") as f:
    text = f.read()

config = r"""\lstset{
  literate={×}{{$\times$}}1 {γ}{{$\gamma$}}1 {δ}{{$\delta$}}1 {ε}{{$\varepsilon$}}1 {‖}{{$\|$}}1 {₀}{{$_0$}}1 {ℂ}{{$\mathbb{C}$}}1 {ℕ}{{$\mathbb{N}$}}1 {ℝ}{{$\mathbb{R}$}}1 {→}{{$\to$}}1 {∀}{{$\forall$}}1 {∃}{{$\exists$}}1 {∧}{{$\wedge$}}1 {≤}{{$\le$}}1 {≥}{{$\ge$}}1 {▸}{{$\triangleright$}}1 {⟨}{{$\langle$}}1 {⟩}{{$\rangle$}}1 {≠}{{$\neq$}}1
}"""

import re
text = re.sub(r'\\lstset\{literate=\{₀\}\{\{\$_0\$\}\}1\}', config, text)

with open("definitions.tex", "w") as f:
    f.write(text)
