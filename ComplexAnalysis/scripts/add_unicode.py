import re
with open("definitions.tex", "r") as f:
    text = f.read()

new_lit = r"""\lstset{
  literate={×}{{$\times$}}1 {γ}{{$\gamma$}}1 {δ}{{$\delta$}}1 {ε}{{$\varepsilon$}}1 {‖}{{$\|$}}1 {₀}{{$_0$}}1 {ℂ}{{$\mathbb{C}$}}1 {ℕ}{{$\mathbb{N}$}}1 {ℝ}{{$\mathbb{R}$}}1 {→}{{$\to$}}1 {∀}{{$\forall$}}1 {∃}{{$\exists$}}1 {∧}{{$\wedge$}}1 {≤}{{$\le$}}1 {≥}{{$\ge$}}1 {▸}{{$\triangleright$}}1 {⟨}{{$\langle$}}1 {⟩}{{$\rangle$}}1 {≠}{{$\neq$}}1 {₁}{{$_1$}}1 {₂}{{$_2$}}1 {§}{{\S}}1 {⁻}{{$^-$}}1 {¹}{{$^1$}}1 {·}{{$\cdot$}}1 {ᶜ}{{$^c$}}1 {•}{{$\bullet$}}1 {↔}{{$\leftrightarrow$}}1 {↦}{{$\mapsto$}}1 {←}{{$\leftarrow$}}1
}"""

text = re.sub(r'\\lstset\{.*?\}', new_lit, text, flags=re.DOTALL)
with open("definitions.tex", "w") as f:
    f.write(text)
