import re
import os

lean_files = ["ComplexAnalysis/R2.lean", "ComplexAnalysis/Sarason/Definitions.lean", "ComplexAnalysis/Sarason/Chapter2.lean"]

def_map = {}

# Parse Lean files
for file_path in lean_files:
    if not os.path.exists(file_path):
        print(f"Skipping {file_path}")
        continue
    with open(file_path, "r", encoding="utf-8") as f:
        lines = f.readlines()
        
    in_def = False
    def_name = None
    def_lines = []
    
    for line in lines:
        if line.startswith("def ") or line.startswith("noncomputable def "):
            if in_def and def_name:
                def_map[def_name] = "".join(def_lines).rstrip()
            
            in_def = True
            def_lines = [line]
            
            parts = line.split()
            if parts[0] == "def":
                def_name = parts[1]
            elif parts[0] == "noncomputable" and parts[1] == "def":
                def_name = parts[2]
                
        elif in_def:
            if line.startswith("lemma ") or line.startswith("theorem ") or line.startswith("namespace ") or line.startswith("--") or line.startswith("def ") or line.startswith("noncomputable def ") or (line.strip() == "" and len(def_lines) > 1 and not def_lines[-1].startswith(" ")):
                if line.startswith("lemma ") or line.startswith("theorem ") or line.startswith("namespace ") or line.startswith("def ") or line.startswith("noncomputable def "):
                    def_map[def_name] = "".join(def_lines).rstrip()
                    in_def = False
                    def_name = None
                    if line.startswith("def ") or line.startswith("noncomputable def "):
                        in_def = True
                        def_lines = [line]
                        parts = line.split()
                        if parts[0] == "def":
                            def_name = parts[1]
                        elif parts[0] == "noncomputable" and parts[1] == "def":
                            def_name = parts[2]
                else:
                    def_lines.append(line)
            else:
                def_lines.append(line)
                
    if in_def and def_name:
        def_map[def_name] = "".join(def_lines).rstrip()

# Now update definitions.tex
with open("definitions.tex", "r", encoding="utf-8") as f:
    tex_content = f.read()

unicode_to_latex = {
    '×': '$\\times$', 'γ': '$\\gamma$', 'δ': '$\\delta$', 'ε': '$\\varepsilon$', 
    '‖': '$\\|$', '₀': '$_0$', 'ℂ': '$\\mathbb{C}$', 'ℕ': '$\\mathbb{N}$', 
    'ℝ': '$\\mathbb{R}$', '→': '$\\to$', '∀': '$\\forall$', '∃': '$\\exists$', 
    '∧': '$\\wedge$', '≤': '$\\le$', '≥': '$\\ge$', '▸': '$\\triangleright$', 
    '⟨': '$\\langle$', '⟩': '$\\rangle$', '≠': '$\\neq$', '₁': '$_1$', '₂': '$_2$', 
    '§': '\\S', '⁻': '$^-$', '¹': '$^1$', '·': '$\\cdot$', 'ᶜ': '$^c$', 
    '•': '$\\bullet$', '↔': '$\\leftrightarrow$', '↦': '$\\mapsto$', '←': '$\\leftarrow$',
    'π': '$\\pi$', '∂': '$\\partial$', '∈': '$\\in$', '∘': '$\\circ$', '𝓏': '$z$', '̄': '$\\bar{}$'
}

def escape_lean_code(code):
    for u, l in unicode_to_latex.items():
        code = code.replace(u, l)
    return code

def replace_lstlisting(match):
    block = match.group(0)
    m = re.search(r'def\s+(\w+)', block)
    if not m:
        m = re.search(r'noncomputable\s+def\s+(\w+)', block)
        
    if m:
        name = m.group(1)
        if name in def_map:
            raw_lean = escape_lean_code(def_map[name])
            # also make sure the lstlisting block has mathescape=true
            return f"\\begin{{lstlisting}}[language=Caml, mathescape=true]\n{raw_lean}\n\\end{{lstlisting}}"
            
    # For blocks not in def_map (like theorems), we should still escape unicode to prevent pdflatex from crashing
    # We will just extract the content, escape it, and reconstruct
    content = match.group(0)
    inner = re.search(r'\\begin\{lstlisting\}(?:\[.*?\])?(.*)\\end\{lstlisting\}', content, flags=re.DOTALL)
    if inner:
        escaped_inner = escape_lean_code(inner.group(1))
        # Keep original header but ensure mathescape=true if language is Caml
        header = content[:inner.start(1)]
        if 'mathescape=true' not in header:
            header = header.replace(']', ', mathescape=true]')
        return f"{header}{escaped_inner}\\end{{lstlisting}}"
        
    return escape_lean_code(block)

new_tex_content = re.sub(r'\\begin\{lstlisting\}.*?\\end\{lstlisting\}', replace_lstlisting, tex_content, flags=re.DOTALL)

with open("definitions.tex", "w", encoding="utf-8") as f:
    f.write(new_tex_content)

print("Synchronization complete.")
