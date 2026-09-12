with open("definitions.tex", "r") as f:
    text = f.read()

# Only replace inside \begin{lstlisting} ... \end{lstlisting}
import re
def replace_in_listing(match):
    content = match.group(0)
    content = content.replace("ux0", "ux₀")
    content = content.replace("uy0", "uy₀")
    content = content.replace("vx0", "vx₀")
    content = content.replace("vy0", "vy₀")
    content = content.replace("f'_0", "f'₀")
    content = content.replace("f'0", "f'₀")
    return content

new_text = re.sub(r'\\begin\{lstlisting\}.*?\\end\{lstlisting\}', replace_in_listing, text, flags=re.DOTALL)

with open("definitions.tex", "w") as f:
    f.write(new_text)
