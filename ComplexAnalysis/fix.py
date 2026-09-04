with open('ComplexAnalysis/R2.lean', 'r') as f:
    text = f.read()

# Replace the text by splitting at 'end ComplexAnalysis.R2'
parts = text.split('end ComplexAnalysis.R2')
if len(parts) >= 2:
    new_text = parts[0] + parts[1] + '\nend ComplexAnalysis.R2\n'
    with open('ComplexAnalysis/R2.lean', 'w') as f:
        f.write(new_text)
