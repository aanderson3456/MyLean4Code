import os
import glob
import shutil

lakefile = "lakefile.toml"
with open(lakefile, "r") as f:
    content = f.read()

if "roots =" not in content:
    content = content.replace('name = "ComplexAnalysis"\n\n[[lean_exe]]', 'name = "ComplexAnalysis"\nroots = ["ComplexAnalysis", "Basic", "BrennanConjecture", "CauchyRiemann", "R2", "Sarason"]\n\n[[lean_exe]]')
    with open(lakefile, "w") as f:
        f.write(content)

for file in glob.glob("**/*.lean", recursive=True):
    with open(file, "r") as f:
        text = f.read()
    
    new_text = text.replace("import ComplexAnalysis.ComplexAnalysis.", "import ")
    new_text = new_text.replace("import ComplexAnalysis.", "import ")
    
    if new_text != text:
        with open(file, "w") as f:
            f.write(new_text)

src_dir = "ComplexAnalysis"
if os.path.exists(src_dir):
    for item in os.listdir(src_dir):
        if item == ".DS_Store": continue
        src_path = os.path.join(src_dir, item)
        dst_path = os.path.join(".", item)
        if os.path.exists(dst_path):
            if os.path.isdir(dst_path):
                shutil.rmtree(dst_path)
            else:
                os.remove(dst_path)
        shutil.move(src_path, dst_path)
    shutil.rmtree(src_dir)
