with open('MirskyNewman.lean', 'r') as f:
    content = f.read()

# Add open scoped Classical after imports
import_section = "import Mathlib.Tactic.Ring"
new_import = "import Mathlib.Tactic.Ring\n\nopen scoped Classical"
content = content.replace(import_section, new_import, 1)

with open('MirskyNewman.lean', 'w') as f:
    f.write(content)
