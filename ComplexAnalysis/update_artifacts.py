import re

with open('/Users/austinanderson/.gemini/antigravity-ide/brain/40f2fd85-39c3-4d6c-a91f-6ca350995a1f/task.md', 'r') as f:
    task = f.read()

task = task.replace("[/] Finalize the core proof of `conformal_implies_holomorphic_II_12`", "[x] Finalize the core proof of `conformal_implies_holomorphic_II_12`")

with open('/Users/austinanderson/.gemini/antigravity-ide/brain/40f2fd85-39c3-4d6c-a91f-6ca350995a1f/task.md', 'w') as f:
    f.write(task)
