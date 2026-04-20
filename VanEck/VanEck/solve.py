import sys
# simple python generator for lean steps to show distance <= P
lean_code = """import VanEck
open Nat

-- lemma showing distance <= P
"""
with open("VanEck/test_eval.lean", "w") as f:
    f.write(lean_code)
