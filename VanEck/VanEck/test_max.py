import subprocess

content = """import VanEck.Basic
open Nat

lemma max_value_implies_M_eq_one_aux (n M k : ℕ) (h_bound : ∀ j ≥ n, vanEckNthTerm j ≤ M)
    (hk : k ≥ n + M)
    (h_kM : vanEckNthTerm k = M)
    (h_no_zeros : ∀ j ≥ n, vanEckNthTerm j ≠ 0) : M = 1 := by {
  sorry
}
"""

with open("VanEck/test_max.lean", "w") as f:
    f.write(content)

result = subprocess.run(["lake", "env", "lean", "test_max.lean"], cwd="/Users/austinanderson/GitHub/MyLean4Code/VanEck", capture_output=True, text=True)
print(result.stdout)
print(result.stderr)
