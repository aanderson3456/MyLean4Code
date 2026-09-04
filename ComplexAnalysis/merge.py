import re

with open('scratch_chain.lean', 'r') as f:
    scratch_content = f.read()

# We want everything starting from `lemma euclideanDist_nonneg` to the end of `chain_rule_R2`
start_idx = scratch_content.find("lemma euclideanDist_nonneg")
end_idx = scratch_content.find("}", scratch_content.rfind("have h_final_bound")) + 1

lemmas_content = scratch_content[start_idx:end_idx]

with open('ComplexAnalysis/R2.lean', 'r') as f:
    r2_content = f.read()

# We want to replace the `chain_rule_R2` stub in R2.lean with `lemmas_content`
# Find where `lemma chain_rule_R2` starts in R2.lean
replace_start = r2_content.find("lemma chain_rule_R2")
replace_end = r2_content.find("}", replace_start) + 1

new_r2_content = r2_content[:replace_start] + lemmas_content + r2_content[replace_end:]

with open('ComplexAnalysis/R2.lean', 'w') as f:
    f.write(new_r2_content)

print("Merged successfully")
