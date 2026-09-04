import sys

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

new_lemma = """
lemma conformal_implies_delBar_zero (ux uy vx vy : ℝ) (h_conf : conformal (ConformalLinearMap_eps ux uy vx vy) 0) :
  delBar_eps ux uy vx vy = 0 := by {
  sorry
}
"""

target = "lemma conformal_implies_del_ne_zero"
content = content.replace(target, new_lemma + "\n" + target)

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
