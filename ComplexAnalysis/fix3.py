import re

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

old_proof = """  have h_simp4 : (((ux * (pathDeriv γ t₀).re + uy * (pathDeriv γ t₀).im : ℝ) : ℂ) + I * ((vx * (pathDeriv γ t₀).re + vy * (pathDeriv γ t₀).im : ℝ) : ℂ)) = 
    ConformalLinearMap_eps ux uy vx vy (pathDeriv γ t₀) := by {
    unfold ConformalLinearMap_eps
    apply Complex.ext <;> simp
  }"""

new_proof = """  have h_simp4 : (((ux * (pathDeriv γ t₀).re + uy * (pathDeriv γ t₀).im : ℝ) : ℂ) + I * ((vx * (pathDeriv γ t₀).re + vy * (pathDeriv γ t₀).im : ℝ) : ℂ)) = 
    ConformalLinearMap_eps ux uy vx vy (pathDeriv γ t₀) := by {
    unfold ConformalLinearMap_eps
    rfl
  }"""

content = content.replace(old_proof, new_proof)

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
