import re

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

# 1. Remove ConformalLinearMap_eps
content = re.sub(
    r"def ConformalLinearMap_eps \(ux uy vx vy : ℝ\) \(v : ℂ\) : ℂ :=\n  \(ux \* v.re \+ uy \* v.im\) \+ I \* \(vx \* v.re \+ vy \* v.im\)\n",
    "",
    content
)

# 2. Fix conformal_map_decomp
content = content.replace(
    "ConformalLinearMap_eps ux uy vx vy v = del_eps ux uy vx vy * v + delBar_eps ux uy vx vy * star v := by {\n  unfold ConformalLinearMap_eps del_eps delBar_eps",
    "(ux * v.re + uy * v.im : ℂ) + I * (vx * v.re + vy * v.im : ℂ) = del_eps ux uy vx vy * v + delBar_eps ux uy vx vy * star v := by {\n  unfold del_eps delBar_eps"
)

# 3. Fix path_comp_deriv_R2
content = content.replace(
    "(ConformalLinearMap_eps ux uy vx vy (pathDeriv γ t₀)) t₀ := by {",
    "(((ux * (pathDeriv γ t₀).re + uy * (pathDeriv γ t₀).im : ℝ) : ℂ) + I * ((vx * (pathDeriv γ t₀).re + vy * (pathDeriv γ t₀).im : ℝ) : ℂ)) t₀ := by {"
)
h_simp4_block = """  have h_simp4 : (((ux * (pathDeriv γ t₀).re + uy * (pathDeriv γ t₀).im : ℝ) : ℂ) + I * ((vx * (pathDeriv γ t₀).re + vy * (pathDeriv γ t₀).im : ℝ) : ℂ)) = 
    ConformalLinearMap_eps ux uy vx vy (pathDeriv γ t₀) := by {
    unfold ConformalLinearMap_eps
    push_cast
    ring
  }
  
  rw [h_simp3, h_simp4] at h_iff2"""
content = content.replace(h_simp4_block, "  rw [h_simp3] at h_iff2")

# 4. Remove conformal_linear_of_conformal_eps
conf_lin_block = r"lemma conformal_linear_of_conformal_eps.*?(?=\n\n\n)[\s\S]*?^}"
content = re.sub(conf_lin_block, "", content, flags=re.MULTILINE | re.DOTALL)

# 5. Fix conformal_implies_delBar_zero
old_delbar = """lemma conformal_implies_delBar_zero (ux uy vx vy : ℝ) (h_conf : conformal (ConformalLinearMap_eps ux uy vx vy) 0) :
  delBar_eps ux uy vx vy = 0 := by {
  sorry
}"""
new_delbar = """lemma conformal_implies_delBar_zero_of_fderiv (u v : ℝ × ℝ → ℝ) (ux uy vx vy : ℝ) (z : ℂ)
  (h_diff : HasFDerivAt_R2_eps u v ux uy vx vy (z.re, z.im))
  (h_conf : conformal (fun w => u (w.re, w.im) + I * v (w.re, w.im)) z) :
  delBar_eps ux uy vx vy = 0 := by {
  sorry
}"""
content = content.replace(old_delbar, new_delbar)

# 6. Fix conformal_implies_del_ne_zero
old_del = """lemma conformal_implies_del_ne_zero (ux uy vx vy : ℝ) (h_conf : conformal (ConformalLinearMap_eps ux uy vx vy) 0) :
  del_eps ux uy vx vy ≠ 0 := by {
  sorry
}"""
new_del = """lemma conformal_implies_del_ne_zero_of_fderiv (u v : ℝ × ℝ → ℝ) (ux uy vx vy : ℝ) (z : ℂ)
  (h_diff : HasFDerivAt_R2_eps u v ux uy vx vy (z.re, z.im))
  (h_conf : conformal (fun w => u (w.re, w.im) + I * v (w.re, w.im)) z) :
  del_eps ux uy vx vy ≠ 0 := by {
  sorry
}"""
content = content.replace(old_del, new_del)

# 7. Update conformal_implies_holomorphic_II_12 usages
usage1 = """    have h_L_conf := conformal_linear_of_conformal_eps u v (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) z hz_diff hz_conf
    have h_delBar_zero := conformal_implies_delBar_zero (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) h_L_conf"""
new_usage1 = """    have h_delBar_zero := conformal_implies_delBar_zero_of_fderiv u v (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) z hz_diff hz_conf"""
content = content.replace(usage1, new_usage1)

usage2 = """    have h_L_conf := conformal_linear_of_conformal_eps u v (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) z hz_diff hz_conf
    have h_del_ne_zero := conformal_implies_del_ne_zero (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) h_L_conf
    have h_delBar_zero := conformal_implies_delBar_zero (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) h_L_conf"""
new_usage2 = """    have h_del_ne_zero := conformal_implies_del_ne_zero_of_fderiv u v (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) z hz_diff hz_conf
    have h_delBar_zero := conformal_implies_delBar_zero_of_fderiv u v (ux (z.re, z.im)) (uy (z.re, z.im)) (vx (z.re, z.im)) (vy (z.re, z.im)) z hz_diff hz_conf"""
content = content.replace(usage2, new_usage2)


with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
