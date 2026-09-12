import re

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

start_idx = content.find("lemma path_comp_deriv_R2")
end_idx = content.find("}", start_idx) + 1

old_lemma = content[start_idx:end_idx]

new_lemma = """lemma path_comp_deriv_R2 (u v : ℝ × ℝ → ℝ) (ux uy vx vy : ℝ) (z : ℂ)
  (h_diff : HasFDerivAt_R2_eps u v ux uy vx vy (z.re, z.im))
  {x y : ℂ} (γ : path_in_C x y) (t₀ : ℝ) (h_eq : γ.extend t₀ = z)
  (hγ_diff : HasDerivAt_R_to_C_eps (fun t => γ.extend t) (pathDeriv γ t₀) t₀) :
  HasDerivAt_R_to_C_eps (fun t => u ((γ.extend t).re, (γ.extend t).im) + I * v ((γ.extend t).re, (γ.extend t).im))
    (ConformalLinearMap_eps ux uy vx vy (pathDeriv γ t₀)) t₀ := by {
  
  have hγ_diff_R2 : HasDerivAt_RtoR2_eps (fun t => ((γ.extend t).re, (γ.extend t).im)) 
    ((pathDeriv γ t₀).re, (pathDeriv γ t₀).im) t₀ := by {
    have h_iff := HasDerivAt_RtoR2_eps_iff_R_to_C_eps (fun t => ((γ.extend t).re, (γ.extend t).im)) ((pathDeriv γ t₀).re, (pathDeriv γ t₀).im) t₀
    have h_simp : (fun t => ((γ.extend t).re : ℂ) + I * ((γ.extend t).im : ℂ)) = (fun t => γ.extend t) := by {
      funext t
      apply Complex.ext <;> simp
    }
    have h_simp2 : (((pathDeriv γ t₀).re : ℂ) + I * ((pathDeriv γ t₀).im : ℂ)) = pathDeriv γ t₀ := by {
      apply Complex.ext <;> simp
    }
    rw [h_simp, h_simp2] at h_iff
    exact h_iff.mpr hγ_diff
  }

  have h_chain := chain_rule_R2 h_diff (fun t => ((γ.extend t).re, (γ.extend t).im)) t₀ (by {
    exact (congrArg (fun w => (w.re, w.im)) h_eq).trans (by simp)
  }) ((pathDeriv γ t₀).re, (pathDeriv γ t₀).im) hγ_diff_R2
  
  have h_iff2 := HasDerivAt_RtoR2_eps_iff_R_to_C_eps (fun t => (u ((γ.extend t).re, (γ.extend t).im), v ((γ.extend t).re, (γ.extend t).im))) 
    (ux * (pathDeriv γ t₀).re + uy * (pathDeriv γ t₀).im, vx * (pathDeriv γ t₀).re + vy * (pathDeriv γ t₀).im) t₀
  
  have h_simp3 : (fun t => (u ((γ.extend t).re, (γ.extend t).im) : ℂ) + I * (v ((γ.extend t).re, (γ.extend t).im) : ℂ)) = 
    (fun t => u ((γ.extend t).re, (γ.extend t).im) + I * v ((γ.extend t).re, (γ.extend t).im)) := rfl
  
  have h_simp4 : (((ux * (pathDeriv γ t₀).re + uy * (pathDeriv γ t₀).im : ℝ) : ℂ) + I * ((vx * (pathDeriv γ t₀).re + vy * (pathDeriv γ t₀).im : ℝ) : ℂ)) = 
    ConformalLinearMap_eps ux uy vx vy (pathDeriv γ t₀) := by {
    unfold ConformalLinearMap_eps
    apply Complex.ext <;> simp
  }
  
  rw [h_simp3, h_simp4] at h_iff2
  exact h_iff2.mp h_chain
}"""

content = content[:start_idx] + new_lemma + content[end_idx:]

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
