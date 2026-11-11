import Mathlib
import brennan.Section2

open Complex Set MeasureTheory Topology Filter Classical
open Brennan.Section2

lemma cayley_zero : cayley 0 = I := by
  dsimp [cayley]
  ring

lemma hasDerivAt_cayley_zero : HasDerivAt cayley (2 * I) 0 := by
  unfold cayley
  have h1 : HasDerivAt (fun (w : ℂ) => I * (1 + w)) I 0 := by
    have h_base := hasDerivAt_id (0 : ℂ) |>.const_add (1 : ℂ)
    convert h_base.const_mul I using 1
    simp
  have h2 : HasDerivAt (fun (w : ℂ) => 1 - w) (-1) 0 := by
    exact hasDerivAt_id (0 : ℂ) |>.const_sub (1 : ℂ)
  have h3 : (fun (w : ℂ) => 1 - w) 0 ≠ 0 := by
    simp
  have h4 := HasDerivAt.div h1 h2 h3
  convert h4 using 1
  simp
  ring
