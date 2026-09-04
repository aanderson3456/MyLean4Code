import sys

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'r') as f:
    content = f.read()

# Fix proof_vx
bad_vx = """      have h_abs_sq : |v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)|^2 = (v (x, z.im) - v (z.re, z.im) - vx * (x - z.re))^2 := sq_abs _
      rw [← h_abs_sq]
      apply Real.le_sqrt_of_sq_le
      have h_sq_nonneg : 0 ≤ (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)) ^ 2 := sq_nonneg _
      have h_comm : (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)) ^ 2 + (v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)) ^ 2 = (v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)) ^ 2 + (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)) ^ 2 := add_comm _ _
      rw [h_comm]
      exact le_add_of_nonneg_right h_sq_nonneg"""

good_vx = """      have h_comm : (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)) ^ 2 + (v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)) ^ 2 = (v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)) ^ 2 + (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)) ^ 2 := add_comm _ _
      rw [h_comm]
      have h_abs_sq : |v (x, z.im) - v (z.re, z.im) - vx * (x - z.re)|^2 = (v (x, z.im) - v (z.re, z.im) - vx * (x - z.re))^2 := sq_abs _
      rw [← h_abs_sq]
      apply Real.le_sqrt_of_sq_le
      have h_sq_nonneg : 0 ≤ (u (x, z.im) - u (z.re, z.im) - ux * (x - z.re)) ^ 2 := sq_nonneg _
      exact le_add_of_nonneg_right h_sq_nonneg"""

# Fix proof_vy
bad_vy = """      have h_abs_sq : |v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)|^2 = (v (z.re, y) - v (z.re, z.im) - vy * (y - z.im))^2 := sq_abs _
      rw [← h_abs_sq]
      apply Real.le_sqrt_of_sq_le
      have h_sq_nonneg : 0 ≤ (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)) ^ 2 := sq_nonneg _
      have h_comm : (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)) ^ 2 + (v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)) ^ 2 = (v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)) ^ 2 + (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)) ^ 2 := add_comm _ _
      rw [h_comm]
      exact le_add_of_nonneg_right h_sq_nonneg"""

good_vy = """      have h_comm : (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)) ^ 2 + (v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)) ^ 2 = (v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)) ^ 2 + (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)) ^ 2 := add_comm _ _
      rw [h_comm]
      have h_abs_sq : |v (z.re, y) - v (z.re, z.im) - vy * (y - z.im)|^2 = (v (z.re, y) - v (z.re, z.im) - vy * (y - z.im))^2 := sq_abs _
      rw [← h_abs_sq]
      apply Real.le_sqrt_of_sq_le
      have h_sq_nonneg : 0 ≤ (u (z.re, y) - u (z.re, z.im) - uy * (y - z.im)) ^ 2 := sq_nonneg _
      exact le_add_of_nonneg_right h_sq_nonneg"""

content = content.replace(bad_vx, good_vx)
content = content.replace(bad_vy, good_vy)

with open('ComplexAnalysis/Sarason/Chapter2.lean', 'w') as f:
    f.write(content)
