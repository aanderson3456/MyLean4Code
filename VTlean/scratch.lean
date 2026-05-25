import VTlean.Cuculiere
import Mathlib

open Nat Finset

lemma max_vt_checksum_succ_test (n : Nat) : max_vt_checksum (n + 1) = max_vt_checksum n + n + 1 := by {
  unfold max_vt_checksum
  have h1 : (n + 1) * (n + 1 + 1) = n * (n + 1) + (n + 1) * 2 := by ring
  rw [h1]
  rw [Nat.add_mul_div_right]
  omega
}
