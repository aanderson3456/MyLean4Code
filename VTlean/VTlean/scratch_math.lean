import Mathlib

lemma test1 (A B m : Nat) : (A + B % m) % m = (A + B) % m := by
  omega

lemma test2 (A B m : Nat) : (A + B % m) % m = (A + B) % m := by
  exact Nat.add_mod A B m -- wait, Nat.add_mod is (a + b) % n = (a % n + b % n) % n
