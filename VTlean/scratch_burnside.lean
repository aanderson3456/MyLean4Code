import Mathlib
import VTlean.VTCode

open Nat Finset

def cyclicShift {n : Nat} (v : List.Vector B (n+1)) : List.Vector B (n+1) :=
  let l := v.val
  have h_not_nil : l ≠ [] := by {
    intro h
    have h_len := v.property
    rw [h] at h_len
    contradiction
  }
  ⟨l.getLast h_not_nil :: l.dropLast, by {
    rw [List.length_cons, List.length_dropLast]
    have h_len := v.property
    omega
  }⟩
