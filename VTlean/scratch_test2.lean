import VTlean.Optimal
import VTlean.VTCode

open Nat Finset B B.Finset

noncomputable def VTCode_finset (n a : Nat) : Finset (List.Vector B n) :=
  univ.filter (fun x => x ∈ VTCode n a)

