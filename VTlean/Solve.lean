import VTlean.Cuculiere

open Finset Nat

/-- 
  The involution mapping a subset S to (n+1) - S.
  This gives us symmetry: VTCode n a and VTCode n (n + 1 - a) have the same cardinality.
-/
-- lemma vt_symmetry (n a : Nat) :
--  Finset.card (Finset.VTCode n a) = Finset.card (Finset.VTCode n ((n + 1 - a) % (n + 1)))

/-- 
  To prove VTCode n 0 is the absolute maximum, we need more than just symmetry.
  We need a translation action or similar combinatorial shift to show 0 is dominant.
-/
