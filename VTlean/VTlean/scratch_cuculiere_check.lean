-- Brute force residue class sums for small n
-- Self-contained, compatible with Lean 4 / Mathlib

def cuculiere_raw : Nat → List Nat
| 0 => [1]
| n + 1 =>
  let prev := cuculiere_raw n
  let shifted := List.replicate (n + 1) 0 ++ prev
  let padded := prev ++ List.replicate (n + 1) 0
  List.zipWith (· + ·) padded shifted

def residue_sum (coeffs : List Nat) (m a : Nat) : Nat :=
  let indices := List.range coeffs.length
  indices.foldl (fun acc i => if i % m == a then acc + coeffs.getD i 0 else acc) 0

def residue_sums (n : Nat) : List Nat :=
  let coeffs := cuculiere_raw n
  let m := n + 1
  (List.range m).map (fun a => residue_sum coeffs m a)

def cuculiere_mod_sum_gen_raw (k m a : Nat) : Nat :=
  let coeffs := cuculiere_raw k
  residue_sum coeffs m (a % m)

-- Show coefficients and residue sums for n=0..10
#eval (List.range 11).map fun n =>
  (n, cuculiere_raw n, residue_sums n)

-- Step-by-step induction for n=4 (mod 5): S(k, 5, a) for a=0..4
#eval (List.range 5).map fun k =>
  (k, (List.range 5).map fun a => cuculiere_mod_sum_gen_raw k 5 a)

-- Step-by-step induction for n=5 (mod 6): S(k, 6, a) for a=0..5
#eval (List.range 6).map fun k =>
  (k, (List.range 6).map fun a => cuculiere_mod_sum_gen_raw k 6 a)

-- Step-by-step induction for n=6 (mod 7): S(k, 7, a) for a=0..6
#eval (List.range 7).map fun k =>
  (k, (List.range 7).map fun a => cuculiere_mod_sum_gen_raw k 7 a)
