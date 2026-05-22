import Mathlib

def isValid (P : ℕ) (v : List ℕ) : Bool :=
  v.length == P &&
  v.all (fun x => x > 0 && x <= P && x != 2) &&
  (List.range P).all (fun k =>
    let val := v.get! k
    let prev_idx := (k + P - val) % P
    v.get! prev_idx == val &&
    (List.range (val - 1)).all (fun j =>
      v.get! ((k + P - 1 - j) % P) != val
    )
  )

-- Test for P=4
lemma p4_impossible : ∀ v : List ℕ, v.length = 4 → isValid 4 v = false := by
  sorry
