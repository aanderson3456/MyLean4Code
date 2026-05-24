import VTlean.NumOsNumIs
import VTlean.InsDel
import VTlean.Optimal

lemma sIns_cons_succ (X : List B) (x : B) (i : Nat) (b : B) :
  sIns (x :: X) (i + 1) b = x :: sIns X i b := by {
  rfl
}
