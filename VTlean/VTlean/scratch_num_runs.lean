import VTlean.B
import VTlean.VTCode
import VTlean.InsDel
open List

namespace List

def num_runs : List B → Nat
| [] => 0
| [_] => 1
| x::y::tail => if x = y then num_runs (y::tail) else num_runs (y::tail) + 1

end List

namespace List.Vector
variable {n : Nat}
def num_runs (X : List.Vector B n) : Nat := List.num_runs X.toList

lemma dS_card_eq_num_runs (X : List.Vector B n) : (dS X).card = num_runs X := by
  sorry

end List.Vector
