import VTlean.DelCode
open Vector Nat Finset
namespace List
open List
def mkIO (n k : Nat)  : List B := List.replicate k I ++ List.replicate (n - k) O
end List
#check _root_.List.mkIO