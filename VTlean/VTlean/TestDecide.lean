import Mathlib
import VTlean.B
import VTlean.DelCode
import VTlean.Dream
import VTlean.VTCode

open B List.Vector Finset

def stringToVector (s : String) : List.Vector B s.length :=
  ⟨s.toList.map (fun c => if c == '1' then B.I else B.O), by simp⟩

def counterexample_C : Finset (List.Vector B 5) :=
  { stringToVector "00000",
    stringToVector "00011",
    stringToVector "01101",
    stringToVector "10010",
    stringToVector "11100",
    stringToVector "11111" }

lemma is_opt : is_OptimalCodeCandidate counterexample_C := by
  decide

lemma is_counterexample :
  ¬ (∑ i ∈ Finset.Icc 1 2, num_words_with_runs counterexample_C i ≤ ∑ i ∈ Finset.Icc 1 2, num_words_with_runs (Finset.VTCode 5 0) i) := by
  decide
