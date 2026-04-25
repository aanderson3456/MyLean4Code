import VTlean.Optimal
namespace Finset

lemma empty_test (a : Nat) (h : a ∈ (∅ : Finset Nat)) : False := by
  simp at h

end Finset
