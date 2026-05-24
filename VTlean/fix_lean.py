import re

with open('VTlean/VTCode.lean', 'r') as f:
    content = f.read()

# Fix sub_mod_sDel_of_pos unfold wt error
content = content.replace("unfold sub_mod wt\n  apply List.sub_mod_sDel_of_pos", "apply List.sub_mod_sDel_of_pos")
content = content.replace("unfold sub_mod wt\n  apply List.sub_mod_sDel_of_neg", "apply List.sub_mod_sDel_of_neg")

# Fix num_LOs_min_num_LOs rewrite error
content = content.replace("have hlen : X.val.length = n := X.property\n  rw [hlen] at H", "have hlen : n = X.val.length := by { rw [X.property] }\n  rw [hlen] at H")

# Fix decoding_alg rewrites
nil_regex = r"lemma sDelErr_correctable_of_nil[\s\S]*?rfl\n\}"
content = re.sub(nil_regex, """lemma sDelErr_correctable_of_nil
    {a : Nat} {X : List.Vector B 0} (H : X ∈ VTCode 0 a) (i : Nat) :
    decoding_alg 0 a ((sDel X i)) = X := by {
  apply Subtype.ext
  change (decoding_alg 0 a (sDel X i)).toList = X.toList
  rw [decoding_alg_to_list]
  unfold List.decoding_alg
  have hlen : List.length ((sDel X i)).val = 0 := by {
    rw [List.length_sDel]
    rw [X.property]
  }
  rw [if_pos hlen]
  have h_val_nil : X.val = [] := by {
    have h : List.length X.val = 0 := X.property
    cases X.val with
    | nil => rfl
    | cons head tail => contradiction
  }
  rw [h_val_nil]
  rfl
}""", content)

pos_regex = r"lemma sDelErr_correctable_of_pos\n    \{n a : Nat\} \{X : List\.Vector B \(n \+ 1\)\}[\s\S]*?apply Hr\n\}"
content = re.sub(pos_regex, """lemma sDelErr_correctable_of_pos
    {n a : Nat} {X : List.Vector B (n + 1)} (HX : X ∈ VTCode (n + 1) a) 
    (i : Nat) (Hr : sub_mod (n + 2) a ((sDel X i)) ≤ wt ((sDel X i))) :
    decoding_alg (n + 1) a ((sDel X i)) = X := by {
  apply Subtype.ext
  change (decoding_alg (n + 1) a (sDel X i)).toList = X.toList
  rw [decoding_alg_to_list]
  apply List.sDelErr_correctable_of_pos
  · rw [X.property]; apply Nat.succ_le_succ; apply Nat.zero_le
  · rw [X.property]
  · rw [mem_VTCode] at HX; apply HX
  · apply Hr
}""", content)

neg_regex = r"lemma sDelErr_correctable_of_neg\n    \{n a : Nat\} \{X : List\.Vector B \(n \+ 1\)\}[\s\S]*?apply Hr\n\}"
content = re.sub(neg_regex, """lemma sDelErr_correctable_of_neg
    {n a : Nat} {X : List.Vector B (n + 1)} (HX : X ∈ VTCode (n + 1) a) 
    (i : Nat) (Hr : ¬ sub_mod (n + 2) a ((sDel X i)) ≤ wt ((sDel X i))) :
    decoding_alg (n + 1) a ((sDel X i)) = X := by {
  apply Subtype.ext
  change (decoding_alg (n + 1) a (sDel X i)).toList = X.toList
  rw [decoding_alg_to_list]
  apply List.sDelErr_correctable_of_neg
  · rw [X.property]; apply Nat.succ_le_succ; apply Nat.zero_le
  · rw [X.property]
  · rw [mem_VTCode] at HX; apply HX
  · apply Hr
}""", content)

correctable_regex = r"theorem sDelErr_correctable\n  \{n a : Nat\} \{c : List\.Vector B n\}[\s\S]*?apply sDelErr_correctable_of_neg Hc i h\n\}"
content = re.sub(correctable_regex, """theorem sDelErr_correctable
  {n a : Nat} {c : List.Vector B n} 
  (Hc : c ∈ VTCode n a) (i : Nat) :
  decoding_alg n a ((sDel c i)) = c := by {
  cases n with
  | zero =>
    apply sDelErr_correctable_of_nil Hc
  | succ n =>
    cases Decidable.em (sub_mod (n + 2) a (sDel c i) ≤ wt (sDel c i)) with
    | inl h => apply sDelErr_correctable_of_pos Hc i h
    | inr h => apply sDelErr_correctable_of_neg Hc i h
}""", content)

# Fix Finset.VTCode scoping and instances
content = content.replace("def VTCode (n a : Nat) : Finset (List.Vector B n) := Finset.filter (fun (X : List.Vector B n) => X ∈ VTCode n a) Finset.univ", "def VTCode (n a : Nat) : Finset (List.Vector B n) := Finset.filter (fun (X : List.Vector B n) => X ∈ _root_.VTCode n a) Finset.univ")
content = content.replace("unfold VTCode\n  rw [Finset.mem_filter]\n  simp", "unfold VTCode\n  rw [Finset.mem_filter]\n  change x ∈ _root_.VTCode n a ∧ _\n  simp")
content = content.replace("is_DelCode (VTCode n a) := by", "is_DelCode (Finset.VTCode n a) := by")
content = content.replace("· apply sDelErr_correctable HX i", "· apply List.Vector.sDelErr_correctable\n    rw [mem_VTCode] at HX\n    exact HX")

# Add DecidablePred local instance for the filter
content = content.replace("namespace Finset\ndef VTCode", "namespace Finset\nlocal instance (n a : Nat) : DecidablePred (fun (X : List.Vector B n) => X ∈ _root_.VTCode n a) :=\n  fun X => inferInstanceAs (Decidable (List.Vector.moment X % (n + 1) = a % (n + 1)))\n\ndef VTCode")


with open('VTlean/VTCode.lean', 'w') as f:
    f.write(content)
