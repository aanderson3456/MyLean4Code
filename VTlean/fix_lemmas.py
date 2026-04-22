import re
import os

with open(f"VTlean/DelCode.lean", "r") as f:
    text = f.read()

# Replace Finset.singleton X with {X}
text = text.replace("Finset.singleton X", "{X}")
text = text.replace("Finset.singleton", "singleton")

text = text.replace("apply False.elim hxin", "exact False.elim (Finset.not_mem_empty _ hxin)")

text = text.replace("rw [mem_singleton]", "rw [Finset.mem_singleton]")

text = text.replace("sdiff_subset_self", "Finset.sdiff_subset")

text = text.replace("iff.intro", "Iff.intro")

text = text.replace("eq.refl", "Eq.refl")

text = text.replace("subset.antisymm", "Finset.Subset.antisymm")
text = text.replace("subset_insert", "Finset.subset_insert")
text = text.replace("subset.trans", "Finset.Subset.trans")
text = text.replace("empty_subset", "Finset.empty_subset")
text = text.replace("inter_comm", "Finset.inter_comm")
text = text.replace("inter_subset_inter_right", "Finset.inter_subset_inter_right")
text = text.replace("filter_subset", "Finset.filter_subset")

with open(f"VTlean/DelCode.lean", "w") as f:
    f.write(text)

print("Patch basic lemmas completed.")
