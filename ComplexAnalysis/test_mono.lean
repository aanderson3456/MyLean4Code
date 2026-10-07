import Mathlib.Data.Real.Basic
import Mathlib.Topology.Instances.Real

example {x y : ℝ} (h : x ≤ y) : ⌊x⌋₊ ≤ ⌊y⌋₊ := Nat.floor_mono h
