import Lake
open Lake DSL

package QuasiRiemann where
  version := v!"0.1.0"
  leanOptions := #[⟨`autoImplicit, false⟩]

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target]
lean_lib OAI where
  roots := #[`OAI.NumberTheory.DirichletL.Nonvanishing]
  globs := #[`OAI.NumberTheory.DirichletL.+]

lean_lib QuasiRiemannHypothesis where
  roots := #[`QuasiRiemannHypothesis]
