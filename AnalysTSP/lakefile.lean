import Lake
open Lake DSL

package «AnalysTSP» where
  -- add package configuration options here
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_exe «AnalysTSP» where
  -- add executable configuration options here
