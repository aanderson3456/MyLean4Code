import Lake
open Lake DSL

package «AnalysTSP» where
  -- add package configuration options here
require mathlib from git
  "https://github.com/leanprover-community/mathlib4"

@[default_target]
lean_lib «AnalysTSP» where
  -- add library configuration options here

lean_lib «WeierstrassLimitR2» where

@[default_target]
lean_lib «AnalyticTSP» where

