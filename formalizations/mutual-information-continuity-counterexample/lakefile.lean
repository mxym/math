import Lake
open Lake DSL

package mutual_information_continuity_counterexample

require mathlib from git "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"

@[default_target]
lean_lib Counterexample where
  srcDir := "src"
  roots := #[`Counterexample]
