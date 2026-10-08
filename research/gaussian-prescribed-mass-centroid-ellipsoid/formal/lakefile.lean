import Lake
open Lake DSL
package gaussianQuotaEllipsoid
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib Algebra
lean_lib RadialComparison
lean_lib AdditionalRadial
