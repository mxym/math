import Lake
open Lake DSL
package bapatQPermanentDependencies
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @
  "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib QDefinitions
lean_lib QPermanent
lean_lib MinorPermanent
lean_lib EndpointIdentity
lean_lib EndpointDefect
lean_lib HermitianReality
lean_lib ProductBounds
lean_lib PolynomialBounds
lean_lib MatrixPerturbation
lean_lib InversionBounds
lean_lib EndpointBridge
lean_lib NonDiagonal
lean_lib PositiveDefiniteViolation
lean_lib DimensionBounds
lean_lib CounterexampleTransfer
lean_lib Controls
