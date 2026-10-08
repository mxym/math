import Lake
open Lake DSL
package arithmeticUpstreamAudit where
  leanOptions := #[⟨`autoImplicit, false⟩]
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "d13f23b723b8a846827a245b89c10fc7d3f11612"
lean_lib ClassFieldTheory where
  srcDir := "../ClassFieldTheory/Lean4"
  globs := #[`ClassFieldTheory.+]
lean_lib ValuedFieldTheory where
  srcDir := "../ClassFieldTheory/Lean4"
  globs := #[`ValuedFieldTheory.+]
lean_lib GaloisCohomology where
  srcDir := "../ClassFieldTheory/Lean4"
  globs := #[`GaloisCohomology.+]
lean_lib ProCGroups where
  srcDir := "../ClassFieldTheory/Lean4"
  globs := #[`ProCGroups.+]
lean_lib PrimeNumberTheoremAnd where
  srcDir := "../PrimeNumberTheoremAnd"
  roots := #[`PrimeNumberTheoremAnd.Wiener]
  globs := #[`PrimeNumberTheoremAnd.+]
lean_lib ArithmeticSupplyRayBridge
lean_lib ArithmeticSupplyPNT
lean_lib ArithmeticAudit

lean_lib ArithmeticSupplyDensityConversions
lean_lib Entry002 where
  srcDir := "../../.."
  globs := #[`Entry002.+]
lean_lib ArithmeticSupplyRayConductor

lean_lib ConductorAudit

lean_lib ArithmeticSupplyFromPrimeIdealPNT

lean_lib ArithmeticSupplyMainFromPrimeIdealPNT

lean_lib PrimeIdealAudit

lean_lib ArithmeticSupplyPrimeIdealWiener

lean_lib PrimeIdealWienerAudit
