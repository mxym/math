# Formalization dependency map — MainTarget PROVED

Lean 4.34.1; mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
The exact original Target.lean and Interfaces.lean are unchanged.
`MainProof.geometric_main_target : MainTarget` is unconditional and checked by
MainTargetProbe.lean against the fully expanded all-real-parameter statement.
All 454 public module lemmas use only standard Lean axioms.

| Construction | Proved modules |
|---|---|
| Exact real geometric powers and signed integer coefficient cover | GeometricParameters,GeometryChain,CoefficientCover |
| Strict original-index activation and all tail guards | Activation,ShiftedActivation,CandidateBounds |
| Full negative/zero/positive affine arrangement bound | SignFiberCount,LineSignBound,Planar (imported unchanged) |
| Actual power/grid cuts, local vectors and continuum entropy | GridCutBridge,BoundedGrid,LocalSignatures,RoutingFactorization |
| Complete tree, exact preorder and global/subtree bounds | RoutingTemplate,RoutingTreeBounds,RoutingPreorder |
| Real dyadic keys, active-point bounds and all-selector address separation | RoutingGeometry,RoutingActiveGeometry,RoutingSeparation |
| Actual first-true/default routing and default-node local hit | RoutingModel,RoutingProbability,RoutingLocalHit,RoutingStableGeometry |
| Finite joint law, actual atoms/default probability and continuum bound | FiniteRoutingProbability,NoDefaultProbability,RoutingCenterAtoms,RoutingLocalProbability,RoutingStableProbability |
| Noncircular simultaneous numerical schedule | EntropySchedule,RoutingChoices,RoutingEntropy,RoutingSchedule |
| Actual canonical global grid and exact exceptional-center density | RoutingGlobalGrid,RoutingStableMeasure |
| Closed projection, infinite-tail repair, measured open cover and grid buffers | ClosedProjection,ClosedRepair,ZeroErrorBuffer,PeriodicRepair |
| Finite-sum Fubini, actual outcome selection and blocker assembly | RoutingMeasure,RoutingAssembly |
| Summable signed countable union, compactification, unconditional target | CountableExhaustion,MainProof |

RoutingInterfaces contains common proposition/event DEFINITIONS, not axioms.
The previously open SmallCompactBlockerSpec is now PROVED by
MainProof.smallCompactBlockerSpec_proved. Intermediate conditional assembly
lemmas remain valid reusable lemmas; their displayed assumptions are discharged
by the actual final construction, not added as global axioms.

The fixed numerical dependency order is K/stride→M→depth→gap→U/L→table outcome.
Local representatives depend on the fixed real center before all unexposed table
assignments. Terminal-address injection holds for EVERY selector assignment.
Closed parameter projection and finite-sum integration avoid analytic-set
projection theory or measurable representative choices. Countable budgets cover
K, integer shifts, signs and every tail; no uncountable parameter budget is summed.

The full source and exact controls are delivered with pinned dependencies and
normal/-O replays. All16 prior reviewed module files and40 imported arrangement
lemmas are unchanged. The stronger written power-remainder theorem is preserved
as source evidence, not claimed Lean-formalized. Novelty remains separately open.
