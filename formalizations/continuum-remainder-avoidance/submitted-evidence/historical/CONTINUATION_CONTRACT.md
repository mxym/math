# Shared continuation contract

The existing MainTarget remains unchanged: all real a != 0, b, 0 < q < 1,
and EVERY natural tail N. No new axiom or assumed global blocker may close it.
Lean 4.34.1 and mathlib d13f23b723b8a846827a245b89c10fc7d3f11612 stay fixed.
The original 102 public-module-proof Library version 2 is frozen; its source
and evidence remain the reviewed baseline. Do not change the three imported
arrangement modules, original Target/Interfaces, historical archives or manifests.

Common definitions are in ContinuumGeometric/RoutingInterfaces.lean:

- OnePeriodic S := forall x, x+1 in S iff x in S.
- unitDensity S := volume (S intersect Ico 0 1).
- CompactPowerHits H K k N quantifies over every real center x and every
  p : PowerParams (1/K) K, and demands an actual original index n >= N.
- SmallCompactBlockerSpec demands an open periodic H of density < delta for
  every K >= 2, integer k, natural N and real 0 < delta < 1. This is an OPEN
  proposition definition, not a theorem or axiom. Its proof is the common goal.
- FiniteRoutingTables S T has selectors : S -> Bool and terminals : T -> Bool.
  In the probability lane, S and T must be genuine finite address types.
- centerExposureAtom exposed sigma fixes exactly the entries marked some v.
- localRoutingSuccess own terminal omega i is the conjunction of its own
  selector bit and its routed terminal bit. terminal may depend on ALL selectors.
- LocalAddressSeparation requires injective own addresses, own addresses outside
  exposure, and injective routed terminal addresses on EVERY center-atom selector
  assignment. These are obligations for the ACTUAL construction, not global
  independence assumptions. Shared auxiliary selector entries are permitted.
- periodicGridSet N cells uses the already compiled exact periodicGridKey.

Probability interface: for finite S,T, real 0 <= p <= 1, fair selector bits and
independent Bernoulli-p terminal bits, prove the exact JOINT event identity

Pr(center atom AND all local tests miss)
  = Pr(center atom) * (1-p/2)^m

under LocalAddressSeparation. The joint form does not divide by an atom of
zero probability. Actual routing must then provide these conditions; generic
algebra alone is not the routing theorem. Strong negative controls should
remove own-address injectivity, terminal injectivity, or exposure avoidance.

Ownership:

1. grid_geometry owns NEW RoutingGeometry/RoutingTemplate/CandidateBounds
   modules: actual ordered-tree windows, nesting, stable-center keys, address
   distinctness, finite candidate counts and actual routing-signature factorization.
   Reuse the exact planar theorem and existing LocalSignatures entropy bound.
   Do not redo the planar arrangement proof. State the concrete finite tree and
   table-address types to random_measure before substantial implementation.
2. random_measure owns NEW FiniteRoutingProbability/RoutingMeasure modules:
   finite weighted/probability model, exposure/tower averaging, local identity,
   continuum union bound, Fubini and outcome selection. Its concrete tree must
   use the geometry owner's agreed types. Generic intermediate lemmas must be
   connected to the actual tree before claiming the blocker exists.
3. repair_exhaustion owns NEW PeriodicRepair/CountableExhaustion modules:
   periodic outer-regular cover of actual closed R, double-buffer enlargement
   measure bound, all-center repair, reflected/countable budgets, compactification
   and the conditional SmallCompactBlockerSpec -> MainTarget bridge. The existing
   closed projection, full-tail repair and coefficient cover are reused, not redone.
4. root owns shared contracts, the noncircular entropy schedule, integration,
   final audit/replay and Library writeback. Only root edits the aggregator,
   Audit/reproduce drivers and baseline manifests. Agents compile their modules
   directly without mutating these shared files.

Write only in your named additive modules and own scratch/evidence folder.
Use xhigh reasoning for construction and boundary analysis. Subagents are
explicitly authorized if they own genuinely disjoint work; notify root first.
No publication, push, author contact, external message or security change.
Do not inspect or resume the saved infrastructure's old disk-covering project.
Before downloads, read the runtime/network guidance and current policy; reuse
the exact existing toolchain and packages whenever possible.

Every substantive status update should state exact theorem/file, compile status,
unproved mathematical inputs, actual blocker if any, and downstream interface.
Do not report an assumed gap as proved or prioritize isolated easy lemmas over
the substantive construction. Report serious proof gaps immediately.
