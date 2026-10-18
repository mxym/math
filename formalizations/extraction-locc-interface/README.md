# Actual finite-round LOCC interface

This package defines `ExtractionLOCC.Tree c d a b`, a finite adaptive tree of
local instruments. At every Alice/Bob node, the finite classical outcome is
communicated and selects a subtree and the acting party's next local dimension.
The terminal systems are `Fin c` and `Fin d`. Individual Kraus outcomes refine
coarser instrument outcomes; repeated continuation subtrees implement the latter.
All node hypotheses are local instrument completeness identities.

`Tree.Leaf` is the complete communicated history and is proved finite.
`leafAlice`, `leafBob`, and `leafKraus` construct the actual ordered products
along that history. The denotation is their finite Kraus sum. `channel_alice`,
`channel_bob`, and `channel_done` prove its operational recursion. Global
completeness, CP, TP, and CP of its actual partial-transpose conjugate follow
from these local identities. Partial transpose acts on Alice (the first party).

`IsFiniteLOCC` is existence of this actual tree with equality of complex-linear
maps. `IsFiniteLOCCProtocol P` applies that definition to P's actual
postprocessing Kraus map. Its definition contains no PPT assumption or
performance conclusion. `productLocal_isFiniteLOCCProtocol` embeds every
existing `P.IsProductLocal` witness via a two-round tree. Every tree produces
an actual `KrausPPTProtocol` through the proved CP/Choi/Kraus construction.

As in the existing extraction model, arbitrary global `P.U` is a separate
preprocessing operation; the finite-LOCC restriction concerns the subsequent
map. No claim is made that adjoining arbitrary global U is itself LOCC/PPT.
This package covers finite-round LOCC, not the topological closure of LOCC.

Lean 4.34.1; Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612.
Use the guarded serialized `worker_build.py` helper. Shared frozen dependency
build locations are recorded in DEPENDENCY_SHARING.json; new package builds
are independent. Validation is ordinary compilation only, pending independent
audit. All prior frozen audit scopes are unchanged.
