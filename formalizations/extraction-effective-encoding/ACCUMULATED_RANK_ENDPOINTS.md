# Actual executed rank records through the extraction compiler

New scope only; all earlier sealed source/configuration and inventories are unchanged.

`EncodedRankEndpoints` calls `constructiveRankProgram` once per occupation endpoint
and stores its returned Fin index and its three returned annotations. The packed
endpoint is formed from that stored index. Branch extension and next-stage
extension preserve these actual annotations.

`RankedBranchWork` evaluates each occupied-letter endpoint and mass once, stores
the records, and compiles merges/Gray paths from the stored packed endpoints.
The annotations sum only fields of those stored endpoint records; they never
invoke rank again to compute a fee. `RankedAlignmentWork` similarly evaluates and
stores one source and one target record per step, then uses the explicit finite
packed swap stack. The semantic embeddings occur only in correctness statements.

`AccumulatedRankGeneration` constructs one literal occupation table per stage,
shares it between both traversals, and returns the built word together with the
rank-work fields from those actual traversals. Recursive compression stores each
previous/stage record once. `rankedExtractionRun` feeds the stored descriptor word
to the existing charged raw target-provider / shared online integer compiler and
returns its generation annotations.

The entire continuous descriptor word equals the preceding literal descriptor
word. The entire finite-label word equals the preceding finite-label compiler,
and its same all-input Bell/discard fidelity theorem follows internally.

For actual `rankedExtractionRun ... k p`, the three accumulated rank annotations
are bounded respectively by:

- explicit range/product/filter list-construction events: `168*k*(k+2)^6`;
- filter predicate requests: `6*k*(k+2)^6`;
- coordinate Nat-equality requests during triple indexing: `18*k*(k+2)^6`.

These annotations have exactly the specified meanings inherited from
`ConstructiveTriples` and `RankByTriples`. They are partial source event models,
not a machine-time theorem. They exclude occupation-input count computation,
Nat comparison/arithmetic/bit access cost, packed-vector materialization and
equality, Gray/swap/list compilation, occupation-table construction fees,
record/map/traversal costs outside the annotated rank builder, annotations'
own arithmetic and storage, fixed gate-library provider time, and all remaining
control/serialization/bit costs. Previously proved occupation-table and provider
models remain separate and are not silently added here. All counter fields are
actual returned program records, rather than unbound supplied fee fields.

Validation for this checkpoint is OWNED_MODULE_CHECK_ONLY_PENDING_AGGREGATE:
all five new mathematical modules and the explicit all-declaration kind/type/
axiom check pass the parent-authorized single-module checker. No standard
aggregate or independent verification is asserted during the frozen audit.
