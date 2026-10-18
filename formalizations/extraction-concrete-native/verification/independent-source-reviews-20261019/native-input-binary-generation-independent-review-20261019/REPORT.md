# Independent fixed-source review: C788 input reads and E2f2 binary generation

Status: **No substantive mathematical, data-correspondence, or stated partial-counter defect found in the fixed objects below. Existing author-standard evidence is independently hash/log rechecked. No new Lean/Lake run, fresh kernel replay, or strict controls were executed. Whole compiler/provider machine bit time remains unproved.**

This is a new independent source-review scope. It does not modify the prior native-library review, its binary appendix, research sources, frozen manuscript/audit inputs, or earlier reports. The review makes no new major-novelty claim. Later author successors and the parent's new uncompiled aggregate interface are excluded.

## Fixed inputs and evidence boundary

| Component | Fixed Git object | Selected author evidence |
|---|---|---|
| C input-reference evaluator and whole synthesis | `7882995102f1d59b863e3b8d510d588600a2eba7` | InputCache: 40 theorem roots/48 models, 3967 jobs; InputWord: 27 roots/12 models, 3971 jobs |
| E retained target-provider traces, binary rank endpoints and complete binary descriptor generation | `2f2ff15e6680d102b8aa11cead10bc3396443ca4` | Retained provider: 36 roots/17 models, 4050 jobs; rank endpoint: 6 roots/8 models, 4022 jobs; binary generation: 29 roots/23 models, 4058 jobs |

These are separate selected author scopes; their overlapping root/model counts must not be added into a new audit total. Fixed package prefixes are `formalizations/extraction-numerical-synthesis` (C) and `formalizations/extraction-effective-encoding` (E). Reads use Git objects, independently of a concurrently changing working tree or later root merge.

The reviewer directly read the new C expression/evaluator/budget/oracle/word-recursion/refinement/cache-polynomial chain and its InputWord check, plus the actual `NativeListLookup`, `NativeLinearPacketCache`, and `NativeLinearCachedSynthesis` dependencies. Those three upstream dependency files are byte-identical to `c64157509fd2686e68fd090d8b58717f6545b976`.

For E, the five new binary generation modules, new check/evaluation, complete retained-provider/label/extraction chain, native rank encoder, unary increment encoder and fixed-width output program were read directly. The reviewer additionally read the relevant carried rank, native occupation selection, constructive triple construction, prepared generation, native provider refinement/Boolean-budget and actual native numeric-budget sources. Only the pertinent rank query definitions and early constructive-rank definitions were read in the older `RankByTriples`/`ConstructiveRankExtraction` files; binding their full bytes is not a claim to re-read every unrelated theorem there. Upstream numeric338's entire earlier primitive development is not independently reconstructed by this review.

The manifest binds all source snapshots in five existing author reports, all selected metadata and directly read files, their fixed Git blob IDs, and independently resolved local import graphs/configurations for the selected C and E check modules. Other transitive modules are byte-bound, not claimed to have been human-reviewed in full. Shared Mathlib is fixed at `d13f23b723b8a846827a245b89c10fc7d3f11612`, Lean 4.34.1 as recorded by the authors. This is source provenance validation, not a new compiled-environment audit.

## C788: actual input references and degree73 reads

`InputPacketExpression.input` stores only a native gate/target cache label and a natural precision. The actual `inputRun` evaluator reaches that leaf, stores one `nativeCacheInputRead`, evaluates the returned packet as a native literal, and returns both the numerical evaluation and the singleton read list. It does not execute `.resolve`. Resolution is a proof-side expression interpretation. All arithmetic children, score vectors, comparisons, and selected branches are stored; `selectMax` evaluates its scores and then only the selected branch. The whole-word correction recursion preserves the same discipline. Read lists are accumulated from these actual returned evaluation records, including repeated visits to the same cache entry when separate expression evaluations really request it.

The reader is concrete: `nativeListLookup` consumes both the list spine and the natural index using constructor matching. A target lookup traverses the precision cache and uses the stored unit packet on a miss. A gate lookup first traverses the gate-cache list, then its precision list; a valid `Fin m` gate index always selects an existing cache, so the supplied fallback does not affect valid-label semantics. Actual read results retain both lookup traces. No `Vector.get` supplies the packet in these value-reader implementations; vector access occurs in proof statements and in other, separately accounted parts of the program.

`NativeListLookupTrace.actions` charges four specified list/option/record actions per visited frame. Packet and gate wrappers add four/eight fixed actions. The actual per-read upper bound is `4*(m+P+5)`, including queries outside the cached range: an out-of-range lookup still traverses at most the stored list length and returns its default. This is a specified list-spine model; it excludes the cost of constructing/decrementing a machine integer index or computing the annotation itself.

The numerical record equality `InputScalarExpression.inputRun_numerical` and its packet counterpart establish equality of the *entire* numerical result with `.wordRun` on the resolved expression, not only decoded scalar values. C's read-count and read-action proofs then induct over every evaluator constructor. Actual retained reads are bounded by numerical trace nodes, then by resolved raw-expression structural operations. The whole-word theorem `inputTracedPairWord_evaluations` connects the returned evaluations to exactly the returned expression list; it is proved from the actual recursion and is not a final-cost premise supplied by callers.

The complete operation/read chain is internally closed:

- The proved factor-twenty refinement relates the resolved input expressions to the older raw arithmetic expression tree, preserving output words and comparison counts.
- Raw whole-recursion operation growth supplies `20*O*(p+1)^64`, where `O=1020*(n+1)*(2*L+1)*offsetGrowth` and the only table premise is the actual maximum-length bound `hL`.
- Actual read count is at most that operation count.
- Summing the retained per-read list-spine actions gives at most `4*(m+P+5)*20*O*(p+1)^64`.
- The existing internal demand bound `P <= 51200000*(L+1)*(p+1)^9` yields the actual `inputCachedRun` read-action endpoint `80*(m+51200000*(L+1)+5)*O*(p+1)^73`.

There is no assumed total-query count or final read-fee certificate. `inputCachedRun` builds gate/target caches once and runs the input-reference recursion on them; online readers themselves never invoke a source provider. The number or cost of provider calls made while building those eager caches is outside this read counter.

Word equality, length and approximation-error transport to the old native run is sound: the input AST constructors commute with proof-side resolution, and the concrete list reader has the same packet value as the older cache interface. The correctness/error theorem still has the expected library oracle approximation, inverse-label, finite-table coverage and target-approximation hypotheses.

**C788 does not prove numeric338 for this input-reference program.** Its whole-word theorem equates the output word, while the retained local numerical-record equalities apply to resolved expressions. Neither output-word equality nor the read-action bound alone proves a whole-program numerical fee. `InputArithmeticRefines` supplies word equality, expression refinement and comparison-count equality; a further actual numerical/decision-record budget bridge is still required. The already-existing `nativeLinearCachedRun_numericalBooleanActions_degree338` belongs to the older native result. It is not silently transferred to C788 by this report.

## E2f2: actual binary rank construction and complete record erasure

`nativeBinaryRankProgram` first executes the carried triple rank table/scan once, obtaining the actual natural rank. It then calls `unaryWordEncoding` on that bounded rank: each successor step runs the real ripple-carry `binaryAddProgram` with `[true]` and the real `binaryTrimProgram`, retaining both traces. Finally `endpointBitsProgram` copies or zero-pads the actual digits to the fixed width in one structural pass. The rank-bit construction does not call `Nat.bits`, `Nat.testBit`, binary quotient conversion, Int/Rat materialization, or a semantic occupation decoder. The `testBit` occurrence in the exact old-endpoint equality is a proof bridge. Other parts of descriptor generation, such as mask preparation and natural control calculations, are not asserted to be covered by this bit-only rank encoding claim.

The fixed-width program is correct at width zero and for empty or padded input lists. The proof `binaryWordValue_testBit_getD` identifies its copied/padded digits with the old rank bit view. `nativeBinaryRankProgram_erase` therefore proves equality of the *whole* older endpoint: actual point bits plus construction/predicate/Nat-equality work fields.

The new endpoint/branch/alignment wrappers retain the actual child rank programs that provide their endpoint values. `binaryIndexedRun` stores the pivot endpoint and every other selected endpoint once. The branch table recursion concatenates their real retained program lists. Alignment stores source and target programs once per alignment step, including repeated endpoint generation across separate real steps; sharing that does not exist is not assumed. Each occupation stage shares the prepared Pauli table and native occupation table through local bindings. Runtime occupied-letter selection uses four native mass positivity checks and an explicit `Fintype` list, so semantic multiset membership in its subtype does not force constructing an occupation multiset as runtime data.

The encoding bound is derived from the actual records. One rank encoding's increment/trim/output-list charge is at most `51*(k+3)^6`. At a stage, at most four branch endpoints give coefficient 204; two alignment endpoints per occupation add 102. The native occupation list has at most `(k+4)^3` entries. Thus the stage bound is `306*(k+4)^9`; summing the actual compression stages gives `306*k*(k+4)^9`, and appending Bell-preparation descriptors does not create additional rank-encoding records. The k=0 base case has no rank records and satisfies the zero bound.

`binaryNativeDescriptorRun_result` preserves the complete previous generated descriptor record, including the word and every original rank-work field. The final `binaryNativeExtractionRun` feeds that actual generated word into `compileProviderWord` at the precision computed from that word's actual length. Its erase theorem preserves precision, rank work and the entire retained compiled result. This is stronger than only a final-code semantic equality. In particular, the subsequent cost projection refers to the returned generation and compilation from this execution; it is not a replayed cost oracle.

## Retained provider, numeric338 and fidelity contract

`retainedNativeTargetRun` prepares one native single-gate input, builds each target cache request's actual `PacketWordEvaluation` once, stores those evaluations in `providerPrograms`, and maps their stored Word-packet values into the actual target cache used by the native numerical run. It does not rerun the provider merely to attach costs. Its erase theorem preserves the entire previous target result, and its cache theorem states exact equality of the target cache with the retained provider values. `compileProviderWord` stores each single-gate execution once and returns output labels and all provider/numerical records projected from those same executions.

The target-provider counter sums the actual retained numerical primitive traces over all eager target requests. Its query fee is internally bounded by represented operand budget and operations of the actual prepared target expression; no caller supplies the target-height or final provider-fee polynomial. The cache size/demand bound then yields degree27 in the outer synthesis precision. Its coefficient is internally polynomial of degree15 in k, with the fixed-library/table-size parameters remaining explicit.

The online numerical counter is the sum of actual stored native synthesis `booleanActions` from those same single-gate records. E's new actual-target budget proof closes the target height internally and applies the established native338 theorem. The remaining supplied size hypothesis is only on the finitely queried *library packet data*: for synthesis precision q, every requested library packet has `IntegerPacketHeight ... (gateB*(q+1)^9)`. This is a data representation condition, not an assumption about provider runtime, total queries, target complexity or final time.

For orientation, the earlier independently reviewed concrete rational Word provider has the stronger pointwise height `r+1`. Combining that with requested precision `r <= P <= 51200000*(L+1)*(q+1)^9` permits the explicit coefficient `gateB=51200000*(L+1)+1`. This is a mathematical consequence of the reviewed statements; this report does not claim that a later concrete aggregate interface implementing that specialization is part of either fixed source. Applying the weaker ninth-power bound at r and then substituting the outer demand would unnecessarily produce degree81 and should not be confused with E's ninth-power input contract.

Let `Gk=actualGatePolynomial k` and `X=logarithmicPrecision k p+1`. The final accounted counter has precisely the following pieces:

| Projection from the actual returned record | Internally established upper bound | Main exclusion |
|---|---|---|
| Rank digit increment/trim/output-list traces | `306*k*(k+4)^9` | Rank table/scan arithmetic and general descriptor/control costs |
| Native literal preparation | `Gk * 200*(4*k+2)^2` | All other preparation/structural costs |
| Target-provider cached numerical traces | `Gk * nativeProviderCachePolynomialConstant L*(k+3)^15*X^27` | Library-provider execution and cache/list construction |
| Online native numerical traces | `Gk * actualNativeBooleanCoefficient n L k gateB*X^338` | Read spines, syntax/structure/control and ordinary machine costs |

The final `binaryNativeExtractionRun_accountedPrimitiveActions` sums those exact projections, using X>=1 to absorb the lower-degree terms into X^338. It has `hL` and the finite library-height premise just described, and no assumed aggregate final-fee certificate. The algebra does not silently add the original `RankWork` counts as if they were Bool actions, or add C's degree73 bound from a different execution.

The physical endpoint `binaryNativeExtractionRun_fidelity` uses the proved exact output-word equality and the existing `numericalExtractionCode_fidelity`. Its hypotheses are actual gate approximation, inverse labels, table length and coverage, and an arbitrary unit input vector. The theorem gives `1-2^(-p)` as the Bell-projector overlap lower bound for the stated approximate extraction output and actual finite-label circuit. No runtime conclusion or new gate-provider complexity follows from that fidelity statement. Precision zero is included.

**The E2f2 execution has not integrated C788's input-reference read path.** It still calls `nativeTracedPairWord` with `nativeCachedPacketOracle` on stored target/gate values. Indeed the C-only input/cache modules are absent from E's fixed source branch. E's numeric338/provider27 and C's read73 are therefore mature separate partial results, not one already-composed complete cost theorem.

## Nat call counts versus actual Bool traces

The older carried-rank `RankWork` has three fields: constructive list events, predicate requests, and natural-equality calls. For example, `tripleEqualityRun` explicitly stores three Nat comparisons and annotates the call count as three. That annotation does not give a constant machine-bit cost to arbitrary Nat equality. Triple construction/filtering similarly counts source events or predicate requests while ordinary arithmetic on masses, indices and counters remains outside the fee. Those fields are preserved by the new rank erasure; they are not changed into a Bool equality implementation.

The new `encodingActions` instead sums actual retained addition/trim/output-digit traces, under their explicit Bool/list/record action conventions. Target-provider and online numerical actions are also projections of concrete retained primitive records. These facts are stronger than a payload-size estimate or a caller budget annotation, but none is an all-inclusive abstract-machine semantics. Trace construction, accumulation, sum evaluation, source list copying, machine integer operations and storage management are not covered merely because the returned data has a polynomial size or the selected primitive projections have polynomial bounds.

## Remaining complete-machine gaps and most effective next bridge

The most effective next connection is to establish the numerical operand/decision budgets and numeric338 fee for the *actual C input-reference record*, using its already-proved exact local numerical-record equality and raw expression refinement. A sufficient bridge must cover returned evaluation/decision traces and the internal height bounds; output-word equality alone is insufficient. The E retained single-target result can then be changed in a separate source revision to store that same input-reference execution while retaining the target provider records. Its final projection could then combine actual read73, actual numeric338 and provider27 for one returned execution, with explicit erasure/fidelity transport. This is a proposed next mathematical development, not a result certified here; later author attempts are excluded.

After that connection, complete machine bit time still requires at least:

1. Actual fixed-library provider execution, precision clock/control, denominator and vector/list construction, including the separately reviewed rational provider's finite-state generation and normalization, accumulated over the actual eager requests. Library packet-height bounds do not supply those costs.
2. Eager cache construction and all indexing/selection work outside the concrete C list readers, including table access, generated precision/demand computations, and machine representation costs for indices/fuel/counters.
3. Native triple range/product/filter generation, predicate arithmetic, actual Nat equalities or their binary implementations, rank index accumulation, occupied-letter selection, sorting, masses and all scalar control calculations. Existing raw call/event counts require operand-size and primitive implementations to become bit-time bounds.
4. Prepared Pauli/mask table generation and lookup, endpoint packing/extension, stored-swap traversal and comparisons, branch/raw compiler generation, wire relabeling, prefix/shift/cast construction, Bell descriptors, and all relevant word/list/AST concatenation/allocation. Existing payload or selected component bounds do not automatically cover their construction.
5. Memory/reference/record management, recursion dispatch, trace bookkeeping and counter accumulation under a defined machine/representation model, with a compositional correspondence to the actual programs. One cannot silently assign all host Nat operations constant cost.
6. The fixed offline finite net still has an existence theorem, not an efficient discovery-time theorem. It may be treated as fixed library-dependent precomputation only when that convention is stated explicitly; uniform net-generation time remains separate.

No substantive correction is requested for the fixed mathematical sources. The remaining limitations are visible proof/model boundaries, rather than a false total-time theorem in the reviewed code.

## Hash-bound author evidence and read-only reproduction

| Author run | Actual log SHA256 |
|---|---|
| C InputCache 3967 jobs | `3811c5c78c7aff947b382c770ff42b9f18b6975e29b4166f82c04ddbd1b1de41` |
| C InputWord 3971 jobs | `865d7965e3d550686d0f2d742ad5e1e6b68b4c136e47db1bbe7a57fb22dfc69a` |
| E retained provider 4050 jobs | `5f948a348f38bf6257d1da8b20e94c04324ee267e07b9f539c87699c40113c5d` |
| E binary rank endpoints 4022 jobs | `bbfb2677c31a0d36bca673615efa83c74e7afd515c062657c5dfc08fcf74f6e9` |
| E binary generation 4058 jobs | `deaffcf64c899dd2571d8a1dd80d7c11f36cd5fe53a8d3b74fe313641c380c9b` |

The independent verifier checks each original D: log against the fixed report hash, its actual successful aggregate-build terminal record, and every selected printed axiom list. E's generated check modules additionally require theorem/model declaration kinds and log the actual corresponding kind-check marker. C's check modules print selected types/axioms and model types. Permitted printed axioms are only `propext`, `Classical.choice`, and `Quot.sound`, with some declarations using fewer or none.

The author's `source_head` fields describe the checkout HEAD observed during their work and may precede committing newly added source files. The snapshot hash maps are therefore explicitly checked against the later fixed C788/E2f2 objects reviewed here; a metadata HEAD is not substituted for the actual source snapshot. Small E evaluations exercise retained yBasis cache requests, a rank endpoint and the k=0 binary descriptor, not the full large extraction pipeline. This independent review rechecks their existing logs and does not run those examples again.

Run `python3 -B /mnt/d/math/tmp/extraction-resume-20261018/native-input-binary-generation-independent-review-20261019/recheck.py` in Ubuntu-22.04. It reads the fixed objects and existing D-backed logs, reconstructs static local import provenance, and compares the result to `MANIFEST.json`. It also checks the unchanged hashes of the original library report/manifest and binary appendix/manifest. It performs no writes, Lean/Lake invocations, Git mutations, or deletions.

Before creating this new small D: review directory, `ensure_d_storage.py` confirmed the research mount is backed by `/mnt/d/math/wsl-data/lean-research-20261016.ext4`. All reviewer output is confined to the new D: directory. No shared cache, Gaussian file, frozen input, prior report or research source was edited or removed. This report does not enlarge any frozen independent audit or hosted-CI scope.
