# Third independent source review: same-execution input fees and first concrete instance

Status: **No substantive mathematical, execution-record correspondence, or stated partial-counter defect found in the three fixed objects below. Actual author logs and source/hash bindings are independently rechecked. No Lean/Lake invocation, fresh kernel replay, or strict controls were run. Complete compiler/provider machine bit time remains open.**

This report is a separate immutable continuation of the earlier source reviews. Their conclusions remain tied to their earlier fixed objects; neither old report is rewritten. Later list-assembly/rank-scan authors' work and the parent's later concrete input-interface revision are expressly excluded. No new major-novelty claim is made.

## Fixed objects and inspected scope

| Fixed component | Git object | Selected ordinary author evidence |
|---|---|---|
| Actual input numerical338 plus same-execution read fees | `4663f467c0dc117ef3c9b73403e01006a28fb657` | 26 theorem roots/8 models; 3974 jobs |
| Fully retained input-reference extraction | `cc94df713f82a301400d1d1ef67606d0eec090c3` | 13 roots/15 models; 4074 jobs |
| First concrete four-gate native instance | `908199a025a8dd9f295d3dfa5e4fd3ee1a198986` | 8 roots/3 selected model roots; 4089 jobs |

The new mathematical modules read in full are C's `InputNumericalBudgets`, `InputNumericalPower`, `InputNumericalSynthesis`; E's `RetainedInputTarget`, `InputLabelCompilation`, `FullyInputNativeExtraction`; and the concrete package's `Program` and `Resources`. Their check/scope/report sources, E's tiny evaluation, the concrete declaration-kind check, and the relevant budget-normalization algebra were also inspected. The original wire-count definition and its `originalWireCount_eq` proof were checked for the 2k-wire interpretation.

The new inputs extend prior components already reviewed here. The verifier checks that the earlier C evaluator/read chain is unchanged, that E uses exactly C4663's three numerical modules, and that the reviewed binary generation/provider chain remains unchanged in both Ecc94 and the first concrete instance. The concrete provider, dyadic interface and SU(2) density sources match the earlier independently read fixed objects. This uses exact bytes, not another author's review conclusion.

All reads use fixed Git objects. The manifest binds directly inspected sources, scope metadata and author source snapshots, original D: logs, and independently resolved local import graphs/configurations. Transitive binding does not mean every imported proof was newly human-reviewed. E's broad author input snapshot also includes unused native Boolean-rank modules; they are hash-bound as provenance only and are absent from the selected reachable import graph. They receive no mathematical review endorsement here.

## C4663: numerical and decision budgets for the actual input program

The earlier C788 evaluator returned actual scalar numerical evaluations, decisions, and concrete cache-read records, but lacked a whole-program numerical338 bound. C4663 fills that particular gap without inferring cost from output-word equality.

`InputArithmeticWordResult.nativeView` is a proof-side record view. It keeps the returned word, comparisons, decisions and already-stored numerical evaluations, and maps the recorded input expressions through proof-side resolution. It is not called by `inputRun` to produce the program's value. In particular, a numerical charge is not obtained by executing a second native program and attaching its unrelated cost. The actual definitions are direct projections:

- `evaluationActions` sums each returned evaluation's numerical trace Boolean actions.
- `decisionActions` sums the returned minimum/comparison traces.
- `numericalActions` is their sum.
- `onlineActions` adds the already-returned concrete `readActions` to that same numerical sum.

The evaluation bound uses the earlier proved equality between each actual input evaluation's entire numerical record and `.wordRun` on its resolved expression, together with the proved expression/evaluation-list correspondence. It then applies the established native primitive-height/action theorem to that same numerical record. The sum of expression budgets bounds each participating operand; a local generic budget lemma has an explicit B premise, as expected, but the final whole-program theorem derives B internally.

The decision proof is separate and necessary. The base case uses the heights of all actual stored score values to bound `wordMinimumProgram`. A correction uses the heights of the actually evaluated score and threshold to bound its actual `wordScalarLEProgram` trace. Splitting the returned expression-budget sum gives the recursive child budgets in the taken branch. Both nested correction levels are covered by induction on `inputTracedPairWord`. Only the selected branches' real records contribute. Comparing expression-list length with structural operations then bounds all decision slots; they are not silently treated as constant-cost comparisons.

For Q=p+1, the raw-expression refinement internally bounds total represented operand budget by `20*C*Q^(a+128)` and operations by `20*O*Q^64`, with

`C=1000000000002*(n+1)*(8*A+10)*(L+1)*traceRGrowth`

and `O=1020*(n+1)*(2*L+1)*offsetGrowth`.

The primitive algebra yields `40000*(40*C+4)^2*(20*O)*Q^(2*a+320)`. Setting the finite input-height envelope exponent a=9 gives degree338. The degree338 theorem's only size assumptions concern gate/target packets at the finitely built cache precisions. Those finite assumptions are extended to all reader queries by the proved cache-value/default behavior; the unit default fits the same nonnegative height bound. No caller supplies a total operation count, total read count, final represented budget, or final numerical-fee certificate.

The same actual input program already has degree73 concrete read-spine actions. Since Q>=1, its Q^73 term is bounded by Q^338, so `inputCachedRun_onlineActions_degree338` adds the numerical338 and read73 coefficients for **one actual returned `InputArithmeticWordResult`**. This is the connection missing at the old C788 checkpoint. It does not add provider/eager-cache/AST construction or arbitrary host control costs.

## Ecc94: every retained field belongs to the same execution

`retainedInputTargetRun` prepares the native target once, constructs the eager target `PacketWordEvaluation` records once per requested precision, stores that vector, maps those stored values into the target cache, builds the gate cache, and calls the actual input-reference recursion on that cache. Its returned fields are the actual prepared input, actual provider records, and actual input-cache/numerical/read result.

Two exact relations are central:

1. `retainedInputTargetRun_cache` equates the stored target cache with the value projection of the stored provider programs.
2. `retainedInputTargetRun_cached` equates the **entire** cached record with `inputCachedRun ... (prepareNativeSingleInput u).packetDataOracle`, not merely their emitted words. This includes the cache, input expression list, numerical evaluations, decisions, read records and word through the nested record.

Thus C4663's online fee applies to the very execution retained by E. Target-provider actions are also projections of the stored provider records, which have the same definitions as the previously bounded retained provider. Equality to that provider's action projection is definitional; no replayed charge oracle is introduced. Target operand heights and provider degree27 are closed internally. The remaining generic supplied size condition concerns only finitely queried library packet data. It is not a provider-time or final-budget assumption.

`compileInputWord` retains each single-gate result once, and output labels and all charges are projected from those same stored results. Its generic `sumCharge` lemma accepts a charge function and per-single bound, but the final theorem instantiates it with the concrete stored-record `accountedActions`, whose preparation/provider/online bounds are proved above. It therefore does not leave a free charge choice or unproved final certificate to the caller.

`fullyInputNativeRun` also executes the reviewed binary descriptor generator once and compiles its actual word at the precision determined from that word's length. The final result holds the actual generation and actual compiled input-reference runs. The `accountedPrimitiveActions` definition sums rank-digit encoding traces and every stored single's preparation, provider and online numerical/read traces. Its internal endpoint is

`306*k*(k+4)^9 + actualGatePolynomial k * (200*(4*k+2)^2 + nativeProviderCachePolynomialConstant L*(k+3)^15 + actualInputOnlineCoefficient m n L k gateB) * (logarithmicPrecision k p+1)^338`.

The online coefficient contains the earlier numeric338 coefficient plus the actual read73 coefficient. Every term now belongs to that returned E execution. The theorem uses table word-length bound `hL` and finite library packet height; actual target heights, demand, provider fees and component sums are internally derived. It does not assume the displayed aggregate bound.

The final output-word equality connects this actual execution to `numericalExtractionCode`; the fidelity theorem then invokes the established physical discard/Bell endpoint under the usual actual library approximation, inverse-label and finite-net coverage hypotheses. The exact *local cached record* equality above is new; this review does not invent an additional equality of E's entire final result to an older final-result type. Its stated final endpoints are word equality, generation-action bound, accounted-action bound and physical fidelity.

## Concrete908199a: fixed four-gate instance and quantifiers

The first concrete package deliberately uses `binaryNativeExtractionRun` from the earlier E2f2-based pipeline. Its returned result type and imports confirm that it does **not** execute `fullyInputNativeRun` from Ecc94. Consequently, its inherited `accountedPrimitiveActions` includes rank digits, preparation, target provider and online native numerical traces, but not the newer actual input-cache read traces. C4663's new fee cannot be appended to this old concrete run's counter without changing the run and proving the new bridge. The package README, report and source comments state that limitation correctly.

The matrix alphabet, inverse labels and provider are the actual `rationalGate`, `inverseLabel` and `nativeEntry` already reviewed. The runtime `run net k p` consumes finite-label/net data and canonical binary packets; it does not inspect the unknown input vector z or evaluate the real/complex SU(2) matrices. Matrix and decoded-denotation objects occur in semantic statements. The static net discovery problem remains separate.

`OfflineNet` contains its finite-domain table, length bound and table size, with length/coverage proof fields. Thus `run net` does accept a table record carrying those proofs; the important closure is that `offlineNet_exists` derives such a record's existence internally from the concrete density/net theorem. `concrete_compiler_exists` then places **one existential net before all k, p and unit input vectors z**. It does not select a new net depending on the input, target circuit size or error precision, nor assume a caller-supplied density/coverage axiom in the final existential statement.

There is no executable default produced by noncomputable choice, and no effective table-finding algorithm or numeric table-size/time bound is asserted. A table on a finite domain is mathematically finite data, while discovery/materialization/access costs remain outside this partial execution model. Constants in the resource and output bounds depend explicitly on this fixed net's length/table-size data.

The library-height specialization uses the stronger provider theorem `nativeEntry_height i r` with exponent r+1. From `r <= numericalDemand L (clog 2 (q+1)) <= cachePrecisionBudget L q`, it proves

`r+1 <= (51200000*(L+1)+1)*(q+1)^9`.

The extra one is covered by `(q+1)^9 >= 1`, including q=0. It does not apply a ninth-power bound at r and nest the demand to degree81. The final `run_accounted_actions` therefore discharges the generic library data-height premise internally using the explicit `gateHeightCoefficient`; no queried-height/cost certificate remains in that concrete theorem's arguments.

The eight selected concrete theorems prove fixed-net existence, exact word equality, finite-library use, output length, physical fidelity, queried height, the specified partial resource bound, and the combined existential instance. The fidelity statement is for every unknown unit vector z in C^4 and its k copies, with lower bound `1-(1/2)^p`. The result uses `originalWireCount k`, and the checked definition/proof identifies that with 2k; no extra wires are introduced by this final interface. Output length and the partial classical primitive counter are separate conclusions.

All natural precisions and k=0 are within the theorem quantifiers. The quantified net's proof fields close coverage/length, the concrete provider closes approximation/queried height, and inverse labels/density are proved upstream. None of these closes the excluded ordinary machine costs.

## Present limits and audit status

The important progress over the prior fixed checkpoint is now present in C4663/Ecc94: numerical primitives, decision primitives and actual visited cache list-spines are associated and bounded for the same retained input-reference execution, alongside actual target-provider records in E. The first concrete908199a instance remains the earlier non-input-reference specialization. All later concrete/input/list/rank successors remain outside this report, even if they are now available in the shared object database.

Complete machine bit time still excludes at least:

- actual fixed-library emissions and normalization accumulated over eager requests; finite library heights are not execution fees;
- eager cache/vector/AST/list construction, index/precision/demand calculations and all uncharged lookup or selection work;
- natural range/filter/rank-scan arithmetic, natural equality bit cost, masses, fuel/counters and host recursion/control; preserved rank call counts are not Bool implementations;
- prepared mask/Pauli construction, endpoint packing/extension, structural swap/Gray processing, label/wire transformations, concatenation and output assembly;
- allocation/memory/reference/record management, trace construction/accumulation and evaluation of the charge projections themselves;
- efficient offline net discovery under a uniform preprocessing model.

The new counters remain specified partial Bool/list/record primitive models. No substantive correction is requested for the reviewed mathematical sources. The separate audit recommendation identifies key final roots and source/model bindings for a possible new fresh/trust-zero/strict-control scope; **no such audit was started here**, and the old frozen372 or any other frozen scope must not be enlarged.

## Evidence and read-only reproduction

| Author evidence | Jobs | Actual aggregate log SHA256 |
|---|---:|---|
| C InputNumeric | 3974 | `f91051a714b04974cadc7724225ffff2d11e42c4becdeae41db588b63c848fd7` |
| E InputNative | 4074 | `301b973ae3e5d3c58d6039bcf70e38fc2e5b4f318d86878ef249fb3a0c6345d8` |
| Concrete first instance | 4089 | `46e3b0096b66402ec2fb503da7ba7c41bf37be4fda2d1ccb483d47ae1d280907` |

The verifier checks fixed source snapshots against the selected final objects, actual successful aggregate-build terminal records and every selected printed axiom list. E's generated kind check and the concrete8-theorem/3-definition kind check are read and their actual log markers verified. C's check prints theorem types/axioms and model types. Allowed axioms remain only `propext`, `Classical.choice`, `Quot.sound`, with some declarations using fewer or none. Original owned concrete Program/Resources logs have the expected empty-file hashes; the meaningful selected type/kind/axiom record is the Check log, also checked independently against its fixed report.

The tiny E existing evaluation exercises one actual target input leaf, returning one read and its numerical/read counters; it does not execute a large full synthesis. Its existing log is checked, without running it again. Author report checkout `source_head` fields may precede committing new source; their explicit snapshot maps are checked against the fixed C/E objects rather than treating an earlier metadata HEAD as the complete mathematical snapshot.

Run `python3 -B /mnt/d/math/tmp/extraction-resume-20261018/native-same-execution-concrete-independent-review-20261019/recheck.py` in Ubuntu-22.04. It compares fixed sources, original logs and static import provenance with `MANIFEST.json`, and verifies the previous reports/manifest hashes are unchanged. It reuses the earlier read-only helper only after checking that helper's exact SHA256. It performs no writes, Lean/Lake/compiler invocation, Git mutation or deletion.

Before creating this new D: output directory, the storage guard confirmed `/mnt/lean-research-d` is backed by `/mnt/d/math/wsl-data/lean-research-20261016.ext4`. Reviewer outputs are confined to this new small directory. No prior report, research source, Gaussian file, shared cache or frozen audit/manuscript input was modified. Source review and author-log validation are not independent kernel certification or new hosted-CI coverage.
