# Gaussian four-cell verification failures: diagnosis and repair

This is a source-error repair and partial-proof checkpoint, not a claim that
the global theorem has been completed. The failed historical runs are retained
as evidence. No failing proof step has been disabled or changed to succeed
unconditionally.

## Diagnosis of the reported failures

All fourteen runs present when this investigation began were examined. Nine
failed. Their preserved compiler logs identify source errors, not a GitHub
outage or a successful proof incorrectly marked red.

| Runs | Failing source / cause | Successful successor covering the affected code |
| --- | --- | --- |
| 38026484991 | ScalarTent: wrong indicator-integrability API, inference and positivity errors | 38033062208; also the current expanded closure |
| 38055617935 | Imported GaussianSimplexAlgebra: missing typeclass instances | 38056539214; also the current expanded closure |
| 38056127244, 38056209353 | CenteredSpectral: rewriting a local matrix value as though it were an equality | 38056539214; also the current expanded closure |
| 38057111598, 38057403190 | PriceMassDifferential: permutation sum API and the actual winning-mass definition | 38064502958 |
| 38057721665 | PriceSecondVariation: identity-function and zero-score-path normalization; extra tactic after closure | 38064502958 |
| 38057929944, 38058196787 | PriceFrechetIntegral plus the preceding second-variation errors: real norm versus absolute value, continuity/Tendsto, winning-score argument order, exact NNReal Lipschitz constants | 38064502958 |

Downstream `PriceFrechetTransport` also required exposing a composed function
before applying the winning-cell reindex identity. Earlier failures had
prevented that module from being reached. These proof terms have now been
checked, rather than merely edited and left pending.

The repair retained unsuccessful intermediate checks as well. They isolated
the remaining NNReal bound and composition failures; they are not represented
as passes. `evidence/ci-repair/HISTORICAL_RUNS.json` binds historical metadata,
original artifact hashes and byte-identical retained diagnostic members. The
compact diagnostic tar omits development object archives and is explicitly
not labeled as an original Actions ZIP.

The first complete repaired 89-module closure passed run **38064502958** at
commit `c21dd3eb4959c3fa7bf317bca2f253721b509512`: 540 audit roots, 60,472
replayed declarations, trust level zero, and eight rejected mutations. Its
original artifact is retained under `evidence/ci-repair/first-green/`.
The centered-Hessian extension and its current receipts are indexed in README.

## Why old red runs are not erased

A rerun of an old workflow checks the same old commit and cannot pick up a
source fix committed later. Repeatedly rerunning a deterministic type error
would not repair it. We preserve the failed run, fix the source in a descendant
commit, execute the full verification there, and record the successful
successor. The active covariance branch is advanced without force-pushing;
its current-head workflow must complete successfully.

## Preventing unnoticed verification gaps

`preflight.py` checks pinned source hashes, complete owned-module inventory,
import/build order and exact agreement between ROOTS.txt, Audit.lean and
Replay.lean. Five regression tests show that valid inventories pass and
unlisted sources, unknown imports, wrong build order and audit-root drift fail.
These Python tests do not substitute for Lean type checking.

The workflow runs this inexpensive check before dependency setup. On any
later failure it publishes the first compiler errors in the Actions summary
and preserves the literal logs and source commit. Failed development objects
may be retained to assist diagnosis, but they are never used as fresh-build
or empty-kernel proof evidence.

The full verifier still constructs a new Lake source tree with zero owned
objects, builds it, separately compiles every owned module into another empty
object directory, audits the roots, and replays the used declaration closure
into `mkEmptyEnvironment 0`. It rejects unexpected axioms and unsafe/partial
proof dependencies. Only `propext`, `Classical.choice` and `Quot.sound` are
allowed. Source hashes are checked before and after verification.

The current nine unique source mutations include the actual covariance
factor 1/2, the price-Hessian constant-shift nullspace and the strict curvature
sign on centered prices. Each must fail actual Lean compilation for a proof
reason, not a missing import or other infrastructure failure.

No main-theorem completion Release or DOI is justified by this checkpoint.
The remaining mathematical obligations are listed in GAPS.md.
