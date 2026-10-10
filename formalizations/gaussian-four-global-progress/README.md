# Four balanced Gaussian cells: partial formalization / 部分形式化

**Status: unconditional partial results, NOT the global sharp theorem.**
The bound `12 * (arctan (sqrt 2))^2 / pi^3` and its complete equality
classification have not been proved by this package. There is no conditional
wrapper presented as that theorem and no axiom for a geometric input.

## Additional core proof modules

`PriceBounds.lean` proves the exact Gaussian pair-price bound from actual
winning-cell masses. `PriceCompactness.lean` proves a normalized-price bound
and a convergent subsequence theorem. `TraceSupport.lean`, `NormalCone.lean`,
and `RegularizedResidual.lean` prove the all-matrix upper-normal equivalence,
complementary slackness, and the intrinsic three-dimensional residual bound.

See [CORE_PROGRESS.md](CORE_PROGRESS.md) for exact statements, dependency
graphs, and the still-missing link to the actual Gaussian covariance gradient.
None is presented as a replacement for the global partition theorem.

## New proved analytic chain

`GaussianFour/Profile.lean` constructs the actual upper Gaussian quartile
`q = upperQuantile (1/4)` and proves, by integration and exact real arithmetic,
`0 < q < 7/10`, `phi(q) > (3/4) phi(0)`, and
`phi(q)^2 > 9/(32*pi)`. No sampled Gaussian CDF, floating-point certificate,
external Taylor bound, or quantitative profile hypothesis is used.

`GaussianFour/QuartileIntervals.lean` identifies equal-mass ordered interval
thresholds as `(-q,0,q)` and computes their **actual Gaussian Bochner moments**
as `(-h, h-phi(0), phi(0)-h, h)`, where `h=phi(q)`. Endpoints are handled by
null-singleton arguments, not by ignoring their measure without proof.

`GaussianFour/OrderedWinning.lean` proves that positive balanced masses of
four strictly ordered affine scores force their consecutive crossings to be
strictly ordered. The actual winning sets are exactly the resulting open
intervals. Gaussian masses then force the quartile thresholds.

`GaussianFour/RankOne.lean` proves that a balanced self-moment diagram has
middle facet weight greater than two and violates the centered spectral
quadratic-form bound, using the explicit vector `(0,1,-1,0)`.

`GaussianFour/CollinearTransport.lean` proves the actual Gaussian pushforward
and Bochner-moment bridge for `v_i = a_i u`, with `norm u=1`, in every ambient
dimension. Thus the ordered-collinear obstruction is not restricted to a
surrogate one-dimensional Gaussian model.

Main new entry point:

```lean
GaussianFour.no_ordered_collinear_selfMoment_spectral_bound
```

Its hypotheses are unit `u`, strictly increasing scalar coefficients `a`,
actual winning-cell masses `1/4`, and actual vector self-moment identities.
Its conclusion rejects the explicit adjacent-facet quadratic-form bound.
It does **not** assert the covariance Hessian/normal-cone bridge that would
supply that bound for every putative global boundary maximizer.

## Retained earlier unconditional results

The five existing separation/triple-tie modules are retained unchanged.
They prove triangular-cap integration, actual fractional pair-moment
separation, four-cell winning-moment separation, limiting non-coalescence,
and the affine middle-score triple-tie obstruction. This round recompiles
and replays their proofs along with the new chain.

The nine actual-measure/price modules in `../gaussian-measure-primal-dual`
and six analytic modules in `../gaussian-mass-envelope-progress` are reused
by source path. The duplicate `GaussianPartition` in the latter is not built
or shadowed. No research-branch theorem is silently imported.

## Verification and reproduction

The new core modules have passed individual compilation and a fresh Lake
build. At this source checkpoint, the retained `kernel-r2` evidence covers
the earlier 26-module/206-root closure only. A separate current source-bound
replay receipt is required before treating the expanded closure as replayed.

Toolchain: Lean 4.34.1, commit
`5045d0056413266e57c625dcd7c365b10e377c52`.
Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`.
Transitive dependencies are fixed by `lake-manifest.json` and checked against
their Git revisions and LF-normalized source blobs by `reproduce.py`.

```bash
cd formalizations/gaussian-four-global-progress
bash fetch_cache.sh
python3 reproduce.py --output-dir /tmp/gaussian-four-independent-check
```

The output directory must not exist. The script constructs a clean Lake
source tree with no owned objects, runs `lake build`, then separately
recompiles every module into a second clean object directory. It checks
source hashes before and after, audits 222 declared roots, and replays
the entire used declaration closure into `mkEmptyEnvironment 0`, checking original and
replayed root types and universes. The only axioms are `propext`,
`Classical.choice`, and `Quot.sound`. The recursive collection routine is
verification metaprogramming, not an assumption of a mathematical theorem.

Six source mutations must be rejected, including: a false quartile upper bound of
zero, the wrong sign of the left quartile boundary, and the wrong sign of
the first interval's moment. These are actual failed Lean compilations,
not a Python comparison of expected answers. The new controls also set the
price bound to zero, reverse the upper-normal sign, and incorrectly set the
regularized residual bound to zero.

`MODULES.json` gives the 31-module build order; `ROOTS.txt` lists all 222
audit roots; `SOURCE_BLOBS.json` binds the reproduction inputs. Literal logs,
SHA-256 source/object hashes, dependency checks, negative-control output,
and the closure list are retained under `evidence/kernel-r2/`. The closure
list is gzip-compressed solely for repository size; its decompressed bytes
are the literal replay output. See `evidence/README.md` for additional runs
and exact CI status. Historical development logs are not represented as
this round's fresh verification.

## Remaining scope

See `DEPENDENCY_MAP.md`, `GAPS.md`, and `PROOF.md`. In particular, rank-two
exclusion, the covariance/price Hessian, higher regularity, the constrained
deformation/mountain-pass argument, actual Gaussian perimeter lower bounds,
the exact tetrahedral arctangent evaluation, and final sharp equality
classification remain. The final arbitrary-partition inequality is not
exported. This is substantial analytic progress, not the last packaging
step of a completed global theorem.

Publication stays on a dedicated partial-progress branch. No completion
Release or DOI is created. Existing immutable editions and third-party
notices are unchanged.

Author: Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. Email: mxymmxym1@gmail.com.
ORCID: 0009-0000-3864-3536. No external funding; AI-assisted research.
Repository notices and third-party licenses remain in force. Original
additions retain all rights except where an existing applicable license
expressly grants otherwise.
