# 四胞高斯全局定理：部分形式化 / Partial formalization

**The sharp four-cell bound and its tetrahedral equality classification are
not proved in this package.** This is an unconditional analytic-core advance,
not a conditional wrapper claiming the global theorem. No Gaussian perimeter
theorem or deformation theorem is postulated.

## Proved scope and entry points

`GaussianFourProgress.lean` imports the proved development. `ROOTS.json` lists
135 proof roots: 85 new theorem/lemma declarations in ten modules, plus 50
roots reused from the existing nine-module actual-measure development. These
are dependency-audit roots, not a count of independent new mathematical results.

| Module | Actual mathematical scope | Principal entry |
|---|---|---|
| `GaussianTent` | Exact tent area and Gaussian projection bound | `gaussian_inner_tent_bound` |
| `GaussianMomentSeparation` | Fractional pair separation; exact paper Lemma 4 | `fractional_pair_separation`, `balanced_winning_moment_separation` |
| `GaussianWinningLimits` | Every integrable Banach-valued function over moving cells; mass and moment limits | `tendsto_winning_setIntegral`, `balanced_winning_limit` |
| `GaussianBoundaryTransfer` | Residual convergence forces noncollision, positive multiplier and actual self-moment limit | `balanced_residual_limit`, `balanced_limit_self_moment` |
| `GaussianBalancedValue` | Actual price infimum attained at all score ranks; Lipschitz continuity; price compactness estimate | `balancedValue_attained`, `balancedValue_lipschitz`, `balanced_price_bound` |
| `GaussianHomogeneity` | Actual assignment-value homogeneity, including zero scale | `balancedValue_scale_nonneg` |
| `GaussianFractionalReduction` | Arbitrary actual balanced fractional partition reduced to centered, unit-energy scores | `sqrt_energy_le_normalized_value` |
| `GaussianSetPartitions` | Original measurable cells modulo null overlaps, exact masses and Bochner moments | `SetPartition.normalized_reduction` |
| `GaussianGramInvariance` | Actual Gaussian score law/value determined by Gram matrix, all ranks and ambient dimensions | `scoreLaw_eq_of_gram_eq`, `balancedValue_isometric_embedding` |
| `GaussianEqualityGuard` | Uniform fractional labels are not hard indicators | `uniform_not_ae_indicator` |

All names above are in namespace `GaussianFourGlobal`. The reused definitions
are `GaussianMeasureBridge.Space`, `gaussian = ProbabilityTheory.stdGaussian`,
`FractionalPartition`, actual integral masses and actual Bochner moments.
The original nine source files are imported from `../gaussian-measure-primal-dual`
and are not copied into the maintained package or modified by it.

The separation constant proved here is
`1/(16*phi(0)) = sqrt(2*pi)/16`. It is **not** the conjectured sharp objective
constant `12*(arctan(sqrt(2)))^2/pi^3`.

## Exact targets, not proved theorems

`UnprovedTargets.lean` contains the well-typed propositions
`FourCellFractionalTarget` and `FourCellMeasurableTarget`. They state the
original quantifiers, the exact sharp constant, and an a.e. equality
classification using a three-dimensional linear isometric embedding and a
permutation of the four regular tetrahedron vertices. Embeddings account for
orthogonal orientation and cylindrical extension. **Neither proposition has
a proof.** This statement-only file is compiled but is not imported into the
proved entry point or counted among the replay theorem roots.

The boundary-transfer results have explicit score/price convergence,
balancing and vanishing actual moment-residual hypotheses. Their injective
limiting scores and positive multiplier are conclusions. Producing such
sequences from the covariance Hessian and the constrained normal-cone
construction is still missing. Facet-area continuity is also not proved.
See `COVERAGE.md`, `GAPS.md`, and `ANALYTIC_SUPPLEMENT.md`.

## Fixed environment and reproduction

Lean 4.34.1, compiler commit `5045d0056413266e57c625dcd7c365b10e377c52`.
Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612`.
`lake-manifest.json` and `DEPENDENCY_PINS.json` fix all dependencies;
`TOOLCHAIN_PINS.json` fixes the Linux release binary hashes. Reproduction is
currently specified for the official x86_64 Linux Lean release.

From a checkout of this research branch:

```sh
cd formalizations/gaussian-four-global-progress
bash fetch_cache.sh
python3 reproduce.py --output-dir /absolute/path/that/does/not/exist
```

An already populated, fixed-version dependency checkout can be supplied:

```sh
python3 reproduce.py \
  --mathlib-dir /absolute/path/to/pinned/mathlib \
  --lean /absolute/path/to/lean-4.34.1-linux/bin/lean \
  --output-dir /absolute/path/that/does/not/exist
```

The script checks the actual tracked Lean/config bytes of all dependencies,
not just their Git HEAD labels. Own/reused sources and checker files have
LF-normalized Git-blob pins in `SOURCE_BLOBS.json`; both normalized and raw
SHA-256 values are recorded. Only CRLF/LF normalization is allowed. Pin refresh
is an explicit maintainer operation (`update_source_manifest.py`), never
called by the verifier or CI.

Verification creates a new Lake mirror and then a second, separately empty
source-elaboration directory. All 21 registered modules are built in each:
9 reused mathematical modules, 10 new mathematical modules, one proof entry,
and one statement-only target file. External dependency caches are reused;
this is **not** a rebuild of all Mathlib source files. The transitive proof
closure of the 135 roots is subsequently replayed from an empty kernel at
trust level zero, with only `propext`, `Classical.choice` and `Quot.sound`
permitted. Unsafe/partial mathematical dependencies fail the closure audit.
The replay driver's partial dependency collector is meta-level verification
code, not part of any mathematical proof dependency.

Four controls require Lean to reject a wrong tent constant, a wrong exact
separation constant, a false zero-score boundary value, and unconditional
purification of a uniform fractional partition. Import failures do not count
as mathematical rejections. Per-command full logs, source/object hashes, the
closure list and a machine-readable report are retained.

The workflow `.github/workflows/gaussian-four-measure-boundary.yml` performs
the same process on a separate GitHub Actions runner. A configured workflow
is not itself evidence of a successful independent run; actual run results
are recorded separately after completion.

## Verification status of this source checkpoint

The ten new mathematical modules and both entry/statement files have passed
individual Lean 4.34.1 compilation. The full fresh-build, empty-kernel and
negative-control pipeline is not yet reported as passing at this checkpoint.
No log from a previous project is presented as verification of these sources.

This work is on a research branch, not merged into main. No immutable Release
or DOI is issued for this partial formalization.

## Authorship and rights

Yongxian Zhang (张永贤), School of Computer Science and Engineering,
South China University of Technology. Email: mxymmxym1@gmail.com.
ORCID: 0009-0000-3864-3536. No external funding. AI-assisted research.
Original new materials: all rights reserved unless separately licensed.
Existing licenses and third-party notices remain unchanged. Kernel validation
is not external peer review, and no worldwide priority claim is made.
