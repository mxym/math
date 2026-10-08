# Manuscript finalization verification

The complete manuscripts are indexed in [manuscripts/README.md](../../manuscripts/README.md).
Current machine-readable outcomes are in [STATUS.json](STATUS.json). A PASS
record is scoped to its actual checks; package hashes, finite diagnostics and
fresh kernel replays are different evidence. Historical records have not been
silently relabeled as new runs. Standard Lean kernel/compiler/runtime semantics
and the axioms `propext`, `Classical.choice`, `Quot.sound` remain trusted.

## Finite and polynomial checks

```sh
python3 -B verification/finalization/replay_finite.py --output /tmp/new-finite-run
python3 -B verification/finalization/check_replay_guards.py
python3 -B verification/finalization/check_cramer_polynomials.py
python3 -O -B verification/finalization/check_cramer_polynomials.py
```

The common runner pins the historical sources, works in disposable copies,
and runs 20 exact checkers with matching normal/optimized-launcher outputs. The
strict launcher compiles the checker with assertions enabled. If invoked in an
optimized process it restarts an isolated unoptimized child, preserving the
assertions in imported local helpers as well. This does not claim that a raw
assert-based checker executed with `python -O` is sound. Negative controls
reject false entrypoint/imported assertions and a corrupted certificate objective.

The three-subset extension exhausts 1,489,083 compressed types in degrees
24--120; the four-subset extension exhausts 129,523 types in degrees 26--50.
The compressed moment identities and completeness of the feasible types are
proved in the paper. Universal permanent polynomial identities use either
degree-bounded rational interpolation or exact coefficient comparison, as
explained in the proofs. The matrix/tensor sample diagnostics alone do not
establish an infinite theorem. The symbolic asymptotic checker requires SymPy
1.14 or compatible; all other certificate checks use the standard library.

The new Cramer checker uses rational coefficient lists and all 120 determinant
terms. It verifies the full polynomial identities, degrees and leading/next
coefficients for every residue class. Its output includes every numerator and
denominator polynomial. This proves the algebraic identities for all parameter
values; positivity for sufficiently large parameters and global dual bounds
are the written analytic steps. It does not assume a discovery solver.

Recorded results: [finite report](results/finite/report.json),
[negative controls](results/replay-guards.txt),
[Cramer polynomial certificate](results/cramer-polynomials.json),
[PDF build](results/pdf-build.json). All five PDFs build without shell escape,
undefined references, missing characters or overfull boxes; they total 88 pages.

## Partial Lean and full frozen releases

The finite fractional projects were recompiled with the pinned toolchain:

```sh
python3 -B notes/sharp-fractional-cover-frontier/verify.py --lean
python3 -B notes/fractional-design-stability/verify.py --lean
python3 -B notes/fractional-matching-spectrum/verify.py --lean
```

Put the Lean 4.34.1 bin directory on PATH first. Their nine frontier exports,
seven extraction/converse exports and three additional anchor exports are
checked against the frozen axiom reports. These are partial formalizations;
they do not cover the entire fractional-spectrum manuscript.

Full fresh upper/lower simplex commands appear in the
[simplex guide](../../manuscripts/sharp-simplex-stability/README.md). Each harness
rebuilds all owned source modules in a new external output directory, validates
dependency sources and artifact provenance, checks the actual target/ownership
and axiom closure, runs controls, and performs empty-environment trust-zero
kernel replay. Missing or mismatched external artifacts are rebuilt from pinned
sources. No cached owned proof artifacts are accepted. The upper package proves
the earlier `gSharp` theorem, not the improved quadratic coefficient.

### Historical dependency-count fingerprints

The complete fresh upper build and its frozen kernel checks passed with 55,066
all-owned closure declarations and 54,276 literal-Main declarations. Its 848
public proofs and 1,833 owned names/types/owners/kinds/axiom sets match the
historical inventories exactly; the literal Main's 1,197 owned dependencies
also match exactly. The sealed Python harness subsequently rejected the
historical numeric fingerprints 55,067/54,277. That failure is retained in
the [original harness record](results/simplex-upper/LEGACY_HARNESS_RESULT.json).

The [complete-graph continuation](replay_simplex_postbuild.py) validates the
current fresh builder's receipt, source closure, toolchain, package pins,
object hashes and original external artifact-reference guards. It reruns the
frozen ownership, axiom, positive/negative, exact-rational and empty-kernel
audits. A graph export is inserted before the unchanged kernel replay; the
Python checker independently checks that this graph is exactly the recursive
closure of every required root, with no unsafe/partial nodes or unexpected
axioms. It records both historical and actual sizes without resealing history.
Its [upper result](results/simplex-upper/VERIFICATION.json) is PASS.
The [lower result](results/simplex-lower/VERIFICATION.json) is also PASS:
125 fresh modules, 850 public proofs, 1,849 owned declarations and 55,162
empty-kernel declarations. Its historical fingerprint is 55,163; the
[original lower rejection](results/simplex-lower/LEGACY_HARNESS_RESULT.json)
is retained as well.

The old upper package did not publish the full external declaration graph,
so this record does not identify a particular removed historical node. The
current full graphs are public for future comparisons. Kernel acceptance of
the complete required roots, together with the frozen type/source checks,
is the mathematical evidence; the graph cardinality is a build fingerprint.

After running the sealed fresh builder, use a new continuation output:

```sh
python3 -B verification/finalization/replay_simplex_postbuild.py \
  --kind upper --fresh-build /tmp/new-simplex-upper \
  --lean-bin /path/to/lean-4.34.1/bin \
  --dependency-project /path/to/pinned-dependency-project \
  --output /tmp/new-simplex-upper-complete-graph
```

Use `--kind lower` with the lower builder's fresh directory for that suite.
An incomplete build receipt, changed object, source/pin/type/axiom discrepancy,
missing graph node or failed kernel check is rejected. This is a continuation
of the current source build; no historical owned proof objects are substituted.

## Continuum cache-miss repair

`replay_continuum.py` corrects cache-miss build defects in the sealed
continuum-remainder release: `import all Module.Name` is a Lean import with an
`all` modifier, not an import of a module called `all`. The original scanner
failed when a required external module was absent from the local cache.
In addition, a direct compilation of a missing Mathlib module must use its
fixed Lake options `autoImplicit=false` and `maxSynthPendingDepth=3`. A fresh
compile of `Mathlib.RingTheory.TensorProduct.Maps` fails with the defaults and
passes with these official options; they affect elaboration, not kernel trust.
Cached modules may themselves import an absent dependency, so the adapter
also traverses their pinned source imports. It uses the separately SHA-pinned
comment/string-aware scanner from the simplex release: comment delimiters in
Lean string literals must not be parsed as actual comments.
All pinned package caches, including Batteries, are merged into the overlay.
Lean selects an entire module root, so a partial overlay must not hide cached
sibling modules in a later package root.

The adapter pins the original verifier's SHA-256 and runs that verifier with
its import-scanning function replaced, cached import closures traversed, and
the single external Mathlib compile call supplied with those options.
Its original full release seal,
toolchain/source pins, fresh owned-module build, axiom checks, semantic
controls and two empty-kernel replays remain active. It neither updates a
historical seal nor substitutes cached owned proof objects for source.

From repository root, with the pinned Lean 4.34.1 environment:

```sh
python3 -B verification/finalization/replay_continuum.py \
  --lean-bin /path/to/lean-4.34.1/bin \
  --dependency-project /path/to/pinned-dependency-project \
  --output /outside/repository/new-run
```

Use a fresh external output directory. The original reproduction instructions
remain an immutable historical record; use this adapter for a cache-miss
replay with current pinned sources. A passing final report, not merely an
import or successful dependency scan, establishes completion of the suite.

The [compiler-option diagnostic](results/continuum-build-options.json) records
both failures and successes against the same pinned Mathlib source. The
[import controls](results/continuum-import-controls.json) compare four scanner
cases with Lean's own `--deps`, with identical normal/optimized output:

```sh
python3 -B verification/finalization/check_continuum_imports.py \
  --lean-bin /path/to/lean-4.34.1/bin
```

Earlier aborted runs are retained as reproduction diagnostics:
[default-option failure](results/continuum-default-mathlib-options-failure.txt)
and [incomplete-cache failure](results/continuum-incomplete-transitive-cache-failure.txt).
The subsequent [shadowed-package failure](results/continuum-shadowed-package-cache-failure.txt)
motivated merging all pinned package caches into the overlay.
These are build failures, not counterexamples to a mathematical theorem.
