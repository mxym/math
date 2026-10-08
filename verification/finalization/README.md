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

## Continuum cache-miss repair

`replay_continuum.py` corrects one dependency-scanning defect in the sealed
continuum-remainder release: `import all Module.Name` is a Lean import with an
`all` modifier, not an import of a module called `all`. The original scanner
failed when a required external module was absent from the local cache.

The adapter pins the original verifier's SHA-256 and runs that verifier with
only its import-scanning function replaced. Its original full release seal,
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
