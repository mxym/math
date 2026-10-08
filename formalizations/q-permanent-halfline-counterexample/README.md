# q-permanent half-line counterexample: Lean formalization

This directory publishes the complete explicit four-dimensional counterexample,
its Lean sources, the recorded fresh-build/kernel-replay evidence, and a separate
static semantic and exact-arithmetic review. It supplements the
[written proof](../../notes/q-permanent-halfline-counterexample/PROOF.md).

## What is proved

The matrix is the real image of the rational matrix

```
[       1  -99/100  0  1/500 ]
[ -99/100        1  0    1/8 ]
[       0        0  1      0 ]
[   1/500      1/8  0      1 ]
```

`qPermanent` sums over every permutation, using the actual inversion number
of the permutation in the original order of all four indices. The isolated
third coordinate is retained. The proof uses the genuine mathlib
`Matrix.PosDef` predicate and proves the matrix is not diagonal.

The exact values are

- `P(49) = 81807513 / 500000`
- `P(50) = 7969 / 50`
- `P(49) - P(50) = 2117513 / 500000 > 0`

Consequently, for every real `a ≤ -1`, the q-permanent is not `MonotoneOn`
on `[a, ∞)` and not `StrictMonoOn` on `(a, ∞)`. The universal conjecture
requiring some `a < -1` for every non-diagonal real positive-definite matrix
is false. The source proves the stronger endpoint bounds `a ≤ 49` for the
closed/nondecreasing version and `a < 49` for the open/strict version.

Formal roots in namespace `QPermanentHalfline`:

- `explicit_counterexample`
- `halfLineConjecture_false`
- `counterexampleMatrix_posDef`
- `counterexampleMatrix_exact_decrease`

This Lean formalization does not establish dimension-four minimality, an
`n ≤ 3` theorem, the separate family for every `t > 1`, or Bapat's original
interval `[-1,1]`. It makes no priority or novelty claim.

## Recorded verification and attribution

The Lean proof producer ran the recorded verification on 2026-10-08 UTC:

- All four owned modules were compiled from source into a new build directory.
- All 26 owned declarations, including generated/private declarations, were
  audited. No mathematical module was excluded.
- Their 13,134-declaration transitive closure was replayed in an empty
  trust-level-zero kernel environment. The four requested roots have a union
  of 13,131 declarations.
- The only closure axioms were `propext`, `Classical.choice`, and `Quot.sound`.
- The outer audit rejects unsafe/partial declarations and nonstandard axioms
  before replay. A separate malformed proof of `False` was rejected.

The independent reviewer checked source meaning, recorded hashes and graph
closure, all 24 permutations using exact rational arithmetic, and a positive
`UᵀDU` factorization. That reviewer did not install, compile, or rerun Lean.
The publication step likewise does not claim a new Lean execution.
See [independent review](audit/independent_review.json),
[recorded replay summary](fresh-verification/manifest/replay-summary.json),
[commands](fresh-verification/manifest/commands.json), and
[logs](fresh-verification/logs/).

Trust level zero comes from `mkEmptyEnvironment 0`. In the pinned
`Lean.Kernel.Environment.replay` implementation, the zeros in `addDeclCore 0 0`
are resource-limit parameters (`maxHeartbeats` and `maxRecDepth`), not the
trust-level setting. `Lean.Replay` alone can skip unsafe/partial declarations
and permits axiom declarations; the outer rejection checks, empty-base check,
and final presence/type/level checks are essential parts of this evidence.
The audit harness contains partial implementation traversals outside the
mathematical declarations. The verifier, Lean implementation, compiler/runtime,
and other infrastructure have not themselves been formally verified here.

## Exact pins

- Lean 4.34.1: `5045d0056413266e57c625dcd7c365b10e377c52`
- mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`
- All transitive package revisions, operational paths, and build parameters:
  [PUBLIC_ENVIRONMENT_CONFIG.json](PUBLIC_ENVIRONMENT_CONFIG.json)
- Selected upstream interfaces and their Git/SHA256 identities:
  [source metadata](audit/upstream/source_metadata.json)

## Verify the public copy without Lean

Run from this directory, with Python 3 and the standard library:

```sh
python3 check_public.py
sha256sum -c SHA256SUMS
```

The default check validates the complete public file inventory and hashes,
the 37 unchanged files in the historical fresh-run manifest, the published
configuration projection, source/control consistency, the dependency graph,
reference hashes, pinned interface hashes, and exact rational arithmetic.
It does not execute Lean. It emits results without modifying historical logs.
`CURRENT_PUBLIC_MANIFEST.json` lists every payload file; `SHA256SUMS` also
checks that manifest. Neither file pretends to hash itself.

## Reproduce the Lean verification

The original checker and control sources are published unchanged under
`verifier/`. The following wrapper uses an existing pinned toolchain and
existing compiled dependency checkouts; it performs no downloads or installation:

```sh
python3 reproduce_lean.py \
  --toolchain /absolute/path/to/lean-4.34.1 \
  --packages-root /absolute/path/to/pinned-dependencies \
  --workdir /absolute/path/to/new-qpermanent-run \
  --run
```

The dependencies directory must contain the package names in the public
configuration (including `mathlib`, `aesop`, `batteries`, `Qq`, and the other
listed packages), checked out at the exact revisions, with their compiled
`.lake/build/lib/lean` libraries. The wrapper creates a separate workspace,
relocates only operational paths, runs `doctor`, then compiles all four owned
modules fresh and runs the original closure/replay/negative checks. Omit
`--run` to prepare the workspace only. Do not place it inside this evidence
snapshot. Missing assets must be obtained from the official upstreams in the
public configuration; they are not bundled here.

For ordinary Lake use, `project/lean-toolchain` and `project/lakefile.toml`
provide the Lean/mathlib pins. A successful `lake build` alone is not the
additional all-owned empty-kernel replay. The recorded run used the direct
Lean commands retained in `fresh-verification/manifest/commands.json`.

## Public-copy provenance and limits

The original input archive was 1,243,043 bytes, SHA256
`d0d3fcbb6da11ed7a4378d14f7e95288f7de2553f100a1568b2e7b548f1a8f4e`.
This directory is a selected public copy, not an unchanged republication of
that archive. [PUBLICATION_MAPPING.json](PUBLICATION_MAPPING.json) records the
exact source-to-public mapping and configuration projection.

Every mathematical source, checker, original build artifact, compile/kernel
log, and other historical fresh-verification manifest is preserved byte for
byte. The one exception is the original environment configuration: two
non-mathematical administrative identifiers were omitted, and its remaining
fields are published as `PUBLIC_ENVIRONMENT_CONFIG.json`. The equivalent
second copy under `verifier/config/` is replaced by the same public file.
The retained fields were compared programmatically with the originals; the
original hash and canonical retained-field hash are recorded in the mapping.

The historical 38-entry checksum list is preserved byte for byte as
`fresh-verification/manifest/SHA256SUMS.original`: 37 original files remain,
and the configuration entry maps to the explicit public projection. That
historical list describes the execution package; use the current top-level
`SHA256SUMS` and default check for this public delivery. Internal recovery
notes, unrelated operational status, large dependency caches, and credentials
are not included. Historical absolute paths are evidence of the original run,
not paths the reader must recreate.

No applicable q-permanent GitHub Actions verification workflow is supplied
by this publication. Recorded local evidence must not be described as a green
GitHub CI run.
