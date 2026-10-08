# Universal orbital primal-dual theorem: complete Lean proof

This package proves the actual universal finite-group action theorem
in [§18 of the sharp robust permanent note](../../notes/sharp-robust-permanent/paper.md).
See [PROOF.md](PROOF.md) for a complete readable proof and the correspondence
between the published symbols and Lean definitions.

The endpoint is [UniversalOrbitalTheorem.lean](UniversalOrbitalTheorem.lean).
It constructs rational optimal class probability laws and orbital dual
coefficients, identifies their value with the actual signed-kernel TV
supremum, and proves the actual group probability bound and disjoint sharp
perturbations. [ClassReduction.lean](ClassReduction.lean) identifies the
matrix with the published conjugacy-class average.
[AllAtoms.lean](AllAtoms.lean) handles sharpness at every atom;
[SpanFormulation.lean](SpanFormulation.lean) proves the actual linear-span
minimum. No faithfulness, transitivity, full-rank or nonzero-optimum
assumption is added to the main theorem.

The rationalization and real dual existence bridges are proved here,
using finite-dimensional linear algebra, rational density and the proved
Hahn–Banach theorem. Missing bridges are not supplied as custom axioms.

This is a complete formal verification of this existing theorem, not a
newly solved famous conjecture. It does not certify the separate explicit
formulas in §§15–17 or the Gaussian results elsewhere in the repository.

The verified run checked **117 owned theorems** and replayed **28,264 used
proof declarations** from an empty kernel. All three positive controls passed;
the omitted-zero-mass false Jordan normalization was rejected. The source
contains no admissions, custom axioms or native-decision oracle. These counts
identify the verification record, rather than measuring mathematical importance.

## Reproduction

Use official Lean `leanprover/lean4:v4.34.1`, commit
`5045d0056413266e57c625dcd7c365b10e377c52`, and the exact nine dependency
revisions in [lake-manifest.json](lake-manifest.json). With a Lake dependency
project containing those packages and their official mathlib build cache:

```bash
python3 formalizations/orbital-primal-dual/replay.py \
  --lean /path/to/leanprover--lean4---v4.34.1/bin/lean \
  --dependency-project /path/to/dependency-project \
  --output /path/to/new-output-directory
```

The output directory must not exist. The script checks dependency revisions,
assembles only the frozen owned source into a fresh compilation unit,
compiles it without an owned `.olean` cache, audits every owned theorem's
axioms, and replays their entire dependency closure into an empty kernel
at trust level zero. The final checked theorem types and universe parameters
must be unchanged. The replay permits only `propext`, `Classical.choice`
and `Quot.sound`; it rejects unsafe/partial proof dependencies and all
other axioms. The replay collector is a metaprogram, outside the theorem
proof closure.

Three positive controls and one rejected omitted-hypothesis control are
included. [MODULES.json](MODULES.json) fixes the owned source order.
The ordinary per-module Lake build is also configured; fresh bundle
compilation avoids repeatedly loading the same large mathlib environment
and records the hashes of every original source file.

Recorded evidence is in `verification/`.
The [rational-witness review](reviews/rational-witnesses.md) and
[endpoint review](reviews/endpoint.md) identify exact source hashes; their
original scratch paths correspond byte for byte to the files in this package. A successful
script exit alone is not the mathematical argument: the readable proof,
actual Lean statements, source hashes, axiom report and empty-kernel
replay are all public for inspection. Semantic reviews explicitly identify
their scope and do not claim outside professional peer review.
