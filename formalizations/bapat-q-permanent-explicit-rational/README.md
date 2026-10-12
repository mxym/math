# Bapat's original conjecture: complete specified rational Lean witness

This separate version proves the written paper's **specified** complex Hermitian
dimension-200 counterexample, including its exact rational epsilon and q0.
The earlier [existential formalization](../bapat-q-permanent-counterexample/README.md)
remains frozen with its original scope.

The actual main theorem is
[`BapatExplicit.explicit_rational_counterexample`](N200Explicit.lean).
There are no negative-endpoint, norm-identity, or certificate hypotheses in that
theorem. It proves that the actual matrix B is positive definite and
non-diagonal, that the specified q0 lies in (0,1), and that

\[
 P_{q_0}(B)-P_1(B)\ \ge\ \frac{h}{8}>0.
\]

Here P is the actual inversion-weighted sum over all permutations in the
published row order. The parameters are

\[
 \Gamma=19900\cdot200!\cdot200\cdot1601^{199},\qquad
 K=19900\cdot19899\cdot200!\cdot1601^{200},
\]
\[
 \varepsilon=1/(4\Gamma),\quad h=1/(8K),\quad q_0=1-h,\quad
 B=VV^*+\varepsilon I_{200}.
\]

V is the actual two-column Gaussian-integer matrix from the ordered published
CSV. [`explicitMatrix_rational_entries`](N200RationalEntries.lean) proves rational
real and imaginary parts, and [`explicit_qPermanent_real`](N200Explicit.lean)
proves real-valuedness for real q. The actual unconditional
`original_conjecture_false_from_explicit` refutes the original strict-monotonicity
conjecture on [-1,1]. See the [definition-by-definition proof](PROOF.md),
[independent model-conducted semantic review](BAPAT_EXPLICIT_SEMANTIC_REVIEW.md),
[author self-review](SEMANTIC_REVIEW.md), and the
[written finite witness](../../notes/bapat-q-permanent-counterexample/proof.md).

## Verified scope

The six new source modules have 30 owned theorems. The execution record checks
fresh source compilation, every owned theorem's axiom dependencies, and the
complete transitive closure of all 30 theorem roots: 22,812 declarations
replayed from an empty kernel with trust level zero. The execution record is in
[`verification/report.json`](verification/report.json). Only `propext`,
`Classical.choice`, and `Quot.sound` are allowed. A materially false bound on
the actual data is required to fail under `decide +kernel`.

The recorded execution reuses the completed fresh source builds of both input
proof packages. The original 22-module finite certificate completed source
compilation, all 928 owned-declaration axiom checks and dependency-graph
generation, but its original reproducer then hit its 30-minute timeout. That
failed execution is retained and is **not** relabelled PASS. A separate
[`verify_original_input.py`](verify_original_input.py) continuation checks the
completed build and replays all 928 owned declarations in one union (22,371
dependencies), with a false-proof control. The continuation verifies that its
root list equals the actual declarations owned by all 22 imported modules.
This avoids repeated individual traversals without reducing proof coverage.

A separate [standard-axiom signature audit](verification/axiom-signatures/report.json)
checks the actual complete types, universe parameters, declaration kind and
safety of the three allowed axioms loaded with this verified bundle. All 13
deliberately altered signatures/kinds/universes/safety flags were rejected.
The checker is adapted, with attribution, from the original package's
[standard-axiom supplement](../bapat-q-permanent-counterexample/standard-axioms-addendum-v1/README.txt).
This supplemental execution checks foundations and does not count as another
mathematical kernel replay.

The universal 52-theorem explicit perturbation package separately completed
its fresh run (21,571 declarations). The new runner checks the source
inventories, successful continuation/run evidence, compiler identity and
package revisions, then freshly compiles and fully replays the new bridge. The new
proof closure includes imported proof dependencies; imported mathematical
theorems are not converted into additional axioms. The report preserves the
exact hashes of the 23 imported owned build artifacts.

The optional default orchestration launches both input runners and, if the
original reproducer fails after its completed source/audit stages, requires a
successful full continuation. If a source compile or audit failed, the
continuation rejects the input. The recorded new execution uses the explicitly
stated reuse-and-continuation mode. This default orchestration combination is
not claimed to have received another complete end-to-end run.

This establishes the specified **complex Hermitian** witness. The separate
real-symmetric theorem, asymptotic existence proof and all other repository
results are outside this record. No external human peer review, journal
acceptance, first-proof claim, or automatically established historical priority
is asserted.

## Sources and independent reproduction

The six modules are ordered in [`MODULES.json`](MODULES.json). Their proof order
is definition correspondence, rational constants, actual coordinate/entry
bounds, rational entries, actual endpoint unit gap, and the unconditional main
counterexample. No own mathematical source uses an added axiom, `sorry`,
`native_decide`, unsafe code, or a postulated analytic bridge.

Use official Linux x86_64 Lean 4.34.1 at commit
`5045d0056413266e57c625dcd7c365b10e377c52` and the nine exact package revisions
in [`lake-manifest.json`](lake-manifest.json), including mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`. The official pinned Lean binary SHA-256
is `e8baaa71855a616dc351028f3ad2200051b0671f423a1696a100e809302d5550`.
The runner does not install or modify the shared dependency cache. A dependency
project must already have the pinned packages and relevant official build
cache available. Output directories must be new.

To check correspondence of the preserved source and execution record:

```sh
python3 -B formalizations/bapat-q-permanent-explicit-rational/check_record.py
python3 -O -B formalizations/bapat-q-permanent-explicit-rational/check_record.py
python3 -B formalizations/bapat-q-permanent-explicit-rational/verify_axiom_signatures.py --check-record
```

These commands verify evidence integrity; they do not run Lean. To compile and
replay the actual proofs independently, including fresh input builds:

```sh
python3 -B formalizations/bapat-q-permanent-explicit-rational/replay.py \
  --lean /path/to/lean-4.34.1/bin/lean \
  --dependency-project /path/to/pinned-dependency-project \
  --output /new/path/explicit-rational-run
```

Alternatively, provide both completed input runs with
`--original-proof-run /path/to/original-run` and
`--parameter-proof-run /path/to/parameter-run`. For a source build whose original
reproducer timed out, first run the complete continuation:

```sh
python3 -B formalizations/bapat-q-permanent-explicit-rational/verify_original_input.py \
  --lean /path/to/lean-4.34.1/bin/lean \
  --dependency-project /path/to/pinned-dependency-project \
  --proof-run /path/to/completed-original-source-run \
  --repository /path/to/math-checkout \
  --output /new/path/original-continuation
```

Then add `--original-proof-continuation /new/path/original-continuation` to the
paired-input replay command. The input directories must contain actual source
build products and execution evidence, not binary-free public evidence trees.
The runner validates and records reuse/continuation, then performs a fresh new source compile, axiom
audit, complete empty-kernel replay, and negative control. No previously built
new-bridge artifact is imported. Source, compiler, inputs, generated checker
sources, command exits, and log hashes are retained in the resulting record.

An already running continuation may be supplied with
`--await-original-proof-continuation`. This overlaps the new independent
bridge kernel check with the original input kernel check. The runner emits an
overall PASS only after the continuation completes successfully and its actual
source/build/evidence hashes are validated. Both input artifacts and all new
mathematical source bytes are checked again before the final report.

After reproducing the proof with paired input directories, the supplemental
signature audit can be rerun using the same paths:

```sh
python3 -B formalizations/bapat-q-permanent-explicit-rational/verify_axiom_signatures.py \
  --lean /path/to/lean-4.34.1/bin/lean \
  --dependency-project /path/to/pinned-dependency-project \
  --proof-run /path/to/new-explicit-rational-run \
  --original-proof-run /path/to/completed-original-source-run \
  --parameter-proof-run /path/to/completed-parameter-run \
  --output /new/path/signature-audit
```

The supplemental runner requires correspondence with the frozen successful
proof report and its source and imported artifact hashes. It freshly compiles
the signature checker and tests the loaded standard axioms; its `--check-record`
mode only checks preserved evidence integrity.
