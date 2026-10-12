# Bapat's original-interval conjecture: complete complex Hermitian Lean counterexample

Publication date: 2026-10-08 (UTC).

The final theorem is `BapatRankTwo.N200.originalBapatConjecture_false` in
[BapatN200Counterexample.lean](evidence/formalization/sources/BapatN200Counterexample.lean).
It refutes the original strict-monotonicity conjecture for non-diagonal complex
Hermitian positive-definite matrices on `[-1,1]`. The formal proof uses the
published, ordered, 200-row Gaussian-integer data and constructs an existential
strictly positive diagonal shift and two ordered interior real points at which
the actual q-permanent strictly decreases.

The formalized q-permanent sums over all permutations, with the actual inversion
count in the original index order. The proof includes the permanent/Fischer
identity, marked-inversion and two-row-cofactor bridges, ordered wedge recurrence,
exact Gaussian-integer coefficient interpretation, all 200 arithmetic transitions,
negative endpoint derivative, Hermitian reality, non-diagonality, positive-definite
perturbation, and the final interior strict decrease. These are proved bridges,
not unproved hypotheses passed into the last theorem.

## What was verified

The preserved fresh execution records report all 22 modules compiled from their
frozen source bytes. All 928 owned declarations, including generated numerical
checkpoints, were audited without exclusions. Their full transitive dependency
closure of 22,371 declarations was replayed from an empty kernel with trust level
zero. The axiom-name allowlist was `propext`, `Classical.choice`, and `Quot.sound`.
The graph records names and dependency edges, not full upstream declaration ASTs;
name-based allowlisting alone is not an independent axiom-signature check.
The invalid-proof negative control was rejected and shared package-cache checks
passed (path/size/mtime fingerprints, not full dependency byte hashes). The union of the six requested root closures has 21,986 declarations.

A separate publication audit checked source and input correspondence, all graph
closures and axiom sets, the original-to-compact file mapping, and independently
recomputed every coefficient of all 201 states and the final strict integer gap.
It also read the mathematical semantics of the full proof chain. This publication
audit did not rerun Lean; the recorded fresh kernel execution and the subsequent
static/integer audit are distinct layers of evidence.

See the [dated verification report](../../notes/bapat-q-permanent-counterexample/LEAN_VERIFICATION_2026-10-08.md),
the [static/integer audit](audit/AUDIT_REPORT.md), the
[preserved execution result](evidence/formalization/RESULT.json), and the
[lossless public graph/source storage](PUBLIC_PROJECTION.json).

## Precise scope

- This is a complete Lean proof of an existential dimension-200 counterexample
  to the original **complex Hermitian** conjecture.
- The positive-definite shift is an existential real number. This formalization
  does not choose the paper's specified rational epsilon or q0, and does not prove
  that its selected positive-definite witness has rational-complex entries.
- The two strict-decrease points lie in `(-1,1)`; their positivity or prescribed
  numerical values are not asserted by this version.
- The separate CP1 asymptotic argument and the real-symmetric existence theorem
  are not formalized here. No human journal acceptance or historical priority is
  claimed.

The written paper and its stronger explicit rational witness remain in the
[mathematical package](../../notes/bapat-q-permanent-counterexample/README.md).
The historical `q > 1` result is a separate formalization.

## Public payload and provenance

`evidence/` directly retains 137 compact-profile files byte for byte. Three large
Lean trace sources and the existing all-owned graph gzip are distributed in
`lossless-storage/` as 20 ordered parts, each at most 393,216 bytes. The source
parts contain gzip-compressed original bytes; graph parts contain the original
gzip bytes. `PUBLIC_PROJECTION.json` gives every part and every restored file
size/hash. The restore script recovers the exact 141-file compact tree. All 22
restored Lean source files total 13,674,735 bytes and retain their original bytes;
no mathematical source is regenerated or replaced with an algorithm. The CSV is frozen at source commit
`c5d7f68e78b6c80912041c6cf1fd4d3cd950beb6`, with SHA-256
`9d16617d6eb287535a752cf5ef6f3d4672a133812bf0fbd908738a10c223fc25`.

This compact profile is **not** a byte-identical copy of either original full
archive. Its mapping accounts for all 196 files of the original public archive:
87 retained, 43 mechanically projected metadata files, 22 deduplicated source
snapshots, and 44 omitted rebuildable `.olean`/`.ilean` files. The omitted build
products total 250,393,677 bytes. Four JSON evidence files are losslessly gzipped;
the decompressed bytes and original hashes are recorded. Machine-path tokens and
process IDs were mechanically projected in the indicated metadata, without
altering the mathematical proof source. The full archive is not uploaded here.

The preserved `evidence/RESULT` fields and reproduction text describe the
pre-publication execution. Statements there about zero GitHub writes refer to
that earlier execution, not to this later repository publication. Historical
checksum files under `evidence/provenance/` describe the original archive;
`evidence/SHA256SUMS` covers the exact restored compact evidence tree, while
`PUBLICATION_MANIFEST.json` covers the actual distributed public files.

`PUBLICATION_MANIFEST.json` additionally covers the actual public files in this
formalization directory and the dated verification report, excluding itself.
The mutable repository-root README is an index and is deliberately outside that
manifest's scope. No compiled dependency binaries or private execution archive
are included.

## Reproduction

From a checkout of the repository:

```sh
python3 -B formalizations/bapat-q-permanent-counterexample/scripts/check_publication.py
python3 -O -B formalizations/bapat-q-permanent-counterexample/scripts/check_publication.py
```

To restore exact sources and original evidence into a new directory outside
this formalization package:

```sh
python3 -B formalizations/bapat-q-permanent-counterexample/scripts/restore_evidence.py --output /new/path/bapat-evidence
python3 -B /new/path/bapat-evidence/reproduce.py --check-only
```

Restoration verifies every compressed part, its ordered concatenation, all
original bytes, and the preserved compact checksum manifest before reporting
PASS. Use the restored directory for the original reproduction commands; the
public `evidence/` directory deliberately lacks the four separately stored files.

For a fresh independent Lean rerun, follow [REPRODUCE.txt](evidence/REPRODUCE.txt).
The runner requires an existing official Lean 4.34.1 installation at commit
`5045d0056413266e57c625dcd7c365b10e377c52` and the pinned package revisions, including
mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. It neither downloads tools nor
installs or changes the shared package environment. It writes fresh own build
products only into a new work directory and checks all owned declarations.

The recorded result is not a guarantee that an arbitrary local toolchain or
different package revision will reproduce the run. Integrity checks alone are
not a new kernel replay.
