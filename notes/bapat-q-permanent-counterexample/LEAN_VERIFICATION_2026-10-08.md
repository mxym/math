# Lean verification: Bapat's original complex Hermitian conjecture

Date: 2026-10-08 (UTC).

The [complete Lean source and public verification evidence](../../formalizations/bapat-q-permanent-counterexample/README.md)
now supply a formal proof of a dimension-200 counterexample to the original
strict-monotonicity conjecture for non-diagonal complex Hermitian positive-definite
matrices on `[-1,1]`. The final theorem is
`BapatRankTwo.N200.originalBapatConjecture_false`.

This supplements the [written counterexample package](README.md). The paper's
explicit rational perturbation and numerical q0 bounds are stronger witness
specifications than this Lean version proves. They should not be conflated.

## Formal statement and mathematical chain

The source defines the q-permanent by summing over **all** permutations, weighted
by their true inversion counts in the original index order. It proves Hermitian
reality, so the real-valued analytic formulation using the real part is exact.
The ordered 200-row CSV is interpreted as an actual complex Gram matrix, and its
nonzero off-diagonal entry is proved to be `398 - I`.

The generic argument proves the marked-inversion, two-row-cofactor,
permanent/Fischer, ordered wedge-sum, and sequential coefficient-recurrence
identities. Gaussian-integer list arithmetic is connected to the actual complex
polynomials. All 200 state transitions and the final positive integer norm gap
are kernel proofs. These imply a strictly negative derivative at q=1. Continuity
then produces a strictly positive real diagonal perturbation and a strictly
decreasing pair of points in `(-1,1)`. Positive definiteness and non-diagonality
are both included in the final existential theorem.

The Lean conclusion does **not** select the paper's particular epsilon or q0,
does not assert rational-complex entries for its chosen positive-definite
matrix, and does not assert that the interior points are positive. It does not
formalize the separate CP1 asymptotic proof or the later real-symmetric existence
theorem. No historical-priority or human journal-acceptance claim is made.

## Recorded fresh execution

- 22 source modules, with all frozen source hashes preserved.
- 928 owned declarations: 639 theorems and 289 definitions; no owned exclusions.
- 22,371 declarations in the entire owned transitive dependency closure.
- Empty-base replay, trust level 0, recorded status PASS.
- The axiom-name allowlist is `propext`, `Classical.choice`, and `Quot.sound`.
  The graph does not encode full upstream declaration ASTs, so this is not an
  independent per-expression check of those three axiom signatures.
- All six requested root closures jointly contain 21,986 declarations.
- The final negation root has 21,963 dependencies including itself; the explicit
  existential root has 21,962; derivative root 13,345; Fischer identity 11,748;
  Hermitian reality bridge 9,759; and integer-gap root 1,775.
- The invalid-proof negative kernel control was rejected. Shared pinned package
  cache checks passed, using path/size/mtime fingerprints rather than full
  dependency-content hashes.

The authentic recorded logs, commands, environment pins, complete declaration
inventory and compressed dependency graph are under
[`fresh-verification`](../../formalizations/bapat-q-permanent-counterexample/evidence/fresh-verification).
See the [replay summary](../../formalizations/bapat-q-permanent-counterexample/evidence/fresh-verification/manifest/replay-summary.json)
and [formal scope](../../formalizations/bapat-q-permanent-counterexample/evidence/formalization/FORMAL_SCOPE.txt).

## Independent publication audit

A separate [static, semantic, provenance and exact-integer audit](../../formalizations/bapat-q-permanent-counterexample/audit/AUDIT_REPORT.md)
checked the final published inputs. It independently reconstructed all graph
closures and all 928 transitive axiom sets, compared every CSV coordinate in order,
recomputed every coefficient in all 201 checkpoints, checked the 200-step chain,
and recovered the final strict integer gap. It compared the source definitions
and final quantifiers with the original conjecture's published statement, and
read the actual proof bridges.

It also checked the full-to-compact byte mapping, retained source bytes, lossless
graph compression, machine-path substitutions, and preserved execution records.
This is separate from the earlier fresh Lean execution. No new Lean installation,
compilation or kernel replay was performed solely for auditing or publication.
The public audit scripts use explicit checks that remain active with Python `-O`.

## Public-copy identity and reproducibility

The Lean input corresponds to the mathematical source at commit
`c5d7f68e78b6c80912041c6cf1fd4d3cd950beb6`. The ordered CSV has SHA-256
`9d16617d6eb287535a752cf5ef6f3d4672a133812bf0fbd908738a10c223fc25`.
The compact input archive had 8,022,381 bytes and SHA-256
`499d5391a0989f68a2cbc49acebd3af92911bf967b0769f60c0fbc7c5099928e`.

The public payload retains 137 compact files directly and stores three large
Lean trace sources plus the all-owned graph gzip as 20 lossless parts of at most
393,216 bytes. The restore script strictly checks part, compressed-stream and
original-byte identities, then reconstructs the exact 141-file compact tree.
It never regenerates source declarations from an algorithm.
This is a compact reproducible profile, **not** a claim that the original full
archive is reproduced byte for byte. All 196 original-public-archive files are
accounted for: 87 retained, 43 metadata projections, 22 source deduplications,
and 44 omitted rebuildable compiler outputs totaling 250,393,677 bytes.
The compressed graph files expand to their original bytes. The 22 mathematical
source files total 13,674,735 bytes and were not changed.

The [public manifest](../../formalizations/bapat-q-permanent-counterexample/PUBLICATION_MANIFEST.json)
covers the actual public payload and this report with per-file size, SHA-256 and
Git blob identity. It excludes itself and the mutable root README. Historical
full-archive checksum files are separately labeled and are not presented as
checksums of the compact tree. Reproduction uses the recorded official Lean
4.34.1 commit and pinned mathlib/package revisions; see
[REPRODUCE.txt](../../formalizations/bapat-q-permanent-counterexample/evidence/REPRODUCE.txt).
