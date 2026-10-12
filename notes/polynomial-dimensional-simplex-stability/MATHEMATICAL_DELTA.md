# Mathematical delta and editorial record

## Mathematical content

There is **no mathematical change from the frozen release basis** in POLYNOMIAL_REFINEMENT.md or SQUARE_PYRAMID_LOWER_BOUND.md. Their complete file hashes are respectively

- 2b398cba3afd73819dbf90d5106e64be64ba06a07f9e42d23f4c2037ff5cd791
- dee887e50590cd750d5b211acd9015fa57db5bd70786dcd67ec701674139596e

The first hash above is checked against SOURCE_FIDELITY.json and the package checker. The independently audited core, starting with `## 1.` and ending immediately before `## 9.`, has SHA-256 94c4e777b0000e5e33e024d59c47e258594fbfacc554e4faa91f8b5264c503f5.

Relative to the earlier sharp proof, preserved as sources/sharp-simplex-proof.tex (SHA-256 9361999cfa4337500041da4b3fc824cd3676a07a22ffad0274e38346bf301b98), the refinement changes the following proved inputs while preserving the invariant, exponent and every-prescribed-maximum-simplex metric:

1. Determinant-weighted selection uses the first absolute lifted determinant V, retaining the singular-tuple indicator. The clipped barycentric bound is paid for by the support diameter, yielding mean assignment cost at most diameter·(d+1)(d+2)(B−A)/(2B), in any norm and without a convex-body realization hypothesis.
2. Prescribed-simplex normalization gives R = d√(d+2), and vertex replacement gives the global excess bound E ≤ d+1.
3. Actual cone-law dispersion follows from Cauchy's formula and fiber integration, giving M = 4dR. This step is not asserted for arbitrary centered laws.
4. Assignment-weight correction and first variation control absolute projection deficits. The projection cap uses the body's radius R, leading to the stated local threshold and retention of the originally prescribed simplex and centroid.
5. The local/global combination gives the exact displayed G_d, with the analytic estimate G_d < 2^20 d^6 for every integer d ≥ 3. The square-pyramid construction gives the stronger necessary lower coefficient (d+1)[d(d+1)]^(1/(d−1)).

This list summarizes the differences from the pinned argument. It is not a novelty or optimal-dimension-growth claim. The exact formulas and proofs in the mathematical files govern.

## Public derivatives and exclusions

The anchor report changes only three source/scope prose passages. The independent audit's bibliographic references are mapped to exact bundled public sources. Its technical Sections 1–7 and square-pyramid calculation in Section 8 are unchanged; one broader construction-class paragraph is explicitly omitted. The original/derivative hashes, sequential line positions, exact fragment hashes and replacement text are recorded in SANITIZATION_LEDGER.json. Original private locators are not reproduced.

The frozen basis's preparation README and private file-list scope metadata are replaced by the public README and narrowed RELEASE_SCOPE.json. No separate anisotropic, simultaneous-truncation, or broader construction-class theorem or checker is included as a claim of this supplement.

The typeset derivative's purely editorial conversions are recorded separately in TYPESETTING_LEDGER.md. It may reflow formulas and add explanatory definitions from the pinned sources; it may not change a hypothesis, quantifier, constant, sign, case split or mathematical conclusion. The complete Markdown remains authoritative.

## Added source accessibility

All four mathematical source copies supplied with the frozen basis remain exact. To resolve an otherwise inaccessible audit reference, entry005 v2 was additionally retrieved at commit 31e3d8a37e4a3051a7f5a2535be1c75642e15bcc and included as sources/entry005-v2.md (SHA-256 8b7ad76a8a4b96ff40d43e9f9c3e7f4fe494dbadcf82bbdc114f980971ffb430). This is a dependency-accessibility addition, not additional release scope. Exact upstream provenance and license copies are retained as documented in SOURCE_PINS.json and NOTICE.md.
