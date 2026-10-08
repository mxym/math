# A sharp target-atom budget at the critical boundary

[Read the reviewed 7-page paper](paper.pdf), its [unchanged TeX source](paper.tex), or the longer [written proof](PROOF.md).

## The joint atom-budget and distance statement

Fix p > 2, d >= 2 and the normalized critical source specified in the paper. Write s = p/(p-2). Each target may have at most N distinct positive-mass atoms and p-th moment at most one; locations and weights may both vary. Here Omega_N(w) is the supremum of the L^2(rho) distance between the two Brenier maps when their targets have W_2 distance at most w.

Using the explicitly imported potential estimate (P), the written theorem gives

    Omega_N(w) ~ w^(1/3) min{N, log(e/w)}^(1/(3s))

uniformly for every integer N >= 2 and all 0 < w <= w_0. The two comparison constants and w_0 depend on p, d and the fixed source, but not N. For N = 1 the exact formula is Omega_1(w) = min{w, 2} for every w >= 0.

The increment is the sharp joint N,w law, including the separate two-atom case and the fixed-N small-distance regime. The critical source and lower constructions are inherited from manuscript 008; the upper bound imports (P) from manuscript 001 v3, Theorem 1.1. The lower bounds do not use (P). This note does not reprove the upstream potential theorem or claim a new mechanism for the unrestricted critical logarithm.

- [001 v3: imported potential theorem (P)](https://github.com/mxym/math/blob/5c6c088aa5abf1c1a4bdca6a8ce5beaa27faaef3/preprints/001-strongly-log-concave-brenier/v3/manuscript.tex)
- [008: critical source and inherited two-atom/multistrip constructions](https://github.com/mxym/math/blob/c2281bc871c9bf60994985d6665ae45f4711d080/preprints/008-density-overlap-phase/v1/main.tex)
- [Source-overlap and target-tail synthesis](https://github.com/mxym/math/blob/c2281bc871c9bf60994985d6665ae45f4711d080/notes/transport-source-tail-synthesis/synthesis.tex)
- [Recorded upstream-link checks](UPSTREAM_REFERENCES.json)

No minimum atom weight or common fixed target support is assumed. There is no arbitrary-source classification, slowly varying boundary theorem, exact optimal numerical coefficient, or proved asymptotic limit.

## Review and provenance

The [independent model review of the written argument](review/PARENT_INDEPENDENT_REVIEW.md) reports PASS with the explicit imported premise (P). The [final-copy record](review/FINAL_COPY_REVIEW.json) records comparison of the final text and inspection of all seven rendered pages. These are written-proof and document checks, not Lean verification, external human peer review or novelty certification. Literature equivalence screening remains incomplete.

The five reviewed deliverables are byte-preserved. The opening status line in PROOF.md records an earlier pre-review checkpoint and is retained for source identity; the review records and this guide describe the completed review. The source's blank author field is unchanged, and this publication assigns no new authorship or blanket license.

[The earlier TeX](history/paper-v1.tex) and [exact final correction](history/paper-v1-to-final.diff) preserve the stray-comma and PDF-bookmark fixes. They do not change the independently reviewed mathematical argument. [SOURCE_MAP.json](SOURCE_MAP.json) lists unchanged inputs, the new public tooling/guide, and omitted unrelated or machine-local material.

## Reproduction

Python 3 is sufficient for frozen-file and exact-diff checks:

    python3 -B verify.py
    python3 -O -B verify.py

To perform an isolated three-pass PDF rebuild in a new directory outside this package:

    sh build.sh /tmp/critical-atom-budget-build

This needs local pdfLaTeX, kpsewhich, pdftotext and the TeX packages used by paper.tex. The builder does not download packages or enable shell escape. On minimal Debian TeX installations it can generate an isolated format and font maps from already installed files. Generated files stay outside the sealed package.

The check compares every extracted text byte and all seven page breaks with the preserved reviewed PDF. PDF timestamps and engine metadata can differ, so it does not claim regenerated PDF binary identity. The delivered PDF is never overwritten. The [integration record](review/INTEGRATION_CHECKS.json) gives the actual publication checks.

MANIFEST.json and SHA256SUMS bind the payload. They are consistency records, not signatures; use a trusted repository commit or externally obtained archive digest for authenticity. These checks neither re-audit the infinite mathematical proof nor establish the imported premise (P).
