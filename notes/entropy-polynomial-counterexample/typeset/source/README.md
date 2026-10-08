# Entropy polynomial counterexample

Version 1.0, 8 October 2026.

## Complete mathematical claim

Wakhare's Conjecture 2 in Journal of Approximation Theory 307 (2025), article 106143, is false. For the coprime pair (k,r)=(11,10), the polynomial defined there has at least four distinct roots in (0,1). The three-page paper gives a finite exact proof by five rational sign evaluations and the intermediate value theorem.

This package does not claim exactly four roots, a refutation of the associated binary-entropy inequality, or a resolution of Frankl's conjecture. The associated entropy inequality was proved by Boon Suan Ho in January 2026. No exhaustive priority or novelty claim is made.

## Contents

- paper.pdf: the complete three-page mathematical proof
- paper.tex: editable LaTeX source
- check_certificate.py: minimal exact integer verifier, including reconstruction of the coefficients from the original finite sums
- certificate.json: full exact numerators, denominators, and positive residuals for (11,10)
- crosscheck_20_19/: an additional coprime counterexample, checked directly from the original sums using rational isolation of alpha
- SOURCES.md: precise source identities and scope
- SHA256SUMS: SHA-256 hashes of this release's files
- build.sh: ordinary LaTeX reproduction command

## Verify

Use Python 3.8 or later, with no third-party packages and without optimization flags:

    python3 check_certificate.py
    python3 crosscheck_20_19/check.py
    sha256sum -c SHA256SUMS

The first verifier uses integer arithmetic only. The cross-check uses exact standard-library Fraction arithmetic. Neither uses floating-point signs, a computer algebra system, or a numerical root finder.

The mathematical inference after the finite checks is explicit in the paper: p changes sign in each of four pairwise disjoint open intervals, so it has four distinct roots. A root-counting algorithm or a claim that the roots are simple is unnecessary.

## Build the PDF

On a working TeX Live installation with the standard packages listed in paper.tex:

    sh build.sh

The PDF is a typeset presentation of the same finite proof. The proof does not depend on a particular PDF renderer. The distributed PDF was rendered and every page inspected for clipping, legibility, and missing formulas.

## Publication

This is a local release package. It has not been submitted to a journal, uploaded to a public repository, or sent to the cited authors by this workflow. Source attribution is given in the paper and SOURCES.md.
