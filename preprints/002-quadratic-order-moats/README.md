# Bounded step walks on irreducibles in quadratic orders

Version **v3**, prepared 7 October 2026.

An all-quadratic-order extension of the planar sieve argument, with infinite-unit exception restoration and exact finite certificates.

- [Complete PDF, 26 pages](v3/quadratic_order_moat_v3.pdf)
- [Editable LaTeX](v3/source.tex)
- [Version 3 files and reproduction instructions](v3/README.md)
- [Mathematical changes](v3/CHANGELOG_v3.md)
- [Exact certificate instructions](v3/certificates_v3/README.md)
- [Build and verification status](../../verification/STATUS.md)
- [Historical version 2 PDF](v2/paper.pdf) and [source](v2/source.tex)
- [Historical version 1 PDF](v1/paper.pdf) and [source](v1/source.tex)
- [Upstream source, OpenAI family 028](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-Step-Walks-on-Gaussian-Primes-September-26-2026/paper.pdf)

## Version 3 scope

The main all-quadratic-order existence theorem and A1–A5 analytic interface are unchanged. New finite certificates permit individual nonzero nonunit principal generators, including ramified norm-prime and composite-norm cases. Two adjugate congruences determine ideal membership, and the least scalar period is |N(alpha)|/gcd(a,b). Exact quotient-component sizes and selected norm values yield stronger conservative integer restoration bounds.

Complete four-step/eight-step examples give full irreducible component bounds of 20/92820 for Z[i] and 179200/351232 for Z[sqrt(2)]. These are upper bounds, not optimal component sizes. The failed Q30 Gaussian eight-step candidate has an explicit nonzero-voltage walk; the Q130 certificate succeeds. Failure concerns the avoiding sieve and does not imply an infinite irreducible walk.

The 41 norm-prime tests, 24 general-principal tests, independent finite-lift/direct-multiplication reconstructions, and 184-generator arithmetic checks pass. Finite tests do not prove the general analytic theorem. Computability is proved only for integral order models and supplied finite coefficient-step sets. The bounded programs do not implement unrestricted search and make no practical-runtime or arbitrary-real-input effectiveness claim.

## Build

Use a complete TeX Live installation in the v3 directory:

```sh
pdflatex source.tex
pdflatex source.tex
```

The source includes its bibliography and needs no external figures or bibliography database. Build output is source.pdf; the frozen supplied PDF is quadratic_order_moat_v3.pdf. The supplied SHA256SUMS checks the frozen version-3 files.

## Status and citation

Research proof draft with explicit upstream attribution. No external peer review, complete machine formalization, publication-priority claim, or personal authorship assertion is made. Versions 1 and 2 remain byte-for-byte preserved. Cite the exact version and Git commit actually used.
