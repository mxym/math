# Exact projection-volume optimization over Cartesian products of simplices

**Read:** [PDF](v1.1/paper.pdf) · [complete LaTeX source](v1.1/build/main.tex) · [proof audit](v1.1/PROOF_AUDIT.md) · [exact certificate](v1.1/verification/exact_certificate.json) · [versioned release](https://github.com/mxym/math/releases/tag/density-simplex-20261007-v1.1)

**First public version:** v1.1, 2026-10-07. The version number records revision of a private draft, not an earlier public disclosure. First source commit: `e6c776cae39477baa4e1a03d59a1547417f1a68e`; compiled release snapshot: `e894ed8678052e45ecd9f1714b6a996cfea33cf3`.

**Attribution:** mxym (repository account), prepared with AI assistance. No institutional affiliation, independent referee review, or proof-assistant verification is asserted.

## Result and scope

The exact optimum in every dimension; a two-candidate balanced-partition formula; a sharp period-thirteen recurrence starting at dimension 100; uniqueness of every optimal dimension multiset; and sharp dimension-mass stability with additive constant 112. The optimal repeated block has dimension thirteen. These statements concern products of simplices and their affine images, not all convex bodies. No proof depends on a private transcript.

## Build and replay

From `v1.1/`:

```sh
(cd build && pdflatex -interaction=nonstopmode -halt-on-error main.tex && pdflatex -interaction=nonstopmode -halt-on-error main.tex)
cp build/main.pdf paper.pdf
python3 verification/verify_exact.py --limit 300 --output verification/exact_certificate.json
```

LaTeX packages: amsmath, amsthm, lmodern, microtype, geometry, hyperref, booktabs and needspace. The standard-library Python verifier uses arbitrary-precision integers and Fraction, never floating-point inequalities or external solvers. The [recorded run](v1.1/verification/run.txt) checks seven strict rational comparisons, eighty finite no-tie cases, and every optimal dimension multiset by independent exhaustive dynamic programming through dimension 300. Explicit exceptions remain active under Python's optimization flag. Infinite-dimensional conclusions also require the analytic proof in the paper.

## Provenance and citation

The product identity, simplex value, and dimension-twenty example are credited to OpenAI, *A product counterexample to the simplex maximum for projection-body volume*, September 24, 2026, family 088, pinned snapshot `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, and rederived in the manuscript. The upstream paper already reports earlier unrestricted counterexamples in all dimensions at least nine. We claim neither the first disproof of Brannen's conjecture nor an unrestricted maximizer. Upstream rights and notices remain applicable; see the root NOTICE and retained Apache-2.0 license. A [post-publication comparison](../../comparisons/2026-10-07-density-simplex.md) records overlaps and limitations without asserting priority.

```bibtex
@misc{mxym2026simplexproducts,
  author = {mxym},
  title = {Exact projection-volume optimization over Cartesian products of simplices},
  year = {2026},
  note = {Research manuscript, version 1.1; AI-assisted; not peer reviewed},
  howpublished = {\url{https://github.com/mxym/math/tree/e894ed8678052e45ecd9f1714b6a996cfea33cf3/preprints/005-simplex-product-optimum}}
}
```

Public disclosure does not certify first discovery. Historical manifests should be checked at their fixed publication commit, because navigation files can subsequently evolve.
