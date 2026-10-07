# Exact projection-volume optimization over Cartesian products of simplices

**First public version:** v1.1, 2026-10-07. The version number records revision of a private draft, not an earlier public disclosure.

**Attribution:** mxym (repository account), prepared with AI assistance. No institutional affiliation, independent referee review, or proof-assistant verification is asserted.

## Result and scope

The exact optimum in every dimension; a two-candidate balanced-partition formula; a sharp period-thirteen recurrence starting at dimension 100; uniqueness of every optimal dimension multiset; and sharp dimension-mass stability with additive constant 112. The optimal repeated block has dimension thirteen. These statements concern products of simplices and their affine images, not all convex bodies.

The [complete LaTeX source](v1.1/build/main.tex) contains the geometric reduction, analytic argument, finite comparisons and references. No proof depends on a private transcript. See the [proof audit](v1.1/PROOF_AUDIT.md). The build produces `v1.1/paper.pdf`.

## Build and replay

From `v1.1/`:

```sh
(cd build && pdflatex -interaction=nonstopmode -halt-on-error main.tex && pdflatex -interaction=nonstopmode -halt-on-error main.tex)
cp build/main.pdf paper.pdf
python3 verification/verify_exact.py --limit 300 --output verification/exact_certificate.json
```

LaTeX packages: amsmath, amsthm, lmodern, microtype, geometry, hyperref, booktabs and needspace. The standard-library Python verifier uses arbitrary-precision integers and Fraction, never floating-point inequalities or external solvers. It checks seven strict rational comparisons, eighty finite no-tie cases, and every optimal dimension multiset by independent exhaustive dynamic programming through dimension 300. Explicit exceptions remain active under Python's optimization flag. Infinite-dimensional conclusions also require the analytic proof in the paper.

## Provenance and citation

The product identity, simplex value, and dimension-twenty example are credited to OpenAI, *A product counterexample to the simplex maximum for projection-body volume*, September 24, 2026, family 088, pinned snapshot `adc7f1241b42e322a6451854ab7e4b4c146bf78a`, and rederived in the manuscript. The upstream paper already reports earlier unrestricted counterexamples in all dimensions at least nine. We claim neither the first disproof of Brannen's conjecture nor an unrestricted maximizer. Upstream rights and notices remain applicable; see the root NOTICE and retained Apache-2.0 license.

```bibtex
@misc{mxym2026simplexproducts,
  author = {mxym},
  title = {Exact projection-volume optimization over Cartesian products of simplices},
  year = {2026},
  note = {Research manuscript, version 1.1; AI-assisted; not peer reviewed},
  howpublished = {\url{https://github.com/mxym/math/tree/main/preprints/005-simplex-product-optimum}}
}
```

Replace `main` by the exact publication commit for reproducible citation. Public disclosure does not certify first discovery. Literature-priority comparison remains separate.
