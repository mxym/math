# Bounded step walks on irreducibles in quadratic orders

Current version: **v2**, prepared 7 October 2026.

An all-quadratic-order extension of the planar sieve argument, with infinite-unit exception restoration.

- [Complete PDF](v2/paper.pdf)
- [Editable LaTeX](v2/source.tex)
- [Build and verification status](../../verification/STATUS.md)
- [Upstream source, OpenAI family 028](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Bounded-Step-Walks-on-Gaussian-Primes-September-26-2026/paper.pdf)

## Status

Complete mathematical research draft, checked for stated hypotheses, proof dependencies and limiting cases. No external peer review, complete machine formalization or publication-priority claim is made. Attribution is explicit in the manuscript. Earlier versions are preserved. [Version 1](v1/paper.pdf) remains available; the current version is v2.

## Build

Use a complete TeX Live installation in the `v2` directory:

```sh
pdflatex source.tex
pdflatex source.tex
pdflatex source.tex
```

## Citation

```bibtex
@misc{mxym_math_002_v2,
  title = {Bounded step walks on irreducibles in quadratic orders},
  year = {2026},
  howpublished = {Research manuscript, mxym/math, version 2},
  url = {https://github.com/mxym/math/tree/main/preprints/002-quadratic-order-moats/v2},
  note = {Cite the exact Git commit used; author metadata has not been asserted}
}
```

## Version 2 additions

Added exact finite certificates and a terminating exhaustive-search proof of computability for integral order models and supplied finite coefficient-step sets. No practical runtime guarantee or effective access to arbitrary real metric inputs is claimed. See [the changelog](v2/CHANGELOG.md) and [certificate instructions](v2/certificates/README.md).
