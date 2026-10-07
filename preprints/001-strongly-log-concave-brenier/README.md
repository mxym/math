# Sharp one-third stability of Brenier maps for strongly log-concave sources

Current version: **v2**, prepared 7 October 2026.

Radius-free centered-potential stability, sharp Gaussian one-third map stability, and a compact log-concave companion theorem.

- [Complete PDF](v2/paper.pdf)
- [Editable LaTeX](v2/manuscript.tex)
- [Build and verification status](../../verification/STATUS.md)
- [Upstream source, OpenAI family 374](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/article.pdf)

## Status

Complete mathematical research draft, checked for stated hypotheses, proof dependencies and limiting cases. No external peer review, complete machine formalization or publication-priority claim is made. Attribution is explicit in the manuscript. Earlier versions are preserved. [Version 1](v1/paper.pdf) remains available; the current version is v2.

## Build

Use a complete TeX Live installation in the `v2` directory:

```sh
pdflatex manuscript.tex
bibtex manuscript
pdflatex manuscript.tex
pdflatex manuscript.tex
```

## Citation

```bibtex
@misc{mxym_math_001_v2,
  title = {Sharp one-third stability of Brenier maps for strongly log-concave sources},
  year = {2026},
  howpublished = {Research manuscript, mxym/math, version 2},
  url = {https://github.com/mxym/math/tree/main/preprints/001-strongly-log-concave-brenier/v2},
  note = {Cite the exact Git commit used; author metadata has not been asserted}
}
```

## Version 2 additions

The potential estimate now covers all finite-second-moment targets. The quantitative map estimate still assumes a common bounded target set. The manuscript also proves curve lifting and an exponential conditional-cell transport inequality. See [the mathematical changelog](v2/CHANGELOG.txt).
