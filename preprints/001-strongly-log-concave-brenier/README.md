# Sharp one-third stability of Brenier maps for strongly log-concave sources

Current version: **v1**, prepared 7 October 2026.

Radius-free centered-potential stability, sharp Gaussian one-third map stability, and a compact log-concave companion theorem.

- [Complete PDF](v1/paper.pdf)
- [Editable LaTeX](v1/manuscript.tex)
- [Build and verification status](../../verification/STATUS.md)
- [Upstream source, OpenAI family 374](https://github.com/openai/math/blob/adc7f1241b42e322a6451854ab7e4b4c146bf78a/preprints/Sharp-One-Third-Stability-of-Brenier-Maps-September-25-2026/article.pdf)

## Status

Complete mathematical research draft, checked for stated hypotheses, proof dependencies and limiting cases. No external peer review, complete machine formalization or publication-priority claim is made. Attribution is explicit in the manuscript. Later versions will be added without replacing this version.

## Build

Use a complete TeX Live installation in the `v1` directory:

```sh
pdflatex manuscript.tex
bibtex manuscript
pdflatex manuscript.tex
pdflatex manuscript.tex
```

## Citation

```bibtex
@misc{mxym_math_001_v1,
  title = {Sharp one-third stability of Brenier maps for strongly log-concave sources},
  year = {2026},
  howpublished = {Research manuscript, mxym/math, version 1},
  url = {https://github.com/mxym/math/tree/main/preprints/001-strongly-log-concave-brenier/v1},
  note = {Cite the exact Git commit used; author metadata has not been asserted}
}
```
