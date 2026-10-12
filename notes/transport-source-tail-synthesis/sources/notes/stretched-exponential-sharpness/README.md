# Sharp logarithmic corrections under stretched exponential target bounds

Supplementary note for the mxym/math research collection, 7 October 2026.
This is a supplement to manuscripts 001 and 007, not a new numbered major paper.

The note proves a matching stretched-exponential logarithmic lower bound for
the fixed uniform cube and fixed cube-truncated Gaussian. It combines their
explicit two-atom constructions in manuscript 001 v3 with the upper bound in
manuscript 007 v1, Corollary 4.1. It also explains the pure one-third bound for
the full Gaussian. The lower-bound proof is self-contained. The upper bounds
use the cited potential theorems proved in manuscript 001; this note does not
independently revalidate those theorems. No novelty or priority claim is made.

## Files

- `stretched_exponential_sharpness.pdf`: six-page supplementary note
- `stretched_exponential_sharpness.tex`: editable LaTeX source
- `build.sh`: two-pass PDF build
- `SHA256SUMS`: hashes of the released files, excluding the manifest itself

## Build

Use a standard TeX Live or MiKTeX installation with pdfLaTeX, Latin Modern,
AMS packages, mathtools, microtype, geometry, and hyperref. No network access,
external images, or BibTeX run is needed.

Run `sh build.sh` from this directory. Intermediate files go into `build/`.
The resulting PDF replaces `stretched_exponential_sharpness.pdf`.
PDF binary hashes may change when rebuilt with a different TeX version or
timestamp. Check the frozen release before rebuilding with `sha256sum -c SHA256SUMS`.

## Pinned sources

Repository snapshot: `0bd6c682edbe6f15001ddc2d73aac3c84ac979a4`.

- [Manuscript 001 v3](https://github.com/mxym/math/blob/0bd6c682edbe6f15001ddc2d73aac3c84ac979a4/preprints/001-strongly-log-concave-brenier/v3/manuscript.tex): Theorem 1.7, Sections 11 and 12.2; Theorem 1.6 for the full Gaussian; Theorems 1.1 and 1.4 for the potential estimates.
- [Manuscript 007 v1](https://github.com/mxym/math/blob/0bd6c682edbe6f15001ddc2d73aac3c84ac979a4/preprints/007-tail-brenier-stability/v1/main.tex): Theorem 3.1 and Corollaries 3.2 and 4.1.

The frozen 007 v1 files are unchanged.
