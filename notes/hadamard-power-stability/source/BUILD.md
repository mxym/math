# Building and checking the manuscript

## Standard TeX installation

Requirements: pdfLaTeX with `article`, `fontenc`, Latin Modern, `geometry`, `amsmath`, `amssymb`, `amsthm`, `mathtools`, `microtype`, `hyperref`, and `enumitem`.

Run from this directory:

```sh
./build.sh
```

The script performs three small pdfLaTeX passes with shell escape disabled, checks the final log for errors, undefined references/citations, overfull boxes, and missing glyphs, then copies `build/main.pdf` to `main.pdf`. It does not download packages or create a new TeX format. `SOURCE_DATE_EPOCH` is fixed to 8 October 2026 UTC for stable output metadata.

## Existing format cache in this preparation environment

The available system TeX tree did not have normal default search-path configuration. The script therefore supports an existing cache containing `pdflatex.fmt` and `pdftex.map`:

```sh
TEX_CACHE_DIR=/absolute/path/to/existing/tex-cache ./build.sh
```

Its preparation-environment fallback is the already existing sibling `../kinetic13_manuscript_independent_audit_20261007/tex-cache`. That fallback is not a vendored dependency and is not required on a normally configured TeX installation. No fresh TeX format or dependency tree was built for this manuscript.

## Visual QA

With Poppler installed:

```sh
mkdir -p qa
pdftoppm -r 100 -png main.pdf qa/page
pdfinfo main.pdf
```

Inspect every page image, especially displays, the order-four matrices, the quadratic block formulas, the exact-certificate matrices, and references. Page images and build logs are preparation evidence and need not be published as manuscript assets.

## Exact finite certificates

`certificates/check_tangent_rank.py` requires Python 3 and SymPy. It uses exact integer/rational operations and writes `tangent_rank_results.json` beside itself. To reproduce without overwriting the retained reviewed result:

```sh
work=$(mktemp -d)
cp certificates/check_tangent_rank.py "$work/"
python3 "$work/check_tangent_rank.py"
cmp certificates/tangent_rank_results.json "$work/tangent_rank_results.json"
```

The original analytic review already performed that exact replay. This typesetting task retained the script and JSON byte-for-byte and did not rerun or extend mathematical computations. These finite checks do not prove the general theorems.

## Integrity

Run `sha256sum -c SHA256SUMS` from this directory. Hashes establish byte identity, not mathematical correctness. Input hashes, pinned external sources, and review receipt identities are in `provenance/source_manifest.json`.
