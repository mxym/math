# Real symmetric counterexamples to Bapat's q-permanent conjecture

Research note, October 8, 2026.

This package gives a self-contained finite-existence proof: for some finite order N there is a non-diagonal real symmetric positive-definite integer matrix B and rational 0 < q0 < q1 < 1 with P_q0(B) > P_q1(B). The q-permanent uses the ordinary inversion count of a permutation in the chosen index order.

The argument first produces a real positive-semidefinite Gram matrix of rank at most four with a negative derivative at q=1. Rational approximation, adding a small positive rational diagonal, and multiplication by a positive common denominator yield the integer positive-definite conclusion. The final matrix is full rank. No explicit dimension bound, numerical real matrix, or numerical parameters are provided. Positive definiteness does not mean entrywise nonnegativity.

## Read the proof

- `paper.pdf`: the typeset 9-page research note
- `paper.tex`: authoritative editable LaTeX source
- `proof.md`: complete Markdown reading copy generated from the same source, with resolved equation references
- `PROOF_DEPENDENCIES.md`: concise map of the logical dependencies and finite choice order
- `SOURCES_AND_REVIEW.md`: provenance, source links, review scope, and mathematical changes from the reviewed draft

No author name or institutional affiliation has been added. Publication authorship and any repository-wide authorship disclosure are left to the repository owner.

## Reproduce the finite algebra checks

Python 3 with its standard library suffices. The mathematical verifiers use assertions and explicitly refuse to run when assertions are disabled (`-O`, `-OO`, or `PYTHONOPTIMIZE`). In that case they exit with code 2 before producing any success output. Run ordinary Python:

```sh
python3 verification/check_exact_algebra.py
python3 verification/check_independent_algebra.py
python3 verification/check_integer_scaling.py
python3 verification/check_optimization_guards.py
```

The first two programs independently compare direct permutation enumeration with polynomial Fischer identities, and check repetition, projective normalization, and selector algebra. The third checks integer denominator scaling coefficient by coefficient on 30 rational Gram-plus-diagonal matrices of orders 2 through 6, and checks value and derivative scaling at four rational q values.

Original reference logs and fresh reproduction logs are included. The independent mathematical scripts have only an added fail-closed assertion guard; their mathematical logic is unchanged. All listed checks passed during preparation. The optimization test driver uses explicit conditions, not assertions, and verifies 16 expected failures across the three mathematical scripts and the document integrity checker. `verification/check_build_configuration.py` separately checks the portable build wrapper with temporary command stubs, without rebuilding or altering the frozen PDF. These programs corroborate finite algebra; they do not computationally prove the limiting lemmas or supply a concrete real counterexample.

## Build the reading copies

With a normal LaTeX installation containing article, geometry, amsmath, amssymb, amsthm, mathtools, and hyperref, run:

```sh
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

`build.sh` performs two passes and, when Poppler is available, renders all pages to PNG and extracts the text into `qa/`. By default it uses ordinary `pdflatex`. To reuse an already prepared custom format/font-map directory, set `LOCAL_TEX_DIR` to that directory; no installation is performed. The archived `build-pass2.log` mechanically replaces the preparation environment's absolute custom TeX directory with `<LOCAL_TEX_DIR>` and is labeled as a publication projection.

To regenerate the full Markdown copy, run `python3 export_markdown.py` after the LaTeX passes. After `./build.sh` and Markdown export, `python3 verification/check_document_integrity.py` rechecks the generated pages, references, and equation tags. The release omits `paper.aux` and the extracted `qa/paper.txt`, so the full build step must precede the document integrity checker; the three mathematical verifiers and the optimization-safety driver work directly from the release without a TeX build. Markdown export uses an already installed Pandoc. `paper.tex` remains the authoritative source. PDF creation timestamps can change on rebuild; fresh hashes therefore need not match the archived PDF even when the mathematical content is unchanged.

## Verification and limits

Two independent AI-assisted mathematical reviews of the underlying proof are included under `review/`, together with the final-copy PASS in `review/FINAL_COPY_REVIEW.md` for the exact TeX, PDF, and Markdown hashes it records. These reports record conventional written mathematical checking by independent model runs, without external human peer-review acceptance. Version 1.1 adds a complete Lean formalization of the integer real symmetric existence theorem; see [the exact Lean coverage and verification scope](LEAN_COVERAGE_V1_1.md). The analytic proof and its formalization establish existence.

The distinct published complex order-200 witness is cited at a fixed commit. It is not a real matrix and is not used to prove the result here. No exhaustive historical-priority claim is made. No third-party paper PDF is redistributed in this package.

`MANIFEST.json` records the payload files, sizes, SHA256 hashes, and Git blob identifiers. `SHA256SUMS` covers those files and the manifest; neither checksum file contains a circular self-hash. `qa/QA_REPORT.md` records the actual rendering and extraction checks. PNG page renders, LaTeX auxiliary files, bbox output, and preparatory drafts remain local QA material and are excluded from the release payload. Original review reports refer to the predecessor draft hashes they audited; see `SOURCES_AND_REVIEW.md` for the distinction from the final typeset copy.
