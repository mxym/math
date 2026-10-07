# Quantitative strict bounds in complete numerical range calculus

This standalone note studies the retained nonnegative deficit in an attributed complete Crouzeix proof and an explicit dimension-free strict-domain certificate. The full proof is in [paper.pdf](paper.pdf); its single-file LaTeX source is [research.tex](research.tex).

## Main statements

For a finite matrix A and a regular analytic convex domain strictly enclosing its numerical range, the intrinsic complete factor is

2 / sqrt(1 + min(mu^2, 3) / M^2),

where M is the maximum exterior resolvent-kernel norm and mu is the minimum positive Hermitian-part eigenvalue. Both constants are defined in Section 2, and mu is strictly positive. The factor is independent of the base dimension, coefficient dimension and polynomial degree.

The note also proves:

- The exact nonnegative singular-vector deficit and quantitative necessary near-equality conditions
- A geometric certificate valid for bounded operators on arbitrary complex Hilbert spaces
- A norm-perturbation certificate on the same enclosing domain
- Explicit analytic convex outer approximation, recovering complete constant two on the numerical-range closure
- A stronger disk comparison deduced separately from classical similarity input

The gap below two applies to a strictly larger enclosing domain and may vanish in the outer limit. Near-equality conditions do not classify extremizers or imply closeness to a prescribed matrix model.

## Attribution and status

The Faber coefficient and ordered-product architecture, the conformal collar and complete-two outer-limit recovery are credited to OpenAI's public direct manuscript at commit adc7f1241b42e322a6451854ab7e4b4c146bf78a. That manuscript already states complete constant two. This note does not claim a first resolution or an independent new complete-two architecture. Its candidate refinements are the retained deficit and explicit rank-free strict-domain certificates. Their novelty and priority have not been established.

The exact pinned URLs and independently matched source hashes are in [PROVENANCE.json](PROVENANCE.json). The original six inputs have been preserved separately; [ORIGINAL_INPUT_HASHES.json](ORIGINAL_INPUT_HASHES.json) records their checksums without including the unrelated original survey in this release.

[TECHNICAL_AUDIT.md](TECHNICAL_AUDIT.md) contains the public mathematical review of the core proof. An independent AI-assisted audit found no core mathematical correction under the stated hypotheses. Exact finite calculations support algebra and examples. Neither the audit nor those checks are proof-assistant formalization, human peer review, publication acceptance or an exhaustive literature assessment.

## Reproduce the exact checks

Only Python's standard library is required:

    python3 verify.py

This replays each checker normally and with Python optimization, requires identical output and verifies the stored finite-check certificates. It also checks source and release manifests when present.

The original rational checker covers 100 generic Laurent block cases, 255 actual nilpotent singular pairs, 1,020 perturbation parameter cases and two boundary/zero cases. The independently written complex rational checker imports no original checker code and covers 20 complex density cases, 60 actual entangled singular pairs, 120 separately ordered product tests and 36 ellipse coefficient cases. The disk comparison checker verifies 870 exact interpolation parameter cases and two endpoints. These finite examples do not prove analytic or universal statements.

## Rebuild the PDF

A working TeX Live installation with the packages used by research.tex and Poppler's pdfinfo/pdftotext is sufficient. The source has no external TeX inputs and requires no downloaded source files.

    python3 verify.py --build

The rebuild runs pdflatex three times with shell escape disabled, rejects unresolved references and overfull boxes, checks the PDF page count, and writes rebuilt-paper.pdf in the directory specified by --output-dir (default: a fresh temporary directory). A TeX installation may need its usual writable format/font caches configured before use. The recorded release was successfully built using the installed TeX distribution and isolated writable caches; no package installation or source change was needed.

For a direct build:

    pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error research.tex
    pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error research.tex
    pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error research.tex

The packaged PDF was rendered and visually checked on all 12 pages. Exact PDF byte equality is not required for a rebuild because TeX may include build timestamps and file identifiers.

## Package integrity

- VERIFICATION.json records exact-check and PDF-build scope
- SOURCE_MANIFEST.json lists the files included in source.tar.gz
- MANIFEST.json lists every release payload other than itself
- PUBLICATION_WHITELIST.json lists the complete permitted publication paths

The source archive includes the single-file proof, reader documentation, public technical review, provenance, exact checkers and their certificates. It excludes machine caches, build logs, render images, private transfer information, and the unrelated survey. Checksums establish byte integrity; they are not mathematical correctness certificates.
