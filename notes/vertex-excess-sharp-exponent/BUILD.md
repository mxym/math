# Build instructions

## Requirements

- POSIX shell
- pdfLaTeX / TeX Live
- `article`, `geometry`, `fontenc`, `lmodern`, `amsmath`, `amssymb`, `amsthm`, `mathtools`, `microtype`, `xurl`, `hyperref`, and `enumitem`
- Poppler `pdfinfo` and `pdftotext`
- Python 3 standard library for the optional verification script

No network fetches, external images, BibTeX database, or Lean build are required. All bibliography entries are in `main.tex`.

## Commands

From this directory:

    ./build.sh
    python3 verify_package.py

The build runs pdfLaTeX three times for stable references and contents, then copies `build/main.pdf` to `vertex_excess_sharp_exponent.pdf`. Intermediate TeX files and logs stay in `build/`. The final PDF is the only reader-facing binary.

## Reused TeX fallback

The preparation environment has TeX Live 2025/dev/Debian binaries and package files, but its default kpathsea configuration does not locate `article.cls`. The build detects that condition and uses `configure_tex.sh`, reused from the existing project TeX setup. It points to installed packages at `/usr/share/texlive/texmf-dist` and `/usr/share/texmf`, creates a local pdfLaTeX format and font map under `tex-cache/`, then invokes the same build.

A normally configured TeX installation bypasses this fallback. If your system has neither a working TeX configuration nor those Debian paths, install/configure TeX Live normally rather than changing the mathematical sources.

## Visual verification

    mkdir -p qa/pages
    pdftoppm -r 100 -png vertex_excess_sharp_exponent.pdf qa/pages/page

Open every page image and check displays, theorem breaks, source-path wrapping, page numbers, and references. Text extraction is a supplementary check and does not replace visual inspection. The included QA report records the actual inspected release PDF hash and page count.

## Reproducibility boundary

The source build is reproducible without private dependencies. PDF timestamps and TeX version can alter binary hashes without altering content; therefore the supplied PDF SHA-256 identifies the prepared release copy, not a promise of cross-platform byte-identical output. No computation here constitutes a formal proof-assistant audit. The rational checks only help catch transcription mistakes.
