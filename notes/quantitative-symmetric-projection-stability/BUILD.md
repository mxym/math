# Article build and archive reproduction

The article is 11 US-letter pages. The final source and PDF were rebuilt from
only `paper.md`, `header.tex`, and `build.sh` in an empty directory. The rebuilt
LaTeX and PDF matched the release files byte for byte. The final pdfLaTeX log
has no overfull or underfull boxes, missing characters, warnings, or errors.
The recorded result is in `results/build.json`; the final log is in
`results/typeset.log`.

## Recorded toolchain

- Pandoc 3.1.11.1.
- pdfTeX 1.40.26, TeX Live 2025/dev/Debian.
- Python 3.12.14 for exact checks and archive construction.
- `pdftoppm` at 110 dpi for the all-page visual inspection in `PDF_QA.md`.

`build.sh` sets `SOURCE_DATE_EPOCH=1791331200` and `FORCE_SOURCE_DATE=1`.
The LaTeX header omits PDF creation dates and the generated trailer identifier.
These controls yielded byte-identical output with the recorded toolchain.
Other Pandoc or TeX versions may produce different PDF bytes while preserving
the same article.

The final article identifiers are:

| File | Bytes | SHA-256 |
| --- | ---: | --- |
| `paper.tex` | 36,623 | `8aa856c42ededb1ad5ec6763fa50395f4f590a2c82ae8006021963daa6351e9b` |
| `paper.pdf` | 393,147 | `12b9b21ff9cf079bf8773aeaaadacbe76550800d6111694c97d92ed00a6ee6d1` |

## Rebuild from Markdown

From the extracted supplement directory:

```sh
sh build.sh
```

The build regenerates `paper.tex` and `paper.pdf`, using intermediate files
under `build/typeset/`. It does not change the recorded verification reports.
An optional argument selects another intermediate directory:

```sh
sh build.sh build/clean-typeset
```

## Compile the standalone LaTeX source

`paper.tex` already includes the complete header and requires no external
figure, bibliography, or repository file. Copy it into an empty directory and
run:

```sh
export SOURCE_DATE_EPOCH=1791331200
export FORCE_SOURCE_DATE=1
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
pdflatex -interaction=nonstopmode -halt-on-error paper.tex
```

## Recreate the archives

After the article and recorded results are present, run:

```sh
python3 code/package_release.py
```

This writes `SOURCE_MANIFEST.json`, `MANIFEST.json`, and two deterministic ZIP
archives under `dist/`. The source archive contains the editable article,
supporting documentation, exact code, and recorded reports. The complete
archive also includes the PDF. Every archive entry is under
`notes/quantitative-symmetric-projection-stability/`, with a fixed timestamp.
No build intermediate, checkout, catalogue file, or numbered preprint is
collected. `dist/SHA256SUMS` records the archive hashes.

The manifests identify file bytes; they are not formal mathematical
certificates. The exact checks and their limitations are documented in
`VERIFICATION.md`, and the mathematical reading is summarized in `AUDIT.md`.
