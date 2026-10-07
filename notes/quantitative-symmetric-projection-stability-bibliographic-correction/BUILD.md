# Article build and archive reproduction

This records the separate bibliographic correction build. The earlier release
remains immutable; article theorem/proof text is unchanged.

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
| `paper.tex` | 39,854 | `723ae494c5ad14d667df699df75495ae5b0f6c69efb133ba868cce1912284a9a` |
| `paper.pdf` | 397,479 | `53feada957f34b8598b3cef5a59f01ddb11aaaf44b78a13eacd71077962c9986` |

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
`notes/quantitative-symmetric-projection-stability-bibliographic-correction/`, with a fixed timestamp.
No build intermediate, checkout, or catalogue file is collected. Separate v4
before/after review copies and the requested attribution patch are included
under `corrections/`; the mathematical dependency pins remain unchanged. `dist/SHA256SUMS` records the archive hashes.

The manifests identify file bytes; they are not formal mathematical
certificates. The exact checks and their limitations are documented in
`VERIFICATION.md`, and the mathematical reading is summarized in `AUDIT.md`.
