# Reproducible build record

Date: 8 October 2026.

The three papers were built using installed system TeX and an existing shared compatible format/font-map cache. No packages were downloaded, no large dependency tree was copied, and shell escape was disabled.

## Toolchain

- pdfTeX 3.141592653-2.6-1.40.26, TeX Live 2025/dev/Debian
- kpathsea 6.4.0/dev
- Latin Modern and AMS fonts supplied by the installed system TeX trees
- Poppler `pdftoppm` 26.05.0
- Python 3.12.14

## Build settings

- Three pdfLaTeX passes per paper
- `-no-shell-escape -halt-on-error -interaction=nonstopmode -file-line-error -recorder`
- `SOURCE_DATE_EPOCH=1791417600`, `FORCE_SOURCE_DATE=1`, `TZ=UTC`, `LC_ALL=C`
- Letter paper, 11-point article class, one-inch margins
- One shared preamble; each paper keeps its own original section/equation numbering

Commands from the bundle root:

    ./build.sh
    python3 verify_bundle.py
    python3 reproduce.py

On the read-only shared installation used for this build, `TEX_CACHE_DIR` was set to the existing compatible cache from the earlier critical-atom build. A normal full TeX installation does not need this option. `build.sh` has a small cache-generation fallback when the installed format or filename database is unavailable; it reuses system packages and never downloads dependencies.

## Clean replay

A fresh temporary directory received only the shared preamble, build script, and each paper's TeX files. The three PDFs were rebuilt from empty output directories with the same shared installed toolchain. All three replay PDFs are **byte-identical** to the delivered PDFs. Extracted text, page breaks, and page counts also match exactly. `REPRODUCIBILITY.json` records this result. Byte identity is established for this toolchain; different TeX/font versions are not promised to produce the same bytes.

Final outputs:

- `top-n/main.pdf`: 12 pages; SHA-256 `026835142ba5402df4ecd20f8f1b085f2843fd18520e701558066441bb9f3241`
- `binary-mass/main.pdf`: 11 pages; SHA-256 `ea26a1d600998a8d35892704239a0409639c504e9cd64e5ed06031d150490548`
- `general-moment/main.pdf`: 9 pages; SHA-256 `98b0563da4a8a1b21b06f003655481b5591b32f2f5b167fd79f183fea14e5571`

Compiler diagnostics contain no overfull boxes, missing characters, unresolved citations/references, or LaTeX errors. The informational epstopdf warning that shell escape is disabled is expected; these papers use no EPS assets or shell-escape features. Raw machine-local compiler logs, filename manifests, format files, fonts, and rendered page images are excluded from the publication file list.
