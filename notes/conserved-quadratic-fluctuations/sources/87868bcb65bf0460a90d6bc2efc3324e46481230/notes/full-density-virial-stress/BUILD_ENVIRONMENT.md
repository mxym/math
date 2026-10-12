# Reproduction toolchain

The checked build used pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian), Python 3.12.14 and Poppler 26.05.0 on Linux x86_64. The source requires the standard LaTeX packages listed in manuscript.tex.

The build fixes SOURCE_DATE_EPOCH=1791331200, FORCE_SOURCE_DATE=1, TZ=UTC and LC_ALL=C, disables shell escape, leaves the author blank, and suppresses path-dependent PDF trailer identifiers. Three passes resolve references. It rejects undefined references and overfull boxes.

The build script can use a build-local fallback format/cache on standard Debian TeX Live installations. It changes no system files. The source archive was verified by extraction and a byte-identical PDF rebuild using this toolchain. Reproduction on a different TeX/package version need not produce byte-identical output.
