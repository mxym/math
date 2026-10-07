# Verification record

7 October 2026. All checks below completed on the publication-ready package. They supplement the independent written audit; no finite computation or hash certifies a universal theorem.

## Mathematical and source checks

- Read the complete TeX and extracted proof text; independently checked every statement of Theorem 1, Corollary 2 and Proposition 3.
- Verified the projection/pyramid normalization against public v2 and v3 at commit 3360e7191cf564a46d09edcbfbd107c9178bd98f.
- Verified ten copied public-source snapshots against their exact pinned commits and the checked repository commit; verified the two literal commit-reference files. Exact paths, hashes and byte sizes are in sources/SOURCE_MANIFEST.json.
- Compared all theorem, corollary, proposition and proof environments before and after publication editing: byte-identical. Also compared all displayed and inline mathematical content: unchanged. The complete editorial diff is in EDITORIAL_CHANGES.md.
- Verified that every received original file remained unchanged. The original 19-member ZIP passed CRC checks and matched the extracted originals byte-for-byte. All eight original manifest entries matched.

## Exact arithmetic replay

Both `python3 check_exact.py` and `python3 -O check_exact.py` completed successfully on an isolated copy, and both were replayed again through the packaged `replay.sh`. Their JSON certificates and text outputs match one another and the received archived results byte-for-byte.

```text
horizontal_minors: 1080
lifted_minors: 300
leibniz_crosschecks: 125
vertex_simplex_subsets: 5385
barycentric_vertex_checks: 1760
difference_body_supporting_facets: 70
difference_body_boundary_triangles: 160
```

Five 3D difference-body volumes are reconstructed using exact supporting facets and boundary triangulations. Facet and barycentric grids use d=2..9, vertex-subset enumeration uses d=2..6, and t ranges over 1/100, 1/10, 1/3, 1/2 and 9/10.

## PDF and text

The original TeX first rebuilt without content changes. Its extracted text matched proof.txt exactly, and all eight rendered pages matched the supplied PDF pixel-for-pixel.

The publication-ready TeX was then rebuilt after the documented editorial substitutions. The final PDF has eight pages. Every page was rendered and visually inspected. The second TeX pass has no unresolved-reference, overfull/underfull-box or missing-glyph warning. proof.txt was re-extracted from that final PDF.

A clean extraction of source.zip was rebuilt using its own build.sh, without borrowing a TeX cache or input file from the preparation directory. The resulting PDF and extracted text are byte-identical to the packaged copies. The clean extraction also passes exact replay and both Python modes of the package-integrity check.

## Packaging

- PACKAGE_FILES.txt specifies the exact complete public package.
- MANIFEST.json hashes every payload file, including source snapshots, notices, README, audit, build scripts and whitelist. It excludes only itself and source.zip to avoid cyclic hashes.
- source.zip contains all whitelisted files except itself, under simplex-truncation-stability/. It has fixed timestamps and permissions; build directories, caches and working notes are excluded.
- Ordinary and optimized `check_package.py` runs verify complete payload coverage, source records, exact archive membership and bytes.
- Re-running `make_package.py` produces identical manifest and ZIP bytes with the tested Python toolchain.
- No repository checkout, push or publication is part of these scripts.

## Tested toolchain

- Python 3.12.14; standard library only for all exact checks and packaging
- pdfTeX 3.141592653-2.6-1.40.26, TeX Live 2025/dev/Debian
- Poppler pdftotext 25.03.0
- ZIP compression through the Python standard-library zipfile module

The build fixes SOURCE_DATE_EPOCH=1791331200 (2026-10-07 00:00:00 UTC), FORCE_SOURCE_DATE=1 and TZ=UTC, and suppresses the PDF trailer identifier. A local fallback initializes installed TeX resources when the system format database is unconfigured, including the Euler font map required for the defect symbol. It installs nothing and uses no network access. Byte-identical rebuilding is verified with the stated toolchain; different font, TeX or Poppler versions may legitimately change output bytes.
