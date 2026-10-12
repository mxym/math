# Artifact verification

7 October 2026.

The public manuscript has 12 US Letter pages, a blank author field and a searchable text layer. Every page was rendered with Poppler and visually inspected after the public-reference edits. No clipped content, overlapping equations, missing glyphs or unreadable type was found. The build reports no overfull boxes or unresolved references/citations. The full-page bibliography is deliberate.

All theorem, assumption, proposition, lemma, corollary and proof environments, and the complete H1–H6 operational input list, are byte-identical to the independently audited mathematical source. The public reference/bibliography and reproducibility edits are documented in EDITORIAL_CHANGES.md. The mathematical audit remains conditional on the named package, not external peer review or certification of that package.

## Public sources and verifier

The upstream source blobs were independently compared with the live GitHub contents API at commit adc7f1241b42e322a6451854ab7e4b4c146bf78a. The four entry-009 files in the public dependency map were compared with the live API at commit 6785c1c830f8e19e2eb07b0bb89f4d475a8b154a; their blob IDs and lengths match.

The offline verifier passed against all 11 pinned source files placed in repository-relative trees. A deliberate byte alteration was rejected with a nonzero exit code; restoring the original bytes restored a pass. Explicit repository roots are required. The verifier has no network or write operation and no hash-regeneration option.

Historical working-review hashes are separated in AUDIT_PROVENANCE.json. They are not external mathematical dependencies. No unavailable research paths occur in the reader-facing source map or verifier.

## Reproducible artifacts

The build fixes its timestamp, locale and timezone, disables shell escape and suppresses path-dependent PDF trailer identifiers. The source archive is deterministic and contains only the files declared in package_source.py. It excludes PDFs, caches, logs and rendered images. The exact archive is extracted, its checksums are checked, and its source is rebuilt independently. ARCHIVE_VERIFICATION.json records the resulting archive and PDF hashes and byte comparison without introducing a self-referential archive hash.

SHA256SUMS checks every delivered file except itself. PACKAGE_MANIFEST.json lists the immutable payload hashes and documents the manifest/checksum exclusions. The original audited source package and previously released manuscripts are preserved separately.
