# Final compact-source artifact verification

7 October 2026.

The public copy changes only the three review-status locations expressly approved by the unchanged independent sign-off. Reversing those substitutions in memory recovers the exact reviewed source hash 757d0ba430e52cfcfd98c5e78afe59150970e7897e99516efdb92adc42d1ab21. All twelve mathematical environments and all other source bytes are unchanged. The read-only verify_review.py checks the current source, reconstructed original, canonical environment digest and certificate bytes. Historical status spans are explicitly separated in editorial-status-changes.json.

The final PDF has ten US Letter pages, blank author metadata and a searchable text layer. Every page was rendered and visually inspected. A final status-sentence shortening was re-rendered to preserve the clean appendix/bibliography break. No clipped content, overlapping equations, missing glyphs, overfull boxes, or unresolved citations/references remain.

The standard-library exact checker reproduces the original results: 292 rational collision cases, 100 partition-division cases, four indicator identities and the hemisphere tensor constants. The normal run checks every assertion; an optimized run reproduces the same deterministic JSON, though Python disables assertions in that mode. These finite checks support the written analytic proof; they do not replace the tail or limiting arguments. A deliberately changed source is rejected by the review verifier.

The independent certificate reviews the exact compact-data theorem only. Gaussian-data extensions, matched-layer strengthening and the unsummed unit-amplitude mean are excluded. No many-particle H1–H6 theorem has been added as a dependency, and no external-peer-review or novelty claim is made. The two actual classical inputs are mapped to version-specific public manuscripts in DEPENDENCIES.md and source-map.json.

The source archive is deterministic, excludes PDFs, caches, logs and rendered images, and rebuilds independently. ARCHIVE_VERIFICATION.json records the exact archive and PDF hashes and clean-build comparison outside the archive to avoid self-reference. The build uses pdfTeX 3.141592653-2.6-1.40.26 (TeX Live 2025/dev/Debian), Python 3.12.14 and Poppler 26.05.0; it fixes SOURCE_DATE_EPOCH=1791331200, UTC and the C locale, disables shell escape and suppresses path-dependent PDF trailer identifiers. Other TeX/package versions can legitimately produce different PDF bytes.

Original reviewed materials and previously finalized packages remain unchanged. Publication is handled separately from this preparation.
