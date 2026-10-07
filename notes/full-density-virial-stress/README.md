# Full-density virial and collisional stress

Research supplement, 7 October 2026.

The [manuscript](manuscript.pdf) and [editable source](manuscript.tex) prove full-unit-amplitude first-order corrections for the mean virial and spatial second moment, and identify a local momentum-balance defect as the classical collisional-stress tensor. Initial position and velocity support is compact. The theorem is conditional on the explicit pinned history package H1–H6.

The weighted passive-record extension is proved here, with global clipping on signed branches, conditional energy/size bounds, auxiliary-contact cancellation and true-flow transfer. The whole one-particle mean correction remains open. No fluctuation theorem for these unbounded spatial tests, external peer review, or priority claim is asserted.

## Contents

- [Theorem and proof](manuscript.pdf)
- [Public dependencies](DEPENDENCIES.md) and [pinned source map](dependency-inventory.json)
- [Mathematical audit](MATHEMATICAL_AUDIT.md)
- [Editorial changes](EDITORIAL_CHANGES.md) and [review provenance](AUDIT_PROVENANCE.json)
- [Artifact checks](ARTIFACT_QA.md)
- [Reproducible source archive](source.tar.gz)

## Build

Requires Bash, Python 3, pdfLaTeX and the standard packages named in manuscript.tex. Run:

    ./build.sh

The build is offline, disables shell escape, and fixes SOURCE_DATE_EPOCH=1791331200, UTC and the C locale. Outputs are manuscript.pdf and diagnostics under build/. The source archive builds independently. Byte identity is checked for the recorded toolchain; other TeX versions may legitimately produce different bytes.

Check delivered files:

    sha256sum -c SHA256SUMS

After extracting the archive:

    sha256sum -c SOURCE_SHA256SUMS
    ./build.sh

Check external public sources:

    python3 verify_dependencies.py --upstream-root /path/to/openai-math --mxym-root /path/to/mxym-math

The verifier does not download files or update expected hashes. DEPENDENCIES.md supplies exact public commits and paths. Historical review hashes are provenance rather than mathematical source requirements.

The source archive excludes PDFs, logs, caches and page images. Exact archive-rebuild evidence is in ARCHIVE_VERIFICATION.json, outside the archive to avoid self-referential hashes.
