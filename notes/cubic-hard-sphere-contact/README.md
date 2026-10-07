# Cubic hard-sphere contact and mean correction

Research supplement, 7 October 2026. The exact compact-data theorem has passed independent model review with no required mathematical changes.

The [ten-page manuscript](manuscript.pdf) and [editable source](manuscript.tex) prove first-diameter expansions of the exact second and third activity coefficients for smooth compactly supported initial data. The cubic incoming contact coefficient is an absolutely convergent infinite-past three-sphere scattering integral with an absolute C/R tail. The cubic mean remainder is o(epsilon), uniformly on finite time intervals in total variation.

Contact convergence is uniform in incoming-flux L1 with a time supremum on every [delta,T], delta>0, and time-integrated through zero. Uniform contact convergence at zero is not claimed. Mean convergence is uniform including zero.

The theorem uses only the cited classical isolated finite-particle flow and scattering facts. It is independent of the many-particle H1–H6 history package. There is no higher-activity summation, unsummed unit-amplitude mean theorem, polynomial cubic remainder rate, external-peer-review claim or novelty claim. Gaussian-data extensions and matched-layer strengthening remain separate and are not included in this sign-off.

## Read and verify

- [Complete theorem and proof](manuscript.pdf)
- [Exact-source independent sign-off](audits/exact-source-signoff.txt)
- [Public classical dependency map](DEPENDENCIES.md) and [versioned links](source-map.json)
- [Editorial changes](EDITORIAL_CHANGES.md) and [review provenance](REVIEW_PROVENANCE.json)
- [Artifact verification](ARTIFACT_QA.md)
- [Reproducible source archive](source.tar.gz)

The certificate applies to the complete exact source whose hash it names. The public TeX differs only at three explicitly approved review-status locations. A read-only verifier reconstructs the reviewed bytes from those substitutions and checks the original reviewed hash, the current hash and the unchanged certificate. No private Library access or unpublished research file is needed.

## Reproduce

Requires Bash, Python 3 and pdfLaTeX with the standard packages named in manuscript.tex:

    python3 verify_review.py
    python3 exact_checks.py
    ./build.sh

Both Python scripts use only the standard library. The review verifier is offline and read-only; the finite checker writes its deterministic result JSON. Neither replaces the analytic proofs. The build is offline, disables shell escape, and fixes SOURCE_DATE_EPOCH=1791331200, UTC and the C locale.

Check delivered files:

    sha256sum -c SHA256SUMS

After extracting the source archive:

    sha256sum -c SOURCE_SHA256SUMS
    python3 verify_review.py
    python3 exact_checks.py
    ./build.sh

The archive excludes PDFs, logs, caches and page images. Its independent rebuild is recorded in ARCHIVE_VERIFICATION.json. Byte identity is checked with the recorded toolchain; another TeX version may produce different bytes. Historical review-status wording in editorial-status-changes.json is retained only to reconstruct the exact reviewed source; it is not the current review status.
