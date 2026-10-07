# Sharp simplex dimension refinements: final-copy evidence

Date: 7 October 2026.

## One development, two preserved methods

The [quadratic-dimensional written proof](../../notes/quadratic-dimensional-simplex-stability/README.md) is the stronger coefficient refinement. The [polynomial-dimensional companion](../../notes/polynomial-dimensional-simplex-stability/README.md) preserves the earlier method and its 11-page typeset derivative. Both concern the same projection/pyramid deficit, exponent 1/(d−1), every prescribed maximum-volume inscribed simplex and that simplex's original centroid, in every integer dimension d >= 3. They are successive refinements of entry 005; the optimal dimension order remains between linear and quadratic.

- Strongest coefficient: at most 4096 d²; [quadratic final-copy audit](quadratic/QUADRATIC_FINAL_COPY_AUDIT.md), [evidence](quadratic/QUADRATIC_FINAL_COPY_EVIDENCE.json), [exact reviewed inventory](quadratic/QUADRATIC_FINAL_COPY_INVENTORY.json).
- Preserved companion coefficient: at most 2^20 d^6; [polynomial final-copy audit](polynomial/FINAL_COPY_AUDIT.md), [mathematical fidelity review](polynomial/math_fidelity/MATHEMATICAL_FIDELITY_AUDIT.md), [evidence](polynomial/AUDIT_EVIDENCE.json), [public-copy ledger](polynomial/PUBLIC_COPY_LEDGER.json).

Both verdicts are PASS for the exact frozen releases. The independent analytic model reviews, final-copy checks, finite regressions and source-integrity checks have different roles. No whole-theorem Lean formalization, human peer review, journal acceptance, novelty or priority determination is asserted.

## Exact package identities

| Package | Files | source.zip bytes | SHA-256 |
| --- | ---: | ---: | --- |
| Quadratic | 40 | 342836 | d79b07df28ad259f6f02c396335a69a9a3bff98b0a98dfd17d89e5199d4b980d |
| Polynomial | 35 | 672029 | 4fc6de94915be740c03f48e4b437b5481c3dbcddef946c86aaee78494264820a |

The companion PDF has eleven pages, 354063 bytes and SHA-256 1972edd13d2b43d6318fbb0ccdbc192ef14139b83f429249da9bc06ae764f2d9. The quadratic edition contains the complete readable Markdown proof and imports; it does not include a new PDF.

## Fresh publication-integration replay

The [integration summary](integration/REPLAY_SUMMARY.json) and adjacent logs record fresh normal/optimized package verification for each release, normal/optimized replay after clean archive extraction, exact archive-member comparison and byte-identical regeneration of each MANIFEST.json, SHA256SUMS and source.zip. All frozen stage bytes remained unchanged. The integration checks were performed on disposable copies. These checks are separate from the final reviewers' deeper analytic/fidelity/hostile-control work. No fresh PDF build or Lean compilation was part of publication integration.

For portable reproduction, run `python3 verify.py` and `PYTHONOPTIMIZE=1 python3 -O verify.py` in each package directory. After archive extraction, append `--extracted`. The polynomial archive has one package-directory prefix; the quadratic archive is flat. In a disposable copy, `python3 make_package.py` reproduces the package's integrity files and source archive. See each package's README for precise dependency and trust limits. The quadratic independent convex-body checker needs SymPy; the polynomial finite checks use Python's standard library.

## Evidence delivery and preservation

Quadratic records are reviewer-authored public summaries with release-relative identifiers. The compact polynomial audit copy preserves the original substantive findings and discloses its locator-only and evidence-delivery edits in PUBLIC_COPY_LEDGER.json. The polynomial visual QA record retains hashes of the eleven independently inspected renders; the render images, disposable compiler directories and raw retrieval logs are not bundled here. Both original mathematical packages remain byte- and mode-identical to their frozen copies.

The [release manifest](../../releases/2026-10-07-dimension-refinements-v1.json) binds every new package/evidence file and exactly four existing navigation/status files. All other historical manuscript, Lean, certificate, archive and workflow bytes and Git modes are retained. Separately audited construction supplements and further unfinished refinements are outside this publication.
