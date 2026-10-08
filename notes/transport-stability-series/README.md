# Sharp transport stability for finite and binary targets

Three complete English research-paper candidates, prepared on 8 October 2026 from the exact proof revisions identified below. Each paper preserves its complete argument and original section/equation numbering. The PDFs are reader editions; the original proof snapshots remain unchanged in `sources/`.

## Papers and reading order

1. [Source scales and finite target complexity](top-n/main.pdf) ([LaTeX](top-n/main.tex), [proof body](top-n/body.tex)). A jointly uniform top-N envelope for a fixed critical boundary source, including nonmonotone slowly varying factors, exact atom accounting, and selected-scale convex-gradient lower constructions.
2. [Binary mass crossover and boundary phases](binary-mass/main.pdf) ([LaTeX](binary-mass/main.tex), [proof body](binary-mass/body.tex)). Direct all-directions binary upper bounds, exact-mass lower examples, fixed-mass and minimum-weight crossover formulas, and the binary phase threshold alpha = 2s.
3. [General convex moment bounds](general-moment/main.pdf) ([LaTeX](general-moment/main.tex), [proof body](general-moment/body.tex)). The response E(m) = sqrt(m) Phi^{-1}(1/m), its sharp source-quantile envelope, a necessary and sufficient continuity criterion, and comparison-only endpoint applications.

For binary targets, begin with paper 2 and then paper 3. Paper 1 is a separate finite-cardinality branch. Reading 1, 2, 3 also gives the chronological development.

## Exact dependency boundary

- Paper 1's upper bounds, and hence its sharp two-sided conclusions, explicitly import the centered-potential estimate (P) from manuscript 001 version 3, Theorem 1.1, with K_rho = sqrt(2) for the displayed 1-strongly log-concave source. The present review checked the applicability of that theorem's statement, **not its proof**. Its lower constructions do not use (P). The full top-N matching result is for N >= 3; the stated binary addition has its separate restricted scope.
- Paper 2 does **not** use (P) or paper 1. It proves its halfspace geometry in Section 2, including the all-orientations fixed-mass motion estimate in **Section 2.3, equation (2.5)**, and solves the binary coupling problem in Section 3. Standard quadratic Brenier existence/uniqueness and the stated elementary analytic tools remain background inputs.
- Paper 3 uses paper 2's **Section 2.3, equation (2.5)** as its geometric interface and recalls paper 2's **Section 3** coupling calculation. It restates the necessary source and target definitions and gives the moment replacement, exact-mass realization, mass optimization, continuity criterion, and endpoint arguments. It does **not** use (P). The three PDFs should therefore be distributed as a series, not described as three logically independent proofs.

The source stays fixed as distance, cardinality, or admissible mass parameters vary. Atoms mean distinct positive-mass support points; coincident labels are merged. All comparison constants and all small-distance restrictions retain the dependencies specified in the papers. The symbol `asymp` in the LaTeX is a two-sided comparison; `sim` is reserved for an actual ratio-one asymptotic. No exact leading coefficient is claimed.

## Review status

The supplied [analytic review](review/REVIEW.md) covers the three original snapshots. It found a local endpoint-proof gap in the original third manuscript and supplied comparison-based replacement proofs. The [final limited recheck](review/LIMITED_RECHECK.md) ([machine-readable receipt](review/LIMITED_RECHECK.json)) confirms that the corrected third snapshot closes that gap without additional hypotheses. **The final limited recheck supersedes the original review's open-repair status.**

Final statuses at the exact source hashes:

- Top-N: conditional PASS on imported (P)
- Binary mass: PASS
- General moment: PASS after the endpoint repair

These are records of AI-assisted analytic checking. They are not Lean or other formal verification, a professional mathematician's certification, external peer review, historical-priority certification, or publication approval. This typesetting pass is a preservation and rendering check, not a new mathematical audit. No new theorem is introduced.

## Contributions and antecedents

Paper 1 combines the already developed L = 1 atom-budget and unrestricted slowly varying analyses into a joint source-weight/cardinality law. Its added ingredients are finite-step top-N compression and genuine selected-scale realizations whose moment cost does not charge skipped scales. Paper 2 adds an all-directions binary upper bound and matching mass-dependent formulas; it does not claim novelty for rotating binary targets or elementary two-by-two couplings. Paper 3 generalizes the response function under the stated monotonicity condition and proves the exact scalar envelope. It does not claim novelty for the uniform-integrability principle itself.

The papers distinguish their results from repository manuscript 008, manuscript 001, the critical atom-budget proof, the unrestricted slow-variation supplement, and the source-tail synthesis. Their primary-literature context includes Bansil--Kitagawa, Delalande--Merigot, and, for binary rotation, Letrouit. The source map records precise predecessor paths and available fixed-revision links. No historical-first claim is made.

## Build and verify

Requirements: Python 3 for integrity checks; a system TeX Live installation with pdfTeX, Latin Modern, AMS packages, geometry, microtype, hyperref, mathtools, and enumitem; Poppler for PDF inspection. There are no downloads, shell escapes, vendored TeX trees, or copied large dependencies.

From this directory:

    ./build.sh
    python3 verify_bundle.py
    python3 reproduce.py

Each paper is compiled three times. A single paper can be rebuilt with `./build.sh top-n`, `./build.sh binary-mass`, or `./build.sh general-moment`. Final PDFs are copied to each paper's `main.pdf`; compiler files remain in its ignored `build/` directory.

The build sets `SOURCE_DATE_EPOCH=1791417600` (8 October 2026, 00:00 UTC), `FORCE_SOURCE_DATE=1`, `TZ=UTC`, and `LC_ALL=C`. A complete system TeX installation is used directly. On a read-only incomplete TeX installation, the script reuses the installed packages and writes only a small format/font-map cache, normally `/tmp/mxym-math-tex-cache`. Set `TEX_CACHE_DIR` to an existing compatible shared cache to reuse it. No dependency packages are copied into this bundle.

The delivered build used the existing shared TeX cache from the earlier critical-atom build. Exact tool versions and replay results are in [BUILD_INFO.md](BUILD_INFO.md). The compiler checks reject missing glyphs, undefined references/citations, and overfull boxes. All pages were rendered and visually inspected; the scope and results are in [QA.md](QA.md). A hash or equation-tag check is not a proof checker.

## Source preservation

- `sources/top-n.PROOF.md`: SHA-256 `c3cf5061de5ac9298f3fb88e07800c9d88257b01a1cd80f82fdc5e1a083055c1`
- `sources/binary-mass.PROOF.md`: SHA-256 `6858879d5acb26657b7d83ffc1b99386e67cd5c9fbf60ab451b579d132f1b9d8`
- `sources/general-moment.PROOF.md`: SHA-256 `2e683e3cf79a373e6f7921bf2d25e45783484548cb7abf85c765a0486f46efbe`

The superseded third snapshot, original machine-readable verdict, and exact endpoint-repair diff are retained only for review provenance. They are not the current theorem version. Original snapshots contain historical status sentences; consult the final status above rather than treating those old sentences as current.

[SOURCE_MAP.md](SOURCE_MAP.md) and [SOURCE_MAP.json](SOURCE_MAP.json) map every source section and displayed equation tag to its typeset paper. They record the limited editorial changes: titles/abstracts, status updates, proper mathematical typography, precise cross-paper citations, expansion of definitions, the reviewed source-support qualifier, and bibliography presentation. The underlying written proof is retained as closely as possible.

This directory is a publication candidate only. Its preparation performs no Git commit, push, release, or user-facing attachment upload. Publication is a separate authorized step.
