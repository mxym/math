# Polynomial-dimensional simplex stability

For every integer d ≥ 3, every full-dimensional convex body K in R^d, and every prescribed maximum-volume inscribed simplex S, the excess dilation about S's own centroid satisfies

    E(K,S) ≤ G_d e(K)^(1/(d−1)) ≤ 2^20 d^6 e(K)^(1/(d−1)).

The exact G_d and local threshold e_0 are given in the proof. The stronger local coefficient G_d/2 applies for 0 ≤ e ≤ e_0; the zero-defect and global cases are included. The exponent 1/(d−1) is sharp by the pinned simplex-truncation construction. The square-pyramid example forces every universal coefficient at this exponent to be at least (d+1)[d(d+1)]^(1/(d−1)). The dimension dependence remains nonoptimal.

**Read:** [complete mathematical proof](POLYNOMIAL_REFINEMENT.md) · [typeset PDF](proof.pdf) · [editable LaTeX](proof.tex) · [independent analytic model audit](INDEPENDENT_REFINEMENT_AUDIT.md).

The mathematical Markdown is the authoritative frozen argument. The PDF is a faithful typeset derivative, documented in [TYPESETTING_LEDGER.md](TYPESETTING_LEDGER.md). The [weighted-anchor theorem](weighted_anchors.md) holds for every bounded centered full-dimensional probability law, in any fixed norm, and controls mean assignment distance rather than support Hausdorff distance. The [square-pyramid proof](SQUARE_PYRAMID_LOWER_BOUND.md) includes the direct facet certificate.

## Conventions and dependencies

ΠK is the projection body, with support function h_{ΠK}(u) = |K projected onto u⊥|_(d−1) for a unit u. The symbol 𝒫K denotes a pyramid over K. In each body's ambient dimension,

    R_proj(K) = |ΠK| / |K|^(d−1),
    a(K) = (d/(d+1))^d R_proj(𝒫K)/R_proj(K) − 1,
    e(K) = a(K) − 1/(d+1),
    E(K,S) = inf{t ≥ 0 : K ⊂ z_S + (1+t)(S−z_S)}.

Thus E is the excess over dilation factor one. The cone-law identity and affine invariance use the exact entry005 convention. Their [pinned v3 source](sources/entry005-v3.md) and the [v2 facet/pyramid source](sources/entry005-v2.md) are included. Cauchy's projection formula, surface-area centering and total mass, volume first variation, and Brunn–Minkowski/Minkowski first inequality are identified classical inputs. There is no smoothness or polytope restriction on the upper theorem.

[SOURCE_PINS.json](SOURCE_PINS.json) records exact copies, SHA-256 hashes and commit-specific public URLs, including the [earlier sharp proof](sources/sharp-simplex-proof.tex), [prior modulus](sources/released-explicit-modulus.md) and [sharp-exponent obstruction](sources/truncation-proof.tex). Historical copies retain their original cross-references; their fixed public URLs provide the original directory context.

## Reproduce offline

Python 3.10 or later, using only its standard library, suffices for integrity and mathematical regressions:

    python3 check_package.py
    python3 verify.py

The verifier runs all three unchanged checkers in isolated temporary directories with assertions enabled, compares the recorded regression logs and the floating constant output, and writes a report under results/. The law/witness and facet computations use exact rational arithmetic. Constant/gate computations use floating logarithms and are finite diagnostics; the universal polynomial bound is proved analytically. Platform-specific last-bit floating differences may require reviewing the recorded numerical-output comparison.

To rebuild the typeset proof, use the TeX requirements in build.sh:

    sh build.sh
    python3 check_package.py

To regenerate the deterministic archive and integrity records:

    python3 make_package.py
    python3 check_package.py

[source.zip](source.zip) contains the note and all listed source files, including the PDF, manifests and verification outputs, except the archive itself. After extraction into an empty directory, run `python3 check_package.py --extracted` and `python3 verify.py --extracted`. The manifest excludes itself, SHA256SUMS and source.zip to avoid self-reference; SHA256SUMS additionally covers MANIFEST.json. The archive uses sorted paths, fixed timestamps, stored compression and normalized permissions. Generated build/ and results/ directories are excluded.

## Review, scope and attribution

The written argument passed an independent analytic model audit. This is AI-assisted mathematical research, not human peer review or Lean/kernel verification. Finite checks do not prove the arbitrary-body or nonatomic-law quantifiers. No novelty, priority, literature-wide best-known result or affiliation claim is made.

The main Markdown and audited core are unchanged. [MATHEMATICAL_DELTA.md](MATHEMATICAL_DELTA.md) records the refinement relative to the earlier sharp proof. [SANITIZATION_LEDGER.json](SANITIZATION_LEDGER.json) records all public-report edits and original/derivative hashes. [RELEASE_SCOPE.json](RELEASE_SCOPE.json) excludes separate anisotropic and simultaneous-truncation research.

Upstream attribution remains with its original authors. See [NOTICE.md](NOTICE.md), the [unmodified upstream notice](sources/UPSTREAM_NOTICE.md) and [retained upstream license](sources/openai_math_LICENSE.txt). No new license for separately authored material has been assigned.
