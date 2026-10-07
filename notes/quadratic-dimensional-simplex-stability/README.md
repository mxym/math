# Quadratic-dimensional sharp simplex stability

**mxym — AI-assisted mathematical supplement, 7 October 2026.**

For every integer $d\ge 3$, every full-dimensional convex body $K\subset\mathbb R^d$, and **every prescribed maximum-volume inscribed simplex** $S$, with its own original centroid $z_S$,

$$E(K,S)\le G_d\,e(K)^{1/(d-1)},$$

$$G_d=16(d+1)^2\left[3d^2(d+1)^3(d+2)\right]^{1/(d-1)}\le4096d^2,
\qquad G_d\sim16d^2.$$

Here $E(K,S)=\inf\{t\ge0:K\subseteq z_S+(1+t)(S-z_S)\}$. The deficit uses the original projection/pyramid invariant:

$$R_{\rm proj}(K)=\frac{|\Pi K|}{|K|^{d-1}},\quad
a(K)=\left(\frac d{d+1}\right)^d\frac{R_{\rm proj}(\mathcal P K)}{R_{\rm proj}(K)}-1,
\quad e(K)=a(K)-\frac1{d+1}.$$

$\Pi K$ is the projection body and $\mathcal P K$ is a pyramid over $K$, with the conventions of the bundled [original manuscript](sources/entry005-v3.md). This is the same invariant as in the earlier sharp-stability theorem. The deficit exponent $1/(d-1)$ remains sharp by the actual simplex-truncation family. The dimension coefficient improves the earlier $O(d^6)$ refinement to $O(d^2)$; the optimal dimension order remains between linear and quadratic.

## Read the complete proof

These three readable Markdown files form one proof:

1. [Main theorem and all-branch assembly](QUADRATIC_DIMENSION_THEOREM.md)
2. [Intrinsic norm conversion](INTRINSIC_NORM_CONVERSION.md)
3. [Relative projection caps and every-maximum-simplex retention](intrinsic_caps/INTRINSIC_GEOMETRIC_BRIDGE.md)

The complete [first-moment weighted-anchor proof](imports/weighted_anchors.md), [earlier polynomial refinement](imports/POLYNOMIAL_REFINEMENT.md), and [cone-law source](sources/entry005-v3.md) are bundled. [SOURCE_GUIDE.md](SOURCE_GUIDE.md) identifies the precise imported statements. The [square-pyramid lower bound](imports/SQUARE_PYRAMID_LOWER_BOUND.md) records the previously audited linear obstruction. There is no dependence on an unbundled new construction or conjecture.

The full public text is provided in Markdown; a newly typeset PDF is not included in this edition. All three new proofs and the substantive imported anchor and cone-law arguments are readable without a PDF or an external service. Earlier sharpness source files are also included as exact TeX copies.

## Review status and limits

The complete written argument received an [independent analytic model audit: PASS](INDEPENDENT_QUADRATIC_AUDIT.md). That audit checked the actual cone law, first absolute determinant moments, norm duality, original centroid, every prescribed maximum, strict endpoint gates, zero deficit, affine caps, matching bootstrap, and the uniform constant. It required no mathematical repair.

This is model-audited written mathematics. It is not Lean or other proof-assistant verification, external human peer review, a novelty certification, or a determination of the optimal dimension order. Finite exact checks support normalization and arithmetic only; the analytic proof establishes the unrestricted theorem. [MATHEMATICAL_DELTA.md](MATHEMATICAL_DELTA.md) separates the mathematical refinement from the public-copy editorial changes.

## Verify the release

Python 3 and SymPy are needed for the independent exact convex-body checker. The integrity checker itself uses only Python's standard library.

From this directory:

    python check_package.py
    python -O check_package.py
    python verify.py
    python -O verify.py

After extracting source.zip, use `--extracted` with either checker or runner because the ZIP does not contain itself:

    python check_package.py --extracted
    python verify.py --extracted

`verify.py` runs all five checks in a temporary copy with optimization explicitly disabled, including when the runner itself is invoked with `-O` or `PYTHONOPTIMIZE` is set. It compares the outputs with the recorded evidence and rechecks integrity. No proof or recorded evidence is rewritten. On success it writes only `results/verification.json`.

The quadratic exact checker covers nine actual bodies, 696 projection directions in the strict-gate cases, all 36 vertex-set maximum simplices of those bodies, 400 rational relative-deficit comparisons, and matching endpoints. These do not substitute for the universal written argument.

`python make_package.py` regenerates MANIFEST.json, SHA256SUMS, and source.zip deterministically. It is a packaging operation, not a validity check; use check_package.py before accepting a received release. Hashes bind bytes and detect changes against a trusted copy; they do not certify authorship or mathematical correctness.

## Sources and rights

All required special imports have exact local copies or tracked public-clean derivatives and SHA-256 pins in [SOURCE_PINS.json](SOURCE_PINS.json). [AUDITED_ORIGINAL_SOURCE_HASHES.json](AUDITED_ORIGINAL_SOURCE_HASHES.json) distinguishes the original audited bytes from public derivatives. [SOURCE_FIDELITY.json](SOURCE_FIDELITY.json) and [SANITIZATION_LEDGER.json](SANITIZATION_LEDGER.json) record unchanged sources and each editorial operation. Historical source copies retain their original cross-references and broader scopes; their exact public commit URLs provide the original surrounding context.

See [NOTICE.md](NOTICE.md), the unchanged [upstream notice](sources/UPSTREAM_NOTICE.md), and the unchanged [upstream license text](sources/openai_math_LICENSE.txt). No new blanket license is assigned to separately authored material.
