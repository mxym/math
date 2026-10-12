# Sharp lower-end simplex stability

For every fixed integer d >= 3, every convex body K in R^d and every
maximum-volume inscribed simplex S, the proof establishes

    E(K,S) <= G_d^sharp [a(K) - 1/(d+1)]^(1/(d-1)).

Here E is the least excess dilation about S's own centroid needed to contain
K. The invariant a has exactly the entry005 projection-cone normalization.
The constants G_d^sharp and the stronger local constant are explicit in
proof.tex, equations (1)--(5). The zero-defect and global cases are included.
The one-vertex truncation family rules out every larger power, so 1/(d-1)
is sharp for this stated theorem class. The constants are very large.

Start with proof.pdf (eight pages) or the authoritative editable proof.tex.
proof.txt is a searchable rendering, not a replacement for the formulas.
The previous 1/d note is preserved separately under sources/prior-integrated-witness.
No novelty, priority, literature-wide best-known-rate or journal guarantee
is claimed.

## Argument

Integrated determinant witnesses choose an enclosing polar simplex.
Centering corrects the assigned weights to its actual cone-law weights,
so Cauchy's formula controls brightness in every direction. First variation
restores absolute scale. A Hausdorff gap survives a suitable projection,
where a cap has (d-1)-dimensional volume. The existing stochastic-matrix
conversion then retains every originally prescribed maximum simplex.
No inverse-Minkowski stability theorem is an input.

## Reproduce offline

Requirements: Python 3 standard library, a configured TeX installation with
pdflatex/pdftex/kpsewhich and the packages used by proof.tex, and Poppler's
pdftotext. No network, package installation or shell escape is used.

    python3 check_package.py
    python3 verify.py
    python3 -O check_package.py

verify.py replays the supplied checker, the independent sharp-endpoint
checker, the prior independent witness checker and the pinned truncation
checker normally and with Python -O. It checks equality of logs/certificates,
rebuilds the PDF twice, rejects unresolved references and overfull boxes,
and records the result in results/verification.json. build.sh alone rebuilds
the PDF/text. It uses a writable TeX cache when an installed Debian TeX tree
lacks a discoverable format; this does not install or alter system packages.
Build/replay scratch files are kept under build/ and excluded from the archive.

To test the source archive, extract source.zip into an empty directory and
run the same commands in sharp-simplex-stability, with
python3 check_package.py --extracted for the initial/final integrity checks.
The archive includes every whitelisted file except itself. make_package.py
recreates it deterministically; MANIFEST.json and SHA256SUMS cover every
payload file apart from their own self-referential entries and source.zip.

## Review and evidence

The complete independent analytic model audit passed with no mathematical
corrections. See INDEPENDENT_ANALYTIC_AUDIT.md and AUDIT_RESULT.json. The
written proof handles arbitrary convex bodies and nonatomic laws; finite
regressions do not prove those quantifiers. The independent polytope checker
uses approximate atan2 only to order facet vertices, then exact rational
coordinates, areas, volumes, identities and inequality comparisons. This
is not formal certification. No human peer review is claimed.

The supplied certificate includes 8 constant dimensions, 380 affine-basis
values, 1,560 weight corrections, 240 weight bounds, 204 projection directions,
12,887 integrated-witness sample tuples and 120 every-maximum matrix cases.
The independent sharp-endpoint certificate includes 3,240 affine-basis values,
6,000 nonuniform corrections, 1,200 weight bounds, 7,200 brightness comparisons,
280 polytope projection cases and 35 each of cap and scale cases.

## Source and editorial provenance

PROVENANCE.json pins public revisions and exact readable bytes. Every
mathematical source dependency is included locally. The earlier quantitative
source was cited historically at one commit and read for this proof at another;
the same SHA-256 bytes are identified explicitly. The old fallback's theorem
and constants are represented by the already public 1/d source, whose exact
editorial relationship and historical hash are disclosed. The original
historical sources and prior published note have not been overwritten.

EDITORIAL_CHANGES.md and SOURCE_CHANGES.json record every proof replacement.
Only author/PDF metadata, completed audit status and public provenance prose
change. The mathematical core is byte-for-byte unchanged. NOTICE.md discloses
AI-assisted research and retained upstream attribution/license records.
