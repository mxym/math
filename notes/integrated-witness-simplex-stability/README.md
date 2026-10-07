# Integrated witness simplex stability

For every full-dimensional compact convex body $K\subset\mathbb R^d$, $d\ge3$, and every maximum-volume inscribed simplex $S$ with centroid $z$, this package proves

$$E(K,S)\le G_d^*\bigl(a(K)-1/(d+1)\bigr)^{1/d},\qquad E(K,S)=\inf\{t\ge0:K\subset z+(1+t)(S-z)\}.$$

All constants, smallness gates and the global large-deficit branch are explicit in paper.md, paper.tex and paper.pdf. No symmetry, smoothness, atom or uniqueness hypothesis is imposed. Every maximum simplex is covered with its own centroid. The integrated-witness assignment error is linear in the original determinant defect. No quantitative inverse-Minkowski theorem is a dependency.

The proved exponent is $1/d$. A separate simplex-truncation obstruction gives a ceiling $1/(d-1)$; the gap is unresolved. Its obstruction proof is separate and is not an input to the present bound. Constants are dimension-dependent and very conservative.

An independent analytic model audit passed without required mathematical corrections. INDEPENDENT_AUDIT.md distinguishes the analytic obligations from finite arithmetic checks. This is not human peer review, full proof-assistant formalization or an optimal-exponent assessment.

Run sh replay.sh, sh build.sh, python3 check_package.py and python3 -O check_package.py. The build uses no network. Requirements and exact tested versions are in VERIFICATION.md. Build/cache products are isolated under build/. source.zip is a deterministic clean archive with the exact whitelist in PACKAGE_FILES.txt; after extraction use python3 check_package.py --extracted. make_package.py intentionally refreshes the manifest/archive only after reviewed edits. It does not publish.

Read DEPENDENCIES.json for pinned input hashes and NOTICE.md for provenance. No third-party full research papers are redistributed.
