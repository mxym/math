# Proof audit — entry 005 version 4

**Date:** 7 October 2026
**Claim audited:** complete equality classification for the sharp centrally symmetric bound \(a(K)\le1/2\).

## 1. Dependency boundary

Version 4 uses the following established results from entry 005 versions 2--3:

- affine invariance and continuity of \(a\);
- the product identity
  \[
  a(A\times B)=\frac{r a(A)+s a(B)}{r+s};
  \]
- the cone-volume representation
  \[
  a(K)=\frac{B(\nu_K)}{(d+1)A(\nu_K)};
  \]
- for an even boundary law, the pointwise balanced-cofactor argument giving
  \[
  B\le\frac{d+1}{2}A;
  \]
- equality \(a=1/2\) for intervals and for every centrally symmetric planar body.

The v3 exact replay of these ingredients was rerun before this version was written: 23 rational laws, 18,199 ordered lifted tuples, 1,149 balanced-sign tests, five spectral examples, 126 direct octahedron minors, and seven deliberate corruptions all passed, with byte-identical ordinary and optimized-Python reports.

Standard external convex-geometric inputs are: almost-everywhere regularity of convex boundaries, the Gauss-map description of surface area measure, the first mixed-volume formula, and Minkowski's first inequality.

## 2. New logical chain

### A. Exact Rademacher equality set

For balanced coefficients \(c_i\), equality in
\[
\mathbb E|\sum\epsilon_i c_i|\le\frac12\sum|c_i|
\]
occurs exactly when the support has size at most three or one absolute coefficient is exactly half the total. The strict direction is proved by convexity on the capped simplex and the interior test point \((1/4,1/4,1/4,1/4)\), whose value is \(3/8\).

**Audit check:** the argument does not assume strict convexity of the expectation functional; it uses the valid fact that a convex function bounded above by a constant and attaining that constant at a relative-interior point must be constant on the entire face.

### B. Exposedness removes the half-mass circuit

For exposed boundary points of a symmetric convex body, a half-mass cofactor relation writes one exposed point as a convex combination of signed boundary points. Exposedness forces every positive-weight term to be the same point. Four or more nonzero cofactors would then give at least three parallel columns, producing at least two independent relations and contradicting the rank-\(d\) cofactor situation.

**Audit check:** equation (3.3) divides the original cofactor relation by \(c_k\); the signed point on the right is \(-\operatorname{sgn}(c_kc_j)x_j\). This sign was explicitly rechecked.

### C. Cone-volume points are exposed almost surely

At a regular boundary point \(y\) of \(K\), its unique outer normal \(u\) gives \(x=u/h_K(u)\in K^\circ\). If \(z\in K^\circ\) also obeys \(\langle z,y\rangle=1\), then \(z\) is in the normal cone of \(K\) at \(y\), which is the ray through \(u\); normalization forces \(z=x\). Hence \(y\) exposes \(x\).

**Audit check:** surface-area measure is obtained from the Gauss map on the regular boundary, and the cone-volume density \(h_K\) is strictly positive because the origin is interior.

### D. Almost-sure short circuits imply rank-two blocks

A basis is chosen from a full-measure set of Fubini-good sections intersected with the positive-measure independent-basis event. A new sample can then have at most two nonzero basis coordinates. If two positive-measure coordinate planes shared a basis index, two generic samples from those planes plus all basis vectors except the shared one would have a unique four-term dependence, contradicting the short-circuit hypothesis. Hence the positive-measure coordinate planes form a matching, and the law is supported on a direct union of one- and two-dimensional subspaces.

**Audit check:** there are finitely many coordinate pairs, so zero-measure two-coordinate classes can be discarded simultaneously. The constructed tuple spans because one of the two samples recovers the omitted basis vector.

### E. Normal blocks force a Cartesian product

After an affine map, make the normal blocks orthogonal. Let \(K_j\) be the block projections and \(P=\prod K_j\). Then \(K\subseteq P\), while \(h_P=h_K\) on the support of \(S_K\). Thus
\[
V(K[d-1],P)=|K|.
\]
Minkowski's first inequality gives \(|P|\le|K|\); inclusion gives the reverse inequality, so \(K=P\).

**Audit check:** this direction uses no unproved uniqueness statement for the Minkowski problem. Equal volume plus actual inclusion is enough.

### F. Dimensionwise near-equality stability

The stability theorem is a compactness consequence, not a quantitative estimate. Symmetric John's theorem puts every body into
\[
B_2^d\subseteq K\subseteq\sqrt d\,B_2^d.
\]
This normalized family is Hausdorff compact. Continuity of \(a\) sends any sequence with \(a(K_n)\to1/2\) to an equality limit after taking a subsequence, and the common inscribed ball upgrades Hausdorff convergence to multiplicative containment.

**Audit check:** the proof only claims a fixed-dimensional nonexplicit modulus. It does not infer any dimension-uniform rate or power-law exponent.

## 3. Guard examples

The exact script \`code/check_examples.py\` verifies a boundary-law equality case that is not of the cone-volume exposed-point type:
\[
\nu=\text{uniform on }\{\pm e_1,\pm e_2,\pm e_3,\pm(1,1,1)/3\}.
\]
It has
\[
A=3/16,\qquad B=3/8,\qquad B/(4A)=1/2.
\]
The circuit
\[
e_1+e_2+e_3-3q=0
\]
has normalized absolute coefficients \(1/6,1/6,1/6,1/2\). This prevents the proof from silently replacing "cone-volume law" by "arbitrary even boundary law."

## 4. Remaining nonclaims

This audit does **not** establish:

- an explicit quantitative stability estimate for \(1/2-a(K)\);
- the optimal recursive spectral supremum from version 2;
- bibliographic novelty or priority;
- proof-assistant formalization.

Within the stated theorem, no numerical optimizer, floating-point comparison, random search, or solver output is a proof dependency.
