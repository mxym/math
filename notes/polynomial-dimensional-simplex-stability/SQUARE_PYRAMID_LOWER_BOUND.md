# A stronger realized lower bound for the endpoint coefficient

For every d≥3, a universal coefficient in the every-maximum-simplex estimate must satisfy

    G_d ≥ (d+1)[d(d+1)]^(1/(d−1)).

This is realized by the explicit full-dimensional polytope and maximum simplex below. The construction, maximality, barycentric excess, invariant calculation, and direct facet certificate were independently analytically audited. No arbitrary law is treated as a convex-body realization. The generic facet formula a=L/(d|K|H) is the formula in the pinned entry005-v3.md, Section 1. The optional pyramid calculation provides a second route; the direct certificate avoids needing that recursion as an extra input.

## 1. An elementary global bound on the geometric excess

If \(S=\operatorname{conv}(v_0,\ldots,v_d)\) is maximum-volume in \(K\), its barycentric coordinates satisfy
\[
 |\alpha_i(x)|\le1\qquad(x\in K).
\]
Indeed, replacing \(v_i\) by \(x\) multiplies volume by \(|\alpha_i(x)|\).
Centroid dilation has the exact characterization
\[
 x\in z_S+(1+t)(S-z_S)
 \quad\Longleftrightarrow\quad
 \alpha_i(x)\ge-\frac{t}{d+1}\ \text{for every }i.
\]
Consequently
\[
 \boxed{E(K,S)\le d+1.} \tag{1}
\]
This applies to every maximum simplex without a normalization or a small-deficit hypothesis. It is much sharper than the coarse outer-radius bound used as the large-deficit branch in the supplied proof.

## 2. The square-pyramid construction

Take
\[
 C_d=\operatorname{conv}(0,e_1,e_2,e_1+e_2,e_3,\ldots,e_d),\qquad
 S_d=\operatorname{conv}(0,e_1,\ldots,e_d).
\]
This is the standard unit square followed by \(d-2\) pyramids. The square has \(a=1/2\), and each pyramid adds one to \(1/a\), so
\[
 a(C_d)=\frac1d,\qquad e(C_d)=\frac1{d(d+1)}. \tag{6}
\]

To check maximality directly, a full-dimensional vertex simplex must contain every \(e_3,\ldots,e_d\), since no other vertex has a nonzero corresponding coordinate. It must also contain exactly three square vertices. Every such triangle has area \(1/2\), so every full-dimensional vertex simplex has volume \(1/d!\). The absolute determinant is separately convex in its vertices, hence no simplex with arbitrary vertices in \(C_d\) has larger volume. In particular, \(S_d\) is maximum.

The point \(e_1+e_2\) has barycentric coordinates
\[
 (-1,1,1,0,\ldots,0)
\]
in \(S_d\). Hence \(E(C_d,S_d)\ge d+1\), with equality by (1). Combining these identities proves the stated necessary lower bound for every universal coefficient.

There is also a direct facet certificate for (6), independent of the pyramid recursion. Put \(c=1/(d-1)!\). The facet area-normal/support pairs are
\[
 (-c e_1,0),\quad(-c e_2,0),\quad(-2c e_i,0)\ (3\le i\le d),
\]
\[
 \left(c(e_1+\sum_{i=3}^d e_i),c\right),\qquad
 \left(c(e_2+\sum_{i=3}^d e_i),c\right).
\]
The corresponding halfspaces describe the square cross-sections
\(0\le x_1,x_2\le1-\sum_{i=3}^d x_i\).
Its volume is \(2/d!\). Direct maximal-minor sums give
\[
 H=c^d d2^{d-1},\qquad L=c^{d+1}2^d,
\]
so \(a=L/(d|C_d|H)=1/d\). To count \(L\), only the four subsets obtained by omitting either top facet or either of the first two coordinate facets contribute, each by \(c^{d+1}2^{d-2}\). For \(H\), the contributions with zero, one, or two top facets are respectively \(1,d,d-1\), all multiplied by \(c^d2^{d-2}\).

The lower bound from the supplied small-truncation family is
\[
 L_d^{\rm small}=(d+1)\left[\frac{(d+1)^2}{d(d-1)}\right]^{1/(d-1)}.
\]
The new bound is strictly larger since
\[
 \left(\frac{L_d^{\rm square}}{L_d^{\rm small}}\right)^{d-1}
 =\frac{d^2(d-1)}{d+1}>1\qquad(d\ge3).
\]
For example, the new bounds for \(d=3,4,5\) are approximately \(13.8564,13.5721,14.0421\), respectively. Numerical values are illustrative only; the formula is exact.

