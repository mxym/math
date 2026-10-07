# Equality in the symmetric projection-cone bound

**mxym — AI-assisted research manuscript. Entry 005, version 4, 7 October 2026.**

This note continues [version 3](../v3/paper.md). Version 3 proved the sharp inequality
\[
a(K)\le \frac12
\]
for every centrally symmetric convex body and gave several equality families, but left the higher-dimensional equality classification open. The purpose of this version is to close that gap.

No claim of first discovery is made. The proof is independent of numerical optimization and closed solvers. The only computations in this directory are exact rational regression examples; the classification itself is a written convex-geometric proof.

## 1. Statement

Let \(K\subset\mathbb R^d\) be a full-dimensional centrally symmetric convex body, translated so that its center is the origin. Retain the affine invariant from versions 2--3,
\[
a(K)=\left(\frac d{d+1}\right)^d\frac{R(\mathcal P K)}{R(K)}-1,
\qquad
R(K)=\frac{|\Pi K|}{|K|^{d-1}}.
\]

### Theorem 1.1. Complete equality classification

For every \(d\ge1\),
\[
\boxed{a(K)=\frac12}
\]
if and only if, after an invertible linear change of coordinates,
\[
\boxed{K=K_1\times\cdots\times K_m,}
\]
where every factor \(K_j\) is centrally symmetric and has dimension one or two.

Thus the equality class is exactly the affine Cartesian-product closure of intervals and centrally symmetric planar bodies.

In dimension three this says that equality holds exactly for affine prisms over centrally symmetric planar bodies. In every dimension \(d\ge3\), an equality body is reducible as a nontrivial Cartesian product; consequently every centrally symmetric body that is affinely indecomposable, strictly convex, or \(C^1\)-smooth has
\[
a(K)<\frac12.
\]

The converse direction is already implicit in version 3: every centrally symmetric planar body has \(a=1/2\), every interval has \(a=1/2\), and the product formula
\[
a(A\times B)=
\frac{\dim(A)a(A)+\dim(B)a(B)}{\dim(A)+\dim(B)}
\]
preserves the value \(1/2\). The rest of this note proves necessity. The case \(d=1\) is immediate, so Sections 2--7 may assume \(d\ge2\).

## 2. The equality set in the balanced Rademacher inequality

Version 3 used the following fact. If real coefficients \(c_1,\ldots,c_N\) satisfy
\[
|c_i|\le \frac12\sum_j|c_j|
\qquad\text{for every }i,
\tag{2.1}
\]
then independent uniform signs \(\epsilon_i\) satisfy
\[
\mathbb E_\epsilon\left|\sum_i\epsilon_i c_i\right|
\le \frac12\sum_i|c_i|.
\tag{2.2}
\]

We need the exact equality set.

### Lemma 2.1. Equality in the balanced Rademacher estimate

Assume (2.1), and put \(M=\sum_i|c_i|\). Equality holds in (2.2) if and only if at least one of the following occurs:

1. at most three coefficients \(c_i\) are nonzero;
2. some coefficient satisfies \(|c_i|=M/2\).

**Proof.**
The zero case is immediate. Otherwise absorb the signs of the \(c_i\), divide by \(M\), and write
\[
t_i=\frac{|c_i|}{M},\qquad
t_i\in[0,1/2],\qquad
\sum_i t_i=1.
\]
Let
\[
F(t)=\mathbb E_\epsilon\left|\sum_i\epsilon_i t_i\right|.
\]

If \(t_k=1/2\), set \(Z=\sum_{i\ne k}\epsilon_i t_i\). Since \(|Z|\le1/2\),
\[
\frac12\left(\left|\frac12+Z\right|+
\left|-\frac12+Z\right|\right)=\frac12.
\]
Averaging over the remaining signs gives \(F(t)=1/2\).

If at most three \(t_i\) are positive, equality is the two- and three-variable identity already proved in version 3. In the three-variable case, after ordering the nonnegative coefficients and using the balance inequalities,
\[
\frac14\bigl[
(t_1+t_2+t_3)+(-t_1+t_2+t_3)
+(t_1-t_2+t_3)+(t_1+t_2-t_3)
\bigr]=\frac12.
\]

Conversely, suppose that exactly \(m\ge4\) coordinates are positive and every one is strictly below \(1/2\). On their support \(I\), the point \(t\) lies in the relative interior of
\[
P_I=
\left\{s_i\ge0:\ \sum_{i\in I}s_i=1,\ s_i\le\frac12,\
s_i=0\ (i\notin I)\right\}.
\]
The function \(F\) is convex, and version 3 gives \(F\le1/2\) on \(P_I\).

If \(F(t)=1/2\), then \(F\) must equal \(1/2\) everywhere on \(P_I\). Indeed, for any \(y\in P_I\), relative interiority of \(t\) lets us write
\[
t=\alpha y+(1-\alpha)z
\]
with \(z\in P_I\) and \(0<\alpha<1\). Convexity gives
\[
\frac12=F(t)
\le \alpha F(y)+(1-\alpha)F(z)
\le\frac12,
\]
so \(F(y)=1/2\).

But \(P_I\) contains the point with four coordinates equal to \(1/4\) and all remaining coordinates zero. For that point,
\[
F=\frac{2\cdot1+8\cdot(1/2)}{16}
=\frac38<\frac12,
\]
a contradiction. \(\square\)

## 3. Exposed points eliminate the second equality mechanism

Let \(C\subset\mathbb R^d\) be an origin-symmetric full-dimensional convex body. For boundary points \(x_1,\ldots,x_{d+1}\in\partial C\), let \(c_i\) be the signed horizontal cofactors, so
\[
\sum_{i=1}^{d+1}c_i x_i=0.
\tag{3.1}
\]
The Minkowski norm with unit ball \(C\) gives the balance condition
\[
|c_i|\le\sum_{j\ne i}|c_j|,
\]
hence Lemma 2.1 applies.

### Lemma 3.1. Exposed tuples have only short equality circuits

Assume every \(x_i\) is an exposed point of \(C\). If equality holds in the balanced Rademacher estimate associated with (3.1), then at most three cofactors \(c_i\) are nonzero.

**Proof.**
Suppose at least four cofactors are nonzero. Lemma 2.1 then forces
\[
|c_k|=\sum_{j\ne k}|c_j|
\tag{3.2}
\]
for some \(k\). Rearranging (3.1) and using (3.2),
\[
x_k
=
\sum_{j\ne k}
\frac{|c_j|}{|c_k|}
\left(-\operatorname{sgn}(c_kc_j)x_j\right).
\tag{3.3}
\]
The coefficients on the right are nonnegative and sum to one. Because \(C\) is symmetric, every sign-changed point on the right belongs to \(C\); the point on the left is exposed. Therefore every right-hand point with positive weight must equal the exposed point on the left.

Hence all columns with nonzero cofactor are parallel up to sign. A nonzero cofactor implies that the full \((d+1)\)-tuple has rank \(d\), so its kernel is one-dimensional and is spanned by the cofactor vector. Three or more parallel columns would already produce at least a two-dimensional space of relations supported on those columns, a contradiction. Thus the assumed four nonzero cofactors are impossible. \(\square\)

The exposed-point hypothesis is genuinely needed for this lemma. Section 9 gives an exact boundary-law example attaining the Rademacher equality through a four-point circuit whose distinguished point lies in the relative interior of a face.

## 4. Cone-volume laws are exposed almost everywhere

For a centered full-dimensional convex body \(K\), version 3 defines its cone-volume law \(\nu_K\) as follows. With support function \(h_K\) and surface area measure \(S_K\), use the probability measure
\[
\frac{h_K(u)}{d|K|}\,dS_K(u)
\]
on the sphere and push it forward under
\[
u\longmapsto \frac{u}{h_K(u)}.
\tag{4.1}
\]
The image lies on \(\partial K^\circ\).

### Lemma 4.1. Almost every cone-volume point is exposed

Let \(C=K^\circ\). Then
\[
\nu_K(\operatorname{Exp} C)=1,
\]
where \(\operatorname{Exp} C\) denotes the exposed points of \(C\).

**Proof.**
The surface area measure is the Gauss-map pushforward of \((d-1)\)-dimensional Hausdorff measure on the regular part of \(\partial K\). A convex body has a unique outer normal at \(\mathcal H^{d-1}\)-almost every boundary point.

Take such a regular boundary point \(y\), let \(u\) be its unique outer unit normal, and put
\[
x=\frac{u}{h_K(u)}\in C.
\]
Then \(\langle x,y\rangle=1\). If \(z\in C\) also satisfies \(\langle z,y\rangle=1\), then for every \(w\in K\),
\[
\langle z,w-y\rangle\le0,
\]
so \(z\) belongs to the normal cone of \(K\) at \(y\). Regularity says that this cone is the ray generated by \(u\), and the equality \(\langle z,y\rangle=1\) fixes the scalar. Hence \(z=x\).

Thus the hyperplane with normal \(y\) exposes \(x\) in \(C\). Since the nonregular part of the boundary has zero \(\mathcal H^{d-1}\)-measure and the weight \(h_K\) in (4.1) is strictly positive, the pushed-forward probability law is concentrated on exposed points. \(\square\)

## 5. A rank-two decomposition theorem for equality laws

We now isolate the linear-algebraic consequence of Lemma 3.1.

The finite-support structural statement below is the representable case of an
established matroid fact. A matroid whose circuits all have at most three elements
is \(U_{3,4}\)-minor-free and is a direct sum of matroids of rank at most two;
see van der Pol–Walsh–Wigal, *Turán densities for matroid basis hypergraphs*,
[arXiv:2502.03673v2](https://arxiv.org/html/2502.03673v2#S5), Section 5 and
Lemma 5.2. We include a direct proof for the almost-sure measure formulation
needed here. This structural fact is distinct from the preceding cone-volume
argument that forces short circuits at equality.

### Lemma 5.1. Almost-sure short circuits force a direct sum of lines and planes

Let \(\nu\) be a spanning probability measure on \(\mathbb R^d\). Assume there is a full-\(\nu\)-measure set \(E\) such that, for \(\nu^{\otimes(d+1)}\)-almost every tuple in \(E^{d+1}\), the cofactor vector has at most three nonzero entries.

Then there is a direct-sum decomposition
\[
\mathbb R^d=V_1\oplus\cdots\oplus V_m,
\qquad
\dim V_j\in\{1,2\},
\tag{5.1}
\]
such that
\[
\nu\left(\bigcup_jV_j\right)=1.
\tag{5.2}
\]

**Proof.**
Let \(G\subset E^{d+1}\) be the full-measure set of tuples with the asserted cofactor support bound. Replace \(G\) by its intersection over all coordinate permutations; it remains full measure and makes the condition explicitly permutation invariant.

Since \(\nu\) spans \(\mathbb R^d\),
\[
\mathbb E|\det(X_1,\ldots,X_d)|>0,
\]
so the set of independent \(d\)-tuples has positive \(\nu^{\otimes d}\)-measure.

Fubini's theorem applied to \(G\) gives a full-measure subset \(H\subset E^d\) such that every \((b_1,\ldots,b_d)\in H\) has the following section properties:

1. for \(\nu\)-almost every \(x\), the tuple
   \((b_1,\ldots,b_d,x)\) lies in \(G\);
2. for every \(j\), for \(\nu^{\otimes2}\)-almost every \((x,y)\), the tuple consisting of \(x,y\) and all \(b_i\) with \(i\ne j\) lies in \(G\).

The finitely many section conditions still define a full-measure set. Intersect \(H\) with the positive-measure independent-basis event and choose
\[
b_1,\ldots,b_d\in E
\tag{5.3}
\]
from that intersection.

Write
\[
x=\sum_{i=1}^d\alpha_i(x)b_i.
\]
For almost every \(x\), the tuple in property 1 has rank \(d\), and its unique relation is
\[
x-\sum_i\alpha_i(x)b_i=0.
\]
Its cofactor support therefore has size
\[
1+\#\{i:\alpha_i(x)\ne0\}\le3.
\]
Thus almost every \(x\) has at most two nonzero coordinates in the basis (5.3).

For \(i<j\), let
\[
E_{ij}=
\{x:\alpha_i(x)\alpha_j(x)\ne0,\
\alpha_\ell(x)=0\text{ for }\ell\notin\{i,j\}\}.
\]
Make a graph on \(\{1,\ldots,d\}\) by declaring \(ij\) to be an edge when \(\nu(E_{ij})>0\).

This graph has maximum degree at most one. Suppose instead that \(ij\) and \(jk\) are two edges with distinct \(i,j,k\). By property 2 for the omitted index \(j\), we may choose
\[
x\in E_{ij},\qquad y\in E_{jk}
\]
from a positive-product-measure set such that the tuple made from \(x,y\) and all basis vectors except \(b_j\) belongs to \(G\). Write
\[
x=\alpha_i b_i+\alpha_j b_j,\qquad
y=\beta_j b_j+\beta_k b_k,
\]
with all four displayed coefficients nonzero. Then
\[
\beta_jx-\alpha_jy
-\beta_j\alpha_i b_i+\alpha_j\beta_k b_k=0.
\tag{5.4}
\]
The tuple spans \(\mathbb R^d\), because the basis vector \(b_j\) is recovered from \(x\) and \(b_i\). Hence its kernel is one-dimensional, and (5.4) is its cofactor relation up to scale. It has exactly four nonzero entries, contradicting membership in \(G\).

Therefore the positive-measure two-coordinate planes form pairwise disjoint pairs of basis indices. For each graph edge \(ij\), take
\[
V=\operatorname{span}(b_i,b_j).
\]
Every basis index not lying on an edge supplies the one-dimensional block \(\operatorname{span}(b_i)\). These blocks are in direct sum, and every almost-sure one- or two-coordinate vector lies in their union. This proves (5.1)--(5.2). \(\square\)

## 6. Surface-area support on rank-two blocks forces a product

The previous lemma is measure-theoretic. The next convex-geometric step turns it into a decomposition of the body itself.

### Lemma 6.1. Block-supported surface area measure implies Cartesian product structure

Suppose
\[
\mathbb R^d=W_1\oplus\cdots\oplus W_m
\]
is an orthogonal direct sum and the surface area measure of a full-dimensional convex body \(K\) is supported on
\[
\bigcup_j(W_j\cap S^{d-1}).
\tag{6.1}
\]
Let \(K_j\) be the orthogonal projection of \(K\) onto \(W_j\). Then
\[
K=K_1\times\cdots\times K_m
\]
under the indicated orthogonal decomposition.

**Proof.**
Put
\[
P=K_1\times\cdots\times K_m.
\]
Every point of \(K\) has its \(W_j\)-component in \(K_j\), so \(K\subseteq P\).

For \(u\in W_j\),
\[
h_P(u)=h_{K_j}(u)=h_K(u).
\]
Because of the support condition (6.1),
\[
\int h_P\,dS_K
=
\int h_K\,dS_K
=
d|K|.
\tag{6.2}
\]
The first mixed-volume formula gives
\[
V(K[d-1],P)=\frac1d\int h_P\,dS_K=|K|.
\]
Minkowski's first inequality therefore yields
\[
|K|
\ge |K|^{(d-1)/d}|P|^{1/d},
\]
hence
\[
|P|\le|K|.
\]
The inclusion \(K\subseteq P\) gives the reverse volume inequality. Thus \(|K|=|P|\), and inclusion of full-dimensional compact convex bodies with equal volume forces \(K=P\). \(\square\)

The orthogonality assumption loses no generality in an affine classification. For a direct sum \(V_1\oplus\cdots\oplus V_m\), choose an invertible linear map \(L\) whose inverse transpose sends the \(V_j\) to mutually orthogonal coordinate subspaces. Outer-normal directions transform by \(L^{-\mathsf T}\), so the surface-area support condition transforms with the same block decomposition.

## 7. Proof of Theorem 1.1

Assume \(d\ge2\) and \(a(K)=1/2\). Let
\[
C=K^\circ,\qquad \nu=\nu_K.
\]
Version 3 proves
\[
B(\nu)\le\frac{d+1}{2}A(\nu),
\tag{7.1}
\]
and, through the exact cone-volume representation,
\[
a(K)=\frac{B(\nu)}{(d+1)A(\nu)}.
\tag{7.2}
\]
Hence our equality assumption makes (7.1) an equality.

The proof of (7.1) is pointwise after independent sign averaging. Its nonnegative pointwise defect therefore vanishes for \(\nu^{\otimes(d+1)}\)-almost every tuple. By Lemma 4.1, almost every sampled point is exposed in \(C\). Lemma 3.1 then shows that almost every tuple has a cofactor vector with at most three nonzero entries.

Lemma 5.1 supplies a direct-sum decomposition
\[
\mathbb R^d=V_1\oplus\cdots\oplus V_m,
\qquad \dim V_j\le2,
\]
with
\[
\nu\left(\bigcup_jV_j\right)=1.
\]
The map \(u\mapsto u/h_K(u)\) is a positive radial rescaling and therefore preserves membership in each linear subspace. Since the cone-volume weight \(h_K\) is strictly positive, the preceding statement is equivalent to
\[
S_K\left(
S^{d-1}\setminus\bigcup_jV_j
\right)=0.
\tag{7.3}
\]

Apply an invertible linear map so that the transformed normal blocks are orthogonal. Lemma 6.1 then shows that the transformed body is the Cartesian product of its projections onto these blocks. Because \(K\) is centrally symmetric, every projected factor is centrally symmetric. Each block has dimension one or two. This proves necessity.

Conversely, let
\[
K=K_1\times\cdots\times K_m
\]
with centrally symmetric factors of dimensions one or two. Every interval has \(a=1/2\), and version 3 proves \(a=1/2\) for every centrally symmetric planar body. Repeated use of the exact product formula gives \(a(K)=1/2\). Affine invariance completes the converse. \(\square\)

## 8. Consequences

### Corollary 8.1. Three-dimensional equality

For a centrally symmetric three-dimensional body,
\[
a(K)=\frac12
\]
if and only if \(K\) is affinely equivalent to
\[
B\times I,
\]
where \(B\) is a centrally symmetric planar convex body and \(I\) is an interval.

### Corollary 8.2. Strictness for indecomposable bodies

If \(d\ge3\) and \(K\) is centrally symmetric but is not affinely equivalent to a nontrivial Cartesian product, then
\[
a(K)<\frac12.
\]

### Corollary 8.3. Strictness for strictly convex or smooth bodies

If \(d\ge3\) and \(K\) is centrally symmetric and either strictly convex or \(C^1\)-smooth, then
\[
a(K)<\frac12.
\]

**Reason.**
A Cartesian product of at least two positive-dimensional compact convex bodies contains nontrivial boundary line segments, so it is not strictly convex. Its boundary also has points at which two factors are simultaneously on their boundaries; at such a point the normal cone has dimension at least two, so the boundary is not \(C^1\). In dimension \(d\ge3\), a decomposition into blocks of dimensions at most two necessarily has at least two positive-dimensional factors. \(\square\)


### Theorem 8.4. Dimensionwise stability of the symmetric equality class

Fix \(d\ge1\) and \(\varepsilon>0\). There is
\[
\delta_{\mathrm{sym}}(d,\varepsilon)>0
\]
such that every centrally symmetric full-dimensional \(K\subset\mathbb R^d\) satisfying
\[
a(K)\ge\frac12-\delta_{\mathrm{sym}}(d,\varepsilon)
\]
is within Banach--Mazur factor \(1+\varepsilon\) of the equality class. More explicitly, there are an equality body \(E\) from Theorem 1.1 and an invertible linear map \(T\) such that
\[
T E\subseteq K\subseteq(1+\varepsilon)T E.
\tag{8.1}
\]

The modulus is uniform in fixed dimension but is not made explicit.

**Proof.**
Because both the hypothesis and conclusion are affine invariant, put every centrally symmetric body in symmetric John position:
\[
B_2^d\subseteq K\subseteq\sqrt d\,B_2^d.
\tag{8.2}
\]
The family of bodies satisfying (8.2) is compact in the Hausdorff topology, and \(a\) is continuous there.

If the theorem failed for some fixed \(d,\varepsilon\), there would be a sequence \(K_n\) in John position with
\[
a(K_n)\longrightarrow\frac12
\]
but whose Banach--Mazur distance from every equality body is greater than \(1+\varepsilon\). Pass to a Hausdorff-convergent subsequence \(K_n\to K_\infty\). The common inscribed ball keeps the limit full-dimensional and centrally symmetric, while continuity gives
\[
a(K_\infty)=\frac12.
\]
Theorem 1.1 therefore makes \(K_\infty\) an equality body.

Let \(\eta>0\). For all sufficiently large \(n\), Hausdorff convergence and the common inclusion \(B_2^d\subseteq K_n,K_\infty\) give
\[
K_n\subseteq K_\infty+\eta B_2^d\subseteq(1+\eta)K_\infty,
\]
and symmetrically
\[
K_\infty\subseteq(1+\eta)K_n.
\]
Hence
\[
\frac1{1+\eta}K_\infty
\subseteq K_n
\subseteq(1+\eta)K_\infty.
\]
Taking \(E=(1+\eta)^{-1}K_\infty\), which remains in the equality class, yields
\[
E\subseteq K_n\subseteq(1+\eta)^2E.
\]
Choose \(\eta\) with \((1+\eta)^2<1+\varepsilon\). This contradicts the assumed distance gap and proves the theorem. \(\square\)

In dimension three, Theorem 8.4 says that every centrally symmetric body with \(a(K)\) sufficiently close to \(1/2\) is uniformly close, after an affine map, to a prism over a centrally symmetric planar body. Obtaining an explicit power-law dependence of \(\delta_{\mathrm{sym}}\) on \(\varepsilon\) remains open.

## 9. Why arbitrary boundary-law equality is broader

The convex-body classification uses Lemma 4.1 in an essential way. An arbitrary even law supported on the boundary of a symmetric body can attain equality in version 3 without having the rank-two block structure.

In \(\mathbb R^3\), let \(C\) be the \(\ell_1\)-unit ball and put
\[
q=\frac13(1,1,1).
\]
Take the uniform law on
\[
\{\pm e_1,\pm e_2,\pm e_3,\pm q\}\subset\partial C.
\]
Exact rational enumeration gives
\[
A=\frac3{16},\qquad B=\frac38,\qquad
\frac{B}{4A}=\frac12.
\]
The four points
\[
e_1,e_2,e_3,q
\]
form the circuit
\[
e_1+e_2+e_3-3q=0,
\]
whose normalized absolute coefficients are
\[
\frac16,\frac16,\frac16,\frac12.
\]
This is precisely the second equality mechanism in Lemma 2.1. The point \(q\) is not extreme in \(C\); it lies in the relative interior of a triangular face. Hence Lemma 3.1 does not apply.

The exact script in this directory verifies this example, the four-equal-coefficient strict case \(F=3/8\), and the inherited three-dimensional boundary-law benchmark values using only rational arithmetic.

## 10. Verification scope and remaining questions

The proof of Theorem 1.1 is analytic and finite-dimensional. Its non-elementary inputs are standard convex-geometric facts already used in version 3: surface area measure as Gauss-map pushforward, almost-everywhere regularity of convex boundaries, the first mixed-volume formula, and Minkowski's first inequality.

The exact regression script is supplementary and does not certify the general theorem. It is designed to catch two tempting but false shortcuts:

1. equality for an arbitrary even boundary law does **not** force the convex-body product classification;
2. the strict part of Lemma 2.1 fails when a coefficient reaches exactly one half of the total absolute mass.

This version closes the higher-dimensional equality question explicitly left open in version 3. It does not determine an effective stability modulus below \(1/2\), nor the optimal recursive spectral supremum from version 2. Those remain the principal open directions within entry 005.

## 11. Provenance

The definitions, cone-volume representation, sharp symmetric inequality, exact product formula, and planar equality statement are inherited from entry 005 versions 2--3. The equality classification above is a continuation built on those statements.

The upstream projection-volume product identity and simplex calculations trace to OpenAI family 088, pinned at commit \`adc7f1241b42e322a6451854ab7e4b4c146bf78a\`, as documented in the earlier versions. This note makes no claim that the classification has no antecedent in the convex-geometric or random-simplex literature; a focused literature comparison is still required before any priority statement.
