# A two-shape reduction for size \(91\) in \(\mathbb F_{13}^{3}\)

> Follow-up: the [complete exclusion of size 91](FugledeF13Size91Geometric.md) now rules out both hypothetical shapes. This note gives only the earlier two-shape reduction.

If \((E,A)\) is a spectral pair of size \(91=7\cdot13\), each member, after a possibly different affine change of coordinates, is one of:
1. a union of seven \(13\)-point slices in distinct parallel affine planes (no points on the other planes);
2. an injective lift of the triangular planar domain
   \[
   T=\{(u,v)\in\{1,\ldots,13\}^2:\ u+v\ge14\},
   \]
   with each coordinate reduced modulo \(13\).

This is an exact restriction on any hypothetical pair, not a nonexistence theorem. In particular the heights of the triangular lift and shapes within each occupied layer in case 1 are not settled.

## The witness forces a pencil with at least eleven uniform normals

Write \(p=13\) and \(m=7\). Let \(U_B\subset\mathrm{PG}(2,13)\) be the directions of nonzero Fourier zeros of \(1_B\), equivalently normals in which each perpendicular affine plane has occupancy \(7\). Write \(V_B\) for its projective complement. For a member \(B\) and partner \(B'\), \(D(B')\subseteq U_B\) by spectrality. The standard pencil count gives no projective line contained in \(U_B\) and the standard plane cap gives occupancy at most \(13\), as proved in the [companion dense-cardinality note](FugledeF13DenseCardinalities.md). These are also Ferguson–Iosevich [arXiv:2610.30712v1](https://arxiv.org/html/2610.30712v1), Lemma 8.2.

If every projective line has at most ten points in \(U_B\), then \(V_B\) is 4-fold blocking (at least four points on every projective line). Choose an inclusion-minimal 4-fold blocking subset \(S\) of \(V_B\) and write \(N=|S|\). [Bishnoi–Mattheus–Schillewaert, Theorem 1.1](https://arxiv.org/abs/1703.07843) gives \(N\le108\), and equality requires every line to have intersection size \(4\) or \(9\). Those intersections are both \(4\bmod5\). Sum the intersections of the fourteen lines through any projective point \(P\): the result is \(N+13\mathbf1_S(P)\equiv 56\bmod5\). At \(N=108\) this forces \(\mathbf1_S(P)\equiv1\bmod5\) for all \(P\), impossible. Thus \(N\le107\). Alternatively the published classification of equality cases in that theorem immediately excludes equality at prime \(13\) with fold \(4\).

Use the positive Fourier witness of [Malikiosis, §§5–6](https://doi.org/10.1007/s43670-023-00078-2). In ambient \(\mathbb F_p^3\), set \(h(x)=1\) on each punctured direction in \(S\), zero at other nonzero vectors, and \(h(0)=N-4p\). With unnormalized transform, for \(y\ne0\) summing all nonzero scalars in each projective direction gives \(\hat h(y)=p(|S\cap y^\perp|-4)\ge0\). At zero, \(\hat h(0)=p(N-4)\). The support condition gives \(h(b-b')=0\) for distinct \(b,b'\in B'\). Hence, by Fourier inversion and positivity,
\[
 |B'|h(0)=\sum_{b,b'\in B'}h(b-b')
   =p^{-3}\sum_y\hat h(y)|\widehat{1_{B'}}(y)|^2
   \ge p^{-3}\hat h(0)|B'|^2 .
\]
The bound \(|B'|\le p^2(N-4p)/(N-4)\le169\cdot55/103<91\) is a contradiction (the fraction is increasing in \(N>4\)). Therefore there is a pencil with at least eleven uniform normals for each member.

## Classify the high-uniformity pencil

Let \(P\) be the two-dimensional space of normals generating such a pencil, and project \(B\) from \(\mathbb F_{13}^{3}\) onto \(\mathbb F_{13}^{3}/P^\perp\). Write \(f(x,y)\) for the integer multiplicities in the two-dimensional quotient, and \(K\) for the number of uniform normals in the pencil, so \(11\le K\le13\). Let \(L=14-K\in\{1,2,3\}\). Choose coordinates in the quotient so a uniform direction is vertical and the remaining \(L\) nonuniform profiles are \(g_i(y-s_i x)\), with distinct \(s_i\); \(g_i(t)\) is the sum of \(f\) along the indicated level.

The fourteen affine lines through a point in the quotient count its multiplicity fourteen times and all others once. Removing the uniform profiles gives the integer identity
\[
 \sum_{i=1}^{L}g_i(y-s_ix)=m(L-1)+p f(x,y).
\]
Reducing modulo \(p\) and representing \(g_i\) by their polynomials of degree at most \(12\), the identity is a formal polynomial identity since each variable has degree at most \(12\). For a positive homogeneous degree \(j\), the coefficients \(c_{ij}\) of \(t^j\) satisfy \(\sum_i c_{ij}s_i^h=0\) for \(0\le h\le j\) using invertible binomial coefficients. Thus for \(j\ge L-1\) the Vandermonde matrix forces all those coefficients to vanish. This is the general-prime version of Ferguson–Iosevich's Lemma 8.4.

If all residues \(g_i(t)\) are constant, the integer bounds \(0\le g_i(t)\le13\) and total \(91\) imply that each is either constantly \(7\) or a vector of seven entries \(13\) and six zero entries. Uniform profiles were removed, so only the latter can occur among the \(g_i\); reducing the projection identity modulo \(13\) requires \(7(L-1)\equiv0\), thus \(L=1\). The identity then gives the indicator of seven parallel lines, and its inverse images give the seven occupied full planes in shape 1. This covers \(L=1,2\) and rules out the all-constant residue case at \(L=3\).

At \(L=3\) all profiles are affine modulo \(13\). The linear coefficient relation has a minimal dependence among its three distinct forms: any two are linearly independent. Hence once one is nonconstant, all three are nonconstant. Each profile takes every residue once, and the value representing residue zero must be \(13\) rather than \(0\), because the total is \(91=1+\cdots+13\). Thus interpret the three profile values as integers \(u,v,w\) in \(1,\ldots,13\). Their sum is \(14+13f(x,y)\). Since it is between \(3\) and \(39\), \(f\) is Boolean and the projection is injective. Two distinct affine normal forms with nonzero slopes in their own arguments give independent coordinates \(u,v\) modulo \(13\). The third is the unique representative \(w\in\{1,\dots,13\}\) with \(w\equiv14-u-v\pmod {13}\). For \(u+v\le13\) it equals \(14-u-v\), and for \(u+v\ge14\) it equals \(27-u-v\). The identity gives exactly \(f=\mathbf1_T\). This proves shape 2.
