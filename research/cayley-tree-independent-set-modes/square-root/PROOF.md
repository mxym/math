# Two-root comparison and deterministic centering

Let $T_n$ be a uniform labeled tree. Write $A(T)=\mathbb E[|I|\mid T]$ for the mean size of a uniform independent set, and $\mu$ for the deterministic center in the [parent theorem](../PROOF.md). We prove the three bounds stated in the [summary](README.md).

## Ball enumeration

For r≥0 consider an unlabelled rooted ball B of radius r; t is its vertex count, b the number at exact level r, and u=t−b. A rooted ball includes all vertices at distances at most r, recording no descendants of its boundary. Aut(B) is its root-preserving automorphism group order. Under PGW(1) its probability is e^{−u}/Aut(B): induct on r using the Poisson offspring law and grouping identical child shapes. Under the Poisson Kesten law this becomes b e^{−u}/Aut(B) (the finite-level size bias; also follows by marking one root-to-level-r path). Thus b≥1 on its support.

Use l=1 or 2 distinct fixed roots in a uniform labeled tree. Prescribe balls B_i of respective radii r_i and require them pairwise disjoint. Put T=Σ t_i, U=Σ u_i. When all b_i≥1 and T≤n/2, the probability of this event divided by the probability of these shapes in l independent Kesten trees is
$$L=\frac{(n-\ell)_{T-\ell}}{n^{T-\ell}}(1-U/n)^{n-T+\ell-2}e^U.\tag{S1}$$

The falling factorial counts injections of other labels after division by Π Aut(B_i). Contract each connected ball to a vertex of weight b_i, the number of its allowed attachment points; give each outside vertex weight 1. A tree extension on these n−T+l vertices has total endpoint multiplicity Π b_i·(n−U)^{n−T+l−2} by weighted Cayley–Prüfer. Conversely, expanding assigns endpoint choices at the boundary independently without changing either ball. In particular, for two adjacent boundaries the balls are still disjoint; interior connections would invalidate the shapes. Divide by n^{n−2} and the independent Kesten masses to get (S1).

Uniformly on T≤sqrt(n)/2, |L−1|≤C T²/n. For large n this follows by expanding sum_{j=l}^{T−1} log(1−j/n)=O(T²/n), and (n−T+l−2)log(1−U/n)+U=O(T²/n); the bound on this log is uniformly bounded there, so exponentiating costs only a constant. Finite n is absorbed by constants.

## Polynomial moment bounds and colliding roots

For each fixed integer d≥0 there exist C_d and A_d independent of n,r such that E |B_r(1)|^d≤C_d(r+1)^{A_d} in the Cayley model. The same bound holds about any root and for the Kesten tree. For the Cayley model the following additional bound holds for two distinct fixed labels:
$$\mathbb E[\mathbf1_{\{\mathrm{dist}(1,2)\le2r\}}(1+|B_r(1)|+|B_r(2)|)^d]\le C_d(1+r)^{A_d}/n.\tag{S2}$$

For comparison, Ralaivaosaona, Šileikis and Wagner already bound single-root level moments polynomially in their Lemma 3; the following argument also handles two colliding roots. Expand integer powers into sums over ordered tuples of at most d (possibly repeated) vertex marks. For the single-ball moment every mark has distance ≤r from the root; for (S2) first partition by which of the two balls each mark is required to belong to, and include a path of length ≤2r between the fixed roots. For every contributing choice of labels the minimal spanning subtree of the marks and root(s) is unique, has ≤(d+2)(r+1)+1 vertices and all leaves are marked or roots. Suppress all *unmarked* degree-two vertices. The remaining abstract skeleton has O_d(1) vertices (all unmarked nonsuppressed vertices have degree ≥3), finitely many marked isomorphism types including coincidences, and at most O_d(1) positive integer path lengths each bounded by O_d(r+1). The number of possible skeletal types with lengths is therefore polynomial in r+1. If such a subtree has v vertices and a=1 or 2 fixed distinct labels, the remaining labels can be assigned in at most n^{v−a} ways. A specified labeled v-vertex tree has probability v/n^{v−1} to be contained in the uniform Cayley tree, by contraction and the same weighted tree formula (also true for v=n). Thus each such expanded skeleton contributes at most v n^{1−a}; summing proves both claims. For the Kesten bound, apply ordinary root local convergence to min(|B_r|^d,L) and then take L to infinity; the Cayley bound is uniform in n. Mixed moment bounds for two arbitrary roots follow from Cauchy–Schwarz and single-root bounds; the same holds for independent Kesten roots.

## Quantitative comparison of local test functions

Suppose f_i(B_{r_i}) (l=1 or 2) satisfy |f_i|≤|B_{r_i}|. Then, for R=max_i r_i,
$$\left|\mathbb E_{\rm Cayley}\prod_i f_i-\prod_i\mathbb E_{\rm Kesten} f_i\right|\le C(1+R)^A/n.\tag{S3}$$

Here C,A can be taken absolute, independent of the functions, radii and n. On disjoint balls with T≤sqrt(n)/2, no b_i is zero: when b_i=0 the entire n-vertex tree would lie in that one ball. Use (S1) and its error bound integrated against the product Kesten laws, paying C/n times the polynomial moment E[(Π t_i)T²]. The omitted part on either measure with T>sqrt(n)/2 is bounded by (4/n) E[(Π t_i)T²], again polynomial. Overlapping balls in the l=2 Cayley law imply dist(1,2)≤r_1+r_2≤2R; use (S2) with d=2. The independent Kesten comparison needs no overlap correction. This proves (S3) for signed functions as well.

## Exponentially summable localization of one vertex's occupation

We use the hard-core message contraction already present in Ralaivaosaona, Šileikis and Wagner, §6.1 equation (44). At λ=1, let H_h be the root occupation computed on its h-ball with odds fixed at zero at depth h (all shallower terminal leaves obey the exact recursion); set H_0=0. In y=log(1+R) coordinates, the parent value is log(1+exp(−Σ y_child)), Lipschitz in the sum with factor 1/2 because R≤1. The final occupancy 1−exp(−y_root) is 1-Lipschitz on y≥0. Between the h-ball and (h−1)-ball approximations, only boundary messages at depth h−1 are changed, by at most log 2. Thus
$$Y_h=H_h-H_{h-1},\qquad |Y_h|\le (\log2)2^{1-h}|B_h|,\qquad h\ge1.$$

Fixing an arbitrary boundary does not impose a condition on the true Gibbs model: H_h exactly equals the actual root occupation once h exceeds the finite-tree radius. Thus p_v:=P(v∈I|T_n)=Σ_{h≥1}Y_h(B_h(v)), also in L^1 uniformly over n by the moment bound. The series is absolutely integrable at independent Kesten roots and products of two roots, by the moment bounds. No uniqueness assumption is needed to compare the series. Denote its Kesten expectation by m. Apply (S3) termwise with each Y_h divided by (log 2)2^{−h+1}, then sum the geometric weights times polynomials. This gives
$$\mathbb E p_1=m+O(n^{-1}),\qquad \mathbb E(p_1p_2)=m^2+O(n^{-1}).$$

The [parent theorem](../PROOF.md) gives E p_1→μ (equivalently, use its identification of the Kesten occupation expectation), so m=μ. Exchangeability and p_v∈[0,1] imply EA=nμ+O(1) and Var A=n Var(p_1)+n(n−1)Cov(p_1,p_2)=O(n).

## Transfer from conditional mean to modes: existing all-forest theorem

Use [Fang et al.](https://arxiv.org/html/2609.20961v1), Prop. 5.1 and Thm. 1.1: for every sufficiently large forest the coefficient distribution is unimodal and its unit-activity conditional variance is ≤C n. Chebyshev puts at least 3/4 of the mass in a centered interval of radius 2 sqrt(Cn). Some atom there has mass ≥c/sqrt(n). Every atom between this index and any global mode has at least that mass by unimodality, so their index distance is O(sqrt(n)) uniformly. Thus max_{m modal}|m−A(T_n)|≤C' sqrt(n) deterministically for large n. Combining with EA and Var A proves all stated conclusions.
