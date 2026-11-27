# Gaussian smoothing and the full mixing profile on a bipartite cycle torus

Let \(H_n=\{x\in\mathbb R^n:\sum_i x_i=0\}\), \(A_{n-1}=\mathbb Z^n\cap H_n\), and
\[
  V_{n,m}=H_n\otimes_{\mathbb R} H_m,\qquad
  F_{n,m}=A_{n-1}\otimes_{\mathbb Z} A_{m-1},\qquad
  \Lambda_{n,m}=F_{n,m}^*=A_{n-1}^*\otimes_{\mathbb Z}A_{m-1}^* .
\]
Use the Frobenius metric on \(n\!\times\!m\) matrices, inherited by \(V_{n,m}\), and min\((n,m)\to\infty\); there is no aspect-ratio assumption. Let \(P_s\) be the centered Gaussian of width \(s>0\) on \(V_{n,m}\), reduced modulo \(\Lambda_{n,m}\), and \(U\) Haar probability on the resulting torus. The convention is density proportional to \(e^{-\pi\|x\|^2/s^2}\).

**Theorem.** Set \(\Theta_{n,m}(a)=\sum_{X\in F_{n,m}} a^{\|X\|_F^2}\) for \(0<a<1\). If \(a\sqrt{nm}\to z\), then
\[
 \Theta_{n,m}(a)\ \longrightarrow\
 \begin{cases}
  e^{-z^2}/(1-z^2),&0\leq z<1,\\
  +\infty,&1\leq z\leq+\infty .
 \end{cases} \tag{1}
\]
For the actual wrapped law write \(q=e^{-\pi s^2}\) and assume \(q^2\sqrt{nm}\to z\). Then
\[
 \|P_s-U\|_{\mathrm{TV}}\ \longrightarrow\
 \begin{cases}
  2\Phi\!\left(\frac12\sqrt{-\log(1-z^2)-z^2}\right)-1,&0\leq z<1,\\
  1,&1\leq z\leq+\infty ,
 \end{cases} \tag{2}
\]
where \(\Phi\) is the standard normal cdf. In the subcritical range the likelihood ratio converges under \(U\) to \(\exp(\sqrt{v}\,G-v/2)\), \(v=-\log(1-z^2)-z^2\), \(G\sim N(0,1)\). In particular \(z=1\) gives TV tending to one, not a nondegenerate critical endpoint.

For fixed \(\epsilon>0\), let \(z_\epsilon\in(0,1)\) be the unique solution to \(e^{-z_\epsilon^2}/(1-z_\epsilon^2)=1+\epsilon\). With the standard convention \(\eta_\epsilon=\inf\{s:\sum_{0\ne X\in\Lambda^*}e^{-\pi s^2\|X\|^2}\leq\epsilon\}\),
\[
 \pi\eta_\epsilon(\Lambda_{n,m})^2
   =\tfrac12\log(nm)-\log z_\epsilon+o(1).
 \tag{3}
\]
The full nonconstant TV profile instead lies at \(\pi s^2=\tfrac14\log(nm)+c\), where \(z=e^{-2c}\). All cycle lengths, rather than just the shortest shell, contribute to both windows. At fixed \(c>0\) the resulting limiting TV is given by (2).

### Context and scope

[Lyubashevsky–Peikert–Regev, *On Ideal Lattices and Learning with Errors over Rings*, Def. 2.1 and Lem. 2.3](https://web.eecs.umich.edu/~cpeikert/pubs/ideal-lwe.pdf) use the smoothing invariant for a near-uniform Gaussian residue. [Micciancio–Peikert, *Hardness of SIS and LWE with Small Parameters*, Cor. 2.7](https://web.eecs.umich.edu/~cpeikert/pubs/LWsE.pdf): that bound is a general structural inequality, not an exact transition for these tori. The proof below uses a signed-cycle mixed-moment argument of the kind developed for real spiked rectangular laws by [Banerjee–Ma, Theorem 1 and §4](https://arxiv.org/abs/1804.00567); their observation law is not a wrapped heat kernel. Here the integer cycle decomposition supplies the exact full second moment, including contributions of all cycle lengths, and the circle Fourier moments directly cover unbalanced diverging dimensions. See the companion [prime-conductor torus note](prime-cyclotomic-wrapped-gaussian.md) for a single \(A^*\) factor, whose one latent circular phase has a different (non-lognormal) profile. We make no claim of an exhaustive priority search.

This is a positive statistical comparison of standalone Gaussian residues on an abstract torus. There is no hidden signal, actual parameter set, test of a protocol, or change to a computational hardness reduction.

## 1. Geometry and finite theta bounds

The set \(F_{n,m}\) consists of all integer matrices with zero row and column sums: indeed the entries indexed \(i<n,j<m\) determine the final row and column, and the tensors \((e_i-e_n)\otimes(e_j-e_m)\) are a basis. The dual is the projection of \(\mathbb Z^{n\times m}\) into \(V_{n,m}\): the projected coordinate vectors with \(i<n,j<m\) are the basis dual to these tensors, and the remaining projections are integral combinations of them. This also verifies the asserted tensor product of the dual lattices.

An oriented simple bipartite cycle of length \(2k\), \(k\geq2\), means a cyclic traversal of \(k\) distinct row vertices and \(k\) distinct column vertices, with orientation retained but no marked start. Assign \(+1\) to edges traversed from row to column and \(-1\) to edges traversed in the reverse direction. The resulting matrix is in \(F_{n,m}\). There are
\[
 N_k=(n)_k(m)_k/k
\]
such matrices: the ordered list of the row vertices and the matching ordered list of successor column vertices has \(k\) choices of the first row. Reversed traversal is the negative matrix, counted separately.

To decompose \(X\in F_{n,m}\), orient each nonzero entry from row to column when it is positive and reverse when negative, with \(|X_{ij}|\) units of arc multiplicity. Every vertex's outflow equals its inflow. A nonempty such finite directed multigraph contains a simple directed cycle; subtract one copy and iterate. There are no directed two-cycles because no single edge supports both signs. This gives a deterministic choice, by a fixed ordering, of a multiset of oriented simple cycles; the multiset recovers \(X\) by summation, so the choice is injective. Because the decomposition never cancels a nonzero sign,
\(\sum_C |C|=\sum_{ij}|X_{ij}|\leq\|X\|_F^2\). For \(0<a<1\), summing over all cycle multisets (even those not arising from the choice) gives
\[
 \Theta_{n,m}(a)\leq
 \prod_{k=2}^{\min(n,m)}(1-a^{2k})^{-N_k}. \tag{4}
\]

For a reverse bound, consider any fixed finite vector of cycle counts \(h_k\geq0\), and choose all these cycles vertex-disjoint. Let \(b=\sum_k k h_k\). The choices yield distinct matrices, since their support components uniquely recover the signed cycles. They have weight \(a^{2b}\), and their number is
\[
 \frac{(n)_b(m)_b}{\prod_{k\geq2} k^{h_k}h_k!}. \tag{5}
\]
One may sum (5) over any finite collection of such vectors.

If \(a\sqrt{nm}\to z<1\), write \(S_{n,m}=\sum_k N_k a^{2k}\). Each term tends to \(z^{2k}/k\) and is eventually dominated by \(z_0^{2k}/k\) for a fixed \(z<z_0<1\). Also \(-\log(1-a^{2k})-a^{2k}\leq a^{2k} a^4/(1-a^4)\), so the logarithm of (4) tends to \(v=\sum_{k\geq2}z^{2k}/k\). Formula (5), first for any fixed finite collection, then enlarged to all finite count vectors, gives \(\liminf\Theta\geq e^v\). This proves (1) on \(z<1\). For every finite \(z\geq1\), the lower bound from single cycles of lengths up to \(2K\) tends to \(1+\sum_{k=2}^K z^{2k}/k\); let \(K\to\infty\). If \(z=+\infty\), the four-edge cycles alone make it diverge. Finally, applying (1) at two offsets bracketing the uniquely defined \(z_\epsilon\), and using strict monotonicity of \(\Theta_{n,m}(e^{-\pi s^2})\), proves (3).

## 2. Signed cycle limits on the torus

One can lift \(U\) to independent uniform circle entries \(Y_{ij}\), then project to \(V_{n,m}\) and reduce modulo \(\Lambda_{n,m}\), since the homomorphism from the ambient product torus is onto. Likewise, to obtain \(P_s\), start with independent scalar real Gaussians of width \(s\), then project and wrap. Under the two lifts put \(\xi_{ij}=\exp(2\pi i Y_{ij})\). Under \(U\), \(\mathbb E \xi_{ij}^r\) is zero for every nonzero integer \(r\), and under \(P_s\) it equals \(q^{r^2}\) for every integer \(r\). The character of any \(X\in F_{n,m}\) depends only on the projected torus point. Define real random variables
\[
 Z_k=N_k^{-1/2}\sum_{\text{oriented cycles }C,\ |C|=2k}
                \prod_{ij}\xi_{ij}^{C_{ij}}, \quad k\geq 2. \tag{6}
\]
They are real because reverse orientations are conjugate. Under Haar they have zero mean and exact identity covariance by character orthogonality. At \(q^2\sqrt{nm}\to z<\infty\), the \(P_s\) expectation of \(Z_k\) is \(\sqrt{N_k}q^{2k}\to\mu_k=z^k/\sqrt k\).

For any fixed \(K\geq2\), the vector \(Z_2,\ldots,Z_K\) converges in law to independent unit Gaussians under Haar, and to independent unit Gaussians with means \(\mu_2,\ldots,\mu_K\) under \(P_s\). Here is a finite-diagram proof keeping \(n,m\) independent. In any mixed moment choose the ordered cycles from the factors in (6); write \(S\) for the sum of their lengths, \(e\) for the number of distinct edges, \(s_1\) for the number of edges appearing once, and \(v_r,v_c\) for the vertex counts on the two sides. Only finitely many abstract overlap diagrams occur at the given mixed order. A fixed one has \(O(n^{v_r}m^{v_c})\) labellings and has normalization of order \((nm)^{-S/4}\). Every participating vertex has distinct-edge degree at least two, so
\[
 2v_r,\ 2v_c \ \leq\ e\ \leq\ (S+s_1)/2.
\]
Under \(P_s\) the absolute expectation of any diagram term is at most \(q^{s_1}=O((nm)^{-s_1/4})\). Under Haar the term is zero if it has any singly occurring edge and at most one otherwise, giving the same argument with \(s_1=0\). Therefore all diagrams with either \(v_r<(S+s_1)/4\) or \(v_c<(S+s_1)/4\) contribute \(o(1)\), no matter how the side sizes diverge.

Equality simultaneously in these bounds forces every vertex to have degree two in the simple union and every edge to occur at most twice. The connected components are then vertex-disjoint simple cycles. On each component the whole cycle was used in one or two of the factors of the mixed moment. A twice-used cycle must have inverse orientations: equal orientations pay \(q^{4|C|}\) under \(P_s\) beyond the singly used edges, and vanish under Haar. A once-used cycle contributes \(\mu_k\) in the limit, or zero under Haar. Each inverse pair contributes one, since there are \(N_k\) choices for the first signed cycle and then exactly one for the second; the normalization is \(N_k^{-1}\). Requiring distinct components vertex-disjoint removes an \(o(1)\) proportion of choices for each fixed grouping, by the chance of coinciding a row or a column among fixed-size vertex sets. Thus the limiting sum over groupings is the Gaussian moment formula with singleton means and unit-variance pairings, restricted to pairings of equal lengths. The calculation covers every mixed moment. Tightness follows from second moments, and higher moments then pass along subsequences by uniform integrability; the joint normal law is determined by its moments. This establishes the two stated vector limits.

## 3. Full total variation, including the endpoint

The likelihood ratio \(D=dP_s/dU\) has Fourier coefficients \(q^{\|X\|_F^2}\) at \(X\in F_{n,m}\), by the Gaussian transform. Parseval gives \(\mathbb E_U D^2=\Theta_{n,m}(q^2)\). For \(z<1\), (1) says this tends to \(e^v\) with \(v=\sum_{k\geq2}\mu_k^2\). Let \(v_K=\sum_{k=2}^K\mu_k^2\), \(G=(G_2,\ldots,G_K)\) independent standard normals, and
\[
 D_K(G)=\exp\!\left(\sum_{k=2}^K\mu_k G_k-v_K/2\right).
\]
It is the density of the limiting shifted Gaussian vector relative to the unshifted vector. For a fixed \(B>0\), put \(g_B=\min(B,D_K)\), a bounded continuous function of the vector in (6). Under the two vector limits,
\[
 \begin{split}
 \mathbb E_U (D-g_B(Z))^2
  &=\mathbb E_U D^2-2\mathbb E_{P_s}g_B(Z)
                       +\mathbb E_U g_B(Z)^2\\
  &\longrightarrow e^v-e^{v_K}+
                               \mathbb E[(D_K(G)-g_B(G))^2].
 \end{split} \tag{7}
\]
Let \(B\to\infty\) at fixed \(K\), using the square integrability of \(D_K(G)\), then \(K\to\infty\). Formula (7) approximates the full likelihood by bounded functions of finitely many cycles with arbitrarily small limiting \(L^2(U)\) error. Since \(D_K(G)\) has the lognormal law with parameters \(-v_K/2,v_K\), it converges in distribution (and its absolute deviation expectation converges) to the lognormal law with \(v_K\) replaced by \(v\). Bounded Lipschitz tests of \(D\) and the function \(|D-1|\) are controlled by the \(L^2\) errors, giving the claimed likelihood limit and TV limit. The elementary Gaussian density integration yields
\(\frac12\mathbb E|\exp(\sqrt vG-v/2)-1|=2\Phi(\sqrt v/2)-1\), with the value zero at \(v=0\).

For finite \(z\geq1\), restrict to the event \(\sum_{k=2}^K\mu_k Z_k>v_K/2\). At each fixed \(K\) its limiting probability difference under the two laws is \(2\Phi(\sqrt{v_K}/2)-1\), using the same two Gaussian vector limits. Since \(v_K=\sum_{k=2}^K z^{2k}/k\to\infty\) even at \(z=1\), the TV tends to one. This argument makes no inference about TV from a divergent second moment alone. For \(z=+\infty\), widen the Gaussian to \(q'^2\sqrt{nm}=1\), eventually possible by adding an independent Gaussian before wrapping. Addition contracts TV and preserves Haar; the exact endpoint already gives the lower limit one.

## 4. A conductor-product instance

For a prime \(p\), in the canonical metric \(\langle x,y\rangle=\operatorname{Tr}(x\bar y)\) (real Euclidean coordinates with the usual \(\sqrt2\) on one member of each complex pair), the power basis \(1,\zeta_p,\ldots,\zeta_p^{p-2}\) has diagonal Gram entries \(p-1\) and off-diagonal entries \(-1\). These are the Gram entries of the basis \(\sqrt p P_{H_p} e_i\), \(i<p\), of \(\sqrt p A_{p-1}^*\). For distinct odd primes \(p,\ell\), the product power basis is an integral basis for \(\mathbb Z[\zeta_{p\ell}]=\mathbb Z[\zeta_p,\zeta_\ell]\): the rings coincide by Bézout and the two cyclotomic relations span by the product power basis, whose rank is exactly \(\varphi(p\ell)\). The embeddings are all pairs of the two sets of embeddings by the Chinese remainder theorem on exponents. Thus the Gram matrix is the tensor product of the two prime Gram matrices. The unscaled canonical integer lattice of conductor \(p\ell\) is therefore isometric to \(\sqrt{p\ell}\,\Lambda_{p,\ell}\).

Apply (1)–(3) to this normalized lattice, or multiply every squared Gaussian width in those formulas by \(p\ell\) for the unscaled canonical lattice. The resulting exact Gaussian residue transition holds for any two distinct odd primes tending to infinity, not necessarily comparably. No statement is made about CRT residues of hidden keys or any scheme.

## Reproduction

Run `python3 verify-bipartite-cycle-torus.py` (Python standard library only). It enumerates small signed circulations, checks cycle coefficients and decomposition, tests exact character moment accounting, and verifies the prime-product Gram relation on small integers. These checks are finite illustrations, not substitutes for the limiting argument.
