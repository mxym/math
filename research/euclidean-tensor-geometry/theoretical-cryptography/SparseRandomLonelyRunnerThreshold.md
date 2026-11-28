# The logarithmic transition for the random Lonely Runner model

Let \(S=S_{N,m}\) be a uniform \(m\)-element subset of \(\{1,\ldots,N\}\), with \(m\ge1\), and put
\[
                  L(S)=\max_{t\in\mathbb R/\mathbb Z}\min_{v\in S}\|vt\|.
\]
Distances are circular distances to the nearest integer, and logarithms are natural.

**Theorem.** For every sequence \(m=N^{o(1)}\), define \(D_N=(1-N^{-1/m})/2\). Then
\[
                                L(S)/D_N\longrightarrow1
                                \quad\text{in probability}.
\tag{1}
\]
In particular:
\[
\begin{array}{c|l}
m/\log N\longrightarrow 0 & L(S)\longrightarrow 1/2,\\
m/\log N\longrightarrow c\in(0,\infty) & L(S)\longrightarrow (1-e^{-1/c})/2,\\
m/\log N\longrightarrow\infty & mL(S)/\log N\longrightarrow 1/2.
\end{array}
\]
The last assertion is in the same subpolynomial regime. Together with the [previous varying-density theorem](VaryingDensityRandomLonelyRunner.md) this removes the earlier growth restriction \(m/(\log N)^2\to\infty\) on the subpolynomial edge, and retains the previous formula when \(\log m/\log N\) tends to a strictly positive exponent. This is a typical-value statement, not a deterministic Lonely Runner lower bound.

[Czerwiński](https://arxiv.org/abs/1102.4464) proves the \(1/2\) limit at fixed dimension, and [Beck–Everett v3, Corollary 6 and Theorem 7 proof](https://arxiv.org/pdf/2609.06259v3) give another fixed-dimension result and an exponential-range upper bound at particular constants for a different construction. Neither is the logarithmic transition (1). The proof here declares a prime-grid point or ordered pair exceptional by a *short dual normal*. A typical pair then has a uniformly accurate forbidden-set intersection, rather than merely a coarse upper bound.

## 1. Dual normals and the rectangular counts

We first prove a threshold criterion. Consider a sequence \(0<\delta=\delta_N\le\delta_*<1/2\) such that \(\delta^{-1}=N^{o(1)}\), and set
\[
  \sigma_N(\delta)=-\,m\log(1-2\delta)/\log N,\qquad
  B_\delta(t)=\{v\in\{1,\ldots,N\}:\|vt\|<\delta\}.
\]
A time reaches gap at least \(\delta\) exactly if its forbidden set misses the sample. We will show that success occurs with probability tending to one if \(\limsup\sigma_N(\delta)<1\), and with probability tending to zero if \(\liminf\sigma_N(\delta)>1\).

Choose a prime \(p\asymp N/\delta\) greater than \(N\); Bertrand's postulate allows this with any required fixed large multiplicative constant. For \(d=2,3\) and \(\mathbf a=(a_1,\ldots,a_{d-1})\in\mathbb F_p^{d-1}\), use the full-rank lattice
\[
 \Lambda_{\mathbf a}=\{(v,x_1,\ldots,x_{d-1})\in\mathbb Z^d:
                          x_i\equiv a_i v\pmod p\}.
\]
Its determinant is \(p^{d-1}\). Its dual consists of \(\mathbf w/p\) for \(\mathbf w\in\mathbb Z^d\) with
\[
                       w_0+\sum_{i=1}^{d-1}a_iw_i\equiv0\pmod p:
\tag{2}
\]
take dot products with the basis \((1,a_1,\ldots,a_{d-1})\) and the \(p e_i\) for \(i\ge1\). For any fixed small \(\eta>0\), call \(\mathbf a\) good if the shortest nonzero dual vector has length at least \(N^{-1+\eta}\). A bad vector has a nonzero integer relation in (2) with coordinate absolute values at most \(pN^{-1+\eta}\). Counting all integer vectors in this cube enlarges the exceptional set. Since the coordinate bound is \(<p\), any possible relation has some nonzero coefficient modulo \(p\) among \(w_1,\ldots,w_{d-1}\); otherwise (2) also forces \(w_0=0\). Each relation has at most \(p^{d-2}\) solutions for \(\mathbf a\). Consequently bad numerators at \(d=2\) number at most \(N^{2\eta+o(1)}\), and bad ordered pairs at \(d=3\) occupy fraction at most \(N^{-1+3\eta+o(1)}\) of all pairs.

For a good lattice, all \(d\) successive minima are \(O_d(N^{1-\eta})\) in Euclidean norm. To see this, choose \(d-1\) independent vectors with lengths at most the first \(d-1\) successive minima in order (they can be chosen by greedily passing through the successive ranks). Their oriented orthogonal product divided by \(\det\Lambda\) is a nonzero dual vector: its dot product with any lattice vector is a determinant ratio in \(\mathbb Z\). Therefore
\[
 \lambda_1(\Lambda^*)\le
 \frac{\lambda_1(\Lambda)\cdots\lambda_{d-1}(\Lambda)}{\det\Lambda},
 \qquad \lambda_d(\Lambda)\lambda_1(\Lambda^*)\le C_d
\]
by Minkowski's second theorem for the Euclidean ball (for example, [Lagacé, Theorem 2.1](https://doi.org/10.4153/S0008414X19000130)). Choose \(d\) independent lattice vectors of length \(O_d(N^{1-\eta})\), generating a full-rank sublattice with parallelepiped diameter \(O_d(N^{1-\eta})\). A box with each side comparable to \(N\) has lattice point count its volume divided by \(\det\Lambda\), with relative error \(O(N^{-\eta})\). Indeed the centered parallelepiped tiles space within each coset of the sublattice; the union of tiles whose centers lie in the box is between its erosion and its enlargement by a constant times the diameter. These two volumes differ from the box volume by relative \(O(N^{-\eta})\). Divide by the sublattice determinant and sum over the cosets, using their number equal to the determinant ratio. This argument does not require the short vectors to be a basis of the whole lattice.

Use the box with \(v\) coordinate in \([1/2,N+1/2]\) and every \(x_i\) coordinate in \((-\delta p,\delta p)\). The latter interval, being of length less than \(p\), includes at most one lift of a given residue. All box sides are comparable to \(N\), even if \(\delta\to0\), by the choice of \(p\). The lattice points correspond exactly to the speeds in the relevant one or two forbidden sets. Hence, uniformly at a good numerator \(a\) and a good ordered pair \((a,b)\), respectively,
\[
 \frac{|B_\delta(a/p)|}{N}=2\delta+O(N^{-\eta}),\qquad
 \frac{|B_\delta(a/p)\cap B_\delta(b/p)|}{N}=4\delta^2+O(N^{-\eta}).
\tag{3}
\]
Strict endpoints cause no change to the volume argument. The same facts hold for any chosen threshold comparable to \(\delta\) with the same prime.

## 2. Lower bound by a weighted second moment

For any fixed forbidden set \(B\) of size \(b\), write \(P(B)=\Pr(S\cap B=\varnothing)\). It is at most \((1-b/N)^m\), with zero probability when \(N-b<m\). When \(N-b\ge c_0N\) for a fixed positive \(c_0\), its exact falling factorial ratio
\[
 P(B)=\frac{(N-b)(N-b-1)\cdots(N-b-m+1)}
                 {N(N-1)\cdots(N-m+1)}
\]
is \((1-b/N)^m(1+O_{c_0}(m^2/N))\) uniformly: factor out the indicated power and bound the logarithmic correction term by \(O_{c_0}(\sum_{j<m}j/N)\). Here \(m=N^{o(1)}\).

Suppose \(\sigma_N(\delta)\le\sigma_0<1\) eventually, and choose \(\eta>0\) so small that \(\sigma_0+3\eta<1\). Let \(\mathcal T\) be all good numerators \(a\) on the prime grid, a set of size \(p(1-o(1))\). Write \(w=1-2\delta\) and \(B_a=B_\delta(a/p)\). By (3),
\[
                            P(B_a)=w^m(1+o(1))
\]
uniformly. If \(a,b\) are both individually good and the ordered pair is good, the complement of \(B_a\cup B_b\) has size \(N(w^2+O(N^{-\eta}))\). Applying the uniform falling factorial estimate then gives \(P(B_a\cup B_b)=w^{2m}(1+o(1))\). The relative errors are \(o(1)\) because \(w\ge1-2\delta_*>0\), \(m^2/N=o(1)\), and \(mN^{-\eta}=o(1)\).

Consider \(Y=\sum_{a\in\mathcal T}\mathbf1_{S\cap B_a=\varnothing}/P(B_a)\). It has expectation \(|\mathcal T|\). A good ordered pair contributes \(1+o(1)\) to the average of the normalized second moment. A bad pair contributes at most \((1+o(1))w^{-m}\), by \(P(B_a\cup B_b)\le\min(P(B_a),P(B_b))\), including diagonal pairs. The exceptional fraction is \(O(N^{-1+3\eta+o(1)})\), and \(w^{-m}\le N^{\sigma_0}\); the total bad contribution tends to zero. Hence the variance divided by \((\mathbb E Y)^2\) tends to zero, and some test succeeds with probability tending to one.

## 3. Upper bound on the same kind of prime grid

Suppose \(\liminf\sigma_N(\delta)>1\). Choose \(0<\gamma<1/2\) constant small enough that \(\delta'=(1-\gamma)\delta\) still has \(\liminf\sigma_N(\delta')>1\). This can be done uniformly because \(f(x)=-\log(1-2x)\) satisfies
\[
 0\le f(\delta)-f(\delta')\le \frac{2\gamma\delta}{1-2\delta_*}
                       \le \frac{\gamma}{1-2\delta_*}f(\delta).
\]
Now choose the prime \(p\asymp N/(\gamma\delta)\) with \(p\ge N/(\gamma\delta)\). If a time succeeds at \(\delta\), a nearest grid point succeeds at \(\delta'\), since each distance changes by at most \(N/(2p)\le\gamma\delta/2\). All good grid points have the one-test count (3) with \(\delta'\). They have success probability \((1+o(1))(1-2\delta')^m\) each and at most \(p=N^{1+o(1)}\) tests, so the probability any of them succeeds tends to zero.

For the bad grid points use a deterministic uniform lower bound on forbidden-set size. Partition the circle into \(K=\lceil 2/\delta'\rceil\) equal half-open arcs, and place the \(N+1\) points \(0,t,\ldots,Nt\) modulo 1 in them, counted with multiplicity. The number of pairs of distinct indices in the same arc is at least \(((N+1)^2/K-(N+1))/2\), by Cauchy–Schwarz. For large \(N\) this is at least \((N+1)^2/(4K)\), since \(K=N^{o(1)}\). The positive difference of the indices of each pair lies in \(B_{\delta'}(t)\); each difference has at most \(N+1\) representations. Thus \(|B_{\delta'}(t)|\ge N\delta'/12\) uniformly, since \(K\le3/\delta'\). The probability of success is at most \(\exp(-m\delta'/12)\). The inequality \(f(\delta')\le 2\delta'/(1-2\delta_*)\) and \(\sigma_N(\delta')>1\) eventually show that this is at most \(N^{-(1-2\delta_*)/24}\). Choose \(\eta>0\) small enough that \(2\eta<(1-2\delta_*)/24\). There are at most \(N^{2\eta+o(1)}\) bad numerators. Their total success probability tends to zero also. This completes the upper threshold criterion.

## 4. From the threshold to the stated limit

By construction \(m f(D_N)=\log N\). Also \(D_N^{-1}=N^{o(1)}\): \(1-e^{-x}\gg\min(x,1)\) at \(x=\log N/m\). For \(0<\epsilon<1\), the threshold \(\delta_-=(1-\epsilon)D_N\) is bounded away from \(1/2\) and has \(m f(\delta_-)\le(1-\epsilon)\log N\) by convexity and \(f(0)=0\). The lower criterion applies.

For the upper bound, indices at which \((1+\epsilon)D_N\ge1/2\) need no test. On the other indices take \(\delta^\flat=(1+\epsilon/2)D_N\), which is bounded above by \((1+\epsilon/2)/(2(1+\epsilon))<1/2\). By convexity \(m f(\delta^\flat)\ge(1+\epsilon/2)\log N\). The upper criterion applies along these indices and excludes \(L(S)\ge(1+\epsilon)D_N\) with probability tending to one. This proves (1), including sequences where \(m/\log N\) does not converge.

The [companion standard-library checker](verify_sparse_random_lonely_runner.py) checks finite exact versions of the single- and pair-lattice counters, dual-exception enumeration, the deterministic lower bound, and falling-factorial ratio identities. It is not a numerical substitute for the asymptotic argument.
