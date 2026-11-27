# Covariance trade-offs for unbiased lattice rounding

**Scope.** A geometric probability problem for an abstract Euclidean lattice. The canonical ring and codifferent of an odd-prime cyclotomic field give examples. This does not analyze a cryptosystem, prescribe parameters for one, or identify any rounded distribution as a discrete Gaussian.

## 1. A common-threshold kernel and its exact quadratic optimality cone

Write \(N=n+1\), and let \(b_1,\ldots,b_N\) be a superbase of a rank-\(n\) lattice \(\Lambda\subset\mathbb R^n\): their sum is zero, and any \(n\) generate the lattice. Write \(B:\mathbb R^N\to\mathbb R^n\) for the matrix with these columns. An unbiased rounding kernel specifies \(W\in\Lambda\) at each input \(x\), with \(\mathbb E[W\mid x]=x\) and finite second moment. Require translation equivariance in law under adding lattice vectors, so the law of the error \(W-x\) is defined on \(\mathbb R^n/\Lambda\).

At \(x=Bt\), a particular unbiased kernel is
\[
  W_0=B\lfloor t+U\mathbf 1\rfloor, \qquad U\sim\operatorname{Unif}[0,1).
                                                        \tag{1}
\]
The same scalar \(U\) is used in all coordinates. Adding a multiple of \(\mathbf1\) to the lift \(t\) simply rotates \(U\bmod1\) and adds a common integer inside the floor, which \(B\) kills. Integer changes of lift translate \(W_0\) by the expected lattice vector. Since \(\mathbb E\lfloor v+U\rfloor=v\) for every real \(v\), the rule is unbiased.

For each \(i<j\) write \(\lambda_{ij}\) for the real functional on \(\mathbb R^n\) with \(\lambda_{ij}(Bv)=v_i-v_j\). This is well-defined because \(\ker B=\mathbb R\mathbf1\); it takes integer values on the lattice. A symmetric cost matrix \(M\) satisfies the Selling identity
\[
  (Bv)^TM(Bv)=\sum_{i<j}p_{ij}(v_i-v_j)^2,\qquad
  p_{ij}=-b_i^T M b_j.                                  \tag{2}
\]
Indeed \(B^T M B\) has zero row sums and the indicated off-diagonals. For an integer-valued random variable of mean \(d\), the minimum variance is \(\{d\}(1-\{d\})\), attained exactly on \(\lfloor d\rfloor,\lceil d\rceil\). This follows by averaging the nonnegative polynomial \((k-\lfloor d\rfloor)(k-\lfloor d\rfloor-1)\) on integers \(k\). In (1) the output difference \(\lfloor t_i+U\rfloor-\lfloor t_j+U\rfloor\) is one of these adjacent integers for mean \(t_i-t_j\). Thus it minimizes all edge variances at once.

In particular, **(1) is optimal at each input for the cost \(\mathbb E[(W-x)^TM(W-x)\mid x]\) if and only if every \(p_{ij}\ge0\)**. The same necessary and sufficient condition holds for average cost with Haar-uniform input modulo \(\Lambda\). For necessity, choose an open region where the phases of labels \(i,j\) are adjacent in the sorted order, with no ties and with both phases strictly inside the unit interval. The support of (1) contains a state \(w\) before either threshold crosses, \(w+b_i\) between them (label \(i\) crosses first), and \(w+b_i+b_j\) after both. These three vertices may be read cyclically because \(\sum b_i=0\). Remove a small positive equal mass from the first and last and add it to \(w+b_i\) and \(w+b_j\). The mean is unchanged, and the cost change per unit mass is
\[
  (w+b_i-x)^TM(w+b_i-x)+(w+b_j-x)^TM(w+b_j-x)
   -(w-x)^TM(w-x)-(w+b_i+b_j-x)^TM(w+b_i+b_j-x)
  =2p_{ij}.
\]
If \(p_{ij}<0\), this strictly improves the cost on a positive-Haar-measure part of the torus. For \(n=1\) the only edge has \(b_j=-b_i\): the same mean-preserving variation replaces some mass at the lattice point represented by the two outside states with mass at the two neighboring directions, so the conclusion also holds for a negative cost. If all \(p_{ij}>0\), the minimizing conditional law is unique at distinct phases: every difference must be an adjacent integer, forcing the normalized lattice coordinates into a single nested chain. This chain has \(N\) affinely independent vertices and the mean fixes the barycentric probabilities. Strictly positive edges include the ordinary Euclidean metric in the regular superbase of \(A_n^*\).

## 2. Haar error law and the covariance cone

With Haar input, the error of (1) has exactly the distribution \(B Z\), where the \(Z_i\) are independent uniform variables on \([-1/2,1/2]\). In fact we can represent Haar input modulo \(\Lambda\) by \(B t\) with \(t_i\) independent uniform on \([0,1)\): the map from \(\mathbb R^N/\mathbb Z^N\) to \(\mathbb R^n/\Lambda\) sends Haar measure to Haar measure. The error is \(-B\{t+U\mathbf1\}\). Conditional on \(U\), the fractional parts are still independent and uniform. Centering the cube and changing its sign do not change the pushforward law. Thus its covariance is
\[
 \Sigma_0=\frac{1}{12} B B^T.                            \tag{3}
\]
A near-Haar input with density in \([1-\epsilon,1+\epsilon]\) relative to Haar gives the same likelihood bounds for the pushed-forward error law. This applies, for example, to a wrapped continuous Gaussian under the corresponding dual mass assumption by Poisson summation. It gives covariance bounds \((1-\epsilon)\Sigma_0\preceq\Sigma\preceq(1+\epsilon)\Sigma_0\). Unbiasedness also implies that the input and the rounding error have zero cross-covariance; thus this describes the additive covariance, without requiring independence or a Gaussian output.

Let \(\Sigma\) be the average error covariance of any such kernel under Haar. Coordinate the covariance set using \(\lambda_{ij}\Sigma\lambda_{ij}^T\). The squares \(\lambda_{ij}^2\) are a basis for the symmetric quadratic forms, as is seen by pulling back along \(B\) and reading the distinct off-diagonal entries in (2). The fractional part of \(t_i-t_j\) is uniform modulo 1, so
\[
   \lambda_{ij}\Sigma\lambda_{ij}^T\ \ge\
    \int_0^1 r(1-r)\,dr=\frac16
    =\lambda_{ij}\Sigma_0\lambda_{ij}^T.                  \tag{4}
\]
The perturbation above changes \(\Sigma\) by \(-b_i b_j^T-b_j b_i^T\) per unit mass. Applying any \(\lambda_{k l}^2\) to this change gives zero for every other edge and \(2\) for \(\{k,l\}=\{i,j\}\). For \(N\ge3\), choose disjoint open positive-measure regions with the required adjacency, one for each edge, with an interior bound on the two removable masses. Applying the perturbations independently produces a small box of nonnegative slacks in every edge coordinate. Hence (4) describes the covariance set in a neighborhood of \(\Sigma_0\), and its cone of directions there is the full nonnegative orthant. The cone of costs minimized at \(\Sigma_0\) is exactly the Selling cone of (2). This is not Loewner dominance: the single-edge covariance perturbation is indefinite for independent \(b_i,b_j\), so for \(n\ge2\) no Haar covariance minimizes all positive semidefinite costs simultaneously. If such a covariance existed it would have to be \(\Sigma_0\), since all edge costs separately have the lower bounds (4), whose equality determines the matrix.

## 3. An exact edge of the global covariance set

Fix one pair \(\{i,j\}\) and require equality in (4) for every other pair. For \(N\ge3\), the precise range of its excess variance is
\[
 \boxed{\quad
   0\ \le\ \lambda_{ij}\Sigma\lambda_{ij}^T-\frac16
             \ \le\ \frac{2}{N(N-1)} .
       \quad}                                          \tag{5}
\]
It is attained throughout the interval. Here the base \(B\) can be any superbase; all coordinates in (5) are measured using the indicated lattice functionals.

To prove the upper bound, equality for each other edge means it must saturate its pointwise variance bound almost everywhere. Write \(f_i=\{t_i\}\) and subtract the integer part of each coordinate from the candidate lattice lift, with common integer shifts of the lift irrelevant. For any constrained edge with \(f_k>f_l\), the resulting integer difference must be 0 or 1. At almost every input all phases are distinct. Suppose \(f_i>f_j\). If some \(f_k\) is strictly between them, the constraints via \(k\) imply that the exceptional difference belongs to \(\{0,1,2\}\). If some other phase is outside their interval, they imply the difference belongs to \(\{-1,0,1\}\). If both situations occur, the exceptional bound is also saturated. Otherwise the pair is adjacent in the cyclic ordering of the phases. Rotating all phases together (and shifting lattice lifts when they cross the cut) lets us assume they are linearly adjacent, with an outside phase as \(N\ge3\). The only new possible difference is then \(-1\).

For this \(-1\) state, write the normalized integers of \(i,j\) as 0 and 1 respectively. The other edge constraints force all phases higher than both target phases to have integer 1, and all lower phases to have integer 0. Thus there is exactly one additional vertex, \(w+b_j\), beyond the \(N\)-vertex chain of (1) ordered with \(i\) crossing first. The chain vertices are affinely independent (successive differences are a basis, after omitting the last crossing around the circle). The relation
\[
       (w+b_i)+(w+b_j)=w+(w+b_i+b_j)
\]
fixes the change in the barycentric weights when the additional vertex is given mass \(\xi\). It is precisely the transfer used in §1. If \(g_-,g_+\) are the two cyclic gaps immediately before and after the pair of crossings, the admissible interval is \(0\le\xi\le\min(g_-,g_+)\). Each unit mass transferred increases the target variance by \(2\) and does not change any other edge variance.

Under Haar, anchor one labeled phase at zero by a common rotation. The other \(N-1\) positions are independent uniform modulo 1. Their order is uniform and independent of the \(N\) cyclic gaps, which are uniform on the simplex of positive gaps summing to 1, by the uniform order-statistic density. The chance that the particular pair is cyclically adjacent is \(2/(N-1)\). Conditional on adjacency, the two gaps \(g_-,g_+\) are distinct, and
\[
 \Pr(\min(g_-,g_+)>y)=(1-2y)^{N-1}\quad(0\le y\le1/2).
\]
This follows by subtracting \(y\) from the two selected gaps and rescaling the remaining simplex. Hence the expected minimum is \(1/(2N)\). The maximum average target excess is \(2\cdot(2/(N-1))\cdot(1/(2N))\). It is realized by taking the maximal transfer at every adjacent input, and all intermediate values follow by mixing with (1). A fixed third label can anchor the cut; it makes the selected pair linearly adjacent whenever it is cyclically adjacent. At the null set of ties one may use (1). This makes the construction measurable and equivariant. When \(N=2\) there are no other edges and the only variance can increase without bound. The interval (5) concerns only one coordinate with the others held at their minima; it does not describe the entire global covariance set.

## 4. Root lattices and prime cyclotomic lattices

On \(H=\mathbf1^\perp\subset\mathbb R^N\), let \(P\) be orthogonal projection and write
\[
       A_n=\mathbb Z^N\cap H, \qquad A_n^*=P\mathbb Z^N .
\]
For \(A_n^*\), use \(b_i=P e_i\), with \(p_{ij}=1/N\) in the Euclidean metric. The unique generic pointwise trace minimizer has exact Haar error law \(P Z\). Its covariance is \(I_H/12\), and by the trace lower bound it also minimizes the maximum eigenvalue of Haar covariance. For every unit \(u\in H\), the fourth cumulant of the scalar error along \(u\) is
\[
 \kappa_4(\langle u,PZ\rangle)=-\frac1{120}\sum_{i=1}^N u_i^4.
\]
Indeed the projection disappears against \(u\) and the cumulants of independent scaled uniforms add. Along a sequence of unit directions in increasing dimension, the scalar error converges to \(N(0,1/12)\) **if and only if** \(\max_i |u_i|\to0\). Sufficiency follows from the Lindeberg condition for the bounded summands. For necessity, the normalized scalar sums have uniformly subgaussian tails by the bounded-variable moment bound, so fourth moments converge under distributional convergence, forcing \(\sum u_i^4\to0\). A fixed contrast between two coordinates does not become Gaussian.

For \(A_n\), the coordinate values of an output are integers with sum zero. The pointwise minimum trace is \(\sum_i f_i(1-f_i)\), where \(f_i=\{x_i\}\). The lower bound follows separately from the elementary integer variance inequality. It is possible to meet it simultaneously: \(K=\sum_i f_i\) is an integer. Partition \([0,K)\) into consecutive intervals of lengths \(f_i\), and select the ones intersecting a randomly shifted unit grid \(U+\mathbb Z\), \(U\) uniform on \([0,1)\). Exactly \(K\) intervals are selected, up to endpoints of measure zero, and the probability of selecting interval \(i\) is \(f_i\), because its length is at most one. Rounding those coordinates up and the others down satisfies the sum and unbiasedness constraints. Each fractional coordinate is Haar-uniform modulo one (the corresponding character of \(H/A_n\) is onto). Thus the optimal average trace is \(N/6\); a permutation-symmetrized minimizer has covariance \(N I_H/(6n)\), attaining the minimum possible maximum eigenvalue. Each single ambient-coordinate error of any trace minimizer has density \(1-|r|\) on \([-1,1]\), by averaging its two outcomes over uniform \(f_i\); this does not specify its joint error law.

In the usual all-embeddings convention for the odd-prime field \(K=\mathbb Q(\zeta_p)\), the lattice \(\sigma(\mathcal O_K)\) is isometric to \(\sqrt p\,A_{p-1}^*\): the Gram matrix of the \(p\) powers \(\zeta_p^j\) is \(pI-\mathbf1\mathbf1^T\), with the one relation that their sum is zero. Taking the Euclidean dual gives \(\sigma(\mathcal O_K^\vee)\cong A_{p-1}/\sqrt p\); conjugation preserves the codifferent. The prime ideal \((1-\zeta_p)\mathcal O_K\) corresponds to \(\sqrt p\,A_{p-1}\), since the cyclic neighboring differences generate \(A_{p-1}\). Hence the Haar-optimal maximum covariance eigenvalues for the ring, codifferent, and this ideal in their original canonical scalings are respectively \(p/12\), \(1/[6(p-1)]\), and \(p^2/[6(p-1)]\). For comparison at unit covolume the \(A_n\)-to-\(A_n^*\) ratio is
\[
             \frac{2N}{N-1}\,N^{-2/(N-1)}\longrightarrow 2 .
\]
Here the unscaled covolumes are \(\sqrt N\) and \(1/\sqrt N\), from the Gram determinant \(N\) of the basis \(e_i-e_N\), \(i<N\). None of these formulas is about nearest-point (biased) quantization.

## 5. Prior comparison and limitations

[Pagès–Wilbertz](https://arxiv.org/abs/1010.4642) establish quadratic optimum of intrinsic-stationary rounding by Delaunay cells, with a separate [sharp asymptotic quantization-rate theory](https://arxiv.org/abs/1012.3441). The superbase conorm identity is classical Selling theory; see [Bost–Künnemann, Appendix B](https://webusers.imj-prg.fr/~vincent.maillot/Arakelov/0036/BostKuennemann-07-01-11.pdf). The \(A_n^*\) barycentric kernel's projected-cube density and exact variance are explicitly in [Baek–Adams–Dolson, Propositions 5.4 and 5.6](https://dspace.mit.edu/bitstream/handle/1721.1/105344/10851_2012_Article_379.pdf). Those are precedents, not novelty claims. Here the focus is the exact covariance geometry (especially the globally sharp one-edge interval), the comparison of the two families in the prime-cyclotomic codifferent geometry, and the necessary-and-sufficient Gaussian projection criterion for the averaged error. [Peikert's Gaussian randomized rounding](https://sites.cc.gatech.edu/fac/cpeikert/pubs/pargauss.pdf) concerns a different law and is not derived from (1). Earlier repository Gaussian-retuning notes concern deterministic coordinate rounding and do not address the edge covariance trade-off of unbiased kernels.

The adjacent verification uses rational toy phases and finite integer state enumerations. It reports 308,296 exact checks and 1,035 numerical checks. The Haar assertions are analytic integrations, not simulation conclusions.
