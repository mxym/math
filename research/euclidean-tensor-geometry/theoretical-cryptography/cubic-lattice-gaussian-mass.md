# A dimension-free local test for Gaussian mass maximality at the cubic lattice

Let \(G\) be a real positive-definite \(n\times n\) Gram matrix, with \(\det G=1\). Write
\[
\Theta_G(t)=\sum_{z\in\mathbb Z^n}e^{-t z^{\mathsf T}Gz},\qquad
\theta(t)=\sum_{j\in\mathbb Z}e^{-tj^2},\qquad
\mathcal D_G(t)=\log\frac{\theta(t)^n}{\Theta_G(t)}.
\]
The centered unwrapped lattice Gaussian on \(G^{1/2}\mathbb Z^n\) has maximal atom \(1/\Theta_G(t)\), so \(\mathcal D_G(t)\) is the difference between the cubic and the given min-entropies, using natural logarithms.

**Theorem.** There is an absolute \(\delta>0\), independent of \(n\), such that if \(\|G-I\|_F\le\delta\), the following are equivalent:

1. \(\Theta_G(t)\le\theta(t)^n\) for every \(t>0\).
2. The two lattices \(G^{1/2}\mathbb Z^n\) and \(G^{-1/2}\mathbb Z^n\) both have shortest nonzero vector length at least \(1\).
3. \(G_{ii}\ge1\) and \((G^{-1})_{ii}\ge1\) for every \(i\).

When these conditions hold and \(G\ne I\), the inequality in 1 is strict for every \(t>0\). For \(\tau=\max(t,\pi^2/t)\), take \(H=G\) at \(t\ge\pi\) and \(H=G^{-1}\) otherwise, and write \(s=\|H-I\|_F\), \(d_i=H_{ii}-1\) and \(W=\sum_i(1-e^{-\tau d_i})\). Then
\[
\mathcal D_G(t)\asymp e^{-\tau}W,\qquad
\mathcal D_G(t)=2e^{-\tau}W\bigl(1+O(e^{-3\tau/4})\bigr)
\quad(\tau\to\infty).
\tag{1}
\]
All constants are absolute. The exact local quadratic coefficient, with a dimension-free remainder even as the scale changes, is
\[
\mathcal D_G(t)=\xi(\tau)\bigl(\tfrac12-\xi(\tau)\bigr)s^2
+O\bigl(\tau e^{-\tau}(s^3+\tau s^4)\bigr),
\qquad
\xi(u)=u\,\frac{\sum_j j^2e^{-u j^2}}{\theta(u)}.
\tag{2}
\]
At the self-dual scale the coefficient is \(1/16\); at large \(\tau\), formula (1) describes the crossover when \(\tau d_i\) are no longer small. The theorem applies in particular to stable lattices having such a basis. Stability means that the lattice has covolume one and every nonzero sublattice has covolume at least one in its span, which implies the two shortest-vector conditions by dual stability.

## Proof

### Necessity, and reduction to a positive diagonal correction

Poisson summation gives
\[
\Theta_G(t)/\theta(t)^n=\Theta_{G^{-1}}(\pi^2/t)/\theta(\pi^2/t)^n.
\tag{3}
\]
If the shortest squared length of \(G^{1/2}\mathbb Z^n\) is \(a<1\), its mass is at least \(1+2e^{-ta}\), whereas \(\theta(t)^n=1+2ne^{-t}+O_n(e^{-2t})\) as \(t\to\infty\). This eventually contradicts 1. Apply (3) to get the same conclusion for the dual. This direction has no neighborhood assumption. Close to \(I\), both \(G\) and its inverse have minimum eigenvalue strictly larger than \(1/2\), so non-axis integer vectors have squared length \(>1\); checking the coordinate unit vectors suffices. This proves equivalence of 2 and 3 locally.

By (3) it remains to work with \(t\ge\pi\), one Gram matrix \(H=I+D+S\), \(D=\operatorname{diag}(d_i)\), \(d_i\ge0\), and \(S\) symmetric with zero diagonal. We prove the estimates for sufficiently small \(s=\|H-I\|_F\), and then shrink the radius for \(G\) so that the inverse lies in the same range; \(\|G^{-1}-I\|_F\le \|G-I\|_F/(1-\|G-I\|_F)\). The determinant constraint yields
\[
d_\Sigma:=\sum_i d_i=s^2/2+O(s^3),\qquad
d_\Sigma\ge s^2/3,\qquad \sum_i d_i^2\le d_\Sigma^2=O(s^4)
\tag{4}
\]
for \(s\le1/128\). Indeed, expand \(\operatorname{tr}\log H=0\): the \(k\)-th trace of \(H-I\) for \(k\ge3\) has absolute value at most \(s^k\), and the \(k=2\) trace is \(s^2\). For independent \(X_i\) with probabilities proportional to \(e^{-t(1+d_i)j^2}\) on \(\mathbb Z\), put \(Q=X^{\mathsf T}SX\), \(M=\mathbb E e^{-tQ}\). Then
\[
\Theta_H(t)/\theta(t)^n=\prod_i\frac{\theta(t(1+d_i))}{\theta(t)}\,M.
\tag{5}
\]
The next bound controls the interaction term in any dimension:
\[
0\le\log M\le C e^{-7t/4}s^2,\qquad
\log M=\frac{t^2}{2}\mathbb E Q^2+O(e^{-7t/4}s^3).
\tag{6}
\]

### Sparse moment comparison

For \(k\ge1\), symmetry and \(d_i\ge0\) give
\[
\mathbb E X_i^{2k}\le
2\left(\frac{16k}{et}\right)^k
\frac{e^{-7t/8}}{1-e^{-21t/8}}
\le p(t)(16/t)^k(2k-1)!!,\qquad p(t)=3e^{-7t/8}<1.
\tag{7}
\]
The first inequality uses \(\sup_{y\ge0}y^{2k}e^{-t y^2/8}=(16k/(et))^k\) and \(j^2\ge1+3(j-1)\) for \(j\ge1\). For the second, \(k!\ge(k/e)^k\), \((2k-1)!!\ge k!\), and \(2/(1-e^{-21\pi/8})<3\).

Let \(Y_i\) be independent real Gaussians of variance \(16/t\). Suppose \(s>0\), let \(P=|S|/s\), where the absolute value is entrywise, and write \(b_k=\mathbb E(tY^{\mathsf T}PY)^k/k!\). Each \(b_k\ge0\) by the monomial expansion and symmetry. Every surviving monomial in \(Q^k\) has even exponents at all indices and involves at least two indices, since \(S\) has zero diagonal. Hence, for \(k\ge2\),
\[
\frac{|\mathbb E(-tQ)^k|}{k!}\le p(t)^2 b_k s^k;
\quad b_1=\mathbb E Q=0 .
\]
Gaussian integration at \(r_0=1/64\) gives
\(\sum_k b_k r_0^k=\det(I-32r_0P)^{-1/2}\).
Here \(\|P\|_F\le1\); the trace-zero property and \(|\operatorname{tr}P^k|\le1\) for \(k\ge2\) bound the log of this determinant expression in absolute value by \(\frac12\sum_{k\ge2}2^{-k}/k<1/4\). For \(s\le r_0\), \(\sum_{k\ge h} b_k s^k\le2(64s)^h\). The true moment expansion is legitimate since \(\exp(t|Q|)\le\exp(ts\|X\|^2)\) has finite expectation for \(s<1\). Taking \(h=2,3\), using \(M\ge1\) by Jensen, and \(\log(1+u)=u+O(u^2)\) for \(u\ge0\), proves (6). The case \(s=0\) is exact. The comparison uses Frobenius norm and a factor \(p(t)^2\) for the two indices, without counting all sites or directions.

### All scales and the quadratic coefficient

For \(t\ge\pi\), the one-dimensional diagonal loss satisfies, uniformly for \(d\ge0\),
\[
\log\frac{\theta(t)}{\theta(t(1+d))}
= 2e^{-t}(1-e^{-td})(1+O(e^{-t})).
\tag{8}
\]
To see this, the \(j=\pm1\) terms in the numerator difference give \(2e^{-t}(1-e^{-td})\). Use \(1-u^{j^2}\le j^2(1-u)\) for \(u=e^{-td}\) to bound the sum over \(|j|\ge2\) by \(O(e^{-4t}(1-e^{-td}))\). The normalization \(\theta(t)=1+O(e^{-t})\) and logarithm preserve the relative estimate, including zero loss at \(d=0\).

Since \(W\ge 1-e^{-t d_\Sigma}\ge c s^2\) for an absolute \(c>0\), subtracting the error bound in (6) from the sum of (8) proves the second estimate in (1) for all sufficiently large \(t\), with \(\tau=t\); in particular it gives strict positivity for \(s>0\) there. The threshold \(T\ge\pi\) where the relative error is less than \(1/2\) can be chosen independent of \(n\).

For the uniform local expansion, write \(m(t)=\xi(t)/t\). The fixed one-dimensional sums give \(m(t)\asymp e^{-t}\) and \(|m'(t)|=\operatorname{Var}_t(J^2)\le C e^{-t}\) for \(t\ge\pi\), where \(J\) is the discrete Gaussian with precision \(t\). Taylor expansion of the logarithm of the product in (5) is therefore
\[
-tm(t)d_\Sigma+O(t^2e^{-t}\sum_i d_i^2)
=-\tfrac12tm(t)s^2+O(te^{-t}s^3+t^2e^{-t}s^4).
\]
With \(m_i=m(t(1+d_i))\) we have \(|m_i-m(t)|\le Ct e^{-t}d_i\), and independence gives \(\mathbb E Q^2=4\sum_{i<j}S_{ij}^2m_i m_j\). Thus
\[
\frac{t^2}{2}\mathbb E Q^2
=t^2 m(t)^2 s^2+O\bigl((t^2+t^3)e^{-2t}s^4\bigr),
\]
where we used \(\|S\|_F^2=s^2-O(s^4)\), and the difference of the products \(m_i m_j\) from \(m(t)^2\) is bounded by \(Cte^{-2t}d_\Sigma\) for all \(i,j\). These expansions and (6) in (5) prove (2).

The one-dimensional case of Poisson summation gives \(\xi(t)+\xi(\pi^2/t)=1/2\); both summands are positive. In fact \(\xi(t)\le1/4\) for \(t\ge\pi\). Indeed,
\[
\xi'(t)=m(t)-t\operatorname{Var}_t(J^2)
\le m(t)\bigl(1-t+t m(t)\bigr)<0
\quad(t\ge\pi),
\]
since \(J^4\ge J^2\), \(tm(t)<1/2\), and \(\xi(\pi)=1/4\). The leading coefficient in (2) is consequently comparable to \(te^{-t}\) with absolute constants for \(t\ge\pi\). On \([\pi,T]\) we now choose an absolute upper bound on \(s\) so that the remainder is less than half the main term. On this interval \(W\asymp t s^2\) by (4) and \(1-e^{-y}\asymp y\) for bounded \(y\ge0\). This gives the first estimate in (1) all the way down to \(t=\pi\), and proves sufficiency and strictness. At scales below \(\pi\) apply (3). This finishes the proof.

## Why smallness is necessary: an isodual eight-dimensional example

Write \(D_4=\{z\in\mathbb Z^4:\sum z_i\ \text{even}\}\). Its dual is
\(D_4^*=\mathbb Z^4\cup(\mathbb Z+\tfrac12)^4\): pairing with \(e_i\pm e_j\) forces all coordinates to be simultaneously integral or half integral, and every such vector pairs integrally with \(D_4\). These lattices have covolumes \(2,1/2\) and shortest squared lengths \(2,1\), respectively. The lattice \(L=D_4^*\oplus D_4\) is isodual of covolume one and has \(\lambda_1(L)=\lambda_1(L^*)=1\).

For the nome \(e^{-t}\), let \(a=\vartheta_3^4\), \(b=\vartheta_2^4\), \(c=\vartheta_4^4\), with \(\vartheta_3=\theta(t)\) and the standard half-integral and alternating definitions of \(\vartheta_2,\vartheta_4\). The two explicit descriptions above give \(\Theta_{D_4^*}=a+b\) and \(\Theta_{D_4}=(a+c)/2\). Jacobi's identity \(a=b+c\) gives the opposite strict inequality at every scale:
\[
\Theta_L(t)-\theta(t)^8 = bc/2 >0 .
\]
In particular, \(L\) is not stable, because its rank-four sublattice \(D_4^*\oplus0\) has covolume \(1/2\). More strongly, even requiring both shortest lengths to be **strictly** greater than one does not give a global sufficient condition. Set \(\alpha=101/100\) and \(L_\alpha=(\alpha D_4^*)\oplus(\alpha^{-1}D_4)\). This is isodual with minimum \(\min(\alpha,\sqrt2/\alpha)>1\). At \(t=\pi\), Poisson gives \(b=c=a/2\), and \(L\)'s mass ratio there is \(9/8\). For any rank-four lattice \(K\), \(-d\log\Theta_K(t)/d\log t\le2\) by differentiating the Poisson formula and using monotonicity of the dual mass. Rescaling the first factor thus lowers its mass by at most the factor \(\alpha^{-4}\); rescaling the second increases it. Consequently \(\Theta_{L_\alpha}(\pi)/\theta(\pi)^8\ge (9/8)\alpha^{-4}>1\), whereas the strict minimum gap forces the ratio below one for sufficiently large \(t\) and, by duality, sufficiently small \(t\).

## Context and scope

- [Regev and Stephens-Davidowitz, *A Reverse Minkowski Theorem*](https://arxiv.org/abs/1611.05979), Theorem 1.6, proves the cubic upper bound for all stable lattices at extreme scales, in a scale range depending on dimension, and discusses the unrestricted-in-scale question. The local test here works at every scale on one neighborhood with radius independent of dimension, requires only the primal and dual rank-one constraints there, and gives a sharp relative leading term in the tails. It does not settle the global stable-lattice question.
- [Eisenberg, Regev and Stephens-Davidowitz, *A Tight Reverse Minkowski Inequality for the Epstein Zeta Function*](https://arxiv.org/abs/2201.05201), proves an exact global comparison for a family of different test potentials on stable lattices. [Bétermin, *Local Optimality of Cubic Lattices for Interaction Energies*](https://arxiv.org/abs/1611.07798), analyzes unconstrained cubic-lattice Hessians in dimension three; the indefinite Hessian on the full space of determinant-one shapes is compatible with the constrained conclusion here. The positive diagonal restrictions suppress first-order diagonal directions. The expansion in (2) is included to identify the exact local coefficient and to obtain a uniform scale range, not as a claim that cubic-lattice second-variation calculations are new.
- [Kominers, *Majorization and Gaussian-Mass Maximality for Construction-A Lattices from Binary Self-Dual Codes*](https://arxiv.org/abs/2606.03482) and [Shi, Dai and Solé, *Gaussian Mass Inequalities for Lattices*](https://arxiv.org/abs/2611.19749) give global comparisons for other special classes. The Jacobi identities in the counterexample are standard; see [DLMF §20.7](https://dlmf.nist.gov/20.7).

These are statements about centered, unwrapped lattice Gaussian noise and its maximal atom. They neither give a comparison for arbitrary centers nor assert any implication for an implemented cryptographic scheme or a computational hardness assumption. The accompanying deterministic script checks generated Gram matrices and exact truncated theta identities as a replay aid, not as a proof.

Replay: `node verify-cubic-lattice-gaussian-mass.js`. The last run passed 145,633 exact and 4,173 numerical checks. The high-dimensional test uses products of two-dimensional shears, rather than enumerating their lattice points in high dimension.
