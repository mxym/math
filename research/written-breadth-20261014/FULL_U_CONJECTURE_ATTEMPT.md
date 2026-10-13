# Full Gaussian polynomial U-conjecture: active algebraic attempt

14 October 2026, Asia/Shanghai. Internal written-breadth research log.
Status: exploration only; the general conjecture is not proved or refuted here.

## Original complete target and current primary-source boundary

For every finite \(n\geq2\), \(X\sim N(0,I_n)\), and arbitrary real polynomials \(P,Q\), does independence of \(P(X)\) and \(Q(X)\) force the polynomials to depend on orthogonal Gaussian subspaces? Nonconstant pairs are the substantive case; constants have zero essential subspace. Allowing the zero-dimensional subspace in this invariant formulation prevents a vacuous counterexample from an indexing convention that excludes constants.

The full target has no degree bound, convexity, symmetry, single-chaos assumption, or dimension restriction.

Primary-source check on 14 October 2026:

- [Hong–Hu, arXiv:2012.14568v1](https://arxiv.org/html/2012.14568v1), subsequently Chinese Journal of Applied Probability and Statistics 38 (2022), explicitly identifies the full problem as open and proves a symmetric quasi-convex class. The full note was read for its actual assumptions. This old class is not our target or new result.
- [Malicet–Nourdin–Peccati–Poly, arXiv:1503.02154v1](https://arxiv.org/html/1503.02154v1), Theorem1.7/Section1.5, proves unlinking for a specific class of sums of squares of fixed Gaussian-chaos components. Its full stated class and equality connection were read. General polynomial sums are not in that class automatically.
- The recent [Ouimet–Greaves scalar GPC, arXiv:2609.20234v1](https://arxiv.org/html/2609.20234v1) supplies a product moment theorem for Gaussian **linear projections**. It does not by itself solve polynomial unlinking.
- Scoped current searches for the full Gaussian polynomial U/unlinking conjecture did not locate a later complete theorem. This is a literature-status check, not a global absence or priority certificate.

## Exact full-object criterion

For a polynomial \(P\), define
\[
 E_P=\operatorname{span}\{\nabla P(x):x\in\mathbb R^n\},\qquad
 K_P=\mathbb E[\nabla P(X)\nabla P(X)^{\mathsf T}].
\]
Then \(\operatorname{range}K_P=E_P\): a vector belongs to the kernel of the positive semidefinite matrix \(K_P\) exactly when its directional derivative of \(P\) vanishes as a polynomial. Gaussian full support justifies passing from zero expectation of a square to a polynomial identity.

Every directional derivative orthogonal to \(E_P\) vanishes, so \(P\) is a polynomial in the orthogonal projection onto \(E_P\). Thus full unlinking is equivalent to
\[
 E_P\perp E_Q
 \quad\Longleftrightarrow\quad
 H(P,Q):=\operatorname{tr}(K_PK_Q)
 =\mathbb E_{X,Y}\big(\nabla P(X)\cdot\nabla Q(Y)\big)^2=0,  \tag{U}
\]
where \(X,Y\) are independent standard Gaussian copies. Positivity and polynomial full support prove both equivalences. This is an exact criterion for the **whole** target, not a chosen-rank substitute.

Independence implies the polynomial-algebra multiplication map
\[
 \mathbb R[P]\otimes\mathbb R[Q]\longrightarrow L^2(\gamma_n),
 \qquad f(P)\otimes g(Q)\mapsto f(P)g(Q),
\]
is an isometry on simple tensors:
\[
 \mathbb E[f(P)^2g(Q)^2]=\mathbb E f(P)^2\,\mathbb E g(Q)^2. \tag{I}
\]
The active route is to show that such an exact isometry of the two full polynomial subalgebras forces (U), using their finite Gaussian-degree filtration and creation/annihilation operators. No such implication is proved yet. The original independence is retained; a finite list of mixed moment identities is not declared equivalent to independence, especially when high-degree polynomial marginals may be moment-indeterminate.

## Two exact obstacles: no universal sign shortcut

A square-covariance inequality for arbitrary polynomials is false. For standard one-dimensional \(Z\), put \(P=Z\), \(Q=1-Z^2/10\). Then
\[
 \operatorname{Cov}(P^2,Q^2)
 =-\frac15\operatorname{Var}(Z^2)
      +\frac1{100}\operatorname{Cov}(Z^2,Z^4)
 =-\frac7{25}<0.
\]
The fixed-chaos positive theorem cannot be silently applied to general polynomial mixtures.

Even eventual positivity of high even powers is false for linked homogeneous polynomials. Let \(X,Y\) be independent standard Gaussians and set
\[
 P(X,Y)=X^2-\tfrac1{10}Y^2,\qquad
 Q(X,Y)=Y^2-\tfrac1{10}X^2.
\]
On the unit circle their individual supremum norms are one. With \(s=x^2\in[0,1]\),
\[
 PQ=\frac{121}{100}s(1-s)-\frac1{10};
 \qquad \|PQ\|_\infty=\frac{81}{400}.
\]
Indeed the positive maximum at \(s=1/2\) is \(81/400\), while the endpoint absolute value is \(1/10\).

Write the Gaussian vector as \(R\Theta\), with independent uniform direction and chi radius in dimension two. Homogeneity, the \(L^p\)-to-supremum limit on the circle, and Stirling's formula give exactly
\[
 \lim_{k\to\infty}
 \left(\frac{\mathbb E[P^{2k}Q^{2k}]}
             {\mathbb E P^{2k}\,\mathbb E Q^{2k}}\right)^{1/k}
 =16\left(\frac{81}{400}\right)^2
 =\frac{6561}{10000}<1.                                  \tag{O}
\]
The radial factor is \(\Gamma(4k+1)/\Gamma(2k+1)^2\), whose \(k\)-th root tends to sixteen. The angular factors give the displayed supremum norms. Thus the ratio tends to zero exponentially. These polynomials are linked and dependent; (O) is an obstruction to a proposed proof shortcut, not an independent-polynomial counterexample or a new priority claim.

The algebraic route must use all exact identities (I), without assuming one universal covariance sign or inferring unlinking solely from leading homogeneous moments. Convex/quasi-convex, one-chaos, bounded-degree or bounded-dimension cases will not be counted as a solution of the full target.

No new Lean module/audit, root or Gaussian-tree modification, push, publication, or submission is part of this attempt.

## Exact finite obstruction even for pure second-chaos bases

The asymptotic sign obstruction persists after centering the two quadratic bases, so it cannot be repaired by merely putting each base variable in one Gaussian chaos. Let
\[
 F=H_2(X)-\tfrac1{10}H_2(Y),\qquad
 G=H_2(Y)-\tfrac1{10}H_2(X),\qquad H_2(z)=z^2-1.
\]
Both \(F,G\) are centered, nonzero elements of the second Wiener chaos. Direct expansion using \(\mathbb E Z^{2r}=(2r-1)!!\) gives
\[
 \mathbb EF^4=\mathbb EG^4=\frac{30123}{500},\qquad
 \mathbb EF^4G^4=\frac{2778705693}{1250000},
\]
\[
 \mathbb EF^4G^4-\mathbb EF^4\,\mathbb EG^4
 =-\frac{109891872}{78125}<0.                            \tag{O2}
\]
The finite rational arithmetic was independently checked by symbolic Gaussian monomial expansion. The analytic expansion, not a floating search, verifies (O2).

There is no conflict with the known chaotic-square theorem: it compares \(F^2G^2\), while \(F^2\) and \(G^2\) themselves contain multiple chaoses when treated as bases for fourth powers. The variables \(F,G\) are not jointly Gaussian linear projections, and they are not PSD quadratic forms. No published full conjecture or new priority is attributed to the stronger false statement eliminated by (O2).

## Why a naive finite-degree projection step fails

Conditional expectation onto a polynomial-generated sigma field need not preserve polynomial degree or even polynomial form. For standard Gaussian \(Z\), let \(A=Z^2+Z\). Given \(A=a>-1/4\), its two roots are \(-1/2\pm u\), \(u=\sqrt{a+1/4}\). Their conditional weights are proportional to \(e^{u/2}\) and \(e^{-u/2}\), since both Jacobian magnitudes are \(2u\). Therefore
\[
 \mathbb E[Z\mid A=a]=-\frac12+u\tanh(u/2).
\]
This is not a polynomial in \(a\). Taking any independent Gaussian-coordinate polynomial for the second variable gives an already unlinked example, so the nonpolynomial projection occurs even in valid independent cases. A proof using the isometry (I) may use the ambient polynomial-degree filtration, but cannot assume that conditional projections onto the two subalgebras preserve that filtration.

## Strong independence is not an automatic input

The entire Section3.6 proof of the 2015 fixed-class unlinking theorem was subsequently read. Its decisive step is a sum of nonnegative pairwise chaotic-square covariances, followed by the Üstünel–Zakai first-contraction criterion. General mixed-chaos polynomial bases lack that sum-of-squares form.

The literature also distinguishes ordinary from strong independence on Wiener space. An existing counterexample in Tudor's asymptotic Cramér work uses a stochastic sign integral with infinitely many Gaussian-chaos components. It is not a finite polynomial pair and cannot be relabelled as a counterexample to the original U-conjecture.
