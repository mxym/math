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

## Bounded multiplication is too weak

The exact isometry (I) must not be weakened to boundedness of multiplication on \(\mathbb R[P]\). Take independent standard Gaussians \(X,Y\),
\[
 P=X^2+Y^4,\qquad Q=X.
\]
Here \(E_P=\mathbb R^2\) and \(E_Q=\mathbb R e_1\), so the essential subspaces overlap. Nevertheless
\[
 \sup_{p>0}\mathbb E[X^2\mid P=p]<\infty.                 \tag{B}
\]
It follows that \(\|Qf(P)\|_2^2\leq C\|f(P)\|_2^2\) for every polynomial \(f\). Bounded multiplication therefore does not force unlinking.

To verify (B), the conditional density of \(X\), up to its positive normalizing factor, is
\[
 1_{\{|x|<\sqrt p\}}\,
 e^{-x^2/2}(p-x^2)^{-3/4}e^{-\sqrt{p-x^2}/2}.
\]
For \(p\downarrow0\), its second moment is at most \(p\), hence tends to zero. On every compact interval of positive \(p\), substituting \(x=\sqrt p\,s\) makes numerator and denominator continuous positive integrals against the integrable weight \((1-s^2)^{-3/4}\).

For \(p\to\infty\), divide the weight by \(p^{-3/4}e^{-\sqrt p/2}\). For \(x^2\leq p/2\), the remaining factor is
\[
 (1-x^2/p)^{-3/4}
 \exp\{(\sqrt p-\sqrt{p-x^2})/2\}
 \leq 2^{3/4}\exp\{x^2/[2\sqrt p(1+1/\sqrt2)]\}.
\]
It tends pointwise to one and is dominated after multiplication by \(e^{-x^2/2}\), also with the additional second-moment factor. For \(x^2>p/2\), the normalized numerator and denominator tails are bounded by a polynomial in \(p\) times \(e^{-p/4+\sqrt p/2}\), using the endpoint integrability of \((p-x^2)^{-3/4}\). They vanish. Thus the normalized conditional density converges with its second moment to a standard Gaussian density, giving
\(\mathbb E[X^2\mid P=p]\to1\). Together with compact continuity and the zero boundary this proves (B).

The conditional second moment is not constant: it tends to zero at the lower boundary and to one at infinity. Therefore this is not an independent pair or a U-conjecture counterexample. It removes the proposed bounded-operator shortcut while preserving the need to exploit **exact** isometry for all algebra elements.

## Conditional-square and weighted-divergence route

Original independence gives, for every integer \(r\geq1\),
\[
 \mathbb E[Q(X)^{2r}\mid P(X)]
       =\mathbb E Q(X)^{2r}.                            \tag{C}
\]
These exact identities are stronger than the bounded multiplication diagnostic. A possible route is to prove a rigidity theorem for this entire conditional-square family and derive (U). No such general rigidity theorem is asserted here.

For a polynomial vector field \(V\), use the Gaussian weighted divergence
\[
 \delta V=x\cdot V-\operatorname{div}V.
\]
If \(V\cdot\nabla P=0\), Gaussian integration by parts gives
\[
 \mathbb E[\delta V\,f(P)]
   =\mathbb E[V\cdot\nabla(f(P))]=0
\]
for every smooth compactly supported scalar test function \(f\). Thus the weighted divergences of polynomial fields tangent to the fibers of \(P\) form a concrete subspace of the polynomial conditional-mean kernel. This is an exact ordinary identity; surjectivity onto that kernel has not been proved and cannot be assumed.

For example, with \(P=XY\) and \(V=(X,-Y)\), \(\delta V=X^2-Y^2\). Taking \(a=X^2-Y^2\) yields
\[
 \delta(aV)=(X^2-Y^2)^2-2(X^2+Y^2),
\qquad
 \mathbb E[\delta(aV)\mid XY]=0.
\]
This is a nonzero linked signed polynomial with conditional mean zero. Adding a constant cannot turn it into a nonnegative polynomial: along \(X=Y\to\infty\) it tends to negative infinity. Thus the conditional-square positivity in (C) is substantive, not an automatic consequence of an arbitrary mean-zero identity.

A naive equality of the full conditional-mean kernel and the tangent-divergence image is false even for a simple polynomial. Let \(P=X^2\) in one Gaussian coordinate. Then \(\mathbb E[X\mid P]=0\), whereas the only polynomial field tangent to \(P\) is zero, since \(2xV(x)=0\) as a polynomial. Adding independent unused coordinates does not repair that representation: every tangent field has zero \(x\)-component, and its weighted divergence has Gaussian mean zero over the unused coordinates for each fixed \(x\), while the polynomial \(x\) does not. The disconnected two-point fibers supply a kernel contribution absent from the tangent module.

The active analytic gap is therefore a positivity-sensitive, component-sensitive rigidity statement for the full conditional-square family, or an independent proof from the exact multiplication isometry. Neither general Gaussian field "strong independence", an arbitrary tangent-module surjectivity assertion, nor a low-order covariance zero condition may be inserted as an unproved premise.

One requested APPT service review was performed during this attempt, 19:40:22–19:43:57 UTC, and is explicitly excluded from its effective research-time budget. No further numerical campaign was launched for this U stage.

## A diagnostic where the conditional-square identity does close: quadratic poles

For \(P(x)=x^{\mathsf T}Ax+b^{\mathsf T}x+c\), \(A=A^{\mathsf T}\), and an arbitrary polynomial \(Q\), the full unlinking conclusion follows from the necessary identity
\[
 \mathbb E[e^{sP}Q^2]=\mathbb E e^{sP}\,\mathbb E Q^2
\]
for real \(s\) in an interval around zero. This is a bounded-degree **base case only**, recorded to identify which analytic step fails beyond degree two; it is not promoted to the full arbitrary-polynomial theorem, or claimed as historically new.

Diagonalize \(A\). Exponential tilting gives a Gaussian with covariance
\[
 C_s=(I-2sA)^{-1}
\]
and mean \(m_s=sC_sb\). The tilted expectation of \(Q^2\) is rational in \(s\), because polynomial Gaussian moments are polynomials in their means and covariances. Independence makes it a constant on an open interval, so it is the constant rational function.

Suppose \(A\) has a positive eigenvalue and let \(\lambda\) be its largest positive eigenvalue. As \(s\uparrow1/(2\lambda)\), the covariance on its eigenspace is \(T I\), \(T\to\infty\). Covariances on every other eigenspace remain finite positive definite, and their means remain finite. If the polynomial degree of \(Q\) in this eigenspace is \(r\geq1\), conditional orthogonal Hermite decomposition in that Gaussian eigenspace gives a lower bound
\[
 \mathbb E_s Q^2\geq T^r\,r!\,\mathbb E_s\|q_r(Y)\|^2,
\]
with the symmetric-coefficient normalization chosen so that the displayed factor is the standard highest-chaos norm. The nonzero top coefficient polynomial \(q_r\) has positive squared Gaussian norm on the other coordinates, bounded away from zero near the pole. This remains true even if the mean in the divergent eigenspace moves: translating a polynomial leaves its top homogeneous coefficient unchanged. The bound diverges, contradicting the constant tilted moment. Therefore \(Q\) is independent of this entire eigenspace.

Factor the tilted expectation over the eliminated eigenspace. On a smaller interval around zero its positive normalizing factor cancels, leaving the same constant identity for the remaining quadratic statistic. Its polynomial tilted moment is again rational, so one may repeat at its largest positive eigenvalue. If there are negative eigenvalues instead, use the most negative one and approach \(s=1/(2\lambda)<0\) from inside the admissible Gaussian interval. All non-eliminated other covariances are again finite positive at this first pole. Iterating removes every nonzero eigenspace of \(A\).

On \(\ker A\), the remaining statistic is linear, \(b_0^{\mathsf T}x\), where \(b_0\) is the projection of \(b\) onto that kernel. Its Gaussian tilt translates by \(sb_0\). If \(Q\) has positive degree in that direction, its squared Gaussian norm under the translation is a nonconstant polynomial in \(s\) with a positive leading coefficient. Hence the constant identity forces \(Q\) to be independent of \(b_0\) as well. Since
\[
 E_P=\operatorname{range}A+\operatorname{span}\{b_0\},
\]
this proves \(E_P\perp E_Q\) in the diagnostic case.

All steps use only actual independence's necessary tilted-square identity, polynomial Gaussian moments, and positivity near a genuine Gaussian pole. No independence of arbitrary chaos projections or moment-determinacy converse is inserted.

For degree at least three, this argument cannot be applied as written. The tilted measure is no longer Gaussian and its polynomial moments need not be rational in the tilt. Odd or indefinite high-degree polynomials may have no nonzero real exponential-moment interval at all. The missing general analytic replacement of the positive-pole argument remains part of the full target.

## Explicit all-degree contraction target

Write the finite Gaussian-chaos decompositions
\[
 P=\sum_{k=0}^d I_k(p_k),\qquad Q=\sum_{\ell=0}^e I_\ell(q_\ell),
\]
with symmetric real tensors and normalization
\(\mathbb E I_k(p_k)^2=k!\|p_k\|^2\). Orthogonality of distinct derivative chaoses gives
\[
 (K_P)_{ij}
 =\sum_{k\geq1}k\,k!\,
       \langle p_k(e_i,\cdot),p_k(e_j,\cdot)\rangle.
\]
Consequently the **whole** essential-subspace defect in (U) is
\[
 H(P,Q)=\sum_{k,\ell\geq1}
         k\,k!\,\ell\,\ell!\,\|p_k\otimes_1q_\ell\|^2.      \tag{H}
\]
To check the trace identity, expand the norm of
\((p_k\otimes_1q_\ell)(u,v)=\sum_i p_k(e_i,u)q_\ell(e_i,v)\)
and sum over \(u,v\). It is exactly the trace of the two positive coefficient-Gram matrices. All coefficients in (H) are positive.

Vanishing of (H) forces every first contraction to vanish and thus the orthogonality of all coefficient-support subspaces. The earlier elementary essential-space argument then gives the original unlinking conclusion. No chosen degree, dimension, rank, or chaos level is discarded.

The substantive missing implication is from actual ordinary independence of \(P(X),Q(X)\) to (H)=0. Assuming independence of each pair of chaos components would simply assume the desired stronger property. The fixed-class source proves it only through its special nonnegative covariance decomposition, which has been explicitly excluded for general polynomial bases.

The all-polynomial isometry (I) is a necessary consequence of the original law independence, not asserted to be a converse. Even an infinite formal mixed-moment factorization is not automatically a law-independence certificate for high-degree moment-indeterminate marginals. A proof from (I) alone would be a sufficient stronger algebraic bridge; if that bridge cannot be established, the full sigma-field independence must still be available through the exact conditional identities (C) and bounded test functions. This distinction is retained in every potential counterexample or continuation.

## Same-point gradient orthogonality is not the target

The independent-copy contraction in (U)/(H) cannot be replaced by
\(\nabla P(x)\cdot\nabla Q(x)=0\) at the same point. For
\[
 P=X^2-Y^2,\qquad Q=2XY,
\]
the same-point gradient inner product vanishes identically, but
\(K_P=K_Q=4I_2\), so \(H(P,Q)=32\). Direct Gaussian moments give
\[
 \mathbb EP^2=\mathbb EQ^2=4,\qquad
 \mathbb EP^2Q^2=48>16,
\]
hence the variables are dependent. The unsymmetrized first contraction and the global essential spaces are the actual objects; a same-point cancellation of the symmetric gradient polynomial does not certify unlinking or independence.
