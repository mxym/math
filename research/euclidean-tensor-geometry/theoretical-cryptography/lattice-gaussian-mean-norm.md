# The mean norm of a lattice Gaussian is minimized on the zero coset

The introduction of [Regev and Stephens-Davidowitz, *An Inequality for Gaussians on Lattices*, arXiv v3](https://arxiv.org/pdf/1502.04796) explicitly asks whether the expected Euclidean norm of a discrete Gaussian on \(L+z\) is minimized at \(z=0\). **Yes, strictly unless \(z\in L\).** The key is to apply their Proposition 4.2 to a Laplace transform, rather than applying their covariance inequality to a square root. The same argument proves an anisotropic Bernstein-loss comparison. Even in one dimension, it cannot be strengthened to stochastic order or to all convex losses, and the guaranteed interval of powers anchored at the Euclidean norm ends at power two.

This note is a self-contained deduction from the cited monotonicity theorem, not a claim that the underlying theorem is new or that no one has previously noticed this consequence. The question also appears in [Stephens-Davidowitz's 2017 dissertation, Chapter 3](https://cs.nyu.edu/media/publications/stephens-davidowitz_noah.pdf); the corresponding article is [SIAM Journal on Discrete Mathematics 31 (2017), 749–757](https://doi.org/10.1137/15M1052226). Expectations below measure the norm relative to the center of the *ambient Gaussian*, not after subtracting the actual discrete mean.

## 1. Laplace order answers the mean-norm question

Fix a full-rank Euclidean lattice \(L\), a positive definite real symmetric precision \(P\), and a positive semidefinite real symmetric observable \(H\). Define
\[
 Z_P(z)=\sum_{x\in L+z}e^{-x^TPx},\qquad f_P(z)=Z_P(z)/Z_P(0).
\]
Write \(X_z\) for the probability distribution proportional to these weights on \(L+z\) and \(q(x)=x^THx\). For every \(u>0\),
\[
 \mathbb E e^{-u q(X_z)}
 =\frac{Z_{P+uH}(z)}{Z_P(z)}
 =\frac{Z_{P+uH}(0)}{Z_P(0)}
      \frac{f_{P+uH}(z)}{f_P(z)}
 \ \le\ \mathbb E e^{-u q(X_0)}. \tag{1}
\]
In fact, Proposition 4.2 of the cited paper states that normalized mass \(f\) is nondecreasing in the Gaussian covariance in positive-semidefinite order. The map from our precisions to the paper's covariance parameter is \(P\mapsto\pi P^{-1}\); since \(P+uH\succeq P\), inversion reverses the order. This proves (1) with no commutativity assumption on \(P,H\).

If \(H\succ0\) and \(z\notin L\), the inequality is strict for every \(u>0\). The numerator-normalized ratio \(f_{P+uH}(z)\) is a positive nonincreasing real-analytic function of \(u\) on an open interval containing \([0,\infty)\), by locally normally convergent Gaussian sums. It tends to zero as \(u\to\infty\): every point of \(L+z\) has Euclidean norm at least \(\operatorname{dist}(z,L)>0\), so the numerator is exponentially small in \(u\) times a fixed summable Gaussian mass, whereas the denominator includes the term one. Equality at any \(u>0\) would make the analytic function constant on \([0,u]\), hence everywhere on the connected interval, a contradiction.

For \(0<p<2\) use the positive integral
\[
 q^{p/2}=\frac{p/2}{\Gamma(1-p/2)}
        \int_0^\infty(1-e^{-uq})u^{-1-p/2}\,du .
\]
Integrate (1), using Tonelli on each nonnegative integrand. Thus \(\mathbb E q(X_z)^{p/2}\ge\mathbb E q(X_0)^{p/2}\), strictly for \(H\succ0\) and \(z\notin L\). Taking \(H=I\) and \(p=1\) answers the question. Taking \(p=2\) instead gives the weak inequality directly by \((1-e^{-uq})/u\to q\) and finite second moments. No global strictness for this endpoint is needed here.

More generally the same comparison holds for every Bernstein loss with representation
\[
 \psi(q)=a+bq+\int_{(0,\infty)}(1-e^{-uq})\,\nu(du),
 \quad a,b\ge0,\quad \nu\ge0,\quad
 \int\min(1,u)\,\nu(du)<\infty .
\]
The expectations are finite since such losses grow at most linearly in \(q\). If \(\nu\ne0\), \(H\succ0\), and \(z\notin L\), the comparison is strict by (1). For a singular \(H\) the weak comparison persists; strictness need not hold, e.g. when the lattice and precision are orthogonal direct products and the shift affects only a factor on which \(H=0\).

### A sharp local modulus for fractional moments

Fix \(0<p<2\) and \(H\succ0\). Writing \(z\) near zero on the torus,
\[
 \mathbb E q(X_z)^{p/2}-\mathbb E q(X_0)^{p/2}
   =\frac{(z^THz)^{p/2}}{Z_P(0)}+O_{L,P,H,p}(\|z\|^2).
 \tag{2}
\]
In the numerator isolate the term from the vector \(z\). The sum over nonzero \(\ell\in L\) of \(q(\ell+z)^{p/2}e^{-(\ell+z)^TP(\ell+z)}\) is even in \(z\), and its derivatives through order two converge normally on a sufficiently small ball because it never meets the singularity at zero there. The denominator is likewise smooth and even. Its value at zero is \(Z_P(0)\); its change, and the change of the nonzero-vector contribution, are \(O(\|z\|^2)\). The isolated term contributes the stated leading expression. By (2), strictness away from the zero coset, and compactness of the lattice torus, there are fixed positive constants \(c_1,c_2\) with
\[
 c_1\operatorname{dist}(z,L)^p
 \le \mathbb E q(X_z)^{p/2}-\mathbb E q(X_0)^{p/2}
 \le c_2\operatorname{dist}(z,L)^p
\]
for all \(z\). In particular the mean Euclidean norm has a genuine linear cusp, not a quadratic minimum.

## 2. Why the Bernstein formulation is materially weaker than convex or stochastic order

Use the one-dimensional lattice \(\mathbb Z\), scalar precision \(s^{-2}\), and \(z=1/2\). Define
\[
 H_s(z)=\mathbb E\big[(|X_z|-1/2)_+\big].
\]
The observable is even and convex, yet as \(s\to\infty\),
\[
 H_s(0)-H_s(1/2)=\frac{1}{4\sqrt\pi\,s}+O(s^{-2})>0 .
 \tag{3}
\]
Indeed set \(g_s(y)=y e^{-(y+1/2)^2/s^2}\) for \(y\ge0\). The unnormalized expectation is \(2\sum_{j\ge0}g_s(j+1/2)\) at the zero coset and \(2\sum_{j\ge0}g_s(j)\) at the shifted coset. For either offset \(\delta\), shifted Euler–Maclaurin gives
\[
 \sum_{j\ge0}g_s(j+\delta)
 =\int_0^\infty g_s(y)\,dy-
 B_1(\delta)g_s(0)-\tfrac12 B_2(\delta)g_s'(0)+O(s^{-1}).
\]
The next Bernoulli term vanishes at both offsets, and its remainder is bounded by a constant times \(\int_0^\infty|g_s'''|=O(s^{-1})\), by scaling. Now \(g_s(0)=0,\ g_s'(0)=e^{-1/(4s^2)}\), and \(B_2(0)-B_2(1/2)=1/4\). The unnormalized difference is \(1/4+O(s^{-1})\). The two Gaussian denominators equal \(\sqrt\pi s(1+O(e^{-\pi^2s^2}))\) by Poisson summation; this proves (3). Among the ranges of large \(s\) the stochastic comparison fails more directly: \(|X_{1/2}|\le1/2\) counts two points of near-equal maximum mass, while \(|X_0|\le1/2\) counts only one, and the normalizers are asymptotically equal.

The interval \(0<p\le2\) is also a sharp initial interval of universally guaranteed **powers**. For every fixed \(2<p<4\), using the same two cosets,
\[
 \mathbb E|X_0|^p-\mathbb E|X_{1/2}|^p
  = \frac{4c_p}{\sqrt\pi\,s}
      (1-2^{-p-1})\zeta(p+1)+o_p(s^{-1}),
 \quad
 c_p=-\frac{2\Gamma(p+1)\sin(\pi p/2)}{(2\pi)^{p+1}}>0 .
 \tag{4}
\]
To see this, use the Fourier convention \(\widehat{F}(\xi)=\int F(x)e^{-2\pi i x\xi}\,dx\). For \(F(x)=|x|^p e^{-x^2}\),
\[
 \widehat F(\xi)=c_p|\xi|^{-p-1}+o_p(|\xi|^{-p-1}).
\]
An elementary derivation subtracts \(G(x)=|x|^p(1+|x|)e^{-|x|}\): \(F-G\) is \(O(|x|^{p+2})\) at zero, with the corresponding derivative bounds on either side and exponential decay at infinity. It has an integrable weak derivative of some integer order \(k>p+1\), \(k<p+3\), so its transform is \(O(|\xi|^{-k})\). The two summands in \(G\) have transforms \(2\Gamma(p+j+1)\operatorname{Re}(1+2\pi i\xi)^{-p-j-1}\) for \(j=0,1\), giving the displayed coefficient. Applying Poisson to \(F((n+z)/s)\), the numerator of the \(p\)-th moment is \(s^{p+1}\sum_{k\in\mathbb Z}\widehat F(ks)e^{2\pi ikz}\). The constant coefficient cancels in the difference; opposite cosets retain exactly the odd frequencies, with factor four on positive odd frequencies. The Fourier remainder is summable uniformly after scaling by \(s^{p+1}\) by the displayed decay. Dividing by the Gaussian denominator yields (4), since denominator corrections are exponentially small.

At \(p=4\) ordinary differentiation of the Gaussian Fourier transform gives the same reversal, with exponentially small leading term \(4\pi^4s^8e^{-\pi^2s^2}\). Explicitly, the transformed fourth-power numerator kernel is \(\sqrt\pi e^{-\pi^2\xi^2}(\pi^4\xi^4-3\pi^2\xi^2+3/4)\); the \(3/4\) terms cancel after normalization, and the first frequency gives the asserted leading term. These examples do not classify every individual power above four; they do establish that there is no longer initial interval valid for all lattices and widths.

## Audit

The accompanying script makes 1,080 numerical comparisons on abstract one- and two-dimensional Gaussian laws, including anisotropic Laplace comparisons, fractional powers, the cusp constant, and the asymptotic reversal for a hinge and higher powers. It also checks 25 exact integer-scaled Bernoulli differences. The pointwise mass identity and analytical estimates, not the numerical tests, prove the results. No claim about learning hardness, keys, implementations, or real instances is made.
