# Log-Jacobian universality for narrow random dyadic ring matrices

This note concerns the realized Euclidean volume of an abstract random module map. Weak convergence of the canonical embedding values is not enough for this volume: the logarithm diverges at every singular block. We obtain sufficiently uniform small-ball bounds to remove that singularity even when the discrete coefficient width goes to zero. No claim is made about computational Ring-LWE or about a cryptosystem's parameters.

## 1. Model and theorem

Let \(n\to\infty\) through powers of two, \(R_n=\mathbb Z[\zeta_{2n}]\), and fix positive matrix sizes \(r\le m\), independent of \(n\). For each \(n\), choose a centered real random coefficient \(Z_n\) of variance \(v_n>0\), and assume
\[
 \frac{n v_n}{\log n}\longrightarrow\infty,\qquad
 \frac{\mathbb E|Z_n|^3}{\sqrt n\,v_n^{3/2}}\longrightarrow0,
 \qquad
 |\phi_n(a)|\le
          e^{-c_0 v_n \operatorname{dist}(a,\mathbb Z)^2}
          \quad (a\in\mathbb R),                              \tag{1}
\]
where \(\phi_n(a)=\mathbb E e^{2\pi i a Z_n}\) and \(c_0>0\) is independent of \(n\). The ring-valued model uses integer coefficients. The same theorem for real coefficients refers to the associated real-linear maps of canonical spaces, not to integral lattices.

Independently sample \(n\) coefficients of each entry of an \(r\times m\) matrix \(X\), as coefficients of the powers \(0,\ldots,n-1\) of \(\zeta_{2n}\). For each complex place \(\sigma\) (one from each conjugate pair), write \(X_\sigma\) for its complex \(r\times m\) matrix and \(G_\sigma=X_\sigma/\sqrt{n v_n}\). Put
\[
                    J(X)=\prod_{\sigma}\det(X_\sigma X_\sigma^*).
\]
This equals the square root of the Gram determinant of the corresponding real-linear map to the \(nr\)-dimensional canonical target: each complex singular value occurs twice under realification, and the same canonical \(\sqrt2\) scaling on source and target cancels. One may set \(\log 0=-\infty\); the event of any rank loss tends to zero. With natural logarithms and \(\psi\) the digamma function,
\[
 \boxed{\frac{\log J(X)}{nr}
       -\frac12\log(nv_n)
       \ \xrightarrow{\mathbb P}\ 
          \frac1{2r}\sum_{j=m-r+1}^{m}\psi(j).}                 \tag{2}
\]
In particular, for a single ring entry \(Y\), the left member is
\((1/n)\log|\mathrm N_{K_n/\mathbb Q}(Y)|-\frac12\log(nv_n)\), with limit \(-\gamma/2\). For every fixed \(\beta>1/[2(m-r+1)]\),
\[
                  \Pr\{\min_\sigma s_{\min}(G_\sigma)
                                    \le n^{-\beta}\}\to0 .     \tag{3}
\]
Here \(s_{\min}\) denotes the smallest of the \(r\) row singular values. Equation (3) is a one-sided bound, not a limiting extreme-value distribution.

A discrete Gaussian coefficient of width \(t>0\) has mass proportional to \(e^{-\pi z^2/t^2}\). This includes the centered spherical canonical discrete Gaussian on \(R_n\) of width \(s=t\sqrt n\), since its power basis has canonical Gram \(n I\). For these coefficients (1) follows from \(n v_n/\log n\to\infty\) alone, as shown below. In particular it includes **every fixed** \(s/\sqrt n>0\), and all widths
\[
                        s\ge C \sqrt{n/\log n}\quad
                          \text{for fixed } C>\sqrt\pi .
\]
It also includes sparse signed coefficients \(Z_n=0,+1,-1\) with probabilities \(1-p_n,p_n/2,p_n/2\), for \(p_n\le 1/2\) and \(n p_n\gg\log n\).

## 2. Context and normalization

The [near-square volume note](near-square-gaussian-kernel-volume.md), §3, obtains the same Jacobian expression for Gaussian inputs by coupling **all** coefficients to rounded continuous Gaussians at a sufficiently large canonical width, \(s\ge n^3 m^3\). Its sizes may grow; here they are fixed but the coefficient width may vanish. When \(t\to\infty\), \(v_n\sim t^2/(2\pi)\) by scalar Riemann sums, so (2) gives exactly the previously used normalization \(s/\sqrt{2\pi}\). For the relevance of column-generation and kernel conditions to Gaussian transfer, see [Albrecht–Felderhoff–Lai–Lapiha–Woo](https://perso.jfelderhoff.fr/work/papers/AFLLW25.pdf) and [Düzlü–Gargava–Tairi, fixed 2026-11-12 version](https://opencryptology.org/2026/2180/versions/20261112T135305Z.pdf). We give neither an integral generation criterion nor an upper bound on the kernel smoothing parameter.

For comparison, [Meckes, Theorem 1](https://case.edu/artsci/math/mwmeckes/circulant-final.pdf) proves a weak empirical spectral law for scalar ordinary circulants using joint Fourier-coordinate CLTs. Weak spectral convergence alone does not allow a logarithmic test at zero. [Barrera–Manrique-Mirón, Theorem 1.2](https://arxiv.org/abs/2109.02282) prove a sharper joint extreme-value law for scalar ordinary circulants under their fixed input-law assumptions, and [Cook–Nguyen, Theorem 1.2](https://arxiv.org/abs/2101.07203) prove minimum-modulus universality on the full circle under their coefficient hypothesis. Those are different statements. The point here is a simple common small-ball bound on every **primitive dyadic evaluation point**, sufficient for fixed-size matrix block logarithms and narrowing coefficient laws.

## 3. A uniform dyadic angular estimate

Write \(\|x\|_{\mathbb T}=\operatorname{dist}(x,\mathbb Z)\). There are universal \(c_1,c_2>0\) such that for any real angle \(\omega\), any odd integer \(b\), and \(0\le A\le c_1 n\),
\[
 \frac1n\sum_{j=0}^{n-1}
     \|A\cos(\pi b j/n-\omega)\|_{\mathbb T}^2
                        \ge c_2\min(A^2,1).                 \tag{4}
\]
For \(A\le1/2\) there is no wrap, and the exact answer is \(A^2/2\) for \(n\ge2\). For larger \(A\), the squared integrand is \(\pi\)-periodic in angle, and the odd \(b\) permutes its \(n\) grid positions modulo \(\pi\). The function \(\|z\|_{\mathbb T}^2\) is 1-Lipschitz on the real line; the angular integrand is thus \(A\)-Lipschitz. The difference between the full-period Riemann mean and its integral mean is at most \(\pi A/n\), uniformly in the angular shift.

The integral mean has a uniform positive lower bound for \(A\ge1/2\). On the arc for which \(A\cos\theta\in[-A/2,A/2]\) with \(0\le\theta\le\pi\), the change of variables \(x=A\cos\theta\) has \(|d\theta/dx|\ge1/A\). If \(A\ge1\), the integral of \(\|x\|_{\mathbb T}^2\) over \([-A/2,A/2]\) is at least \(\lfloor A\rfloor/12\ge A/24\), since a whole unit period integrates to \(1/12\). If \(1/2\le A\le1\), use just \([-1/4,1/4]\) where the integral is \(1/96\) and \(1/A\ge1\). Dividing by \(\pi\) gives a common positive constant, and taking \(c_1\) small enough absorbs the Riemann error. This proves (4) without any equidistribution assumption about a generic point of the circle.

For a ring entry \(Y\) at any selected place, test its characteristic function in \(\mathbb R^2\) at \(\xi\). Independence of its coefficients gives a product of scalar characteristic functions with arguments \(A\cos(\pi b j/n-\omega)\), \(A=|\xi|\), for a suitable \(\omega\) and odd \(b\). By (1), (4) this product in absolute value is at most
\[
                    \exp[-c_3 n v_n \min(|\xi|^2,1)]
                    \quad (|\xi|\le c_1 n) .                 \tag{5}
\]
Here and below constants may depend on \(c_0\), and constants for fixed-size matrix statements may depend on \(r,m\).

## 4. Microscopic small balls and row-distance control

Let \(P_\sigma\) be the law of the complex value of one unnormalized entry. The following elementary Fourier majorant works without a density. The product of two functions \((\sin(\pi x)/(\pi x))^2\) (value 1 at zero) is nonnegative, bounded below on \([-1/2,1/2]^2\), and has a bounded Fourier transform supported on \([-1,1]^2\). Apply it to \((Y-y)/(2a)\) and use Fourier inversion of the test function. This gives, for a ball of radius \(a\) about \(y\),
\[
 \Pr(|Y-y|\le a)
    \le C a^2 \int_{|\xi|\le C/a} |\widehat P_\sigma(\xi)|\,d\xi .
\]
All Fourier integrals here have \(2\pi\) convention. For \(a\ge C_4/n\) with \(C_4\) sufficiently large this frequency region lies within (5); integration over \(|\xi|\le1\) and over its complement gives \(C a^2/(n v_n)+C e^{-c_3 n v_n}\). For smaller \(a\), use monotonicity in the radius. Setting \(\kappa_n=(n^3 v_n)^{-1/2}\), we have \(e^{-c_3 n v_n}=o(\kappa_n^2)\) by (1), since \(n v_n\gg\log n\) and also \(n v_n\gg\log(n v_n)\). In standardized coordinates we therefore have, uniformly in the place, center \(z\in\mathbb C\) and radius \(x\ge0\),
\[
       \Pr\{|(G_\sigma)_{ij}-z|\le x\}
                           \le C_5 (x^2+\kappa_n^2).          \tag{6}
\]

Put \(d=m-r+1\). Condition on all rows but one, so the remaining row has independent entries and the orthogonal complement of the span of the other rows contains a complex \(d\)-dimensional subspace. Take a \(d\times m\) matrix \(P\) with orthonormal rows representing projection onto such a subspace (in orthonormal coordinates). Cauchy–Binet shows that some \(d\) columns form a square submatrix \(P_S\) with \(|\det P_S|\ge\binom md^{-1/2}\), because \(\det(PP^*)=1\). Its operator norm is at most one, so \(s_{\min}(P_S)\ge|\det P_S|\). After fixing the complementary \(m-d\) entries of the random row, having distance at most \(x\) to the old span forces the remaining \(d\) entries jointly within a ball of radius \(\binom md^{1/2} x\) about a prescribed vector. In particular each such entry lies in a prescribed disk of that radius. By independence and (6), the conditional probability is bounded by \(C_{r,m}(x^2+\kappa_n^2)^d\).

For a full-row-rank complex matrix \(G\), the \(i\)-th diagonal entry of \((GG^*)^{-1}\) is the inverse squared distance of row \(i\) to the span of the other rows, by the Schur complement. If \(s_{\min}(G)\le x\), its inverse squared value is at most the trace of \((GG^*)^{-1}\), so some row has distance at most \(\sqrt r\,x\). In the rank-deficient case some row already has distance zero. Union over the rows proves
\[
                \Pr\{s_{\min}(G_\sigma)\le x\}
                   \le C_{r,m}(x^2+\kappa_n^2)^d.             \tag{7}
\]
As \(n\kappa_n^{2d}\to0\) under (1), a further union over the \(n/2\) places proves (3) and the all-places event \(s_{\min}(G_\sigma)\ge\kappa_n\) with probability tending to one. No independence across places was used for either conclusion.

## 5. Truncated logarithms, and removing the truncation

The powers at conjugate-pair representatives are orthogonal for real and imaginary parts: for an angle \(\theta_b=\pi b/n\), the sum of \(e^{2ij\theta_b}\) for \(0\le j<n\) is zero, and for two distinct representatives the sums for \(\theta_b\pm\theta_{b'}\) vanish as well. Thus the real coordinate vector for one or two standardized places of each entry has covariance \(\frac12 I\). Every fixed real linear functional is a sum of \(n\) independent centered variables with total third moment bounded by \(C\mathbb E|Z_n|^3/(\sqrt n v_n^{3/2})\), because the summand amplitudes are \(O(n^{-1/2})\) in units of standard deviation. By Lyapunov and Cramér–Wold, one or two places converge jointly to one or two independent standard complex Gaussian matrices, uniform in the selected places: failure of convergence for a bounded continuous test would give a sequence of chosen representatives contradicting the same Lyapunov bound. Independence of distinct entries gives joint convergence of their finitely many coordinate vectors.

For \(L>0\), let \(F_L(G)\) be \(\log\det(GG^*)\) truncated to \([-L,L]\), with value \(-L\) at singularity. It is bounded and continuous. The one-place CLT and the two-place CLT show, respectively, that the expectation of its empirical mean over the \(n/2\) complex places tends to \(\mathbb E F_L(\mathcal G)\), and that its variance tends to zero (the uniformly vanishing covariances suffice). Here \(\mathcal G\) has iid standard complex Gaussian entries with \(\mathbb E|\mathcal G_{ij}|^2=1\).

For the positive tail, \(\log\det(GG^*)\le r\log\|G\|_{\mathrm F}^2\), and \(\mathbb E\|G_\sigma\|_{\mathrm F}^2=rm\); Markov gives an exponentially decaying tail in the log, uniformly in \(\sigma,n\). For the negative tail, on the all-places event from (7), it is bounded by \(2r(-\log s_{\min}(G_\sigma))_+\). Define
\[
 U_\sigma=\min\{\log(1/\kappa_n),(-\log s_{\min}(G_\sigma))_+\},
\]
taking the cap at singularity. For \(0\le z<\log(1/\kappa_n)\), (7) gives \(\Pr(U_\sigma>z)\le C_{r,m} e^{-2d z}\), and the probability is zero above the cap. Thus the expected excess of either truncated tail over \(L\), on the good event, is uniformly \(O_{r,m}(e^{-c L})\), by integration. These estimates also bound the expectation of the positive empirical truncation error plus the negative error on the good event. Markov's inequality and then \(L\to\infty\) remove the truncation in probability without requiring an expectation at singularity.

For \(\mathcal G\), orthogonalizing rows gives independent squared row residuals of laws \(\operatorname{Gamma}(j,1)\), \(j=m,m-1,\ldots,m-r+1\): condition on previous rows, and the projected standard complex Gaussian has that many independent standard complex components. The conditional distribution depends only on the residual dimension, which gives independence of the residual lengths. The mean logarithm of \(\det(\mathcal G\mathcal G^*)\) is therefore \(\sum_j\psi(j)\). Hence the empirical mean of the untruncated logarithm converges in probability to that value. There are \(n/2\) places, and each \(X_\sigma=\sqrt{n v_n} G_\sigma\) contributes \(r\log(n v_n)\) to the log Gram determinant. This accounts for both factors in (2). For \(r=m=1\), the product of the complex Gram determinants equals the absolute field norm, proving the assertion about the norm.

## 6. Gaussian coefficients and the limit of the scope

For \(t\le1\) put \(\lambda=e^{-\pi/t^2}\). Then \(v_t=\operatorname{Var}Z_t\sim 2\lambda\) as \(t\to0\) and is comparable to \(\lambda\) on \(0<t\le1\); the third absolute moment is \(O(\lambda)\), by summing \(\sum_{j\ge1}j^3\lambda^{j^2}\). For \(t\ge1\), comparison of the scalar Gaussian sums with integrals, or grouping integer points in intervals of length \(t\), gives \(v_t\asymp t^2\) and third absolute moment \(O(t^3)\). For a lower bound on \(v_t\), integers between \(t\) and \(2t\) provide \(\Omega(t)\) terms of second moment at least \(t^2 e^{-4\pi}\) for \(t\ge2\); the term at 1 suffices on \(1\le t\le2\). Thus the third-moment condition in (1) is implied by \(n v_t\gg\log n\).

The Jacobi triple product for the scalar characteristic function is
\[
 \phi_t(a)=\prod_{j\ge1}\left[
    1-\frac{4e^{-\pi(2j-1)/t^2}}
            {(1+e^{-\pi(2j-1)/t^2})^2}\sin^2(\pi a)\right].
\]
Its factors are positive and at most one. At \(t\le1\), the first factor alone gives \(\phi_t(a)\le e^{-c\lambda\|a\|_{\mathbb T}^2}\) using \(|\sin(\pi a)|\ge2\|a\|_{\mathbb T}\). At \(t\ge1\), the first \(\lfloor t^2\rfloor\ge t^2/2\) factors have the coefficient of sine squared bounded below by a universal constant, giving \(\phi_t(a)\le e^{-c t^2\|a\|_{\mathbb T}^2}\). This verifies the envelope of (1). In the signed sparse example \(v_n=p_n=\mathbb E|Z_n|^3\), and the nonnegative characteristic function \(1-2p_n\sin^2(\pi a)\) gives the same kind of envelope.

If \(t\to0\) with \(n e^{-\pi/t^2}\) bounded, even the scalar Gaussian ring entry has a probability bounded away from zero of being the zero polynomial, by its product mass at the origin. So the finite log norm cannot converge in probability to the limit above in that regime. Necessity of the extra \(\log n\) in the sufficient condition is not claimed. No conclusion is made for generally indexed cyclotomics (where the angular grid argument changes), for growing \(r,m\), or for a sharp distribution of the extreme singular values. The convergence survives conditioning on any events of probability bounded away from zero by the usual conditional probability bound; a separate generation theorem is needed to know such probability for integral surjectivity.

## Reproduction

Run `python3 verify-dyadic-log-jacobian.py` with Python 3, NumPy, SymPy and mpmath. It checks the exact dyadic angle permutation, orthogonality, and norm identities; numerical finite angular means and the scalar characteristic bound are corroboration, not proofs of the asymptotic estimates.
