# Poisson spectral peaks at logarithmic sparsity on the dyadic odd-root grid

Let \(n\) run through powers of two, \(N=n/2\), and \(\zeta=e^{\pi i/n}\). Take one representative set \(\mathcal A_n\) from the pairs \(\{a,-a\}\) of odd residues modulo \(2n\). Choose exactly \(K\) positions uniformly without replacement from \(\{0,\ldots,n-1\}\), put independent fair signs at those positions, and zero elsewhere. For \(a\in\mathcal A_n\), let \(X_a=\sum_j Z_j\zeta^{aj}\) be its complex evaluation. Assume \(K/\log N\to c\in(0,\infty)\).

Write
\[
 \ell(\lambda)=\log I_0(\lambda),\qquad I_0(\lambda)=\int_0^{2\pi} e^{\lambda\cos u}\frac{du}{2\pi},\qquad
 I(r)=\sup_{\lambda\ge0}(\lambda r-\ell(\lambda)).
\]
At \(r\in(0,1)\) let \(\lambda(r)>0\) solve \(\ell'(\lambda)=r\). This exists uniquely since \(\ell''>0\) and \(\ell'\) rises from 0 to 1, the latter by concentration of the tilted cosine near its maximum. The function \(I\) rises continuously from 0 to \(+\infty\) as \(r\) goes from 0 to 1: \(I'(r)=\lambda(r)>0\), and \(e^{-\lambda}I_0(\lambda)\to0\) gives \(I(1)=\infty\). Define \(r_{n,K}\) by \(K I(r_{n,K})=\log N\), and put
\[
 \lambda_{n,K}=\lambda(r_{n,K}),\qquad
 C(r)=\sqrt{\frac{r}{\lambda(r)\ell''(\lambda(r))}},\qquad
 Y_a=\lambda_{n,K}(|X_a|-K r_{n,K})-\log C(r_{n,K}).
 \tag{1}
\]
Then \(\sum_{a\in\mathcal A_n}\delta_{Y_a}\) converges to the Poisson point process of intensity \(e^{-x}\,dx\) on \(\mathbb R\), including convergence of counts in intervals \((x,\infty)\). In particular \(\max_a Y_a\) tends to the standard Gumbel. Also \(\max_a |X_a|/K\to r_c\) in probability, where \(I(r_c)=1/c\).

For independent signed-Bernoulli coefficients with nonzero probability \(p_n\) and \(\mu_n=np_n\), \(\mu_n/\log N\to c\), let \(K\) denote the realized count. The point process centered using \(K\) as in (1) converges jointly with \((K-\mu_n)/\sqrt{\mu_n}\) to the above Poisson process and an independent standard normal. Using only deterministic centering instead, one has
\[
 \frac{\max_a |X_a|-\mu_n r_{n,\mu_n}}{\sqrt{\mu_n}}
     \ \Longrightarrow\ \frac{\ell(\lambda(r_c))}{\lambda(r_c)}\,\mathcal N(0,1),
 \tag{2}
\]
where the definition of \(r_{n,K}\) permits positive real \(K\) in the deterministic centering. Events \(K=0\) can be assigned arbitrary values in (1), with probability tending to zero.

This is the scalar \(\Theta(\log n)\) support window, not the \(\Theta((\log n)^2)\) moderate-deviation regime of the [earlier matrix theorem](dyadic-spectral-extreme.md). [Davis–Mikosch](https://pure.rug.nl/ws/portalfiles/portal/72126009/euclid.aop.1022677270.pdf) establish ordinary Fourier maximum/point-process limits for fixed iid inputs, and [Barrera–Manrique-Mirón](https://arxiv.org/abs/2109.02282) study extremal singular values of random ordinary circulants. Their polynomial is not the present logarithmically supported triangular array. No growing matrix shape, efficiency, scheme, or hardness conclusion is claimed.

## 1. The radial large-deviation constant for independent circle steps

First replace the \(K\) signed positions by \(K\) iid uniform integers \(U_j\) in \(\mathbb Z/(2n)\), and define all evaluations as \(X_a=\sum_j\zeta^{aU_j}\). Because each \(a\) is odd, adding \(n\) to an index exactly flips the sign. Conditioning on all \(U_j\bmod n\) being distinct gives precisely the ordered without-replacement model. The probability of a collision is at most \(K(K-1)/(2n)\to0\), so for joint process limits it suffices to work in the iid-index model. All rare-event estimates below are made in that model before transferring the final process law.

Let \(S_K\) instead be the sum of \(K\) iid Haar circle points. Uniformly for \(r\) in any compact subinterval of \((0,1)\) and \(y\) bounded,
\[
       \Pr\{|S_K|>Kr+y\}
          = C(r)e^{-K I(r)-\lambda(r)y}(1+o(1)).
 \tag{3}
\]
For large \(K\) the circle sum has a continuous density, so strict and non-strict tails agree. The formula is stable under \(o(1)\) shifts of \(y\).

To prove (3), tilt each circle step by density \(e^{\lambda\cos u-\ell(\lambda)}\) to obtain a two-dimensional step of mean \(r e_1\). Its covariance is diagonal, with entries \(\ell''(\lambda)\) and \(r/\lambda\), by the Hessian of the radial log-mgf \(\ell(\|z\|)\) at \(\lambda e_1\). For the sum of these tilted steps let \(g_{\lambda,K}\) denote its density. Uniformly for \(\lambda\) in the corresponding compact subset of \((0,\infty)\), Fourier inversion gives
\[
  \sup_w K g_{\lambda,K}(w)\le C,\qquad
  K g_{\lambda,K}((Kr+s)e_1)
       \longrightarrow\frac{1}{2\pi\sqrt{\ell''(\lambda) r/\lambda}}
               \quad\text{uniformly for bounded }s .
 \tag{4}
\]
Here are the relevant local density details for the singular one-step distribution. Its characteristic function is the circle integral with integrand a uniformly smooth bounded tilt amplitude times \(e^{i\|t\|\cos(u-\arg t)}\). For \(\|t\|\ge1\), bound the two stationary neighborhoods of radius \(\|t\|^{-1/2}\) by their lengths. On the complementary arcs integrate by parts using the phase derivative \(-\|t\|\sin(u-\arg t)\); the boundary contributions and the integrals of the derivative ratios are \(O(\|t\|^{-1/2})\). More precisely the cutoff sine lower bound is a constant times \(\|t\|^{-1/2}\), its reciprocal derivative is integrable on each arc with endpoint cost \(O(\|t\|^{1/2})\), and the tilt-amplitude derivative contributes at most that much before division by \(\|t\|\). This gives uniform decay. On a compact annulus away from zero the modulus is uniformly below 1, because a nonzero linear functional of a full circle is not constant modulo \(2\pi\) on the support of its positive continuous angular density. Near zero, Taylor expansion with uniformly positive covariance gives the Gaussian quadratic term and a modulus bound \(e^{-c\|t\|^2}\) for centered steps. Invert the \(K\)-th power: on a small ball pass to \(t=u/\sqrt K\) with Gaussian domination, on the compact annulus use exponential decay, and outside a sufficiently large ball integrate a fixed power \(>4\) of the decaying characteristic function and bound the remaining powers by a fixed \(\vartheta<1\). This proves both parts of (4), uniformly as stated.

The untilted density at \((Kr+s)e_1\) is \(e^{-K I(r)-\lambda s}g_{\lambda,K}((Kr+s)e_1)\). It is radial, so integrate this against the circumference \(2\pi(Kr+s)\) over \(s>y\). Apply (4) and dominated convergence (the density is zero beyond radius \(K\) and \(\lambda\) has a positive lower bound for these \(r\)'s). The remaining coefficient is
\(r/(\lambda\sqrt{\ell''(\lambda)r/\lambda})=C(r)\), proving (3). The arc integration is why there is no factor \(K^{-1/2}\) in the radial tail.

## 2. Generic tuples: relative rare-event probabilities by angular binning

Fix a tuple size \(k\), and choose integers \(M=\lfloor(\log N)^2\rfloor\) and \(H=\lfloor(\log N)^{16(k+1)}\rfloor\). Call a tuple of distinct places \(H\)-generic if
\[
          \sum_{j=1}^k m_j a_j\not\equiv0\pmod{2n}
       \quad\text{for nonzero }(m_j)\in[-H,H]^k\cap\mathbb Z^k .
 \tag{5}
\]
Divide each angle circle into \(M\) equal bins. Uniformly for a generic tuple, the law of the bins of \((\zeta^{a_jU})_{j=1}^k\) at one common uniform index \(U\) has probability
\[
                        M^{-k}+O_k(H^{-1/4})
 \tag{6}
\]
in each bin box. To see this, majorize and minorize each bin indicator by smooth periodic cutoff functions taking values in \([0,1]\), differing from it only within distance \(O(H^{-1/4})\) of the endpoints. This is possible with second derivative bounded in \(L^1\) by \(O(H^{1/2})\): use a fixed smooth interpolation scaled to boundary width \(H^{-1/4}\), and the same bound even in \(L^\infty\). Truncate each Fourier expansion to degree \(H\); the omitted sup norm is \(O(H^{-1/2})\) by integrating by parts twice and summing \(\sum_{m>H}m^{-2}\). Products of the truncated functions at the correlated arguments have exactly their product Haar means, by (5) and root orthogonality. Sandwich the true box and account for the cutoff mean error and uniform truncation error. This gives (6), even at discrete bin boundaries by choosing the smooth inequalities pointwise.

The relative error in (6) is \(O_k(M^kH^{-1/4})=o(1/K)\). Across the \(K=\Theta(\log N)\) independent indices, the entire bin-list law therefore has probability ratio \(1+o(1)\) uniformly on all lists compared with independent Haar steps for every place and draw. A phase can be changed to its bin representative with error \(O(1/M)\) in complex distance. Each sum's magnitude changes by at most \(O(K/M)=o(1)\). For every fixed vector \(x_1,\ldots,x_k\), use (3) on both sides of this deterministic threshold error to obtain, uniformly over generic tuples,
\[
        \Pr\{Y_{a_j}>x_j,\ 1\le j\le k\}
                  =(1+o(1))\,N^{-k}\prod_{j=1}^k e^{-x_j}.
 \tag{7}
\]
This is relative control of events of order \(N^{-k}\), not an additive angular approximation at that scale.

## 3. Nongeneric tuples: a uniform additional tilt cost

For a nongeneric tuple, choose an inclusion-maximal \(H\)-generic subtuple of size \(s<k\). A singleton is generic for large \(n\) because its odd exponent is a unit modulo \(2n\), so \(s\ge1\). Adjoining any other \(b\) creates a relation with coefficients bounded by \(H\), with a nonzero coefficient of \(b\). For each fixed base and other coordinate this gives at most \(H(2H+1)^{s+1}\) candidates for that coordinate: choose a coefficient list and solve one linear congruence for \(b\), with at most \(H\) solutions by its nonzero coefficient's gcd with \(2n\). Thus all such tuples with base size \(s\) number at most \(N^s\) times a fixed power of \(\log N\), absorbing the finitely many choices of base positions. In particular the generic tuples are \(N^k(1+o(1))\) of the ordered distinct tuples.

Write \(\lambda=\lambda_{n,K}\) and \(r=r_{n,K}\). At a single uniform index \(U\), tilt by the \(s\) base directions:
\[
            \exp\!\left(\lambda\sum_{j=1}^s
                        \cos(2\pi a_j U/(2n)-\theta_j)\right).
\]
The normalizer is \(I_0(\lambda)^s(1+o(1))\) uniformly in the base and angles, by expanding
\(e^{\lambda\cos u}=\sum_{m\in\mathbb Z} I_{|m|}(\lambda)e^{imu}\) and using (5). The tail of this expansion past \(H/3\) is superpolynomial in \(H^{-1}\), uniformly for \(\lambda\) in a compact subset of \((0,\infty)\); indeed \(I_m(\lambda)\le I_0(\lambda)(\lambda/2)^m/m!\) follows from the positive Bessel series. Under this normalized tilt, the modulus of the expected extra phase \(e^{2\pi i b U/(2n)}\) is at most \(r-\kappa\), for a fixed \(\kappa>0\) and all large \(n\), uniformly in the angle choices. To prove it, after truncating \(|m_j|\le H/3\), there is at most one solution of
\(\sum_j m_j a_j+b=0\bmod2n\): two solutions would give a nonzero relation in (5) for the base. If no solution exists, the expected phase is \(o(1)\). Otherwise the absolute contribution stripped of the normalizer is at most \(\prod_j I_{|m_j|}(\lambda)/I_0(\lambda)+o(1)\).

Since \(2n\) is even and all \(a_j,b\) are odd, at least one \(m_j\) is odd. An odd coefficient of magnitude at least 3 contributes at most \(I_3(\lambda)/I_0(\lambda)<r\). This follows by repeated use of \(I_{m-1}-I_{m+1}=2m I_m/\lambda>0\), from integration by parts on the Bessel integral. If its magnitude is 1, there must be another nonzero index: a single \(\pm1\) would make \(b=\pm a_j\), not a distinct place. That index contributes a factor at most \(\max(I_1,I_2)/I_0<1\) by the same recurrence and \(I_2<I_0\). Since \(I_1/I_0=\ell'(\lambda)=r\), all cases give a fixed gap by compactness of the possible \(\lambda\)'s. Arbitrary directions of the extra phase do not change this absolute bound. This explains why arithmetic dependencies must be treated, but cannot create a cluster of extremes at this scale.

We now bound all-threshold probabilities for a bad tuple by testing only the generic base and a single additional place. If all magnitudes exceed their \(Kr+O(1)\) thresholds, choose directions in a fixed sufficiently fine angular net so that each chosen real projection is at least \(K(r-\varepsilon)-O(1)\). A fixed net suffices for fixed \(\varepsilon>0\). For a given net choice give the base projections tilt \(\lambda\) and the extra projection a small fixed tilt \(u>0\). Its real one-step variable \(W\in[-1,1]\) has mean at most \(r-\kappa\) under the base tilt, hence \(\log\mathbb E_{\rm tilt}e^{uW}\le u(r-\kappa)+C_1u^2\) for small \(u\) by Taylor's theorem. The joint log-mgf is thus at most \(s\ell(\lambda)+o(1)+u(r-\kappa)+C_1u^2\). Chernoff's inequality and independence across the \(K\) draws bound the tail, up to a constant for the finite angular net and bounded threshold offsets, by
\[
 \exp\left(-K\left[s I(r)+u\kappa-C_1u^2-(s\lambda+u)\varepsilon-o(1)\right]\right).
\]
Choose \(u\) small and then \(\varepsilon\) smaller, uniformly for \(1\le s<k\) and the compact \(\lambda\) interval. This gives \(O(N^{-s}e^{-\kappa'K})\) for some \(\kappa'>0\), using \(K I(r)=\log N\). The polylogarithmic overhead in the count of bad tuples is then negligible as \(K/\log N\to c>0\).

## 4. Poisson limits and the random-count Gaussian drift

For any fixed number of disjoint intervals \((x,y]\) or \((x,\infty)\), expand the mixed falling factorial moments of their counts. The sum is over ordered distinct tuples. Generic tuples contribute the product of their interval intensities, by (7) and inclusion-exclusion at the endpoints. Nongeneric tuples contribute \(o(1)\) by §3, using the smallest lower threshold among the intervals. All factorial moments converge to those of independent Poisson counts. These moments imply convergence in law: ordinary moments are finite linear combinations of factorial moments, tightness follows from the first moments, higher moments give uniform integrability along subsequences, and the independent Poisson vector is moment determinate by its exponential moments. This gives the point process in (1) on bounded intervals and all asserted upper-tail counts. For the maximum, the count in \((x,\infty)\) is zero with limiting probability \(\exp(-e^{-x})\). Convergence of compactly supported tests in the point-process statement follows by step-function approximation and local count tightness. The coupling of §1 transfers these final laws to uniform support without replacement.

The proof and the normalized limits hold for every deterministic sequence \(K/\log N\to c\). Therefore they also hold uniformly over the sets \(K/\log N=c+o(1)\) selected by any deterministic shrinking tolerance (otherwise a violating subsequence would give a deterministic countersequence). In the signed-Bernoulli model, conditioned on \(K\) the signs and positions have exactly the original without-replacement law, and \(K/\log N\to c\) in probability. Conditional expected values of bounded continuous tests of the counts or of the centered maximum converge in probability to deterministic Poisson or Gumbel expectations. Multiplying by bounded tests of the normalized binomial count and taking expectations shows the joint limit with independent normal count fluctuations.

Finally consider \(g_n(k)=k r_{n,k}\) for real \(k>0\). Differentiating \(k I(r_{n,k})=\log N\),
\[
            g_n'(k)=r_{n,k}-I(r_{n,k})/\lambda(r_{n,k})
                     =\ell(\lambda(r_{n,k}))/\lambda(r_{n,k}).
\]
This derivative tends to \(\ell(\lambda(r_c))/\lambda(r_c)>0\) uniformly when \(k/\log N=c+o(1)\). Conditional Poisson convergence makes the count-corrected maximum equal to \(g_n(K)+O_{\mathbb P}(1)\). The mean value theorem and the binomial CLT then give (2). This distinguishes a conditional Gumbel from the leading Gaussian drift if one removes only a deterministic center.

The companion verifier checks the finite odd-frequency congruences, generic-box Fourier orthogonality, maximal-base counting conditions, and coefficient identities for the tilted harmonics. The probability limit uses the local density, relative binning, and bad-tuple control above rather than finite simulation.
