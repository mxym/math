# Global log-volume fluctuations and the Poisson hard edge of dyadic random module matrices

At fixed rectangular matrix shape, the sum of the logarithmic Gram determinants over the dyadic canonical places has a Gaussian limit. Its variance is not the independent complex Gaussian variance: the standardized fourth cumulant of a single real coefficient contributes exactly \(r/(2m)\) times that cumulant, in the per-place normalization below. The Gaussian bulk fluctuation and the Poisson process of least singular values are asymptotically independent.

This is abstract Euclidean matrix probability, not a lattice-solving algorithm, an assessment of any cryptosystem, or a hardness implication. The earlier [log-Jacobian note](dyadic-log-jacobian.md) gives a law of large numbers and the [hard-edge note](dyadic-hard-edge.md) gives the marginal point process. For ordinary scalar periodograms, [Faÿ and Soulier (2001)](https://www.sciencedirect.com/science/article/pii/S0304414900000776) already proved nonlinear-statistic CLTs by triangular-array Edgeworth expansion, with a fourth-cumulant correction. Their scalar logarithmic-domain use is also explicit in [Faÿ and Philippe (2002), §4.1](https://www.numdam.org/article/PS_2002__6__239_0.pdf). We do not claim that scalar phenomenon or the Edgeworth approach as new. The scope here is the odd-root canonical grid, fixed rectangular log-Gram determinants, lattice-valued triangular arrays, and joint asymptotic independence from the hard edge. [Barrera and Manrique-Mirón (2022), Theorem 1.2](https://arxiv.org/pdf/2109.02282) concern the joint *minimum and maximum* for ordinary scalar circulants, rather than a bulk log-volume statistic.

## 1. Model and result

Let \(n\to\infty\) through powers of two, \(N=n/2\), and take a set \(\mathcal A_n\) of odd residues modulo \(2n\) with exactly one member from each pair \(\{a,-a\}\). Fix \(1\le r\le m\). For each matrix entry \(e\) in an \(r\)-by-\(m\) array and each \(0\le b<n\), let \(Z_{n,e,b}\) be independent copies of a symmetric real law \(Z_n\), with variance \(v_n>0\). Put
\[
   G_{a,e}=\frac{\sum_{b=0}^{n-1}Z_{n,e,b}e^{\pi iab/n}}{\sqrt{nv_n}},
      \qquad a\in\mathcal A_n .
\]
Assume \(\max(v_n,v_n^{-1})=n^{o(1)}\), that every fixed moment of \(|Z_n|/\sqrt{v_n}\) is at most \(n^{o(1)}\), and that, for fixed positive \(c,C,h_0,\lambda\),
\[
 |\mathbb E e^{2\pi iuZ_n}|\le e^{-cv_n\operatorname{dist}(\lambda u,\mathbb Z)^2}
       \quad(u\in\mathbb R),\qquad
 \log\mathbb E e^{uZ_n}\le Cv_n u^2\quad(|u|\le h_0).
 \tag{1}
\]
Examples are fixed symmetric nondegenerate integer laws with a finite exponential moment, and the \(\{0,\pm1\}\) law with nonzero probability \(p_n\le1/2\) and \(1/p_n=n^{o(1)}\). The characteristic and mgf bounds for these inputs are checked in the preceding hard-edge note, §6; moment bounds for the sparse example are exactly \(p_n^{1-j/2}\) at order \(j\).

Let \(f(G)=\log\det(GG^*)\). Define \(L_n=\sum_a f(G_a)\) when all matrices have full row rank, and assign an arbitrary finite value on the complementary event. Let
\[
 \mu=\sum_{i=1}^r\psi(m-i+1),\quad
 \sigma^2=\sum_{i=1}^r\psi_1(m-i+1),\quad
 \chi_n=\mathbb E Z_n^4/v_n^2-3,\quad
 V_n=\sigma^2+\frac{\chi_n r}{2m},
\]
where \(\psi, \psi_1\) are the digamma and trigamma. Set \(d=m-r+1\) and \(C_{r,m}=\Gamma(m+1)/[(r-1)!\Gamma(d+1)^2]\). Then
\[
 \left(\frac{L_n-N\mu}{\sqrt{NV_n}},
     \ \sum_{a\in\mathcal A_n}\delta_{\,C_{r,m}N s_{\min}(G_a)^{2d}}\right)
   \ \Longrightarrow\ (\mathcal N(0,1),\ \operatorname{PPP}(dx)),
 \tag{2}
\]
with independent components, in the usual vague topology on locally finite point measures on \([0,\infty)\). In particular no convergence of \(\chi_n\) is needed. Jensen gives \(\chi_n\ge-2\), and \(\psi_1(j)=\sum_{\ell\ge0}(j+\ell)^{-2}>1/j\) by integration, so \(V_n\ge\sigma^2-r/m>0\) uniformly. For \(r=m=1\) the correction is \(\chi_n/2\); symmetric signs give variance \(\pi^2/6-1\), rather than \(\pi^2/6\). Shape growth, nonsymmetric coefficients, and polynomially sparse coefficients are not covered.

## 2. Uniform polynomial-accuracy local expansion

Use real coordinates in \(\mathbb C^{r\times m}\) and real dot products. For every place use an independent random vector \(U_a\) with a smooth radial probability density supported in the ball of radius
\[
                  \epsilon_n=n^{-1/2}\exp[-\sqrt{\log n}].
\]
It is a dilation of one fixed compactly supported density. Use \(Y_a=G_a+U_a\). Let \(g\) be the density of a single matrix of independent standard complex normal entries (real-coordinate variance \(1/2\)), and \(g_\epsilon=g*\operatorname{law}(U_a)\).

Fix any number \(s\) of distinct places \(a_1,\ldots,a_s\), and any expansion order \(M\). Uniformly over their choice, the density of \((Y_{a_1},\ldots,Y_{a_s})\) is the inverse Fourier transform of
\[
  \Big(\prod_{i=1}^s\widehat{g_\epsilon}(t_i)\Big)
  \left[\sum_{\substack{\mathbf j=(j_4,j_6,\ldots)\\
                 \sum_h j_h(h/2-1)\le M}}\prod_h\frac{P_h(t)^{j_h}}{j_h!}\right]
 \tag{3}
\]
up to a uniform absolute error \(O(n^{-M-1+o(1)})\), where \(h\) runs through even integers \(h\ge4\) and, in the convention \(\widehat{P}(t)=\int e^{2\pi i\langle t,x\rangle}dP(x)\),
\[
 P_h(t)=\frac{\kappa_{h,n}}{h!\,n^{h/2}}
     \sum_{e,b}\left(2\pi i\sum_{i=1}^s \langle t_{i,e},u_{a_i,b}\rangle\right)^h,\qquad
 u_{a,b}=(\cos(\pi ab/n),\sin(\pi ab/n)).
 \tag{4}
\]
Here \(\kappa_{h,n}\) is the \(h\)-th cumulant of \(Z_n/\sqrt{v_n}\); every fixed cumulant is \(n^{o(1)}\) in absolute value. The bracket includes the constant term.

For completeness, covariance is exactly \(I/2\) by averaging each pair of odd-root modes over \(b<n\); products of two modes are \(n\)-periodic and average to zero except opposite frequencies. For \(\|t\|\) up to a fixed small multiple of \(\sqrt{nv_n}\), (1) then gives \(e^{-c_s\|t\|^2}\) as a modulus bound. From there through \(T_n=\sqrt{nv_n}\,n^{\tau_s}\), the uniform angular lemma of [the hard-edge note, §2](dyadic-hard-edge.md) gives modulus at most \(e^{-n^{c_s'}}\) for some \(c_s'>0\) after decreasing the fixed \(\tau_s>0\) if necessary. It applies to the entry with largest real-dual norm. Beyond \(T_n\) use the product mollifier: its Fourier absolute value is at most \(C_D(1+\epsilon_n\|t\|)^{-D}\) for every fixed \(D\), since some place has norm at least \(\|t\|/\sqrt{s}\). As \(\epsilon_nT_n=n^{\tau_s-o(1)}\), its integral over that region is \(O(n^{-B})\) for any prescribed \(B\) by choosing \(D\) large.

On \(\|t\|\le n^\eta\), with a small fixed \(\eta>0\) chosen for \(M,s,r,m\), expand the log characteristic through order \(2M+2\). The moment hypothesis bounds its remainder, after summation over the \(O(n)\) independent real coefficients, by \(n^{-M-1+o(1)}(1+\|t\|)^{2M+4}\). One elementary justification is to use Taylor's theorem for \(e^{ix}\) through order \(2M+3\) with error bounded by \(\mathbb E|x|^{2M+4}/(2M+4)!\), and then expand the real positive log by a finite geometric Taylor series around one. The arguments at each coefficient are \(O_s(n^{-1/2}\|t\|)\), the characteristic function is real even, and the order-two term is exact. The log Taylor series remainder has the same bound by lowering \(\eta\) to ensure all per-coefficient deviations are small; the error from each fixed moment is subpolynomial. Each \(P_h\) has absolute value at most \(n^{-(h/2-1)+o(1)}C_h\|t\|^h\). For such \(\eta\), the sum of their absolute values, and also the log remainder, are \(o(1)\) uniformly on this ball. Taylor expanding the exponential through ordinary product degree \(M\) and dropping terms of total weight \(>M\) leaves an error dominated by \(n^{-M-1+o(1)}\) times a fixed polynomial in \(\|t\|\) times \(e^{-\pi^2\|t\|^2}\). For the exponential Taylor remainder use the sum bound and at least \(M+1\) factors; every factor has weight at least 1. The integral from \(n^\eta\) to the small multiple of \(\sqrt{nv_n}\) is superpolynomially small by the Gaussian modulus bound, as is the tail of the finitely many reference Gaussian polynomials. Fourier inversion gives (3).

Inverting the monomials gives products of derivatives of \(g_\epsilon\), one factor at each place. The derivative order at each place is its number of occurrences in the monomial (counted with multiplicity). An \(h\)-factor costs \(n^{-(h/2-1)+o(1)}\), because its coefficient sum in \(b\) has at most \(n\) terms. To track which terms survive, expand every real directional expression into the two complex exponentials with signs \(\pm1\) and complex linear coefficient forms. A coefficient sum in \(b\) is exactly \(n\) if the signed sum of its odd exponents vanishes modulo \(2n\), and zero otherwise. The signed sum is even, since \(h\) is even, so the average is precisely a finite geometric progression with ratio an \(n\)-th root. A signed relation with any nonzero place coefficient removes one free place choice: holding all other residues fixed, the congruence for that variable has at most \(h\) solutions modulo \(2n\). Thus for an \(s\)-tuple of slots, the total assignments satisfying any one specified nontrivial relation are \(O_h(n^{s-1})\). This allows resonances without assuming that all tuples are generic.

## 3. Truncation and removing the auxiliary noise

The Gaussian Gram–Schmidt product expresses \(\det(GG^*)\), for \(G\) of density \(g\), as a product of independent Gamma variables of shapes \(m,m-1,\ldots,m-r+1\), all unit scale. Indeed each row is isotropic and independent of the previous ones, so its squared residual length has the designated Gamma law independent of those rows by conditional rotation. Thus \(f\) has all absolute log moments, Gaussian mean \(\mu\), and variance \(\sigma^2\).

Choose a fixed \(A>6r\) and let \(f_{\rm clip}(x)=\max(-A\log n,\min(A\log n,f(x)))\), with the natural value at singular matrices. Write \(H_n=\log n\) and
\[
      F_n(x)=(f_{\rm clip}(x)-c_n)\mathbf 1_{\{\|x\|_F\le H_n\}},
 \qquad
      c_n=\frac{\int_{\|x\|_F\le H_n} f_{\rm clip}(x)g_\epsilon(x)\,dx}
                        {\int_{\|x\|_F\le H_n}g_\epsilon(x)\,dx}.
 \tag{5}
\]
Here \(F_n\) is exactly centered under \(g_\epsilon\). It is bounded by \(O(\log n)\) and invariant under a common complex phase rotation, row/column permutations, and sign. Under \(g\), clipping changes the mean by \(o(n^{-1/2})\): the negative clipping threshold requires \(s_{\min}\le n^{-A/(2r)}\), whose Gaussian probability is \(O(n^{-Ad/r})\) by the fixed-shape Gaussian hard-edge bound; then use the second log moment and Cauchy–Schwarz. Positive clipping implies \(\|G\|_F\ge n^{A/(2r)}\). A cutoff at \(H_n\) also gives errors smaller than any power of \(n^{-1}\). Replacing \(g\) by \(g_\epsilon\) on a bounded log-size test changes its integral by \(O(\epsilon_n\log n)=o(n^{-1/2})\), since a Gaussian has integrable first derivatives. Therefore \(c_n=\mu+o(n^{-1/2})\). The same bounds at higher powers, and \(L^1\) convergence of each derivative of \(g_\epsilon\) to that of \(g\) with error \(O(\epsilon_n)\), justify the limits
\[
 s_n^2:=\int F_n^2 g_\epsilon\longrightarrow\sigma^2,\qquad
 c_{e,n}:=\frac12\int F_n\partial_{\Re e}^2 g_\epsilon
             \longrightarrow \operatorname{Cov}_g(f(G),|G_e|^2).
 \tag{6}
\]
Here \(f\) times Gaussian derivative is integrable by Cauchy–Schwarz and the Gaussian log moments. Use common phase invariance to see that the same \(c_{e,n}\) is obtained using any real unit direction in the complex \(e\)-plane. Row/column permutations show that all limiting covariances in (6) are equal. Under density \((\pi w)^{-rm}\exp(-\|x\|_F^2/w)\), the expectation of \(f\) is \(\mu+r\log w\). Differentiating its density at \(w=1\) yields \(\sum_e\operatorname{Cov}_g(f,|G_e|^2)=r\) (integrable by the preceding log moments and the scale change, or Gaussian derivative domination near \(w=1\)). Thus the covariance per entry is \(1/m\), and \(\sum_e c_{e,n}^2\to r/m\). For (6) explicitly, \(\partial_{\Re e}^2 g/g=4(\Re G_e)^2-2\); phase rotation makes the contribution of \(2(\Re G_e)^2\) equal to that of \(|G_e|^2\).

It remains to show that this local smoothing is small enough for the sum of singular logarithms. The subgaussian local mgf in (1) and Chernoff's bound give \(\Pr(\|G_a\|_F>H_n-1)=O(n^{-B})\), for every fixed \(B\), uniformly in \(a\): use each real coordinate, tune the mgf parameter of its normalized sum to \(O(\log n)\) and note that the per-coefficient parameter remains below \(h_0\). The expansion (3) implies a uniform upper bound on the density of \(Y_a\). The tube \(\{\|Y_a\|_F\le H_n+1,\ s_{\min}(Y_a)\le x\}\) has Lebesgue volume \(O((1+H_n)^{C_0}x^{2d})\). To see it, take a unit vector in the left near-kernel and a coefficient of magnitude at least \(1/\sqrt r\); the corresponding row has distance at most \(\sqrt r x\) to the span of the other rows, whose complex codimension is at least \(d\). Integrate row-wise over the Frobenius ball and sum over the \(r\) choices. This proves
\[
 \Pr(s_{\min}(G_a)\le x)\le C_1(1+H_n)^{C_0}(x+\epsilon_n)^{2d}+O(n^{-B}),
                \quad 0\le x\le1 ,
 \tag{7}
\]
by perturbation of singular values; constants may depend on fixed shape. In particular a union bound at \(x=n^{-2}\), or at \(x=n^{-A/(2r)}\), shows that all \(G_a\) have full rank and remain above the clipping threshold with probability tending to one. For \(s_{\min}(G_a)>2\epsilon_n\), logarithms of the positive singular values vary by at most a constant times \(\epsilon_n/s_{\min}(G_a)\). Clipping does not increase that difference. The expectation of \(1/s_{\min}\) restricted to \(s_{\min}>2\epsilon_n\) is \(O((1+H_n)^{C_0})\) by integrating (7) (take \(B\) large). On the remaining event the clipped difference is \(O(\log n)\), while (7) bounds its probability by \(O((1+H_n)^{C_0}\epsilon_n^{2d}+n^{-B})\). Crossing the norm cutoff has superpolynomially small probability. Thus
\[
  \frac{\sum_a F_n(Y_a)-(L_n-N\mu)}{\sqrt{NV_n}}\ \xrightarrow{\mathbb P}\ 0,
 \tag{8}
\]
by \(V_n\ge c>0\), \(\sqrt n\epsilon_n(1+\log n)^C\to0\) for every fixed \(C\), the mean estimate in (5), and the high-probability untruncation.

## 4. A marked Wick expansion

Let \(I_1,\ldots,I_b\) be disjoint bounded intervals of \([0,\infty)\) of positive lengths. For \(Y_a\) mark it as type \(\ell\) if \(\|Y_a\|_F\le H_n\) and \(C_{r,m}N s_{\min}(Y_a)^{2d}\in I_\ell\). Denote the counts by \(Q_{n,\ell}\), and put \(S_n=\sum_a F_n(Y_a)/\sqrt{NV_n}\). For a standard Gaussian matrix, [the hard-edge calculation, §4](dyadic-hard-edge.md), gives probability \((|I_\ell|+o(1))/N\) for this marker, also under \(g_\epsilon\): singular-value perturbation by \(\epsilon_n=o(N^{-1/(2d)})\) only changes the scaled endpoints by \(o(1)\), and Gaussian norm tails are negligible. The marker's support volume is \(O((1+\log n)^{C_0}/n)\) by the same row tube. This volume bound applies even for derivatives of \(g_\epsilon\), which are uniformly bounded at every fixed order.

For any fixed \(k\ge0\) and \(t_1,\ldots,t_b\ge0\), expand \(S_n^k\prod_\ell (Q_{n,\ell})_{t_\ell}\), with \((x)_t=x(x-1)\cdots(x-t+1)\). There are \(t=\sum_\ell t_\ell\) marked place slots; their places are distinct (within each falling factorial by definition, and between types because the markers are disjoint). Write \(u\) for the number of the \(k\) statistic slots assigned to marked places. Among unmarked places let \(j\) be the number appearing only once in the statistic, and let \(s\) count all their distinct places. Then \(s\le(k-u+j)/2\). For each fixed grouping apply (3) at its \(s+t\) distinct places; the integrand vanishes outside the corresponding norm balls by (5) and the markers. Choosing expansion order \(M>k+t+2\) makes the summed remainder \(o(1)\): all volumes and values contribute at most powers of \(\log n\) aside from the displayed \(n\) factors, and \(V_n\) is bounded below.

A singleton unmarked place must receive at least two derivatives. Zero derivatives vanish by the exact centering in (5), one derivative by the evenness of both test and reference. For a density monomial of weight \(w=\sum_h j_h(h/2-1)\), the total derivative order is \(D'=\sum_h j_h h\), and \(w\ge D'/4\ge j/2\). There are at most \(O(n^{s+t})\) assignments, marked volumes contribute \(n^{-t}\) up to logarithms, and coefficients contribute at most \(n^{-w+o(1)}\). After normalization each such term is \(O(n^{s-k/2-w+o(1)})\), and
\[
                 s-k/2-w\le -u/2 .
 \tag{9}
\]
Any strict inequality with respect to zero yields \(o(1)\), because only finitely many groupings and monomial patterns are present for fixed moments. Equality requires: no statistic slot on any marked place; every repeated unmarked place has multiplicity exactly two; all derivative factors have degree exactly four; every singleton unmarked place has exactly two derivatives and no other place receives any. In particular the marked places now contribute only their unperturbed reference probabilities.

By the congruence count in §2, terms with some nontrivial signed modular relation among their places lose a further factor \(O(1/n)\), so they contribute \(o(1)\) even in the equality case. In a quartic factor with all signed coefficients formally balanced, each place occurs an even number of times. The equality conditions force two different singleton places with two occurrences each. Quartic factors therefore pair all the singleton places; repeated pairs use the ordinary local second moment. Equivalently a pairing of the \(k\) labeled statistic slots is colored by whether each pair shares one place or uses two different places (joined by a quartic cumulant). No leading pairing exists for odd \(k\).

A same-place pair contributes \(s_n^2\). For two specified different places and a single common matrix entry \(e\), the \(2+2\) quartic binomial term has coefficient \(\binom42\chi_n/(4!n^2)\) times the sum of \(n\) direction-derivative products. Each integrated second direction derivative is \(2c_{e,n}\) by phase invariance, so the resulting contribution is exactly \(\chi_n c_{e,n}^2/n\). Here the derivative sign is positive at total order four in the Fourier convention in (3). To use this full \(2+2\) expression, one may add back its nontrivial signed-resonant terms; by §2 and (9) they change the final moment by \(o(1)\). Disjoint cross-place factors enter exactly once each, since the factorial in (3) cancels the permutations of those factors. Summing over all \(rm\) entry choices yields a cross-place contribution \(\chi_n\sum_e c_{e,n}^2/n\). These arguments also cover negative \(\chi_n\); no positivity of individual terms is required.

If \(k=2h\) and a pairing has \(v\) cross-place pairs, its labeled statistic locations and marked slots have \((N)_{h+v+t}=N^{h+v+t}(1+O(1/N))\) choices. Pair statistics give \(N^{h+v}/N^h\) times the \(n^{-v}\) from the cross-place pairs, hence one factor \(1/2\) per cross-place pair; the \(N^t\) marked factor cancels their reference probabilities. Therefore the mixed moments are
\[
 \mathbb E\!\left[S_n^k\prod_\ell(Q_{n,\ell})_{t_\ell}\right]
 = \begin{cases}
 (2h-1)!!\left(\displaystyle\frac{s_n^2+
                \chi_n\sum_e c_{e,n}^2/2}{V_n}\right)^h
                           \prod_\ell (|I_\ell|+o(1))^{t_\ell}+o(1),& k=2h,\\
 o(1),&k\text{ odd}.
 \end{cases}
 \tag{10}
\]
Use \((-1)!!=1\) when \(h=0\). For each color \(O(1/N)\) count errors are \(o(1)\) since the fixed cumulants are subpolynomial and \(V_n\) is bounded below. The ratio inside (10) tends to one by (6): both \(1/V_n\) and \(|\chi_n|/V_n\) are bounded, even when rare coefficients give growing positive kurtosis. Equation (10) gives the moments of an independent standard normal and independent Poisson variables of means \(|I_\ell|\). Ordinary moments follow by expanding powers in falling factorials. Tightness follows from second moments. Higher marginal moments give uniform integrability of mixed moments by Hölder; all subsequential limits have the displayed moments. The product limiting law is moment determinate, for instance by finite exponential moments in a neighborhood of zero (the determined marginals and Hölder give such moments for any law with these mixed moments). Thus convergence holds jointly with the indicated independent limit.

## 5. Transfer of marks and point-process conclusion

The marks of the \(G_a\)'s and \(Y_a\)'s differ only on a norm-cutoff failure or if \(Y_a\) has scaled least singular value in an \(o(1)\)-neighborhood of an interval endpoint. This uses Weyl's singular-value inequality and \(\epsilon_n=o(N^{-1/(2d)})\), uniformly for fixed bounded scaled endpoints, including zero. The probability of a Gaussian reference hit at any such neighborhood is \(o(1/n)\), even under \(g_\epsilon\), by the continuous Gaussian small-\(s_{\min}\) expansion and the same perturbation bound. The one-place density comparison (3) implies \(\|p_{Y_a}-g_\epsilon\|_\infty=n^{-1+o(1)}\); the neighborhood truncated to the Frobenius ball has volume \(O((1+\log n)^{C_0}/n)\). Thus the absolute transfer error for each place is \(n^{-2+o(1)}\), uniformly. A union bound shows that all the original counts on the chosen intervals agree with the smoothed counts with probability tending to one. The Gaussian component transfers by (8).

The one-interval first moment for smoothed counts is bounded for every bounded interval; the transfer just proved gives tight local counts for the original measure. Counting on a finite set of disjoint bounded intervals suffices to identify the unit-rate Poisson limit, since its expected measure has no atoms and such interval counts determine the random locally finite measure. More explicitly, approximate continuous compactly supported test functions by step functions on those intervals and use tightness of the total count on their compact support. Applying the same argument jointly with the tight scalar statistic gives (2). The result does not imply finite-\(n\) independence, a bound on the speed of Gaussian convergence, or a joint claim with the upper spectral extreme.

The companion script uses exact integers and rationals for finite checks of the odd-grid exponential sum, quartic \(2+2\) resonance classification, and the colored-pair normalization. The probability limit uses the uniform expansion and transfer proofs above, not enumeration.
