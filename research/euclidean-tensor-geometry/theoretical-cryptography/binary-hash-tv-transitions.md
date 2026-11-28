# Poisson and Gaussian total-variation profiles for random binary linear hashing

For an independent biased binary source, the Fourier coefficients after a linear hash are powers of the bias indexed by the weights of a random binary linear code. This does not make total variation a weight enumerator: it is the \(L^1\) norm of an associated character sum, and the signs can be dependent. We determine its exact normalized law when the shortest weights dominate, and its Gaussian constant throughout the transition to the many-weight regime. The ensemble mean has a different transition, which we also quantify.

All distributions here are abstract and classical, without side information, a deployed extractor, or a scheme or learning instance. [Skórski, *Exact Bias of Linear TRNG Correctors*, §§3 and Appendix 0.A](https://arxiv.org/html/2509.26393v1) gives the Fourier formula, weight-enumerator norms, and bounds for actual total variation; we do not claim those formulas or the leading minimum-weight mechanism as new. [Hao–Huang–Livshyts–Tikhomirov, Theorem I.1 and Proposition 3.2](https://arxiv.org/pdf/1912.12833) establishes the independent minimum-weight asymptotics and an exponential bound on dependencies among short words. Below we use the same short-word mechanism (and give a simple fixed-order binary proof). The new conclusions are normalized **total-variation laws**, the many-word Gaussian constant and binomial window, and the typical-versus-mean transition. The [finite-module Shannon-window result](module-information-spectrum.md) concerns the extraction threshold at entropy, not these fixed-rate low-error windows.

## 1. Parameters and statements

For \(n\to\infty\), let \(A\) be uniformly random among full-row-rank \(k=k_n\) by \(n\) matrices over \(\mathbb F_2\), and let \(X\in\mathbb F_2^n\) have independent \(\mathrm{Bernoulli}(p)\) coordinates, independent of \(A\), with fixed \(0<p<1\), \(p\ne1/2\). Put \(a=|1-2p|\in(0,1)\), and let
\[
 T_A=\operatorname{TV}(\mathcal L(AX\mid A),U_k)
\]
where \(U_k\) is uniform. All ensemble distribution or expectation assertions refer to this fixed-amplitude \(a\).

Assume \(k/n\to R\in(0,1)\), let \(\delta_n\in(0,1/2)\) solve \(h_2(\delta_n)=1-k/n\), where \(h_2\) is binary entropy in bits, and write \(\delta=\lim\delta_n\). Put
\[
 m_n=(2^k-1)2^{-n},\qquad
 u_n=\min\{w\in\mathbb N: m_n\binom n w\ge 1\},\qquad
 \lambda_n=m_n\binom n {u_n}.
\]
The minimum is well-defined for all large \(n\), \(u_n=\delta_n n+O(\log n)\), and \(1\le\lambda_n\le (1-\delta)/\delta+o(1)\). Define the two distinguished weights
\[
        \delta_2=\frac{a^2}{1+a^2},\qquad
        \delta_1=\frac a{1+a},\qquad \delta_2<\delta_1 .
\]

**I. Shortest-word regime.** If \(\delta>\delta_2\), let \(B=(1-\delta)/\delta\). Along any subsequence with \(\lambda_n\to\lambda\), let \((N_j)_{j\in\mathbb Z}\) be independent Poisson variables with means \(\lambda B^j\). Conditional on them, take independent signs \(\varepsilon_{j,\ell}\) with probability \(1/2\) each. Then as a distribution over the public matrix,
\[
 \frac{T_A}{a^{u_n}}\ \Longrightarrow\
 \frac12\,\mathbb E_\varepsilon\left|
      \sum_{j\in\mathbb Z} a^j\sum_{\ell=1}^{N_j}\varepsilon_{j,\ell}
                                  \right|.
 \tag{1}
\]
The sum is defined in conditional \(L^2\), is almost surely finite in that sense, and the right side is a positive, nonconstant random variable of the Poisson counts. In particular the typical limit of \(n^{-1}\log T_A\) is \(\delta\log a\) in probability. The subsequence provision in (1) retains the integer-lattice oscillation of the minimum weight.

**II. Gaussian transition.** If \(\delta_n\to\delta_2\), define
\[
 V_n=m_n(1+a^2)^n\Pr[\operatorname{Bin}(n,\delta_2)\ge u_n].
\]
Then in probability, and also in mean,
\[
                 \frac{T_A}{\sqrt{V_n}}\ \longrightarrow\ \frac1{\sqrt{2\pi}} .
 \tag{2}
\]
There is no restriction on the speed with which \(\delta_n\to\delta_2\). In particular, let \(R_2=1-h_2(\delta_2)\). If
\((k-nR_2)/\sqrt n\to\nu\in\mathbb R\), then
\[
 \frac{T_A}{\sqrt{m_n(1+a^2)^n}}
 \ \longrightarrow\
 \sqrt{\frac1{2\pi}\,
       \Phi\left(\frac{\nu}{h_2'(\delta_2)\sqrt{\delta_2(1-\delta_2)}}\right)}
 \tag{3}
\]
in probability and mean. Here \(\Phi\) is the standard real normal cdf. In particular the untruncated mean-square normalization can differ from the typical variance by a factor tending to two in the centered critical window, and by an unbounded factor along paths with \(\sqrt n(\delta_n-\delta_2)\to+\infty\); (2) uses the truncated binomial mass.

**III. A different transition for the ensemble mean.** Still in the shortest-word regime, if \(\delta_2<\delta<\delta_1\), the expectation of the normalized variable in (1) also converges to the expectation of its limit along each specified subsequence. If \(\delta>\delta_1\), then
\[
                    \mathbb E_A T_A\sim\tfrac12 m_n(1+a)^n ,
 \tag{4}
\]
which decays at a strictly smaller exponential rate than the typical error because it is driven by exponentially rare matrices. If \(\delta_n\to\delta_1\), define
\[
 W_n=m_n(1+a)^n\Pr[\operatorname{Bin}(n,\delta_1)\le u_n].
\]
Then \(\mathbb E_A T_A\sim W_n/2\), with no speed restriction. This is a mean transition; (1) still describes the typical random law there.

We do not determine the fixed rates with \(\delta<\delta_2\) in this note, nor transfer these claims to arbitrary sources, finite rings, or computational assumptions.

## 2. Fourier identity, short-word dependencies, and normalization

It is enough to consider \(p<1/2\); complementing all input bits when \(p>1/2\) is an output translation. Let \(Y\) be uniform in \(\mathbb F_2^k\) and write \(w_y=\operatorname{wt}(A^\mathsf T y)\), \(\chi_y(Y)=(-1)^{y\cdot Y}\). Fourier inversion gives
\[
 T_A=\tfrac12\,\mathbb E_Y|F_A(Y)|,\qquad
             F_A(Y)=\sum_{y\ne0} a^{w_y}\chi_y(Y).
 \tag{5}
\]
The characters are orthonormal in \(L^2\) of the uniform output. In particular, for any subset of the summands, dropping the others changes the absolute expectation in (5) by at most the square root of the sum of their squared amplitudes, or by the sum of their amplitudes. Also \(T_A\ge a^{w_y}/2\) for any nonzero \(y\), because it is at least half the magnitude of any nonconstant Fourier coefficient.

For the proof first let the entries of \(A\) be iid fair bits. The images \(A^\mathsf T y_i\) for linearly independent \(y_i\) are iid uniform binary words. In particular any distinct nonzero binary pair has this property. The probability of rank failure is at most \(m_n\), by summing \(\Pr(A^\mathsf T y=0)=2^{-n}\) over all \(y\ne0\). We condition back to full rank at the end. For counts \(N_{n,w}=|\{y\ne0:w_y=w\}|\),
\[
 \mathbb E N_{n,w}=m_n\binom n w,\qquad
 \operatorname{Var}\left(\sum_{y\ne0} f(w_y)\right)
       \le m_n\sum_{w=0}^n\binom n w f(w)^2                       \tag{6}
\]
for any deterministic real \(f\), by pairwise independence. Stirling's formula around \(\delta_n n\), where
\(\log[m_n\binom n {\lfloor\delta_n n\rfloor}]=-\frac12\log n+O(1)\) uniformly for rates in a compact interior range, and the ratio
\(\binom n {w+1}/\binom n w=(n-w)/(w+1)\) establish the stated facts about \(u_n,\lambda_n\). The same adjacent ratio gives, for each fixed integer \(j\),
\[
 \binom n{u_n+j}/\binom n{u_n}\longrightarrow B^j .
 \tag{7}
\]
For positive offsets the ratios in (7) are bounded above by \(((n-u_n)/(u_n+1))^j\); for negative offsets \(-j\) with \(j>0\) they are bounded by \((u_n/(n-u_n+1))^j\). Indices outside \([0,n]\) give zero counts.

Here is the dependence estimate used in both limits. Suppose \(t_n/n\to\delta\in(0,1/2)\) and \(2^k\Pr[\operatorname{Bin}(n,1/2)\le t_n]=e^{o(n)}\). For every fixed \(s\), the expected number of ordered tuples of at most \(s\) *distinct nonzero* messages with linearly dependent entries whose images all have weight at most \(t_n\) tends to zero exponentially. For a tuple of rank \(r\) choose an independent basis inside it (only a constant number of choices for fixed \(s\)) and test one other word, a sum of at least two basis entries. Conditional on all basis images in the ball \(\operatorname{wt}\le t_n\), they are independent uniform words of that ball. Their weights lie in \([(\delta-\epsilon)n,t_n]\) except with probability \(e^{-c n}\) by the binomial ratios (or entropy bounds), for any sufficiently small fixed \(\epsilon>0\). Given their integer weights, the basis words are independent uniform on their spheres. For a sum of \(\ell\ge2\) of them, realize each sphere as independent Bernoulli coordinates of mean its relative weight, conditioned on its total. This incurs only a polynomial cost for fixed \(\ell\), since the binomial mass at its mean is at least \(1/(n+1)\) by its mode property. Without that conditioning each output parity is an independent Bernoulli with mean
\((1-\prod_{i=1}^{\ell}(1-2p_i))/2\ge 2(\delta-\epsilon)(1-\delta+\epsilon)>\delta+\epsilon\)
for small enough \(\epsilon\). A binomial Chernoff bound then makes the tested sum fall below \(t_n\) with probability at most \(e^{-c' n}\), still exponential after conditioning. Thus each dependent tuple of rank \(r\) has probability at most \(e^{-c_s n}\Pr[\operatorname{Bin}(n,1/2)\le t_n]^r\) of passing all weight tests. There are \(O_s(2^{kr})\) such tuples, by choosing the basis and expressing each other member among its finitely many combinations. This proves the estimate. It is the fixed-order binary case of the short-word estimates used by Hao et al.; no independence of the entire code is assumed.

## 3. Proof of the shortest-word law

Fix an integer \(J\). At the weights \(u_n-J,\ldots,u_n+J\), the count vector converges jointly to independent Poisson variables of the indicated means. Indeed, mixed falling factorial moments count tuples of distinct messages. Independent tuples give products of their binomial weight probabilities, because their images are iid, and their number is \((1+o(1))2^{ks}\) for each fixed total order \(s\). Dependent tuples contribute exponentially little by the preceding estimate; its assumption on the ball holds at \(u_n+J\) by (6)–(7) and the binomial ratio bound. The factorial moments therefore converge to the independent Poisson ones, which determine their distribution. For the same reason, with probability tending to one all messages in this finite weight band form an independent set: first make the count exceed a fixed \(s\) with probability arbitrarily small using tightness, then exclude every dependent tuple of size at most \(s\). For independent messages their characters under the uniform output are jointly independent fair signs. Equation (5) restricted to this band therefore has the limit in (1) restricted to the same band, for each \(J\).

Words at offsets \(<-J\) exist with probability \(O(B_-^{-J})\) uniformly for large \(n\), for some \(B_->1\), by the negative binomial ratio bound and (6). For offsets \(>J\), the expected sum of squared amplitudes divided by \(a^{2u_n}\) is \(O((B_+a^2)^J)\) for a fixed \(B_+>B\) with \(B_+a^2<1\). Thus Parseval, Cauchy–Schwarz and Markov give the required upper-tail truncation in probability. In the limiting Poisson series there are finitely many negative-offset words almost surely, and the nonnegative series has finite conditional squared amplitude because \(\sum_{j\ge0}\lambda B^j a^{2j}<\infty\). Letting \(J\to\infty\) proves (1). With probability one some Poisson count is positive; conditional fair signs give \(\mathbb E_\varepsilon|C+a^j\varepsilon|\ge a^j\) for any independent \(C\). The law is thus positive, and has unbounded support because there is positive probability of a word at arbitrarily negative \(j\). It is almost surely finite, so it is not constant. Compactness of the possible \(\lambda_n\) limits and \(u_n/n\to\delta\) give the typical exponent via subsequences.

If \(\delta<\delta_1\), the expected negative-tail sum of amplitudes divided by \(a^{u_n}\) tends uniformly to zero as \(J\to\infty\): choose \(B_-<B\) close enough that \(aB_->1\), and sum \(\sum_{j>J}(aB_-)^{-j}\). The upper-tail expected square-root bound already tends to zero. At any fixed band the absolute expectation is uniformly integrable by (6) and bounded second moments of the counts. This proves the claimed convergence of means in this range.

## 4. Proof of the many-word transition

Now \(\delta_n\to\delta_2\); abbreviate \(q=\delta_2\) and \(v_n=V_n/a^{2u_n}\). The tilt identity is exact:
\[
 V_n=m_n\sum_{w\ge u_n}\binom n w a^{2w}.
\]
For every fixed \(j\ge0\), the term at \(w=u_n+j\) divided by \(a^{2u_n}\) has size \(\lambda_n\) times a factor tending to one, by (7) because \(Ba^2=1\) at the limiting weight \(q\). Hence \(v_n\to\infty\). Also \(\log v_n=o(n)\): bounding \(V_n\) by its untruncated tilt gives
\[
 \log v_n\le n\,D(\delta_n\|q)+O(\log n)=o(n),
\]
using the natural-log binary relative entropy \(D\) and \(u_n=n\delta_n+O(\log n)\).

Choose \(J_n=\lfloor\log(v_n)/(4|\log a|)\rfloor\), so \(J_n\to\infty\), \(J_n=o(n)\), and \(a^{-2J_n}\le\sqrt{v_n}\). With high probability there are no words below \(u_n-J_n\) by the binomial ratio bound. The expected total squared amplitude of the words between \(u_n-J_n\) and \(u_n-1\) is at most \(O(J_n a^{2u_n} a^{-2J_n})=o(V_n)\), since the binomial coefficients below \(u_n<n/2\) only decrease. The largest squared amplitude in the retained range is at most \(a^{2u_n}a^{-2J_n}=o(V_n)\).

Choose an upper cutoff \(t_n=\lceil(q+\eta_n)n\rceil\) with
\(\eta_n=\max\{4|u_n/n-q|,n^{-1/4}\}\). The tilted binomial above \(t_n\) has mass \(o\) of its mass at or above \(u_n\): use a Chernoff upper bound \(e^{-nD(t_n/n\|q)}\) (shifting by a single integer does not matter), and lower bound the denominator by its mass at \(u_n\), at least \(c n^{-1/2}e^{-nD(u_n/n\|q)}\). The local quadratic expansion of \(D(\,\cdot\,\|q)\) and the factor four in \(\eta_n\) give a gap at least \(c' n\eta_n^2\ge c'\sqrt n\). Consequently the tail above \(t_n\) has expected squared amplitude \(o(V_n)\). In the retained band \([u_n-J_n,t_n]\), (6) bounds the variance of its squared-amplitude total by its largest squared amplitude times its mean. The mean is \((1+o(1))V_n\) by the preceding bounds. Hence its squared-amplitude total divided by \(V_n\) tends in probability to one.

For each fixed moment order \(s\), with probability tending to one all distinct sets of at most \(s\) retained messages are independent, by the short-word estimate in §2: \(t_n/n\to q=\delta\) and \(2^k\Pr[\operatorname{Bin}(n,1/2)\le t_n]=e^{o(n)}\). Thus conditional on such a matrix, the first \(s\) moments of the retained character sum agree *exactly* with those for the same coefficients on independent Rademacher signs. The normalized largest coefficient tends to zero while normalized variance tends to one. For independent signs this implies the standard normal law and convergence of all fixed moments, by the Lindeberg theorem and the subgaussian moment bound. It therefore implies a conditional normal limit in probability for the actual uniformly evaluated character sum as well: along any subsequence pass to another on which the variance and each fixed-order independence event hold eventually almost surely, use the moment method with the moment-determinate normal, and use bounded second moments for uniform integrability of the absolute value. This proves convergence in probability of its normalized absolute expectation to \(\sqrt{2/\pi}\). The omitted upper tail is negligible for (5) by Parseval and Markov; the omitted lower tail is absent with high probability. Equation (2) in probability follows.

For the mean assertion, drop all words below \(u_n\). The expected amplitude sum removed is \(O(a^{u_n})=o(\sqrt{V_n})\) by the negative ratio bound, since near \(q\) one has \(Ba>1\). The truncated \(T_A\) divided by \(\sqrt{V_n}\) has bounded second moment by Parseval and the exact expected squared amplitude \(V_n\). Uniform integrability gives convergence of its mean, hence of the untruncated one. Finally if \((k-nR_2)/\sqrt n\to\nu\), the defining equation of \(\delta_n\) gives
\((u_n-nq)/\sqrt n\to-\nu/h_2'(q)\). The binomial central limit then yields (3).

## 5. Mean transition at the first moment tilt and full rank

If \(\delta>\delta_1\), choose a real \(b\in(\delta_1,\delta)\) and count weights at most \(bn\). Their mean count \(\rho_n\) is exponentially small, but the expectation of their amplitude sum is \((1-o(1))m_n(1+a)^n\) by tilting with \(\operatorname{Bin}(n,\delta_1)\). By pairwise independence, the expectation lost by keeping these contributions only when *exactly one* of them occurs is at most \(\rho_n\) times the full expected low-weight amplitude sum: apply the union bound to every marked summand and each distinct possible companion. On the one-word event (5) is at least half this single coefficient, irrespective of higher frequencies. For the upper bound use half the entire amplitude sum. This proves (4). Its exponential rate is strictly different from the typical one: the first-moment tilt maximizes \(h(x)+x\log a\) at \(\delta_1\), strictly before \(\delta\); there the value is strictly larger than at \(\delta\). The same proof attributes the leading mean to an event of exponentially small probability, not to typical error.

If \(\delta_n\to\delta_1\), \(\mathbb E\) of the amplitude sum at weights \(\le u_n\) is \(W_n\). Here \(w_n=W_n/a^{u_n}\to\infty\), since for each fixed negative offset its individual contribution is \(\lambda_n\) times a factor tending to one; also \(\log w_n=o(n)\) by the same entropy bound as above with first-moment tilt. Retain just weights \(\le u_n-J_n'\) with \(J_n'=\lfloor\log(w_n)/(2|\log a|)\rfloor\). Their expected count tends to zero, and the expected lost amplitude above this cutoff but at most \(u_n\) is \(O(J_n' a^{u_n}a^{-J_n'})=o(W_n)\), since the binomial coefficient is decreasing to the left. The same single-word argument supplies the lower bound. For the upper bound split (5) at \(u_n\): the expected upper-tail \(L^2\) bound is \(O(a^{u_n})=o(W_n)\), since \(Ba^2\to a<1\). Below the split half the expected amplitude sum is \(W_n/2\). This gives the asserted mean at the first-moment transition.

All probability claims persist on conditioning to full row rank since the probability of failure tends to zero. For the means the rank-failure contribution is at most \(m_n\) since \(T_A\le1\). For \(\delta>\delta_1\) this is exponentially smaller than the scale \(m_n(1+a)^n\). In the other asserted mean limits the comparison scale is at least a constant times \(a^{u_n}\), and \(m_n=o(a^{u_n})\): the limiting exponent of \(m_n/a^{u_n}\) is \(-h(\delta)-\delta\log a<0\) for \(\delta\le\delta_1<a\). Thus all means are unchanged to the stated order. Natural logs \(h\) were used in these exponential comparisons, distinct from \(h_2\) in the rate equations.

## Reproduction

Run \(\texttt{python3 verify-binary-hash-tv-transitions.py}\) (standard library). The verifier checks exact Fourier/Parseval, pairwise weight identities and the dependency versus independent-sign distinction on small synthetic matrices, together with the two positive binomial tilts. It does not estimate a deployed extractor or replace the proof of the asymptotic laws.
