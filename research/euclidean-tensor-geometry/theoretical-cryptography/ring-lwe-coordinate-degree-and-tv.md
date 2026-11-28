# Conditional coordinate-degree spectrum and total variation for broad wrapped ring learning

We calculate two different asymptotic quantities for the same random ring-design experiment. The squared norm of the response-coordinate-degree likelihood projection follows a binomial profile for a typical public design, with an exponentially small **absolute** error uniformly over every degree cutoff. The same law holds for the conditional correlation norm of any prescribed mean-zero normalized label feature. For the ordinary likelihood, the full-degree second-moment transition occurs at half the true total-variation transition. Above the latter transition there is still a linear-order coordinate-degree barrier for standardized linear observables. This is a restricted moment statement, not a running-time lower bound or a method for recovering labels.

## 1. Setup and results

Fix an odd integer \(q\ge3\) and \(\beta>0\). Let \(d\) range over powers of two, \(R=(\mathbb Z/q)[X]/(X^d+1)\), and \(N=q^d\). Let \(b=\beta/d<1\), and take \(T=T_d\) with \(t_d=Tb^2\) in a fixed compact subinterval of \((0,\infty)\). There are \(M=Td\) scalar response coordinates. Sample a uniform label \(S\in R\) and independent uniform public rows \(A_1,\ldots,A_T\in R\). Let \(P_A\) be the conditional response law given the whole design \(A\):
\[
 Y_t=A_tS/q+E_t\quad\bmod1,\qquad
 f_b(y)=\sum_{k\in\mathbb Z}b^{k^2}e^{2\pi i k y},
\]
where the errors are independent, each scalar error has density \(f_b\), and division by \(q\) denotes the additive embedding of each coefficient into \(\mathbb T=\mathbb R/\mathbb Z\). The reference response law \(Q\) is product with scalar density
\[
 g(y)=\frac1q\sum_{x\in\mathbb Z/q}f_b(y-x/q)=f_{b^{q^2}}(qy).
\]
It is independent of \(A\). Both densities are positive by the periodized Gaussian formula. Let \(L_A=dP_A/dQ\).

Let \(\mathcal H_{\le D}\) be the closed span in \(L^2(Q)\) of all square-integrable functions depending on at most \(D\) response coordinates. The orthogonal projection \(\Pi_{\le D}\) is onto this space for each fixed \(A\). There is no restriction on dependence on the publicly known \(A\), and no restriction on the one-coordinate functions. Write
\[
 Z_A(D)=\big\|\Pi_{\le D}(L_A-1)\big\|_{L^2(Q)}^2.
\]
For residues \(r\bmod q\), define
\[
 \tau_r=\int_{\mathbb T}\frac{\left|\sum_{k\equiv r\bmod q}b^{k^2}e^{2\pi i k y}\right|^2}{g(y)}\,dy,
 \qquad B=\sum_{r\ne0}\tau_r .
\]
Here \(\tau_0=1\), \(\tau_{\pm1}=b^2+O_q(b^8)\), and for the other nonzero residues \(\tau_r=O_q(b^8)\), so \(B=2b^2+O_q(b^8)\). These estimates follow from scalar Parseval and \(g=1+O_q(b^{q^2})\), all uniformly in \(y\).

**Theorem 1 (uniform conditional profile).** There is a constant \(c>0\) depending only on the fixed parameters and the compact subinterval for \(t_d\), such that for all sufficiently large \(d\),
\[
 {\mathbb E}_A \max_{0\le D\le M}
 \left| Z_A(D)-q^{-d}\sum_{k=1}^D\binom Mk B^k\right|\le e^{-cd}.
 \tag{1}
\]
In particular this is not merely an average squared-moment formula, and the error is absolute even when the reference binomial sum is exponentially large. There is a prescribed-label-feature version: let \(h_d:R\to\mathbb R\) be any deterministic sequence of functions with \(\mathbb E_S h_d(S)=0\) and \(\mathbb E_S h_d(S)^2=1\). Set \(H_A=\mathbb E_s[h_d(s)L_{A,s}]\) with \(L_{A,s}=dP_{A,s}/dQ\) the fixed-label likelihood, and replace \(Z_A(D)\) in (1) by \(\|\Pi_{\le D}H_A\|_2^2\). The same exponential bound holds with constants independent of \(h_d\); that rate is not claimed simultaneously over choices made after seeing \(A\). A simultaneous version does hold with a slower error: for every fixed \(\epsilon>0\), the expected maximum error over the degree cutoff and all unit-\(L^2\), mean-zero label features, even features chosen after seeing \(A\), is \(O_\epsilon(d^{-2+\epsilon})\). This controls squared projected norms, not the norm itself.

**Theorem 2 (true total variation).** If \(\sqrt d(t_d-\log q)\to\xi\) for finite or infinite \(\xi\), then, in \(L^1\) over the public design,
\[
 \operatorname{TV}(P_A,Q)\longrightarrow
 \Phi\!\left(\frac{\xi}{\sqrt{2\log q}}\right),
 \tag{2}
\]
where \(\Phi\) is the standard normal CDF. The same holds with product Haar \(Q_{\rm Haar}\) in (2). It is a statement about statistical laws, not an effective way to distinguish them.

For a fixed \(A\), the largest possible absolute mean gap over observables in \(\mathcal H_{\le D}\) of null variance at most one is precisely \(\sqrt{Z_A(D)}\): center the observable and use orthogonal projection and Cauchy–Schwarz. In particular for \(D=o(d)\) this mean gap tends to zero for typical \(A\) at each fixed \(t_d\to t>0\), even when true TV tends to one. For a prescribed feature the same bound applies to \(|\mathbb E[h_d(S)F(Y)\mid A]|\) for \(F\in\mathcal H_{\le D}\) of null variance at most one, since \(H_A\) represents this correlation and has null mean zero. This concerns standardized linear means or correlations of the specified observables. It does not claim that arbitrary nonlinear functions of those observables, or arbitrary algorithms, have the same limitation.

## 2. Fourier formula and elementary ideal bounds

Let \(v_r(y)\) be the sum in the numerator defining \(\tau_r\), divided by \(g(y)\). The \(v_r\) are orthogonal under \(g(y)\,dy\), by the character of their translations through \(1/q\). Also \(v_0=1\). The scalar relative density at a shift \(x/q\) is \(\sum_r e^{-2\pi i rx/q}v_r(y)\). Thus expansion of the product density, followed by uniform averaging of \(S\), leaves exactly the sectors satisfying
\[
 \sum_{t=1}^T \overline{A_t} w_t=0,\qquad
 \overline a=a(X^{-1}),\qquad w=(w_1,\ldots,w_T)\in R^T .
\]
The coefficient pairing gives \(\langle u,as\rangle=\langle\overline a u,s\rangle\), since multiplication by \(X\) is a signed shift. The bar is a bijection and an automorphism. Each sector is a product of mean-zero coordinate functions on precisely its nonzero residue positions. Such a product is orthogonal to every function that misses a nonzero position. Writing \(\operatorname{wt}(w)\) for the number of these positions, \(\omega(w)=\prod_{t,j}\tau_{(w_t)_j}\), and \(G_{A,k}\) for the degree-\(k\) contribution, we get
\[
 G_{A,k}=\sum_{\operatorname{wt}(w)=k}\omega(w)
        \mathbf1_{\{\sum_t\overline{A_t}w_t=0\}},\qquad
 Z_A(D)=\sum_{k=1}^D G_{A,k}.
 \tag{3}
\]
The full weight at degree \(k\) without the constraint is \(W_k=\binom Mk B^k\). More generally let \(G_{A,k}(z)\) have the right side of (3) with the target \(z\in R\) instead of zero, and \(Z_A(D;z)=\sum_{k=1}^D G_{A,k}(z)\). With \(\widehat h(z)=\mathbb E_s h_d(s)e^{-2\pi i\langle z,s\rangle/q}\), the squared projected feature norm is exactly \(\sum_z|\widehat h(z)|^2 Z_A(D;z)\). The missing zero-degree term is zero by centering \(h_d\), and \(\sum_z|\widehat h(z)|^2=1\).

The following two uniform facts hold for fixed odd \(q\). Some \(\alpha>0\) satisfies \(|J|\ge e^{\alpha d}\) for every nonzero ideal \(J\lhd R\); also the fraction of nonunits in \(R\) is at most \(C_q e^{-\alpha d}\), possibly reducing \(\alpha\). To see this, for each \(p\mid q\) the irreducible factors of \(X^d+1\bmod p\) are distinct and have degree \(\operatorname{ord}_{2d}(p)\). All roots have exact order \(2d\), and Frobenius cycles therefore have that common degree. For fixed odd \(p\) the degree is a constant positive fraction of \(d\) for all sufficiently large dyadic \(d\): repeated squaring gives \(v_2(p^{2^j}-1)=v_2(p^2-1)+j-1\) for \(j\ge1\). The number of factors stays bounded. A nonunit must vanish modulo one of these maximal residues. A nonzero ideal in a prime-power CRT component contains a nonzero element of its top \(p\)-torsion layer (multiply an element with minimal coefficient valuation by the suitable power of \(p\)). That layer is isomorphic as an \(R\)-module to the ring modulo \(p\), so the ideal has size at least the size of one residue field. CRT transfers the same lower bound after minimizing over \(p\mid q\).

For each \(w\) the sum in (3), over uniform \(A\), is uniform on \(J(w)=\sum_t w_tR\), by equal fibers of multiplication and independent addition. Thus for \(w\ne0\) the probability of any prescribed target is at most \(e^{-\alpha d}\); it is either zero or \(1/|J(w)|\). In particular this handles low degrees without incorrectly treating all rare ring words as unit words.

## 3. Concentration in the entire active degree band

Choose fixed small \(c_0>0\) and large \(C_0>0\), to be specified. Sample one \(w\) of weight \(k\in[c_0d,C_0 d]\) from \(\omega(w)/W_k\). Its support is a uniform \(k\)-subset of the \(M\) response positions, and at these positions its residues are independent with law \(\tau_r/B\), \(r\ne0\). We call a row a singleton row for \(w\) if exactly one of its \(d\) positions is occupied. Constants in \(e^{-\Omega(d\log d)}\) below can depend on \(c_0,C_0\) and the fixed parameters.

With probability \(1-e^{-\Omega(d\log d)}\), there are at least \(k/2\) singleton rows. If there are fewer, at most \(\lfloor3k/4\rfloor\) rows are occupied. A fixed set of \(r\) rows contains the whole support with probability at most \((r/T)^k\), by sampling coordinates without replacement. The union bound with \(r=\lfloor3k/4\rfloor\) is at most \(e^r(r/T)^{k-r}\); here \(T=\Theta(d^2)\).

For two independently drawn words of weights \(k,l\in[c_0d,C_0d]\), with the same overwhelmingly high probability there are at least \(k/4\) singleton rows of the first word missed by the second word, and at least \(l/4\) in the reverse direction (rounding integer thresholds has no effect). Indeed a failure with \(k/2\) singletons requires the second support to hit at least \(k/4\) of the first support's singleton rows. For any \(h=\lfloor k/4\rfloor\) specified distinct rows, the probability that all are hit by a uniform \(l\)-subset is bounded by
\[
 \frac{(l)_h d^h}{(Td)_h}\le (2l/T)^h .
\]
The first inequality is the count over injections into the \(l\) ordered chosen positions; a union bound over the possible row sets costs at most \(2^k\). Interchange the two words for the other direction. Conditional on both supports, singleton residue values remain independent. The probability that a nonzero residue drawn from \(\tau_r/B\) is not a unit in \(\mathbb Z/q\) is at most \(O_q(b^6)\) because \(1,-1\) are units. Therefore except on another \(e^{-\Omega(d\log d)}\) event, each word has an exclusive singleton row whose residue is a unit. The same argument for just one word yields a unit singleton without the exclusivity condition.

A singleton with unit residue is a unit monomial in \(R\). Its row makes the sum for that word uniform on all of \(R\) given the other public coefficients. In the pair case two disjoint exclusive singleton rows make the two sums jointly uniform on \(R^2\), even conditional on all other public coefficients. Outside the good occupancy events probabilities are simply bounded by one. Consequently uniformly on the band, for every fixed target \(z\),
\[
 \begin{split}
 \big|{\mathbb E}_A G_{A,k}(z)-q^{-d}W_k\big|
       &\le e^{-\Omega(d\log d)}W_k,\\
 {\mathbb E}_A G_{A,k}(z)^2 &\le (q^{-2d}+e^{-\Omega(d\log d)})W_k^2.
 \end{split}
\]
Expanding about \(q^{-d}W_k\) and using both estimates gives \({\mathbb E}_A|G_{A,k}(z)-q^{-d}W_k|\le W_k e^{-\Omega(d\log d)}\). The sum of all \(W_k\) is \((1+B)^M=\exp(O(d))\), so total mean absolute error over the active band is still superexponentially small.

Below \(c_0d\), use the ideal bound from Section 2, since there may be nonunit words. Using \(MB=O(d)\) and \(\binom Mk\le(eM/k)^k\), choose \(c_0\) small enough that \(\sum_{1\le k<c_0d}W_k\le e^{\alpha d/2}\). The total mean contribution and the deterministic comparison term over this lower range are exponentially small. Above \(C_0 d\), positivity and the bound
\[
 \sum_{k>C_0d} W_k\le e^{-C_0d}(1+eB)^M
\]
make the whole high range exponentially small, by choosing \(C_0\) large. The maximum over cutoffs is bounded by the sum of absolute errors over all degrees. This proves (1), even with \(Z_A(D;z)\) for any fixed target \(z\) and a bound uniform in \(z\). Weighting these bounds by \(|\widehat h(z)|^2\) proves the feature assertion in mean at the exponential rate.

For the simultaneously chosen feature assertion, fix an integer \(r\ge2\). Use the same active band but choose its lower endpoint \(c_0d\) small enough that \(V:=\sum_{1\le k<c_0d} W_k\le e^{\alpha d/(2r)}\). On the band a union bound in expectation over at most \(q^d\) target values costs only \(e^{O(d)}\) against the superexponential error, and the upper tail is bounded deterministically. For the low band write \(C_A(z)=\sum_{1\le k<c_0d}G_{A,k}(z)\). In expanding \(\mathbb E_A\sum_z C_A(z)^r\), if two of the chosen words \(w,w'\) differ, equality of all their sums requires the sum for \(w-w'\ne0\) to vanish. By Section 2 this has probability at most \(e^{-\alpha d}\), without independence assumptions on the other words. The all-identical terms contribute only the sum of the \(r\)-th powers of their weights. Thus
\[
 \mathbb E_A \sum_z C_A(z)^r
 \le e^{-\alpha d} V^r+\big(1+\textstyle\sum_{a\ne0}\tau_a^r\big)^M-1
 =O_r(e^{-\alpha d/2}+d^{3-2r}).
\]
By positivity this also bounds the \(r\)-th moment of the maximum over low-band prefixes and targets. Taking the \(r\)-th root gives \(O_r(d^{-2+3/r})\); the deterministic low-band comparison is exponentially small. Take \(r\) large as a function of \(\epsilon\). The feature formula expresses its squared norm as a convex combination of target terms, so the bound applies to all features at once. This estimate is near the natural pointwise error scale: at degree one the maximum over targets is at least \(\tau_1\sim\beta^2d^{-2}\) by picking the target of any word with a single residue \(1\), whereas the binomial comparison for \(D=1\) is exponentially small. This last observation is about the maximum over Fourier targets, not a claim of an efficient test.

## 4. Consequences of the binomial law

Put \(p_*=B/(1+B)\). The deterministic term in (1) is
\[
 q^{-d}(1+B)^M\Pr[\operatorname{Bin}(M,p_*)\le D]-q^{-d}.
 \tag{4}
\]
Both \(Mp_*\) and \(M\log(1+B)\) equal \(2t_d d+O(d^{-1})\). It follows from (1) that the full-degree \(\chi^2(P_A\Vert Q)\) goes to zero in probability for fixed limit \(t<\log q/2\), and is asymptotic in probability to \(\exp[d(2t_d-\log q)]\) for \(t>\log q/2\). At the transition, if \(d(2t_d-\log q)\to u\) and \((D-2t_d d)/\sqrt{2t_d d}\to x\), then \(Z_A(D)\to e^u\Phi(x)\) in \(L^1\) over \(A\), by the binomial CLT. Taking \(D=M\) gives \(e^u\).

There is also a sharp degree transition for any fixed \(t>\log q/2\). Here take \(t_d=t+O(d^{-2})\), as for \(T=\lfloor t/b^2\rfloor\). Let \(\delta\in(0,2t)\) be the unique solution of
\[
 \delta(1+\log(2t/\delta))=\log q,\qquad \theta=\log(2t/\delta)>0.
\]
If \(x_d=D-\delta d-(\log d)/(2\theta)\) stays bounded, then in \(L^1\) over \(A\)
\[
 Z_A(D)-\frac{e^{\theta x_d}}{(1-e^{-\theta})\sqrt{2\pi\delta}}\longrightarrow0 .
 \tag{5}
\]
The real \(x_d\) need not converge, because \(D\) is integer. Indeed \(\binom MD B^D=(MB)^D/D!\,(1+o(1))\), as \(D^2/M=O(d^{-1})\); Stirling's formula gives \(q^{-d}W_D=e^{\theta x_d}/\sqrt{2\pi\delta}\,(1+o(1))\). For \(k\le D\), \(W_{k-1}/W_k=k/((M-k+1)B)\) is increasing in \(k\), is bounded by a fixed constant strictly less than one for large \(d\), and converges to \(e^{-\theta}\) for \(D-k\) fixed. Thus the prefix sum has the displayed geometric factor. For a fixed fractional cutoff below \(\delta\), (1) gives vanishing \(Z_A\); above \(\delta\), it gives divergence, by monotonicity and the same estimate at a cutoff between \(\delta\) and \(2t\). The absolute error assertion in (1) is not an exact relative rate for extremely small cutoffs.

## 5. True TV: conditional phase soft covering

For fixed \(s,A\), let \(L_{A,s}(y)\) denote the relative density of the unaveraged response law at label \(s\). Under that law, \(\log L_{A,s}(Y)\) has one common distribution independent of \(s,A\), namely the law of
\[
 I_M=\sum_{i=1}^M \log\frac{f_b(E_i)}{g(E_i)},\qquad E_i\stackrel{\mathrm{iid}}\sim f_b .
\]
The mean and variance of one summand are \(b^2+O_q(b^4)\) and \(2b^2+O_q(b^4)\). For example use \(f_b=1+2b\cos(2\pi y)+O(b^4)\), expand its log through order \(b^3\), and integrate; odd cosine powers contribute no mean and \(g=1+O(b^9)\). The third absolute centered moment is \(O(b^3)\) uniformly. Thus \(I_M\) has mean \(t_d d+O(d^{-1})\), variance \(2t_d d+O(d^{-1})\), and after centering and scaling converges to a standard normal by Lyapunov's criterion.

Fix \(h_d=d^{1/4}\) and let \(\rho_\pm=\Pr[I_M>d\log q\pm h_d]\). For each fixed \(A\),
\[
 \operatorname{TV}(P_A,Q)\ge \rho_+-e^{-h_d}.
 \tag{6}
\]
Indeed the mass under \(Q\) of the union of all level sets \(L_{A,s}>N e^{h_d}\) is at most \(e^{-h_d}\) by a union/Markov bound, whereas under \(P_A\) its mass is at least the probability of this level for the actual label. This event serves only to bound the statistical distance.

For the upper bound truncate each summand of the mixture to the set \(L_{A,s}\le N e^{-h_d}\), calling its truncated likelihood \(U_{A,s}\) and writing \(U_A=N^{-1}\sum_s U_{A,s}\). For each response coordinate write \(y=(j+\eta)/q\) with \(j\in\mathbb Z/q\), \(0\le\eta<1\). Let \(\boldsymbol\eta\) be the full vector of within-cell positions. Under \(Q\), conditionally on \(\boldsymbol\eta\), all grid phases \(j\) are independent uniform. Thus for each fixed \(A,s\), the conditional \(Q\)-mean of \(U_{A,s}\) is the same \(m(\boldsymbol\eta)\), independent of \(A,s\), since a grid shift permutes the phases and preserves \(\boldsymbol\eta\). It is at most one because the untruncated version has conditional mean one.

If \(\Delta=s-s'\) is a unit, then under independent uniform \(A\) and \(Y\sim Q\), conditionally on \(\boldsymbol\eta\), the phase vectors of \(Y-As/q\) and of \(Y-As'/q\) are independent uniform. The first is uniform independently of \(A\) by translation, and their phase difference is uniform because every \(A_t\Delta\) is uniform. This remains true when \(s,s'\) are nonunits individually. It gives
\[
 {\mathbb E}_{A,Q}[U_{A,s}U_{A,s'}\mid\boldsymbol\eta]=m(\boldsymbol\eta)^2 .
 \tag{7}
\]
It is essential to condition on \(\boldsymbol\eta\); the two continuous residuals share it, and are not independent without conditioning.

For \(\Delta\ne0\) a nonunit, the following bound suffices:
\[
 {\mathbb E}_{A,Q}U_{A,s}U_{A,s'}\le
 {\mathbb E}_{A,Q}L_{A,s}L_{A,s'}\le e^{O(1)}.
 \tag{8}
\]
For one row, integrate the product of the two likelihoods under the scalar product reference. Orthogonality of the \(v_r\) yields the autocorrelation \(\sum_{w\in R}\prod_j\tau_{w_j}\,e^{2\pi i\langle w,A_t\Delta\rangle/q}\); averaging \(A_t\) retains frequencies in the coefficient orthogonal complement of \(I=\Delta R\). No singleton with coefficient \(+1\) or \(-1\) can survive there: a nonzero \(I\) has a nonzero coefficient somewhere and its signed cyclic shifts cover every position. For nonunit singleton residues the total weight is \(O(d b^8)\). All words of weight at least two contribute at most \(O((dB)^2)\), by a binomial bound. Thus the one-row averaged autocorrelation is \(1+O(d^{-2})\), and the \(T=O(d^2)\) row product is bounded as in (8). Nonzero nonunit differences form only an exponentially small fraction of the ordered pairs by the ideal estimates.

Finally the diagonal term \({\mathbb E}_Q U_{A,s}^2\) is bounded by \(Ne^{-h_d}\), since \(U_{A,s}\le Ne^{-h_d}\) and \({\mathbb E}_Q U_{A,s}\le1\). Expanding the square of \(U_A-m(\boldsymbol\eta)\), the exact conditional centering and (7) cancel the unit-difference terms. Using (8) for the others gives
\[
 \mathbb E_{A,Q}|U_A-m(\boldsymbol\eta)|^2
       \le e^{-h_d}+O(e^{-\alpha d}) .
\]
The expected integrated mass removed from \(L_A\) is \(\rho_-\); also \(\int (1-m)\,dQ=\rho_-\). The \(L^1\) triangle inequality therefore yields
\[
 \mathbb E_A\operatorname{TV}(P_A,Q)
       \le \rho_-+O(e^{-h_d/2}+e^{-\alpha d/2}).
 \tag{9}
\]
The normal limit makes \(\rho_+,\rho_-\) converge to the same right side of (2); for an infinite \(\xi\) the same conclusion follows from Chebyshev or the centered normal limit. The lower bound (6) holds for every design, and together with the mean upper bound (9) this gives \(L^1\) convergence over \(A\). Finally the product comparison \(\operatorname{TV}(Q,Q_{\rm Haar})\le M O(b^{q^2})=o(1)\) proves the Haar claim. The orthogonal projection in Theorem 1 was defined under \(Q\); the Haar TV statement alone does not replace that Hilbert-space reference.

## 6. Scope and prior work

* [Kunisky, Wein and Bandeira, arXiv:1907.11636](https://arxiv.org/abs/1907.11636), especially Sec. 4.2.4 and footnote 17, discuss the distinction between polynomial and coordinate degree, due to Hopkins for this formulation. [Holmgren and Wein, ITCS 2021 paper on counterexamples](https://drops.dagstuhl.de/entities/document/10.4230/LIPIcs.ITCS.2021.75) and [Chen, Gong, Haferkamp and Quek, arXiv:2505.22743v2, Secs. 3.6 and 10.1](https://arxiv.org/html/2505.22743v2) also give important limitations and comparison with finite-field parity models. No inference about polynomial-time algorithms is made here from a coordinate-degree norm.
* [Cuff, Soft Covering with High Probability](https://arxiv.org/abs/1605.06396) gives second-order soft covering for an independently sampled memoryless codebook; [Pathegama and Barg, arXiv:2308.11009](https://arxiv.org/abs/2308.11009) relate binary code smoothing and Rényi thresholds. The ordinary structural analogue of (2) is channel resolvability, not a new general soft-covering principle. Our ensemble here has dependent codewords from one fixed-ring design, and the proof uses conditional grid phases and nonunit controls, while (1) is a conditional *all-degree* spectrum.
* The [previous local-batch communication note](https://github.com/mxym/math/blob/9c7c903b1aa999d663b8bc4f5b48ad499beb738e/research/euclidean-tensor-geometry/theoretical-cryptography/ring-lwe-batch-communication-entropy-scale.md) gives the general ideal-sector annealed identity and a proper-ideal bound, as well as the first-order information scale for local inference. Our use of the same sector expansion does not claim those facts anew. Here the coefficients are fully public, and the new conclusions concern concentration over them, the degree windows, and the true marginal-output TV window.
* The formulas are for fixed odd \(q\), independent ring coefficients, and the stated broad continuous product-noise scaling. In particular, divergence of the low-degree squared norm can coexist with vanishing true TV (\(\log q/2<t<\log q\)), and is not by itself an effective statistic or even a positive TV lower bound. No key-search algorithm, general polynomial-time lower bound, or inference about a concrete scheme is given.

The accompanying checker only tests finite algebraic and combinatorial identities and the approximation formulas on generated data; it is not a solver.
