# Unconditional pruning of the primitive-conductor sum at dyadic Goldbach targets

Let \(N=2^k\), \(L=\log N\), and \(R_{\rm p}(N)=\sum_{p+p'=N}(\log p)(\log p')\) with ordered primes. Fix \(0<\delta<13/15\), \(0<\epsilon<1/30\). There is an exact, real, explicitly calibrated primitive-character detector. In its asymptotic zero-product formula:
* all nonprincipal conductors \(q\mid N\) with \(q\le N^{13/15-\delta}\) contribute \(O_{\delta,\epsilon,A}(NL^{-A})\);
* at **every remaining** primitive conductor, nontrivial zeros outside \([1/2-B(A)\log\log N/\log N,\ 5/6+\epsilon)\) can be deleted, including their mixed terms with undiscarded zeros, at total cost \(O_{\delta,\epsilon,A}(NL^{-A})\). Here \(B(A)>0\) is a fixed sufficiently large constant.

Both bounds hold for any fixed \(A>0\), without GRH or a ratios hypothesis. The remaining high-conductor, lower-real-part, \(\chi(-1)\)-signed zero product is **not** estimated. The result neither proves positivity for \(2^k\) nor bounds its exceptional indices. The near-one deletion below follows from independent published Weyl subconvexity and classical fixed-modulus large values; it does not extrapolate a newer large-values argument from \([.7,.8]\) to the near-one regime.

## 1. Exact dyadic calibration and uniform explicit formula

Put \(C_2=\prod_{p>2}(1-1/(p-1)^2)\) and \(h(v)=e^{20(1-v)}(\sin(\pi(v-1))/(\pi(v-1)))^2\), as in [Gou–Wang–Xu, arXiv:2611.18825v1](https://arxiv.org/html/2611.18825v1), §3.5. Set
\[
 \lambda=\frac{\int_0^\infty v h(v)\,dv-C_2}{\int_0^\infty v(v-1)^2 h(v)\,dv},\qquad
 H(v)=h(v)(1-\lambda(v-1)^2).
\]
The denominator is finite positive. Exactly \(H(1)=1,\ H(j)=0\) at integers \(j\ge2\), and \(\int vH(v)\,dv=C_2\). The auxiliary kernel need not be nonnegative away from integer sums. With \(e(t)=e^{2\pi it}\), write
\[
 H(u+v)=e^{20}\int_{-1}^1(1-|\tau|)e(-\tau)
 \sum_{i,j\ge0,\ i+j\le2}c_{ij}\,w_{\tau,i}(u)w_{\tau,j}(v)\,d\tau,
 \qquad w_{\tau,i}(u)=u^i e^{-(20-2\pi i\tau)u}.
\]
This is the Fourier identity for \(\operatorname{sinc}^2\), followed by expanding \(1-\lambda(u+v-1)^2\); in the exponential \(i=\sqrt{-1}\), distinct from the integer weight index. Constants \(c_{ij}\) are real. Denote this bilinear finite sum/integral on arrays by \(\mathcal B\). Character orthogonality modulo \(N\), with \(\chi(-1)\chi(m)\bar\chi(n)\) (not \(\chi(m)\chi(n)\)), then gives exactly
\[
 \sum_{\substack{m+n=N\\m,n\text{ odd}}}\Lambda(m)\Lambda(n)
 =\frac1{\phi(N)}\sum_{\chi\bmod N}\chi(-1)\mathcal B(A_\chi,A_{\bar\chi}),
 \qquad A_\chi(\tau,i)=\sum_{n\ge1}\Lambda(n)\chi(n)w_{\tau,i}(n/N).
 \tag{1}
\]
At any nonprincipal conductor \(q=2^j\mid N\), the primitive source and its lift have precisely the same values on all integers. There is no primitive \(q=2\) family. The \(q=1\) source is the principal lift, ignoring powers of 2. By the ordinary PNT and uniform partial summation on these finitely many smooth \(w_{\tau,i}\), its contribution is
\(N^2\int vH(v)\,dv/\phi(N)+O_A(NL^{-A})=2C_2N+O_A(NL^{-A})\). The total difference upon retaining only true primes on the left is \(O(N^{1/2}L^3)\).

The transform is \(\widehat w_{\tau,i}(s)=\Gamma(s+i)(20-2\pi i\tau)^{-s-i}\) with the obvious index convention. On any closed strip of positive real parts, it is \(\ll (1+|\Im s|)^C e^{-c|\Im s|}\) uniformly in \(|\tau|\le1\), since \(|\arg(20-2\pi i\tau)|\le\arctan(\pi/10)<\pi/2\). Uniformly for nonprincipal primitive \(q\le N\), the standard explicit formula gives
\[
 A_\chi(\tau,i)=-\sum_{\substack{\rho\ \text{nontrivial}\\\Re\rho\ge1/4,\ |\Im\rho|\le V}}
       N^\rho\widehat w_{\tau,i}(\rho)+O(N^{1/4}L^C),\qquad V=DL
 \tag{2}
\]
for sufficiently large absolute \(D\). To check uniformity, move truncated Mellin inversion from \(5/4\) to a character-dependent abscissa in \([1/10,1/5]\) at distance \(\gg L^{-3}\) from every real part of a nontrivial zero of height at most \(V+2\); there are \(O(L^2)\) such zeros per character. Choose top/bottom ordinates in \([V,V+1]\) and \([-V-1,-V]\) away from zeros by \(\gg L^{-2}\), using \(O(L)\) local zeros in each unit bin. The local logarithmic derivative formula bounds all new sides by a fixed log power, with the horizontal terms negligible by exponential decay. The residue sign is minus, and all zeros are counted with multiplicity. Terms with \(\Re\rho<1/4\) crossed on the chosen side cost \(O(N^{1/4}L^C)\); those at heights between \(V\) and the chosen end ordinates are exponentially small. No trivial zero or gamma pole lies in the contour.

For any selected zero set \(\mathcal Z\), let \(Z_{\chi,\mathcal Z}\) be the portion of the sum in (2), with its minus sign. Cauchy and the \(O(\log(q(2+|\gamma|)))\) unit-bin zero count give
\[
 \sum_{\chi\bmod q}^{*}|Z_{\chi,\mathcal Z}(\tau,i)|^2
 \ll L\sum_{\chi\bmod q}^{*}\sum_{\rho\in\mathcal Z}N^{2\Re\rho}.
 \tag{3}
\]
Use the exponentially decaying weight above in both factors of Cauchy, then discard it from the inner square. Also the complete character energy satisfies
\[
 \sum_{\chi\bmod q}|A_\chi(\tau,i)|^2\ll N^2 L \qquad(q\le N). \tag{4}
\]
Indeed apply orthogonality, and Cauchy separately in each residue class with one exponentially decaying factor; its unweighted mass is \(O(N/q)\) per residue, and \(\sum_{n\ge1}\Lambda(n)^2(n/N)^{2i}e^{-20n/N}\ll NL\) by Chebyshev and \(\Lambda^2\le\Lambda\log\). Thus the aggregate cost of the (2) errors and their cross terms in (1) is \(O(N^{3/4}L^{C'})\), using \(\sum_{\chi\bmod q}^*|{\rm error}|^2\ll N^{3/2}L^C\) and \(O(L)\) conductors. The same reasoning via (4) pays the mixed terms when any spectral deletion has total squared norm \(O_A(N^2L^{-A})\) per \(q\). It does not apply a positivity claim to \(\mathcal B\), and does not estimate the retained signed sum.

## 2. A log-power density bound uniformly up to the 1-line

Here \(q>1\) is arbitrary, \(V\ge2\), \(P=q(2+V)\), \(r=\epsilon/100\). With \(\omega=5/6+\epsilon\), the following bound holds for all \(\omega\le b\le1\):
\[
 \sum_{\chi\bmod q}^{*}\#\{\rho:\Re\rho\ge b,\ |\Im\rho|\le V\}
 \ll_\epsilon P^{(2-24r)(1-b)}(\log P)^{C_\epsilon}. \tag{5}
\]
Proof: choose zero detector \(X=P^r,\ Y=P^{1/2-8r}\),
\(M_X(s,\chi)=\sum_{n\le X}\mu(n)\chi(n)n^{-s}\), and the usual exponentially weighted series \(L(s,\chi)M_X(s,\chi)\) with coefficient \(a(n)=\sum_{d\mid n,d\le X}\mu(d)\). At a zero \(\rho=\beta+i\gamma\) in the stated range, shift its Mellin representation to \(\Re w=1/2-\beta\), using \(\Gamma(w)Y^w\). The residue at \(w=0\) vanishes and there is no principal pole for a primitive character of conductor \(q>1\). The line integral is absolutely
\[
 \ll_\epsilon Y^{1/2-\beta}P^{1/6+r}X^{1/2}=o(1)
\]
by [Petrow–Young, Duke Math. J. 172 (2023), Theorem 1.1](https://discovery.ucl.ac.uk/id/eprint/10158522/1/1908.10346v3.pdf), which gives the literal hybrid Weyl bound for **all** primitive conductors. Here \(q(1+|\gamma+\Im w|)\ll P(1+|\Im w|)\), the extra factor integrated by gamma decay; no power of \(q\) is hidden. The exponent is at most \(r(3/2+8/3-50)+800r^2<0\). Thus the zero is detected by the Dirichlet-polynomial branch alone. The \(n=1\) term is \(1+o(1)\), the terms \(1<n\le X\) vanish, and \(n>Y\log^2P\) has exponentially small tail (use \(|a(n)|\le d(n)\)). Dyadic subdivision yields a block \(M<n\le2M\), possibly shortened by those endpoints, with the polynomial of size \(\gg1/\log P\).

Put \(u_0=2/3-8r\). For each such fixed block raise its polynomial to the least integer \(j\) with \(M^j\ge P^{u_0}\). The endpoint \(X/2\le M\le P^{1/2-7r}\) implies \(2\le j=O_\epsilon(1)\). If \(j=2\), \(M^j\le P^{1-14r}\); otherwise \(M^j<P^{u_0}M\le P^{3u_0/2}=P^{1-12r}\). The coefficients after raising are bounded by \(d_{2j}(n)\) on a range bounded above/below by fixed multiples (depending on \(j\)) of \(M^j\). Their second and \(d(n)\)-weighted square moments, after multiplication by \(n^{-b}\), are \(O_\epsilon((M^j)^{1-2b}(\log P)^{O_\epsilon(1)})\), by the elementary fixed divisor moments. At each tested zero the remaining evaluation argument \(\rho-b\) has nonnegative real part.

Apply the fixed-modulus large-values estimate [Montgomery–Vaughan, *Multiplicative Number Theory III*, author manuscript](https://personal.science.psu.edu/rcv4/Vol3/Vol3.pdf), Thm 27.13 and Corollary (27.54), with size threshold \(\gg(\log P)^{-j}\). One can shift negative ordinates to the interval \([0,2V]\) by coefficient phases, and split zeros per character into \(O(\log P)\) classes of ordinate spacing at least 1, using the local count. With \(D_M=M^j\), the estimate gives at most
\[
 (\log P)^{O_\epsilon(1)}
 [\,D_M^{2(1-b)}+P D_M^{4-6b}\,]
\]
zeros for this block (compare their (28.30) and the line indicating the fixed-modulus substitution after that argument). Both terms are bounded by \(P^{(2-24r)(1-b)}\). For the second, \((4-6b)<0\), so use \(D_M\ge P^{u_0}\), and the difference of exponents is
\(1+u_0(4-6b)-(2-24r)(1-b)=5/3-2b+(24b-8)r\le-184r\).
Sum the \(O(\log P)\) blocks and spacing classes. This proves (5) independently of a claimed near-one extrapolation of a new density theorem. A fixed-\(\epsilon\) power saving in the **counting bound's prefactor** would not be an acceptable substitute for the displayed polylog loss.

## 3. Applying the density bounds to the genuine dyadic detector

First suppress nonprincipal \(q\le L^3\) by the usual Siegel–Walfisz theorem and smooth partial summation, with arbitrary log precision. Smooth weights of scale \(N\) can be integrated against prefix estimates on \([N/L^K, NL^K]\) for \(K\) large; the initial \(O(N/L^K)\) and exponentially decaying upper tails preserve arbitrary log precision. No exceptional term is discarded in the large dyadic family: for \(q=2^j\ge16\), every real character factors modulo 8 (squares of units are precisely the kernel of mod 8), so no primitive real character exists. [Banks–Shparlinski, arXiv:1605.07553, Thm 3.2](https://arxiv.org/html/1605.07553#S3.SS2) applies directly to primitive dyadic moduli (its prime-exponent balance condition is automatic) and \(|\gamma|\le V=DL\) when \(q>L^3\). It gives \(1-\beta\gg (\log q)^{-2/3}(\log\log q)^{-1/3}\), uniformly \(\gg L^{-2/3}(\log L)^{-1/3}\), with no real exception.

Apply (5) to the part \(\beta\ge\omega\) for **every** such \(q\le N\). Integration against \(N^{2b}\) by partial summation and the zero-free gap yields
\[
 \sum_{\chi\bmod q}^{*}\sum_{\beta\ge\omega,\ |\gamma|\le V}N^{2\beta}
 \ll_\epsilon N^2 L^C
       \exp[-c_\epsilon L^{1/3}(\log L)^{-1/3}].
\]
In fact \(P=q(2+V)\le NL^{O(1)}\), so the exponent deficit \(24r(1-b)L\) pays all log powers. The counts in (3) can be restricted to the indicated subset; there is no need to bound the parity difference in this deleted strip. Equations (3)–(4) pay all of its mixed terms.

Now take \(q\le N^\theta\), \(\theta=13/15-\delta\). For the zeros \(1/4\le \beta\le1/2\) the trivial count \(O(qV\log(q(2+V)))\) suffices, since their squared contribution is \(O(N^{1+\theta}L^C)\). For \(1/2<\beta<\omega\) use the \(30/13\) density exponent of [Chen–Gupta–Li, arXiv:2507.08296v2, Thm 1.2](https://arxiv.org/html/2507.08296v2) for \(V\)-smooth moduli (powers of 2 satisfy it). In fact only their proved interval \([.7,.8]\) is needed: adjoining it on the left is the uniform Ingham estimate (28.9) of Montgomery–Vaughan, with exponent at most \(30/13\) for \(\beta\le.7\); on the right use (28.10) there with, e.g., \(\eta=1/10\), giving exponent \(\le15/7<30/13\) for \(\beta\ge.8\). Thus we do not rely on a sharper \(<2\) extrapolation of Chen–Gupta–Li to \(\beta>.9\). The additive small power in CGL causes no problem **only in the bounded-away-from-one interval**: \(2-(30/13)\theta>0\), \(1-\omega>0\), so choose it less than half of \((2-(30/13)\theta)(1-\omega)\). Partial summation gives \(O_{\delta,\epsilon}(N^{2-c}L^C)\) for a fixed \(c>0\). This pays the complete remaining \(q\le N^\theta\) nonprincipal contribution by (3); dividing by \(\phi(N)=N/2\), the \(O(L)\) possible primitive conductors cost only one log.

There is also a cheap lower-real-part deletion at **all** remaining conductors, not just low ones. Let \(b_-(N)=1/2-B\log L/L\), with \(B=A+10\). There are \(O(qVL)\) zeros altogether in (2). By (3), those with \(1/4\le\beta<b_-\) give a norm square \(O(LqVLN^{2b_-})=O(N^2L^{3-2B})\), since \(q\le N\) and \(V=DL\). Against the full energy (4) every cross term is \(O(N^2 L^{2-B})\), before normalization. Even after the divisor sum and division by \(\phi(N)\), this is \(O(NL^{3-B})\), compatible with the advertised error.

Finally let \(Z_\chi\) be the sum in (2) restricted to \(b_-(N)\le\Re\rho<\omega,\ |\Im\rho|\le V\). The resulting asymptotic pruning formula is
\[
 R_{\rm p}(2^k)=2C_2 N+\frac1{\phi(N)}
 \sum_{\substack{q\mid N\\q>N^{13/15-\delta}}}
 \sum_{\chi\bmod q}^{*}\chi(-1)\mathcal B(Z_\chi,Z_{\bar\chi})
 +O_{\delta,\epsilon,A}(NL^{-A}).
\]
On a hypothetical dyadic exception, this particular residual is negative by essentially \(2C_2N\). That is a necessary consequence, not an independently established lower bound for the residual. In particular, the top conductor family contains many nonreal characters of both parities, and neither the new density estimate nor the absolute second-moment in (4) distinguishes their signed cross-correlation in the retained real-part range.

## Comparison with sparse-target work

Brüdern–Perelli, [*Goldbach numbers in sparse sequences* (1998), Theorem 1](https://www.numdam.org/article/AIF_1998__48_2_353_0.pdf), prove an almost-all result for nearest-even values of \(\exp((\log n)^\gamma)\), \(1<\gamma<3/2\), using exponential sums over those target values. This is not an assertion on the prescribed targets \(2^k\). The power-of-two summands in classical Goldbach–Linnik (or [Johnston–Trudgian arXiv:2605.17825](https://arxiv.org/abs/2605.17825)) are extra variables, not a pure binary representation of a dyadic target. The present formula is pointwise at that target, but a pruning formula, not a representation or exceptional-set theorem.
