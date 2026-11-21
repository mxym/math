# The full Goldbach singular series in disjoint flat-topped shells of zeta zero pairs

Assume Dirichlet GRH, including zeta. This companion to [ReflectedZetaMajorMinorShells.md](ReflectedZetaMajorMinorShells.md) extracts the **whole** expected singular series (up to \(o(1)\)) from a geometric mask on the *total ordinate* of genuine Riemann-zeta zero pairs. The pairs have macroscopic, separated height ratio. For even targets the actual double-zero contribution selected by the mask is strictly positive of order at least \(X\). The remaining signed aggregate on the mask complement is **not** bounded below here. This is not strong Goldbach. The signed major-shell estimate would hold even at an exceptional even target.

Use \(X=N-1/2,\ \delta=1/X,\ L=\log X,\ H=X^{2/5},\ Q=\lfloor X^{1/100}\rfloor,\ D=\lfloor X^{1/25}\rfloor\). Let \(w,J,V,C\) be exactly the weight, ratio kernel, pair term and reflected prime-power integral of the companion. Set \(U=\int u w(u)du,\ V_0=\int u(1-u)w(u)du\). Fix real even \(F\in C_c^\infty((-2,2))\), \(0\le F\le1\), equal to 1 on \([-1,1]\). The distinct reduced rational numbers
\[
 {\cal R}=\{r=a/q+j:\ 1\le q\le Q,\ 0\le a<q,\ (a,q)=1,\ j\in\mathbb Z,\ |r|\le D\}
\]
include \(0\) via \(q=1,a=0\). Put
\[
 M_X(t)=\sum_{r\in{\cal R}}F(H(t/X-2\pi r)).
\]
Different centers \(2\pi r\) are spaced at least \(2\pi/Q^2\) apart, much greater than \(4/H\). Thus \(0\le M_X\le1\) pointwise; it is exactly 1 on the specified cores, exactly 0 off their expanded union. No deconvolution or division by an oscillatory Fresnel factor is being asserted.

Let \(\mathcal H\) consist of ordered zeta-zero pairs, with multiplicities, \(X^{4/5}\le|\gamma|,|\gamma'|\le X^{6/5}\), same sign, \(.29\le\gamma/(\gamma+\gamma')\le .37\). Write \(t=\gamma+\gamma'\). For \(\mathfrak S(N)=\sum_{q\ge1}\mu(q)^2c_q(N)/\varphi(q)^2\) the conclusions are
\[
 \sum_{\mathcal H} V(\rho,\rho')M_X(t)
      = X[\mathfrak S(N) U - V_0]+o(X),                                      \tag{1}
\]
\[
 C(X)=X\mathfrak S(N)U+
       \sum_{\mathcal H} V(\rho,\rho')[1-M_X(t)]+o(X).                          \tag{2}
\]
The symmetric mask makes these sums real. For even \(N\), \(\mathfrak S(N)\ge2\prod_{p>2}(1-(p-1)^{-2})>1\). The last strict lower bound is elementary: the product over all integers \(k\ge2\) of \(1-k^{-2}\) is \(1/2\), and omitting at least one factor already increases it by a fixed factor. Hence the pair term in (1) has a positive uniform linear lower bound. For odd \(N\) the series is zero. Equation (3) in the companion identifies \(C(X)\) with a single genuine prime-pair count up to \(O(\sqrt X L^2)\); thus strict positivity at fixed macroscopic scale in (2) would imply a representation, but the rightmost signed term can have either sign. The zero-frequency cell accounts for the pole \(XV_0\), not a new high-ordinate diagonal.

### 1. Short-interval sums in moving residue phases

For a fixed Schwartz function \(b\) of integral 1, \(\chi\bmod q,\ q\le Q\), and any fixed central interval of real \(m\asymp X\), one has
\[
 \int \left|\sum_p(\log p)\chi(p)b((p-m)/H)-{\bf1}_{\chi_0}H\right|^2 dm
       \ll_b XH L^4.                                                           \tag{3}
\]
The same bound holds summing the squared expression on the half-integer mesh. Here and below a fixed smooth \(g(p/X)=1\) on a neighborhood of the \(m/X\) interval and supported in a compact subset of \((0,\infty)\) may be inserted; omitted tails cost arbitrary negative powers by Schwartz decay. For nonnegative or signed \(b\) the estimates are unchanged.

Here is a proof, to make the conductor dependence explicit. For a primitive inducing character apply the ordinary differentiated von Mangoldt explicit formula to the compact test \(g(v/X)b((v-m)/H)\) with \(\Lambda\) weights. The pole integral is \(H+O_A(X^{-A})\) for conductor one. The trivial-zero series is \(O(H/X)\) uniformly: its kernels on the support are \(v^{-1-\nu}\) over admissible nonnegative integers \(\nu\) of the given parity (zeta has \(\nu\ge2\)); constant terms of the integrated explicit formula differentiate to zero on this interval away from 1. The nontrivial zero term for \(\rho=1/2+i\gamma\) is, up to the global minus sign,
\[
 (H/\sqrt X)e^{i\gamma\log m}A_\gamma(m/X),\quad
 A_\gamma(s)=\int g(s+hz)b(z)(s+hz)^{-1/2}
           \exp(i\gamma\log(1+hz/s))\,dz,\quad h=H/X.
\]
For fixed \(k,B\) all \(s\) derivatives through order \(k\) are \(O_{k,B}((1+|\gamma|h)^{-B})\) uniformly on the fixed \(s\)-range. Differentiating the phase in \(s\) only costs \(O_j(|\gamma|h|z|)\) there, since \(s\) and \(s+hz\) stay bounded away from zero. In the large \(|\gamma|h\) range integrate by parts repeatedly in \(z\), whose phase derivative is \(\gamma h/(s+hz)\); the Schwartz bounds absorb all powers of \(z\). For the squared \(m\) norm use a smooth majorant and integrate by parts twice in \(\log s\). The resulting Gram kernel after the exterior \(H^2\) is bounded by
\[
 (1+|\gamma|h)^{-B}(1+|\gamma'|h)^{-B}(1+|\gamma-\gamma'|)^{-2}.
\]
The local zero count in unit intervals is \(O(\log(q(2+|\gamma|)))\); the row-sum estimate and a dyadic tail sum give the total \(O(H^2 h^{-1}L^2)=O(XH L^2)\). The rapid decay also justifies the smooth explicit-formula expansion. Passing from the inducing primitive character to \(\chi\) in the **prime-only** sum costs at most \(O_b(\log q)\). In removing proper powers, the near range \(|p^k-m|\le H X^{1/200}\) contains \(O(1)\) powers of each exponent \(k\ge2\) since the consecutive integer \(k\)-th powers near \(X\) are spaced \(\gg\sqrt X\). There are \(O(L)\) exponents and each weight is \(O(L)\); the rest costs \(O_A(X^{-A})\). These uniform errors are absorbed into (3). Finally the sum on the left changes by \(O_b(L)\) under a displacement of \(m\) by at most 1, by the Schwartz bound for \(b'\), summing over integers at spacing 1. Integrate on each mesh cell to deduce the discrete estimate.

For reduced \(a\bmod q\) expand \(e(-a p/q)\) on the unit group, with \(e(x)=e^{2\pi i x}\), and separate the \(p\mid q\) terms at cost \(O_b(\log q)\). The principal Fourier coefficient is \(\mu(q)/\varphi(q)\). By Parseval the normalized Fourier coefficients have squared sum 1, so their absolute sum is at most \(\sqrt{\varphi(q)}\). Minkowski and (3) show that the squared mesh norm of the modulated sum minus \(H\mu(q)/\varphi(q)\) is \(O(q XH L^4)\). The analogous long-range one-prime sum with a fixed-compact-support weight \(G(p/X)\) of bounded sup norm and total variation is
\[
 \sum_p(\log p)G(p/X)e(-ap/q)
 =X\frac{\mu(q)}{\varphi(q)}\int G+O(\sqrt{qX}L^2)
\]
uniformly in such \(G\) of bounded norm and variation, by the standard Dirichlet-GRH prime number theorem and partial summation. No bound for *pairs* of primes in a short window has been assumed.

### 2. One rational shell, uniform over all aliases

Choose the inverse Schwartz transform \(b\) with \(F(z)=\int b(v)e^{ivz}dv\); it is real even, need not be positive, and has integral 1. Fix \(\xi=1/200\) and real compact smooth \(\sigma=1\) on \([-1,1]\), supported in \((-2,2)\). For \(\tau=2\pi r\) take the average
\[
 \mathcal A_\tau=\int b(v)\sigma(v/X^\xi)
             e^{-i\tau H v}e^{-2hv} C(Xe^{hv})\,dv .                           \tag{4}
\]
Throughout (4) \(\delta=1/X\) is unchanged. Inserting the finite polynomial cutoffs of the companion costs \(O(X^{9/10}L^2)\) uniformly per center, since the absolute mass of the measure is bounded and \(|hv|=o(1)\). The mixed pole/zero terms are \(O(\sqrt X)\). The pole/pole is \(XV_0[{\bf1}_{\tau=0}+O(hX^\xi)+O_A(X^{-A})]\): use \(e^{hv}=1+O(hX^\xi)\) and \(F(-\tau H)=0\) for nonzero \(r\) since \(|r|\ge1/Q\). Each retained pair's multiplier is \(F(H(t/X-\tau))+O_A(X^{-A})\); the uniform error is simply the \(L^1\) tail of the Schwartz inverse beyond \(X^\xi\). There are \(O(X^{12/5}L^2)\) retained pairs before any ratio pruning, each \(O_w(1)\) in magnitude. Wrong signs or ratios in these cutoffs cost \(O_A(X^{-A})\) in total, by integration by parts in \(J\): \(|\gamma-tu|\gg |\gamma|+|\gamma'|\) on the support if the signs differ (also if \(t=0\)), or if the signs agree but the ratio misses \([.29,.37]\). These errors are uniform under the bounded shell multipliers. This proves
\[
 \mathcal A_\tau=XV_0{\bf1}_{r=0}+\sum_{\mathcal H} V\,F(H(t/X-\tau))
          + O(X^{9/10}L^2+X h X^\xi).                                        \tag{5}
\]

On the arithmetic side let \(s=(B-X)/H\), so \(v=\log(1+hs)/h=s+O(hs^2)\) on the integration range. Replace \(e^{-i\tau Hv}\) by \(e^{-i\tau Hs}\). The error in its phase is \(O((1+D)H^2X^{-1+2\xi})\); this is possible because \(H<\sqrt X\) by a power. The Jacobian and \(e^{-2hv}\) are \(1+O(hX^\xi)\). Replacing \(b(v)\sigma(v/X^\xi)\) by \(b(s)\) has integrated error \(O(hX^{3\xi})+O_A(X^{-A})\) by the mean value theorem on the retained range and the Schwartz tail on its edges. One may keep a smooth truncation to \(|s|\le3X^\xi\) until after the prime sums are compactly restricted. On that range \(C(B)\ll X L^2\) uniformly by the at-most-two integer totals and bounded cells; proper powers cost \(O(\sqrt X L^2)\).

As in (6) of the companion, integrate the two independent cell variables \(y=p-z,\ B-y=p'-z'\). The intervals are exactly \(0\le z\le p/(X+1),\ 0\le z'\le p'/(X+1)\) up to endpoints. The exponential on the cells is \(e^{-i\tau(p+p'-X)}e^{i\tau(z+z')}\), integrated *without approximation in \(\tau\)* to the two aperture factors. Write \(A_\tau(u)=\int_0^u e^{i\tau z} dz\); its derivative has modulus 1, even for the largest aliases. Replacing \(w(y/B)\), the two endpoints and the argument of \(b\) as in the companion has additive error per log weight \(O(H X^\xi/X+1/H)\); there are \(O(XH X^\xi)\) possible pairs before multiplying by \(1/H\). In the resulting expression replace \(A_\tau(p'/X)\) by \(A_\tau(1-p/X)\) at the same cost, because \(|p+p'-X|\ll HX^\xi\). With fixed compact cutoffs on both primes all discarded Schwartz tails cost \(O_A(X^{-A})\). Combining these estimates, the uniform total arithmetic error so far is
\[
 O\left(X L^2 \left[(1+D)H^2X^{-1+4\xi}+H^{-1}X^{4\xi}
                      +(H/X)X^{4\xi}\right]+\sqrt X L^2\right).               \tag{6}
\]
In particular it is \(O(X^{.87})\) for large \(X\).

The remaining expression is a short modulated prime sum centered at the half-integer \(X-p\), averaged against \((\log p)e(-ap/q)\) and \(w(u)A_\tau(u)A_\tau(1-u)\), \(u=p/X\), times \(e^{i\tau X}/H\). Both the boundedness and total variation of this last smooth weight are uniform in \(\tau\), by the aperture derivative bound. Cauchy with \(\sum_{p\asymp X}\log^2p\ll XL\) and the mesh variance in §1, followed by the long-range one-prime estimate, yields
\[
 \mathcal A_\tau =
 X\,\frac{\mu(q)^2}{\varphi(q)^2}\,e(aN/q)
   \int w(u) \frac{\sin(\pi r u)\sin(\pi r(1-u))}{\pi^2r^2}\,du
 +O\left(X^{.87}+X\sqrt{q/H}L^3+\sqrt{qX}L^2\right).                          \tag{7}
\]
Use the continuous limit at \(r=0\). In deriving the phase in (7), the two aperture phases multiply to \(e^{i\tau/2}\), and \(X+1/2=N\) is an integer. An integer translate \(j\) changes the aperture but not \(e(aN/q)\), and the argument has not silently set the aperture equal to 1.

### 3. The alias identity and the full singular series

For each fixed \(\alpha=a/q\) and \(0<u<1/2\),
\[
 \sum_{j\in\mathbb Z}
 \frac{\sin(\pi(\alpha+j)u)\sin(\pi(\alpha+j)(1-u))}
      {\pi^2(\alpha+j)^2}=u.                                                   \tag{8}
\]
Indeed these are the Fourier transform values at \(\alpha+j\) of the convolution of the centered interval indicators of lengths \(u\) and \(1-u\). The convolution is continuous, supported on \([-1/2,1/2]\), and its value at 0 is \(u\). Periodization after modulation and Fourier inversion at 0 prove (8); the \(O((1+|j|)^{-2})\) tails converge absolutely, uniformly on the support of \(w\) and \(\alpha\in[0,1)\). Extending the finite \(|j+\alpha|\le D\) sum of *main terms only* in (7) costs
\[
 \ll X D^{-1}\sum_{q\le Q}1/\varphi(q)=o(X).
\]
For example \(1/\varphi(q)\ll \log(2q)/q\) is ample. No infinite sum of the errors in (5) or (7) is taken. There are \(O(Q^2D)=O(X^{.06})\) actual centers. Their total error in (5)–(7) is \(o(X)\): even the largest cutoff cost \(X^{.9}L^2\) per center gives \(O(X^{.96}L^2)\).

Summing the phases over reduced \(a\) gives \(c_q(N)\). Uniformly for \(N=X+1/2\), the omitted series tail is \(O_\epsilon(X^\epsilon Q^{-1+\epsilon})=o(1)\) with sufficiently small \(\epsilon\). In detail, for squarefree \(q\) write \(q=d e,\ d=(q,N)\). Then \(|c_q(N)|=\varphi(d)\) and the absolute coefficient is \(1/(\varphi(d)\varphi(e)^2)\). For \(d\mid N,\ d\le Q\), use \(\sum_{e>Q/d}1/\varphi(e)^2\ll_\epsilon(Q/d)^{-1+\epsilon}\); for \(d>Q\) the \(e\)-sum is bounded. The divisor count and \(d/\varphi(d)\ll_\epsilon d^\epsilon\) give the claimed bound with arbitrarily small adjustments to \(\epsilon\). The Euler product gives the stated value for even \(N\) and zero for odd \(N\). Equations (5)–(8) give (1). Subtract this from the fixed-\(X\), cutoff explicit formula of the companion to get (2).

**Boundary of the conclusion.** This is the usual additive singular series, now evaluated as an actual signed aggregate in flat-topped, separated, near-rational **zeta-ordinate** bands. It is not a substitute for proving negativity cannot build up on the complement. The mask is exactly zero for heights beyond the last retained alias; those portions remain in the complement as well, unless separately bounded. The complement includes the tapered edges of the major windows; it vanishes on all their inner cores. The historical sources on the circle method, double-zero expansions and reflected-interval tests listed in the companion apply here. Neither ordinary Montgomery near-neighbor pair correlation nor a mean-square over even targets provides the missing signed estimate.

For an earlier major-arc explicit formula see [Bhowmik–Grimmelt, §7](https://arxiv.org/html/2607.27282v2#S7), with Dirichlet-character zero terms on the ordinary additive circle. [Gou–Wang–Xu, §3.5](https://arxiv.org/html/2611.18825v1#S3.SS5) obtains a full fixed-target asymptotic under their additional ratios hypothesis. This note uses neither a novelty claim for the singular series nor an estimate for its own remaining fixed-target complement.
