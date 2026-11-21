# The unconditional full singular-series main in an adaptive zeta-pair mask

Use the notation and positive compact cardinal band of [UnconditionalCardinalZetaBand.md](UnconditionalCardinalZetaBand.md). No zero hypothesis is made. Write \(L=\log X,\ H=X^{2/5},\ Q=\lfloor\exp(L^{1/20})\rfloor,\ \eta=L^{-3/4}\). In the previous mask of reduced rationals of denominators \(q\le Q\), together with \(2d\) for odd \(d\le Q\), omit every denominator divisible by \(r\), **if** there is a primitive Dirichlet character of conductor \(r\le 2Q\) with a real zero \(\beta>1-\eta\). Call the resulting mask \(M^{\rm reg}\). There is at most one such inducing character. Then, uniformly in even \(N\),
\[
 \sum_{\mathcal B_X} B_*(\rho,\rho')M^{\rm reg}(\gamma+\gamma')
       =X\mathfrak S(N)\int w+o(X).                                  \tag{1}
\]
This is an **absolute** \(o(X)\), including when the singular series increases with the target. When there is an exceptional inducing character the omitted spectral shells are **not** asserted negligible: only their lost principal-model contribution is negligible. The genuine aggregate off the selected rational cores remains open.

### Zero and character bounds used

Take primitive inducing characters of the allowed moduli. Landau–Page for conductors through \(2Q\), including the classical zero-free region for bounded imaginary part, excludes all zeros \(\beta>1-\eta,\ |\gamma|\le10\) for the retained conductors; the possible exception would have been real, unique and excluded. See [Ford–Green–Konyagin–Maynard–Tao, Lemma 7.1](https://ford126.web.illinois.edu/wwwpapers/primegaps2.pdf). For \(10\le |\gamma|\le X^{.65}\), [Khale, Theorem 1.1](https://arxiv.org/pdf/2210.06457) gives \(1-\beta\gg(\log(2Q)+L^{2/3}(\log L)^{1/3})^{-1}>\eta\); use the ordinary zeta case for the conductor-one character. We use the classical hybrid density theorem, in the precise form [Koukoulopoulos (1.2) and the paragraph following it](https://dms.umontreal.ca/~koukoulo/documents/publications/shortaps.pdf): for all \(1/2\le\sigma\le1\),
\[
 \sum_{d\le 2Q}\sum_{\chi\bmod d}^{*}N(\sigma,T,\chi)
   \ll ((2Q)^2T)^{(5/2)(1-\sigma)}\log^{14}(2QT),\quad T\ge2.
\]
Here \(5/2>12/5\), and no Riemann/density conjecture is used.

Let \(b\) be a fixed Schwartz function with integral one (the inverse transform of the flat-top); \(m\) ranges through a fixed compact multiple of \(X\). For every retained primitive character,
\[
 \frac1X\int\left|H^{-1}\sum_n\Lambda(n)\chi(n)b((n-m)/H)-{\bf1}_{\chi_0}\right|^2dm
       \ll \exp(-c L^{1/4}).                                          \tag{2}
\]
Here and below one can put a fixed compact smooth cutoff on \(n/X\) equal to one on a neighborhood of the whole \(m/X\)-interval. Its effect on the central smoothed sums is arbitrarily power-small. For details of (2), the smooth explicit formula for a primitive character has normalized zero coefficients \(m^{\rho-1}b_{\rho}(m)\), where
\[
 b_{\rho}(m)=\int b(v)(1+Hv/m)^{\rho-1}g((m+Hv)/X)\,dv
\]
on the positive support of \(g\). For any fixed \(j,D\), \(|(m\partial_m)^j b_{\rho}(m)|\ll_{j,D}(1+|\gamma|H/X)^{-D}\). Indeed for small \(|\gamma|H/X\) this follows by differentiating and Schwartz moments; otherwise integrate by parts repeatedly in \(v\), whose phase derivative has magnitude \(\asymp|\gamma|H/X\) on the support. Each logarithmic \(m\)-derivative costs only a polynomial in \(v\) and \(|\gamma|H/X\), paid by further integrations by parts. The pole gives \(\int b=1\) up to arbitrary inverse powers; the trivial zeros and the possible residue at zero contribute \(O(X^{-1}\log^2(2qX))\) or less after normalization (equivalently use the smooth von Mangoldt explicit formula with compact support away from zero). All nontrivial sums converge after the integrations by parts.

A smooth majorant of the \(m\)-window and two integrations by parts in \(\log m\) bound the integrated pair by the product of the two decaying envelopes times \((1+|\gamma-\gamma'|)^{-2}\); the two real exponents are bounded. Use \(2ab\le a^2+b^2\) and the elementary local zero count \(\#\{t\le\gamma<t+1\}\ll\log(2q(2+|t|))\). The normalized mean square in (2), apart from the small residue error, is at most a constant times
\[
 \sum_{\rho}X^{-2(1-\beta)}(1+|\gamma|H/X)^{-D}\log(2q(2+|\gamma|)).
\]
The part with \(|\gamma|>X^{.65}\) is \(O(X^{-2})\) for \(D=100\), by ordinary dyadic counts and \(H/X=X^{-.6}\). Up to this height, the zeros left of the critical line cost \(O(X^{-.35}L^2)\). On the other half integrate the density bound against \(2L X^{-2(1-\sigma)}d\sigma\) up to \(1-\eta\), including the lower boundary term. Since \((2Q)^2 X^{.65}\le X^{.66}\), the net exponent coefficient satisfies \(2-2.5\cdot .66=.35>0\), giving \(L^{O(1)}e^{-.35 L\eta}\). This proves (2). For imprimitive characters the removed powers of primes dividing the modulus have continuous mean absolute contribution \(O(X^{-1}\log(2q)L)\) in the normalized sum. Removing all proper powers likewise costs \(O(X^{-1/2}L^2)\) in that mean: interchange the nonnegative absolute sums and the smooth mass around each such integer. Only mean **absolute** estimates for the prime-only/imprimitive version are used.

For a long smooth sum tested by \(g_0(p/X)\), with bounded smooth seminorms and fixed compact support, the analogous average against an individual character is \({\bf1}_{\chi_0}X\int g_0+O(Xe^{-cL^{1/4}})\). The smooth explicit formula now has the usual rapidly decreasing Mellin transform. For \(|\gamma|\le X^{.65}\) use \(X^\beta\le Xe^{-L^{1/4}}\) and sum \((1+|\gamma|)^{-3}\) with the local zero count. The tail and discarded prime powers are smaller.

### Rational mask and singular series

Moving \(m\) by at most one changes each unnormalized smooth sum by \(O(L)\) using the elementary absolute derivative sum. Thus (2)'s Cauchy–Schwarz mean absolute bound transfers to the half-integer mesh, uniformly in each allowed character. Expanding the phase on the reduced classes modulo \(q\) costs at most \(O(q)\) in absolute character coefficients (sum of their absolute values is even at most \(\sqrt q\)); primes dividing \(q\) in the central support are absent. The principal additive coefficient is the Ramanujan sum \(\mu(q)/\varphi(q)\). On the outer prime mesh bound the log weight by \(L\) and extend the absolute inner errors to the full mesh. The long estimate above treats the other prime. All costs \(Q^{O(1)}L^{O(1)}\) for characters, mesh and centers are absorbed by \(e^{-cL^{1/4}}\). The unconditional cardinal note's per-window off-line spectral transfer and the geometric replacements have power savings uniform in the bounded real center; \(O(Q^2)=X^{o(1)}\) such windows preserve them. Their disjointness also persists. Thus the finite main is the same paired model as before for every denominator not removed.

If \(r\) is even then \(4\mid r\) (primitive real conductors are fundamental discriminants in absolute value), so every squarefree denominator is retained, hence all nonzero principal terms pair as usual. For odd \(r\) the two squarefree denominators \(d,2d\) are discarded together precisely when \(r\mid d\). With \(g(d)=|\mu^2(d)c_d(N)|/\varphi(d)^2\), terms at multiples of odd squarefree \(r\) have total mass at most \(\prod_{p\mid r}g(p)\,\prod_p(1+g(p))\ll \mathfrak S(N)/\varphi(r)\). The last is \(o(1)\) uniformly: by the elementary effective bound \(1-\beta\gg r^{-1/2}\log^{-2}(2r)\) in the Landau–Page reference and \(1-\beta< L^{-3/4}\), necessarily \(r>L\) for large \(X\), whereas \(\mathfrak S(N)\ll\log\log X\) and \(\varphi(r)\gg\sqrt r\). For our growing \(Q\), the earlier Rankin tail estimate gives \(\sum_{d>Q}g(d)\ll \mathfrak S(N)\exp(-(.9)L^{1/20}/\log L)=o(1)\). This proves (1). Any exception-dependent deletion is part of the definition of the proved mask, not an assertion that the possible exceptional-zero bias is tiny on its own modulus. The classical inputs and exceptional-character excision are not new; the conclusion here is for the cardinal geometric selection of actual Riemann-zeta pairs. It neither requires nor proves an unconditional global exclusion of Landau–Siegel zeros.

### Comparison with recent major-arc work

[Bhowmik–Grimmelt, arXiv:2607.27282v2](https://arxiv.org/abs/2607.27282v2) give an explicit formula for ordinary Goldbach major arcs, including possible exceptional-character terms. [Pintz–Althöfer, arXiv:2610.15559v1](https://arxiv.org/abs/2610.15559v1) use a different explicit formula to bound the size of the Goldbach exceptional set under a uniform zero bound. Neither statement is a fixed-target bound on the complement of the zeta-pair selection defined here. The comparison is about the cutoff geometry and exact quantity estimated, not a new major-arc prime theorem.
