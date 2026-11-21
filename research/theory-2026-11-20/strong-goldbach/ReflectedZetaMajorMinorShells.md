# A parity-signed and an irrational-frequency shell of two actual zeta zeros

Assume the Riemann hypothesis **for zeta only**. There is a subunit reflected-prime-interval integral at one fixed target. In its double-zero expansion, a smooth shell of *two distinct positive ordinates*, both of order the target and with their ratio bounded away from one, has a positive order-\(N\) real part at every large even \(N\). A different shell at a badly approximable additive frequency is \(O_\epsilon(N^{19/20+\epsilon})\). These are **components** of the expansion, not a signed estimate for their sum. The first component corresponds to a classical *major* frequency and would be positive even if that particular even target were missing. Its proof uses nearby nonmissing sums. There is no strong Goldbach conclusion or assertion that each minor shell can be summed with the displayed individual saving.

### Definitions and conclusions

Let \(X=N-1/2,\ \delta=1/X,\ L=\log X\), for any large integer \(N\). Fix nonnegative nonzero \(w\in C_c^\infty((.31,.35))\), and nonnegative \(b\in C_c^\infty((-1,1))\) with \(\int b=1\). Write \(\rho=1/2+i\gamma,\ \rho'=1/2+i\gamma'\), counting multiplicities, and define
\[
 c(\rho)=\frac{(1+\delta)^\rho-1}{\rho},\quad t=\gamma+\gamma',\quad
 J(\rho,\rho')=\int w(u)u^\rho(1-u)^{\rho'}du,\quad
 V(\rho,\rho')=X^{2+it}c(\rho)c(\rho')J(\rho,\rho').
\]
For fixed \(\tau>0\) and \(1\ll H=o(X)\), the actual complex shell multiplier is
\[
 K_{\tau,H}(t)=\int b(v)(1+Hv/X)^{2+it}e^{-i\tau Hv}\,dv.
\]
Keeping its complex phase matters: there is **no** claim about the same sharp-cutoff sum with multiplier 1. In the following sums retain only \(\gamma,\gamma'>0,\ .29\le \gamma/t\le .37\).
* **Parity frequency:** for \(H=X^{1/2}L^4\) and each fixed \(0<\epsilon<1/4\), restrict additionally to \(|t-\pi X|\le X^{1/2+\epsilon}\). Then
\[
 \sum V(\rho,\rho')K_{\pi,H}(t)
 =(-1)^N\frac{2X}{\pi^2}\int w(u)\sin(\pi u)\,du+o(X).
 \tag{1}
\]
The main term is real with nonzero specified sign. The claim is for all integer targets, not an average over target centers. One can also use \(H=X^{1/2-\eta}\) and shell width \(X^{1/2+2\eta}\), for fixed \(0<\eta<1/4\), using the short-interval variant below.
* **A genuinely minor frequency:** fix a badly approximable \(\alpha\in(0,1)\) (e.g. \(\sqrt2-1\)), put \(\tau=2\pi\alpha,\ H=X^{7/10}\), and restrict additionally to \(|t-\tau X|\le(2+2\tau)H\). Then
\[
 \left|\sum V(\rho,\rho') K_{\tau,H}(t)\right|\ll_{w,b,\alpha,\epsilon}X^{19/20+\epsilon}. \tag{2}
\]
No assertion of a first use of zeta double sums or of a new prime-exponential-sum bound is intended. The ingredients and their prior scope are below.

### Fixed-target anchor, not a modular surrogate

Put \(U(y)=\psi((1+\delta)y)-\psi(y)\), and
\[
 C(B)=\int w(y/B)U(y)U(B-y)\,dy.
\]
**The one value of \(\delta=1/X\) is held fixed for all \(B\)** in this argument. At \(B=X\) each contributing pair of integers \(m,n\) has \(X<m+n\le X+1\), so \(m+n=N\) exactly. Write \(d_m=m/(X+1)\): the cell giving the increment at \(m\) is \(y\in[m-d_m,m)\) up to null endpoints. For \(w\) on the indicated support the full first cell is admissible: writing \(y=m-z\) gives \(0\le z<d_m<1/2\) and \(X-y=n-1/2+z\), which lies in the second cell since \(d_n>1/2\). This statement is needed only for cells meeting the support (and then \(m/X\in(.30,.36)\) for large \(X\)). Consequently
\[
 C(X)=\sum_{p+p'=N}(\log p)(\log p')\int_0^{d_p} w((p-z)/X)\,dz
           +O_w(\sqrt X L^2)
 \tag{3}
\]
with genuine primes. Uniformly for \(|B-X|\le H=o(X)\), possible integer totals lie in \((B,(1+\delta)B]\), at most two integers, and each operand ranges over a fixed subinterval of \((0,X)\). If either operand is a proper prime power there are \(O(\sqrt X)\) possibilities for it (squares dominate; cubic and higher powers cost \(O(X^{1/3}\log X)\)); the other operand then has at most two possibilities. Cell lengths are bounded. This proves the error also for each \(C(B)\), uniformly; coalescing these terms into primes is unnecessary.

### Exact explicit formula in local \(L^2\)

The ordinary von Mangoldt explicit formula away from prime-power endpoints gives
\[
 U(y)=\delta y-\sum_\rho c(\rho)y^\rho+O(\delta X^{-2})
 \quad(c_1X\le y\le c_2X)
 \tag{4}
\]
for fixed positive \(c_1,c_2\), the remainder from the difference of the smooth trivial-zero terms. Constants in the explicit formula cancel. Symmetric zero cutoffs have their usual almost-everywhere meaning. They also converge in local \(L^2(dy)\), as follows.

For \(T\ge2\), any subset of \(T<|\gamma|\le2T\) contributes squared norm
\[
 \ll X^2\log(2T)\sum_\gamma |c(\rho)|^2
 \ll X^2\min(\delta^2 T,T^{-1})\log^2(2T).
 \tag{5}
\]
Indeed take \(z=\log(y/X)\) and a compact smooth majorant in \(z\); the integrals of \(e^{i(\gamma-\gamma')z}\) decay faster than \((1+|\gamma-\gamma'|)^{-2}\). The row and column sums of this kernel are \(O(\log(2T))\) by the ordinary local zero count with multiplicity, and \(|c|\ll\min(\delta,T^{-1})\). A bounded initial segment is harmless. Minkowski's inequality over dyadic intervals bounds the entire low tail up to \(T_0\) by \(O(\sqrt{T_0}\log(2T_0))\) in norm, and the entire high tail above \(T_1\) by \(O(X\log(2T_1)/\sqrt{T_1})\) if \(T_0\le X\le T_1\). This proves the asserted convergence without an absolute exchange of the bare double-zero series.

Throughout the moving \(B\) interval the two integration variables lie in fixed compact positive multiples of \(X\), below \(.8X\). There \(\|U\|_2\ll\sqrt{XL}\): its integer cells have lengths \(<1\), do not overlap, and \(\sum_{m\ll X}\Lambda(m)^2\ll X\log X\). The same norm bound holds for the full zero sum by (4). Cauchy therefore justifies inserting both expansions into the reflected integral, by first taking finite cutoffs. In particular keeping \(X/L^A\le|\gamma|,|\gamma'|\le XL^A\) has covariance error \(O(X L^{(3-A)/2})\) for \(A>3\); keeping instead \(X^{4/5}\le|\gamma|,|\gamma'|\le X^{6/5}\) costs \(O(X^{9/10}L^2)\). These bounds are uniform before any \(B\)-averaging. The pure continuous main is \(\delta^2B^3\int wu(1-u)\,du\). Either single-zero cross term is \(O(\sqrt X)\): its smooth \(u\)-integral is \(O_k((1+|\gamma|)^{-k})\) by integration by parts, and its outer factors are \(O(\delta B^{5/2}|c|)\) with \(|c|\ll\delta\). Trivial-zero errors are smaller. At fixed \(B=X\) the remaining term is precisely the limit of the sums of \(V\).

### A genuine spectral projection and its arithmetic value

Average \(C(X+Hv)\) against \(b(v)e^{-i\tau Hv}dv\). Its zero-pair term is exactly \(\sum V K_{\tau,H}\) with the preceding cutoff convention. Its continuous main is \(O_k(X(1+H)^{-k})\) by smooth Fourier decay; its single-zero terms remain \(O(\sqrt X)\). To evaluate the arithmetic side, replace the integration in \(B,y\) by \(y,z=B-y\) (Jacobian 1). On prime cells \(y=p-a,\ z=p'-a'\), one has \(0\le a\le d_p,\ 0\le a'\le d_{p'}\). Define \(A_\tau(v)=\int_0^v e^{i\tau s}\,ds\). Up to error \(O((H+X/H)L^2+\sqrt X L^2)\), the average equals
\[
 \frac1H\sum_{p,p'}\log p\log p'\ b((p+p'-X)/H)\,e^{-i\tau(p+p'-X)}
 w(p/X) A_\tau(p/X) A_\tau(p'/X).
 \tag{6}
\]
To see the error, replace \(w(y/B)\) by \(w(p/X)\), the argument of \(b\) by the integer-total argument, and \(d_p,d_{p'}\) by \(p/X,p'/X\). Their per-cell accumulated relative-to-unit additive errors are \(O(H/X+1/H+1/X)\). There are \(O(XH)\) candidate integer pairs in the enlarged support and each log weight is \(O(L^2)\); the outside factor is \(1/H\). Both prime variables can freely be cut to fixed compact subintervals of \((0,X)\) with smooth cutoffs equal to one on the implied supports. The fixed proper-power error was proved after (3).

At \(\tau=\pi\), both primes are odd, so \(e^{-i\pi(p+p'-X)}=(-1)^N(-i)\). The product of apertures is \((4/\pi^2)e^{i\pi(p+p')/(2X)}\sin(\pi p/(2X))\sin(\pi p'/(2X))\). Since \(p+p'=X+O(H)\), after multiplication by the phase this is
\[
 (-1)^N(2/\pi^2)\sin(\pi p/X)+O(H/X).
\]
For \(H=\sqrt X L^4\), the RH prime number theorem and partial summation give \(\sum_{p'}\log p'\, b((p'-(X-p))/H)=H+O_b(\sqrt X L^2)\) uniformly on the retained \(p\) range. Another ordinary PNT in \(p\) proves the main on the right of (1), already with relative \(o(1)\).

For the optional \(H=X^{1/2-\eta}\) use the classical RH Selberg integral for short prime increments, \(\int_{cX}^{CX}|\theta(s+h)-\theta(s)-h|^2ds\ll X h L^2\) for \(1\le h\ll X\), and \(O(XL^2)\) for \(0\le h<1\). Integrating the two one-sided increment formulas against the derivative of \(b\), or Minkowski, gives the smooth error \(E(s)=\sum_{p'}(\log p')b((p'-s)/H)-H\) squared norm \(O(X H L^2)\). Restricting \(s\) to the half-integers \(X-p\) poses no evaluation issue: over a displacement \(\le1\), \(E\) changes by \(O_b(L)\), since \(b'\) is bounded, the support contains \(O(H)\) integers and each contributes \(O(L/H)\) to the derivative. Hence the sum of squared errors over the complete half-integer mesh is \(O(X H L^2)\). Cauchy against \(\log p\) and \(\sum_{p\asymp X}\log^2p\ll X L\) costs \(O(X L^{3/2}/\sqrt H)=o(X)\) after the \(1/H\). The first choice of \(H\) avoids invoking the short-interval theorem at all.

For (2), put \(e(v)=e^{2\pi iv}\). Fourier inversion on \(H^{-1}b((p+p'-X)/H)\) writes (6) as an integral of products of two *ordinary additive prime exponential sums* at \(\beta-\alpha\), with scalar factor of modulus \(|\widehat b(2\pi H\beta)|\); here \(\widehat b(t)=\int b(v)e^{-itv}dv\). All other prime weights are fixed, smooth and compactly supported, so partial summation transfers ordinary partial-sum bounds. Fix small \(\xi>0\). The contribution of \(|\beta|>X^\xi/H\) is \(O_A(X^{-A})\) for arbitrary fixed \(A\), by rapid Fourier decay and trivial prime bounds. On the remaining interval, Dirichlet approximation gives a reduced \(a/q\) for \(\beta-\alpha\) with \(q\le M=\lfloor X/\sqrt H\rfloor\), error \(\le 1/(qM)\). Bad approximability gives
\[
 c_\alpha\le q^2|\alpha+a/q|\le q^2X^\xi/H+q/M,
\]
so \(q\gg_\alpha\sqrt H X^{-\xi/2}\); otherwise both terms are too small. The Vinogradov–Vaughan bound is \(O((X/\sqrt q+X^{4/5}+\sqrt{Xq})L^4)\), also for prime-only sums since powers cost \(O(\sqrt X L^2)\). With \(H=X^{7/10}\) this is \(O(X^{33/40+O(\xi)}L^4)\). The \(L^1\)-mass of \(\widehat b(2\pi H\beta)\) is \(O(1/H)\), proving (2) on taking \(\xi\) sufficiently small. The explicit arithmetic approximation error in (6) is smaller.

### Removal of every pair outside the stated shell

First use the polynomial cutoffs after (5), with \(O(X^{9/10}L^2)\) error, acceptable for both assertions. There are \(O(X^{12/5} L^2)\) ordered pairs left, each with \(X^2|c c'|=O(1)\). The phase in \(K\) is \(t\log(1+Hv/X)-\tau H v\), with derivative
\[
 (H/X)(t-\tau X-\tau Hv)/(1+Hv/X).
\]
For the parity shell (including the optional variant), outside its displayed total-ordinate window the magnitude is \(\gg X^{\epsilon/2}\) for the first choice of \(H\) and \(\gg X^\eta\) for the second, for all large \(X\). For the minor shell exterior it is \(\gg H^2/X=X^{2/5}\). In all cases the exterior has \(|t-\tau X|\gg H\), with margin over \(|\tau|H\); derivatives of order \(j\ge2\) are \(O_j(|t|(H/X)^j)\), bounded by constants times the first-derivative lower bound since \(|t|\le|t-\tau X|+\tau X\). Repeated nonstationary integration by parts thus costs \(O_A(X^{-A})\) per excluded pair. On the retained total-ordinate interval \(t\asymp X\). The derivative of the phase in \(J\) is \((\gamma-tu)/(u(1-u))\). If \(\gamma/t\notin[.29,.37]\), its magnitude on the support of \(w\) is \(\gg|\gamma|+|\gamma'|\gg X\) (also when ordinates have opposite signs); its higher derivatives are \(O_j(|\gamma|+|\gamma'|)\). The same integrations remove those pairs. The retained ratios enforce two *different* positive ordinates. This completes the shell estimates with multiplicities and no assumed pair-correlation law.

**References and scope.** The beta/gamma double-zero mechanism is classical: [Languasco–Zaccagnini, A Cesàro average of Goldbach numbers](https://arxiv.org/abs/1206.0251) already have a double sum with \(\Gamma(\rho)\Gamma(\rho')/\Gamma(\rho+\rho'+k+1)\); [Bhowmik–Ramaré–Schlage-Puchta](https://www.numdam.org/item/10.5802/jtnb.940.pdf) study oscillations and sum ordinates. [Granville (2007), pp.17–18, crediting Vaughan](https://dms.umontreal.ca/~andrew/PDF/GoldbachFinal.pdf) records a parity-projected Dirichlet double-zero formula for sums over multiples. Reflected prime interval bilinear forms and RH Selberg bounds are prior [Goldston](https://www.cambridge.org/core/services/aop-cambridge-core/content/view/F73ED944781B38B244B14ADD72AD7B24/S001708950000937Xa.pdf), [Chirre–Hagen](https://doi.org/10.1007/s40993-026-00767-6), and [Hubbard](https://hexagonmath.org/pdf/2610.00542v3). The latter is a Hexagon identifier, not an arXiv number. [Bhowmik–Grimmelt §4, Prop.4.1](https://arxiv.org/html/2607.27282v2#S4) state the classical exponential sum used in (2). [Althöfer–Chen–Perelli–Pintz](https://arxiv.org/abs/2611.09386) handle exceptional sets, and [Gou–Wang–Xu §3](https://arxiv.org/html/2611.18825v1#S3) use a fixed-target Dirichlet parity projection and an additional ratios conjecture. Neither mean-square control over target integers nor a proof of that ratios hypothesis is being used here. In particular (1) and (2) do not prove cancellation of the remaining shells or pointwise positivity of (3).

See also [Languasco–Zaccagnini’s short-interval Cesàro formulas](https://arxiv.org/abs/1606.00869) for prior target averaging; the specific shell statements (1)–(2) do not transfer their average to individual prime-pair counts.
