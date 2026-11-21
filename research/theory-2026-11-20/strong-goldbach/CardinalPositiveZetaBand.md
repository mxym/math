# One compact positive band of zeta ordinates preserves an individual even target

Let \(N\) be even, \(X=N-1/2,\ \delta=1/X\), and fix \(0\le w\in C_c^\infty((.31,.35))\), \(w\not\equiv0\). Write
\[
 R_w(N)=\sum_{p+p'=N}(\log p)(\log p')w(p/X)
\]
for genuine ordered primes. We give a compact positive-height zeta-pair expression for this **individual** count with absolute \(o(X)\) error under zeta RH. Under Dirichlet GRH the disjoint rational cores inside the very same band carry the full expected positive main term. No estimate for the aggregate complement, and hence no Goldbach conclusion, follows. The error is suitable for a macroscopic one-sided test, not the detection of one microscopic representation by numerical rounding.

Fix \(0<\eta<\pi/4\) and let \(I=(\pi/2-\eta,3\pi/2+\eta)\). Construct \(0\le G\in C_c^\infty(I)\) with \(\sum_{j\in\mathbb Z}G(t+j\pi)=2\): periodize a nonnegative bump in \(I\) positive on the closed interval \([\pi/2,3\pi/2]\), divide it by its strictly positive smooth periodization, and multiply by 2. It need not be even. The length can approach \(\pi\), the sampling period; an interval of length below \(\pi\) cannot cover the line after such translations. This last sharpness statement applies to this scalar cardinal construction only.

For \(u\) in a fixed compact neighborhood of the support of \(w\) inside \((.29,.37)\), use
\[
 A_u(t)=\frac{4\sin(tu/2)\sin(t(1-u)/2)}{t^2},\qquad
 P_u(t)=G(t)/A_u(t)\quad(t\in I),
\]
and extend \(P_u\) by zero elsewhere. The aperture denominator has no zero on the closure of \(I\) in this \(u\)-range. All derivatives in either variable are uniformly bounded. Define the inverse transform \(b_u\) by
\[
 P_u(t)=\int_{\mathbb R} b_u(s)e^{its}ds,\qquad
 b_u(s)=\frac1{2\pi}\int P_u(t)e^{-its}dt.
\]
These functions and all needed \(u\)-derivatives are uniformly Schwartz in \(s\); they can be complex. Whenever an extension in \(u\) is useful, first multiply by a fixed smooth bump equal to 1 on the support of \(w\).

For a zeta-zero pair \(\rho=1/2+i\gamma,\ \rho'=1/2+i\gamma'\), put \(t=\gamma+\gamma'\), \(c(\rho)=((1+\delta)^\rho-1)/\rho\), and
\[
 B(\rho,\rho')=X^{2+it}c(\rho)c(\rho')
    \int w(u)u^\rho(1-u)^{\rho'}P_u(t/X)\,du .
\]
Let \(\mathcal B_X\) denote the ordered pairs (with multiplicities) for which \(t/X\in I,\ .29\le\gamma/t\le.37\). In particular **both ordinates are positive, distinct, and bounded above and below by positive constants times \(X\)**. There is no diagonal or pole to add. Our first result, on zeta RH, is
\[
 R_w(N)=\sum_{\mathcal B_X}B(\rho,\rho')+o(X).                              \tag{1}
\]
For the second define \(H=X^{2/5}, Q=\lfloor X^{1/100}\rfloor\), and a real even \(F\in C_c^\infty((-2,2))\), \(0\le F\le1\), equal to 1 on \([-1,1]\). Use all reduced rationals \(r\in[-1,1]\) with denominator \(q\le Q\), **as well as** denominators \(2d\) for all odd \(d\le Q\) (duplicates included only once). Put \(M_X(t)=\sum_r F(H(t/X-2\pi r))\). The centers are separated by at least \(2\pi/(2Q)^2>4/H\), so the mask is a true disjoint smooth selection, equal to 1 on each core and 0 outside the expanded union. Then on Dirichlet GRH, uniformly in even \(N\),
\[
 \sum_{\mathcal B_X}B(\rho,\rho')M_X(t)
   =X\mathfrak S(N)\int w(u)du+o(X),                                        \tag{2}
\]
\[
 R_w(N)=X\mathfrak S(N)\int w(u)du+
     \sum_{\mathcal B_X}B(\rho,\rho')\,[1-M_X(t)]+o(X).                      \tag{3}
\]
All these asymptotics concern the complex sums; the indicated main terms are real. The rightmost sum in (3) lives entirely inside one fixed positive band and off the cores of rational frequencies. It includes the transition edges. A target with no prime pair would force its real part to cancel the whole positive main term up to \(o(X)\).

## 1. Exact cardinal sampling on the actual prime cells

Use the reflected subunit increments \(U_\delta(y)=\psi((1+\delta)y)-\psi(y)\), keeping \(\delta=1/X\) fixed. In the variable \(s=X\log(Y/X)\) integrate
\[
 D=\int_{\mathbb R}\sigma(s/X^\xi)e^{-2s/X}
       \int w(u)b_u(s)U_\delta(y)U_\delta(Y-y)\,dy\,ds,\quad
 Y=Xe^{s/X},\quad u=y/Y,\quad \xi=1/200,                                    \tag{4}
\]
where \(\sigma\in C_c^\infty((-2,2))\) equals 1 on \([-1,1]\). The truncation avoids any exponential tails at unbounded log delays.

On the arithmetic side set \(z=Y-y\), \(dy\,ds= (X/Y)dy\,dz\). Replace \(s\) by \(Y-X\) inside \(b_u\), \(u\) there and in \(w\) by \(p/X\), and the exterior Jacobian/exponential by 1. In retained cells \(|Y-X|\ll X^\xi,\ |s-(Y-X)|\ll X^{2\xi-1},\ |u-p/X|\ll X^{\xi-1}\). Absolute derivatives of all weighted test functions are uniformly bounded; all cell lengths are less than 1 and there are \(O(X^{1+\xi})\) candidate integer pairs in this region with individual log weight \(O((\log X)^2)\). The total replacement error is \(O(X^{3\xi}(\log X)^2)=o(X)\). The cutoff edges can be dropped at arbitrary power saving by the uniform Schwartz tails. For \(Y=X+O(X^\xi)\) at most two integer totals are possible in \((Y,(1+\delta)Y]\); hence pairs involving any proper prime power cost \(O(\sqrt X(\log X)^2)\) after integration, using \(\sup_u |b_u(s)|\ll(1+|s|)^{-2}\). This is uniform also for the signed weight.

Write \(u_p=p/X,\ k=p+p'-N\). The exact cells are \(y=p-a,\ z=p'-a'\), \(0\le a\le p/(X+1),\ 0\le a'\le p'/(X+1)\) up to null endpoints. These lengths differ from \(u_p,1-u_p\) by \(O(X^{\xi-1})\) on the retained support. Extending their endpoints to the latter lengths costs \(O(X^{2\xi}(\log X)^2)\) in total. Terms outside \(|k|\ll X^\xi\) can be reinstated in the resulting convolution with \(O_A(X^{-A})\) cost by uniform Schwartz decay; the two primes may be restricted to fixed compact multiples of \(X\) containing the whole \(k=0\) range. The cell value is now
\[
 \int_0^{u_p}\int_0^{1-u_p} b_{u_p}(k+1/2-a-a')\,da'\,da
    =\frac{1}{2\pi}\int G(t)e^{-ikt}dt.                                     \tag{5}
\]
The two interval Fourier integrals contribute exactly \(e^{it/2}A_{u_p}(t)\), canceling the center phase. Both primes on this support are odd, so \(k\) is even. For \(k=2j\), periodizing \(G\) modulo \(\pi\) in (5) gives \(\mathbf1_{j=0}\). This shows \(D=R_w(N)+o(X)\). In particular it has not been replaced by an average over surviving neighboring even sums.

## 2. Single positive-height band, with quantitative exchanges

[The reflected shell note](ReflectedZetaMajorMinorShells.md), (4)–(5), proves the uniform local \(L^2(dy)\) explicit formula and shows that cutting each zero expansion to \(X^{4/5}\le|\gamma|\le X^{6/5}\) costs \(O(X^{9/10}(\log X)^2)\) in the reflected product. It applies in (4): at each \(s\) the weight is bounded by \(C(1+|s|)^{-2}\) and the two \(y\)-ranges remain in compact positive multiples below \(.8X\). Cauchy followed by absolute integration over \(s\) gives this same cutoff error. The single-zero terms are \(O(\sqrt X)\) after integration because all \(u\)-derivatives of \(w(u)b_u(s)\) decay uniformly in \(s\); nonstationary integration in \(u\) gives arbitrary inverse powers of the single ordinate. The pole/pole contributes \(O(1)\): its integral is \(X\int w(u)u(1-u)\int e^{s/X}\sigma(s/X^\xi)b_u(s)\,ds\,du\); \(\int b_u=P_u(0)=0\), and replacing \(e^{s/X}\) by 1 costs \(O(1/X)\) using the first absolute moment. Smooth trivial-zero errors are smaller.

In the cutoff pair terms \(e^{-2s/X}\) cancels \((Y/X)^2\) exactly, leaving \(e^{its/X}\). The integral in \(s\) equals \(P_u(t/X)+O_A(X^{-A})\) uniformly in \(t,u\), as do its \(u\)-derivatives, by the discarded Schwartz tail. There are \(O(X^{12/5}\log^2 X)\) ordered cutoff pairs; \(X^2|c(\rho)c(\rho')|\ll1\). Thus the exact compact frequency multiplier can be used at \(o(1)\) cost. It vanishes unless \(t/X\in I\), so \(t\asymp X\) is positive. Off the displayed ratio range the derivative \((\gamma-tu)/(u(1-u))\) of the \(u\)-phase has magnitude \(\gg|\gamma|+|\gamma'|\gg X\); higher derivatives are \(O_j(|\gamma|+|\gamma'|)\). All derivatives of the amplitude \(w(u)P_u(t/X)\) are uniformly bounded. Integration by parts removes every wrong-sign/wrong-ratio pair at arbitrary power saving. All remaining pairs automatically lie strictly inside the original polynomial cuts for large \(X\). This proves (1).

## 3. Why the existing rational-shell estimate transfers to this different aperture

Do **not** simply freeze \(P_u(t/X)\) at \(P_u(2\pi r)\) pointwise and sum the differences absolutely over zeros. Instead use a physical-delay convolution. In the sign convention above let \(f\) be the inverse Schwartz transform of \(F\). The inverse transform (dual variable \(\lambda=t/X\)) of
\[
 P_u(\lambda)F(H(\lambda-\tau)),\quad \tau=2\pi r,
\]
is \(b_u * [H^{-1}f(\cdot/H)e^{-i\tau\cdot}]\). Uniformly in \(u,|\tau|\le2\pi\), it equals
\[
 P_u(\tau)H^{-1}f(s/H)e^{-i\tau s}
       +O_A(H^{-2}(1+|s|/H)^{-A}).                                         \tag{6}
\]
Factor out the modulation, use \(\int b_u(v)e^{i\tau v}dv=P_u(\tau)\), and apply the mean value bound to \(f((s-v)/H)-f(s/H)\) with the uniform Schwartz moments of \(b_u\); the same bound holds after any fixed number of \(u\)-derivatives. Truncate the physical delays at \(|s|\le2HX^\xi\) smoothly as before. Every discarded Fourier-transform tail is \(O_A(X^{-A})\), and estimated against only polynomially many cutoff zero pairs. In this retained range \(Y=Xe^{s/X}=X+O(HX^\xi)\), and the unsigned primitive reflected *arithmetic* integral with a bounded weight is \(O(XL^2)\), \(L=\log X\). Thus the error term of (6) costs \(O(XL^2/H)\) in that integral per center by absolute integration; the corresponding pole term costs \(O(X/H)\), the mixed/zero cutoff errors are \(O(X^{9/10}L^2)\) as before, since the integrated sup norms are uniformly bounded. This justifies freezing the center dependence in physical norm before evaluating the selected pairs.

Now use [the flat-top aggregate proof](FlatTopZetaSingularSeries.md), (5)–(7), at every center with the uniformly smooth weight \(w(u)P_u(\tau)\), the same \(H,Q,\xi\) (denominators up to \(2Q\) only change constants), and \(|r|\le1\). Its per-center errors \(O(X^{9/10}L^2+X^{.87}+X\sqrt{q/H}L^3+\sqrt{qX}L^2)\) and the extra \(O(XL^2/H)\) sum to \(o(X)\) over \(O(Q^2)\) centers. For \(\tau=0\) the frozen weight vanishes identically; for every other center there is no pole at the retained accuracy. The paired main from the cited formula has factors \(e(rN)\mu(q)^2/\varphi(q)^2\) and \(\int w(u)P_u(\tau)A_u(\tau)\,du=G(\tau)\int w\). This remains valid if \(\tau\) lies outside the support of \(G\): use the zero weight and the physical error in (6), even for a shell straddling its edge.

Finally organize the main sum at **finite** \(Q\), not by an invalid absolutely convergent sum over all rational numerators. For each odd squarefree \(d\le Q\) and each unit \(a\bmod d\), the two values \(a/d,\ a/d+1/2\bmod1\) run over the corresponding reduced fractions of denominators \(d,2d\). Their \(\mu^2/\varphi^2\) weights agree; their phases \(e(rN)\) also agree because \(N\) is even. Including integer translates inside \([-1,1]\) includes every potentially nonzero \(G(2\pi r)\), since \(I\subset(0,2\pi)\). The complete sum of the paired \(G\) values is exactly 2 by periodization. Cases of nonsquarefree denominator give zero main even though they are included in the mask. The total main therefore uses exactly
\[
 2\sum_{\substack{d\le Q\\d\ {\rm odd}}}\frac{\mu(d)^2}{\varphi(d)^2}c_d(N)
   =\mathfrak S(N)+o(1)
\]
uniformly for even \(N\). Indeed \(c_{2d}(N)=c_d(N)\), and the absolute *denominator-series* tail after numerator summation is \(O_\epsilon(X^\epsilon Q^{-1+\epsilon})\) as proved in the linked note. All finite aliases, including the \(d=1,2d=2\) pair, are covered. This proves (2) and (3).

**Interpretation and antecedents.** The sampling identity is elementary Fourier cardinal interpolation for the grid of possible even sums, with an explicit correction for the two subunit interval apertures. The additive Hardy–Littlewood singular series and the classical double-zeta-zero mechanism are not new. For prior primary formulas, reflected-interval estimates, and their distinct scopes see the citations in the two linked companions, especially Languasco–Zaccagnini's Cesàro formula, Granville/Vaughan's averaged Dirichlet parity formula, and Chirre–Hagen's reflected short intervals. No usual local pair-correlation theorem evaluates the residual in (3): the two positive heights are macroscopically separated and their signed phase matters.
