# A genuine piece of the ordinary minor arcs with subexponential small-radical denominators

Research note, 2026-11-24. Applies to the actual aggregate mixed statistic in [the G23 decomposition](SmallRadicalG23CoreBilateral.md), with its exact translated selector. Only the frequency region stated below is paid; the general remaining minor arcs are not.

## 1. Precise estimate and boundaries

Put \(L=\log P\), \(y=e^{L^\delta}\) for \(0<\delta<.1\), and \(R_y(m)=1_{P^-(m)>y}\). Let \(g(m)=\lambda(m)R_y(m)\) times the indicator of any fixed interior interval at scale \(P\), or a fixed smooth weight of bounded variation on that scale. Let \(f(n)\) be any function supported on \(n\asymp P\), with \(|f|\le L^C\) for fixed \(C\). In particular it can include the true source \(G_{23}\) short-divisor marker, exact translated selector, arithmetic rough mask, and actual sign. Define Fourier sums \(S_f(t)=\sum_n f(n)e(nt)\), \(S_g(t)=\sum_m g(m)e(mt)\).

Fix \(B_0\ge0\), \(0<\theta<4/7\), and choose \(\alpha\) with \(\theta<\alpha<4/7\). Let \(Q_*=\exp(L^\theta)\). The frequency set \(\mathfrak S\) is the union of
\[
t=\frac a q+\beta,\quad q\le Q_*,\quad (a,q)=1,\quad
\operatorname{rad}(q)\le L^{B_0},\quad |\beta|P\le Q_* .
\tag{1}
\]
For sufficiently large \(P\),
\[
\left|\int_{\mathfrak S} S_f(t)S_g(t)e(-Pt)\,dt\right|
\le \int_{\mathfrak S}|S_fS_g|\,dt
\ll P e^{-c L^\alpha}.
\tag{2}
\]
The same holds for any subregion of this union, in particular the portion outside the previous ordinary polylog major arcs. The assumptions concern the **actual denominator \(q\)** in (1), not the radical of \(P\) alone. No claim here covers large-radical rational denominators, polynomial-sized denominators, or the complementary generic minor arcs.

## 2. Primitive twisted Liouville at subexponential Perron height

Set \(U=L^\alpha,\ T=e^U\). For any primitive **nonprincipal** \(\psi\) inducing a character modulo an allowed \(q\), its conductor \(r\mid q\) satisfies \(\operatorname{rad}(r)\le L^{B_0}\) and
\[
\log(r(|t|+3))=O(U)\qquad(|t|\le2T+1).
\]
By [Iwaniec, On zeros of Dirichlet's L series, Theorems 1 and 2](https://gdz.sub.uni-goettingen.de/download/pdf/PPN356556735_0023/PPN356556735_0023.pdf#page=97), the growth and zero-free inputs used in [the small-radical projection proof](small_radical_projection/Proof.md) hold here with its size parameter \(L\) replaced by \(U\). More precisely the first theorem gives \(\log|L(s,\psi)|\ll U^{1/4}+\log\operatorname{rad}(r)\ll U^{1/4}\) whenever the real part is within \(O(U^{-1/2}(\log U)^{-2})\) of 1 throughout those heights. The second gives a zero-free strip of width \(\gg U^{-3/4}(\log U)^{-3/4}\), except for a possible real zero of a real character. Every primitive real character here has conductor \(\le4\operatorname{rad}(r)\le4L^{B_0}\); Siegel's ineffective lower bound, with a sufficiently small fixed exponent, keeps any such real zero at distance \(\gg L^{-\alpha/4}\) from 1. In particular it is excluded from the narrower working strip. This does not assume effective Siegel or any exceptional control for the large-radical conductors outside (1).

For detail identical to the reciprocal argument in that proof, put
\[
u=c_0 U^{-1/2}(1+\log U)^{-2},\qquad
\Theta=C_0 U^{3/4}(1+\log U)^2,\qquad
\eta=\Theta^{-1}.
\]
Use disks of radius \(3u\) centered at \(1+2u+it\) and the local logarithmic derivative estimate with interior radii \(2.2u,2.9u\). The center Euler product gives \(|L(1+2u+it,\psi)|\gg u\), and the first Iwaniec bound gives a local derivative approximation by zeros with error \(O(u^{-1}(U^{1/4}+\log(1/u)))=O(\Theta)\). All zeros in the local disk lie at real part \(\le1-8\eta\) for \(C_0\) large. At \(s_*=1+\eta+it\), \(L'/L(s_*,\psi)=O(\Theta)\) by the Euler product; hence the sum of nonnegative real parts of the local zero terms there is \(O(\Theta)\). For \(s=\sigma+it,\ 1-\eta/2\le\sigma\le1+\eta\), 
\[
\left|\frac1{s-\rho}-\frac1{s_*-\rho}\right|
\ll\frac{\eta}{|s_*-\rho|^2}
\ll\operatorname{Re}\frac1{s_*-\rho}
\]
for each retained zero. This proves \(L'/L=O(\Theta)\) in that interval. Horizontal integration from \(s_*\), where \(1/L=O(\Theta)\) by Euler product, gives \(1/L=O(\Theta)\) there. The same bound to its right is direct.

The exact Dirichlet series of the twisted Liouville coefficient is \(L(2s,\psi^2)/L(s,\psi)\); the numerator is bounded absolutely on the whole contour since \(2\operatorname{Re}s>3/2\). For a half-integer \(X\) with \(P^\epsilon\le X\le 2P\) and any fixed \(\epsilon>0\), use truncated Perron at \(1+1/\log X\) with height \(T\) and its usual bounded-coefficient error \(O(X(\log X)^2/T)\) (integer endpoints move to the neighboring half-integer). Shift to \(1-\eta/2\). The vertical error is \(\ll X\Theta\log T\,e^{-\eta\log X/2}\), and each horizontal is \(O(X\Theta/T)\). Crucially
\[
\eta\log X\gg_\epsilon L^{1-3\alpha/4}(1+\log L)^{-2}\gg U
\]
because \(\alpha<4/7\); the rate \(e^{-cU}\) is not asserted at the endpoint \(4/7\). We have proved uniformly \(\sum_{m\le X}\lambda(m)\psi(m)\ll X e^{-cU}\). For the primitive principal character, the classical Vinogradov--Korobov Mertens bound \(\sum_{m\le X}\mu(m)\ll X\exp(-c(\log X)^{3/5}(\log\log X)^{-1/5})\) gives the same via \(\lambda=\mu*1_{\rm squares}\), splitting square divisors at \(X^{1/2}\). This is valid since \(\alpha<4/7<3/5\). No roughness reduction via squareful absolute tails is used in this lemma.

## 3. The true rough twist and actual frequencies

Every prime of \(q\) is below \(y\) by (1), so characters modulo \(q\) agree with their inducing primitive characters on the exact \(R_y\) support. For the latter twist, use the exact finite Euler convolution
\[
\lambda(n)R_y(n)=\sum_{\substack{v\mid n\\v\ {\rm squarefree},\ P^+(v)\le y}}\lambda(n/v).
\]
Twist both sides by the primitive character. For \(n\le X\asymp P\), the \(v\le\sqrt X\) terms have true inner endpoint \(X/v\ge \sqrt X\) and are bounded by the previous \(\lambda\psi\) estimate times \(\sum_v1/v\ll\log y\). For larger \(v\), using \(s=1/\log y\), the actual reciprocal tail is at most 
\[
X^{-s/2}\prod_{\ell\le y}(1+\ell^{s-1})
\ll e^{-c L^{1-\delta}}L^{O(1)}
\]
by Rankin. This is far smaller than \(e^{-cU}\). Thus all prefixes at \(X\asymp P\), and differences giving actual fixed-interior endpoints, are \(O(Pe^{-cU})\) for the true \(\lambda R_y\) twist. Keeping the imprimitive character by equality on rough support avoids artificial Euler factors at primes in \(q/r\).

On the unit group mod \(q\), expand \(e(a n/q)\) in multiplicative characters with normalized Fourier coefficients. Their squared sum is \(1\) by Parseval on that group, so their absolute sum is \(\le\sqrt{\varphi(q)}\le Q_*^{1/2}\). This is the complete Gauss cost, including imprimitive characters. The slow phase \(e(\beta n)\) and the interval weight spend at most \(O(1+|\beta|P)=O(Q_*)\) by partial summation. Since \(\log Q_*=L^\theta=o(U)\), the aggregate bound is still \(|S_g(a/q+\beta)|\ll P e^{-cU}\), with a decreased \(c\).

The arcs in (1) have total measure at most \(O(Q_*^3/P)\) even if one counts every potential reduced rational with \(q\le Q_*\); in fact they are disjoint for sufficiently large \(P\). Since \(\sup |S_f|\ll P L^C\), the same \(L^\theta=o(U)\) absorbs their entire measure loss and gives (2). This is an absolute bound on a real region of the ordinary minor integral of the marked statistic. It does not need the true translated mark to factor through any Fourier or one-variable profile.
