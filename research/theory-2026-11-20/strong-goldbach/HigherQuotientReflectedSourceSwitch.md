# Reflected-source switch for a signed marked higher quotient

This is a fixed-even-target signed evaluation of the **original** reflected coefficient on a genuinely higher-than-square-root quotient. Its independent SW variable is a genuine prime on the reflected **source**, not a factor of the modulus. A Selberg square keeps the resulting signed mean at the same normalization as the prime-quotient row and equals one on every genuine prime quotient. It does **not** force that quotient to be prime. The artificial composite part has a genuine additional positive chamber, and no Goldbach bound is claimed.

## Statement

Let \(N=2x\), \(L=\log x\), \(H=\exp(L^\sigma)\), with \(0<\sigma<1\) fixed, and keep the original
\[
 U=\sqrt x/H^4,\quad V=H,\quad Q_0=\sqrt x/H^2,\qquad
 C(m)=\sum_{d\ell\mid m,\,d>U,\,\ell>V,\,d\ell>Q_0}\mu(d)\Lambda(\ell).
\]
Write \(n=N-m\in(x/2,x]\), \(m\in[x,3x/2)\). Use true prime \(s,a,Q\) with exponents respectively in
\[
 (.138,.139),\qquad (.068,.069),\qquad (.297,.298),
\]
and let \(v=saQ\), \((v,N)=1\). Keep \((m,N)=1\), and write \(b=n/v\) when \(v\mid n\). Thus \(x^{.503}<v<x^{.506}\), \(b\asymp x/v\), \(b<B=x^{.501}<ab\), and \(Q<B\) automatically for large \(x\). If \(b\) is prime then this is literally an original \(\mathcal Q_1\) row with \(q=aQb\) and \(b\) the unique marked prime. No prime condition is imposed on \(b\) in the theorem.

Let \(E=(x^{.311},x^{.321})\), \(\omega_E(m)=\#\{p\in E:p\mid m,\ p\ \mathrm{prime}\}\), \(h=\log(.321/.311)\), and \(W_s(q)=(1-t)(1-2t)^2,\ t=\log s/\log(sq)\) as before. Let \(R=x^{1/40}\), and define the ordinary optimal Selberg square
\[
 {\cal R}(b)=\Big(\sum_{d\mid b}\lambda_d\Big)^2,\qquad
 G_R=\sum_{d<R,\ (d,N)=1}\mu(d)^2\prod_{p\mid d}\frac1{p-2}.
\]
The real \(\lambda_d\) are supported on squarefree \(d<R\) coprime to \(N\), with \(\lambda_1=1\), and minimize the quadratic form for \(g(p)=1/(p-1)\) on \(p\nmid N\). In particular \({\cal R}(b)=1\) when \(b\) is prime, as \(b\gg x^{.494}>R\).

Let
\[
 {\cal V}=\sum_{s,a,Q,\,(v,N)=1}\frac1{\phi(v)}
       \int_x^{3x/2} W_s((N-y)/s)\,dy.
\]
For \(j=1,2,3\), with all sums over the actual physical tuples just specified, one has for every fixed \(A>0\)
\[
 \sum_{s,a,Q;\ m\equiv N\ (v)} W_s(n/s)\,{\cal R}((N-m)/v)\, C(m)\binom{\omega_E(m)}j
 = (j-1)\frac{{\cal V}}{G_R}
    \sum_{\substack{p_1<\cdots<p_j\in E\\ \mathrm{prime},\\ (p_1\cdots p_j,N)=1}}
          \frac1{p_1\cdots p_j} +O_A(xL^{-A}).                                      \tag{1}
\]
In particular, replacing the binomial by \(1_{\omega_E>0}\) gives
\[
 \big(-h^2/2+h^3/3+o(1)\big){\cal V}/G_R.
                                                                            \tag{2}
\]
Replacing it by \(1_{\omega_E=1}\) gives \((-h^2+h^3+o(1)){\cal V}/G_R\). Both signs are strictly negative at **every** sufficiently large even \(N\). The normalization is
\[
 {\cal V}/G_R \sim 40 K M_N,\qquad
 K=\Big(\int_{.138}^{.139}(1-t)(1-2t)^2\,\frac{dt}{t}\Big)
   \log(.069/.068)\log(.298/.297)>0,\qquad M_N=\mathfrak S(N)x/(2L).
                                                                            \tag{3}
\]
The same proof with \({\cal R}=1\) simply omits \(1/G_R\) from (1). In that version the one-mark mean is again zero, but the two/three-mark means have a different scale.

## 1. Exact progression transfer on the reflected source

Expand \({\cal R}\) as \(\sum_{w\mid b}\xi_w\), where \(w=[d_1,d_2]<R^2=x^{.05}\) and \(\xi_w=\sum_{[d_1,d_2]=w}\lambda_{d_1}\lambda_{d_2}\) is divisor- and log-power bounded. The actual reduced progression is \(m\equiv N\pmod{k}\), \(k=vw\). All three modulus slots are independent after dyadic and fine relative subdivisions:
\[
                   q_1=Q,\qquad q_2=sw,\qquad q_3=a .
\]
Indeed \(s\) is the unique prime divisor of \(sw\) above \(x^{.05}\) and the other bands do not intersect. Hence each coefficient of \(q_2\) depends only on \(q_2\); in particular it does not depend on the reflected-source prime. Every modulus prime is below \(x^{.298}\), so no marked prime \(p\in E\) can divide it.

Drop all rows with any \(p^2\mid m,\ p\in E\). This costs \(O(x^{.689+o(1)})\) unweighted plus \(O(x^{.321+o(1)})\) for floors. All weights, including the summed factorization multiplicity at the actual \(N-m\), are \(x^{o(1)}\) on these rows. The same deletion works in the principal terms by the harmonic bound on the sum of the modulus coefficients divided by \(\phi(k)\). For \(j\) marks, use ordered distinct tuples divided by \(j!\), and write \(m=p u\) with the first marked prime \(p\in E\); the other \(j-1\) actual prime marks are encoded in the coefficient of \(u\). Drop \(p\mid u\) (already in the square deletion); the possible coincidence of \(p\) with any mark encoded in \(u\) is therefore treated, not inserted as an independent constraint.

For \(p\nmid u\), expand \(C(pu)\) in exactly three terms: \(p\) outside \(d\ell\); \(p\mid d\), when \(d=p d'\) contributes \(-\mu(d')\); and \(\ell=p\), when the factor is \(\log p\) and \(d\mid u\). The last case has \(p>V\) and \(pd>Q_0\) automatically if \(d>U\). In the middle case the only \(p\)-dependent divisor cutoffs are \(p d'>U\) and \(p d'\ell>Q_0\). Freeze the location of \(p\) on relative \(L^{-F}\) intervals for these comparisons only, retaining its actual prime label. Any misclassification certifies an actual divisor of \(m\) in a relative \(O(L^{-F})\) strip about \(U\) or \(Q_0\). The count of integers \(m\asymp x\) in such a strip about \(T\) is
\[
 O\Big(\sum_{d=T+O(TL^{-F})}x/d\Big)=O(xL^{-F}+x/T).
\]
A sum over the finite set of cuts does not change this bound. Global moments of \(\tau(m)\) and \(\tau(N-m)\) and Cauchy bound all log-power weighted errors by \(O_A(xL^{-A})\), for \(F\) large. This applies both to the actual sum and to the principal, whose total modulus weight divided by \(\phi(k)\) is log-bounded. The same physical interval subdivision allows product gate \(p u\in[x,3x/2)\) to be replaced by independent rectangles: only an \(O(x L^{-F})\) strip at a central endpoint can be lost. Freeze \(s\) and \(m\) similarly when separating \(W_s((N-m)/s)\); this smooth weight has log-bounded variation and error \(O(L^{-F})\) per tuple. There are only log-power many subdivisions; all lost sums can equivalently be bounded before subdividing using the indicated global divisor moments. Logs of a true \(p\) in the third term are harmless bounded-SW factors after division by \(O(L)\) (partial summation of the SW prefixes). The cut \((pu,N)=1\) is independent on both factors.

Now apply [Lichtman, Proposition 5.2](https://arxiv.org/html/2309.08522#S5) to the source \(p\times u\), retaining the actual residue \(N=2x<x^{1+\epsilon}\). The first sequence is an ordinary prime interval coprime to \(N\) (uniform SW with the auxiliary divisor mask, by his Definition 2.1 and deleting the \(O(L)\) primes dividing \(N\)); all its prime factors exceed the required \(z_0\). The \(u\) coefficient is an arbitrary divisor/log bounded function independent of \(p\) after the preceding cuts, and \(u\asymp x/p\) in each product box. With \(\theta=7/32\), the strict limiting upper exponents in the four rails are bounded by
\[
\begin{array}{c|c}
Q_1/X_p&.298-.311=-.013\\
X_p^2Q_2Q_3^2 &2(.321)+.189+2(.069)=.969\\
|N|^\theta X_p Q_1Q_2^5Q_3^2 & 7/32+.321+.298+5(.189)+2(.069)=1.92075\\
(X_pQ_3/Q_2)^{2\theta}X_pQ_1Q_2^5Q_3^2
 & (7/16)(.321+.069-.138)+.321+.298+5(.189)+2(.069)=1.81225 .
\end{array}
\]
Here \(X_p\) denotes the length scale of the first factor, \(q_2=sw\) ranges through exponent \([.138,.189]\), and fixed dyad constants are absorbed by any small fixed slack. Every coefficient is supported on moduli coprime to \(N\).

For the printed 1-boundedness requirement clip the \(u\) and modulus coefficients at sufficiently high powers of \(L\), and then divide out the log powers. The true exceptional contribution is estimated by Cauchy and arbitrary fixed divisor moments: an exceptional \(u\) forces \(\tau(m)\) to exceed a high log power, an exceptional modulus slot forces \(\tau(N-m)\) to exceed one, and the remaining tuple multiplicities are bounded by fixed powers of these two divisor functions. For the principal, use the same moments on \(m\) with the harmonic sum \(\sum_k \tau(k)^c/\phi(k)\ll L^{O_c(1)}\); a clipped modulus coefficient is paid by the harmonic divisor moment of one additional arbitrarily high order. Removing \(p\mid u\) and restoring both frozen cutoffs on both sides of the proposition costs the same physical strip/prime-square estimates. This proves, after summing all boxes, replacement of the reduced progression indicator by \(1_{(m,k)=1}/\phi(k)\) with error \(O_A(xL^{-A})\) in the entire \(j\)-marked weighted sum. This uses neither a progression theorem for standalone \(\Lambda(m)\) with \(k>\sqrt x\), nor a theorem with \(b\) restricted to primes.

## 2. Conditional principal mean of the original coefficient

Fix distinct allowed marks \(p_1,\ldots,p_j\), \(k=vw\), \(F=p_1\cdots p_j\), and put \(m=Fu_0\), \((u_0,D)=1\), \(D=NkF\). Both \((k,N)=1\) and \((k,F)=1\) hold, and primes in \(F\) dividing \(N\) were already discarded. The principal calculation is an ordinary **unprogressioned** one:
\[
 \sum_{u_0\in I/F,\,(u_0,D)=1} W_s((N-Fu_0)/s) C(Fu_0)
 =(j-1)F^{-1}\int_I W_s((N-y)/s)\,dy
   +O_A((x/F)L^{-A})                                                     \tag{4}
\]
for any subinterval \(I\subseteq[x,3x/2)\). There is no assumption that the integer \(u_0\) is rough, squarefree or prime. The marks are at most simple by the coprime mask. The usual exact reassembly is \(C=\Lambda-T_1+T_2-T_3\), where
\[
\begin{aligned}
 T_1(m)&=\sum_{d\mid m,d\le U}\mu(d)\log(m/d),\\
 T_2(m)&=\sum_{d\ell\mid m,d\le U,\ell\le V}\mu(d)\Lambda(\ell),\\
 T_3(m)&=\sum_{d\ell\mid m,d>U,\ell>V,d\ell\le Q_0}\mu(d)\Lambda(\ell).
\end{aligned}
\]
The \(\Lambda(m)\) term is exactly zero: \(m\) has the specified polynomial mark only to the first power and \(m\gg p_1\). Two distinct marks cannot fit into any of the short divisor arguments since \((.311+.311)>.5\); in the two correction terms no \(\ell\) itself can carry the mark (in \(T_2\) it exceeds \(V\), and in \(T_3\) a \(d>U\) together with it would exceed \(Q_0\)). The endpoint comparisons, uniform for all actual \(m\), are:
\[
\begin{array}{c|c|c}
j&u_0\asymp x/F&\text{which short }d'\text{ bounds exhaust its divisor list}\\
1&x^{.679}\text{ to }O(x^{.689})&\text{none}\\
2&x^{.358}\text{ to }O(x^{.378})&U\text{ (no mark), not }U/p_i\\
3&x^{.037}\text{ to }O(x^{.067})&U\text{ and all }U/p_i.
\end{array}
\]

Specifically in \(T_1\) choose no mark in \(d\), or one mark \(p_i\) with sign minus. For an exhausted divisor list use \(\sum_{d'\mid u_0}\mu(d')\log(Yu_0/d')=\Lambda(u_0)\), as \(u_0>1\); its actual unrestricted weighted mean with \((u_0,D)=1\) is \(1\) by PNT at a polynomially long scale. Omitting primes dividing \(D\) from that mean costs \(O(L^3)\), including powers. For each remaining short list (bound \(U\) or \(U/p_i\)), write \(u_0=d'h\). For \((d',D)=1\), the density is \(\phi(D)/(Dd')\), with \(O(\tau(D))\) floor error per \(d'\); otherwise it is zero. The two uniform finite coprime Möbius harmonic moments
\[
 \sum_{d'\le T,(d',D)=1}\frac{\mu(d')}{d'}=O_A(L^{-A}),\qquad
 \sum_{d'\le T,(d',D)=1}\frac{\mu(d')}{d'}\log(T/d')
       =\frac{D}{\phi(D)}+O_A(L^{-A})
\]
apply at these polynomial \(T\) and mask \(D\ll x^3\). Indeed, \(\mu(d')1_{(d',D)=1}\) is the convolution of \(\mu\) with \(1_{r\mid D^\infty}\). The ordinary unrestricted moments are \(0,1\) respectively with arbitrary log reserve by the prime number theorem for \(\mu\); for the logarithmic moment the limiting value \(1\) follows from \(\zeta(1+z)^{-1}/z\to1\) and partial summation. In the convolution restrict \(r\le\sqrt T\) to invoke these errors uniformly at \(T/r\), with \(\sum_{r\mid D^\infty}1/r=D/\phi(D)\ll L^{O(1)}\). The remaining harmonic mass is at most \(T^{-1/8}\prod_{p\mid D}(1-p^{-3/4})^{-1}=T^{-1/8}x^{o(1)}\) by splitting the primes at \(L^2\); all weighted tails remain power-small. Thus each non-exhausted list also has mean \(1\), before its indicated sign. The factor \(\log(Yu_0/T)=O(L)\) is harmless. The coefficient \(T_1\) therefore has mean \(1-j\).

For \(T_2\), any exhausted list \(\sum_{d'\mid u_0/\ell}\mu(d')\) is zero, since \(u_0>\ell\) for \(\ell\le V\). A non-exhausted list has principal zero using the first harmonic moment at \(U\) or \(U/p_i\) for each fixed \(\ell\), and summing the log-bounded \(\Lambda(\ell)/\ell\) harmonic mass. The floors here cost at most the short divisor bound times \(V x^{o(1)}\), which is power-smaller than \(x/F\) for every non-exhausted row in the table. For \(T_3\), the no-mark list is impossible if \(u_0<U\); the one-mark list is impossible if \(u_0<U/p_i\). In each other case use the first harmonic moment difference on the interval \(U/e<d'\le Q_0/(e\ell)\), where \(e=1\) or \(e=p_i\); both endpoints are at least the polynomial \(U/e\) in a nonempty interval. As before CRT works with \((d'\ell,D)=1\) and \(\ell d'\mid u_0\), without wrongly requiring \((d',\ell)=1\); the floor sum is \((Q_0/e)x^{o(1)}\), power-smaller than \(x/F\) in the cases used. Partial summation retains all interval endpoints and the smooth test. These are the zero means of \(T_2,T_3\), proving (4).

## 3. Summation and normalization

Sum (4), divided by \(\phi(k)=\phi(v)\phi(w)\) because \(w<x^{.05}\) is coprime to \(v\), over the modulus weights and marks. The error stays \(O_A(xL^{-A})\) by log-bounded harmonic sums; all allowed \(F\) are coprime to \(k\) without any exclusion inside their bands. The optimal Selberg quadratic sum is
\[
                  \sum_w \xi_w/\phi(w)=1/G_R .
\]
For clarity, for squarefree permitted \(d\) set \(g(d)=1/\phi(d)\), \(h_0(d)=\prod_{p\mid d}(p-2)^{-1}\); if \(y_r=\sum_{r\mid d}\lambda_d g(d)\), the quadratic sum is \(\sum_r y_r^2/h_0(r)\), since \(1/g((d_1,d_2))=\sum_{r\mid(d_1,d_2)}1/h_0(r)\). The condition \(\lambda_1=1\) is \(\sum_r\mu(r)y_r=1\), so \(y_r=\mu(r)h_0(r)/G_R\) is the optimizer by Cauchy. Inverting gives \(|\lambda_d|\le h_0(d)/g(d)\ll L^{O(1)}\). This proves (1). As \(\omega_E\le3\) on the support, \(1_{\omega_E>0}=\binom{\omega_E}1-\binom{\omega_E}2+\binom{\omega_E}3\) and \(1_{\omega_E=1}=\binom{\omega_E}1-2\binom{\omega_E}2+3\binom{\omega_E}3\). The elementary symmetric harmonic prime sums tend to \(h^j/j!\) by PNT; removing target divisors and repeated labels costs power-small. This gives (2) and its exact-one analogue.

For the normalization the absolutely convergent factor defined by
\[
 \sum_{(d,N)=1}\mu^2(d)h_0(d)d^{-z}=\zeta(1+z)E_N(z)
\]
has \(E_N(0)=\mathfrak S(N)^{-1}\). At \(\Re z\ge-1/4\), the sum of the absolute Euler coefficients of \(E_N\) times \(d^{1/4}\) is \(x^{o(1)}\): away from \(N\) the quadratic factors converge absolutely since their first-order coefficient is \(O(p^{-2})\); for \(p\mid N\) their absolute factors are \(1+p^{-3/4}\) whose product is \(x^{o(1)}\) by splitting at \((\log x)^2\). Also \(E_N'(0)/E_N(0)\ll1+\sum_{p\mid N}\log p/p\ll\log\log x\). Convolving with the ordinary harmonic series now gives \(G_R=(\log R+O(\log\log x))/\mathfrak S(N)+O(R^{-1/8}x^{o(1)})\), uniformly (the harmless weaker \(1/8\) out of \(1/4\) absorbs the log tail). Finally \({\cal V}\sim Kx/2\) by the three bounded exponential-band reciprocal prime sums and \(W_s((N-y)/s)=W(\log_x s)+O(1/L)\) uniformly in \(y\). This proves (3).

## 4. Ledger and what is not controlled

On actual true prime \(b\), the original \(\mathcal Q_1\) reverse coefficient is \(1\); since \(v=saQ>x^{.503}\), the previously used \(F_2\) transfer counts \(Q\) but not \(aQ\). Thus the \(D_B(q)/\log q+2F_2/3\) ledger (no \(F_1\)) leaves \(+1/3\) here. A centered correction subtracting \(\tfrac13 {\cal R}(b)1_{\omega_E=1} C(m)\) on these quotient boxes removes that coefficient on true-\(b\) rows with exactly one reflected mark, without adding anything on \(C=0\) giant rows or on reflected primes. Equation (1) accounts for its full signed mean on all eligible integers \(b\). It does **not** bound the new composite-\(b\) complement.

In fact positive debit is unavoidable for that particular correction. On an open sufficiently narrow exponent box about \(s=.1385,a=.0685,Q=.2975\), let \(b\) be a product of three distinct primes near exponent \(.4955/3\) apiece, with \(n\) in the central physical range. Then every factor of \(b\) exceeds \(R\), so \({\cal R}(b)=1\) even though it is composite. At the separate true reflected semiprime \(m=pP\), with \(p\in E\) and \(P=m/p\), one has exactly one mark and \(C=-\log p\). In the original adjusted ledger without \(F_1\), \(F_2=2\) from singles \(Q,b_1,b_2,b_3\) and pairs \(a b_i,b_ib_j\). The exact long-product reversal gives
\[
 D_B(q)/\log q=-2-(3\log a+2\log b)/\log q
\]
on these rows: all prime factors exceed \(V_q\), \(a\) is the sole factor \(\le U_q\), and the full list \(z\mid q,z<q/B\) consists exactly of the unit, all five singles, and the six displayed pairs. In the exact squarefree formula \(D_B/\log q=-\sum_{z<q/B}\mu(z)-(\log q)^{-1}\sum_{z<q/B}\mu(z)\sum_{p\mid z,z/p>U_q}\log p\) this gives the asserted coefficient. The formula follows by adding (8) of [WholeQuotientTriprimeRemoval](WholeQuotientTriprimeRemoval.md) to the original reverse Vaughan coefficient: its short Möbius term \(-\mu(z)\log(q/z)\) for \(z\le U_q\) combines with the long-switch term \(-\mu(z)\log z\). Thus \(D_B/\log q+2F_2/3<0\) here. Subtraction creates an additional \(+\tfrac13\log p\) in the positive part, not merely an algebraically possible adverse sign. The companion checker verifies the strict rails and this central divisor profile in rational arithmetic. The box has positive genuine dyadic density at \(M_N\) scale: choose smaller disjoint prime-label exponent intervals inside it, fix all but the last true prime on each of \(n,m\), and apply ordinary PNT on fixed relative product subintervals; \(\log p\) supplies the reflected factor of \(L\). Distinctness and \((n,m)=1\) cost a power-small CRT/square loss since all factors are polynomial. As in [WholeQuotientTriprimeRemoval](WholeQuotientTriprimeRemoval.md), each odd product pair has the actual even target \(N=n+m\); the singular-series mean on these targets in the comparison normalization is unchanged. No fixed-target lower on the positive debit, or cancellation against it, is asserted.

This is a marked composite-source evaluation, not an invocation of Fouvry 1987 II Corollary 5 for \(\Lambda(m)\) at a moving residue. That corollary uses its fixed-integer-residue formula (1.7), whose error constant may depend on the residue. Nor does the theorem bound the original full signed complement or any Goldbach representation count.
