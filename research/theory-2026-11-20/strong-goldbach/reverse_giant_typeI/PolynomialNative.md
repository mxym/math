# Polynomial native factorization of the entire fixed-gap giant remainder

Fix a compact \(J_0\Subset(0,1)\), an interval \(J\subset J_0\), and \(0<\epsilon<1/2\). For a prescribed even \(N\), write \(L=\log N,\ \ell=\log L,\ S=\exp(\ell^4),\ B=N/S,\ z=\exp(\ell^2)\), and take any interval
\[
I\subset [N^{1/2+\epsilon},B].
\]
As in the [reverse Type I proof](ReverseTypeI.md), put \(y=N-x\),
\(T_y=y/B\), \(Q_y(m)=\sum_{d\mid m,\ d<T_y}\mu(d)\), and let \(C_I\) denote the true giant-prime score
\[
 C_I=\sum_{\substack{x\in NJ\\x\ {\rm prime}}}(\log x)
       \sum_{\substack{rm=y,\ r\in I\\r\ {\rm prime}}}
                      (\log r)Q_y(m).
\]
All inequalities on divisors in \(Q_y\) are strict. Define \(\gamma=1/2-\epsilon\); the literal quotient already has \(m\le N^\gamma\). Choose fixed positive exponents \(\eta_x,\omega_x,\eta_r,\omega_r\) satisfying
\[
 \eta_x+\omega_x<(1-\gamma)/2,\qquad
 \eta_r+\omega_r<1/2-\gamma.                                      \tag{1}
\]
Put \(U_i=N^{\eta_i},\ W_i=N^{\omega_i}\), for \(i=x,r\). For either slot let
\[
 H_{U_i}(A)=1_{A>1}\sum_{\substack{a\mid A\\a\le U_i}}\mu(a).
\]
In particular \(H_{U_i}(A)=0\) for every positive \(A\le U_i\), including \(A=1\).

**Theorem.** Uniformly at every prescribed even \(N\), and all the indicated \(I,J\), one has, for any fixed \(D>0\),
\[
 C_I=
 \sum_{\substack{x=A f\in NJ,\ y=m C h=N-x,\ Ch\in I\\
                  (xy,N)=1,\ P^-(AC)>z\\
                  f>W_x,\ h>W_r,\ f,h\ {\rm prime}\\
                  A>U_x,\ C>U_r}}
    (\log f)(\log h)\,H_{U_x}(A)H_{U_r}(C)Q_y(m)
       +O_{D,J_0,\epsilon,\eta_i,\omega_i}(NL^{-D}).                 \tag{2}
\]
This is a single calibration of the **entire** fixed-gap range: both native cofactors and both genuine prime labels have fixed positive polynomial lower scales. The quotient \(m\) is not replaced by an independent sample. No smooth-radical hypothesis is used.

This is the counterpart to the near-full two-high-label calibration with polynomial Möbius cutoffs; unlike the [rough double Vaughan expansion](DoubleRough.md), it keeps both prime labels and both native cofactors simultaneously polynomial throughout the fixed-gap interval. For arbitrarily small fixed \(\epsilon\) one must choose the right cutoffs smaller, and the near-root collar is not included. Formula (2) is not a bound or a sign for its right side.

## Proof

We use ordinary true-prime Bombieri–Vinogradov, including maximal real prefixes, at the scales \(N\) and \(N/m\). In each application the modulus is inside its square-root limit by a fixed power from (1). Fixed divisor-power weights on the discrepancy are harmless by the usual truncation: on \(\tau(q)\le L^{D'}\) increase the logarithmic precision beforehand; on the remaining moduli use the individual estimate \(O(XL/q+XL/\varphi(q))\) and arbitrarily high fixed divisor moments with reciprocal weight. Every modulus below is a literal product of its displayed divisor labels, not its least common multiple.

We will use two quotients of the uniform harmonic in [ReverseTypeI.md, §1](ReverseTypeI.md). If \(m\asymp M\gg_{J_0}S\) and \(K\subset [M,2M]\cap[T_y,\infty)\) is a real subinterval, then
\[
\begin{split}
 \sum_{\substack{m\in K\\(m,N)=1}}
       Q_y(m)F(m)/\varphi(Hm)&=O_D\big(L^{-D}/\varphi(H)\big),
                  &&(H,N)=1,\\
 \sum_{\substack{m\in K\\(m,H_0)=1}}
       Q_y(m)F(m)/m&=O_D(L^{-D}),                                  \tag{3}
\end{split}
\]
uniformly for polynomial-sized \(H,H_0\) and \(F\) of any fixed log-bounded supremum plus total variation. The first is exactly the cited result. For the second, open \(d<T_y,\ m=dn\). With \(d>\sqrt S\) fix \(n\) and apply the actual \((d,H_0)=1\) signed harmonic at \(d>\sqrt S\), then sum \(1/n\). For \(d\le\sqrt S\) count \(H_0\)-units \(n\) in real intervals at scale \(M/d\) and partial-sum \(F(dn)/n\). The count differs from its real density \(\varphi(H_0)/H_0\) by
\[
 O\!\left((M/d)^\sigma\prod_{p\mid H_0}(1+p^{-\sigma})\right),
 \qquad \sigma=1-\frac1{10\ell}.
\]
This uses the floor and omitted-main bound on the expanded squarefree divisors. The product is \(\ell^{O(1)}\) by splitting at \(L^2\). The signed main sums \(\mu(d)1_{(d,H_0)=1}/d\) up to \(\sqrt S\). Its complete value is zero, and the signed tails at all lengths \(\ge\sqrt S\) are arbitrarily log-small, uniformly for this polynomial mask: its series is \(1/\zeta(s)\) times \(\prod_{p\mid H_0}(1-p^{-s})^{-1}\); the coefficient norm of the extra factor at \(\sigma\) is \(\ell^{O(1)}\), using the same split. Convolution, splitting the absolute factor at the square root of the real length, and classical Mertens give the claimed tail after partial summation. These arguments are uniform for short real subintervals inside the dyad and do not cost \(\tau(H_0)\) at the scale \(S\). An arbitrary polynomial upper limit on \(m\) is allowed, using \(O(L)\) dyads.

First replace the two genuine primes \(x,r\) by their von Mangoldt weights, always keeping the true unit conditions \((x r m,N)=1\) and the \(z\)-roughness of \(x,r\). These changes cost a power saving. The original \(x\) proper powers are \(N^{1/2+o(1)}\) physical integers. On the \(r\)-side the reciprocal sum of proper powers \(r\ge N^{1/2+\epsilon}\) is \(N^{-(1/2+\epsilon)/2+o(1)}\), so count their multiples \(y\le N\). Primes or proper powers with underlying prime dividing \(N\) number \(O(L^2)\); on the \(r\)-side each has at most \(N^\gamma\) allowed multiples. All physical expansions below are bounded at fixed \(x,y\) by fixed divisor powers and log powers, both \(N^{o(1)}\) for these power-small errors. Prime \(x,r\) in these ranges are \(z\)-rough.

On each slot \(n=x\) or \(r=y/m\), at its own cutoff pair \(U,W\), use the exact identity
\[
\begin{split}
 \Lambda(n)&=\mathcal I(n)+\mathcal D(n),\\
 \mathcal I(n)&=\sum_{\substack{a\mid n\\a\le U}}\mu(a)\log(n/a)
  -\sum_{\substack{af\mid n\\a\le U,\ f\le W}}\mu(a)\Lambda(f),\\
 \mathcal D(n)&=-\sum_{\substack{f\mid n\\f>W}}\Lambda(f)H_U(n/f).
                                                                    \tag{4}
\end{split}
\]
Here \(n>W\) always. To verify (4), the Type I difference is the \(f>W\) sum of \(\Lambda(f)\sum_{a\mid n/f,a\le U}\mu(a)\). Adding the last line leaves just \(\Lambda(n)\) from \(n/f=1\). Roughness of the original slot is retained in every term; on opened products it is roughness of each actual factor. If \(P,R\) denote the two original weights including roughness and units, then the exact product identity is
\[
  P R=P\mathcal I_r+\mathcal I_x R-\mathcal I_x\mathcal I_r
                   +\mathcal D_x\mathcal D_r,                       \tag{5}
\]
with the inherited masks on each factor.

Here are the common roughness and error conventions. In a Type I term, write \(n=a f g\) with \(f=1\) in the first term, and \(g\) the free integer. The outer factors are themselves \(z\)-rough and target units. Open \(P^-(g)>z\) by successive squarefree Bonferroni degrees around \(C_D\ell/\log(2\ell)\), on primes \(\le z\) outside \(N\). The label \(e\mid g\) has \(e\le N^{o(1)}\); the number of labels in this truncation or at the next degree is \(N^{o(1)}\). The first omitted degree has reciprocal mass at most
\((O(\log\ell))^j/j!\), with either \(1/e\) or \(1/\varphi(e)\). Choose \(C_D\) before \(N\) to beat every required fixed log power. The pointwise difference between the indicator and a truncated expansion is bounded by the count of the first omitted degree. With two roughness factors use the telescoping product difference and bound the absolute truncated terms by their divisor-label sums. For a true prime leg the omitted-degree assignments are inside precisely the same BV modulus bounds as the retained assignments. Their positive principal upper is bounded by the indicated factorial reciprocal mass times log powers (use \(\varphi(H e)\ge\varphi(H)\varphi(e)\); no disjointness with \(m\) is needed). In the integer overlap the same upper follows from the ordinary CRT density \(1/q_1q_2\) on compatible moduli; the floors for all of these terms have the same fixed power reserve shown below. Thus all roughness truncation errors are \(O_D(NL^{-D})\). Absolute multiplicities in any true modulus are bounded by a fixed divisor power, including \(d\mid m\) in \(Q_y\).

**The right Type I term.** In \(P\mathcal I_r\) fix \(m,a,f,e\). The actual true prime \(x\) is in the reduced class \(N\bmod m a f e\). Its modulus is at most \(N^\gamma U_rW_rN^{o(1)}<N^{1/2-\delta}\) for some fixed \(\delta>0\) from (1). Use true-prime BV at scale \(N\); opening \(d\mid m\), the strict condition \(d<T_y\) only restricts a real endpoint. In the main integral fix \(x\), hence \(y\). The \(m\)-interval is precisely \(y/m\in I\) and automatically \(m\ge T_y\), with all target units retained. Its model is \(1/\varphi(m a f e)\). The first log weight is \(\log(y/(ma))\), not a log divided by the roughness label; it has fixed log-bounded variation on each \(m\)-dyad. Summing \(d\) back, the first harmonic in (3), with \(H=a f e\), cancels the principal. The remaining absolute \(a,f,e\) sums after extracting \(1/\varphi(H)\) cost fixed log powers.

**The left Type I term.** In \(\mathcal I_x R\), for each actual \(m\) keep the coprimality \((m,qN)=1\), \(q=a f e\). This is necessary because \(q\mid x=N-mr\) and \(x\) is a target unit. The true prime \(r\) lies in the reduced class \(N\overline m\bmod q\). Its length scale is \(X=N/m\), and \(q\le U_xW_xN^{o(1)}<X^{1/2}N^{-\delta}\) by (1), uniformly in \(m\). Thus maximal-prefix BV at this true scale, summed over \(m\) with the reciprocal divisor-weight harmonic from the factor \(X=N/m\), costs only fixed log powers. The same endpoint argument applies to \(d<T_y\). In the principal the density is \(1/\varphi(q)\), independent of the actual \(m\) after \((m,qN)=1\) has been enforced. Change integration variable from \(r\) to \(x=N-mr\); its measure is \(dx/m\). At fixed \(x,a,f,e\), the type-I weight is independent of \(m\), and the literal \(m\)-interval still is \(y/m\in I\); the \(d\)-cutoff recombines exactly into \(Q_y(m)\). Use the **second** harmonic in (3), \(H_0=qN\), before summing the outer labels. This does not evaluate two true primes jointly.

**The overlap.** For two opened Type I terms put \(q_1=a f e_1,\ q_2=m c h e_2\). Their unit support forces \((q_1q_2,N)=1\) and \((q_1,q_2)=1\), otherwise the actual CRT class is empty. For compatible tuples \(x\equiv0\bmod q_1,\ x\equiv N\bmod q_2,\ (x,N)=1\) has density \(\varphi(N)/(N q_1 q_2)\), with floor at most \(\tau(N)\) by exact target-unit inclusion–exclusion. Fixed log costs from the endpoint weights follow by real partial summation. The total floor, including the roughness labels and all quotient choices, is at most
\[
 N^{\gamma+o(1)}U_xW_xU_rW_r
 \le N^{1-\delta'}
\]
for some fixed \(\delta'>0\), since the exponent in (1) is strictly less than \(1-\gamma/2\). After returning the \(d\mid m\) sum to \(Q_y(m)\), at fixed \(x,a,f,e_1,c,h,e_2\) the \(m\)-dependent unit condition in the principal is just \((m,Nq_1)=1\); other endpoint compatibility is independent of \(m\). The only remaining nonconstant smooth weight in \(m\) is \(\log(y/(mc))\) when the right term is the first Type I term. The second harmonic of (3) applies, then the absolute reciprocal sums over the fixed labels cost log powers. This kills the overlap, not just a product of two separately asserted marginal estimates.

Only \(\mathcal D_x\mathcal D_r\) remains in (5). The minus signs in (4) cancel. Set \(x=A f,\ y=m C h\); the \(r=Ch\in I\) gate remains **exact**, as does \(d<T_y\) inside \(Q_y\). The native masks force \(A>U_x,\ C>U_r\). Labels \(f>W_x,\ h>W_r\) which are proper powers have reciprocal mass \(N^{-c+o(1)}\) for some fixed \(c>0\); counting their actual multiples of \(x\) or \(y\) and using the physical divisor envelope pays their removal. All remaining labels are literal primes, establishing (2).

## Optional exact change of the native coefficients

For a fixed slot replace \(\mu(a)1_{a\le U}\) in (4) by any fixed coefficients \(c_a\) supported on \(a\le U\), with \(c_1=1\) and \(|c_a|\le L^{O(1)}\tau(a)^{O(1)}\). In the native term put \(H_c(A)=1_{A>1}\sum_{a\mid A}c_a\). The same elementary identity holds, and every modeled cancellation above is uniform because it is applied to the actual \(m\)-harmonic at fixed outer labels. This flexibility alone does not force \(A>U\) for the changed \(H_c\), or prove any sign. The polynomial lower supports in (2) refer to the literal Möbius choices only.
