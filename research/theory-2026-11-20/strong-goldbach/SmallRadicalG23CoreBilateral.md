# One short-prime mixed input makes the entire genuine A2/A3 bilateral core benign

Research note, 2026-11-24. A tightening of [the short-prime mixed-parity marker](SmallRadicalShortPrimeMixedParity.md) and [half-divisor tradeoff](SmallRadicalHalfDivisorTradeoff.md). The high-body bound in the genuine core is proved; control of the global uncovered mixed input is not. Order-of-magnitude statements below are for fixed \(P\), with actual primes and exact translated marks.

## 1. Exact coefficient and the single remaining mixed input in this representation

Use large even \(P\), \(L=\log P\), \(\operatorname{rad}(P)\le L^B\), \(I=PJ\) fixed interior, \(y=e^{L^\delta}\), \(0<\delta<.1\), \(z=e^{L^{.24}}\), \(m=P-n\), and the actual translated first-cover \(C=C_{>1}\). Set
\[
H=L^{3/5},\qquad D=P^{1/2}e^{-H},\qquad
s(n)=\sum_{\substack{P^\sigma<p\le D\\p\mid n,\ p\ {\rm prime}}}1,\quad 0<\sigma<1/4.
\]
Define the following short-prime counter, with only one mixed term:
\[
G_{23}(n)=1-\tfrac23s(n)-\tfrac13s(n)\lambda(n)
=
\begin{cases}
1-s(n),&\lambda(n)=+1,\\
1-s(n)/3,&\lambda(n)=-1 .
\end{cases}
\tag{1}
\]
It is 1 on every true prime in \(I\). Thus \(w(n)=(\log n)G_{23}(n)+T_{23}(n)\) pointwise for \(T_{23}(n)=-(\log n)G_{23}(n)1_{n\ {\rm composite}}\). Multiplying the two terms by \(R_z(n)\) does not change the true prime coefficient. The contributions of \(1-\tfrac23s(n)\) to the first coefficient, against \(C R_z(n)R_y(m)\lambda(m)\log n\), are exactly the already verified near-square-root shifted Type I, with short \(d=1\) or an actual prime \(p\le D\) and \(\log n=\log d+\log(n/d)\). The additional small reciprocal/profile modulus logs are \(o(H)\), and the actual endpoint after \(v\mid m\) is \(P/v=P^{1-o(1)}\), leaving the same full BV margin as in the half-divisor proof. Hence the exact original marked budget can be written
\[
\begin{aligned}
\sum_{n\in I} C R_y(m)\lambda(m)w(n)
&=-\tfrac13\mathcal M
 +\sum_{n\in I} C R_z(n)R_y(m)\lambda(m)T_{23}(n)+O_A(PL^{-A}),\\
\mathcal M
&=\sum_{n\in I} C R_z(n)R_y(m)(\log n)s(n)\lambda(n)\lambda(m).
\end{aligned}
\tag{2}
\]
This is literally the mixed statistic from the previous G note, whose true base-covered part is paid. Its residual outside base cover is still open. In particular (2) does not export that covered bound to the true polynomial low-rank cores considered below.

Here is the proved additional conclusion. Let \(A_j\) consist of the actual squarefree rank-\(j\) products all of whose prime factors exceed \(P^{1/4}\). For all genuine oriented rows \(n\in I,\ n,m\in A_2\cup A_3\), the total **negative part** of the high sum in (2) is
\[
O\bigl(PS(P)H/L^2+PS(P)H^2/L^3+P^{.84}\bigr)
=o(PV_y(P)/L).
\tag{3}
\]
This bound is unconditional given the elementary Kloosterman and sieve input, and applies with or without the actual \(C\). A symmetric bilateral conclusion follows by bounding both orientations separately with \(I\) and its reflection. It is not a bound on other rank types or on \(\mathcal M\).

## 2. Exact sign check on \(A_2,A_3\)

On \(A_2\) write \(n=pq,\ P^{1/4}<p<q\), \(n\asymp_J P\). The inequality \(D^2=o(n)\) shows at most one prime is \(\le D\). Thus \(G_{23}=0\) if \(p\le D\) and \(G_{23}=1\) otherwise. This coefficient is never negative, so only complements of type \(A_2\) can give a negative score in the stated core. If \(p>D\), it lies in the actual shell \((D,\sqrt P]\), of reciprocal prime mass \(O(H/L)\). Reflect the roles in [the established one-window semiprime Kloosterman upper bound](SmallRadicalAdverseSemiprimeWindow.md); this pays the whole \(A_2\)-source negative amount by the first term of (3).

On \(A_3\) write \(n=p q r\) with \(P^{1/4}<p<q<r\), again \(n\asymp_J P\). There cannot be two primes above \(D\): their product with the remaining one would exceed \(D^2P^{1/4}>P\). All factors exceed \(P^\sigma\). Therefore \(s(n)\) is 3 or 2, and \(G_{23}=0\) or \(1/3\), respectively. The only negative score within the core is now \(m\in A_2\) and \(r>D\); there is none against \(A_3\). Put \(t=pq\). On the exceptional rows
\[
P^{1/2}<t\le P/r<P^{1/2}e^H,\qquad
P^{1/4}<p<q<P^{1/4}e^H.
\tag{4}
\]
These bounds follow from the two genuine quarter-size lower bounds and \(r>D\), not from a distribution assumption. In fact \(r<P^{1/2}\) because \(t>P^{1/2}\). The family \(\mathcal T\) of possible \(t\)'s is squarefree with exactly two primes and has reciprocal mass
\[
\sum_{t\in\mathcal T}t^{-1}
\le \tfrac12\left(\sum_{P^{1/4}<p<P^{1/4}e^H,\ p\ {\rm prime}}p^{-1}\right)^2
=O((H/L)^2)
\tag{5}
\]
by quantitative Mertens at its two genuine log endpoints. The pair \(p,q\) is uniquely recoverable from \(t\).

The target equation for this remaining case is now
\[
x q'+t r=P,\qquad m=xq'\in A_2,
\tag{6}
\]
for genuine smaller \(x<q'\) and genuine \(r\). Both complement primes exceed \(P^{1/4}\). We next upper bound (6) with fixed \(t\) and with the **same** \(P\), not by an independence approximation.

## 3. Modular-hyperbola completion at the squarefree two-prime modulus \(t\)

This is the earlier prime-modulus upper sieve with one extra Fourier check. Cover the \(A_2\) product \(m\) in the fixed reflected interior interval by \(O(L)\) boxes \(I_1\times I_2\) for \(x,q'\). In each, the short scale \(X\ge P^{1/4}\), long scale \(Y\asymp_J P/X\), and \(X+Y\ll_J P^{.75}\). The boxes may be widened at fixed relative widths inside a slightly larger fixed interior interval; this keeps \(r=(P-xq')/t\gg_J P/t\).

Fix \(t=ab\in\mathcal T\) with distinct true primes \(a,b>P^{1/4}\); \((t,P)=1\). For a sieve modulus \(d\) coprime to \(t\), fix a residue class of each of \(x,q'\) modulo \(d\). Their counts in the box are \(N_1=|I_1|/d+O(1)\), \(N_2=|I_2|/d+O(1)\). Their step-\(d\) progressions mod \(t\) split into complete periods and one terminal interval-progression of length \(<t\) each. The hyperbola \(xq'\equiv P\bmod t\) lives on the unit group. The complete-complete main is exact, with density \(\varphi(t)/t^2\); a cross term involving just one terminal progression deviates from this main by at most \(O((N_1+N_2)\tau(t)/t)\), because its number of units differs from \(\varphi(t)/t\) times its size by at most \(\tau(t)=4\), by the elementary divisor inclusion-exclusion. This works even when one progression has many full periods and the other has none.

For clarity, for a terminal progression let \(\widehat B(h)\) be its normalized additive Fourier coefficient mod \(t\); for each \(g\mid t\),
\[
\sum_{\substack{h\bmod t\\h\ne0,\ g\mid h}}|\widehat B(h)|\ll \frac{\log(2t)}g,\qquad |\widehat B(0)|\le1.
\tag{7}
\]
Indeed write \(h=g j\) and use the geometric-series bound (with factor \(1/t\)); multiplication by the step \(d\) permutes the nonzero frequencies modulo \(t/g\), and summing their bounds gives \(O((t/g)/t\cdot\log(2t))\). This argument does not assume \(h\) itself is a unit.

For the two terminal progressions, the zero-zero mode gives exactly \(\varphi(t)\) times the two normalized lengths. If only \(k\) is nonzero, the complete sum is \(c_t(kP)\), a Ramanujan sum, since inversion permutes the units. For the other axis it is \(c_t(h)\). By CRT on squarefree \(t\), each local factor of \(c_t(j)\) is \(\ell-1\) if \(\ell\mid j\) and \(-1\) if not, so \(|c_t(j)|\le (j,t)\). In particular single-frequency nonunits, rather than being treated as unit frequencies, cost at most
\[
\sum_{g\mid t}g
    \sum_{\substack{h\ne0\\g\mid h}}|\widehat B(h)|
\ll \tau(t)\log(2t)
\]
by (7). If both frequencies \(h,k\) are nonzero modulo \(t\), the complete twisted sum is \(K_t(h,kP)\). On each prime factor \(\ell\), the two reduced frequencies may be both zero (cost \(\ell-1\)), exactly one zero (sum \(-1\)), or both nonzero (Weil bound \(2\sqrt\ell\)). CRT only multiplies them by unit factors locally, so together
\[
|K_t(h,kP)|\le4\sqrt t\sqrt{(h,k,t)}.
\]
Use \(\sqrt{(h,k,t)}\le\sum_{g\mid h,k,t}\sqrt g\) and (7) for both nonzero modes. Their total is at most
\[
O\!\left(\sqrt t\,\log^2(2t)\sum_{g\mid t}g^{-3/2}\right)
=O(\sqrt t\,\log^2(2t)).
\]
This handles all CRT coincidences and axes. Replacing \(N_1,N_2\) by interval lengths divided by \(d\) adds floor \(O((|I_1|+|I_2|)/(dt)+1/t)\). Thus the count in the stipulated residue pair equals
\[
\frac{\varphi(t)}{t^2}\frac{|I_1||I_2|}{d^2}
+O\left(\sqrt t\,\log^2(2t)+\frac{|I_1|+|I_2|}{dt}+\frac1t\right).
\tag{8}
\]

## 4. Selberg counting, exact errors, and consequence

Use sieve divisor level \(B_0=P^{1/100}\) and sieving primes \(\ell\le W=B_0^\gamma\) for a sufficiently small fixed \(\gamma>0\). They do not divide \(t\), since \(a,b>P^{1/4}\), and all true prime slots \(x,q',r\) exceed \(W\). For each additional prime the exact bad pairs for \(x,q'\) are \(x=0\), \(q'=0\), and \(xq'=P\bmod\ell\) (since \(r=(P-xq')/t\)). Their union has \(3\ell-2\) points if \(\ell\nmid P\), \(2\ell-1\) otherwise, exactly as before. For squarefree \(d\) on these primes, CRT multiplies the counts on the **residue pair**, and the number of simultaneous bad pairs is \(\le d^2\). Summing (8) over those pairs gives the old main local product, and errors
\[
O(d^2\sqrt t\,L^2+d(X+Y)/t).
\]
No hidden \(\tau(d)\) accumulation is needed. The standard finite Selberg square has \(|\lambda_d|\le1\), at most \(B_0^2\) ordered coefficient pairs, and true modulus \([d_1,d_2]\le B_0^2\). The denominator comparison by the independent normalized divisor product of mean log \(O(\log W)\) yields the expected upper \(S(P)/L^3\) times the raw lattice main. Thus per fixed \(t\) and box the true count is
\[
\ll PS(P)/(tL^3)+B_0^6\sqrt t\,L^2+B_0^4(X+Y)/t.
\]
When summing floors in \(t\le P^{1/2}e^H=P^{1/2+o(1)}\), the sum of \(\sqrt t\) is \(P^{.75+o(1)}\) even over integers and the other harmonic uses (5) (or the crude log bound). Including \(O(L)\) boxes and the actual weight \(O(L)\) gives a total negligible \(O(P^{.84})\). The main weighted total is \(O(PS(P)/L\cdot(H/L)^2)\) by (5), proving the second term in (3). All counts on marked rows are bounded by this genuine unmarked absolute bill.

Thus no substantial **negative** oriented or bilateral coefficient remains among actual \(A_2,A_3\) pairs in (2). The true previously unfavorable wide \(A_2,A_2\) need no independent asymptotic here, and the adverse wide \(A_3,A_3\) created by half-divisor exchange is not created by this corrected coefficient. The price is explicit: ordinary short-divisor estimates pay only the linear \(1-\tfrac23s\) part in (2); \(\mathcal M\) is a genuine mixed two-point sign. The already paid base-covered part of \(\mathcal M\) does not cover these true polynomial-factor pairs, and no total estimate or Goldbach conclusion follows.
