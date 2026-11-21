# Opposite actual high signs with the same complete low divisor list

This is an arithmetic localization of the high remainder in [CoupledQRShortPart](CoupledQRShortPart.md), on its actual six-prime source \(\mathcal B\). Two genuinely populated (dyadically) physical profiles have exactly opposite high weights while keeping the same kind of actual short core and **all** its short divisors. The total rough occupancy of these cores (not either parity separately) has a uniform fixed-target comparison. No Goldbach bound is claimed.

## Exact opposite signs and the remaining sum

Keep the notation, original \(C\), actual prime-label source \(\mathcal B\), and exact remainder \(A(p,u)\) with \(D=x^{.219}\) from the linked note. Mark actual primes with
\[
 \log_x p\in(.315,.317),\qquad
 \log_x r_1\in(.098,.100),\qquad
 \log_x r_2\in(.100,.102),\qquad
 w=r_1r_2,\quad p w\mid m .
\]
Write \(u=m/p=w v\). Take the marks simple, as they are in the two squarefree profiles below. Then \(x^{.198}<w<x^{.202}<D\), \(v\) has exponent in \([.481,.487]+o(1)\), and the following are pointwise statements on the physical integer \(m\), not approximated logarithms:
\[
\begin{array}{c|c|c}
v&\{d:d\mid u,\ d\le x^{.22}\}&A(p,u)\\ \hline
P\ \text{a prime}&\{1,r_1,r_2,w\}&-\log(pw)\\
P_1P_2\ \text{distinct primes, each in }(x^{.23},x^{.255})&
       \{1,r_1,r_2,w\}&+\log(pw).
\end{array}                                                               \tag{1}
\]
There is exactly one earlier \(E\)-mark on each such row. All reflected factors exceed \(V\) by fixed powers, so both \(\Lambda(\ell)\) corrections in \(A\) vanish: the low one uses \(\ell\le V\), and the high one would require \(\ell\le Q_0/U=H^2\). With \(v=P\), the only divisor \(d\) in \((D,U]\) is \(P\) itself, since \(P r_i>x^{.579}\). In the semiprime case, \(P_j d'\in(D,U]\) for every \(d'\mid w\), since \(.255+.202<.5\); their total signed logarithm for each \(P_j\) is zero because \(\sum_{d'\mid w}\mu(d')=\sum_{d'\mid w}\mu(d')\log d'=0\), with two distinct prime factors in \(w\). The divisor \(P_1P_2=v\) is in the high interval and attaching even one \(r_i\) pushes it out, so its contribution alone is \(+\log(pw)\). This proves (1).

Both profile signs have positive \(M_N\)-normalized **dyadic** mass, not necessarily at the same target or for identical \(p,w\) in that target. For each sign, take slightly narrower open exponents for the marks inside the stated intervals and, in the semiprime case, for two distinct balanced residual primes. Fix all but the final true prime on each of the two independently counted products \(n\) and \(m\), and apply PNT in fixed relative product intervals as in [CoupledQRShortPart](CoupledQRShortPart.md). The weighted count in each product interval has density \(\asymp 1/L\), and \(\log(pw)\asymp L\). Pairs of odd products give the literal even targets \(N=n+m\). Choose their intervals strictly inside \(n\in(x/2,x]\), \(m\in[x,3x/2)\), \(x\in[X,2X]\); exponent constraints are unchanged by \(O(1/L)\) shifts if comparing \(x,X\). Common factors and repeated prime labels cost power-small (all are polynomial, or their independent intervals are disjoint). The comparison uses the actual sum of \(M_N\) over the dyad, with \(\mathfrak S(N)\) of mean 2 on the even lattice.

Thus bounding just the selected source with these short marks can leave a genuine fixed-target prime-versus-balanced-semiprime difference:
\[
 \sum_{\mathcal B} W_s(q)
   \sum_{\substack{p w\mid N-n\\p,w\ \text{as above}}}
       \log(pw)\left[1_{v=P_1P_2\ \text{as in (1)}}-1_{v\text{ prime}}\right].
                                                                            \tag{2}
\]
This is an exact term of the high remainder restricted to the two displayed profiles; no claim about other ranks or other marked cores is made. It identifies a specific missing comparison, not an impossibility theorem for distribution methods.

## Uniform rough occupancy on the actual independent cores (not a sign split)

Here is what the same source presently supplies. Put \(z=x^\kappa\) for a sufficiently small fixed \(\kappa>0\),
\[
 V_N(z)=\prod_{\substack{\ell\le z\\ \ell\text{ prime},\,\ell\nmid N}}
                   \left(1-\frac1{\ell-1}\right),\qquad
 U_{\mathcal B}(N)=\sum_{\mathcal B}W_s(q),
 \qquad
 h_{p,N}=\sum_{\substack{p\text{ in its band}\\p\nmid N}}\frac1{p-1}.
\]
For each \(w=r_1r_2\) as above, \((w,N)=1\), let \(Z_w\) be the genuine weighted count of \(\mathcal B,p\) rows with \(p w\mid m\) and resulting \(v=m/(p w)\) squarefree and \(P^-(v)>z\). Count each permitted \(p\) separately. Then for any fixed \(\eta>0\) one can choose a sufficiently small fixed \(\kappa\) so that, for all sufficiently large actual even \(N\),
\[
 \sum_w\left|Z_w-\frac{h_{p,N}}{\phi(w)}V_N(z)U_{\mathcal B}(N)\right|
 \le \eta\, h_{p,N} V_N(z)U_{\mathcal B}(N)\sum_w\frac1{\phi(w)}.             \tag{3}
\]
The source mass \(U_{\mathcal B}(N)\asymp x/L\), by ordinary PNT fixing the other five primes in interior exponential profile bands and varying the final true prime on the central interval; upper PNT gives the opposite bound. Excluding factors of \(N\) from these polynomial lengths is negligible. Similarly \(h_{p,N}\) and \(\sum_w1/\phi(w)\) tend to strictly positive band integrals. In particular the weighted occupancy in (3) is of order \(\mathfrak S(N)x/L^2\) at fixed target \((\kappa\) fixed), not a count over uniformly random cores and not a prime count.

To see (3), use the very same independent actual source coefficients \(\alpha=b_2b_3\), \(\beta=s a Q r\) as in the linked note. For any signs \(|\theta_w|\le1\), and upper/lower linear sieve coefficients on squarefree \(d\le x^{.015}\), \(P^+(d)\le z\), the literal progression is \(n\equiv N\bmod p w d\). All slots in [Lichtman Proposition 5.2](https://arxiv.org/html/2309.08522#S5) are again truly independent:
\[
 q_1=p,\qquad q_2=w d\le x^{.217},\qquad q_3=1 .
\]
Indeed the two \(w\) primes are the unique factors of \(q_2\) in their disjoint polynomial bands and no \(d\) prime hits these bands. Thus \(\theta_w\) and the sieve coefficient act only on \(q_2\); they do not depend on \(p\). The railway inequalities follow with slack from the linked proof, which allowed \(q_2\le x^{.22}\), including clipping and uniform SW of the first source. The physical weight \(W_s\), endpoints and masks are treated by the same fine independent boxes and log reserve. Variables \(p,w,d\) share no primes with the actual \(n\), as the six source bands are disjoint from these three mark bands and all their primes exceed \(z\). For target nonunits a divisibility is impossible, so \((pwd,N)=1\) is enforced. The principal for each triple is therefore exactly \(U_{\mathcal B}(N)/[\phi(p)\phi(w)\phi(d)]\) up to the already controlled sum of progression errors.

The weight in \(d\) consequently has the standard dimension-one local factor \(g(\ell)=1/(\ell-1)\) for \(\ell\nmid N\), zero for \(\ell\mid N\) (and \(2\mid N\)). This has the uniform dimension bound: the corresponding product without target deletions is bounded by the universal \(\log z_2/\log z_1\) dimension-one envelope, and deleting factors only decreases this product on any sifting interval. Thus the upper and lower fundamental lemma applies with \(s=.015/\kappa\), giving a relative \(o_{s\to\infty}(1)\) to \(V_N(z)\) uniformly in the target. Split the positive and negative selectors \(\theta_w\) and use the proper upper/lower bounds separately for any of their real signed sums. This handles the sifting error on scale \(h_{p,N}V_N(z)U_{\mathcal B}\sum_w1/\phi(w)\), not on scale \(x\). All log-reserve progression errors are smaller. Squareful \(v\) can be dropped by \(\sum_{\ell\ge z}\lfloor O(x)/\ell^2\rfloor\ll x/z+\sqrt x\), with bounded-by-divisor-powers physical tuple multiplicities; this is power-small. The same applies if one insists the three marks occur only to the first power (all are polynomial). Choose \(\kappa\) small before \(x\) grows, then choose \(\theta_w\) as the sign of the true discrepancy to obtain (3). The \(p\)-sum stays independent of \(\theta_w\); (3) is not a pointwise bound for a prescribed pair \((p,w)\).

This technique cannot take \(z=x^{.22}\): even when using the whole available second slot, its residual sieve level after the actual \(w>x^{.198}\) is at most \(x^{.022}\). There is no lower rough occupancy from that choice, and the proved small-\(\kappa\) occupancy can contain many higher ranks. The complete short-divisor identity (1) shows why the known abundance of real cores in (3) does not estimate (2) by itself.
